// makefun-forge: a standalone GitHub-compatible git forge in one process.
//
// Surfaces: git smart HTTP (upload-pack v2 + v0, receive-pack v0), REST v3
// under /api/v3, GraphQL v4 at /api/graphql, MCP at /mcp. Node 22 standard
// library only, zero dependencies, all state in memory.
//
// Lifecycle: bind an ephemeral port, POST {"port"} to $MAKEFUN_ENV_URL/register,
// long-poll GET $MAKEFUN_ENV_URL/done, exit 0 when it says done.
import { createHash } from 'node:crypto';
import http from 'node:http';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------- constants

const VIEWER_LOGIN = 'adaiversen';
const VIEWER_ID = 1000;
const VIEWER_NAME = 'ada iversen';
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const ZERO_OID = '0'.repeat(40);
const DEFAULT_BRANCH = 'main';
const FORGE_NAME = 'makefun-forge';
const FORGE_VERSION = '1.0.0';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const ENV_URL = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');

// Deterministic timestamps: a fixed epoch plus a monotonic sequence, so no
// wall clock ever reaches a response.
const TIME_BASE_SEC = 1_735_689_600; // 2025-01-01T00:00:00Z
let timeSeq = 0;
function nextIso(): string {
  timeSeq += 1;
  return new Date((TIME_BASE_SEC + timeSeq) * 1000).toISOString();
}
function nextEpochSec(): number {
  timeSeq += 1;
  return TIME_BASE_SEC + timeSeq;
}

// ---------------------------------------------------------------- small utils

function sha1(data: Buffer | string): string {
  return createHash('sha1').update(data).digest('hex');
}
function hashObject(type: string, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1(Buffer.concat([header, data]));
}
function b64encode(data: Buffer | string): string {
  return Buffer.from(data).toString('base64');
}
function b64decode(text: string): Buffer {
  return Buffer.from(text.replace(/[\r\n\t ]+/g, ''), 'base64');
}
function b64url(text: string): string {
  return Buffer.from(text, 'utf8').toString('base64url');
}
function b64urlDecode(text: string): string {
  return Buffer.from(text, 'base64url').toString('utf8');
}
function isOid(value: unknown): value is string {
  return typeof value === 'string' && /^[0-9a-f]{40}$/.test(value);
}
function jsonBody(value: unknown): string {
  return JSON.stringify(value);
}

// ---------------------------------------------------------------- pkt-lines

function pktLine(payload: Buffer | string): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = body.length + 4;
  const head = Buffer.from(len.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, body]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

type PktKind = 'data' | 'flush' | 'delim' | 'end';
interface Pkt {
  kind: PktKind;
  payload: Buffer;
}

/** Parse a whole buffer of pkt-lines. Throws on malformed framing. */
function parsePktLines(buf: Buffer): { packets: Pkt[]; rest: Buffer } {
  const packets: Pkt[] = [];
  let off = 0;
  while (off < buf.length) {
    if (off + 4 > buf.length) throw new Error('truncated pkt-line header');
    const head = buf.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-f]{4}$/.test(head)) throw new Error(`bad pkt-line length ${JSON.stringify(head)}`);
    const len = parseInt(head, 16);
    if (len === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      off += 4;
      continue;
    }
    if (len === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      off += 4;
      continue;
    }
    if (len === 2) {
      packets.push({ kind: 'end', payload: Buffer.alloc(0) });
      off += 4;
      continue;
    }
    if (len < 4 || off + len > buf.length) throw new Error('bad pkt-line length');
    packets.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return { packets, rest: Buffer.alloc(0) };
}

// ---------------------------------------------------------------- git objects

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObject {
  type: ObjType;
  data: Buffer;
}

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    if (sp < 0) break;
    const nul = data.indexOf(0x00, sp + 1);
    if (nul < 0 || nul + 21 > data.length) break;
    const mode = data.subarray(off, sp).toString('utf8');
    const name = data.subarray(sp + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    off = nul + 21;
  }
  return entries;
}

/** Git tree sort: directories compare as if their name ended with '/'. */
function treeSortKey(entry: { mode: string; name: string }): string {
  return entry.mode === '40000' ? `${entry.name}/` : entry.name;
}
function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const ka = treeSortKey(a);
    const kb = treeSortKey(b);
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

interface CommitView {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
}
function parseCommit(data: Buffer): CommitView {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split < 0 ? text : text.slice(0, split);
  const message = split < 0 ? '' : text.slice(split + 2);
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, author, committer, message };
}
function buildCommit(fields: { tree: string; parents: string[]; message: string; author: string; committer: string; timestamp: number }): Buffer {
  const lines: string[] = [`tree ${fields.tree}`];
  for (const parent of fields.parents) lines.push(`parent ${parent}`);
  const stamp = `${fields.timestamp} +0000`;
  lines.push(`author ${fields.author} ${stamp}`, `committer ${fields.committer} ${stamp}`, '');
  return Buffer.from(`${lines.join('\n')}\n${fields.message}`, 'utf8');
}
function buildTag(fields: { object: string; type: string; tag: string; message: string; tagger: string; timestamp: number }): Buffer {
  const stamp = `${fields.timestamp} +0000`;
  return Buffer.from(
    `object ${fields.object}\ntype ${fields.type}\ntag ${fields.tag}\ntagger ${fields.tagger} ${stamp}\n\n${fields.message}`,
    'utf8',
  );
}
function parseTag(data: Buffer): { object: string; type: string; tag: string; tagger: string; message: string } {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split < 0 ? text : text.slice(0, split);
  const message = split < 0 ? '' : text.slice(split + 2);
  let object = '';
  let type = '';
  let tag = '';
  let tagger = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim();
    else if (line.startsWith('tag ')) tag = line.slice(4).trim();
    else if (line.startsWith('tagger ')) tagger = line.slice(7);
  }
  return { object, type, tag, tagger, message };
}

// ---------------------------------------------------------------- packfiles

const PACK_TYPE_IDS: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
const PACK_TYPE_NUM: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };

function readPackEntryHeader(buf: Buffer, start: number): { typeNum: number; size: number; next: number } {
  let off = start;
  const first = buf[off] ?? 0;
  off += 1;
  const typeNum = (first >> 4) & 0x7;
  let size = first & 0x0f;
  let shift = 4;
  while ((first & 0x80) !== 0 || (buf[off - 1] ?? 0) & 0x80) {
    const b = buf[off] ?? 0;
    off += 1;
    size |= (b & 0x7f) << shift;
    shift += 7;
    if ((b & 0x80) === 0) break;
  }
  return { typeNum, size, next: off };
}
function readOfsBase(buf: Buffer, start: number): { baseOffset: number; next: number } {
  let off = start;
  let b = buf[off] ?? 0;
  off += 1;
  let offset = b & 0x7f;
  while ((b & 0x80) !== 0) {
    b = buf[off] ?? 0;
    off += 1;
    offset = ((offset + 1) << 7) | (b & 0x7f);
  }
  return { baseOffset: offset, next: off };
}
function readVarint(buf: Buffer, start: number): { value: number; next: number } {
  let off = start;
  let value = 0;
  let shift = 0;
  for (;;) {
    const b = buf[off] ?? 0;
    off += 1;
    value |= (b & 0x7f) << shift;
    shift += 7;
    if ((b & 0x80) === 0) break;
  }
  return { value, next: off };
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const src = readVarint(delta, off);
  off = src.next;
  const tgt = readVarint(delta, off);
  off = tgt.next;
  if (src.value !== base.length) throw new Error('delta source size mismatch');
  const out: Buffer[] = [];
  let outLen = 0;
  while (off < delta.length) {
    const op = delta[off] ?? 0;
    off += 1;
    if ((op & 0x80) !== 0) {
      let cpOff = 0;
      let cpSize = 0;
      for (let i = 0; i < 4; i += 1) {
        if ((op & (1 << i)) !== 0) {
          cpOff |= (delta[off] ?? 0) << (i * 8);
          off += 1;
        }
      }
      for (let i = 0; i < 3; i += 1) {
        if ((op & (0x10 << i)) !== 0) {
          cpSize |= (delta[off] ?? 0) << (i * 8);
          off += 1;
        }
      }
      if (cpSize === 0) cpSize = 0x10000;
      out.push(base.subarray(cpOff, cpOff + cpSize));
      outLen += cpSize;
    } else if (op !== 0) {
      out.push(delta.subarray(off, off + op));
      outLen += op;
      off += op;
    } else {
      throw new Error('delta op 0');
    }
  }
  if (outLen !== tgt.value) throw new Error('delta target size mismatch');
  return Buffer.concat(out);
}

/**
 * Parse a packfile. `resolveBase` answers bases that are not in this pack
 * (the server's own object store, for thin packs). Returns the objects keyed
 * by their recomputed ids.
 */
function readPack(pack: Buffer, resolveBase?: (oid: string) => GitObject | undefined): Map<string, GitObject> {
  if (pack.length < 32 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('bad pack header');
  const count = pack.readUInt32BE(8);
  const objects = new Map<string, GitObject>();
  const byOffset = new Map<number, GitObject>();
  let off = 12;
  for (let i = 0; i < count; i += 1) {
    const entryStart = off;
    const header = readPackEntryHeader(pack, off);
    off = header.next;
    let typeNum = header.typeNum;
    let data: Buffer;
    let base: GitObject | undefined;
    if (typeNum === 6) {
      const ofs = readOfsBase(pack, off);
      off = ofs.next;
      const baseObj = byOffset.get(entryStart - ofs.baseOffset);
      if (!baseObj) throw new Error('ofs-delta base missing');
      const inflated = inflateAt(pack, off, header.size);
      off = inflated.next;
      data = applyDelta(baseObj.data, inflated.data);
      typeNum = PACK_TYPE_NUM[baseObj.type] ?? 0;
    } else if (typeNum === 7) {
      const baseOid = pack.subarray(off, off + 20).toString('hex');
      off += 20;
      const inflated = inflateAt(pack, off, header.size);
      data = inflated.data;
      off = inflated.next;
      base = objects.get(baseOid) ?? resolveBase?.(baseOid);
      if (!base) throw new Error(`ref-delta base ${baseOid} missing`);
      data = applyDelta(base.data, data);
      typeNum = PACK_TYPE_NUM[base.type] ?? 0;
    } else {
      const inflated = inflateAt(pack, off, header.size);
      data = inflated.data;
      off = inflated.next;
    }
    const type = PACK_TYPE_IDS[typeNum];
    if (!type) throw new Error(`unknown pack object type ${typeNum}`);
    const oid = hashObject(type, data);
    const obj: GitObject = { type, data };
    objects.set(oid, obj);
    byOffset.set(entryStart, obj);
  }
  return objects;
}

/**
 * Inflate one zlib stream starting at `off` and return the data plus the
 * offset just past the stream. inflateSync ignores trailing bytes, so the
 * end is found by binary search for the smallest end that inflates to the
 * header's declared size (the predicate is monotonic: a truncated stream
 * throws, a complete one inflates to exactly `expectedSize`).
 */
function inflateAt(buf: Buffer, off: number, expectedSize: number): { data: Buffer; next: number } {
  const tryEnd = (end: number): Buffer | null => {
    try {
      const data = inflateSync(buf.subarray(off, end));
      return data.length === expectedSize ? data : null;
    } catch {
      return null;
    }
  };
  // Exponential phase: find an upper bound that inflates (or the buffer end).
  let hi = buf.length;
  let probe = off + 16;
  let found: { data: Buffer; next: number } | null = null;
  while (probe < hi) {
    const data = tryEnd(probe);
    if (data !== null) {
      hi = probe;
      found = { data, next: probe };
      break;
    }
    probe = Math.min(hi, probe * 2);
  }
  // Binary search for the smallest end that inflates to the declared size.
  // (If the true end is exactly the exponential bound, no mid ever succeeds
  // and `found` keeps the exponential-phase result.)
  let lo = off + 1;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    const data = tryEnd(mid);
    if (data !== null) {
      hi = mid;
      found = { data, next: mid };
    } else {
      lo = mid + 1;
    }
  }
  if (found === null) throw new Error('corrupt zlib stream in pack');
  return found;
}

function writePackObjectHeader(typeNum: number, size: number): Buffer {
  const bytes: number[] = [];
  let first = (typeNum << 4) | (size & 0x0f);
  size >>= 4;
  if (size > 0) first |= 0x80;
  bytes.push(first);
  while (size > 0) {
    let b = size & 0x7f;
    size >>= 7;
    if (size > 0) b |= 0x80;
    bytes.push(b);
  }
  return Buffer.from(bytes);
}

/** Build a packfile (version 2, no deltas) from full objects. */
function writePack(objects: readonly GitObject[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const object of objects) {
    parts.push(writePackObjectHeader(PACK_TYPE_NUM[object.type], object.data.length));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  const trailer = Buffer.from(sha1(body), 'hex');
  return Buffer.concat([body, trailer]);
}

// ---------------------------------------------------------------- store

interface Issue {
  id: string; // global (Relay) id, opaque
  dbId: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  comments: { id: number; nodeId: string; body: string; createdAt: string }[];
  createdSeq: number;
  createdAt: string;
  updatedAt: string;
}

interface PullFile {
  filename: string;
  status: 'added' | 'modified' | 'removed';
  additions: number;
  deletions: number;
  changes: number;
}

interface Pull {
  id: string;
  dbId: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  headRef: string;
  baseRef: string;
  headSha: string;
  baseSha: string;
  mergeBaseSha: string;
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  files: PullFile[];
  createdSeq: number;
  createdAt: string;
  updatedAt: string;
}

interface Repo {
  dbId: number;
  globalId: string;
  owner: string;
  name: string;
  description: string;
  private: boolean;
  defaultBranch: string;
  createdSeq: number;
  createdAt: string;
  updatedAt: string;
  objects: Map<string, GitObject>;
  refs: Map<string, string>;
  labels: Map<string, { name: string; color: string }>;
  issues: Map<number, Issue>;
  issueSeq: number;
  issueDbSeq: number;
  commentDbSeq: number;
  pulls: Map<number, Pull>;
  pullSeq: number;
  pullDbSeq: number;
}

const repos = new Map<string, Repo>();
let repoDbSeq = 0;
let globalSeq = 0;

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}
function repoGlobalId(owner: string, name: string): string {
  return b64url(`repo:${owner}/${name}`);
}
function issueGlobalId(owner: string, name: string, number: number): string {
  return b64url(`issue:${owner}/${name}/${number}`);
}
function pullGlobalId(owner: string, name: string, number: number): string {
  return b64url(`pr:${owner}/${name}/${number}`);
}
function commentGlobalId(owner: string, name: string, issueNumber: number, commentId: number): string {
  return b64url(`comment:${owner}/${name}/${issueNumber}/${commentId}`);
}

function createRepoRecord(owner: string, name: string, opts: { description?: string; private?: boolean }): Repo {
  repoDbSeq += 1;
  globalSeq += 1;
  const now = nextIso();
  const repo: Repo = {
    dbId: repoDbSeq,
    globalId: repoGlobalId(owner, name),
    owner,
    name,
    description: opts.description ?? '',
    private: opts.private ?? false,
    defaultBranch: DEFAULT_BRANCH,
    createdSeq: globalSeq,
    createdAt: now,
    updatedAt: now,
    objects: new Map(),
    refs: new Map(),
    labels: new Map(),
    issues: new Map(),
    issueSeq: 0,
    issueDbSeq: 0,
    commentDbSeq: 0,
    pulls: new Map(),
    pullSeq: 0,
    pullDbSeq: 0,
  };
  repos.set(repoKey(owner, name), repo);
  return repo;
}

function getRepo(owner: string, name: string): Repo | undefined {
  return repos.get(repoKey(owner, name));
}
function deleteRepo(owner: string, name: string): boolean {
  return repos.delete(repoKey(owner, name));
}

// ---------------------------------------------------------------- git model

function putObject(repo: Repo, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}
function getObject(repo: Repo, oid: string): GitObject | undefined {
  return repo.objects.get(oid);
}
function refTip(repo: Repo, ref: string): string | undefined {
  return repo.refs.get(ref);
}
function branchTip(repo: Repo, branch: string): string | undefined {
  return repo.refs.get(`refs/heads/${branch}`);
}

/** Resolve a ref-ish (branch name, full ref, or commit oid) to a commit oid. */
function resolveRef(repo: Repo, ref: string): string | undefined {
  if (isOid(ref)) return repo.objects.has(ref) ? ref : undefined;
  if (ref.startsWith('refs/')) return repo.refs.get(ref);
  return repo.refs.get(`refs/heads/${ref}`);
}

/** Walk commit parents from `tip` (newest first, deduped). */
function walkCommits(repo: Repo, tip: string): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  const stack: string[] = [tip];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    out.push(oid);
    const view = parseCommit(obj.data);
    for (const parent of view.parents) stack.push(parent);
  }
  return out;
}

/** All ancestors of `tip` (including itself). */
function ancestors(repo: Repo, tip: string): Set<string> {
  return new Set(walkCommits(repo, tip));
}

/** The merge-base of two commits: the first common ancestor found walking from `a`. */
function mergeBase(repo: Repo, a: string, b: string): string | undefined {
  const bAnc = ancestors(repo, b);
  for (const oid of walkCommits(repo, a)) {
    if (bAnc.has(oid)) return oid;
  }
  return undefined;
}

/** Flatten a tree (recursively) into path -> {mode, oid}. */
function flattenTree(repo: Repo, treeOid: string | undefined, prefix = ''): Map<string, { mode: string; oid: string }> {
  const out = new Map<string, { mode: string; oid: string }>();
  if (!treeOid) return out;
  const obj = repo.objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const entry of parseTree(obj.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (entry.mode === '40000') {
      for (const [p, v] of flattenTree(repo, entry.oid, path)) out.set(p, v);
    } else {
      out.set(path, { mode: entry.mode, oid: entry.oid });
    }
  }
  return out;
}

/** Rebuild nested trees from a flat path map; stores the trees; returns the root oid. */
function buildTreeFromFlat(repo: Repo, flat: Map<string, { mode: string; oid: string }>): string {
  interface Node {
    files: Map<string, { mode: string; oid: string }>;
    dirs: Map<string, Node>;
  }
  const make = (): Node => ({ files: new Map(), dirs: new Map() });
  const root = make();
  for (const [path, value] of flat) {
    const segments = path.split('/');
    let node = root;
    for (let i = 0; i < segments.length - 1; i += 1) {
      const seg = segments[i] as string;
      if (!node.dirs.has(seg)) node.dirs.set(seg, make());
      node = node.dirs.get(seg) as Node;
    }
    node.files.set(segments[segments.length - 1] as string, value);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, value] of node.files) entries.push({ mode: value.mode, name, oid: value.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    return putObject(repo, 'tree', buildTree(entries));
  };
  return build(root);
}

/** Set or delete one path in a tree; returns the new root tree oid. */
function updateTreePath(repo: Repo, baseTreeOid: string | undefined, path: string, value: { mode: string; oid: string } | null): string {
  const flat = flattenTree(repo, baseTreeOid);
  if (value === null) flat.delete(path);
  else flat.set(path, value);
  return buildTreeFromFlat(repo, flat);
}

/** Read one file's blob from a tree. */
function readTreePath(repo: Repo, treeOid: string | undefined, path: string): { mode: string; oid: string } | undefined {
  return flattenTree(repo, treeOid).get(path);
}

/** All objects reachable from `tips` (commits, trees, blobs, tags). */
function collectReachable(repo: Repo, tips: Iterable<string>): Set<string> {
  const out = new Set<string>();
  const stack: string[] = [...tips];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (out.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (!obj) continue;
    out.add(oid);
    if (obj.type === 'commit') {
      const view = parseCommit(obj.data);
      stack.push(view.tree);
      for (const parent of view.parents) stack.push(parent);
    } else if (obj.type === 'tree') {
      for (const entry of parseTree(obj.data)) stack.push(entry.oid);
    } else if (obj.type === 'tag') {
      stack.push(parseTag(obj.data).object);
    }
  }
  return out;
}

/**
 * Objects to send for a fetch: closure(wants) minus closure(haves), honouring
 * depth and the client's shallow boundaries. Returns the objects, the new
 * shallow boundary commits and the newly-unshallowed commits.
 */
function fetchSelection(
  repo: Repo,
  wants: readonly string[],
  haves: readonly string[],
  shallowBoundaries: readonly string[],
  depth: number | undefined,
): { objects: Map<string, GitObject>; shallow: string[]; unshallow: string[] } {
  const shallowSet = new Set(shallowBoundaries);
  // Held objects: full closure of each have, except shallow boundaries, which
  // are leaves (only the commit itself plus its tree/blobs).
  const held = new Set<string>();
  for (const have of haves) {
    if (shallowSet.has(have)) {
      const obj = repo.objects.get(have);
      if (!obj) continue;
      held.add(have);
      if (obj.type === 'commit') {
        const view = parseCommit(obj.data);
        // Leaf: the commit plus its full tree closure (trees and blobs).
        for (const oid of collectReachable(repo, [view.tree])) held.add(oid);
      }
    } else {
      for (const oid of collectReachable(repo, [have])) held.add(oid);
    }
  }
  // Included: depth-limited closure of the wants.
  const included = new Set<string>();
  const includedCommits = new Set<string>();
  const queue: Array<{ oid: string; gen: number }> = [];
  for (const want of wants) {
    const obj = repo.objects.get(want);
    if (!obj) continue;
    if (obj.type === 'tag') {
      included.add(want);
      const target = parseTag(obj.data).object;
      const targetObj = repo.objects.get(target);
      if (targetObj?.type === 'commit') queue.push({ oid: target, gen: 0 });
      else if (targetObj) {
        for (const oid of collectReachable(repo, [target])) included.add(oid);
      }
    } else if (obj.type === 'commit') {
      queue.push({ oid: want, gen: 0 });
    } else {
      for (const oid of collectReachable(repo, [want])) included.add(oid);
    }
  }
  const maxGen = depth === undefined ? Number.POSITIVE_INFINITY : depth;
  const seenGen = new Map<string, number>();
  while (queue.length > 0) {
    const { oid, gen } = queue.shift() as { oid: string; gen: number };
    if (gen >= maxGen) continue;
    const prev = seenGen.get(oid);
    if (prev !== undefined && prev <= gen) continue;
    seenGen.set(oid, gen);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    included.add(oid);
    includedCommits.add(oid);
    const view = parseCommit(obj.data);
    // The commit's whole tree closure: root tree, nested trees, and blobs.
    for (const treeOid of collectReachable(repo, [view.tree])) included.add(treeOid);
    for (const parent of view.parents) queue.push({ oid: parent, gen: gen + 1 });
  }
  const send = new Map<string, GitObject>();
  for (const oid of included) {
    if (held.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (obj) send.set(oid, obj);
  }
  // Shallow boundaries: included commits whose parents are not all included.
  const shallow: string[] = [];
  for (const oid of includedCommits) {
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    const view = parseCommit(obj.data);
    if (view.parents.length > 0 && view.parents.some((p) => !includedCommits.has(p))) shallow.push(oid);
  }
  // Unshallow: previously shallow boundaries that are now fully included.
  const unshallow: string[] = [];
  for (const boundary of shallowBoundaries) {
    if (!includedCommits.has(boundary)) continue;
    const obj = repo.objects.get(boundary);
    if (!obj || obj.type !== 'commit') continue;
    const view = parseCommit(obj.data);
    if (view.parents.every((p) => includedCommits.has(p))) unshallow.push(boundary);
  }
  return { objects: send, shallow, unshallow };
}

/** Diff two flat trees; returns changed paths with old/new blob oids. */
function diffTrees(
  oldFlat: Map<string, { mode: string; oid: string }>,
  newFlat: Map<string, { mode: string; oid: string }>,
): Array<{ path: string; oldOid: string | null; newOid: string | null }> {
  const out: Array<{ path: string; oldOid: string | null; newOid: string | null }> = [];
  const paths = new Set([...oldFlat.keys(), ...newFlat.keys()]);
  for (const path of [...paths].sort()) {
    const oldOid = oldFlat.get(path)?.oid ?? null;
    const newOid = newFlat.get(path)?.oid ?? null;
    if (oldOid !== newOid) out.push({ path, oldOid, newOid });
  }
  return out;
}

/** Line counts for a file change (multiset line diff). */
function lineDiff(oldData: Buffer | null, newData: Buffer | null): { additions: number; deletions: number } {
  const linesOf = (data: Buffer | null): string[] => {
    if (data === null) return [];
    const text = data.toString('utf8');
    const lines = text.split('\n');
    if (lines.length > 0 && lines[lines.length - 1] === '') lines.pop();
    return lines;
  };
  const oldLines = linesOf(oldData);
  const newLines = linesOf(newData);
  const oldCount = new Map<string, number>();
  for (const line of oldLines) oldCount.set(line, (oldCount.get(line) ?? 0) + 1);
  let additions = 0;
  for (const line of newLines) {
    const left = oldCount.get(line) ?? 0;
    if (left > 0) oldCount.set(line, left - 1);
    else additions += 1;
  }
  let deletions = 0;
  for (const left of oldCount.values()) deletions += left;
  return { additions, deletions };
}

/** Build the PullFile list for a merge-base -> head diff. */
function pullFilesFor(repo: Repo, mergeBaseOid: string | undefined, headOid: string): PullFile[] {
  const baseTree = mergeBaseOid === undefined ? undefined : parseCommit(repo.objects.get(mergeBaseOid)?.data ?? Buffer.alloc(0)).tree;
  const headTree = parseCommit(repo.objects.get(headOid)?.data ?? Buffer.alloc(0)).tree;
  const oldFlat = flattenTree(repo, baseTree);
  const newFlat = flattenTree(repo, headTree);
  const files: PullFile[] = [];
  for (const change of diffTrees(oldFlat, newFlat)) {
    const oldData = change.oldOid === null ? null : (repo.objects.get(change.oldOid)?.data ?? null);
    const newData = change.newOid === null ? null : (repo.objects.get(change.newOid)?.data ?? null);
    const { additions, deletions } = lineDiff(oldData, newData);
    const status = change.oldOid === null ? 'added' : change.newOid === null ? 'removed' : 'modified';
    files.push({ filename: change.path, status, additions, deletions, changes: additions + deletions });
  }
  return files;
}

/** Would merging `headOid` onto `baseTipOid` (merge-base `baseOid`) conflict? */
function mergeConflicts(repo: Repo, baseOid: string | undefined, baseTipOid: string, headOid: string): boolean {
  const baseTree = baseOid === undefined ? undefined : parseCommit(repo.objects.get(baseOid)?.data ?? Buffer.alloc(0)).tree;
  const baseTipTree = parseCommit(repo.objects.get(baseTipOid)?.data ?? Buffer.alloc(0)).tree;
  const headTree = parseCommit(repo.objects.get(headOid)?.data ?? Buffer.alloc(0)).tree;
  const baseFlat = flattenTree(repo, baseTree);
  const tipFlat = flattenTree(repo, baseTipTree);
  const headFlat = flattenTree(repo, headTree);
  for (const change of diffTrees(baseFlat, headFlat)) {
    const baseVal = baseFlat.get(change.path)?.oid ?? null;
    const tipVal = tipFlat.get(change.path)?.oid ?? null;
    const headVal = change.newOid;
    if (tipVal !== baseVal && headVal !== baseVal && tipVal !== headVal) return true;
  }
  return false;
}

/** Create a commit on `branch` from a tree change; returns the new commit oid. */
function commitOnBranch(
  repo: Repo,
  branch: string,
  message: string,
  mutate: (flat: Map<string, { mode: string; oid: string }>) => void,
): string {
  const tip = branchTip(repo, branch);
  const baseTree = tip === undefined ? undefined : parseCommit(repo.objects.get(tip)?.data ?? Buffer.alloc(0)).tree;
  const flat = flattenTree(repo, baseTree);
  mutate(flat);
  const treeOid = buildTreeFromFlat(repo, flat);
  const ident = `${VIEWER_NAME} <${VIEWER_EMAIL}>`;
  const commitData = buildCommit({
    tree: treeOid,
    parents: tip === undefined ? [] : [tip],
    message: message.endsWith('\n') ? message : `${message}\n`,
    author: ident,
    committer: ident,
    timestamp: nextEpochSec(),
  });
  const commitOid = putObject(repo, 'commit', commitData);
  repo.refs.set(`refs/heads/${branch}`, commitOid);
  return commitOid;
}

// ---------------------------------------------------------------- http core

let requestSeq = 0;
function nextRequestId(): string {
  requestSeq += 1;
  return `req_${Date.now().toString(36)}_${requestSeq}`;
}

function sendJson(res: http.ServerResponse, status: number, value: unknown, extraHeaders: Record<string, string> = {}): void {
  const body = jsonBody(value);
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'x-github-request-id': nextRequestId(),
    ...extraHeaders,
  });
  res.end(body);
}
function sendError(res: http.ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}
function sendRaw(res: http.ServerResponse, status: number, contentType: string, body: Buffer): void {
  res.writeHead(status, {
    'content-type': contentType,
    'x-github-request-id': nextRequestId(),
  });
  res.end(body);
}

const MAX_BODY = 64 * 1024 * 1024;
function readBody(req: http.IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (chunk: Buffer) => {
      total += chunk.length;
      if (total > MAX_BODY) {
        reject(new Error('request body too large'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

class HttpError extends Error {
  status: number;
  constructor(status: number, message: string) {
    super(message);
    this.status = status;
  }
}

async function parseJsonBody(req: http.IncomingMessage): Promise<Record<string, unknown>> {
  const raw = await readBody(req);
  if (raw.length === 0) return {};
  try {
    const parsed: unknown = JSON.parse(raw.toString('utf8'));
    if (parsed === null || typeof parsed !== 'object' || Array.isArray(parsed)) {
      throw new HttpError(400, 'Invalid JSON body');
    }
    return parsed as Record<string, unknown>;
  } catch (err) {
    if (err instanceof HttpError) throw err;
    throw new HttpError(400, 'Invalid JSON body');
  }
}

/** Auth for /api/v3, /api/graphql and /mcp. Returns true when authorised. */
function checkAuth(req: http.IncomingMessage, res: http.ServerResponse): boolean {
  const header = req.headers.authorization ?? '';
  const match = /^Bearer\s+(.+)$/.exec(header);
  if (!match) {
    sendError(res, 401, 'Requires authentication');
    return false;
  }
  if (TOKEN !== '' && match[1] !== TOKEN) {
    sendError(res, 401, 'Bad credentials');
    return false;
  }
  return true;
}

function queryInt(query: URLSearchParams, name: string, fallback: number): number {
  const raw = query.get(name);
  if (raw === null) return fallback;
  const n = Number.parseInt(raw, 10);
  return Number.isFinite(n) && n > 0 ? n : fallback;
}

/** Paginate a list; returns the page slice and a Link header value (or ''). */
function paginate<T>(items: readonly T[], query: URLSearchParams, baseUrl: string): { page: T[]; link: string } {
  const perPage = Math.min(Math.max(queryInt(query, 'per_page', 30), 1), 100);
  const pageNum = queryInt(query, 'page', 1);
  const start = (pageNum - 1) * perPage;
  const page = items.slice(start, start + perPage);
  let link = '';
  if (start + perPage < items.length) {
    const next = new URL(baseUrl);
    next.searchParams.set('per_page', String(perPage));
    next.searchParams.set('page', String(pageNum + 1));
    link = `<${next.toString()}>; rel="next"`;
  }
  return { page, link };
}

function absoluteUrl(req: http.IncomingMessage, path: string): string {
  const host = req.headers.host ?? 'localhost';
  return `http://${host}${path}`;
}

// ---------------------------------------------------------------- REST shapes

function repoJson(repo: Repo): Record<string, unknown> {
  return {
    id: repo.globalId,
    databaseId: repo.dbId,
    node_id: repo.globalId,
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: VIEWER_ID, type: 'User' },
    private: repo.private,
    description: repo.description,
    default_branch: repo.defaultBranch,
    created_at: repo.createdAt,
    updated_at: repo.updatedAt,
    pushed_at: repo.updatedAt,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}`,
    clone_url: `https://example.invalid/${repo.owner}/${repo.name}.git`,
    has_issues: true,
    has_pull_requests: true,
    has_projects: false,
    has_wiki: false,
    fork: false,
    archived: false,
    disabled: false,
    visibility: repo.private ? 'private' : 'public',
    open_issues_count: [...repo.issues.values()].filter((i) => i.state === 'open').length,
  };
}

function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: issue.id,
    databaseId: issue.dbId,
    node_id: issue.id,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => ({ name, color: repo.labels.get(name)?.color ?? 'ffffff' })),
    user: { login: VIEWER_LOGIN, id: VIEWER_ID },
    assignee: null,
    created_at: issue.createdAt,
    updated_at: issue.updatedAt,
    closed_at: issue.state === 'closed' ? issue.updatedAt : null,
    comments: issue.comments.length,
  };
}

function pullMergeable(repo: Repo, pull: Pull): boolean {
  const baseTip = branchTip(repo, pull.baseRef);
  if (baseTip === undefined) return false;
  return !mergeConflicts(repo, pull.mergeBaseSha, baseTip, pull.headSha);
}

function pullJson(repo: Repo, pull: Pull): Record<string, unknown> {
  return {
    id: pull.id,
    databaseId: pull.dbId,
    node_id: pull.id,
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    locked: false,
    draft: false,
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: pullMergeable(repo, pull),
    mergeable_state: pullMergeable(repo, pull) ? 'clean' : 'dirty',
    head: { ref: pull.headRef, sha: pull.headSha, label: `${repo.owner}:${pull.headRef}` },
    base: { ref: pull.baseRef, sha: pull.baseSha, label: `${repo.owner}:${pull.baseRef}` },
    user: { login: VIEWER_LOGIN, id: VIEWER_ID },
    created_at: pull.createdAt,
    updated_at: pull.updatedAt,
    closed_at: pull.state === 'closed' ? pull.updatedAt : null,
    commits: 1,
    additions: pull.files.reduce((sum, f) => sum + f.additions, 0),
    deletions: pull.files.reduce((sum, f) => sum + f.deletions, 0),
    changed_files: pull.files.length,
  };
}

function branchJson(name: string, sha: string): Record<string, unknown> {
  return { name, commit: { sha, url: '' }, protected: false };
}

// ---------------------------------------------------------------- REST handlers

async function handleRest(req: http.IncomingMessage, res: http.ServerResponse, url: URL): Promise<void> {
  const method = req.method ?? 'GET';
  const path = url.pathname;
  const seg = path.split('/').filter((s) => s.length > 0);
  // seg[0] === 'api', seg[1] === 'v3'
  const rest = seg.slice(2);
  const origin = absoluteUrl(req, path);

  // GET /api/v3/ and /api/v3
  if (rest.length === 0) {
    if (method !== 'GET') return sendError(res, 404, 'Not Found');
    return sendJson(res, 200, { current_user_url: `${origin}/user` }, { 'x-oauth-scopes': 'repo, read:org' });
  }
  // GET /api/v3/meta
  if (rest.length === 1 && rest[0] === 'meta') {
    if (method !== 'GET') return sendError(res, 404, 'Not Found');
    return sendJson(res, 200, { installed_version: FORGE_VERSION });
  }
  // GET /api/v3/user
  if (rest.length === 1 && rest[0] === 'user') {
    if (method !== 'GET') return sendError(res, 404, 'Not Found');
    return sendJson(res, 200, {
      login: VIEWER_LOGIN,
      id: VIEWER_ID,
      node_id: b64url(`user:${VIEWER_LOGIN}`),
      name: VIEWER_NAME,
      email: VIEWER_EMAIL,
      type: 'User',
    });
  }
  // POST /api/v3/user/repos ; GET /api/v3/user/repos
  if (rest.length === 2 && rest[0] === 'user' && rest[1] === 'repos') {
    if (method === 'POST') {
      const body = await parseJsonBody(req);
      const name = body.name;
      if (typeof name !== 'string' || name.length === 0) throw new HttpError(422, 'name is required');
      if (getRepo(VIEWER_LOGIN, name) !== undefined) throw new HttpError(422, 'Repository already exists');
      const repo = createRepoRecord(VIEWER_LOGIN, name, {
        description: typeof body.description === 'string' ? body.description : undefined,
        private: body.private === true,
      });
      return sendJson(res, 201, repoJson(repo));
    }
    if (method === 'GET') {
      const all = [...repos.values()]
        .filter((r) => r.owner === VIEWER_LOGIN)
        .sort((a, b) => a.createdSeq - b.createdSeq)
        .map(repoJson);
      const { page, link } = paginate(all, url.searchParams, origin);
      return sendJson(res, 200, page, link === '' ? {} : { link });
    }
    return sendError(res, 404, 'Not Found');
  }
  // /api/v3/repos/{owner}/{repo}[...]
  if (rest.length >= 3 && rest[0] === 'repos') {
    const owner = rest[1] as string;
    const name = rest[2] as string;
    const tail = rest.slice(3);
    const repo = getRepo(owner, name);
    if (tail.length === 0) {
      if (method === 'GET') {
        if (repo === undefined) return sendError(res, 404, 'Not Found');
        return sendJson(res, 200, repoJson(repo));
      }
      if (method === 'PATCH') {
        if (repo === undefined) return sendError(res, 404, 'Not Found');
        const body = await parseJsonBody(req);
        if (typeof body.description === 'string') repo.description = body.description;
        if (typeof body.private === 'boolean') repo.private = body.private;
        repo.updatedAt = nextIso();
        return sendJson(res, 200, repoJson(repo));
      }
      if (method === 'DELETE') {
        if (repo === undefined) return sendError(res, 404, 'Not Found');
        deleteRepo(owner, name);
        res.writeHead(204, { 'x-github-request-id': nextRequestId() });
        return res.end();
      }
      return sendError(res, 404, 'Not Found');
    }
    if (repo === undefined) return sendError(res, 404, 'Not Found');
    return handleRepoSub(req, res, url, repo, tail, origin);
  }
  return sendError(res, 404, 'Not Found');
}

async function handleRepoSub(
  req: http.IncomingMessage,
  res: http.ServerResponse,
  url: URL,
  repo: Repo,
  tail: string[],
  origin: string,
): Promise<void> {
  const method = req.method ?? 'GET';

  // git refs ------------------------------------------------------------
  if (tail[0] === 'git' && tail[1] === 'refs') {
    if (method === 'POST' && tail.length === 2) {
      const body = await parseJsonBody(req);
      const ref = body.ref;
      const sha = body.sha;
      if (typeof ref !== 'string' || typeof sha !== 'string' || !isOid(sha)) {
        throw new HttpError(422, 'ref and sha are required');
      }
      if (repo.objects.get(sha) === undefined) throw new HttpError(422, 'sha not found');
      repo.refs.set(ref, sha);
      return sendJson(res, 201, { ref, object: { sha } });
    }
    if (method === 'GET' && tail.length >= 3) {
      const ref = tail.join('/');
      const sha = repo.refs.get(ref);
      if (sha === undefined) return sendError(res, 404, 'Not Found');
      return sendJson(res, 200, { ref, object: { sha } });
    }
    return sendError(res, 404, 'Not Found');
  }
  // branches ------------------------------------------------------------
  if (tail[0] === 'branches') {
    if (method === 'GET' && tail.length === 1) {
      const list = [...repo.refs.entries()]
        .filter(([ref]) => ref.startsWith('refs/heads/'))
        .map(([ref, sha]) => branchJson(ref.slice('refs/heads/'.length), sha));
      return sendJson(res, 200, list);
    }
    if (method === 'GET' && tail.length === 2) {
      const sha = branchTip(repo, tail[1] as string);
      if (sha === undefined) return sendError(res, 404, 'Not Found');
      return sendJson(res, 200, branchJson(tail[1] as string, sha));
    }
    return sendError(res, 404, 'Not Found');
  }
  // commits -------------------------------------------------------------
  if (tail[0] === 'commits') {
    if (method !== 'GET') return sendError(res, 404, 'Not Found');
    const shaParam = url.searchParams.get('sha');
    const tip = shaParam === null ? branchTip(repo, repo.defaultBranch) : resolveRef(repo, shaParam);
    if (tip === undefined) return sendJson(res, 200, []);
    const commits = walkCommits(repo, tip).map((oid) => {
      const view = parseCommit(repo.objects.get(oid)?.data ?? Buffer.alloc(0));
      // GitHub strips the trailing newline from commit messages.
      return { sha: oid, commit: { message: view.message.replace(/\n+$/, '') } };
    });
    const { page, link } = paginate(commits, url.searchParams, origin);
    return sendJson(res, 200, page, link === '' ? {} : { link });
  }
  // contents ------------------------------------------------------------
  if (tail[0] === 'contents') {
    const path = tail.slice(1).map(decodeURIComponent).join('/');
    return handleContents(req, res, url, repo, path);
  }
  // labels --------------------------------------------------------------
  if (tail[0] === 'labels') {
    if (method === 'POST' && tail.length === 1) {
      const body = await parseJsonBody(req);
      const name = body.name;
      if (typeof name !== 'string' || name.length === 0) throw new HttpError(422, 'name is required');
      if (repo.labels.has(name)) throw new HttpError(422, 'Label already exists');
      const color = typeof body.color === 'string' ? body.color : 'ffffff';
      repo.labels.set(name, { name, color });
      return sendJson(res, 201, { name, color });
    }
    if (method === 'GET' && tail.length === 1) {
      return sendJson(res, 200, [...repo.labels.values()]);
    }
    return sendError(res, 404, 'Not Found');
  }
  // issues --------------------------------------------------------------
  if (tail[0] === 'issues') {
    return handleIssues(req, res, url, repo, tail.slice(1), origin);
  }
  // pulls ---------------------------------------------------------------
  if (tail[0] === 'pulls') {
    return handlePulls(req, res, url, repo, tail.slice(1), origin);
  }
  return sendError(res, 404, 'Not Found');
}

/** Resolve the branch for a contents operation; auto-creates it from the default tip when missing. */
function contentsBranch(repo: Repo, branchParam: unknown): string {
  const branch = typeof branchParam === 'string' && branchParam.length > 0 ? branchParam : repo.defaultBranch;
  if (branchTip(repo, branch) === undefined) {
    const baseTip = branchTip(repo, repo.defaultBranch);
    if (baseTip !== undefined) repo.refs.set(`refs/heads/${branch}`, baseTip);
  }
  return branch;
}

async function handleContents(
  req: http.IncomingMessage,
  res: http.ServerResponse,
  url: URL,
  repo: Repo,
  path: string,
): Promise<void> {
  const method = req.method ?? 'GET';
  const refParam = url.searchParams.get('ref');

  if (method === 'GET') {
    const tip = refParam === null ? branchTip(repo, repo.defaultBranch) : resolveRef(repo, refParam);
    if (tip === undefined) return sendError(res, 404, 'Not Found');
    const treeOid = parseCommit(repo.objects.get(tip)?.data ?? Buffer.alloc(0)).tree;
    const flat = flattenTree(repo, treeOid);
    if (path === '') {
      // Root directory listing.
      const entries: Record<string, unknown>[] = [];
      const seenDirs = new Set<string>();
      for (const [p, v] of [...flat.entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
        const top = p.split('/')[0] as string;
        if (p.includes('/')) {
          if (!seenDirs.has(top)) {
            seenDirs.add(top);
            entries.push({ type: 'dir', name: top, path: top, sha: '' });
          }
        } else {
          entries.push({ type: 'file', name: top, path: top, sha: v.oid });
        }
      }
      return sendJson(res, 200, entries);
    }
    const file = flat.get(path);
    if (file !== undefined) {
      const blob = repo.objects.get(file.oid);
      if (blob === undefined) return sendError(res, 404, 'Not Found');
      return sendJson(res, 200, {
        type: 'file',
        encoding: 'base64',
        size: blob.data.length,
        name: path.split('/').pop() ?? path,
        path,
        content: b64encode(blob.data),
        sha: file.oid,
      });
    }
    // Directory listing for a sub-path.
    const prefix = `${path}/`;
    const children = [...flat.entries()].filter(([p]) => p.startsWith(prefix));
    if (children.length === 0) return sendError(res, 404, 'Not Found');
    const entries: Record<string, unknown>[] = [];
    const seenDirs = new Set<string>();
    for (const [p, v] of children.sort((a, b) => a[0].localeCompare(b[0]))) {
      const rest = p.slice(prefix.length);
      const top = rest.split('/')[0] as string;
      if (rest.includes('/')) {
        if (!seenDirs.has(top)) {
          seenDirs.add(top);
          entries.push({ type: 'dir', name: top, path: `${path}/${top}`, sha: '' });
        }
      } else {
        entries.push({ type: 'file', name: top, path: p, sha: v.oid });
      }
    }
    return sendJson(res, 200, entries);
  }

  if (method === 'PUT') {
    const body = await parseJsonBody(req);
    const message = typeof body.message === 'string' ? body.message : 'Update file';
    const content = body.content;
    if (typeof content !== 'string') throw new HttpError(422, 'content is required');
    const branch = contentsBranch(repo, body.branch);
    const data = b64decode(content);
    const blobOid = putObject(repo, 'blob', data);
    const tip = branchTip(repo, branch);
    const baseTree = tip === undefined ? undefined : parseCommit(repo.objects.get(tip)?.data ?? Buffer.alloc(0)).tree;
    const flat = flattenTree(repo, baseTree);
    const existing = flat.get(path);
    if (existing !== undefined) {
      if (typeof body.sha === 'string' && body.sha !== existing.oid) {
        throw new HttpError(409, 'sha does not match');
      }
      const commitOid = commitOnBranch(repo, branch, message, (f) => {
        f.set(path, { mode: '100644', oid: blobOid });
      });
      return sendJson(res, 200, {
        content: { name: path.split('/').pop() ?? path, path, sha: blobOid, size: data.length, encoding: 'base64' },
        commit: { sha: commitOid, message },
      });
    }
    const commitOid = commitOnBranch(repo, branch, message, (f) => {
      f.set(path, { mode: '100644', oid: blobOid });
    });
    return sendJson(res, 201, {
      content: { name: path.split('/').pop() ?? path, path, sha: blobOid, size: data.length, encoding: 'base64' },
      commit: { sha: commitOid, message },
    });
  }

  if (method === 'DELETE') {
    const body = await parseJsonBody(req);
    const message = typeof body.message === 'string' ? body.message : 'Delete file';
    const branch = contentsBranch(repo, body.branch);
    const tip = branchTip(repo, branch);
    if (tip === undefined) return sendError(res, 404, 'Not Found');
    const baseTree = parseCommit(repo.objects.get(tip)?.data ?? Buffer.alloc(0)).tree;
    const flat = flattenTree(repo, baseTree);
    const existing = flat.get(path);
    if (existing === undefined) return sendError(res, 404, 'Not Found');
    if (typeof body.sha === 'string' && body.sha !== existing.oid) {
      throw new HttpError(409, 'sha does not match');
    }
    const commitOid = commitOnBranch(repo, branch, message, (f) => {
      f.delete(path);
    });
    return sendJson(res, 200, { commit: { sha: commitOid, message } });
  }
  return sendError(res, 404, 'Not Found');
}

// ---------------------------------------------------------------- issues

async function handleIssues(
  req: http.IncomingMessage,
  res: http.ServerResponse,
  url: URL,
  repo: Repo,
  tail: string[],
  origin: string,
): Promise<void> {
  const method = req.method ?? 'GET';

  // POST /issues  and  GET /issues
  if (tail.length === 0) {
    if (method === 'POST') {
      const body = await parseJsonBody(req);
      const title = body.title;
      if (typeof title !== 'string' || title.length === 0) throw new HttpError(422, 'title is required');
      const labelNames: string[] = Array.isArray(body.labels) ? body.labels.filter((l): l is string => typeof l === 'string') : [];
      for (const label of labelNames) {
        if (!repo.labels.has(label)) throw new HttpError(422, `Label does not exist: ${label}`);
      }
      repo.issueSeq += 1;
      repo.issueDbSeq += 1;
      globalSeq += 1;
      const now = nextIso();
      const issue: Issue = {
        id: issueGlobalId(repo.owner, repo.name, repo.issueSeq),
        dbId: repo.issueDbSeq,
        number: repo.issueSeq,
        title,
        body: typeof body.body === 'string' ? body.body : '',
        state: 'open',
        labels: labelNames,
        comments: [],
        createdSeq: globalSeq,
        createdAt: now,
        updatedAt: now,
      };
      repo.issues.set(issue.number, issue);
      return sendJson(res, 201, issueJson(repo, issue));
    }
    if (method === 'GET') {
      const stateParam = url.searchParams.get('state') ?? 'open';
      const direction = url.searchParams.get('direction') ?? 'desc';
      let list = [...repo.issues.values()];
      if (stateParam !== 'all') list = list.filter((i) => i.state === stateParam);
      list.sort((a, b) => (direction === 'asc' ? a.createdSeq - b.createdSeq : b.createdSeq - a.createdSeq));
      const { page, link } = paginate(list.map((i) => issueJson(repo, i)), url.searchParams, origin);
      return sendJson(res, 200, page, link === '' ? {} : { link });
    }
    return sendError(res, 404, 'Not Found');
  }

  const number = Number.parseInt(tail[0] as string, 10);
  if (!Number.isFinite(number)) return sendError(res, 404, 'Not Found');
  const issue = repo.issues.get(number);

  // /issues/{n}/comments
  if (tail.length === 2 && tail[1] === 'comments') {
    if (issue === undefined) return sendError(res, 404, 'Not Found');
    if (method === 'POST') {
      const body = await parseJsonBody(req);
      if (typeof body.body !== 'string' || body.body.length === 0) throw new HttpError(422, 'body is required');
      repo.commentDbSeq += 1;
      const now = nextIso();
      const comment = {
        id: repo.commentDbSeq,
        nodeId: commentGlobalId(repo.owner, repo.name, number, repo.commentDbSeq),
        body: body.body,
        createdAt: now,
      };
      issue.comments.push(comment);
      issue.updatedAt = now;
      return sendJson(res, 201, {
        id: comment.id,
        node_id: comment.nodeId,
        body: comment.body,
        user: { login: VIEWER_LOGIN, id: VIEWER_ID },
        created_at: comment.createdAt,
        updated_at: comment.createdAt,
      });
    }
    if (method === 'GET') {
      return sendJson(res, 200, issue.comments.map((c) => ({
        id: c.id,
        node_id: c.nodeId,
        body: c.body,
        user: { login: VIEWER_LOGIN, id: VIEWER_ID },
        created_at: c.createdAt,
        updated_at: c.createdAt,
      })));
    }
    return sendError(res, 404, 'Not Found');
  }

  // /issues/{n}
  if (tail.length === 1) {
    if (issue === undefined) return sendError(res, 404, 'Not Found');
    if (method === 'GET') return sendJson(res, 200, issueJson(repo, issue));
    if (method === 'PATCH') {
      const body = await parseJsonBody(req);
      if (typeof body.title === 'string') issue.title = body.title;
      if (typeof body.body === 'string') issue.body = body.body;
      if (body.state === 'open' || body.state === 'closed') issue.state = body.state;
      if (Array.isArray(body.labels)) {
        const labelNames = body.labels.filter((l): l is string => typeof l === 'string');
        for (const label of labelNames) {
          if (!repo.labels.has(label)) throw new HttpError(422, `Label does not exist: ${label}`);
        }
        issue.labels = labelNames;
      }
      issue.updatedAt = nextIso();
      return sendJson(res, 200, issueJson(repo, issue));
    }
    return sendError(res, 404, 'Not Found');
  }
  return sendError(res, 404, 'Not Found');
}

// ---------------------------------------------------------------- pulls

async function handlePulls(
  req: http.IncomingMessage,
  res: http.ServerResponse,
  url: URL,
  repo: Repo,
  tail: string[],
  origin: string,
): Promise<void> {
  const method = req.method ?? 'GET';

  // POST /pulls  and  GET /pulls
  if (tail.length === 0) {
    if (method === 'POST') {
      const body = await parseJsonBody(req);
      const title = body.title;
      const head = body.head;
      const base = body.base;
      if (typeof title !== 'string' || title.length === 0) throw new HttpError(422, 'title is required');
      if (typeof head !== 'string' || typeof base !== 'string') throw new HttpError(422, 'head and base are required');
      const headSha = branchTip(repo, head);
      const baseSha = branchTip(repo, base);
      if (headSha === undefined || baseSha === undefined) throw new HttpError(422, 'head or base branch not found');
      for (const existing of repo.pulls.values()) {
        if (existing.state === 'open' && existing.headRef === head && existing.baseRef === base) {
          throw new HttpError(422, 'A pull request already exists for this head and base');
        }
      }
      const baseOid = mergeBase(repo, headSha, baseSha);
      repo.pullSeq += 1;
      repo.pullDbSeq += 1;
      globalSeq += 1;
      const now = nextIso();
      const pull: Pull = {
        id: pullGlobalId(repo.owner, repo.name, repo.pullSeq),
        dbId: repo.pullDbSeq,
        number: repo.pullSeq,
        title,
        body: typeof body.body === 'string' ? body.body : '',
        state: 'open',
        headRef: head,
        baseRef: base,
        headSha,
        baseSha,
        mergeBaseSha: baseOid ?? baseSha,
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
        files: pullFilesFor(repo, baseOid, headSha),
        createdSeq: globalSeq,
        createdAt: now,
        updatedAt: now,
      };
      repo.pulls.set(pull.number, pull);
      return sendJson(res, 201, pullJson(repo, pull));
    }
    if (method === 'GET') {
      const stateParam = url.searchParams.get('state') ?? 'open';
      let list = [...repo.pulls.values()];
      if (stateParam !== 'all') list = list.filter((p) => p.state === stateParam);
      list.sort((a, b) => b.createdSeq - a.createdSeq);
      const { page, link } = paginate(list.map((p) => pullJson(repo, p)), url.searchParams, origin);
      return sendJson(res, 200, page, link === '' ? {} : { link });
    }
    return sendError(res, 404, 'Not Found');
  }

  const number = Number.parseInt(tail[0] as string, 10);
  if (!Number.isFinite(number)) return sendError(res, 404, 'Not Found');
  const pull = repo.pulls.get(number);

  // GET /pulls/{n}/files
  if (tail.length === 2 && tail[1] === 'files') {
    if (pull === undefined) return sendError(res, 404, 'Not Found');
    if (method !== 'GET') return sendError(res, 404, 'Not Found');
    return sendJson(res, 200, pull.files);
  }
  // PUT /pulls/{n}/merge
  if (tail.length === 2 && tail[1] === 'merge') {
    if (pull === undefined) return sendError(res, 404, 'Not Found');
    if (method !== 'PUT' && method !== 'POST') return sendError(res, 404, 'Not Found');
    const body = await parseJsonBody(req).catch(() => ({} as Record<string, unknown>));
    const mergeMethod = typeof body.merge_method === 'string' ? body.merge_method : 'squash';
    if (pull.merged || pull.state !== 'open') throw new HttpError(405, 'Pull request is not open');
    const commitOid = mergePullRequestInternal(repo, pull, mergeMethod);
    return sendJson(res, 200, {
      sha: commitOid,
      merged: true,
      message: 'Pull request successfully merged',
    });
  }
  // GET /pulls/{n}
  if (tail.length === 1) {
    if (pull === undefined) return sendError(res, 404, 'Not Found');
    if (method !== 'GET') return sendError(res, 404, 'Not Found');
    return sendJson(res, 200, pullJson(repo, pull));
  }
  return sendError(res, 404, 'Not Found');
}

// ---------------------------------------------------------------- merge core

/** Squash/merge a pull request; returns the new commit oid. Throws HttpError(405) on conflict. */
function mergePullRequestInternal(repo: Repo, pull: Pull, mergeMethod: string): string {
  if (mergeMethod !== 'squash' && mergeMethod !== 'merge') throw new HttpError(405, 'Unsupported merge method');
  const baseTip = branchTip(repo, pull.baseRef);
  if (baseTip === undefined) throw new HttpError(405, 'Base branch not found');
  if (mergeConflicts(repo, pull.mergeBaseSha, baseTip, pull.headSha)) {
    throw new HttpError(405, 'Merge conflict');
  }
  const baseTree = parseCommit(repo.objects.get(baseTip)?.data ?? Buffer.alloc(0)).tree;
  const baseFlat = flattenTree(repo, baseTree);
  const headTree = parseCommit(repo.objects.get(pull.headSha)?.data ?? Buffer.alloc(0)).tree;
  const mergeBaseTree = parseCommit(repo.objects.get(pull.mergeBaseSha)?.data ?? Buffer.alloc(0)).tree;
  const mergeBaseFlat = flattenTree(repo, mergeBaseTree);
  const headFlat = flattenTree(repo, headTree);
  for (const change of diffTrees(mergeBaseFlat, headFlat)) {
    if (change.newOid === null) baseFlat.delete(change.path);
    else baseFlat.set(change.path, { mode: headFlat.get(change.path)?.mode ?? '100644', oid: change.newOid });
  }
  const newTree = buildTreeFromFlat(repo, baseFlat);
  const ident = `${VIEWER_NAME} <${VIEWER_EMAIL}>`;
  const parents = mergeMethod === 'merge' ? [baseTip, pull.headSha] : [baseTip];
  const commitData = buildCommit({
    tree: newTree,
    parents,
    message: mergeMethod === 'merge' ? `Merge pull request #${pull.number} from ${pull.headRef}\n` : `${pull.title}\n`,
    author: ident,
    committer: ident,
    timestamp: nextEpochSec(),
  });
  const commitOid = putObject(repo, 'commit', commitData);
  repo.refs.set(`refs/heads/${pull.baseRef}`, commitOid);
  pull.merged = true;
  pull.state = 'closed';
  pull.mergedAt = nextIso();
  pull.mergeCommitSha = commitOid;
  pull.updatedAt = nextIso();
  return commitOid;
}

// ---------------------------------------------------------------- GraphQL

type GqlValue =
  | { kind: 'var'; name: string }
  | { kind: 'enum'; value: string }
  | string
  | number
  | boolean
  | null
  | GqlValue[]
  | { [key: string]: GqlValue };

interface FieldNode {
  kind: 'field';
  name: string;
  alias?: string;
  args: Record<string, GqlValue>;
  selections?: SelectionNode[];
}
interface SpreadNode {
  kind: 'spread';
  name: string;
}
interface InlineNode {
  kind: 'inline';
  typeCondition?: string;
  selections: SelectionNode[];
}
type SelectionNode = FieldNode | SpreadNode | InlineNode;
interface OperationNode {
  kind: 'operation';
  opType: 'query' | 'mutation';
  name?: string;
  variables: Record<string, { defaultValue?: GqlValue }>;
  selections: SelectionNode[];
}
interface FragmentNode {
  kind: 'fragment';
  name: string;
  typeCondition: string;
  selections: SelectionNode[];
}

interface GqlToken {
  kind: 'name' | 'int' | 'float' | 'string' | 'punct' | 'eof';
  value: string;
}

function tokenizeGql(src: string): GqlToken[] {
  const tokens: GqlToken[] = [];
  let i = 0;
  while (i < src.length) {
    const ch = src[i] as string;
    if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',') {
      i += 1;
      continue;
    }
    if (ch === '#') {
      while (i < src.length && src[i] !== '\n') i += 1;
      continue;
    }
    if (ch === '.' && src.slice(i, i + 3) === '...') {
      tokens.push({ kind: 'punct', value: '...' });
      i += 3;
      continue;
    }
    if ('{}():![]$=@'.includes(ch)) {
      tokens.push({ kind: 'punct', value: ch });
      i += 1;
      continue;
    }
    if (ch === '"') {
      let j = i + 1;
      let out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) {
          const esc = src[j + 1] as string;
          out += esc === 'n' ? '\n' : esc === 't' ? '\t' : esc === 'r' ? '\r' : esc;
          j += 2;
        } else {
          out += src[j] as string;
          j += 1;
        }
      }
      tokens.push({ kind: 'string', value: out });
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(ch)) {
      let j = i;
      let isFloat = false;
      while (j < src.length && /[0-9.eE+-]/.test(src[j] as string)) {
        if (src[j] === '.' || src[j] === 'e' || src[j] === 'E') isFloat = true;
        j += 1;
      }
      tokens.push({ kind: isFloat ? 'float' : 'int', value: src.slice(i, j) });
      i = j;
      continue;
    }
    if (/[A-Za-z_]/.test(ch)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j] as string)) j += 1;
      tokens.push({ kind: 'name', value: src.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`Unexpected character in GraphQL: ${ch}`);
  }
  tokens.push({ kind: 'eof', value: '' });
  return tokens;
}

class GqlParser {
  private tokens: GqlToken[];
  private pos = 0;
  constructor(src: string) {
    this.tokens = tokenizeGql(src);
  }
  private peek(): GqlToken {
    return this.tokens[this.pos] as GqlToken;
  }
  private next(): GqlToken {
    const tok = this.tokens[this.pos] as GqlToken;
    this.pos += 1;
    return tok;
  }
  private expect(value: string): GqlToken {
    const tok = this.next();
    if (tok.value !== value) throw new Error(`Expected ${value} but got ${tok.value}`);
    return tok;
  }
  private expectName(): string {
    const tok = this.next();
    if (tok.kind !== 'name') throw new Error(`Expected name but got ${tok.value}`);
    return tok.value;
  }
  parseDocument(): { operations: OperationNode[]; fragments: Map<string, FragmentNode> } {
    const operations: OperationNode[] = [];
    const fragments = new Map<string, FragmentNode>();
    while (this.peek().kind !== 'eof') {
      if (this.peek().value === '{') {
        operations.push({
          kind: 'operation',
          opType: 'query',
          variables: {},
          selections: this.parseSelectionSet(),
        });
      } else if (this.peek().value === 'query' || this.peek().value === 'mutation' || this.peek().value === 'subscription') {
        const opType = this.next().value as 'query' | 'mutation';
        const op: OperationNode = { kind: 'operation', opType, variables: {}, selections: [] };
        if (this.peek().kind === 'name') op.name = this.next().value;
        if (this.peek().value === '(') op.variables = this.parseVariableDefinitions();
        while (this.peek().value === '@') this.parseDirective();
        op.selections = this.parseSelectionSet();
        operations.push(op);
      } else if (this.peek().value === 'fragment') {
        this.next();
        const name = this.expectName();
        this.expect('on');
        const typeCondition = this.expectName();
        while (this.peek().value === '@') this.parseDirective();
        fragments.set(name, { kind: 'fragment', name, typeCondition, selections: this.parseSelectionSet() });
      } else {
        throw new Error(`Unexpected token ${this.peek().value}`);
      }
    }
    return { operations, fragments };
  }
  private parseDirective(): void {
    this.expect('@');
    this.expectName();
    if (this.peek().value === '(') this.parseArguments();
  }
  private parseVariableDefinitions(): Record<string, { defaultValue?: GqlValue }> {
    const out: Record<string, { defaultValue?: GqlValue }> = {};
    this.expect('(');
    while (this.peek().value !== ')') {
      this.expect('$');
      const name = this.expectName();
      this.expect(':');
      this.parseType();
      if (this.peek().value === '=') {
        this.next();
        out[name] = { defaultValue: this.parseValue() };
      } else {
        out[name] = {};
      }
      if (this.peek().value === '@') this.parseDirective();
    }
    this.expect(')');
    return out;
  }
  private parseType(): void {
    if (this.peek().value === '[') {
      this.next();
      this.parseType();
      this.expect(']');
    } else {
      this.expectName();
    }
    if (this.peek().value === '!') this.next();
  }
  private parseSelectionSet(): SelectionNode[] {
    this.expect('{');
    const out: SelectionNode[] = [];
    while (this.peek().value !== '}') {
      out.push(this.parseSelection());
    }
    this.expect('}');
    return out;
  }
  private parseSelection(): SelectionNode {
    if (this.peek().value === '...') {
      this.next();
      if (this.peek().value === 'on') {
        this.next();
        const typeCondition = this.expectName();
        while (this.peek().value === '@') this.parseDirective();
        return { kind: 'inline', typeCondition, selections: this.parseSelectionSet() };
      }
      if (this.peek().kind === 'name') {
        const name = this.next().value;
        while (this.peek().value === '@') this.parseDirective();
        return { kind: 'spread', name };
      }
      return { kind: 'inline', selections: this.parseSelectionSet() };
    }
    const first = this.expectName();
    let name = first;
    let alias: string | undefined;
    if (this.peek().value === ':') {
      this.next();
      alias = first;
      name = this.expectName();
    }
    let args: Record<string, GqlValue> = {};
    if (this.peek().value === '(') args = this.parseArguments();
    while (this.peek().value === '@') this.parseDirective();
    const field: FieldNode = { kind: 'field', name, args };
    if (alias !== undefined) field.alias = alias;
    if (this.peek().value === '{') field.selections = this.parseSelectionSet();
    return field;
  }
  private parseArguments(): Record<string, GqlValue> {
    const out: Record<string, GqlValue> = {};
    this.expect('(');
    while (this.peek().value !== ')') {
      const name = this.expectName();
      this.expect(':');
      out[name] = this.parseValue();
    }
    this.expect(')');
    return out;
  }
  private parseValue(): GqlValue {
    const tok = this.next();
    if (tok.value === '$') return { kind: 'var', name: this.expectName() };
    if (tok.value === '[') {
      const list: GqlValue[] = [];
      while (this.peek().value !== ']') list.push(this.parseValue());
      this.expect(']');
      return list;
    }
    if (tok.value === '{') {
      const obj: Record<string, GqlValue> = {};
      while (this.peek().value !== '}') {
        const name = this.expectName();
        this.expect(':');
        obj[name] = this.parseValue();
      }
      this.expect('}');
      return obj;
    }
    if (tok.kind === 'int') return Number.parseInt(tok.value, 10);
    if (tok.kind === 'float') return Number.parseFloat(tok.value);
    if (tok.kind === 'string') return tok.value;
    if (tok.kind === 'name') {
      if (tok.value === 'true') return true;
      if (tok.value === 'false') return false;
      if (tok.value === 'null') return null;
      return { kind: 'enum', value: tok.value };
    }
    throw new Error(`Unexpected value token ${tok.value}`);
  }
}

function resolveGqlValue(value: GqlValue, variables: Record<string, unknown>): unknown {
  if (value !== null && typeof value === 'object' && !Array.isArray(value)) {
    if ((value as { kind?: string }).kind === 'var') return variables[(value as { name: string }).name];
    if ((value as { kind?: string }).kind === 'enum') return (value as { value: string }).value;
    const out: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(value as Record<string, GqlValue>)) out[k] = resolveGqlValue(v, variables);
    return out;
  }
  if (Array.isArray(value)) return value.map((v) => resolveGqlValue(v, variables));
  return value;
}

function gqlArgs(node: FieldNode, variables: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const [k, v] of Object.entries(node.args)) out[k] = resolveGqlValue(v, variables);
  return out;
}

// ---------------------------------------------------------------- GraphQL schema (introspection data)

const SCHEMA_FIELDS: Record<string, string[]> = {
  User: ['id', 'login', 'name', 'email'],
  Repository: [
    'id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef',
    'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequest', 'pullRequests',
  ],
  Issue: ['id', 'number', 'title', 'state', 'body'],
  PullRequest: ['id', 'number', 'headRefName', 'baseRefName', 'mergeable', 'state', 'merged', 'files'],
  Ref: ['name'],
  IssueConnection: ['nodes', 'pageInfo'],
  PullRequestConnection: ['nodes', 'pageInfo'],
  PullRequestChangedFileConnection: ['nodes', 'pageInfo'],
  PullRequestChangedFile: ['path'],
  PageInfo: ['hasNextPage', 'endCursor', 'hasPreviousPage', 'startCursor'],
  CreateIssuePayload: ['issue', 'clientMutationId'],
  CloseIssuePayload: ['issue', 'clientMutationId'],
  CreatePullRequestPayload: ['pullRequest', 'clientMutationId'],
  MergePullRequestPayload: ['pullRequest', 'clientMutationId'],
  AddCommentPayload: ['commentEdge', 'clientMutationId'],
  IssueCommentEdge: ['node'],
  IssueComment: ['id', 'body'],
  Query: ['viewer', 'repository', 'node', '__type', '__schema'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  __Type: ['name', 'kind', 'fields', 'enumValues', 'description'],
  __Schema: ['types', 'queryType', 'mutationType', 'description'],
  __Field: ['name', 'description', 'args', 'type'],
  __EnumValue: ['name', 'description'],
  __InputValue: ['name', 'description', 'type'],
};

const SCHEMA_ENUMS: Record<string, string[]> = {
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['CONFLICTING', 'MERGEABLE', 'UNKNOWN'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
};

function typeInfoObject(name: string): Record<string, unknown> | null {
  if (SCHEMA_FIELDS[name] !== undefined) {
    return {
      __typename: '__Type',
      name,
      kind: 'OBJECT',
      fields: SCHEMA_FIELDS[name].map((f) => ({ __typename: '__Field', name: f, description: null, args: [], type: { __typename: '__Type', name: 'String', kind: 'SCALAR' } })),
      enumValues: null,
    };
  }
  if (SCHEMA_ENUMS[name] !== undefined) {
    return {
      __typename: '__Type',
      name,
      kind: 'ENUM',
      fields: null,
      enumValues: (SCHEMA_ENUMS[name] as string[]).map((v) => ({ __typename: '__EnumValue', name: v, description: null })),
    };
  }
  return null;
}

type GqlParent =
  | { __typename: string; [key: string]: unknown };

function findRepoByGlobalId(globalId: string): Repo | undefined {
  for (const repo of repos.values()) {
    if (repo.globalId === globalId) return repo;
  }
  return undefined;
}
function findIssueByGlobalId(globalId: string): { repo: Repo; issue: Issue } | undefined {
  for (const repo of repos.values()) {
    for (const issue of repo.issues.values()) {
      if (issue.id === globalId) return { repo, issue };
    }
  }
  return undefined;
}
function findPullByGlobalId(globalId: string): { repo: Repo; pull: Pull } | undefined {
  for (const repo of repos.values()) {
    for (const pull of repo.pulls.values()) {
      if (pull.id === globalId) return { repo, pull };
    }
  }
  return undefined;
}

function cursorForNumber(n: number): string {
  return b64url(`cursor:${n}`);
}
function numberFromCursor(cursor: unknown): number | undefined {
  if (typeof cursor !== 'string') return undefined;
  try {
    const decoded = b64urlDecode(cursor);
    const m = /^cursor:(\d+)$/.exec(decoded);
    return m === null ? undefined : Number.parseInt(m[1] as string, 10);
  } catch {
    return undefined;
  }
}

function issueNode(repo: Repo, issue: Issue): GqlParent {
  return {
    __typename: 'Issue',
    id: issue.id,
    number: issue.number,
    title: issue.title,
    state: issue.state === 'open' ? 'OPEN' : 'CLOSED',
    body: issue.body,
  };
}
function pullNode(repo: Repo, pull: Pull): GqlParent {
  return {
    __typename: 'PullRequest',
    id: pull.id,
    number: pull.number,
    headRefName: pull.headRef,
    baseRefName: pull.baseRef,
    mergeable: pullMergeable(repo, pull) ? 'MERGEABLE' : 'CONFLICTING',
    state: pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED',
    merged: pull.merged,
    _repo: repo,
    _pull: pull,
  };
}
function repoNode(repo: Repo): GqlParent {
  return {
    __typename: 'Repository',
    id: repo.globalId,
    databaseId: repo.dbId,
    name: repo.name,
    nameWithOwner: `${repo.owner}/${repo.name}`,
    _repo: repo,
  };
}

class GqlExecError extends Error {}

function executeSelections(
  selections: SelectionNode[],
  parentType: string,
  parent: GqlParent | null,
  variables: Record<string, unknown>,
  fragments: Map<string, FragmentNode>,
  errors: Array<{ message: string }>,
): Record<string, unknown> | null {
  const data: Record<string, unknown> = {};
  for (const sel of selections) {
    if (sel.kind === 'spread') {
      const frag = fragments.get(sel.name);
      if (frag === undefined) {
        errors.push({ message: `Unknown fragment "${sel.name}".` });
        continue;
      }
      const sub = executeSelections(frag.selections, parentType, parent, variables, fragments, errors);
      if (sub !== null) Object.assign(data, sub);
      continue;
    }
    if (sel.kind === 'inline') {
      if (sel.typeCondition !== undefined && sel.typeCondition !== parentType && sel.typeCondition !== 'Node') continue;
      const sub = executeSelections(sel.selections, parentType, parent, variables, fragments, errors);
      if (sub !== null) Object.assign(data, sub);
      continue;
    }
    const fieldName = sel.name;
    const outName = sel.alias ?? fieldName;
    if (fieldName === '__typename') {
      data[outName] = parentType;
      continue;
    }
    const known = SCHEMA_FIELDS[parentType] ?? [];
    if (!known.includes(fieldName) && !(parentType === 'Query' && fieldName === '__type') && !(parentType === 'Query' && fieldName === '__schema')) {
      errors.push({ message: `Cannot query field "${fieldName}" on type "${parentType}".` });
      continue;
    }
    const args = gqlArgs(sel, variables);
    let value: unknown;
    try {
      value = resolveGqlField(parentType, parent, fieldName, args);
    } catch (err) {
      if (err instanceof HttpError) {
        errors.push({ message: err.message });
        continue;
      }
      throw err;
    }
    if (value === undefined) {
      data[outName] = null;
      continue;
    }
    if (sel.selections !== undefined && value !== null && typeof value === 'object') {
      if (Array.isArray(value)) {
        data[outName] = value.map((item) => {
          if (item !== null && typeof item === 'object' && (item as GqlParent).__typename !== undefined) {
            return executeSelections(sel.selections as SelectionNode[], (item as GqlParent).__typename as string, item as GqlParent, variables, fragments, errors);
          }
          return item;
        });
      } else {
        const childType = (value as GqlParent).__typename as string;
        data[outName] = executeSelections(sel.selections, childType, value as GqlParent, variables, fragments, errors);
      }
    } else {
      data[outName] = value;
    }
  }
  return data;
}

function resolveGqlField(
  parentType: string,
  parent: GqlParent | null,
  fieldName: string,
  args: Record<string, unknown>,
): unknown {
  if (parentType === 'Query') {
    if (fieldName === 'viewer') {
      return { __typename: 'User', id: VIEWER_ID, login: VIEWER_LOGIN, name: VIEWER_NAME, email: VIEWER_EMAIL };
    }
    if (fieldName === 'repository') {
      const repo = getRepo(String(args.owner ?? ''), String(args.name ?? ''));
      return repo === undefined ? null : repoNode(repo);
    }
    if (fieldName === 'node') {
      const id = String(args.id ?? '');
      let decoded = '';
      try {
        decoded = b64urlDecode(id);
      } catch {
        return null;
      }
      if (decoded.startsWith('repo:')) {
        const repo = findRepoByGlobalId(id);
        return repo === undefined ? null : repoNode(repo);
      }
      if (decoded.startsWith('issue:')) {
        const found = findIssueByGlobalId(id);
        return found === undefined ? null : issueNode(found.repo, found.issue);
      }
      if (decoded.startsWith('pr:')) {
        const found = findPullByGlobalId(id);
        return found === undefined ? null : pullNode(found.repo, found.pull);
      }
      if (decoded.startsWith('comment:')) {
        const m = /^comment:([^/]+)\/([^/]+)\/(\d+)\/(\d+)$/.exec(decoded);
        if (m === null) return null;
        const repo = getRepo(m[1] as string, m[2] as string);
        const issue = repo?.issues.get(Number.parseInt(m[3] as string, 10));
        const comment = issue?.comments.find((c) => c.id === Number.parseInt(m[4] as string, 10));
        if (comment === undefined) return null;
        return { __typename: 'IssueComment', id: comment.nodeId, body: comment.body };
      }
      return null;
    }
    if (fieldName === '__type') {
      return typeInfoObject(String(args.name ?? ''));
    }
    if (fieldName === '__schema') {
      return {
        __typename: '__Schema',
        queryType: { __typename: '__Type', name: 'Query' },
        mutationType: { __typename: '__Type', name: 'Mutation' },
        types: Object.keys(SCHEMA_FIELDS).map((name) => typeInfoObject(name)),
      };
    }
  }
  if (parentType === 'Mutation') {
    if (fieldName === 'createIssue') {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const repo = findRepoByGlobalId(String(input.repositoryId ?? ''));
      if (repo === undefined) throw new HttpError(404, 'Repository not found');
      repo.issueSeq += 1;
      repo.issueDbSeq += 1;
      globalSeq += 1;
      const now = nextIso();
      const issue: Issue = {
        id: issueGlobalId(repo.owner, repo.name, repo.issueSeq),
        dbId: repo.issueDbSeq,
        number: repo.issueSeq,
        title: String(input.title ?? ''),
        body: typeof input.body === 'string' ? input.body : '',
        state: 'open',
        labels: [],
        comments: [],
        createdSeq: globalSeq,
        createdAt: now,
        updatedAt: now,
      };
      repo.issues.set(issue.number, issue);
      return { __typename: 'CreateIssuePayload', issue: issueNode(repo, issue), clientMutationId: input.clientMutationId ?? null };
    }
    if (fieldName === 'closeIssue') {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const found = findIssueByGlobalId(String(input.issueId ?? ''));
      if (found === undefined) throw new HttpError(404, 'Issue not found');
      found.issue.state = 'closed';
      found.issue.updatedAt = nextIso();
      return { __typename: 'CloseIssuePayload', issue: issueNode(found.repo, found.issue), clientMutationId: input.clientMutationId ?? null };
    }
    if (fieldName === 'createPullRequest') {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const repo = findRepoByGlobalId(String(input.repositoryId ?? ''));
      if (repo === undefined) throw new HttpError(404, 'Repository not found');
      const headRef = String(input.headRefName ?? '');
      const baseRef = String(input.baseRefName ?? '');
      const headSha = branchTip(repo, headRef);
      const baseSha = branchTip(repo, baseRef);
      if (headSha === undefined || baseSha === undefined) throw new HttpError(422, 'head or base branch not found');
      const baseOid = mergeBase(repo, headSha, baseSha);
      repo.pullSeq += 1;
      repo.pullDbSeq += 1;
      globalSeq += 1;
      const now = nextIso();
      const pull: Pull = {
        id: pullGlobalId(repo.owner, repo.name, repo.pullSeq),
        dbId: repo.pullDbSeq,
        number: repo.pullSeq,
        title: String(input.title ?? ''),
        body: typeof input.body === 'string' ? input.body : '',
        state: 'open',
        headRef,
        baseRef,
        headSha,
        baseSha,
        mergeBaseSha: baseOid ?? baseSha,
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
        files: pullFilesFor(repo, baseOid, headSha),
        createdSeq: globalSeq,
        createdAt: now,
        updatedAt: now,
      };
      repo.pulls.set(pull.number, pull);
      return { __typename: 'CreatePullRequestPayload', pullRequest: pullNode(repo, pull), clientMutationId: input.clientMutationId ?? null };
    }
    if (fieldName === 'mergePullRequest') {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const found = findPullByGlobalId(String(input.pullRequestId ?? ''));
      if (found === undefined) throw new HttpError(404, 'Pull request not found');
      const method = typeof input.mergeMethod === 'string' ? input.mergeMethod.toLowerCase() : 'squash';
      if (found.pull.merged || found.pull.state !== 'open') throw new HttpError(405, 'Pull request is not open');
      mergePullRequestInternal(found.repo, found.pull, method);
      return { __typename: 'MergePullRequestPayload', pullRequest: pullNode(found.repo, found.pull), clientMutationId: input.clientMutationId ?? null };
    }
    if (fieldName === 'addComment') {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const found = findIssueByGlobalId(String(input.subjectId ?? ''));
      if (found === undefined) throw new HttpError(404, 'Subject not found');
      found.repo.commentDbSeq += 1;
      const now = nextIso();
      const comment = {
        id: found.repo.commentDbSeq,
        nodeId: commentGlobalId(found.repo.owner, found.repo.name, found.issue.number, found.repo.commentDbSeq),
        body: String(input.body ?? ''),
        createdAt: now,
      };
      found.issue.comments.push(comment);
      found.issue.updatedAt = now;
      return {
        __typename: 'AddCommentPayload',
        commentEdge: { __typename: 'IssueCommentEdge', node: { __typename: 'IssueComment', id: comment.nodeId, body: comment.body } },
        clientMutationId: input.clientMutationId ?? null,
      };
    }
  }
  if (parent === null) return null;
  if (parentType === 'Repository') {
    const repo = parent._repo as Repo;
    if (fieldName === 'owner') return { __typename: 'User', login: repo.owner, id: VIEWER_ID, name: repo.owner, email: '' };
    if (fieldName === 'defaultBranchRef') return { __typename: 'Ref', name: repo.defaultBranch };
    if (fieldName === 'viewerPermission') return 'ADMIN';
    if (fieldName === 'hasIssuesEnabled') return true;
    if (fieldName === 'issue') {
      const issue = repo.issues.get(Number(args.number));
      return issue === undefined ? null : issueNode(repo, issue);
    }
    if (fieldName === 'issues') {
      const states = Array.isArray(args.states) ? (args.states as string[]) : [];
      const afterNum = numberFromCursor(args.after);
      let list = [...repo.issues.values()];
      if (states.length > 0) list = list.filter((i) => states.includes(i.state === 'open' ? 'OPEN' : 'CLOSED'));
      list.sort((a, b) => b.number - a.number);
      if (afterNum !== undefined) list = list.filter((i) => i.number < afterNum);
      const first = typeof args.first === 'number' ? args.first : 10;
      const slice = list.slice(0, first);
      const hasNext = list.length > slice.length;
      const endCursor = slice.length > 0 ? cursorForNumber((slice[slice.length - 1] as Issue).number) : null;
      return {
        __typename: 'IssueConnection',
        nodes: slice.map((i) => issueNode(repo, i)),
        pageInfo: { __typename: 'PageInfo', hasNextPage: hasNext, endCursor, hasPreviousPage: false, startCursor: slice.length > 0 ? cursorForNumber((slice[0] as Issue).number) : null },
      };
    }
    if (fieldName === 'pullRequest') {
      const pull = repo.pulls.get(Number(args.number));
      return pull === undefined ? null : pullNode(repo, pull);
    }
    if (fieldName === 'pullRequests') {
      const states = Array.isArray(args.states) ? (args.states as string[]) : ['OPEN'];
      const afterNum = numberFromCursor(args.after);
      let list = [...repo.pulls.values()];
      list = list.filter((p) => {
        const s = p.merged ? 'MERGED' : p.state === 'open' ? 'OPEN' : 'CLOSED';
        return states.includes(s);
      });
      list.sort((a, b) => b.number - a.number);
      if (afterNum !== undefined) list = list.filter((p) => p.number < afterNum);
      const first = typeof args.first === 'number' ? args.first : 10;
      const slice = list.slice(0, first);
      const hasNext = list.length > slice.length;
      return {
        __typename: 'PullRequestConnection',
        nodes: slice.map((p) => pullNode(repo, p)),
        pageInfo: { __typename: 'PageInfo', hasNextPage: hasNext, endCursor: slice.length > 0 ? cursorForNumber((slice[slice.length - 1] as Pull).number) : null, hasPreviousPage: false, startCursor: slice.length > 0 ? cursorForNumber((slice[0] as Pull).number) : null },
      };
    }
  }
  if (parentType === 'PullRequest') {
    const pull = parent._pull as Pull;
    if (fieldName === 'files') {
      const first = typeof args.first === 'number' ? args.first : 10;
      const nodes = pull.files.slice(0, first).map((f) => ({ __typename: 'PullRequestChangedFile', path: f.filename }));
      return {
        __typename: 'PullRequestChangedFileConnection',
        nodes,
        pageInfo: { __typename: 'PageInfo', hasNextPage: pull.files.length > nodes.length, endCursor: null, hasPreviousPage: false, startCursor: null },
      };
    }
  }
  if (parentType === '__Type') {
    if (fieldName === 'fields') return parent.fields ?? null;
    if (fieldName === 'enumValues') return parent.enumValues ?? null;
  }
  if (parentType === '__Schema') {
    if (fieldName === 'types') return parent.types ?? [];
  }
  // Plain property fallback.
  const value = (parent as Record<string, unknown>)[fieldName];
  return value === undefined ? null : value;
}

function executeGraphQL(body: Record<string, unknown>): Record<string, unknown> {
  const query = body.query;
  if (typeof query !== 'string') {
    return { data: null, errors: [{ message: 'query is required' }] };
  }
  let doc: { operations: OperationNode[]; fragments: Map<string, FragmentNode> };
  try {
    doc = new GqlParser(query).parseDocument();
  } catch (err) {
    return { data: null, errors: [{ message: `Syntax error: ${err instanceof Error ? err.message : 'parse failed'}` }] };
  }
  const variables = (body.variables ?? {}) as Record<string, unknown>;
  const operationName = typeof body.operationName === 'string' ? body.operationName : undefined;
  let op: OperationNode | undefined;
  if (operationName !== undefined) {
    op = doc.operations.find((o) => o.name === operationName);
    if (op === undefined) return { data: null, errors: [{ message: `Unknown operation named "${operationName}".` }] };
  } else {
    if (doc.operations.length === 0) return { data: null, errors: [{ message: 'No operation provided.' }] };
    op = doc.operations[0] as OperationNode;
  }
  const vars: Record<string, unknown> = { ...variables };
  for (const [name, def] of Object.entries(op.variables)) {
    if (vars[name] === undefined && def.defaultValue !== undefined) {
      vars[name] = resolveGqlValue(def.defaultValue, vars);
    }
  }
  const rootType = op.opType === 'mutation' ? 'Mutation' : 'Query';
  const errors: Array<{ message: string }> = [];
  const data = executeSelections(op.selections, rootType, { __typename: rootType }, vars, doc.fragments, errors);
  if (errors.length > 0) return { data: null, errors };
  return { data };
}

async function handleGraphQL(req: http.IncomingMessage, res: http.ServerResponse): Promise<void> {
  if ((req.method ?? 'GET') !== 'POST') return sendError(res, 404, 'Not Found');
  const raw = await readBody(req);
  let body: unknown;
  try {
    body = JSON.parse(raw.toString('utf8'));
  } catch {
    throw new HttpError(400, 'Invalid JSON body');
  }
  if (Array.isArray(body)) {
    const results = body.map((item) =>
      item !== null && typeof item === 'object' ? executeGraphQL(item as Record<string, unknown>) : { data: null, errors: [{ message: 'Invalid request' }] },
    );
    return sendJson(res, 200, results);
  }
  if (body === null || typeof body !== 'object') throw new HttpError(400, 'Invalid JSON body');
  return sendJson(res, 200, executeGraphQL(body as Record<string, unknown>));
}

// ---------------------------------------------------------------- MCP

const MCP_TOOLS: Array<Record<string, unknown>> = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the viewer.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        name: { type: 'string', description: 'Repository name' },
        description: { type: 'string', description: 'Repository description' },
        private: { type: 'boolean', description: 'Whether the repository is private' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Issue title' },
        body: { type: 'string', description: 'Issue body' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        state: { type: 'string', description: 'Issue state filter: open, closed, or all' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Pull request title' },
        body: { type: 'string', description: 'Pull request body' },
        head: { type: 'string', description: 'Head branch name' },
        base: { type: 'string', description: 'Base branch name' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        pull_number: { type: 'integer', description: 'Pull request number' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

function mcpResult(id: unknown, result: Record<string, unknown>): Record<string, unknown> {
  return { jsonrpc: '2.0', id: id ?? null, result };
}
function mcpError(id: unknown, code: number, message: string): Record<string, unknown> {
  return { jsonrpc: '2.0', id: id ?? null, error: { code, message } };
}
function mcpToolResult(obj: unknown): Record<string, unknown> {
  const text = jsonBody(obj);
  return { content: [{ type: 'text', text }], structuredContent: obj };
}
function mcpToolError(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function mcpCreateIssue(repo: Repo, title: string, body: string): Record<string, unknown> {
  repo.issueSeq += 1;
  repo.issueDbSeq += 1;
  globalSeq += 1;
  const now = nextIso();
  const issue: Issue = {
    id: issueGlobalId(repo.owner, repo.name, repo.issueSeq),
    dbId: repo.issueDbSeq,
    number: repo.issueSeq,
    title,
    body,
    state: 'open',
    labels: [],
    comments: [],
    createdSeq: globalSeq,
    createdAt: now,
    updatedAt: now,
  };
  repo.issues.set(issue.number, issue);
  return issueJson(repo, issue);
}

function mcpCreatePull(repo: Repo, title: string, body: string, head: string, base: string): Record<string, unknown> {
  const headSha = branchTip(repo, head);
  const baseSha = branchTip(repo, base);
  if (headSha === undefined || baseSha === undefined) throw new HttpError(422, 'head or base branch not found');
  const baseOid = mergeBase(repo, headSha, baseSha);
  repo.pullSeq += 1;
  repo.pullDbSeq += 1;
  globalSeq += 1;
  const now = nextIso();
  const pull: Pull = {
    id: pullGlobalId(repo.owner, repo.name, repo.pullSeq),
    dbId: repo.pullDbSeq,
    number: repo.pullSeq,
    title,
    body,
    state: 'open',
    headRef: head,
    baseRef: base,
    headSha,
    baseSha,
    mergeBaseSha: baseOid ?? baseSha,
    merged: false,
    mergedAt: null,
    mergeCommitSha: null,
    files: pullFilesFor(repo, baseOid, headSha),
    createdSeq: globalSeq,
    createdAt: now,
    updatedAt: now,
  };
  repo.pulls.set(pull.number, pull);
  return pullJson(repo, pull);
}

async function handleMcp(req: http.IncomingMessage, res: http.ServerResponse): Promise<void> {
  if ((req.method ?? 'GET') !== 'POST') {
    res.writeHead(405, { 'x-github-request-id': nextRequestId() });
    return res.end();
  }
  const raw = await readBody(req);
  let body: Record<string, unknown>;
  try {
    const parsed: unknown = JSON.parse(raw.toString('utf8'));
    if (parsed === null || typeof parsed !== 'object' || Array.isArray(parsed)) throw new Error('bad');
    body = parsed as Record<string, unknown>;
  } catch {
    return sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
  }
  const id = body.id ?? null;
  const method = body.method;
  if (typeof method !== 'string') return sendJson(res, 200, mcpError(id, -32600, 'Invalid Request'));
  const params = (body.params ?? {}) as Record<string, unknown>;

  // Legacy initialize (pre-2026-07-28 clients).
  if (method === 'initialize') {
    const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25';
    return sendJson(res, 200, mcpResult(id, {
      protocolVersion: requested,
      capabilities: { tools: {} },
      serverInfo: { name: FORGE_NAME, version: FORGE_VERSION },
    }));
  }
  if (method === 'notifications/initialized' || method === 'notifications/cancelled' || method.startsWith('notifications/')) {
    res.writeHead(202, { 'x-github-request-id': nextRequestId() });
    return res.end();
  }
  if (method === 'ping') return sendJson(res, 200, mcpResult(id, {}));

  if (method === 'server/discover') {
    const serverInfo = { name: FORGE_NAME, version: FORGE_VERSION };
    return sendJson(res, 200, mcpResult(id, {
      protocolVersion: '2026-07-28',
      supportedVersions: ['2026-07-28'],
      capabilities: { tools: {} },
      serverInfo,
      _meta: { 'io.modelcontextprotocol/serverInfo': serverInfo },
    }));
  }
  if (method === 'tools/list') {
    return sendJson(res, 200, mcpResult(id, { tools: MCP_TOOLS }));
  }
  if (method === 'tools/call') {
    const name = params.name;
    const args = (params.arguments ?? {}) as Record<string, unknown>;
    if (typeof name !== 'string') return sendJson(res, 200, mcpError(id, -32602, 'Tool name is required'));
    const tool = MCP_TOOLS.find((t) => t.name === name);
    if (tool === undefined) return sendJson(res, 200, mcpError(id, -32602, `Unknown tool: ${name}`));
    const required = ((tool.inputSchema as Record<string, unknown>).required ?? []) as string[];
    for (const key of required) {
      if (args[key] === undefined || args[key] === null || args[key] === '') {
        return sendJson(res, 200, mcpResult(id, mcpToolError(`Missing required argument: ${key}`)));
      }
    }
    try {
      const result = callMcpTool(name, args);
      return sendJson(res, 200, mcpResult(id, result));
    } catch (err) {
      if (err instanceof HttpError) return sendJson(res, 200, mcpResult(id, mcpToolError(err.message)));
      throw err;
    }
  }
  return sendJson(res, 200, mcpError(id, -32601, `Method not found: ${method}`));
}

function callMcpTool(name: string, args: Record<string, unknown>): Record<string, unknown> {
  if (name === 'create_repo') {
    const repoName = String(args.name ?? '');
    const owner = typeof args.owner === 'string' && args.owner.length > 0 ? args.owner : VIEWER_LOGIN;
    if (getRepo(owner, repoName) !== undefined) throw new HttpError(422, 'Repository already exists');
    const repo = createRepoRecord(owner, repoName, {
      description: typeof args.description === 'string' ? args.description : undefined,
      private: args.private === true,
    });
    return mcpToolResult(repoJson(repo));
  }
  const owner = String(args.owner ?? '');
  const repoName = String(args.repo ?? '');
  const repo = getRepo(owner, repoName);
  if (repo === undefined) throw new HttpError(404, 'Repository not found');
  if (name === 'get_repo') return mcpToolResult(repoJson(repo));
  if (name === 'create_issue') {
    return mcpToolResult(mcpCreateIssue(repo, String(args.title ?? ''), typeof args.body === 'string' ? args.body : ''));
  }
  if (name === 'list_issues') {
    const state = typeof args.state === 'string' ? args.state : 'open';
    let list = [...repo.issues.values()];
    if (state !== 'all') list = list.filter((i) => i.state === state);
    list.sort((a, b) => b.createdSeq - a.createdSeq);
    return mcpToolResult(list.map((i) => issueJson(repo, i)));
  }
  if (name === 'create_pull_request') {
    return mcpToolResult(mcpCreatePull(
      repo,
      String(args.title ?? ''),
      typeof args.body === 'string' ? args.body : '',
      String(args.head ?? ''),
      String(args.base ?? ''),
    ));
  }
  if (name === 'merge_pull_request') {
    const pull = repo.pulls.get(Number(args.pull_number));
    if (pull === undefined) throw new HttpError(404, 'Pull request not found');
    if (pull.merged || pull.state !== 'open') throw new HttpError(405, 'Pull request is not open');
    const sha = mergePullRequestInternal(repo, pull, 'squash');
    return mcpToolResult({ sha, merged: true, message: 'Pull request successfully merged' });
  }
  throw new HttpError(400, `Unknown tool: ${name}`);
}

// ---------------------------------------------------------------- git smart HTTP

const UPLOAD_V2_CAPS = 'version 2\nagent=makefun-forge/1.0\nls-refs=unborn\nfetch=shallow wait-for-done\nobject-format=sha1\n';

function gitAdvertise(repo: Repo | undefined, service: 'upload-pack' | 'receive-pack'): Buffer {
  const chunks: Buffer[] = [pktLine(`# service=git-${service}\n`), PKT_FLUSH];
  const caps = service === 'upload-pack'
    ? 'symref=HEAD:refs/heads/main side-band-64k thin-pack ofs-delta shallow multi_ack multi_ack_detailed'
    : 'report-status side-band-64k delete-refs ofs-delta';
  const refs = repo === undefined ? [] : [...repo.refs.entries()].sort((a, b) => a[0].localeCompare(b[0]));
  if (refs.length === 0) {
    chunks.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    let first = true;
    for (const [ref, oid] of refs) {
      if (first) {
        chunks.push(pktLine(`${oid} ${ref}\0${caps}\n`));
        first = false;
      } else {
        chunks.push(pktLine(`${oid} ${ref}\n`));
      }
      // Peeled tag lines: for annotated tags, advertise the target too.
      const obj = repo?.objects.get(oid);
      if (obj?.type === 'tag') {
        const target = parseTag(obj.data).object;
        chunks.push(pktLine(`${target} ${ref}^{}\n`));
      }
    }
  }
  chunks.push(PKT_FLUSH);
  return Buffer.concat(chunks);
}

/** Sideband band-1 packets carrying pack bytes. */
function sidebandPack(pack: Buffer): Buffer {
  const chunks: Buffer[] = [];
  const CHUNK = 60000;
  if (pack.length === 0) {
    chunks.push(pktLine(Buffer.concat([Buffer.from([1])])));
  } else {
    for (let i = 0; i < pack.length; i += CHUNK) {
      const slice = pack.subarray(i, Math.min(pack.length, i + CHUNK));
      chunks.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
    }
  }
  chunks.push(PKT_FLUSH);
  return Buffer.concat(chunks);
}

function buildPack(_repo: Repo, objects: Map<string, GitObject>): Buffer {
  return writePack([...objects.values()]);
}

/** Parse a v2 ls-refs / fetch request body into commands and arguments. */
interface V2Request {
  command: string;
  args: string[];
  delimSeen: boolean;
}
function parseV2Request(body: Buffer): V2Request {
  const { packets } = parsePktLines(body);
  const commandLine = (packets.find((p) => p.kind === 'data')?.payload.toString('utf8') ?? '').trim();
  const args: string[] = [];
  let delimSeen = false;
  for (const p of packets) {
    if (p.kind === 'delim') {
      delimSeen = true;
      continue;
    }
    if (p.kind !== 'data') continue;
    const text = p.payload.toString('utf8').trim();
    if (text === commandLine) continue;
    if (text.startsWith('agent=') || text.startsWith('object-format=')) continue;
    args.push(text);
  }
  return { command: commandLine.replace(/^command=/, ''), args, delimSeen };
}

function handleLsRefs(repo: Repo | undefined, body: Buffer): Buffer {
  const req = parseV2Request(body);
  const wantPeel = req.args.includes('peel');
  const wantSymrefs = req.args.includes('symrefs');
  const wantUnborn = req.args.includes('unborn');
  const prefixes = req.args.filter((a) => a.startsWith('ref-prefix ')).map((a) => a.slice('ref-prefix '.length));
  const matches = (name: string): boolean => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
  const chunks: Buffer[] = [];
  const refs = repo === undefined ? [] : [...repo.refs.entries()].sort((a, b) => a[0].localeCompare(b[0]));
  const emit = (oid: string, name: string, extra = ''): void => {
    chunks.push(pktLine(`${oid} ${name}${extra}\n`));
  };
  if (matches('HEAD')) {
    const headTarget = `refs/heads/${DEFAULT_BRANCH}`;
    const headOid = repo?.refs.get(headTarget);
    if (headOid !== undefined) {
      emit(headOid, 'HEAD', wantSymrefs ? ` symref-target:${headTarget}` : '');
    } else if (wantUnborn) {
      emit('unborn', 'HEAD', wantSymrefs ? ` symref-target:${headTarget}` : '');
    }
  }
  for (const [ref, oid] of refs) {
    if (!matches(ref)) continue;
    let extra = '';
    const obj = repo?.objects.get(oid);
    if (wantPeel && obj?.type === 'tag') extra += ` peeled:${parseTag(obj.data).object}`;
    emit(oid, ref, extra);
  }
  chunks.push(PKT_FLUSH);
  return Buffer.concat(chunks);
}

function handleFetchV2(repo: Repo, body: Buffer): Buffer {
  const req = parseV2Request(body);
  const wants: string[] = [];
  const haves: string[] = [];
  const shallowBoundaries: string[] = [];
  let depth: number | undefined;
  let thinPack = false;
  for (const arg of req.args) {
    if (arg.startsWith('want ')) wants.push(arg.slice(5).trim());
    else if (arg.startsWith('have ')) haves.push(arg.slice(5).trim());
    else if (arg.startsWith('shallow ')) shallowBoundaries.push(arg.slice(8).trim());
    else if (arg.startsWith('deepen ')) depth = Number.parseInt(arg.slice(7).trim(), 10);
    else if (arg === 'thin-pack') thinPack = true;
  }
  const { objects, shallow, unshallow } = fetchSelection(repo, wants, haves, shallowBoundaries, depth);
  const chunks: Buffer[] = [];
  if (haves.length > 0) {
    chunks.push(pktLine('acknowledgments\n'));
    chunks.push(pktLine('NAK\n'));
    chunks.push(PKT_DELIM);
  }
  if (shallow.length > 0 || unshallow.length > 0) {
    chunks.push(pktLine('shallow-info\n'));
    for (const oid of shallow) chunks.push(pktLine(`shallow ${oid}\n`));
    for (const oid of unshallow) chunks.push(pktLine(`unshallow ${oid}\n`));
    chunks.push(PKT_DELIM);
  }
  chunks.push(pktLine('packfile\n'));
  chunks.push(sidebandPack(buildPack(repo, objects)));
  void thinPack;
  return Buffer.concat(chunks);
}

function handleFetchV0(repo: Repo, body: Buffer): Buffer {
  const { packets } = parsePktLines(body);
  const wants: string[] = [];
  const haves: string[] = [];
  let depth: number | undefined;
  let first = true;
  for (const p of packets) {
    if (p.kind !== 'data') continue;
    const text = p.payload.toString('utf8');
    if (text.startsWith('want ')) {
      wants.push(text.slice(5).split(' ')[0] as string);
      first = false;
    } else if (text.startsWith('have ')) {
      haves.push(text.slice(5).trim());
    } else if (text.startsWith('deepen ')) {
      depth = Number.parseInt(text.slice(7).trim(), 10);
    } else if (text === 'done') {
      break;
    }
    void first;
  }
  const { objects, shallow, unshallow } = fetchSelection(repo, wants, haves, [], depth);
  const chunks: Buffer[] = [pktLine('NAK\n')];
  for (const oid of shallow) chunks.push(pktLine(`shallow ${oid}\n`));
  for (const oid of unshallow) chunks.push(pktLine(`unshallow ${oid}\n`));
  chunks.push(sidebandPack(buildPack(repo, objects)));
  return Buffer.concat(chunks);
}

/** Fast-forward check: is `oldTip` an ancestor of `newTip` (or ZERO for create)? */
function isFastForward(repo: Repo, oldTip: string, newTip: string): boolean {
  if (oldTip === ZERO_OID) return true;
  if (newTip === ZERO_OID) return true;
  return ancestors(repo, newTip).has(oldTip);
}

async function handleReceivePack(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo): Promise<void> {
  const body = await readBody(req);
  interface Command {
    oldOid: string;
    newOid: string;
    ref: string;
  }
  const commands: Command[] = [];
  // Walk the command pkt-lines manually: after the flush packet the rest of
  // the body is raw pack bytes, not pkt-lines.
  let packStart = -1;
  let off = 0;
  while (off + 4 <= body.length) {
    const head = body.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-f]{4}$/.test(head)) throw new HttpError(400, 'Invalid pkt-line framing');
    const len = parseInt(head, 16);
    if (len === 0) {
      off += 4;
      packStart = off;
      break;
    }
    if (len < 4 || off + len > body.length) throw new HttpError(400, 'Invalid pkt-line framing');
    const text = body.subarray(off + 4, off + len).toString('utf8').trim();
    const m = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)(?:\0.*)?$/.exec(text);
    if (m !== null) {
      commands.push({ oldOid: m[1] as string, newOid: m[2] as string, ref: m[3] as string });
    }
    off += len;
  }
  if (packStart === -1) packStart = body.length;
  const packBytes = body.subarray(packStart);
  let packObjects: Map<string, GitObject> | null = null;
  if (packBytes.length > 0) {
    try {
      packObjects = readPack(packBytes, (oid) => repo.objects.get(oid));
    } catch (err) {
      console.error('readPack failed:', err instanceof Error ? err.message : err);
      return sendError(res, 400, 'Invalid packfile');
    }
  }
  // Store the pack objects first: validation (fast-forward checks) walks the
  // object graph, so the new objects must already be in the store. They are
  // unreachable until the refs below move, exactly like a real receive-pack.
  if (packObjects !== null) {
    for (const [oid, obj] of packObjects) repo.objects.set(oid, obj);
  }
  // Validate all commands before mutating any refs.
  const results: Array<{ ref: string; ok: boolean; reason?: string }> = [];
  for (const cmd of commands) {
    const current = repo.refs.get(cmd.ref);
    if (cmd.newOid === ZERO_OID) {
      // Delete.
      if (current === undefined) results.push({ ref: cmd.ref, ok: false, reason: 'cannot delete a non-existent ref' });
      else if (cmd.oldOid !== ZERO_OID && cmd.oldOid !== current) results.push({ ref: cmd.ref, ok: false, reason: 'old value does not match' });
      else results.push({ ref: cmd.ref, ok: true });
      continue;
    }
    if (cmd.oldOid !== ZERO_OID && current !== cmd.oldOid) {
      results.push({ ref: cmd.ref, ok: false, reason: 'old value does not match' });
      continue;
    }
    if (current !== undefined && cmd.oldOid === ZERO_OID) {
      results.push({ ref: cmd.ref, ok: false, reason: 'already exists' });
      continue;
    }
    const target = packObjects?.get(cmd.newOid) ?? repo.objects.get(cmd.newOid);
    if (target === undefined) {
      results.push({ ref: cmd.ref, ok: false, reason: 'object not found' });
      continue;
    }
    if (current !== undefined && !isFastForward(repo, current, cmd.newOid)) {
      results.push({ ref: cmd.ref, ok: false, reason: 'non-fast-forward' });
      continue;
    }
    results.push({ ref: cmd.ref, ok: true });
  }
  // Apply: move accepted refs.
  for (let i = 0; i < commands.length; i += 1) {
    const cmd = commands[i] as Command;
    const result = results[i] as { ref: string; ok: boolean };
    if (!result.ok) continue;
    if (cmd.newOid === ZERO_OID) repo.refs.delete(cmd.ref);
    else repo.refs.set(cmd.ref, cmd.newOid);
  }
  const inner: Buffer[] = [pktLine('unpack ok\n')];
  for (const result of results) {
    inner.push(result.ok ? pktLine(`ok ${result.ref}\n`) : pktLine(`ng ${result.ref} ${result.reason ?? 'rejected'}\n`));
  }
  inner.push(PKT_FLUSH);
  const out = pktLine(Buffer.concat([Buffer.from([1]), Buffer.concat(inner)]));
  sendRaw(res, 200, 'application/x-git-receive-pack-result', Buffer.concat([out, PKT_FLUSH]));
}

async function handleGit(req: http.IncomingMessage, res: http.ServerResponse, url: URL): Promise<void> {
  const method = req.method ?? 'GET';
  const path = url.pathname;
  const m = /^\/([^/]+)\/([^/]+)\.git\/(.+)$/.exec(path);
  if (m === null) return sendError(res, 404, 'Not Found');
  const owner = decodeURIComponent(m[1] as string);
  const name = decodeURIComponent(m[2] as string);
  const tail = m[3] as string;
  const repo = getRepo(owner, name);

  if (method === 'GET' && tail === 'info/refs') {
    const service = url.searchParams.get('service') ?? '';
    if (service === 'git-upload-pack') {
      if (repo === undefined) return sendError(res, 404, 'Not Found');
      // Honour Git-Protocol: version=2: answer with the v2 capability advertisement.
      if ((req.headers['git-protocol'] ?? '') === 'version=2') {
        const lines = UPLOAD_V2_CAPS.split('\n').filter((l) => l.length > 0).map((l) => pktLine(`${l}\n`));
        return sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', Buffer.concat([...lines, PKT_FLUSH]));
      }
      return sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', gitAdvertise(repo, 'upload-pack'));
    }
    if (service === 'git-receive-pack') {
      if (repo === undefined) return sendError(res, 404, 'Not Found');
      return sendRaw(res, 200, 'application/x-git-receive-pack-advertisement', gitAdvertise(repo, 'receive-pack'));
    }
    return sendError(res, 400, 'Missing service parameter');
  }
  if (method === 'POST' && tail === 'git-upload-pack') {
    if (repo === undefined) return sendError(res, 404, 'Not Found');
    const body = await readBody(req);
    const isV2 = (req.headers['git-protocol'] ?? '') === 'version=2';
    if (isV2) {
      const parsed = parseV2Request(body);
      if (parsed.command === 'ls-refs') {
        return sendRaw(res, 200, 'application/x-git-upload-pack-result', handleLsRefs(repo, body));
      }
      if (parsed.command === 'fetch') {
        return sendRaw(res, 200, 'application/x-git-upload-pack-result', handleFetchV2(repo, body));
      }
      return sendError(res, 400, `Unknown command: ${parsed.command}`);
    }
    return sendRaw(res, 200, 'application/x-git-upload-pack-result', handleFetchV0(repo, body));
  }
  if (method === 'POST' && tail === 'git-receive-pack') {
    if (repo === undefined) return sendError(res, 404, 'Not Found');
    return handleReceivePack(req, res, repo);
  }
  return sendError(res, 404, 'Not Found');
}

// ---------------------------------------------------------------- dispatch + lifecycle

async function dispatch(req: http.IncomingMessage, res: http.ServerResponse): Promise<void> {
  const url = new URL(req.url ?? '/', 'http://localhost');
  const path = url.pathname;
  try {
    if (path === '/healthz') {
      if ((req.method ?? 'GET') !== 'GET') return sendError(res, 404, 'Not Found');
      return sendJson(res, 200, { ok: true });
    }
    if (path === '/api/graphql') {
      if (!checkAuth(req, res)) return;
      await handleGraphQL(req, res);
      return;
    }
    if (path === '/mcp') {
      if (!checkAuth(req, res)) return;
      await handleMcp(req, res);
      return;
    }
    if (path === '/api/v3' || path.startsWith('/api/v3/')) {
      if (!checkAuth(req, res)) return;
      await handleRest(req, res, url);
      return;
    }
    if (/^\/[^/]+\/[^/]+\.git\//.test(path)) {
      await handleGit(req, res, url);
      return;
    }
    return sendError(res, 404, 'Not Found');
  } catch (err) {
    if (err instanceof HttpError) return sendError(res, err.status, err.message);
    console.error('handler error:', err);
    if (!res.headersSent) return sendError(res, 500, 'Internal Server Error');
  }
}

const server = http.createServer((req, res) => {
  dispatch(req, res).catch((err) => {
    console.error('dispatch error:', err);
    if (!res.headersSent) sendError(res, 500, 'Internal Server Error');
  });
});

async function fetchJson(url: string, init: { method?: string; body?: string; headers?: Record<string, string> }): Promise<{ status: number; text: string }> {
  const response = await fetch(url, {
    method: init.method ?? 'GET',
    body: init.body,
    headers: init.headers,
  });
  return { status: response.status, text: await response.text() };
}

async function main(): Promise<void> {
  await new Promise<void>((resolve) => server.listen(0, '127.0.0.1', resolve));
  const address = server.address();
  if (address === null || typeof address === 'string') throw new Error('failed to bind');
  const port = address.port;
  console.error(`makefun-forge listening on 127.0.0.1:${port}`);
  if (ENV_URL !== '') {
    try {
      const reg = await fetchJson(`${ENV_URL}/register`, {
        method: 'POST',
        body: jsonBody({ port }),
        headers: { 'content-type': 'application/json' },
      });
      if (reg.status !== 200 && reg.status !== 201) {
        console.error(`register failed: ${reg.status} ${reg.text}`);
      }
    } catch (err) {
      console.error('register error:', err);
    }
    for (;;) {
      try {
        const done = await fetchJson(`${ENV_URL}/done`, {});
        if (done.status === 200) {
          const parsed: unknown = JSON.parse(done.text);
          if ((parsed as { done?: boolean }).done === true) break;
        }
      } catch {
        // Transient: keep polling.
      }
      await new Promise((resolve) => setTimeout(resolve, 250));
    }
  } else {
    // No env URL (local smoke test): stay up until killed.
    await new Promise(() => undefined);
  }
  server.close();
  process.exit(0);
}

void main();

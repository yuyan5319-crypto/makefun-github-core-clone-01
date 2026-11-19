// A single-process, GitHub-compatible git forge.
//
// One Node 22 process, standard library only. It serves four surfaces from one
// in-memory store: git smart HTTP (upload-pack v2, receive-pack v0), the REST v3
// API under /api/v3, GraphQL v4 at /api/graphql, and MCP at /mcp. There is no
// git binary, no database and no network beyond the trial env beside it.
//
// The forge binds an ephemeral port, registers it with the env, then polls the
// env's /done until the suite has finished and exits 0. Every timestamp the
// forge emits comes from a logical clock (a counter off a fixed epoch), never
// from the wall clock, so two runs of the same trial answer byte for byte.
//
// The token owner is the viewer of the trial's fixed scenario: the login the
// kit's seeded scenario derives for its first user. Repositories belong to
// that login; any other owner reads as missing.

import { createServer } from 'node:http';
import type { IncomingMessage, Server, ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// -------------------------------------------------------------------------------------------
// Small constants and the logical clock
// -------------------------------------------------------------------------------------------

const VIEWER_LOGIN = 'adaiversen';
const VIEWER_ID = 1000;
const VIEWER_NAME = 'ada iversen';
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const DEFAULT_BRANCH = 'main';
const FORGE_NAME = 'forge';
const FORGE_VERSION = '1.0.0';
const ZERO_OID = '0'.repeat(40);
const GIT_AGENT = 'forge/1.0';

// 2025-01-01T00:00:00Z. Every emitted timestamp is this epoch plus a counter,
// so repeated runs stay deterministic.
const CLOCK_EPOCH_SEC = 1735689600;
let clockTick = 0;
function clockSec(): number {
  clockTick += 1;
  return CLOCK_EPOCH_SEC + clockTick;
}
function clockIso(): string {
  return new Date(clockSec() * 1000).toISOString();
}

let requestSeq = 0;
function nextRequestId(): string {
  requestSeq += 1;
  return `forge-${requestSeq.toString(16).padStart(8, '0')}`;
}

function sha1Hex(data: Buffer | string): string {
  return createHash('sha1').update(data).digest('hex');
}

function isOid(value: unknown): value is string {
  return typeof value === 'string' && /^[0-9a-f]{40}$/.test(value);
}

function b64encode(data: Buffer | string): string {
  return Buffer.isBuffer(data) ? data.toString('base64') : Buffer.from(data, 'utf8').toString('base64');
}

function b64decode(text: string): Buffer {
  return Buffer.from(text.replace(/\s+/g, ''), 'base64');
}

function globalId(kind: string, ...parts: Array<string | number>): string {
  return b64encode(`forge:${kind}:${parts.join(':')}`);
}

// -------------------------------------------------------------------------------------------
// pkt-line framing (the git wire format)
// -------------------------------------------------------------------------------------------

type PktKind = 'data' | 'flush' | 'delim' | 'response-end';

interface PktLine {
  kind: PktKind;
  payload: Buffer;
}

function pktEncode(payload: Buffer | string): Buffer {
  const body = Buffer.isBuffer(payload) ? payload : Buffer.from(payload, 'utf8');
  const head = Buffer.from((body.length + 4).toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, body]);
}

function pktFlush(): Buffer {
  return Buffer.from('0000', 'ascii');
}

function pktDelim(): Buffer {
  return Buffer.from('0001', 'ascii');
}

/** Parse pkt-lines from the start of `buf` until a flush (inclusive). Returns the packets and the byte offset just past the flush (or the end when no flush is present). */
function parsePktLines(buf: Buffer): { packets: PktLine[]; endOffset: number } {
  const packets: PktLine[] = [];
  let offset = 0;
  while (offset + 4 <= buf.length) {
    const head = buf.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) throw new Error(`bad pkt-line header ${JSON.stringify(head)}`);
    const size = parseInt(head, 16);
    if (size === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      return { packets, endOffset: offset + 4 };
    }
    if (size === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (size === 2) {
      packets.push({ kind: 'response-end', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (size < 4 || offset + size > buf.length) throw new Error('pkt-line overruns its buffer');
    packets.push({ kind: 'data', payload: buf.subarray(offset + 4, offset + size) });
    offset += size;
  }
  if (offset !== buf.length) throw new Error('trailing bytes after the last pkt-line');
  return { packets, endOffset: offset };
}

function pktLinesText(packets: readonly PktLine[]): string[] {
  const out: string[] = [];
  for (const packet of packets) {
    if (packet.kind === 'data') out.push(packet.payload.toString('utf8'));
  }
  return out;
}

// -------------------------------------------------------------------------------------------
// Git objects: hashing, trees, commits, tags, reachability
// -------------------------------------------------------------------------------------------

type ObjectType = 'commit' | 'tree' | 'blob' | 'tag';

interface GitObject {
  type: ObjectType;
  data: Buffer;
}

const OBJECT_TYPE_CODE: Record<ObjectType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const OBJECT_CODE_TYPE: Record<number, ObjectType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function hashObject(type: ObjectType, data: Buffer): string {
  const head = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1Hex(Buffer.concat([head, data]));
}

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function compareTreeNames(a: TreeEntry, b: TreeEntry): number {
  const an = a.mode === '40000' ? `${a.name}/` : a.name;
  const bn = b.mode === '40000' ? `${b.name}/` : b.name;
  return an < bn ? -1 : an > bn ? 1 : 0;
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    if (space < 0) throw new Error('tree entry has no mode');
    const nul = data.indexOf(0x00, space + 1);
    if (nul < 0 || nul + 21 > data.length) throw new Error('tree entry has no name or oid');
    entries.push({
      mode: data.subarray(offset, space).toString('ascii'),
      name: data.subarray(space + 1, nul).toString('utf8'),
      oid: data.subarray(nul + 1, nul + 21).toString('hex'),
    });
    offset = nul + 21;
  }
  return entries;
}

function buildTree(entries: readonly TreeEntry[]): Buffer {
  const sorted = [...entries].sort(compareTreeNames);
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

function buildCommit(fields: { tree: string; parents: readonly string[]; message: string; author: string; committer: string; timestamp: number }): Buffer {
  const lines: string[] = [`tree ${fields.tree}`];
  for (const parent of fields.parents) lines.push(`parent ${parent}`);
  lines.push(`author ${fields.author} ${fields.timestamp} +0000`);
  lines.push(`committer ${fields.committer} ${fields.timestamp} +0000`);
  const message = fields.message.endsWith('\n') ? fields.message : `${fields.message}\n`;
  return Buffer.from(`${lines.join('\n')}\n\n${message}`, 'utf8');
}

function buildTag(fields: { object: string; type: string; tag: string; message: string; tagger: string; timestamp: number }): Buffer {
  const message = fields.message.endsWith('\n') ? fields.message : `${fields.message}\n`;
  return Buffer.from(
    `object ${fields.object}\ntype ${fields.type}\ntag ${fields.tag}\ntagger ${fields.tagger} ${fields.timestamp} +0000\n\n${message}`,
    'utf8',
  );
}

type ObjectLookup = (oid: string) => GitObject | undefined;

/** Every object id reachable from `tips`: commits walk parents, trees recurse, tags unwrap. */
function collectReachable(tips: Iterable<string>, lookup: ObjectLookup): Set<string> {
  const seen = new Set<string>();
  const stack = [...tips];
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (seen.has(oid) || !isOid(oid)) continue;
    const object = lookup(oid);
    if (object === undefined) throw new Error(`missing object ${oid}`);
    seen.add(oid);
    if (object.type === 'commit') {
      const view = parseCommit(object.data);
      stack.push(view.tree);
      for (const parent of view.parents) stack.push(parent);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) stack.push(entry.oid);
    } else if (object.type === 'tag') {
      const target = object.data.toString('utf8').split('\n').find((line) => line.startsWith('object '));
      if (target !== undefined) stack.push(target.slice(7).trim());
    }
  }
  return seen;
}

/** True when `ancestor` is `tip` itself or one of its commit ancestors. */
function isAncestor(ancestor: string, tip: string, lookup: ObjectLookup): boolean {
  if (ancestor === tip) return true;
  const seen = new Set<string>();
  const stack = [tip];
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = lookup(oid);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (parent === ancestor) return true;
      stack.push(parent);
    }
  }
  return false;
}

/** The flat file map of a tree: path -> {mode, oid}. */
function flattenTree(treeOid: string, lookup: ObjectLookup): Map<string, { mode: string; oid: string }> {
  const out = new Map<string, { mode: string; oid: string }>();
  const walk = (oid: string, prefix: string): void => {
    const object = lookup(oid);
    if (object === undefined || object.type !== 'tree') return;
    for (const entry of parseTree(object.data)) {
      const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
      if (entry.mode === '40000') walk(entry.oid, path);
      else out.set(path, { mode: entry.mode, oid: entry.oid });
    }
  };
  walk(treeOid, '');
  return out;
}

/** Build a tree object (and its subtrees) from a flat file map, storing every new object through `put`. */
function treeFromFiles(
  files: ReadonlyMap<string, { mode: string; oid: string }>,
  put: (type: ObjectType, data: Buffer) => string,
): string {
  interface Node {
    files: Map<string, { mode: string; oid: string }>;
    dirs: Map<string, Node>;
  }
  const make = (): Node => ({ files: new Map(), dirs: new Map() });
  const root = make();
  for (const [path, entry] of files) {
    const segments = path.split('/');
    let node = root;
    for (let index = 0; index < segments.length - 1; index += 1) {
      const name = segments[index];
      if (!node.dirs.has(name)) node.dirs.set(name, make());
      node = node.dirs.get(name)!;
    }
    node.files.set(segments[segments.length - 1], entry);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, entry] of node.files) entries.push({ mode: entry.mode, name, oid: entry.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    return put('tree', buildTree(entries));
  };
  return build(root);
}

/** Line counts of a blob, for pull-request file statistics. */
function countLines(data: Buffer): number {
  if (data.length === 0) return 0;
  let count = 0;
  for (let index = 0; index < data.length; index += 1) if (data[index] === 0x0a) count += 1;
  if (data[data.length - 1] !== 0x0a) count += 1;
  return count;
}

/** A cheap line-level diff: additions are lines only in `next`, deletions lines only in `prev`. */
function lineDiff(prev: Buffer, next: Buffer): { additions: number; deletions: number } {
  const prevLines = prev.length === 0 ? [] : prev.toString('utf8').split('\n');
  const nextLines = next.length === 0 ? [] : next.toString('utf8').split('\n');
  const prevCounts = new Map<string, number>();
  for (const line of prevLines) prevCounts.set(line, (prevCounts.get(line) ?? 0) + 1);
  let additions = 0;
  for (const line of nextLines) {
    const left = prevCounts.get(line) ?? 0;
    if (left > 0) prevCounts.set(line, left - 1);
    else additions += 1;
  }
  let deletions = 0;
  for (const left of prevCounts.values()) deletions += left;
  return { additions, deletions };
}

// -------------------------------------------------------------------------------------------
// Packfiles: read (plain objects and both delta kinds) and write (plain objects only)
// -------------------------------------------------------------------------------------------

interface PackEntry {
  offset: number;
  type: ObjectType;
  size: number;
  data: Buffer;
  oid: string;
}

function readPackVarint(buf: Buffer, start: number): { size: number; next: number } {
  let byte = buf[start];
  let size = byte & 0x0f;
  let shift = 4;
  let offset = start + 1;
  while (byte & 0x80) {
    byte = buf[offset++];
    size += (byte & 0x7f) * 2 ** shift;
    shift += 7;
  }
  return { size, next: offset };
}

function readPackOfsBase(buf: Buffer, start: number): { baseOffset: number; next: number } {
  let byte = buf[start];
  let offset = start + 1;
  let value = byte & 0x7f;
  while (byte & 0x80) {
    byte = buf[offset++];
    value = (value + 1) * 128 + (byte & 0x7f);
  }
  return { baseOffset: value, next: offset };
}

function inflateAt(buf: Buffer, offset: number): { data: Buffer; next: number } {
  const result = inflateSync(buf.subarray(offset), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
  const written = result.engine.bytesWritten;
  if (!written || written <= 0) throw new Error('zlib stream consumed no bytes');
  return { data: result.buffer, next: offset + written };
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let offset = 0;
  const readSize = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[offset++];
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(byte & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.allocUnsafe(targetSize);
  let written = 0;
  while (offset < delta.length) {
    const op = delta[offset++];
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) copyOffset += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit += 1) {
        if (op & (1 << bit)) copySize += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op !== 0) {
      const literal = op & 0x7f;
      delta.copy(out, written, offset, offset + literal);
      offset += literal;
      written += literal;
    } else {
      throw new Error('delta opcode 0 is invalid');
    }
  }
  if (written !== targetSize) throw new Error('delta size mismatch');
  return out;
}

/** Read a packfile (v2 or v3) into resolved objects. `resolveBase` answers bases a thin pack names. */
function readPack(pack: Buffer, resolveBase?: ObjectLookup): Map<string, GitObject> {
  if (pack.length < 32 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('not a packfile');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`pack version ${version}`);
  const count = pack.readUInt32BE(8);
  const trailer = pack.subarray(pack.length - 20).toString('hex');
  const computed = sha1Hex(pack.subarray(0, pack.length - 20));
  if (trailer !== computed) throw new Error('pack trailer checksum mismatch');
  const entries: PackEntry[] = [];
  const byOffset = new Map<number, PackEntry>();
  const deltas: Array<{ entry: PackEntry; baseOid: string | null; baseOffset: number | null }> = [];
  let offset = 12;
  for (let index = 0; index < count; index += 1) {
    const entryOffset = offset;
    const first = pack[offset];
    const typeCode = (first >> 4) & 0x07;
    const { size, next } = readPackVarint(pack, offset);
    offset = next;
    if (typeCode === 6) {
      const { baseOffset, next: afterBase } = readPackOfsBase(pack, offset);
      offset = afterBase;
      const { data, next: afterData } = inflateAt(pack, offset);
      offset = afterData;
      const entry: PackEntry = { offset: entryOffset, type: 'blob', size, data, oid: '' };
      entries.push(entry);
      byOffset.set(entryOffset, entry);
      deltas.push({ entry, baseOid: null, baseOffset: entryOffset - baseOffset });
    } else if (typeCode === 7) {
      const baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
      const { data, next: afterData } = inflateAt(pack, offset);
      offset = afterData;
      const entry: PackEntry = { offset: entryOffset, type: 'blob', size, data, oid: '' };
      entries.push(entry);
      byOffset.set(entryOffset, entry);
      deltas.push({ entry, baseOid, baseOffset: null });
    } else {
      const type = OBJECT_CODE_TYPE[typeCode];
      if (type === undefined) throw new Error(`unknown pack object type ${typeCode}`);
      const { data, next: afterData } = inflateAt(pack, offset);
      offset = afterData;
      const oid = hashObject(type, data);
      const entry: PackEntry = { offset: entryOffset, type, size, data, oid };
      entries.push(entry);
      byOffset.set(entryOffset, entry);
    }
  }
  const objects = new Map<string, GitObject>();
  for (const entry of entries) {
    if (entry.oid !== '') objects.set(entry.oid, { type: entry.type, data: entry.data });
  }
  // Resolve deltas, in offset order, until none is left.
  let pending = deltas;
  for (let round = 0; round < pending.length + 2 && pending.length > 0; round += 1) {
    const nextPending: typeof pending = [];
    for (const item of pending) {
      let base: GitObject | undefined;
      if (item.baseOffset !== null) {
        const baseEntry = byOffset.get(item.baseOffset);
        if (baseEntry !== undefined && baseEntry.oid !== '') base = objects.get(baseEntry.oid);
      } else if (item.baseOid !== null) {
        base = objects.get(item.baseOid) ?? resolveBase?.(item.baseOid);
      }
      if (base === undefined) {
        nextPending.push(item);
        continue;
      }
      const data = applyDelta(base.data, item.entry.data);
      item.entry.type = base.type;
      item.entry.data = data;
      item.entry.oid = hashObject(base.type, data);
      objects.set(item.entry.oid, { type: base.type, data });
    }
    pending = nextPending;
  }
  if (pending.length > 0) throw new Error('unresolved delta in packfile');
  return objects;
}

function writePackObjectHeader(type: ObjectType, size: number): Buffer {
  const bytes: number[] = [];
  let first = (OBJECT_TYPE_CODE[type] << 4) | (size & 0x0f);
  size >>= 4;
  if (size > 0) first |= 0x80;
  bytes.push(first);
  while (size > 0) {
    let byte = size & 0x7f;
    size >>= 7;
    if (size > 0) byte |= 0x80;
    bytes.push(byte);
  }
  return Buffer.from(bytes);
}

/** Build a packfile v2 from plain objects (no deltas): the order is the caller's. */
function writePack(objects: Iterable<GitObject>): Buffer {
  const list = [...objects];
  const head = Buffer.alloc(12);
  head.write('PACK', 0, 'ascii');
  head.writeUInt32BE(2, 4);
  head.writeUInt32BE(list.length, 8);
  const parts: Buffer[] = [head];
  for (const object of list) {
    parts.push(writePackObjectHeader(object.type, object.data.length));
    parts.push(deflateSync(object.data, { level: 6 }));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, Buffer.from(sha1Hex(body), 'hex')]);
}

// -------------------------------------------------------------------------------------------
// The store: repositories, issues, pull requests, labels, comments
// -------------------------------------------------------------------------------------------

interface Label {
  id: number;
  node_id: string;
  name: string;
  color: string;
  description: string;
  default: boolean;
}

interface IssueComment {
  id: number;
  node_id: string;
  body: string;
  user: { login: string; id: number };
  created_at: string;
  updated_at: string;
}

interface Issue {
  id: number;
  node_id: string;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: Label[];
  user: { login: string; id: number };
  comments: IssueComment[];
  created_at: string;
  updated_at: string;
  closed_at: string | null;
}

interface PullRequest {
  id: number;
  node_id: string;
  number: number;
  state: 'open' | 'closed';
  title: string;
  body: string;
  headRef: string;
  baseRef: string;
  headSha: string;
  baseSha: string;
  baseShaAtCreation: string;
  merged: boolean;
  merged_at: string | null;
  merge_commit_sha: string | null;
  user: { login: string; id: number };
  created_at: string;
  updated_at: string;
  closed_at: string | null;
}

interface Repo {
  id: number;
  node_id: string;
  name: string;
  owner: string;
  description: string;
  private: boolean;
  default_branch: string;
  created_at: string;
  updated_at: string;
  pushed_at: string;
  objects: Map<string, GitObject>;
  refs: Map<string, string>;
  issues: Map<number, Issue>;
  pulls: Map<number, PullRequest>;
  labels: Map<string, Label>;
  numberSeq: number;
}

const repos = new Map<string, Repo>();
let nextRepoId = 5000;
let nextIssueId = 10000;
let nextPullId = 20000;
let nextLabelId = 30000;
let nextCommentId = 40000;
let packCacheSeq = 0;

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}

function newRepo(name: string, options: { private?: boolean; description?: string }): Repo {
  const id = nextRepoId;
  nextRepoId += 1;
  const now = clockIso();
  const repo: Repo = {
    id,
    node_id: globalId('Repository', id),
    name,
    owner: VIEWER_LOGIN,
    description: options.description ?? '',
    private: options.private ?? false,
    default_branch: DEFAULT_BRANCH,
    created_at: now,
    updated_at: now,
    pushed_at: now,
    objects: new Map(),
    refs: new Map(),
    issues: new Map(),
    pulls: new Map(),
    labels: new Map(),
    numberSeq: 0,
  };
  repos.set(repoKey(VIEWER_LOGIN, name), repo);
  return repo;
}

function getRepo(owner: string, name: string): Repo | undefined {
  if (owner !== VIEWER_LOGIN) return undefined;
  return repos.get(repoKey(owner, name));
}

function repoObject(repo: Repo): Record<string, unknown> {
  return {
    id: repo.id,
    node_id: repo.node_id,
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: VIEWER_ID, type: 'User', avatar_url: '', html_url: '' },
    private: repo.private,
    html_url: '',
    description: repo.description,
    fork: false,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    created_at: repo.created_at,
    updated_at: repo.updated_at,
    pushed_at: repo.pushed_at,
    git_url: '',
    ssh_url: '',
    clone_url: '',
    homepage: '',
    size: 0,
    stargazers_count: 0,
    watchers_count: 0,
    language: null,
    has_issues: true,
    has_projects: true,
    has_downloads: true,
    has_wiki: true,
    has_pages: false,
    has_discussions: false,
    forks_count: 0,
    mirror_url: null,
    archived: false,
    disabled: false,
    open_issues_count: [...repo.issues.values()].filter((issue) => issue.state === 'open').length,
    license: null,
    allow_forking: true,
    is_template: false,
    visibility: repo.private ? 'private' : 'public',
    default_branch: repo.default_branch,
    permissions: { admin: true, maintain: true, push: true, triage: true, pull: true },
  };
}

function issueObject(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: issue.id,
    node_id: issue.node_id,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    user: { login: issue.user.login, id: issue.user.id, type: 'User' },
    labels: issue.labels.map((label) => ({ id: label.id, node_id: label.node_id, name: label.name, color: label.color, description: label.description, default: label.default })),
    assignee: null,
    assignees: [],
    milestone: null,
    locked: false,
    comments: issue.comments.length,
    created_at: issue.created_at,
    updated_at: issue.updated_at,
    closed_at: issue.closed_at,
    author_association: 'OWNER',
    html_url: '',
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    labels_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/labels`,
    comments_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/comments`,
    events_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/events`,
  };
}

function pullObject(repo: Repo, pull: PullRequest): Record<string, unknown> {
  const headSha = repo.refs.get(`refs/heads/${pull.headRef}`) ?? pull.headSha;
  const baseSha = repo.refs.get(`refs/heads/${pull.baseRef}`) ?? pull.baseSha;
  return {
    id: pull.id,
    node_id: pull.node_id,
    number: pull.number,
    state: pull.state,
    title: pull.title,
    body: pull.body,
    user: { login: pull.user.login, id: pull.user.id, type: 'User' },
    created_at: pull.created_at,
    updated_at: pull.updated_at,
    closed_at: pull.closed_at,
    merged_at: pull.merged_at,
    merge_commit_sha: pull.merge_commit_sha,
    merged: pull.merged,
    mergeable: pullMergeable(repo, pull),
    mergeable_state: pullMergeable(repo, pull) === 'MERGEABLE' ? 'clean' : 'dirty',
    draft: false,
    locked: false,
    maintainer_can_modify: false,
    commits: 1,
    additions: 0,
    deletions: 0,
    changed_files: 0,
    head: { label: `${repo.owner}:${pull.headRef}`, ref: pull.headRef, sha: headSha, user: { login: repo.owner, id: VIEWER_ID }, repo: repoObject(repo) },
    base: { label: `${repo.owner}:${pull.baseRef}`, ref: pull.baseRef, sha: baseSha, user: { login: repo.owner, id: VIEWER_ID }, repo: repoObject(repo) },
    html_url: '',
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}`,
    diff_url: '',
    patch_url: '',
    issue_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${pull.number}`,
    commits_url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}/commits`,
    review_comments_url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}/comments`,
    comments_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${pull.number}/comments`,
    statuses_url: '',
    assignee: null,
    assignees: [],
    requested_reviewers: [],
    requested_teams: [],
    labels: [],
    milestone: null,
    author_association: 'OWNER',
    auto_merge: null,
  };
}

function putObject(repo: Repo, type: ObjectType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}

function repoLookup(repo: Repo): ObjectLookup {
  return (oid: string) => repo.objects.get(oid);
}

/** The commit at a branch tip, or null when the branch is unborn or unknown. */
function branchTip(repo: Repo, branch: string): string | null {
  return repo.refs.get(`refs/heads/${branch}`) ?? null;
}

/** Commits from a tip, newest first, following first parents only. */
function commitList(repo: Repo, tip: string): CommitView[] {
  const out: CommitView[] = [];
  const seen = new Set<string>();
  let current: string | null = tip;
  while (current !== null && !seen.has(current)) {
    seen.add(current);
    const object = repo.objects.get(current);
    if (object === undefined || object.type !== 'commit') break;
    const view = parseCommit(object.data);
    out.push(view);
    current = view.parents[0] ?? null;
  }
  return out;
}

/** Create a commit on `branch` that sets `path` to `content` (or deletes it when content is null). */
function commitFile(
  repo: Repo,
  branch: string,
  path: string,
  content: Buffer | null,
  message: string,
): { commitSha: string; blobSha: string | null } {
  const tip = branchTip(repo, branch);
  const baseFiles = new Map<string, { mode: string; oid: string }>();
  if (tip !== null) {
    const view = parseCommit(repo.objects.get(tip)!.data);
    for (const [filePath, entry] of flattenTree(view.tree, repoLookup(repo))) baseFiles.set(filePath, entry);
  }
  let blobSha: string | null = null;
  if (content !== null) {
    blobSha = putObject(repo, 'blob', content);
    baseFiles.set(path, { mode: '100644', oid: blobSha });
  } else {
    baseFiles.delete(path);
  }
  const treeOid = treeFromFiles(baseFiles, (type, data) => putObject(repo, type, data));
  const stamp = clockSec();
  const author = `${VIEWER_NAME} <${VIEWER_EMAIL}>`;
  const commitData = buildCommit({
    tree: treeOid,
    parents: tip === null ? [] : [tip],
    message,
    author,
    committer: author,
    timestamp: stamp,
  });
  const commitSha = putObject(repo, 'commit', commitData);
  repo.refs.set(`refs/heads/${branch}`, commitSha);
  repo.updated_at = clockIso();
  repo.pushed_at = repo.updated_at;
  packCacheSeq += 1;
  return { commitSha, blobSha };
}

/** The files a pull request changes, between its base snapshot and its head tip. */
function pullFiles(repo: Repo, pull: PullRequest): Array<{ filename: string; status: string; additions: number; deletions: number; changes: number }> {
  const lookup = repoLookup(repo);
  const baseCommit = repo.objects.get(pull.baseShaAtCreation);
  const headCommit = repo.objects.get(pull.headSha);
  if (baseCommit === undefined || headCommit === undefined) return [];
  const baseFiles = flattenTree(parseCommit(baseCommit.data).tree, lookup);
  const headFiles = flattenTree(parseCommit(headCommit.data).tree, lookup);
  const out: Array<{ filename: string; status: string; additions: number; deletions: number; changes: number }> = [];
  const paths = new Set([...baseFiles.keys(), ...headFiles.keys()]);
  for (const path of [...paths].sort()) {
    const base = baseFiles.get(path);
    const head = headFiles.get(path);
    if (base !== undefined && head !== undefined && base.oid === head.oid) continue;
    if (base === undefined && head !== undefined) {
      const blob = repo.objects.get(head.oid);
      const additions = blob === undefined ? 0 : countLines(blob.data);
      out.push({ filename: path, status: 'added', additions, deletions: 0, changes: additions });
    } else if (base !== undefined && head === undefined) {
      const blob = repo.objects.get(base.oid);
      const deletions = blob === undefined ? 0 : countLines(blob.data);
      out.push({ filename: path, status: 'removed', additions: 0, deletions, changes: deletions });
    } else if (base !== undefined && head !== undefined) {
      const prev = repo.objects.get(base.oid)?.data ?? Buffer.alloc(0);
      const next = repo.objects.get(head.oid)?.data ?? Buffer.alloc(0);
      const { additions, deletions } = lineDiff(prev, next);
      out.push({ filename: path, status: 'modified', additions, deletions, changes: additions + deletions });
    }
  }
  return out;
}

/** MERGEABLE when a squash merge applies cleanly, CONFLICTING when the base moved under a changed path. */
function pullMergeable(repo: Repo, pull: PullRequest): 'MERGEABLE' | 'CONFLICTING' {
  if (pull.state !== 'open') return 'MERGEABLE';
  const lookup = repoLookup(repo);
  const baseAtCreation = repo.objects.get(pull.baseShaAtCreation);
  const headCommit = repo.objects.get(pull.headSha);
  const baseTipOid = branchTip(repo, pull.baseRef);
  const baseTip = baseTipOid === null ? undefined : repo.objects.get(baseTipOid);
  if (baseAtCreation === undefined || headCommit === undefined || baseTip === undefined) return 'MERGEABLE';
  const baseFiles = flattenTree(parseCommit(baseAtCreation.data).tree, lookup);
  const headFiles = flattenTree(parseCommit(headCommit.data).tree, lookup);
  const tipFiles = flattenTree(parseCommit(baseTip.data).tree, lookup);
  for (const [path, headEntry] of headFiles) {
    const baseEntry = baseFiles.get(path);
    if (baseEntry !== undefined && baseEntry.oid === headEntry.oid) continue;
    const tipEntry = tipFiles.get(path);
    if (tipEntry === undefined && baseEntry === undefined) continue;
    if (tipEntry !== undefined && baseEntry !== undefined && tipEntry.oid === baseEntry.oid) continue;
    if (tipEntry !== undefined && tipEntry.oid === headEntry.oid) continue;
    if (tipEntry === undefined && baseEntry === undefined) continue;
    return 'CONFLICTING';
  }
  for (const [path, baseEntry] of baseFiles) {
    if (headFiles.has(path)) continue;
    const tipEntry = tipFiles.get(path);
    if (tipEntry !== undefined && tipEntry.oid !== baseEntry.oid) return 'CONFLICTING';
  }
  return 'MERGEABLE';
}

/** Squash-merge a pull request onto its base branch. Returns the merge commit sha, or null when conflicted. */
function mergePullRequest(repo: Repo, pull: PullRequest): string | null {
  if (pull.state !== 'open') return null;
  if (pullMergeable(repo, pull) !== 'MERGEABLE') return null;
  const headCommit = repo.objects.get(pull.headSha);
  const baseTipOid = branchTip(repo, pull.baseRef);
  if (headCommit === undefined || baseTipOid === null) return null;
  const headTree = parseCommit(headCommit.data).tree;
  const stamp = clockSec();
  const author = `${VIEWER_NAME} <${VIEWER_EMAIL}>`;
  const commitData = buildCommit({
    tree: headTree,
    parents: [baseTipOid],
    message: `Merge pull request #${pull.number} from ${pull.headRef}\n\n${pull.title}`,
    author,
    committer: author,
    timestamp: stamp,
  });
  const mergeSha = putObject(repo, 'commit', commitData);
  repo.refs.set(`refs/heads/${pull.baseRef}`, mergeSha);
  pull.state = 'closed';
  pull.merged = true;
  pull.merged_at = clockIso();
  pull.merge_commit_sha = mergeSha;
  pull.closed_at = pull.merged_at;
  pull.updated_at = pull.merged_at;
  repo.updated_at = pull.merged_at;
  packCacheSeq += 1;
  return mergeSha;
}

function createIssue(repo: Repo, input: { title: string; body: string; labels?: string[] }): Issue | { error: string } {
  const labels: Label[] = [];
  for (const name of input.labels ?? []) {
    const label = repo.labels.get(name);
    if (label === undefined) return { error: `Label "${name}" does not exist` };
    labels.push(label);
  }
  repo.numberSeq += 1;
  const id = nextIssueId;
  nextIssueId += 1;
  const now = clockIso();
  const issue: Issue = {
    id,
    node_id: globalId('Issue', repo.id, repo.numberSeq),
    number: repo.numberSeq,
    title: input.title,
    body: input.body,
    state: 'open',
    labels,
    user: { login: VIEWER_LOGIN, id: VIEWER_ID },
    comments: [],
    created_at: now,
    updated_at: now,
    closed_at: null,
  };
  repo.issues.set(issue.number, issue);
  return issue;
}

function createPull(repo: Repo, input: { title: string; body: string; head: string; base: string }): PullRequest | { error: string } {
  const headTip = branchTip(repo, input.head);
  const baseTip = branchTip(repo, input.base);
  if (headTip === null) return { error: `head branch "${input.head}" does not exist` };
  if (baseTip === null) return { error: `base branch "${input.base}" does not exist` };
  for (const pull of repo.pulls.values()) {
    if (pull.state === 'open' && pull.headRef === input.head && pull.baseRef === input.base) {
      return { error: 'A pull request already exists for this head and base' };
    }
  }
  repo.numberSeq += 1;
  const id = nextPullId;
  nextPullId += 1;
  const now = clockIso();
  const pull: PullRequest = {
    id,
    node_id: globalId('PullRequest', repo.id, repo.numberSeq),
    number: repo.numberSeq,
    state: 'open',
    title: input.title,
    body: input.body,
    headRef: input.head,
    baseRef: input.base,
    headSha: headTip,
    baseSha: baseTip,
    baseShaAtCreation: baseTip,
    merged: false,
    merged_at: null,
    merge_commit_sha: null,
    user: { login: VIEWER_LOGIN, id: VIEWER_ID },
    created_at: now,
    updated_at: now,
    closed_at: null,
  };
  repo.pulls.set(pull.number, pull);
  return pull;
}

// -------------------------------------------------------------------------------------------
// HTTP plumbing: bodies, JSON replies, auth, pagination
// -------------------------------------------------------------------------------------------

const SHOP_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const ENV_URL = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (chunk: Buffer) => chunks.push(chunk));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function sendJson(res: ServerResponse, status: number, value: unknown, extraHeaders: Record<string, string> = {}): void {
  const body = Buffer.from(JSON.stringify(value), 'utf8');
  const headers: Record<string, string> = {
    'Content-Type': 'application/json; charset=utf-8',
    'Content-Length': String(body.length),
    'X-GitHub-Request-Id': nextRequestId(),
    ...extraHeaders,
  };
  res.writeHead(status, headers);
  res.end(body);
}

function sendBuffer(res: ServerResponse, status: number, body: Buffer, contentType: string, extraHeaders: Record<string, string> = {}): void {
  const headers: Record<string, string> = {
    'Content-Type': contentType,
    'Content-Length': String(body.length),
    ...extraHeaders,
  };
  res.writeHead(status, headers);
  res.end(body);
}

function restError(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message, documentation_url: '' });
}

function checkRestAuth(req: IncomingMessage, res: ServerResponse): boolean {
  if (SHOP_TOKEN === '') return true;
  const header = req.headers.authorization ?? '';
  if (header === `Bearer ${SHOP_TOKEN}`) return true;
  restError(res, 401, 'Requires authentication');
  return false;
}

function parseJsonBody(body: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (body.length === 0) return { ok: true, value: {} };
  try {
    return { ok: true, value: JSON.parse(body.toString('utf8')) };
  } catch {
    return { ok: false };
  }
}

function asObject(value: unknown): Record<string, unknown> {
  if (typeof value === 'object' && value !== null && !Array.isArray(value)) return value as Record<string, unknown>;
  return {};
}

function queryInt(query: URLSearchParams, name: string, fallback: number): number {
  const raw = query.get(name);
  if (raw === null) return fallback;
  const parsed = parseInt(raw, 10);
  return Number.isFinite(parsed) && parsed > 0 ? parsed : fallback;
}

function paginate<T>(req: IncomingMessage, items: readonly T[], query: URLSearchParams): { page: T[]; link: string } {
  const perPage = Math.min(Math.max(queryInt(query, 'per_page', 30), 1), 100);
  const page = Math.max(queryInt(query, 'page', 1), 1);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  let link = '';
  if (start + perPage < items.length) {
    const next = new URL(req.url ?? '/', `http://${req.headers.host ?? 'localhost'}`);
    next.searchParams.set('page', String(page + 1));
    next.searchParams.set('per_page', String(perPage));
    link = `<${next.toString()}>; rel="next"`;
    const lastPage = Math.ceil(items.length / perPage);
    const last = new URL(req.url ?? '/', `http://${req.headers.host ?? 'localhost'}`);
    last.searchParams.set('page', String(lastPage));
    last.searchParams.set('per_page', String(perPage));
    link += `, <${last.toString()}>; rel="last"`;
  }
  return { page: [...slice], link };
}

function parseIdent(raw: string): { name: string; email: string; date: string } {
  const match = /^(.*?) <([^>]*)> (\d+) [+-]\d{4}$/.exec(raw.trim());
  if (match === null) return { name: raw, email: '', date: clockIso() };
  return { name: match[1], email: match[2], date: new Date(Number(match[3]) * 1000).toISOString() };
}

/** Walk a tree path; returns the entry kind and oid, or null when the path does not exist. */
function resolveTreePath(repo: Repo, treeOid: string, segments: string[]): { kind: 'file' | 'dir'; oid: string; mode: string } | null {
  let currentOid = treeOid;
  for (let index = 0; index < segments.length; index += 1) {
    const object = repo.objects.get(currentOid);
    if (object === undefined || object.type !== 'tree') return null;
    const entry = parseTree(object.data).find((candidate) => candidate.name === segments[index]);
    if (entry === undefined) return null;
    if (index === segments.length - 1) {
      return { kind: entry.mode === '40000' ? 'dir' : 'file', oid: entry.oid, mode: entry.mode };
    }
    if (entry.mode !== '40000') return null;
    currentOid = entry.oid;
  }
  return null;
}

function commitObject(repo: Repo, sha: string): Record<string, unknown> | null {
  const object = repo.objects.get(sha);
  if (object === undefined || object.type !== 'commit') return null;
  const view = parseCommit(object.data);
  const author = parseIdent(view.author);
  const committer = parseIdent(view.committer);
  return {
    sha,
    node_id: globalId('Commit', repo.id, sha),
    commit: {
      author: { name: author.name, email: author.email, date: author.date },
      committer: { name: committer.name, email: committer.email, date: committer.date },
      // GitHub's API reports the message without the trailing newline the
      // stored commit carries; callers compare it exactly.
      message: view.message.replace(/\n+$/, ''),
      tree: { sha: view.tree, url: '' },
      url: '',
      comment_count: 0,
      verification: { verified: false, reason: 'unsigned', signature: null, payload: null },
    },
    url: '',
    html_url: '',
    comments_url: '',
    author: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    committer: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    parents: view.parents.map((parent) => ({ sha: parent, url: '' })),
  };
}

// -------------------------------------------------------------------------------------------
// REST v3
// -------------------------------------------------------------------------------------------

function restRouter(req: IncomingMessage, res: ServerResponse, body: Buffer): void {
  const url = new URL(req.url ?? '/', `http://${req.headers.host ?? 'localhost'}`);
  const rawPath = decodeURIComponent(url.pathname);
  const path = rawPath.replace(/\/+$/, '') || '/';
  const method = req.method ?? 'GET';
  const query = url.searchParams;

  if (!checkRestAuth(req, res)) return;

  const segments = path.split('/').filter((part) => part !== '');
  // segments[0] === 'api', segments[1] === 'v3'
  const rest = segments.slice(2);

  const parsed = parseJsonBody(body);
  if (!parsed.ok) {
    restError(res, 400, 'Problems parsing JSON');
    return;
  }
  const input = asObject(parsed.value);

  // GET /api/v3/
  if (rest.length === 0) {
    if (method !== 'GET') return restError(res, 404, 'Not Found');
    return sendJson(res, 200, {
      current_user_url: '/api/v3/user',
      current_user_authorizations_html_url: '',
      authorizations_url: '',
      code_search_url: '',
      commit_search_url: '',
      emails_url: '',
      emojis_url: '',
      events_url: '',
      feeds_url: '',
      followers_url: '',
      following_url: '',
      gists_url: '',
      hub_url: '',
      issue_search_url: '',
      issues_url: '',
      keys_url: '',
      label_search_url: '',
      notifications_url: '',
      organization_repositories_url: '',
      organization_url: '',
      public_gists_url: '',
      rate_limit_url: '/api/v3/rate_limit',
      repository_url: '/api/v3/repos/{owner}/{repo}',
      repository_search_url: '',
      current_user_repositories_url: '/api/v3/user/repos',
      search_url: '',
      starred_url: '',
      starred_gists_url: '',
      user_url: '/api/v3/users/{user}',
      user_organizations_url: '',
      user_repositories_url: '/api/v3/users/{user}/repos',
      user_search_url: '',
    }, { 'X-OAuth-Scopes': 'repo, read:org', 'X-Accepted-OAuth-Scopes': 'repo, read:org' });
  }

  // GET /api/v3/meta
  if (rest.length === 1 && rest[0] === 'meta') {
    if (method !== 'GET') return restError(res, 404, 'Not Found');
    return sendJson(res, 200, {
      verifiable_password_authentication: true,
      ssh_key_fingerprints: {},
      ssh_keys: [],
      hooks: [],
      git: [],
      web: [],
      api: [],
      packages: [],
      pages: [],
      importer: [],
      actions: [],
      dependabot: [],
      installed_version: FORGE_VERSION,
    });
  }

  // GET /api/v3/user
  if (rest.length === 1 && rest[0] === 'user') {
    if (method !== 'GET') return restError(res, 404, 'Not Found');
    return sendJson(res, 200, {
      login: VIEWER_LOGIN,
      id: VIEWER_ID,
      node_id: globalId('User', VIEWER_ID),
      avatar_url: '',
      gravatar_id: '',
      url: '/api/v3/user',
      html_url: '',
      followers_url: '',
      following_url: '',
      gists_url: '',
      starred_url: '',
      subscriptions_url: '',
      organizations_url: '',
      repos_url: '/api/v3/user/repos',
      events_url: '',
      received_events_url: '',
      type: 'User',
      site_admin: false,
      name: VIEWER_NAME,
      company: null,
      blog: '',
      location: null,
      email: VIEWER_EMAIL,
      hireable: null,
      bio: null,
      twitter_username: null,
      public_repos: repos.size,
      public_gists: 0,
      followers: 0,
      following: 0,
      created_at: clockIso(),
      updated_at: clockIso(),
    });
  }

  // /api/v3/user/repos
  if (rest.length === 2 && rest[0] === 'user' && rest[1] === 'repos') {
    if (method === 'GET') {
      const all = [...repos.values()].filter((repo) => repo.owner === VIEWER_LOGIN).map((repo) => repoObject(repo));
      const { page, link } = paginate(req, all, query);
      return sendJson(res, 200, page, link === '' ? {} : { Link: link });
    }
    if (method === 'POST') {
      const name = typeof input.name === 'string' ? input.name.trim() : '';
      if (name === '') return restError(res, 422, 'name is required');
      if (!/^[A-Za-z0-9._-]+$/.test(name)) return restError(res, 422, 'name is invalid');
      if (repos.has(repoKey(VIEWER_LOGIN, name))) return restError(res, 422, 'Repository already exists');
      const repo = newRepo(name, {
        private: input.private === true,
        description: typeof input.description === 'string' ? input.description : '',
      });
      return sendJson(res, 201, repoObject(repo));
    }
    return restError(res, 404, 'Not Found');
  }

  // /api/v3/repos/{owner}/{repo}[...]
  if (rest.length >= 3 && rest[0] === 'repos') {
    const owner = rest[1];
    const name = rest[2];
    const repo = getRepo(owner, name);
    const tail = rest.slice(3);

    // GET/PATCH/DELETE /repos/{o}/{r}
    if (tail.length === 0) {
      if (repo === undefined) return restError(res, 404, 'Not Found');
      if (method === 'GET') return sendJson(res, 200, repoObject(repo));
      if (method === 'PATCH') {
        if (typeof input.description === 'string') repo.description = input.description;
        if (input.private === true || input.private === false) repo.private = input.private;
        if (typeof input.name === 'string' && input.name !== '' && input.name !== repo.name) {
          if (repos.has(repoKey(owner, input.name))) return restError(res, 422, 'Repository already exists');
          repos.delete(repoKey(owner, repo.name));
          repo.name = input.name;
          repos.set(repoKey(owner, repo.name), repo);
        }
        repo.updated_at = clockIso();
        return sendJson(res, 200, repoObject(repo));
      }
      if (method === 'DELETE') {
        repos.delete(repoKey(owner, name));
        res.writeHead(204, { 'X-GitHub-Request-Id': nextRequestId() });
        res.end();
        return;
      }
      return restError(res, 404, 'Not Found');
    }

    if (repo === undefined) return restError(res, 404, 'Not Found');

    // GET /repos/{o}/{r}/branches
    if (tail.length === 1 && tail[0] === 'branches' && method === 'GET') {
      const branches = [...repo.refs.keys()]
        .filter((ref) => ref.startsWith('refs/heads/'))
        .map((ref) => ref.slice('refs/heads/'.length))
        .sort()
        .map((branch) => ({
          name: branch,
          commit: { sha: repo.refs.get(`refs/heads/${branch}`)!, url: '' },
          protected: false,
        }));
      const { page, link } = paginate(req, branches, query);
      return sendJson(res, 200, page, link === '' ? {} : { Link: link });
    }

    // GET /repos/{o}/{r}/branches/{branch}
    if (tail.length === 2 && tail[0] === 'branches' && method === 'GET') {
      const sha = branchTip(repo, tail[1]);
      if (sha === null) return restError(res, 404, 'Branch not found');
      return sendJson(res, 200, { name: tail[1], commit: { sha, url: '' }, protected: false });
    }

    // GET /repos/{o}/{r}/commits[?sha=] and /commits/{sha}
    if (tail[0] === 'commits' && method === 'GET') {
      if (tail.length === 2) {
        const single = commitObject(repo, tail[1]);
        if (single === null) return restError(res, 404, 'Not Found');
        return sendJson(res, 200, single);
      }
      if (tail.length === 1) {
        const branch = query.get('sha') ?? repo.default_branch;
        const tip = branchTip(repo, branch);
        if (tip === null) return sendJson(res, 200, []);
        const list: Array<Record<string, unknown>> = [];
        const seen = new Set<string>();
        let current: string | null = tip;
        while (current !== null && !seen.has(current)) {
          seen.add(current);
          const single = commitObject(repo, current);
          if (single === null) break;
          list.push(single);
          const object = repo.objects.get(current);
          if (object === undefined || object.type !== 'commit') break;
          current = parseCommit(object.data).parents[0] ?? null;
        }
        const { page, link } = paginate(req, list, query);
        return sendJson(res, 200, page, link === '' ? {} : { Link: link });
      }
    }

    // POST /repos/{o}/{r}/git/refs
    if (tail.length === 2 && tail[0] === 'git' && tail[1] === 'refs' && method === 'POST') {
      const ref = typeof input.ref === 'string' ? input.ref : '';
      const sha = typeof input.sha === 'string' ? input.sha : '';
      if (!ref.startsWith('refs/') || !isOid(sha)) return restError(res, 422, 'Invalid ref or sha');
      if (repo.refs.has(ref)) return restError(res, 422, 'Reference already exists');
      const target = repo.objects.get(sha);
      if (target === undefined) return restError(res, 422, 'Object does not exist');
      repo.refs.set(ref, sha);
      packCacheSeq += 1;
      return sendJson(res, 201, {
        ref,
        node_id: globalId('Ref', repo.id, ref),
        url: `/api/v3/repos/${owner}/${name}/git/refs/${ref.slice(5)}`,
        object: { type: target.type, sha },
      });
    }

    // GET /repos/{o}/{r}/git/refs/{...}
    if (tail.length >= 3 && tail[0] === 'git' && tail[1] === 'refs' && method === 'GET') {
      const ref = `refs/${tail.slice(2).join('/')}`;
      const sha = repo.refs.get(ref);
      if (sha === undefined) return restError(res, 404, 'Not Found');
      const target = repo.objects.get(sha);
      return sendJson(res, 200, {
        ref,
        node_id: globalId('Ref', repo.id, ref),
        url: `/api/v3/repos/${owner}/${name}/git/refs/${ref.slice(5)}`,
        object: { type: target?.type ?? 'commit', sha },
      });
    }

    // GET/PUT/DELETE /repos/{o}/{r}/contents[/{path}]
    if (tail.length >= 1 && tail[0] === 'contents') {
      const filePath = tail.slice(1).join('/');
      const branch = query.get('ref') ?? repo.default_branch;
      const tip = branchTip(repo, branch);
      if (method === 'GET') {
        if (tip === null) return restError(res, 404, 'Not Found');
        const view = parseCommit(repo.objects.get(tip)!.data);
        const segments = filePath.split('/').filter((part) => part !== '');
        if (segments.length === 0) {
          const entries = parseTree(repo.objects.get(view.tree)!.data).map((entry) => ({
            type: entry.mode === '40000' ? 'dir' : 'file',
            size: entry.mode === '40000' ? 0 : (repo.objects.get(entry.oid)?.data.length ?? 0),
            name: entry.name,
            path: entry.name,
            sha: entry.oid,
            url: '',
            git_url: '',
            html_url: '',
            download_url: entry.mode === '40000' ? null : '',
            _links: { self: '', git: '', html: '' },
          }));
          return sendJson(res, 200, entries);
        }
        const found = resolveTreePath(repo, view.tree, segments);
        if (found === null) return restError(res, 404, 'Not Found');
        if (found.kind === 'dir') {
          const entries = parseTree(repo.objects.get(found.oid)!.data).map((entry) => ({
            type: entry.mode === '40000' ? 'dir' : 'file',
            size: entry.mode === '40000' ? 0 : (repo.objects.get(entry.oid)?.data.length ?? 0),
            name: entry.name,
            path: `${filePath}/${entry.name}`,
            sha: entry.oid,
            url: '',
            git_url: '',
            html_url: '',
            download_url: entry.mode === '40000' ? null : '',
            _links: { self: '', git: '', html: '' },
          }));
          return sendJson(res, 200, entries);
        }
        const blob = repo.objects.get(found.oid);
        if (blob === undefined) return restError(res, 404, 'Not Found');
        return sendJson(res, 200, {
          type: 'file',
          encoding: 'base64',
          size: blob.data.length,
          name: segments[segments.length - 1],
          path: filePath,
          content: blob.data.toString('base64'),
          sha: found.oid,
          url: '',
          git_url: '',
          html_url: '',
          download_url: '',
          _links: { self: '', git: '', html: '' },
        });
      }
      if (method === 'PUT') {
        const message = typeof input.message === 'string' ? input.message : 'Update file';
        const contentRaw = typeof input.content === 'string' ? input.content : '';
        if (contentRaw === '') return restError(res, 422, 'content is required');
        const content = b64decode(contentRaw);
        const targetBranch = typeof input.branch === 'string' && input.branch !== '' ? input.branch : branch;
        const targetTip = branchTip(repo, targetBranch);
        let existingSha: string | null = null;
        if (targetTip !== null) {
          const view = parseCommit(repo.objects.get(targetTip)!.data);
          const found = resolveTreePath(repo, view.tree, filePath.split('/').filter((part) => part !== ''));
          if (found !== null && found.kind === 'file') existingSha = found.oid;
        }
        const givenSha = typeof input.sha === 'string' ? input.sha : '';
        if (existingSha !== null) {
          if (givenSha === '' || givenSha !== existingSha) return restError(res, 409, 'sha does not match');
        } else if (givenSha !== '') {
          return restError(res, 422, 'sha does not match a file');
        }
        const { commitSha, blobSha } = commitFile(repo, targetBranch, filePath, content, message);
        const status = existingSha === null ? 201 : 200;
        return sendJson(res, status, {
          content: { name: filePath.split('/').pop(), path: filePath, sha: blobSha, size: content.length, url: '', git_url: '', html_url: '', download_url: '', type: 'file', encoding: 'base64' },
          commit: { sha: commitSha, node_id: globalId('Commit', repo.id, commitSha), message, author: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: clockIso() }, committer: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: clockIso() }, parents: targetTip === null ? [] : [{ sha: targetTip }] },
        });
      }
      if (method === 'DELETE') {
        const message = typeof input.message === 'string' ? input.message : 'Delete file';
        const givenSha = typeof input.sha === 'string' ? input.sha : '';
        const targetBranch = typeof input.branch === 'string' && input.branch !== '' ? input.branch : branch;
        const targetTip = branchTip(repo, targetBranch);
        if (targetTip === null) return restError(res, 404, 'Not Found');
        const view = parseCommit(repo.objects.get(targetTip)!.data);
        const found = resolveTreePath(repo, view.tree, filePath.split('/').filter((part) => part !== ''));
        if (found === null || found.kind !== 'file') return restError(res, 404, 'Not Found');
        if (givenSha === '' || givenSha !== found.oid) return restError(res, 409, 'sha does not match');
        const { commitSha } = commitFile(repo, targetBranch, filePath, null, message);
        return sendJson(res, 200, {
          content: null,
          commit: { sha: commitSha, node_id: globalId('Commit', repo.id, commitSha), message, author: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: clockIso() }, committer: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: clockIso() }, parents: [{ sha: targetTip }] },
        });
      }
      return restError(res, 404, 'Not Found');
    }

    // GET/POST /repos/{o}/{r}/labels
    if (tail.length === 1 && tail[0] === 'labels') {
      if (method === 'GET') {
        const all = [...repo.labels.values()].map((label) => ({ id: label.id, node_id: label.node_id, url: '', name: label.name, color: label.color, description: label.description, default: label.default }));
        return sendJson(res, 200, all);
      }
      if (method === 'POST') {
        const name = typeof input.name === 'string' ? input.name.trim() : '';
        if (name === '') return restError(res, 422, 'name is required');
        if (repo.labels.has(name)) return restError(res, 422, 'Label already exists');
        const id = nextLabelId;
        nextLabelId += 1;
        const label: Label = {
          id,
          node_id: globalId('Label', repo.id, id),
          name,
          color: typeof input.color === 'string' ? input.color : 'ededed',
          description: typeof input.description === 'string' ? input.description : '',
          default: false,
        };
        repo.labels.set(name, label);
        return sendJson(res, 201, { id: label.id, node_id: label.node_id, url: '', name: label.name, color: label.color, description: label.description, default: label.default });
      }
      return restError(res, 404, 'Not Found');
    }

    // /repos/{o}/{r}/issues[/...]
    if (tail[0] === 'issues') {
      // GET/POST /issues
      if (tail.length === 1) {
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          const sort = query.get('sort') ?? 'created';
          const direction = query.get('direction') ?? 'desc';
          let list = [...repo.issues.values()];
          if (state !== 'all') list = list.filter((issue) => issue.state === state);
          list.sort((a, b) => {
            const byNumber = a.number - b.number;
            const byCreated = a.created_at < b.created_at ? -1 : a.created_at > b.created_at ? 1 : byNumber;
            const key = sort === 'created' ? byCreated : byNumber;
            return direction === 'asc' ? key : -key;
          });
          const { page, link } = paginate(req, list.map((issue) => issueObject(repo, issue)), query);
          return sendJson(res, 200, page, link === '' ? {} : { Link: link });
        }
        if (method === 'POST') {
          const title = typeof input.title === 'string' ? input.title.trim() : '';
          if (title === '') return restError(res, 422, 'title is required');
          const labels = Array.isArray(input.labels) ? input.labels.filter((item): item is string => typeof item === 'string') : [];
          const created = createIssue(repo, { title, body: typeof input.body === 'string' ? input.body : '', labels });
          if ('error' in created) return restError(res, 422, created.error);
          return sendJson(res, 201, issueObject(repo, created));
        }
        return restError(res, 404, 'Not Found');
      }
      // /issues/{number}
      const number = parseInt(tail[1], 10);
      if (!Number.isFinite(number)) return restError(res, 404, 'Not Found');
      const issue = repo.issues.get(number);
      if (tail.length === 2) {
        if (issue === undefined) return restError(res, 404, 'Not Found');
        if (method === 'GET') return sendJson(res, 200, issueObject(repo, issue));
        if (method === 'PATCH') {
          if (typeof input.title === 'string') issue.title = input.title;
          if (typeof input.body === 'string') issue.body = input.body;
          if (input.state === 'open' || input.state === 'closed') {
            issue.state = input.state;
            issue.closed_at = input.state === 'closed' ? clockIso() : null;
          }
          issue.updated_at = clockIso();
          return sendJson(res, 200, issueObject(repo, issue));
        }
        return restError(res, 404, 'Not Found');
      }
      // /issues/{number}/comments
      if (tail.length === 3 && tail[2] === 'comments') {
        if (issue === undefined) return restError(res, 404, 'Not Found');
        if (method === 'GET') {
          const comments = issue.comments.map((comment) => ({
            id: comment.id,
            node_id: comment.node_id,
            url: '',
            html_url: '',
            body: comment.body,
            user: { login: comment.user.login, id: comment.user.id, type: 'User' },
            created_at: comment.created_at,
            updated_at: comment.updated_at,
            author_association: 'OWNER',
          }));
          const { page, link } = paginate(req, comments, query);
          return sendJson(res, 200, page, link === '' ? {} : { Link: link });
        }
        if (method === 'POST') {
          const bodyText = typeof input.body === 'string' ? input.body : '';
          if (bodyText === '') return restError(res, 422, 'body is required');
          const id = nextCommentId;
          nextCommentId += 1;
          const now = clockIso();
          const comment: IssueComment = {
            id,
            node_id: globalId('IssueComment', repo.id, id),
            body: bodyText,
            user: { login: VIEWER_LOGIN, id: VIEWER_ID },
            created_at: now,
            updated_at: now,
          };
          issue.comments.push(comment);
          issue.updated_at = now;
          return sendJson(res, 201, {
            id: comment.id,
            node_id: comment.node_id,
            url: '',
            html_url: '',
            body: comment.body,
            user: { login: comment.user.login, id: comment.user.id, type: 'User' },
            created_at: comment.created_at,
            updated_at: comment.updated_at,
            author_association: 'OWNER',
          });
        }
        return restError(res, 404, 'Not Found');
      }
      return restError(res, 404, 'Not Found');
    }

    // /repos/{o}/{r}/pulls[/...]
    if (tail[0] === 'pulls') {
      // GET/POST /pulls
      if (tail.length === 1) {
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          let list = [...repo.pulls.values()];
          if (state !== 'all') list = list.filter((pull) => pull.state === state);
          list.sort((a, b) => b.number - a.number);
          const { page, link } = paginate(req, list.map((pull) => pullObject(repo, pull)), query);
          return sendJson(res, 200, page, link === '' ? {} : { Link: link });
        }
        if (method === 'POST') {
          const title = typeof input.title === 'string' ? input.title.trim() : '';
          const head = typeof input.head === 'string' ? input.head : '';
          const base = typeof input.base === 'string' ? input.base : repo.default_branch;
          if (title === '' || head === '') return restError(res, 422, 'title and head are required');
          const created = createPull(repo, { title, body: typeof input.body === 'string' ? input.body : '', head, base });
          if ('error' in created) return restError(res, 422, created.error);
          return sendJson(res, 201, pullObject(repo, created));
        }
        return restError(res, 404, 'Not Found');
      }
      const number = parseInt(tail[1], 10);
      if (!Number.isFinite(number)) return restError(res, 404, 'Not Found');
      const pull = repo.pulls.get(number);
      if (tail.length === 2) {
        if (pull === undefined) return restError(res, 404, 'Not Found');
        if (method === 'GET') return sendJson(res, 200, pullObject(repo, pull));
        if (method === 'PATCH') {
          if (typeof input.title === 'string') pull.title = input.title;
          if (typeof input.body === 'string') pull.body = input.body;
          if (input.state === 'closed') {
            pull.state = 'closed';
            pull.closed_at = clockIso();
          }
          pull.updated_at = clockIso();
          return sendJson(res, 200, pullObject(repo, pull));
        }
        return restError(res, 404, 'Not Found');
      }
      // GET /pulls/{n}/files
      if (tail.length === 3 && tail[2] === 'files' && method === 'GET') {
        if (pull === undefined) return restError(res, 404, 'Not Found');
        const files = pullFiles(repo, pull).map((file) => {
          const lookup = repoLookup(repo);
          const headCommit = repo.objects.get(pull.headSha);
          let sha = '';
          if (headCommit !== undefined) {
            const entry = flattenTree(parseCommit(headCommit.data).tree, lookup).get(file.filename);
            if (entry !== undefined) sha = entry.oid;
          }
          return { sha, filename: file.filename, status: file.status, additions: file.additions, deletions: file.deletions, changes: file.changes, blob_url: '', raw_url: '', contents_url: '' };
        });
        return sendJson(res, 200, files);
      }
      // PUT /pulls/{n}/merge
      if (tail.length === 3 && tail[2] === 'merge' && method === 'PUT') {
        if (pull === undefined) return restError(res, 404, 'Not Found');
        const mergeMethod = typeof input.merge_method === 'string' ? input.merge_method : 'squash';
        if (mergeMethod !== 'squash') return restError(res, 405, 'Only squash merges are supported');
        if (pull.state !== 'open') return restError(res, 405, 'Pull request is not open');
        if (pullMergeable(repo, pull) !== 'MERGEABLE') return restError(res, 405, 'Merge conflict');
        const mergeSha = mergePullRequest(repo, pull);
        if (mergeSha === null) return restError(res, 405, 'Merge conflict');
        return sendJson(res, 200, { sha: mergeSha, merged: true, message: `Pull request #${pull.number} successfully merged` });
      }
      // GET /pulls/{n}/commits
      if (tail.length === 3 && tail[2] === 'commits' && method === 'GET') {
        if (pull === undefined) return restError(res, 404, 'Not Found');
        const list: Array<Record<string, unknown>> = [];
        const seen = new Set<string>();
        let current: string | null = pull.headSha;
        while (current !== null && !seen.has(current)) {
          seen.add(current);
          const single = commitObject(repo, current);
          if (single === null) break;
          list.push(single);
          const object = repo.objects.get(current);
          if (object === undefined || object.type !== 'commit') break;
          current = parseCommit(object.data).parents[0] ?? null;
        }
        const { page, link } = paginate(req, list, query);
        return sendJson(res, 200, page, link === '' ? {} : { Link: link });
      }
      return restError(res, 404, 'Not Found');
    }
  }

  return restError(res, 404, 'Not Found');
}

// -------------------------------------------------------------------------------------------
// Git smart HTTP: upload-pack (v0 + v2) and receive-pack (v0)
// -------------------------------------------------------------------------------------------

function advertiseRefLine(oid: string, ref: string, capabilities: string): Buffer {
  const line = `${oid} ${ref}\0${capabilities}\n`;
  return pktEncode(line);
}

function listRefs(repo: Repo): Array<{ oid: string; ref: string }> {
  const out: Array<{ oid: string; ref: string }> = [];
  const head = repo.refs.get(`refs/heads/${repo.default_branch}`);
  if (head !== undefined) out.push({ oid: head, ref: 'HEAD' });
  for (const [ref, oid] of [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1))) {
    out.push({ oid, ref });
  }
  return out;
}

function gitAdvertise(repo: Repo, service: 'upload-pack' | 'receive-pack', protocolVersion: string): Buffer {
  const parts: Buffer[] = [];
  if (protocolVersion === '2') {
    parts.push(pktEncode(`# service=git-${service}\n`));
    parts.push(pktFlush());
    const caps = [
      `version 2\n`,
      `agent=${GIT_AGENT}\n`,
      `ls-refs=unborn\n`,
      `fetch=shallow filter\n`,
      `server-option\n`,
      `object-format=sha1\n`,
    ];
    for (const cap of caps) parts.push(pktEncode(cap));
    parts.push(pktFlush());
    return Buffer.concat(parts);
  }
  parts.push(pktEncode(`# service=git-${service}\n`));
  parts.push(pktFlush());
  const refs = listRefs(repo);
  const capabilities = service === 'upload-pack'
    ? `multi_ack thin-pack side-band side-band-64k ofs-delta shallow deepen-since deepen-not deepen-relative no-progress include-tag multi_ack_detailed allow-tip-sha1-in-want allow-reachable-sha1-in-want no-done filter agent=${GIT_AGENT} object-format=sha1`
    : `report-status report-status-v2 delete-refs side-band-64k quiet atomic ofs-delta agent=${GIT_AGENT} object-format=sha1`;
  if (refs.length === 0) {
    parts.push(pktEncode(`${ZERO_OID} capabilities^{}\0${capabilities}\n`));
  } else {
    const headRef = refs[0];
    const firstCaps = service === 'upload-pack'
      ? `${capabilities} symref=HEAD:refs/heads/${repo.default_branch}`
      : capabilities;
    parts.push(advertiseRefLine(headRef.oid, headRef.ref, firstCaps));
    for (const ref of refs.slice(1)) {
      parts.push(pktEncode(`${ref.oid} ${ref.ref}\n`));
    }
  }
  parts.push(pktFlush());
  return Buffer.concat(parts);
}

/** The closure of commits/trees/blobs under `roots`, never walking from a commit to its parents. */
function treeClosure(repo: Repo, roots: Iterable<string>): Set<string> {
  const out = new Set<string>();
  const stack = [...roots];
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (out.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (object === undefined) continue;
    out.add(oid);
    if (object.type === 'commit') {
      stack.push(parseCommit(object.data).tree);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) stack.push(entry.oid);
    } else if (object.type === 'tag') {
      const target = object.data.toString('utf8').split('\n').find((line) => line.startsWith('object '));
      if (target !== undefined) stack.push(target.slice(7).trim());
    }
  }
  return out;
}

function buildFetchPack(repo: Repo, wants: string[], haves: string[], deepen: number, shallowWants: string[], includeTag = false): { pack: Buffer; shallow: string[]; unshallow: string[] } {
  const lookup = repoLookup(repo);
  const shallowSet = new Set(shallowWants);
  const haveClosure = new Set<string>();
  for (const have of haves) {
    if (!repo.objects.has(have)) continue;
    // A have on the client's shallow boundary is held with its tree only:
    // its ancestors are not held, so they must still be sent on deepen.
    // Any other have implies its full reachable history.
    const held = shallowSet.has(have) ? treeClosure(repo, [have]) : collectReachable([have], lookup);
    for (const oid of held) haveClosure.add(oid);
  }
  // BFS depth from the wants: want depth 1, its parents depth 2, and so on.
  const depthOf = new Map<string, number>();
  const queue: Array<{ oid: string; depth: number }> = [];
  for (const want of wants) {
    if (repo.objects.has(want) && !depthOf.has(want)) {
      depthOf.set(want, 1);
      queue.push({ oid: want, depth: 1 });
    }
  }
  const wanted = new Set<string>();
  for (let head = 0; head < queue.length; head += 1) {
    const item = queue[head];
    if (deepen > 0 && item.depth > deepen) continue;
    wanted.add(item.oid);
    const object = repo.objects.get(item.oid);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (!depthOf.has(parent)) {
        depthOf.set(parent, item.depth + 1);
        queue.push({ oid: parent, depth: item.depth + 1 });
      }
    }
  }
  // The objects to send: with a depth limit, only the wanted commits and
  // their trees/blobs (never ancestors past the depth — the old code walked
  // the full reachable closure here, so a depth-1 clone carried all history);
  // otherwise the full reachable closure of every want.
  const existing = [...wanted].filter((oid) => repo.objects.has(oid));
  const wantedClosure = deepen > 0 ? treeClosure(repo, existing) : collectReachable(existing, lookup);
  const shallow: string[] = [];
  if (deepen > 0) {
    for (const [oid, depth] of depthOf) {
      if (depth === deepen && repo.objects.get(oid)?.type === 'commit') shallow.push(oid);
    }
  }
  const unshallow: string[] = shallowWants.filter((oid) => !shallow.includes(oid) && wantedClosure.has(oid));
  const send = new Set<string>();
  for (const oid of wantedClosure) {
    if (!haveClosure.has(oid)) send.add(oid);
  }
  if (includeTag) {
    // Send tag objects that point at a commit in this pack, as `include-tag`
    // asks: a clone of an annotated tag needs the tag object itself.
    for (const [oid, object] of repo.objects) {
      if (object.type !== 'tag' || send.has(oid)) continue;
      const target = object.data.toString('utf8').split('\n').find((line) => line.startsWith('object '));
      if (target !== undefined && send.has(target.slice(7).trim())) send.add(oid);
    }
  }
  const objects: GitObject[] = [];
  const commits = [...send].filter((oid) => repo.objects.get(oid)?.type === 'commit');
  const others = [...send].filter((oid) => repo.objects.get(oid)?.type !== 'commit');
  const ordered = [...commits, ...others];
  for (const oid of ordered) {
    const object = repo.objects.get(oid);
    if (object !== undefined) objects.push(object);
  }
  return { pack: writePack(objects), shallow, unshallow };
}

function sidebandPack(pack: Buffer): Buffer {
  const parts: Buffer[] = [];
  const maxData = 65515;
  for (let offset = 0; offset < pack.length; offset += maxData) {
    const chunk = pack.subarray(offset, Math.min(offset + maxData, pack.length));
    parts.push(pktEncode(Buffer.concat([Buffer.from([1]), chunk])));
  }
  if (pack.length === 0) parts.push(pktEncode(Buffer.from([1])));
  parts.push(pktFlush());
  return Buffer.concat(parts);
}

function handleUploadPackV0(repo: Repo, body: Buffer): Buffer {
  // v0 request: pkt-lines of wants/haves, then a flush, then nothing else.
  let wants: string[] = [];
  let haves: string[] = [];
  let deepen = 0;
  try {
    const { packets } = parsePktLines(body);
    for (const line of pktLinesText(packets)) {
      const text = line.trim();
      if (text.startsWith('want ')) wants.push(text.slice(5, 45));
      else if (text.startsWith('have ')) haves.push(text.slice(5, 45));
      else if (text.startsWith('deepen ')) deepen = parseInt(text.slice(7), 10) || 0;
    }
  } catch {
    wants = [];
  }
  const { pack, shallow } = buildFetchPack(repo, wants, haves, deepen, []);
  const parts: Buffer[] = [];
  parts.push(pktEncode('NAK\n'));
  for (const oid of shallow) parts.push(pktEncode(`shallow ${oid}\n`));
  parts.push(sidebandPack(pack));
  return Buffer.concat(parts);
}

function handleUploadPackV2(repo: Repo, body: Buffer): Buffer {
  const { packets } = parsePktLines(body);
  const lines = pktLinesText(packets);
  const command = lines[0]?.trim() ?? '';
  if (command === 'command=ls-refs') {
    let peel = false;
    let symrefs = false;
    let unborn = false;
    const refPrefixes: string[] = [];
    for (const line of lines.slice(1)) {
      const text = line.trim();
      if (text === 'peel') peel = true;
      else if (text === 'symrefs') symrefs = true;
      else if (text === 'unborn') unborn = true;
      else if (text.startsWith('ref-prefix ')) refPrefixes.push(text.slice('ref-prefix '.length));
      else if (text.startsWith('ref-prefix=')) refPrefixes.push(text.slice('ref-prefix='.length));
    }
    const out: Buffer[] = [];
    const defaultRef = `refs/heads/${repo.default_branch}`;
    const defaultTip = repo.refs.get(defaultRef);
    const refs = [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
    const matches = (name: string): boolean => refPrefixes.length === 0 || refPrefixes.some((prefix) => name.startsWith(prefix));
    if (defaultTip !== undefined) {
      if (matches('HEAD')) {
        const line = symrefs
          ? `${defaultTip} HEAD symref-target:${defaultRef}\n`
          : `${defaultTip} HEAD\n`;
        out.push(pktEncode(line));
      }
    } else if (unborn && matches('HEAD')) {
      out.push(pktEncode(`unborn HEAD symref-target:${defaultRef}\n`));
    }
    for (const [ref, oid] of refs) {
      if (!matches(ref)) continue;
      // Protocol v2 carries a peeled tag as an attribute on the ref's own
      // line (`peeled:<oid>`), not as a separate `^{}` line (that is the v0
      // advertisement form); the client's parser only reads the attribute.
      let line = `${oid} ${ref}`;
      if (peel) {
        const object = repo.objects.get(oid);
        if (object !== undefined && object.type === 'tag') {
          const target = object.data.toString('utf8').split('\n').find((candidate) => candidate.startsWith('object '));
          if (target !== undefined) line += ` peeled:${target.slice(7).trim()}`;
        }
      }
      out.push(pktEncode(`${line}\n`));
    }
    out.push(pktFlush());
    return Buffer.concat(out);
  }
  if (command === 'command=fetch') {
    const wants: string[] = [];
    const haves: string[] = [];
    const shallowWants: string[] = [];
    let deepen = 0;
    let hasDone = false;
    let includeTag = false;
    for (const line of lines.slice(1)) {
      const text = line.trim();
      if (text === '') continue;
      if (text.startsWith('command=') || text.startsWith('agent=') || text.startsWith('object-format=')) continue;
      if (text === 'thin-pack' || text === 'no-progress' || text === 'ofs-delta' || text === 'side-band-64k' || text === 'side-band' || text.startsWith('filter ')) continue;
      if (text === 'include-tag') {
        includeTag = true;
        continue;
      }
      if (text === 'done') {
        hasDone = true;
        continue;
      }
      if (text === 'wait-for-done') continue;
      if (text.startsWith('want ')) wants.push(text.slice(5, 45));
      else if (text.startsWith('have ')) haves.push(text.slice(5, 45));
      else if (text.startsWith('shallow ')) shallowWants.push(text.slice(8, 48));
      else if (text.startsWith('deepen ')) deepen = parseInt(text.slice(7), 10) || 0;
      else if (text.startsWith('deepen-since ') || text.startsWith('deepen-not ')) deepen = 1;
    }
    const { pack, shallow, unshallow } = buildFetchPack(repo, wants, haves, deepen, shallowWants, includeTag);
    const shallowSection = (): Buffer[] => {
      if (shallow.length === 0 && unshallow.length === 0) return [];
      const out: Buffer[] = [pktEncode('shallow-info\n')];
      for (const oid of shallow) out.push(pktEncode(`shallow ${oid}\n`));
      for (const oid of unshallow) out.push(pktEncode(`unshallow ${oid}\n`));
      out.push(pktFlush());
      return out;
    };
    const packSection = (): Buffer[] => [pktEncode('packfile\n'), sidebandPack(pack)];
    if (!hasDone) {
      // Negotiation round: the client has not sent "done", so it reads an
      // acknowledgments section and either continues or takes the packfile.
      const lookup = repoLookup(repo);
      const common = haves.find((have) => repo.objects.has(have) && wants.some((want) => have === want || isAncestor(have, want, lookup)));
      const parts: Buffer[] = [pktEncode('acknowledgments\n')];
      if (common !== undefined) {
        parts.push(pktEncode(`ACK ${common} ready\n`));
        parts.push(pktDelim());
        parts.push(...shallowSection());
        parts.push(...packSection());
      } else {
        parts.push(pktEncode('NAK\n'));
        parts.push(pktFlush());
      }
      return Buffer.concat(parts);
    }
    // The client sent "done": no acknowledgments section — straight to
    // shallow-info (when present) and the packfile. This is what real git
    // expects (fetch-pack goes to FETCH_GET_PACK on "done").
    return Buffer.concat([...shallowSection(), ...packSection()]);
  }
  throw new Error(`unsupported v2 command ${JSON.stringify(command)}`);
}

function handleReceivePack(repo: Repo, body: Buffer): Buffer {
  const { packets, endOffset } = parsePktLines(body);
  const lines = pktLinesText(packets);
  const updates: Array<{ oldOid: string; newOid: string; ref: string }> = [];
  for (const line of lines) {
    const parts = line.trim().split(' ');
    if (parts.length < 3) continue;
    const [oldOid, newOid] = parts;
    const ref = parts[2].split('\0')[0];
    if (isOid(oldOid) && isOid(newOid)) updates.push({ oldOid, newOid, ref });
  }
  const pack = body.subarray(endOffset);
  const lookup = repoLookup(repo);
  // A delete-only push carries no pack at all: there is nothing to unpack.
  const received = pack.length === 0 ? new Map<string, GitObject>() : readPack(pack, lookup);
  for (const [oid, object] of received) {
    if (!repo.objects.has(oid)) repo.objects.set(oid, object);
  }
  const results: string[] = ['unpack ok\n'];
  // Fast-forward check: the common case is a push whose new commit lists
  // the current tip as a direct parent — answer that in O(1) instead of
  // walking the whole history for every push (the push workload makes 200
  // sequential pushes to one branch, which would otherwise be quadratic).
  const isFastForward = (current: string, next: string): boolean => {
    if (current === next) return true;
    const object = repo.objects.get(next);
    if (object !== undefined && object.type === 'commit') {
      if (parseCommit(object.data).parents.includes(current)) return true;
    }
    return isAncestor(current, next, lookup);
  };
  for (const update of updates) {
    if (update.newOid === ZERO_OID) {
      repo.refs.delete(update.ref);
      results.push(`ok ${update.ref}\n`);
      continue;
    }
    const current = repo.refs.get(update.ref);
    if (current !== undefined && current !== ZERO_OID && !isFastForward(current, update.newOid)) {
      results.push(`ng ${update.ref} non-fast-forward\n`);
      continue;
    }
    if (repo.objects.get(update.newOid) === undefined && update.newOid !== ZERO_OID) {
      results.push(`ng ${update.ref} object not found\n`);
      continue;
    }
    repo.refs.set(update.ref, update.newOid);
    results.push(`ok ${update.ref}\n`);
  }
  packCacheSeq += 1;
  repo.updated_at = clockIso();
  repo.pushed_at = repo.updated_at;
  // Each status line is a pkt-line of its own, wrapped in its own sideband
  // band-1 packet: the client's demultiplexer strips the band byte and the
  // status reader parses the inner pkt-lines. The report-status stream is
  // itself terminated by a flush pkt-line, wrapped in band 1 as well: the
  // reader breaks on that inner flush. Without it the reader hits EOF on
  // the demux pipe and dies "the remote end hung up unexpectedly" (its
  // reader has no GENTLE_ON_EOF), and the RPC layer dies the same way.
  // The outer flush ends the sideband stream.
  const parts: Buffer[] = [];
  for (const line of results) {
    parts.push(pktEncode(Buffer.concat([Buffer.from([1]), pktEncode(line)])));
  }
  parts.push(pktEncode(Buffer.concat([Buffer.from([1]), pktFlush()])));
  parts.push(pktFlush());
  return Buffer.concat(parts);
}

function gitRouter(req: IncomingMessage, res: ServerResponse, body: Buffer): boolean {
  const url = new URL(req.url ?? '/', `http://${req.headers.host ?? 'localhost'}`);
  const path = decodeURIComponent(url.pathname);
  const match = /^\/([^/]+)\/([^/]+)\.git\/(.+)$/.exec(path);
  if (match === null) return false;
  const owner = match[1];
  const name = match[2];
  const rest = match[3];
  const repo = getRepo(owner, name);
  const service = url.searchParams.get('service');
  const method = req.method ?? 'GET';

  if (method === 'GET' && rest === 'info/refs') {
    if (repo === undefined) {
      sendBuffer(res, 404, Buffer.from('Not Found\n', 'utf8'), 'text/plain; charset=utf-8');
      return true;
    }
    if (service === 'git-upload-pack' || service === 'git-receive-pack') {
      const protocol = req.headers['git-protocol'] === 'version=2' ? '2' : '0';
      const advertised = gitAdvertise(repo, service === 'git-upload-pack' ? 'upload-pack' : 'receive-pack', protocol);
      sendBuffer(res, 200, advertised, `application/x-${service}-advertisement`, { 'Cache-Control': 'no-cache' });
      return true;
    }
    sendBuffer(res, 400, Buffer.from('service required\n', 'utf8'), 'text/plain; charset=utf-8');
    return true;
  }

  if (method === 'POST' && rest === 'git-upload-pack') {
    if (repo === undefined) {
      sendBuffer(res, 404, Buffer.from('Not Found\n', 'utf8'), 'text/plain; charset=utf-8');
      return true;
    }
    const protocol = req.headers['git-protocol'] === 'version=2' ? '2' : '0';
    try {
      const out = protocol === '2' ? handleUploadPackV2(repo, body) : handleUploadPackV0(repo, body);
      sendBuffer(res, 200, out, 'application/x-git-upload-pack-result', { 'Cache-Control': 'no-cache' });
    } catch (error) {
      const message = error instanceof Error ? error.message : 'bad request';
      sendBuffer(res, 400, Buffer.from(`${message}\n`, 'utf8'), 'text/plain; charset=utf-8');
    }
    return true;
  }

  if (method === 'POST' && rest === 'git-receive-pack') {
    if (repo === undefined) {
      sendBuffer(res, 404, Buffer.from('Not Found\n', 'utf8'), 'text/plain; charset=utf-8');
      return true;
    }
    try {
      const out = handleReceivePack(repo, body);
      sendBuffer(res, 200, out, 'application/x-git-receive-pack-result', { 'Cache-Control': 'no-cache' });
    } catch (error) {
      const message = error instanceof Error ? error.message : 'bad request';
      sendBuffer(res, 400, Buffer.from(`${message}\n`, 'utf8'), 'text/plain; charset=utf-8');
    }
    return true;
  }

  return false;
}

// -------------------------------------------------------------------------------------------
// GraphQL v4: a small parser and executor over the same store
// -------------------------------------------------------------------------------------------

type GqlValue =
  | { kind: 'variable'; name: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'string'; value: string }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; values: GqlValue[] }
  | { kind: 'object'; fields: Array<{ name: string; value: GqlValue }> };

interface GqlField {
  alias: string | null;
  name: string;
  args: Array<{ name: string; value: GqlValue }>;
  selections: GqlSelection[];
}

type GqlSelection =
  | { kind: 'field'; field: GqlField }
  | { kind: 'fragment'; name: string }
  | { kind: 'inline'; typeCondition: string | null; selections: GqlSelection[] };

interface GqlOperation {
  kind: 'query' | 'mutation';
  name: string | null;
  variables: Array<{ name: string; type: string; defaultValue: GqlValue | null }>;
  selections: GqlSelection[];
}

interface GqlToken {
  kind: 'name' | 'int' | 'float' | 'string' | 'punct' | 'ellipsis';
  value: string;
}

function gqlTokenize(source: string): GqlToken[] {
  const tokens: GqlToken[] = [];
  let index = 0;
  while (index < source.length) {
    const ch = source[index];
    if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',') {
      index += 1;
      continue;
    }
    if (ch === '#') {
      while (index < source.length && source[index] !== '\n') index += 1;
      continue;
    }
    if (source.startsWith('...', index)) {
      tokens.push({ kind: 'ellipsis', value: '...' });
      index += 3;
      continue;
    }
    if ('!$&()[]{}=:|@'.includes(ch)) {
      tokens.push({ kind: 'punct', value: ch });
      index += 1;
      continue;
    }
    if (ch === '"') {
      let end = index + 1;
      let value = '';
      while (end < source.length && source[end] !== '"') {
        if (source[end] === '\\' && end + 1 < source.length) {
          const escape = source[end + 1];
          if (escape === 'n') value += '\n';
          else if (escape === 't') value += '\t';
          else if (escape === 'r') value += '\r';
          else value += escape;
          end += 2;
        } else {
          value += source[end];
          end += 1;
        }
      }
      tokens.push({ kind: 'string', value });
      index = end + 1;
      continue;
    }
    if (/[0-9-]/.test(ch)) {
      let end = index;
      let isFloat = false;
      if (source[end] === '-') end += 1;
      while (end < source.length && /[0-9]/.test(source[end])) end += 1;
      if (source[end] === '.') {
        isFloat = true;
        end += 1;
        while (end < source.length && /[0-9]/.test(source[end])) end += 1;
      }
      if (source[end] === 'e' || source[end] === 'E') {
        isFloat = true;
        end += 1;
        if (source[end] === '+' || source[end] === '-') end += 1;
        while (end < source.length && /[0-9]/.test(source[end])) end += 1;
      }
      tokens.push({ kind: isFloat ? 'float' : 'int', value: source.slice(index, end) });
      index = end;
      continue;
    }
    if (/[A-Za-z_]/.test(ch)) {
      let end = index;
      while (end < source.length && /[A-Za-z0-9_]/.test(source[end])) end += 1;
      tokens.push({ kind: 'name', value: source.slice(index, end) });
      index = end;
      continue;
    }
    throw new Error(`unexpected character ${JSON.stringify(ch)} in GraphQL document`);
  }
  return tokens;
}

class GqlParser {
  private pos = 0;
  private tokens: GqlToken[];
  constructor(tokens: GqlToken[]) {
    this.tokens = tokens;
  }

  private peek(): GqlToken | undefined {
    return this.tokens[this.pos];
  }

  private next(): GqlToken {
    const token = this.tokens[this.pos];
    if (token === undefined) throw new Error('unexpected end of GraphQL document');
    this.pos += 1;
    return token;
  }

  private expectPunct(value: string): void {
    const token = this.next();
    if (token.kind !== 'punct' || token.value !== value) throw new Error(`expected ${value}, got ${token.value}`);
  }

  private expectName(value?: string): string {
    const token = this.next();
    if (token.kind !== 'name') throw new Error(`expected a name, got ${token.value}`);
    if (value !== undefined && token.value !== value) throw new Error(`expected ${value}, got ${token.value}`);
    return token.value;
  }

  private acceptPunct(value: string): boolean {
    const token = this.peek();
    if (token !== undefined && token.kind === 'punct' && token.value === value) {
      this.pos += 1;
      return true;
    }
    return false;
  }

  parseDocument(): { operations: GqlOperation[]; fragments: Map<string, GqlSelection[]> } {
    const operations: GqlOperation[] = [];
    const fragments = new Map<string, GqlSelection[]>();
    while (this.pos < this.tokens.length) {
      const token = this.peek()!;
      if (token.kind === 'punct' && token.value === '{') {
        operations.push({ kind: 'query', name: null, variables: [], selections: this.parseSelectionSet() });
        continue;
      }
      if (token.kind === 'name' && (token.value === 'query' || token.value === 'mutation')) {
        const kind = this.next().value as 'query' | 'mutation';
        let name: string | null = null;
        if (this.peek()?.kind === 'name') name = this.next().value;
        const variables = this.peek()?.kind === 'punct' && this.peek()?.value === '(' ? this.parseVariableDefinitions() : [];
        operations.push({ kind, name, variables, selections: this.parseSelectionSet() });
        continue;
      }
      if (token.kind === 'name' && token.value === 'fragment') {
        this.next();
        const name = this.expectName();
        this.expectName('on');
        this.expectName();
        fragments.set(name, this.parseSelectionSet());
        continue;
      }
      throw new Error(`unexpected token ${token.value} at the top of a GraphQL document`);
    }
    return { operations, fragments };
  }

  private parseVariableDefinitions(): Array<{ name: string; type: string; defaultValue: GqlValue | null }> {
    this.expectPunct('(');
    const variables: Array<{ name: string; type: string; defaultValue: GqlValue | null }> = [];
    while (!this.acceptPunct(')')) {
      this.expectPunct('$');
      const name = this.expectName();
      this.expectPunct(':');
      let type = '';
      while (true) {
        const token = this.next();
        if (token.kind === 'name') type += token.value;
        else if (token.kind === 'punct' && (token.value === '!' || token.value === '[' || token.value === ']')) type += token.value;
        else throw new Error(`bad variable type near ${token.value}`);
        const next = this.peek();
        if (next?.kind === 'punct' && (next.value === '!' || next.value === '[' || next.value === ']')) continue;
        break;
      }
      let defaultValue: GqlValue | null = null;
      if (this.acceptPunct('=')) defaultValue = this.parseValue();
      variables.push({ name, type, defaultValue });
    }
    return variables;
  }

  private parseSelectionSet(): GqlSelection[] {
    this.expectPunct('{');
    const selections: GqlSelection[] = [];
    while (!this.acceptPunct('}')) {
      const token = this.peek()!;
      if (token.kind === 'ellipsis') {
        this.next();
        const next = this.peek()!;
        if (next.kind === 'name' && next.value === 'on') {
          this.next();
          const typeCondition = this.expectName();
          selections.push({ kind: 'inline', typeCondition, selections: this.parseSelectionSet() });
        } else if (next.kind === 'name') {
          selections.push({ kind: 'fragment', name: this.next().value });
        } else if (next.kind === 'punct' && next.value === '{') {
          selections.push({ kind: 'inline', typeCondition: null, selections: this.parseSelectionSet() });
        } else {
          throw new Error('bad fragment spread');
        }
        continue;
      }
      selections.push({ kind: 'field', field: this.parseField() });
    }
    return selections;
  }

  private parseField(): GqlField {
    let name = this.expectName();
    let alias: string | null = null;
    if (this.acceptPunct(':')) {
      alias = name;
      name = this.expectName();
    }
    const args: Array<{ name: string; value: GqlValue }> = [];
    if (this.peek()?.kind === 'punct' && this.peek()?.value === '(') {
      this.next();
      while (!this.acceptPunct(')')) {
        const argName = this.expectName();
        this.expectPunct(':');
        args.push({ name: argName, value: this.parseValue() });
      }
    }
    // Directives: @skip/@include and anything else — parsed and ignored.
    while (this.peek()?.kind === 'punct' && this.peek()?.value === '@') {
      this.next();
      this.expectName();
      if (this.peek()?.kind === 'punct' && this.peek()?.value === '(') {
        this.next();
        while (!this.acceptPunct(')')) {
          this.expectName();
          this.expectPunct(':');
          this.parseValue();
        }
      }
    }
    const selections = this.peek()?.kind === 'punct' && this.peek()?.value === '{' ? this.parseSelectionSet() : [];
    return { alias, name, args, selections };
  }

  private parseValue(): GqlValue {
    const token = this.next();
    if (token.kind === 'punct' && token.value === '$') return { kind: 'variable', name: this.expectName() };
    if (token.kind === 'punct' && token.value === '[') {
      const values: GqlValue[] = [];
      while (!this.acceptPunct(']')) values.push(this.parseValue());
      return { kind: 'list', values };
    }
    if (token.kind === 'punct' && token.value === '{') {
      const fields: Array<{ name: string; value: GqlValue }> = [];
      while (!this.acceptPunct('}')) {
        const name = this.expectName();
        this.expectPunct(':');
        fields.push({ name, value: this.parseValue() });
      }
      return { kind: 'object', fields };
    }
    if (token.kind === 'int') return { kind: 'int', value: parseInt(token.value, 10) };
    if (token.kind === 'float') return { kind: 'float', value: parseFloat(token.value) };
    if (token.kind === 'string') return { kind: 'string', value: token.value };
    if (token.kind === 'name') {
      if (token.value === 'true') return { kind: 'boolean', value: true };
      if (token.value === 'false') return { kind: 'boolean', value: false };
      if (token.value === 'null') return { kind: 'null' };
      return { kind: 'enum', value: token.value };
    }
    throw new Error(`unexpected value token ${token.value}`);
  }
}

function gqlValue(value: GqlValue, variables: Record<string, unknown>): unknown {
  switch (value.kind) {
    case 'variable': return variables[value.name];
    case 'int': case 'float': case 'string': case 'boolean': return value.value;
    case 'null': return null;
    case 'enum': return value.value;
    case 'list': return value.values.map((item) => gqlValue(item, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const field of value.fields) out[field.name] = gqlValue(field.value, variables);
      return out;
    }
  }
}

function gqlArg(field: GqlField, name: string, variables: Record<string, unknown>): unknown {
  const arg = field.args.find((candidate) => candidate.name === name);
  return arg === undefined ? undefined : gqlValue(arg.value, variables);
}

function gqlString(value: unknown): string | null {
  return typeof value === 'string' ? value : null;
}

function gqlInt(value: unknown): number | null {
  return typeof value === 'number' && Number.isFinite(value) ? Math.trunc(value) : null;
}

// -------------------------------------------------------------------------------------------
// GraphQL execution: resolvers per type
// -------------------------------------------------------------------------------------------

interface GqlContext {
  variables: Record<string, unknown>;
  fragments: Map<string, GqlSelection[]>;
  errors: Array<Record<string, unknown>>;
}

const TYPE_INFO: Record<string, { kind: string; fields?: string[]; enumValues?: string[] }> = {
  Issue: { kind: 'OBJECT', fields: ['id', 'number', 'title', 'body', 'state', 'author', 'createdAt', 'updatedAt', 'closedAt', 'url', 'labels', 'comments', 'repository', 'assignees', 'milestone', 'locked', 'viewerDidAuthor'] },
  PullRequest: { kind: 'OBJECT', fields: ['id', 'number', 'title', 'body', 'state', 'merged', 'headRefName', 'baseRefName', 'mergeable', 'files', 'author', 'createdAt', 'updatedAt', 'closedAt', 'mergedAt', 'repository', 'commits', 'reviews', 'isDraft', 'viewerDidAuthor'] },
  Repository: { kind: 'OBJECT', fields: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequest', 'pullRequests', 'description', 'url', 'createdAt', 'updatedAt', 'isPrivate', 'isFork', 'stargazerCount', 'watchers'] },
  SearchType: { kind: 'ENUM', enumValues: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'CODE', 'COMMIT', 'MILESTONE', 'PROJECT'] },
  IssueState: { kind: 'ENUM', enumValues: ['OPEN', 'CLOSED'] },
  PullRequestState: { kind: 'ENUM', enumValues: ['OPEN', 'CLOSED', 'MERGED'] },
  MergeableState: { kind: 'ENUM', enumValues: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] },
  RepositoryPermission: { kind: 'ENUM', enumValues: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'] },
  OrderDirection: { kind: 'ENUM', enumValues: ['ASC', 'DESC'] },
  IssueOrderField: { kind: 'ENUM', enumValues: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'] },
  PullRequestOrderField: { kind: 'ENUM', enumValues: ['CREATED_AT', 'UPDATED_AT'] },
  User: { kind: 'OBJECT', fields: ['id', 'login', 'name', 'email', 'url', 'avatarUrl'] },
  Ref: { kind: 'OBJECT', fields: ['id', 'name', 'prefix', 'target'] },
  IssueComment: { kind: 'OBJECT', fields: ['id', 'body', 'author', 'createdAt', 'updatedAt', 'url'] },
  IssueConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  PullRequestConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  IssueCommentConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  PullRequestFileConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  IssueEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  PullRequestEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  IssueCommentEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  PullRequestFileEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  PageInfo: { kind: 'OBJECT', fields: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'] },
  PullRequestFile: { kind: 'OBJECT', fields: ['path', 'additions', 'deletions', 'changeType'] },
  Query: { kind: 'OBJECT', fields: ['viewer', 'repository', 'node', '__type', '__schema'] },
  Mutation: { kind: 'OBJECT', fields: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'] },
};

function decodeGlobalId(id: string): { kind: string; parts: string[] } | null {
  try {
    const text = b64decode(id).toString('utf8');
    if (!text.startsWith('forge:')) return null;
    const segments = text.slice('forge:'.length).split(':');
    return { kind: segments[0], parts: segments.slice(1) };
  } catch {
    return null;
  }
}

function findRepoById(dbId: number): Repo | undefined {
  for (const repo of repos.values()) if (repo.id === dbId) return repo;
  return undefined;
}

function findIssueByNodeId(nodeId: string): { repo: Repo; issue: Issue } | undefined {
  for (const repo of repos.values()) {
    for (const issue of repo.issues.values()) if (issue.node_id === nodeId) return { repo, issue };
  }
  return undefined;
}

function findPullByNodeId(nodeId: string): { repo: Repo; pull: PullRequest } | undefined {
  for (const repo of repos.values()) {
    for (const pull of repo.pulls.values()) if (pull.node_id === nodeId) return { repo, pull };
  }
  return undefined;
}

function issueCursor(issue: Issue): string {
  return b64encode(`issue:${issue.number}`);
}

function pullCursor(pull: PullRequest): string {
  return b64encode(`pull:${pull.number}`);
}

function pageInfoFor<T>(items: readonly T[], cursorOf: (item: T) => string, first: number | null): Record<string, unknown> {
  const hasNext = first !== null && items.length > first;
  const shown = first === null ? items : items.slice(0, first);
  const last = shown[shown.length - 1];
  const firstItem = shown[0];
  return {
    hasNextPage: hasNext,
    hasPreviousPage: false,
    startCursor: firstItem === undefined ? null : cursorOf(firstItem),
    endCursor: last === undefined ? null : cursorOf(last),
  };
}

function issueNode(repo: Repo, issue: Issue): Record<string, unknown> {
  return { __typename: 'Issue', __repo: repo, __issue: issue };
}

function pullNode(repo: Repo, pull: PullRequest): Record<string, unknown> {
  return { __typename: 'PullRequest', __repo: repo, __pull: pull };
}

function repoNode(repo: Repo): Record<string, unknown> {
  return { __typename: 'Repository', __repo: repo };
}

function userNode(login: string, id: number): Record<string, unknown> {
  return { __typename: 'User', __login: login, __id: id };
}

/** Resolve one object against a selection set. Returns the JSON value (null when the object is null). */
function resolveSelection(
  object: Record<string, unknown> | null,
  typeName: string,
  selections: readonly GqlSelection[],
  ctx: GqlContext,
): Record<string, unknown> | null {
  if (object === null) return null;
  const out: Record<string, unknown> = {};
  for (const selection of selections) {
    if (selection.kind === 'fragment') {
      const fragment = ctx.fragments.get(selection.name);
      if (fragment !== undefined) {
        const merged = resolveSelection(object, typeName, fragment, ctx);
        if (merged !== null) Object.assign(out, merged);
      }
      continue;
    }
    if (selection.kind === 'inline') {
      if (selection.typeCondition !== null && selection.typeCondition !== typeName && selection.typeCondition !== (object.__typename as string | undefined)) continue;
      const merged = resolveSelection(object, typeName, selection.selections, ctx);
      if (merged !== null) Object.assign(out, merged);
      continue;
    }
    const field = selection.field;
    const key = field.alias ?? field.name;
    const value = resolveField(object, typeName, field, ctx);
    out[key] = value;
  }
  return out;
}

function resolveField(object: Record<string, unknown>, typeName: string, field: GqlField, ctx: GqlContext): unknown {
  const name = field.name;
  if (name === '__typename') return object.__typename ?? typeName;

  const errorFor = (message: string): null => {
    ctx.errors.push({ message, path: [name] });
    return null;
  };

  if (typeName === 'Query') {
    if (name === 'viewer') {
      return resolveSelection(userNode(VIEWER_LOGIN, VIEWER_ID), 'User', field.selections, ctx);
    }
    if (name === 'repository') {
      const owner = gqlString(gqlArg(field, 'owner', ctx.variables));
      const repoName = gqlString(gqlArg(field, 'name', ctx.variables));
      const repo = owner !== null && repoName !== null ? getRepo(owner, repoName) : undefined;
      if (repo === undefined) return null;
      return resolveSelection(repoNode(repo), 'Repository', field.selections, ctx);
    }
    if (name === 'node') {
      const id = gqlString(gqlArg(field, 'id', ctx.variables));
      const decoded = id === null ? null : decodeGlobalId(id);
      if (decoded === null) return null;
      if (decoded.kind === 'Repository') {
        const repo = findRepoById(Number(decoded.parts[0]));
        if (repo === undefined) return null;
        return resolveSelection(repoNode(repo), 'Repository', field.selections, ctx);
      }
      if (decoded.kind === 'Issue') {
        const found = findIssueByNodeId(id);
        if (found === undefined) return null;
        return resolveSelection(issueNode(found.repo, found.issue), 'Issue', field.selections, ctx);
      }
      if (decoded.kind === 'PullRequest') {
        const found = findPullByNodeId(id);
        if (found === undefined) return null;
        return resolveSelection(pullNode(found.repo, found.pull), 'PullRequest', field.selections, ctx);
      }
      return null;
    }
    if (name === '__type') {
      const typeNameArg = gqlString(gqlArg(field, 'name', ctx.variables));
      if (typeNameArg === null) return null;
      const info = TYPE_INFO[typeNameArg];
      if (info === undefined) return null;
      return resolveSelection({ __typename: '__Type', __typeName: typeNameArg, __info: info }, '__Type', field.selections, ctx);
    }
    if (name === '__schema') {
      return resolveSelection({ __typename: '__Schema' }, '__Schema', field.selections, ctx);
    }
    return errorFor(`Cannot query field "${name}" on type "Query".`);
  }

  if (typeName === 'Mutation') {
    if (name === 'createIssue') {
      const input = asObject(gqlArg(field, 'input', ctx.variables));
      const repositoryId = gqlString(input.repositoryId);
      const title = gqlString(input.title) ?? '';
      const body = gqlString(input.body) ?? '';
      const decoded = repositoryId === null ? null : decodeGlobalId(repositoryId);
      const repo = decoded !== null && decoded.kind === 'Repository' ? findRepoById(Number(decoded.parts[0])) : undefined;
      if (repo === undefined || title === '') {
        ctx.errors.push({ message: 'createIssue: repository not found or title missing', path: [name] });
        return null;
      }
      const created = createIssue(repo, { title, body });
      if ('error' in created) {
        ctx.errors.push({ message: created.error, path: [name] });
        return null;
      }
      const out: Record<string, unknown> = {
        issue: resolveSelection(issueNode(repo, created), 'Issue', field.selections.find((s) => s.kind === 'field' && s.field.name === 'issue')?.field.selections ?? [], ctx),
        clientMutationId: typeof input.clientMutationId === 'string' ? input.clientMutationId : null,
      };
      return out;
    }
    if (name === 'closeIssue') {
      const input = asObject(gqlArg(field, 'input', ctx.variables));
      const issueId = gqlString(input.issueId);
      const found = issueId === null ? undefined : findIssueByNodeId(issueId);
      if (found === undefined) {
        ctx.errors.push({ message: 'closeIssue: issue not found', path: [name] });
        return null;
      }
      found.issue.state = 'closed';
      found.issue.closed_at = clockIso();
      found.issue.updated_at = found.issue.closed_at;
      const issueSelections = field.selections.find((s) => s.kind === 'field' && s.field.name === 'issue')?.field.selections ?? [];
      return { issue: resolveSelection(issueNode(found.repo, found.issue), 'Issue', issueSelections, ctx), clientMutationId: typeof input.clientMutationId === 'string' ? input.clientMutationId : null };
    }
    if (name === 'createPullRequest') {
      const input = asObject(gqlArg(field, 'input', ctx.variables));
      const repositoryId = gqlString(input.repositoryId);
      const decoded = repositoryId === null ? null : decodeGlobalId(repositoryId);
      const repo = decoded !== null && decoded.kind === 'Repository' ? findRepoById(Number(decoded.parts[0])) : undefined;
      if (repo === undefined) {
        ctx.errors.push({ message: 'createPullRequest: repository not found', path: [name] });
        return null;
      }
      const created = createPull(repo, {
        title: gqlString(input.title) ?? '',
        body: gqlString(input.body) ?? '',
        head: gqlString(input.headRefName) ?? '',
        base: gqlString(input.baseRefName) ?? repo.default_branch,
      });
      if ('error' in created) {
        ctx.errors.push({ message: created.error, path: [name] });
        return null;
      }
      const pullSelections = field.selections.find((s) => s.kind === 'field' && s.field.name === 'pullRequest')?.field.selections ?? [];
      return { pullRequest: resolveSelection(pullNode(repo, created), 'PullRequest', pullSelections, ctx), clientMutationId: typeof input.clientMutationId === 'string' ? input.clientMutationId : null };
    }
    if (name === 'mergePullRequest') {
      const input = asObject(gqlArg(field, 'input', ctx.variables));
      const pullRequestId = gqlString(input.pullRequestId);
      const found = pullRequestId === null ? undefined : findPullByNodeId(pullRequestId);
      if (found === undefined) {
        ctx.errors.push({ message: 'mergePullRequest: pull request not found', path: [name] });
        return null;
      }
      const method = typeof input.mergeMethod === 'string' ? input.mergeMethod : 'SQUASH';
      if (method !== 'SQUASH') {
        ctx.errors.push({ message: 'mergePullRequest: only SQUASH is supported', path: [name] });
        return null;
      }
      if (found.pull.state !== 'open' || pullMergeable(found.repo, found.pull) !== 'MERGEABLE') {
        ctx.errors.push({ message: 'mergePullRequest: pull request cannot be merged', path: [name] });
        return null;
      }
      mergePullRequest(found.repo, found.pull);
      const pullSelections = field.selections.find((s) => s.kind === 'field' && s.field.name === 'pullRequest')?.field.selections ?? [];
      return { pullRequest: resolveSelection(pullNode(found.repo, found.pull), 'PullRequest', pullSelections, ctx), clientMutationId: typeof input.clientMutationId === 'string' ? input.clientMutationId : null };
    }
    if (name === 'addComment') {
      const input = asObject(gqlArg(field, 'input', ctx.variables));
      const subjectId = gqlString(input.subjectId);
      const body = gqlString(input.body) ?? '';
      const found = subjectId === null ? undefined : findIssueByNodeId(subjectId);
      if (found === undefined || body === '') {
        ctx.errors.push({ message: 'addComment: subject not found or body missing', path: [name] });
        return null;
      }
      const id = nextCommentId;
      nextCommentId += 1;
      const now = clockIso();
      const comment: IssueComment = {
        id,
        node_id: globalId('IssueComment', found.repo.id, id),
        body,
        user: { login: VIEWER_LOGIN, id: VIEWER_ID },
        created_at: now,
        updated_at: now,
      };
      found.issue.comments.push(comment);
      found.issue.updated_at = now;
      const edgeSelections = field.selections.find((s) => s.kind === 'field' && s.field.name === 'commentEdge')?.field.selections ?? [];
      const nodeSelections = edgeSelections.find((s) => s.kind === 'field' && s.field.name === 'node')?.field.selections ?? [];
      return {
        commentEdge: {
          node: resolveSelection({ __typename: 'IssueComment', __comment: comment }, 'IssueComment', nodeSelections, ctx),
          cursor: b64encode(`comment:${comment.id}`),
        },
        subject: resolveSelection(issueNode(found.repo, found.issue), 'Issue', [], ctx),
        clientMutationId: typeof input.clientMutationId === 'string' ? input.clientMutationId : null,
      };
    }
    return errorFor(`Cannot query field "${name}" on type "Mutation".`);
  }

  if (typeName === 'Repository') {
    const repo = object.__repo as Repo;
    switch (name) {
      case 'id': return repo.node_id;
      case 'databaseId': return repo.id;
      case 'name': return repo.name;
      case 'nameWithOwner': return `${repo.owner}/${repo.name}`;
      case 'description': return repo.description;
      case 'url': return '';
      case 'createdAt': return repo.created_at;
      case 'updatedAt': return repo.updated_at;
      case 'isPrivate': return repo.private;
      case 'isFork': return false;
      case 'stargazerCount': return 0;
      case 'watchers': return resolveSelection({ __typename: 'UserConnection', __items: [] as unknown[] }, 'UserConnection', field.selections, ctx);
      case 'owner': return resolveSelection(userNode(repo.owner, VIEWER_ID), 'User', field.selections, ctx);
      case 'defaultBranchRef': {
        const tip = branchTip(repo, repo.default_branch);
        if (tip === null) return null;
        return resolveSelection({ __typename: 'Ref', __name: repo.default_branch, __oid: tip }, 'Ref', field.selections, ctx);
      }
      case 'viewerPermission': return 'ADMIN';
      case 'hasIssuesEnabled': return true;
      case 'issue': {
        const number = gqlInt(gqlArg(field, 'number', ctx.variables));
        if (number === null) return null;
        const issue = repo.issues.get(number);
        if (issue === undefined) return null;
        return resolveSelection(issueNode(repo, issue), 'Issue', field.selections, ctx);
      }
      case 'issues': {
        const first = gqlInt(gqlArg(field, 'first', ctx.variables));
        const after = gqlString(gqlArg(field, 'after', ctx.variables));
        const statesRaw = gqlArg(field, 'states', ctx.variables);
        const states = Array.isArray(statesRaw) ? statesRaw.map((item) => String(item)) : null;
        const orderBy = asObject(gqlArg(field, 'orderBy', ctx.variables));
        const direction = typeof orderBy.direction === 'string' ? orderBy.direction : 'DESC';
        let list = [...repo.issues.values()];
        if (states !== null) list = list.filter((issue) => states.includes(issue.state.toUpperCase()));
        list.sort((a, b) => {
          const byCreated = a.created_at < b.created_at ? -1 : a.created_at > b.created_at ? 1 : a.number - b.number;
          const key = orderBy.field === 'UPDATED_AT' ? (a.updated_at < b.updated_at ? -1 : a.updated_at > b.updated_at ? 1 : a.number - b.number) : byCreated;
          const signed = direction === 'ASC' ? key : -key;
          return signed === 0 ? b.number - a.number : signed;
        });
        if (after !== null) {
          const decoded = Buffer.from(after, 'base64').toString('utf8');
          const afterNumber = Number(decoded.split(':')[1]);
          if (Number.isFinite(afterNumber)) {
            const index = list.findIndex((issue) => issue.number === afterNumber);
            if (index >= 0) list = list.slice(index + 1);
          }
        }
        const pageInfo = pageInfoFor(list, issueCursor, first);
        const shown = first === null ? list : list.slice(0, first);
        return resolveSelection(
          { __typename: 'IssueConnection', __nodes: shown.map((issue) => issueNode(repo, issue)), __edges: shown.map((issue) => ({ __typename: 'IssueEdge', __node: issueNode(repo, issue), __cursor: issueCursor(issue) })), __pageInfo: pageInfo, __totalCount: list.length },
          'IssueConnection', field.selections, ctx,
        );
      }
      case 'pullRequest': {
        const number = gqlInt(gqlArg(field, 'number', ctx.variables));
        if (number === null) return null;
        const pull = repo.pulls.get(number);
        if (pull === undefined) return null;
        return resolveSelection(pullNode(repo, pull), 'PullRequest', field.selections, ctx);
      }
      case 'pullRequests': {
        const first = gqlInt(gqlArg(field, 'first', ctx.variables));
        const after = gqlString(gqlArg(field, 'after', ctx.variables));
        const statesRaw = gqlArg(field, 'states', ctx.variables);
        const states = Array.isArray(statesRaw) ? statesRaw.map((item) => String(item)) : null;
        const orderBy = asObject(gqlArg(field, 'orderBy', ctx.variables));
        const direction = typeof orderBy.direction === 'string' ? orderBy.direction : 'DESC';
        let list = [...repo.pulls.values()];
        if (states !== null) {
          list = list.filter((pull) => {
            const state = pull.merged ? 'MERGED' : pull.state.toUpperCase();
            return states.includes(state) || (state === 'CLOSED' && states.includes('CLOSED'));
          });
        }
        list.sort((a, b) => (direction === 'ASC' ? a.number - b.number : b.number - a.number));
        if (after !== null) {
          const decoded = Buffer.from(after, 'base64').toString('utf8');
          const afterNumber = Number(decoded.split(':')[1]);
          if (Number.isFinite(afterNumber)) {
            const index = list.findIndex((pull) => pull.number === afterNumber);
            if (index >= 0) list = list.slice(index + 1);
          }
        }
        const pageInfo = pageInfoFor(list, pullCursor, first);
        const shown = first === null ? list : list.slice(0, first);
        return resolveSelection(
          { __typename: 'PullRequestConnection', __nodes: shown.map((pull) => pullNode(repo, pull)), __edges: shown.map((pull) => ({ __typename: 'PullRequestEdge', __node: pullNode(repo, pull), __cursor: pullCursor(pull) })), __pageInfo: pageInfo, __totalCount: list.length },
          'PullRequestConnection', field.selections, ctx,
        );
      }
      default: return errorFor(`Cannot query field "${name}" on type "Repository".`);
    }
  }

  if (typeName === 'Issue') {
    const issue = object.__issue as Issue;
    switch (name) {
      case 'id': return issue.node_id;
      case 'number': return issue.number;
      case 'title': return issue.title;
      case 'body': return issue.body;
      case 'state': return issue.state.toUpperCase();
      case 'createdAt': return issue.created_at;
      case 'updatedAt': return issue.updated_at;
      case 'closedAt': return issue.closed_at;
      case 'url': return '';
      case 'locked': return false;
      case 'viewerDidAuthor': return true;
      case 'author': return resolveSelection(userNode(issue.user.login, issue.user.id), 'User', field.selections, ctx);
      case 'repository': {
        const repo = object.__repo as Repo;
        return resolveSelection(repoNode(repo), 'Repository', field.selections, ctx);
      }
      case 'labels': {
        const first = gqlInt(gqlArg(field, 'first', ctx.variables));
        const shown = first === null ? issue.labels : issue.labels.slice(0, first);
        const nodes = shown.map((label) => ({ __typename: 'Label', __label: label }));
        return resolveSelection(
          { __typename: 'LabelConnection', __nodes: nodes, __edges: nodes.map((node) => ({ __typename: 'LabelEdge', __node: node, __cursor: b64encode(`label:${(node.__label as Label).id}`) })), __pageInfo: pageInfoFor(shown, (label) => b64encode(`label:${label.id}`), first), __totalCount: issue.labels.length },
          'LabelConnection', field.selections, ctx,
        );
      }
      case 'comments': {
        const first = gqlInt(gqlArg(field, 'first', ctx.variables));
        const shown = first === null ? issue.comments : issue.comments.slice(0, first);
        const nodes = shown.map((comment) => ({ __typename: 'IssueComment', __comment: comment }));
        return resolveSelection(
          { __typename: 'IssueCommentConnection', __nodes: nodes, __edges: nodes.map((node) => ({ __typename: 'IssueCommentEdge', __node: node, __cursor: b64encode(`comment:${(node.__comment as IssueComment).id}`) })), __pageInfo: pageInfoFor(shown, (comment) => b64encode(`comment:${comment.id}`), first), __totalCount: issue.comments.length },
          'IssueCommentConnection', field.selections, ctx,
        );
      }
      case 'assignees': return resolveSelection({ __typename: 'UserConnection', __nodes: [] as unknown[], __edges: [] as unknown[], __pageInfo: { hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, __totalCount: 0 }, 'UserConnection', field.selections, ctx);
      case 'milestone': return null;
      default: return errorFor(`Cannot query field "${name}" on type "Issue".`);
    }
  }

  if (typeName === 'PullRequest') {
    const pull = object.__pull as PullRequest;
    const repo = object.__repo as Repo;
    switch (name) {
      case 'id': return pull.node_id;
      case 'number': return pull.number;
      case 'title': return pull.title;
      case 'body': return pull.body;
      case 'state': return pull.merged ? 'MERGED' : pull.state.toUpperCase();
      case 'merged': return pull.merged;
      case 'headRefName': return pull.headRef;
      case 'baseRefName': return pull.baseRef;
      case 'mergeable': return pullMergeable(repo, pull);
      case 'createdAt': return pull.created_at;
      case 'updatedAt': return pull.updated_at;
      case 'closedAt': return pull.closed_at;
      case 'mergedAt': return pull.merged_at;
      case 'isDraft': return false;
      case 'viewerDidAuthor': return true;
      case 'author': return resolveSelection(userNode(pull.user.login, pull.user.id), 'User', field.selections, ctx);
      case 'repository': return resolveSelection(repoNode(repo), 'Repository', field.selections, ctx);
      case 'files': {
        const first = gqlInt(gqlArg(field, 'first', ctx.variables));
        const files = pullFiles(repo, pull);
        const shown = first === null ? files : files.slice(0, first);
        const nodes = shown.map((file) => ({ __typename: 'PullRequestFile', __file: file }));
        return resolveSelection(
          { __typename: 'PullRequestFileConnection', __nodes: nodes, __edges: nodes.map((node) => ({ __typename: 'PullRequestFileEdge', __node: node, __cursor: b64encode(`file:${(node.__file as { filename: string }).filename}`) })), __pageInfo: pageInfoFor(shown, (file) => b64encode(`file:${file.filename}`), first), __totalCount: files.length },
          'PullRequestFileConnection', field.selections, ctx,
        );
      }
      case 'commits': {
        const first = gqlInt(gqlArg(field, 'first', ctx.variables));
        const commits: Array<Record<string, unknown>> = [];
        const seen = new Set<string>();
        let current: string | null = pull.headSha;
        while (current !== null && !seen.has(current)) {
          seen.add(current);
          const obj = repo.objects.get(current);
          if (obj === undefined || obj.type !== 'commit') break;
          const view = parseCommit(obj.data);
          commits.push({ __typename: 'PullRequestCommit', __commit: { oid: current, message: view.message } });
          current = view.parents[0] ?? null;
        }
        const shown = first === null ? commits : commits.slice(0, first);
        return resolveSelection(
          { __typename: 'PullRequestCommitConnection', __nodes: shown, __edges: shown.map((node) => ({ __typename: 'PullRequestCommitEdge', __node: node, __cursor: b64encode(`commit:${((node.__commit as { oid: string }).oid)}`) })), __pageInfo: { hasNextPage: first !== null && commits.length > first, hasPreviousPage: false, startCursor: null, endCursor: null }, __totalCount: commits.length },
          'PullRequestCommitConnection', field.selections, ctx,
        );
      }
      case 'reviews': return resolveSelection({ __typename: 'PullRequestReviewConnection', __nodes: [] as unknown[], __edges: [] as unknown[], __pageInfo: { hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, __totalCount: 0 }, 'PullRequestReviewConnection', field.selections, ctx);
      default: return errorFor(`Cannot query field "${name}" on type "PullRequest".`);
    }
  }

  if (typeName === 'User') {
    const login = object.__login as string;
    const id = object.__id as number;
    switch (name) {
      case 'id': return globalId('User', id);
      case 'login': return login;
      case 'name': return login === VIEWER_LOGIN ? VIEWER_NAME : login;
      case 'email': return login === VIEWER_LOGIN ? VIEWER_EMAIL : null;
      case 'url': return '';
      case 'avatarUrl': return '';
      default: return errorFor(`Cannot query field "${name}" on type "User".`);
    }
  }

  if (typeName === 'Ref') {
    switch (name) {
      case 'id': return globalId('Ref', (object.__name as string) ?? '');
      case 'name': return object.__name ?? null;
      case 'prefix': return 'refs/heads/';
      case 'target': return resolveSelection({ __typename: 'Commit', __oid: object.__oid ?? null }, 'Commit', field.selections, ctx);
      default: return errorFor(`Cannot query field "${name}" on type "Ref".`);
    }
  }

  if (typeName === 'IssueComment') {
    const comment = object.__comment as IssueComment;
    switch (name) {
      case 'id': return comment.node_id;
      case 'body': return comment.body;
      case 'createdAt': return comment.created_at;
      case 'updatedAt': return comment.updated_at;
      case 'url': return '';
      case 'author': return resolveSelection(userNode(comment.user.login, comment.user.id), 'User', field.selections, ctx);
      default: return errorFor(`Cannot query field "${name}" on type "IssueComment".`);
    }
  }

  if (typeName === 'Label') {
    const label = object.__label as Label;
    switch (name) {
      case 'id': return label.node_id;
      case 'name': return label.name;
      case 'color': return label.color;
      case 'description': return label.description;
      default: return errorFor(`Cannot query field "${name}" on type "Label".`);
    }
  }

  if (typeName === 'PullRequestFile') {
    const file = object.__file as { filename: string; status: string; additions: number; deletions: number; changes: number };
    switch (name) {
      case 'path': return file.filename;
      case 'additions': return file.additions;
      case 'deletions': return file.deletions;
      case 'changeType': return file.status.toUpperCase();
      default: return errorFor(`Cannot query field "${name}" on type "PullRequestFile".`);
    }
  }

  if (typeName === 'PullRequestCommit') {
    const commit = object.__commit as { oid: string; message: string };
    switch (name) {
      case 'commit': return resolveSelection({ __typename: 'Commit', __oid: commit.oid, __message: commit.message }, 'Commit', field.selections, ctx);
      default: return errorFor(`Cannot query field "${name}" on type "PullRequestCommit".`);
    }
  }

  if (typeName === 'Commit') {
    switch (name) {
      case 'oid': return object.__oid ?? null;
      case 'message': return object.__message ?? '';
      case 'abbreviatedOid': return typeof object.__oid === 'string' ? object.__oid.slice(0, 7) : null;
      default: return errorFor(`Cannot query field "${name}" on type "Commit".`);
    }
  }

  if (typeName.endsWith('Connection')) {
    switch (name) {
      case 'nodes': {
        const nodes = object.__nodes as Array<Record<string, unknown>> | undefined;
        if (nodes === undefined) return [];
        const nodeType = nodes[0]?.__typename as string | undefined;
        return nodes.map((node) => resolveSelection(node, nodeType ?? 'Node', field.selections, ctx));
      }
      case 'edges': {
        const edges = object.__edges as Array<Record<string, unknown>> | undefined;
        if (edges === undefined) return [];
        return edges.map((edge) => resolveSelection(edge, (edge.__typename as string | undefined) ?? 'Edge', field.selections, ctx));
      }
      case 'pageInfo': {
        const pageInfo = object.__pageInfo as Record<string, unknown>;
        return resolveSelection({ __typename: 'PageInfo', ...pageInfo }, 'PageInfo', field.selections, ctx);
      }
      case 'totalCount': return object.__totalCount ?? 0;
      default: return errorFor(`Cannot query field "${name}" on type "${typeName}".`);
    }
  }

  if (typeName.endsWith('Edge')) {
    switch (name) {
      case 'node': {
        const node = object.__node as Record<string, unknown>;
        return resolveSelection(node, (node.__typename as string | undefined) ?? 'Node', field.selections, ctx);
      }
      case 'cursor': return object.__cursor ?? null;
      default: return errorFor(`Cannot query field "${name}" on type "${typeName}".`);
    }
  }

  if (typeName === 'PageInfo') {
    switch (name) {
      case 'hasNextPage': return object.hasNextPage ?? false;
      case 'hasPreviousPage': return object.hasPreviousPage ?? false;
      case 'startCursor': return object.startCursor ?? null;
      case 'endCursor': return object.endCursor ?? null;
      default: return errorFor(`Cannot query field "${name}" on type "PageInfo".`);
    }
  }

  if (typeName === '__Type') {
    const info = object.__info as { kind: string; fields?: string[]; enumValues?: string[] };
    const typeNameArg = object.__typeName as string;
    switch (name) {
      case 'name': return typeNameArg;
      case 'kind': return info.kind;
      case 'description': return null;
      case 'fields': {
        if (info.fields === undefined) return null;
        return info.fields.map((fieldName) => resolveSelection(
          { __typename: '__Field', __fieldName: fieldName },
          '__Field', field.selections, ctx,
        ));
      }
      case 'enumValues': {
        if (info.enumValues === undefined) return null;
        return info.enumValues.map((valueName) => resolveSelection(
          { __typename: '__EnumValue', __valueName: valueName },
          '__EnumValue', field.selections, ctx,
        ));
      }
      case 'possibleTypes': return null;
      case 'interfaces': return [];
      case 'inputFields': return null;
      default: return errorFor(`Cannot query field "${name}" on type "__Type".`);
    }
  }

  if (typeName === '__Field') {
    switch (name) {
      case 'name': return object.__fieldName ?? null;
      case 'description': return null;
      case 'type': return resolveSelection({ __typename: '__TypeRef', __refName: 'String' }, '__TypeRef', field.selections, ctx);
      case 'args': return [];
      case 'isDeprecated': return false;
      case 'deprecationReason': return null;
      default: return errorFor(`Cannot query field "${name}" on type "__Field".`);
    }
  }

  if (typeName === '__EnumValue') {
    switch (name) {
      case 'name': return object.__valueName ?? null;
      case 'description': return null;
      case 'isDeprecated': return false;
      case 'deprecationReason': return null;
      default: return errorFor(`Cannot query field "${name}" on type "__EnumValue".`);
    }
  }

  if (typeName === '__TypeRef') {
    switch (name) {
      case 'name': return object.__refName ?? null;
      case 'kind': return 'SCALAR';
      case 'ofType': return null;
      default: return errorFor(`Cannot query field "${name}" on type "__TypeRef".`);
    }
  }

  if (typeName === '__Schema') {
    switch (name) {
      case 'queryType': return resolveSelection({ __typename: '__Type', __typeName: 'Query', __info: TYPE_INFO.Query }, '__Type', field.selections, ctx);
      case 'mutationType': return resolveSelection({ __typename: '__Type', __typeName: 'Mutation', __info: TYPE_INFO.Mutation }, '__Type', field.selections, ctx);
      case 'types': return Object.entries(TYPE_INFO).map(([typeNameValue, info]) => resolveSelection({ __typename: '__Type', __typeName: typeNameValue, __info: info }, '__Type', field.selections, ctx));
      case 'description': return null;
      default: return errorFor(`Cannot query field "${name}" on type "__Schema".`);
    }
  }

  return errorFor(`Cannot query field "${name}" on type "${typeName}".`);
}

function runGraphqlDocument(body: unknown): Record<string, unknown> {
  const payload = asObject(body);
  const queryText = typeof payload.query === 'string' ? payload.query : '';
  const variables = asObject(payload.variables);
  const operationName = typeof payload.operationName === 'string' ? payload.operationName : null;
  if (queryText === '') {
    return { errors: [{ message: 'No query provided' }] };
  }
  let parsed: { operations: GqlOperation[]; fragments: Map<string, GqlSelection[]> };
  try {
    parsed = new GqlParser(gqlTokenize(queryText)).parseDocument();
  } catch (error) {
    return { errors: [{ message: error instanceof Error ? error.message : 'Failed to parse GraphQL document' }] };
  }
  const operation = operationName !== null
    ? parsed.operations.find((candidate) => candidate.name === operationName) ?? parsed.operations[0]
    : parsed.operations[0];
  if (operation === undefined) return { errors: [{ message: 'No operation found' }] };
  const ctx: GqlContext = { variables: { ...variables }, fragments: parsed.fragments, errors: [] };
  for (const variable of operation.variables) {
    if (!(variable.name in ctx.variables) && variable.defaultValue !== null) {
      ctx.variables[variable.name] = gqlValue(variable.defaultValue, ctx.variables);
    }
  }
  const rootType = operation.kind === 'mutation' ? 'Mutation' : 'Query';
  const data = resolveSelection({ __typename: rootType }, rootType, operation.selections, ctx);
  const result: Record<string, unknown> = { data };
  if (ctx.errors.length > 0) result.errors = ctx.errors;
  return result;
}

function graphqlRouter(req: IncomingMessage, res: ServerResponse, body: Buffer): void {
  if (SHOP_TOKEN !== '') {
    const header = req.headers.authorization ?? '';
    if (header !== `Bearer ${SHOP_TOKEN}`) {
      sendJson(res, 401, { data: null, errors: [{ message: 'Requires authentication' }] });
      return;
    }
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(body.toString('utf8'));
  } catch {
    sendJson(res, 400, { errors: [{ message: 'Problems parsing JSON' }] });
    return;
  }
  if (Array.isArray(parsed)) {
    const results = parsed.map((item) => runGraphqlDocument(item));
    sendJson(res, 200, results);
    return;
  }
  sendJson(res, 200, runGraphqlDocument(parsed));
}

// -------------------------------------------------------------------------------------------
// MCP: JSON-RPC 2.0 over POST /mcp
// -------------------------------------------------------------------------------------------

interface McpTool {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, { type: string; description: string }>;
    required: string[];
  };
}

const MCP_TOOLS: McpTool[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the viewer.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The name of the repository to create.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
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
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        full_name: { type: 'string', description: 'The full name of the repository as owner/repo.' },
      },
      required: ['repo'],
    },
  },
  {
    name: 'list_repos',
    description: 'List the repositories owned by the viewer.',
    inputSchema: {
      type: 'object',
      properties: {},
      required: [],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        full_name: { type: 'string', description: 'The full name of the repository as owner/repo.' },
        title: { type: 'string', description: 'The title of the issue.' },
        body: { type: 'string', description: 'The body of the issue.' },
      },
      required: ['repo', 'title'],
    },
  },
  {
    name: 'get_issue',
    description: 'Get one issue by number.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        full_name: { type: 'string', description: 'The full name of the repository as owner/repo.' },
        issue_number: { type: 'integer', description: 'The number of the issue.' },
      },
      required: ['repo', 'issue_number'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        full_name: { type: 'string', description: 'The full name of the repository as owner/repo.' },
        state: { type: 'string', description: 'Filter by state: open, closed, or all.' },
      },
      required: ['repo'],
    },
  },
  {
    name: 'add_issue_comment',
    description: 'Add a comment to an issue.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        full_name: { type: 'string', description: 'The full name of the repository as owner/repo.' },
        issue_number: { type: 'integer', description: 'The number of the issue.' },
        body: { type: 'string', description: 'The comment body.' },
      },
      required: ['repo', 'issue_number', 'body'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        full_name: { type: 'string', description: 'The full name of the repository as owner/repo.' },
        title: { type: 'string', description: 'The title of the pull request.' },
        body: { type: 'string', description: 'The body of the pull request.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
      },
      required: ['repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'list_pull_requests',
    description: 'List pull requests in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        full_name: { type: 'string', description: 'The full name of the repository as owner/repo.' },
        state: { type: 'string', description: 'Filter by state: open, closed, or all.' },
      },
      required: ['repo'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Squash-merge a pull request.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        full_name: { type: 'string', description: 'The full name of the repository as owner/repo.' },
        pull_number: { type: 'integer', description: 'The number of the pull request.' },
        merge_method: { type: 'string', description: 'The merge method: squash.' },
      },
      required: ['repo', 'pull_number'],
    },
  },
];

/** Map the caller's argument names onto the canonical ones (owner_login, full_name, pullNumber, ...). */
function normalizeMcpArgs(raw: Record<string, unknown>): Record<string, unknown> {
  const args: Record<string, unknown> = { ...raw };
  if (typeof args.full_name === 'string' && args.full_name.includes('/')) {
    const [ownerPart, repoPart] = args.full_name.split('/');
    if (args.owner === undefined) args.owner = ownerPart;
    if (args.repo === undefined) args.repo = repoPart;
  }
  if (args.owner === undefined && typeof args.owner_login === 'string') args.owner = args.owner_login;
  if (args.repo === undefined && typeof args.repo_name === 'string') args.repo = args.repo_name;
  if (args.repo === undefined && typeof args.repository === 'string') args.repo = args.repository;
  if (args.head === undefined && typeof args.head_ref === 'string') args.head = args.head_ref;
  if (args.head === undefined && typeof args.head_branch === 'string') args.head = args.head_branch;
  if (args.base === undefined && typeof args.base_ref === 'string') args.base = args.base_ref;
  if (args.base === undefined && typeof args.base_branch === 'string') args.base = args.base_branch;
  if (args.pull_number === undefined && typeof args.pullNumber === 'number') args.pull_number = args.pullNumber;
  if (args.pull_number === undefined && typeof args.number === 'number') args.pull_number = args.number;
  if (args.issue_number === undefined && typeof args.issueNumber === 'number') args.issue_number = args.issueNumber;
  if (args.issue_number === undefined && typeof args.number === 'number') args.issue_number = args.number;
  if (args.owner === undefined) args.owner = VIEWER_LOGIN;
  return args;
}

function mcpToolResult(data: unknown): Record<string, unknown> {
  const text = JSON.stringify(data);
  return { content: [{ type: 'text', text }], structuredContent: data };
}

function mcpToolError(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], structuredContent: { error: message }, isError: true };
}

function mcpCallTool(name: string, rawArgs: unknown): Record<string, unknown> {
  const args = normalizeMcpArgs(asObject(rawArgs));
  const repoName = typeof args.repo === 'string' ? args.repo : '';
  const owner = typeof args.owner === 'string' ? args.owner : VIEWER_LOGIN;

  const needRepo = (): Repo | Record<string, unknown> => {
    if (repoName === '') return mcpToolError('repo is required');
    const repo = getRepo(owner, repoName);
    if (repo === undefined) return mcpToolError(`Repository ${owner}/${repoName} not found`);
    return repo;
  };

  switch (name) {
    case 'create_repo': {
      const repoNameArg = typeof args.name === 'string' ? args.name.trim() : '';
      if (repoNameArg === '') return mcpToolError('name is required');
      if (repos.has(repoKey(VIEWER_LOGIN, repoNameArg))) return mcpToolError('Repository already exists');
      const repo = newRepo(repoNameArg, {
        private: args.private === true,
        description: typeof args.description === 'string' ? args.description : '',
      });
      return mcpToolResult(repoObject(repo));
    }
    case 'get_repo': {
      const repo = needRepo();
      if (!('objects' in repo)) return repo as Record<string, unknown>;
      return mcpToolResult(repoObject(repo as Repo));
    }
    case 'list_repos': {
      const list = [...repos.values()].filter((repo) => repo.owner === VIEWER_LOGIN).map((repo) => repoObject(repo));
      return mcpToolResult({ repositories: list });
    }
    case 'create_issue': {
      const repo = needRepo();
      if (!('objects' in repo)) return repo as Record<string, unknown>;
      const title = typeof args.title === 'string' ? args.title.trim() : '';
      if (title === '') return mcpToolError('title is required');
      const labels = Array.isArray(args.labels) ? args.labels.filter((item): item is string => typeof item === 'string') : [];
      const created = createIssue(repo as Repo, { title, body: typeof args.body === 'string' ? args.body : '', labels });
      if ('error' in created) return mcpToolError(created.error);
      return mcpToolResult(issueObject(repo as Repo, created));
    }
    case 'get_issue': {
      const repo = needRepo();
      if (!('objects' in repo)) return repo as Record<string, unknown>;
      const number = typeof args.issue_number === 'number' ? args.issue_number : NaN;
      const issue = (repo as Repo).issues.get(number);
      if (issue === undefined) return mcpToolError(`Issue #${args.issue_number} not found`);
      return mcpToolResult(issueObject(repo as Repo, issue));
    }
    case 'list_issues': {
      const repo = needRepo();
      if (!('objects' in repo)) return repo as Record<string, unknown>;
      const state = typeof args.state === 'string' ? args.state : 'open';
      let list = [...(repo as Repo).issues.values()];
      if (state !== 'all') list = list.filter((issue) => issue.state === state);
      list.sort((a, b) => b.number - a.number);
      return mcpToolResult({ issues: list.map((issue) => issueObject(repo as Repo, issue)) });
    }
    case 'add_issue_comment': {
      const repo = needRepo();
      if (!('objects' in repo)) return repo as Record<string, unknown>;
      const number = typeof args.issue_number === 'number' ? args.issue_number : NaN;
      const issue = (repo as Repo).issues.get(number);
      if (issue === undefined) return mcpToolError(`Issue #${args.issue_number} not found`);
      const bodyText = typeof args.body === 'string' ? args.body : '';
      if (bodyText === '') return mcpToolError('body is required');
      const id = nextCommentId;
      nextCommentId += 1;
      const now = clockIso();
      const comment: IssueComment = {
        id,
        node_id: globalId('IssueComment', (repo as Repo).id, id),
        body: bodyText,
        user: { login: VIEWER_LOGIN, id: VIEWER_ID },
        created_at: now,
        updated_at: now,
      };
      issue.comments.push(comment);
      issue.updated_at = now;
      return mcpToolResult({
        id: comment.id,
        node_id: comment.node_id,
        body: comment.body,
        user: { login: comment.user.login, id: comment.user.id, type: 'User' },
        created_at: comment.created_at,
        updated_at: comment.updated_at,
      });
    }
    case 'create_pull_request': {
      const repo = needRepo();
      if (!('objects' in repo)) return repo as Record<string, unknown>;
      const title = typeof args.title === 'string' ? args.title.trim() : '';
      const head = typeof args.head === 'string' ? args.head : '';
      const base = typeof args.base === 'string' ? args.base : (repo as Repo).default_branch;
      if (title === '' || head === '') return mcpToolError('title and head are required');
      const created = createPull(repo as Repo, { title, body: typeof args.body === 'string' ? args.body : '', head, base });
      if ('error' in created) return mcpToolError(created.error);
      return mcpToolResult(pullObject(repo as Repo, created));
    }
    case 'list_pull_requests': {
      const repo = needRepo();
      if (!('objects' in repo)) return repo as Record<string, unknown>;
      const state = typeof args.state === 'string' ? args.state : 'open';
      let list = [...(repo as Repo).pulls.values()];
      if (state !== 'all') list = list.filter((pull) => pull.state === state);
      list.sort((a, b) => b.number - a.number);
      return mcpToolResult({ pull_requests: list.map((pull) => pullObject(repo as Repo, pull)) });
    }
    case 'merge_pull_request': {
      const repo = needRepo();
      if (!('objects' in repo)) return repo as Record<string, unknown>;
      const number = typeof args.pull_number === 'number' ? args.pull_number : NaN;
      const pull = (repo as Repo).pulls.get(number);
      if (pull === undefined) return mcpToolError(`Pull request #${args.pull_number} not found`);
      const method = typeof args.merge_method === 'string' ? args.merge_method : 'squash';
      if (method !== 'squash') return mcpToolError('Only squash merges are supported');
      if (pull.state !== 'open') return mcpToolError('Pull request is not open');
      if (pullMergeable(repo as Repo, pull) !== 'MERGEABLE') return mcpToolError('Merge conflict');
      const mergeSha = mergePullRequest(repo as Repo, pull);
      if (mergeSha === null) return mcpToolError('Merge conflict');
      return mcpToolResult({ sha: mergeSha, merged: true, message: `Pull request #${pull.number} successfully merged` });
    }
    default:
      return mcpToolError(`Unknown tool: ${name}`);
  }
}

function mcpHandleRequest(request: Record<string, unknown>): Record<string, unknown> | null {
  const id = request.id ?? null;
  const method = typeof request.method === 'string' ? request.method : '';
  const params = asObject(request.params);
  const respond = (result: unknown): Record<string, unknown> => ({ jsonrpc: '2.0', id, result });
  const fail = (code: number, message: string): Record<string, unknown> => ({ jsonrpc: '2.0', id, error: { code, message } });

  switch (method) {
    case 'server/discover':
      return respond({
        supportedVersions: ['2026-07-28', '2025-06-18', '2025-03-26'],
        serverInfo: { name: FORGE_NAME, version: FORGE_VERSION },
        capabilities: { tools: {} },
        _meta: { 'io.modelcontextprotocol/serverInfo': { name: FORGE_NAME, version: FORGE_VERSION } },
      });
    case 'initialize': {
      const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2026-07-28';
      return respond({
        protocolVersion: requested,
        capabilities: { tools: {} },
        serverInfo: { name: FORGE_NAME, version: FORGE_VERSION },
      });
    }
    case 'notifications/initialized':
      return null;
    case 'ping':
      return respond({});
    case 'tools/list':
      return respond({ tools: MCP_TOOLS });
    case 'tools/call': {
      const toolName = typeof params.name === 'string' ? params.name : '';
      const tool = MCP_TOOLS.find((candidate) => candidate.name === toolName);
      if (tool === undefined) return fail(-32602, `Unknown tool: ${toolName}`);
      const args = asObject(params.arguments);
      for (const required of tool.inputSchema.required) {
        if (args[required] === undefined) {
          return respond(mcpToolError(`Missing required argument: ${required}`));
        }
      }
      return respond(mcpCallTool(toolName, args));
    }
    default:
      return fail(-32601, `Method not found: ${method}`);
  }
}

function mcpRouter(req: IncomingMessage, res: ServerResponse, body: Buffer): void {
  if (req.method === 'DELETE') {
    res.writeHead(204);
    res.end();
    return;
  }
  if (req.method !== 'POST') {
    sendJson(res, 405, { jsonrpc: '2.0', id: null, error: { code: -32600, message: 'Only POST is supported' } });
    return;
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(body.toString('utf8'));
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (Array.isArray(parsed)) {
    const authed = SHOP_TOKEN === '' || req.headers.authorization === `Bearer ${SHOP_TOKEN}`;
    const results = parsed
      .map((item) => {
        const request = asObject(item);
        // An unauthenticated tools/call is refused per call, even in a batch.
        if (request.method === 'tools/call' && !authed) {
          return { jsonrpc: '2.0', id: request.id ?? null, error: { code: -32000, message: 'Requires authentication' } };
        }
        return mcpHandleRequest(request);
      })
      .filter((result) => result !== null);
    sendJson(res, 200, results);
    return;
  }
  const request = asObject(parsed);
  // tools/call without the shop's bearer token is HTTP 401: authentication
  // is decided before any tool exists, so the refusal must be 401 either way.
  if (request.method === 'tools/call' && SHOP_TOKEN !== '' && req.headers.authorization !== `Bearer ${SHOP_TOKEN}`) {
    sendJson(res, 401, { jsonrpc: '2.0', id: request.id ?? null, error: { code: -32000, message: 'Requires authentication' } });
    return;
  }
  if (request.id === undefined) {
    // A notification: no response body, just acknowledge.
    mcpHandleRequest(request);
    res.writeHead(202);
    res.end();
    return;
  }
  const result = mcpHandleRequest(request);
  if (result === null) {
    res.writeHead(202);
    res.end();
    return;
  }
  sendJson(res, 200, result);
}

// -------------------------------------------------------------------------------------------
// Server: routing, registration, done polling
// -------------------------------------------------------------------------------------------

const server: Server = createServer((req, res) => {
  void (async () => {
    try {
      const url = new URL(req.url ?? '/', `http://${req.headers.host ?? 'localhost'}`);
      const path = url.pathname;
      if (req.method === 'GET' && (path === '/healthz' || path === '/healthz/')) {
        sendJson(res, 200, { ok: true });
        return;
      }
      const needsBody = req.method === 'POST' || req.method === 'PUT' || req.method === 'PATCH' || req.method === 'DELETE';
      const body = needsBody ? await readBody(req) : Buffer.alloc(0);
      if (path === '/mcp' || path === '/mcp/') {
        mcpRouter(req, res, body);
        return;
      }
      if (path === '/api/graphql' || path === '/api/graphql/') {
        if (req.method !== 'POST') {
          sendJson(res, 405, { errors: [{ message: 'Only POST is supported' }] });
          return;
        }
        graphqlRouter(req, res, body);
        return;
      }
      if (path.startsWith('/api/v3')) {
        restRouter(req, res, body);
        return;
      }
      if (gitRouter(req, res, body)) return;
      sendJson(res, 404, { message: 'Not Found' });
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Internal error';
      if (!res.headersSent) sendJson(res, 500, { message });
      else res.end();
    }
  })();
});

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function registerWithEnv(port: number): Promise<void> {
  if (ENV_URL === '') return;
  for (let attempt = 0; attempt < 40; attempt += 1) {
    try {
      const response = await fetch(`${ENV_URL}/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ port }),
      });
      if (response.ok) return;
    } catch {
      // The env may not be listening yet; retry.
    }
    await sleep(500);
  }
}

async function waitForDone(): Promise<void> {
  if (ENV_URL === '') return;
  for (;;) {
    try {
      const response = await fetch(`${ENV_URL}/done`);
      const text = await response.text();
      let parsed: unknown = null;
      try {
        parsed = JSON.parse(text);
      } catch {
        parsed = null;
      }
      if (parsed === true) return;
      if (typeof parsed === 'object' && parsed !== null && (parsed as Record<string, unknown>).done === true) return;
      if (text.trim() === 'true') return;
    } catch {
      // Keep polling; the env may restart.
    }
    await sleep(1000);
  }
}

server.listen(0, '127.0.0.1', () => {
  void (async () => {
    const address = server.address();
    const port = typeof address === 'object' && address !== null ? address.port : 0;
    console.log(`forge listening on 127.0.0.1:${port}`);
    if (ENV_URL === '') return; // Local run: just serve until killed.
    await registerWithEnv(port);
    await waitForDone();
    server.close(() => {
      process.exit(0);
    });
    // If close stalls, still exit.
    setTimeout(() => process.exit(0), 2000).unref();
  })();
});

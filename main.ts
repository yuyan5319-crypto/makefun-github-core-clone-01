// GitHub-compatible git forge — single process, Node stdlib only.
// Serves: git smart HTTP (upload-pack v2, receive-pack v0), REST v3,
// GraphQL v4, MCP (Streamable HTTP JSON-RPC 2.0).
import http from "node:http";
import crypto from "node:crypto";
import zlib from "node:zlib";

const TRIAL_NOW = process.env.MAKEFUN_TRIAL_NOW || "2026-11-19T00:00:00.000Z";
const EPOCH = (() => { const t = Date.parse(TRIAL_NOW); return Number.isFinite(t) ? Math.floor(t / 1000) : 1700000000; })();
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN || "";
const ENV_URL = (process.env.MAKEFUN_ENV_URL || "").replace(/\/$/, "");
const ZERO = "0000000000000000000000000000000000000000";
const AUTHOR = "Forge User <forge@example.com>";

// ---------- small utils ----------
function sha1(b: Buffer): string { return crypto.createHash("sha1").update(b).digest("hex"); }
function objSha(type: string, data: Buffer): string {
  return sha1(Buffer.concat([Buffer.from(`${type} ${data.length}\0`), data]));
}
function pktLine(s: string | Buffer): Buffer {
  const p = typeof s === "string" ? Buffer.from(s) : s;
  const h = Buffer.alloc(4);
  h.write((p.length + 4).toString(16).padStart(4, "0"));
  return Buffer.concat([h, p]);
}
const FLUSH = Buffer.from("0000");
const DELIM = Buffer.from("0001");
function u32(n: number): Buffer { const b = Buffer.alloc(4); b.writeUInt32BE(n >>> 0, 0); return b; }
function b64(s: string): string { return Buffer.from(s).toString("base64"); }
function unb64(s: string): string { try { return Buffer.from(s, "base64").toString("utf8"); } catch { return ""; } }
function nodeId(kind: string, id: string): string { return b64(`${kind}:${id}`); }

// pkt-line reader over a buffer
class Pkt {
  buf: Buffer; pos = 0;
  constructor(buf: Buffer) { this.buf = buf; }
  // returns payload string, or null on flush, or "DELIM" on delim
  line(): string | null | "DELIM" {
    if (this.pos + 4 > this.buf.length) return null;
    const len = parseInt(this.buf.subarray(this.pos, this.pos + 4).toString("ascii"), 16);
    if (!Number.isFinite(len) || len === 0) { this.pos += 4; return null; }
    if (len === 1) { this.pos += 4; return "DELIM"; }
    const s = this.buf.subarray(this.pos + 4, this.pos + len).toString("utf8");
    this.pos += len;
    return s;
  }
  rest(): Buffer { return this.buf.subarray(this.pos); }
}

// ---------- store ----------
interface GitObj { type: string; data: Buffer }
interface Label { id: number; name: string; color: string; description: string }
interface Issue {
  id: number; number: number; title: string; body: string; state: string;
  labels: Label[]; created_at: string; updated_at: string; closed_at: string | null;
  user: string; comments: number;
}
interface Pull {
  id: number; number: number; title: string; body: string; state: string;
  head: string; base: string; headSha: string; baseSha: string; merged: boolean;
  mergeable: boolean; mergeSha: string | null; created_at: string; updated_at: string;
  closed_at: string | null; merged_at: string | null; user: string;
}
interface Repo {
  id: number; name: string; owner: string | null; description: string; defaultBranch: string;
  objects: Map<string, GitObj>; refs: Map<string, string>;
  issues: Issue[]; pulls: Pull[]; labels: Label[];
  issueSeq: number; prSeq: number; labelSeq: number;
  created_at: string; updated_at: string; pushed_at: string;
  fileCache: Map<string, Map<string, { mode: string; sha: string }>>;
}
const repos = new Map<string, Repo>();
let nextRepoId = 1;
let boundLogin: string | null = null;
let reqCounter = 0;

function login(): string { return boundLogin || "user"; }
function bindOwner(o: string): void { if (!boundLogin && o) boundLogin = o; }

function newRepo(name: string, description: string): Repo {
  const r: Repo = {
    id: nextRepoId++, name, owner: null, description, defaultBranch: "main",
    objects: new Map(), refs: new Map(), issues: [], pulls: [], labels: [],
    issueSeq: 0, prSeq: 0, labelSeq: 0,
    created_at: TRIAL_NOW, updated_at: TRIAL_NOW, pushed_at: TRIAL_NOW,
    fileCache: new Map(),
  };
  repos.set(name, r);
  return r;
}
function findRepo(owner: string, name: string): Repo | null {
  const r = repos.get(name);
  if (!r) return null;
  if (r.owner && r.owner !== owner) return null;
  if (!r.owner) { bindOwner(owner); r.owner = owner; }
  return r;
}
function ownerOf(r: Repo): string { return r.owner || login(); }

// ---------- git objects ----------
function storeObj(r: Repo, type: string, data: Buffer): string {
  const s = objSha(type, data);
  if (!r.objects.has(s)) r.objects.set(s, { type, data });
  return s;
}
function getObj(r: Repo, sha: string): GitObj | undefined { return r.objects.get(sha); }
function commitField(data: Buffer, key: string): string[] {
  const head = data.toString("utf8").split("\n\n")[0];
  const out: string[] = [];
  for (const ln of head.split("\n")) if (ln.startsWith(key + " ")) out.push(ln.slice(key.length + 1));
  return out;
}
function commitTree(r: Repo, sha: string): string | null {
  const o = getObj(r, sha); if (!o || o.type !== "commit") return null;
  const t = commitField(o.data, "tree"); return t.length ? t[0] : null;
}
function commitParents(r: Repo, sha: string): string[] {
  const o = getObj(r, sha); if (!o || o.type !== "commit") return [];
  return commitField(o.data, "parent");
}
function isAncestor(r: Repo, anc: string, desc: string): boolean {
  if (anc === desc) return true;
  const seen = new Set<string>(); const stack = [desc];
  while (stack.length) {
    const c = stack.pop()!;
    if (c === anc) return true;
    if (seen.has(c)) continue; seen.add(c);
    for (const p of commitParents(r, c)) stack.push(p);
  }
  return false;
}
function makeCommit(r: Repo, treeSha: string, parents: string[], message: string): string {
  let s = `tree ${treeSha}\n`;
  for (const p of parents) s += `parent ${p}\n`;
  s += `author ${AUTHOR} ${EPOCH} +0000\ncommitter ${AUTHOR} ${EPOCH} +0000\n\n${message}\n`;
  return storeObj(r, "commit", Buffer.from(s));
}
// flat path -> {mode, sha} map of a commit's tree (cached)
function filesOfCommit(r: Repo, commitSha: string): Map<string, { mode: string; sha: string }> {
  const cached = r.fileCache.get(commitSha);
  if (cached) return cached;
  const out = new Map<string, { mode: string; sha: string }>();
  const treeSha = commitTree(r, commitSha);
  if (treeSha) walkTree(r, treeSha, "", out);
  r.fileCache.set(commitSha, out);
  return out;
}
function walkTree(r: Repo, treeSha: string, prefix: string, out: Map<string, { mode: string; sha: string }>): void {
  const o = getObj(r, treeSha); if (!o || o.type !== "tree") return;
  const d = o.data; let p = 0;
  while (p < d.length) {
    const sp = d.indexOf(0x20, p); const nul = d.indexOf(0, sp);
    if (sp < 0 || nul < 0) break;
    const mode = d.subarray(p, sp).toString("ascii");
    const name = d.subarray(sp + 1, nul).toString("utf8");
    const sha = d.subarray(nul + 1, nul + 21).toString("hex");
    p = nul + 21;
    if (mode === "40000") walkTree(r, sha, prefix + name + "/", out);
    else out.set(prefix + name, { mode, sha });
  }
}
function buildTree(r: Repo, files: Map<string, { mode: string; sha: string }>): string {
  function build(dir: string): string {
    const entries: { name: string; mode: string; sha: string; isDir: boolean }[] = [];
    const dirs = new Set<string>();
    for (const [path, f] of files) {
      if (!path.startsWith(dir)) continue;
      const rest = path.slice(dir.length);
      const slash = rest.indexOf("/");
      if (slash === -1) entries.push({ name: rest, mode: f.mode, sha: f.sha, isDir: false });
      else {
        const d = rest.slice(0, slash);
        if (!dirs.has(d)) { dirs.add(d); entries.push({ name: d, mode: "40000", sha: build(dir + d + "/"), isDir: true }); }
      }
    }
    entries.sort((a, b) => {
      const an = a.isDir ? a.name + "/" : a.name, bn = b.isDir ? b.name + "/" : b.name;
      return an < bn ? -1 : an > bn ? 1 : 0;
    });
    const parts: Buffer[] = [];
    for (const e of entries) {
      parts.push(Buffer.from(`${e.mode} ${e.name}\0`));
      parts.push(Buffer.from(e.sha, "hex"));
    }
    return storeObj(r, "tree", Buffer.concat(parts));
  }
  return build("");
}
function diffFiles(a: Map<string, { mode: string; sha: string }>, b: Map<string, { mode: string; sha: string }>): { path: string; status: string }[] {
  const out: { path: string; status: string }[] = [];
  for (const [p, f] of b) {
    const old = a.get(p);
    if (!old) out.push({ path: p, status: "added" });
    else if (old.sha !== f.sha) out.push({ path: p, status: "modified" });
  }
  for (const p of a.keys()) if (!b.has(p)) out.push({ path: p, status: "removed" });
  out.sort((x, y) => (x.path < y.path ? -1 : 1));
  return out;
}

// ---------- packfiles ----------
const TYPE_NUM: Record<string, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const NUM_TYPE: Record<number, string> = { 1: "commit", 2: "tree", 3: "blob", 4: "tag" };
function objHeader(type: string, size: number): Buffer {
  const tn = TYPE_NUM[type] || 3;
  const bytes: number[] = [];
  let sz = size;
  bytes.push(((tn & 7) << 4) | (sz & 15)); sz >>= 4;
  while (sz > 0) { bytes[bytes.length - 1] |= 0x80; bytes.push(sz & 0x7f); sz >>= 7; }
  return Buffer.from(bytes);
}
function writePack(r: Repo, shas: string[]): Buffer {
  const parts: Buffer[] = [Buffer.from("PACK"), u32(2), u32(shas.length)];
  for (const s of shas) {
    const o = r.objects.get(s); if (!o) continue;
    parts.push(objHeader(o.type, o.data.length), zlib.deflateSync(o.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, crypto.createHash("sha1").update(body).digest()]);
}
// find the exact length of a zlib stream starting at buf[pos] (binary search)
function inflateAt(buf: Buffer, pos: number): { data: Buffer; next: number } {
  const avail = buf.length - pos;
  let lo = 1, hi = avail, ok = -1;
  // exponential probe first
  let probe = 64;
  while (probe < avail) {
    try { zlib.inflateSync(buf.subarray(pos, pos + probe)); ok = probe; break; } catch { probe *= 2; }
  }
  if (ok === -1) {
    try { zlib.inflateSync(buf.subarray(pos)); ok = avail; } catch { throw new Error("bad deflate stream"); }
    return { data: zlib.inflateSync(buf.subarray(pos)), next: buf.length };
  }
  lo = Math.floor(probe / 2) + 1; hi = probe;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    try { zlib.inflateSync(buf.subarray(pos, pos + mid)); ok = mid; hi = mid - 1; } catch { lo = mid + 1; }
  }
  return { data: zlib.inflateSync(buf.subarray(pos, pos + ok)), next: pos + ok };
}
interface PackEntry { off: number; typeNum: number; data: Buffer; baseOff?: number; baseSha?: string; delta?: Buffer }
function readPack(buf: Buffer): PackEntry[] {
  if (buf.length < 12 || buf.subarray(0, 4).toString("ascii") !== "PACK") throw new Error("bad pack header");
  const count = buf.readUInt32BE(8);
  const entries: PackEntry[] = [];
  let pos = 12;
  for (let i = 0; i < count; i++) {
    const start = pos;
    let b = buf[pos++]; const typeNum = (b >> 4) & 7;
    let size = b & 15; let shift = 4;
    while (b & 0x80) { b = buf[pos++]; size |= (b & 0x7f) << shift; shift += 7; }
    if (typeNum === 6) {
      let b2 = buf[pos++]; let off = b2 & 0x7f;
      while (b2 & 0x80) { b2 = buf[pos++]; off = ((off + 1) << 7) | (b2 & 0x7f); }
      const inf = inflateAt(buf, pos); pos = inf.next;
      entries.push({ off: start, typeNum, data: Buffer.alloc(0), baseOff: start - off, delta: inf.data });
    } else if (typeNum === 7) {
      const baseSha = buf.subarray(pos, pos + 20).toString("hex"); pos += 20;
      const inf = inflateAt(buf, pos); pos = inf.next;
      entries.push({ off: start, typeNum, data: Buffer.alloc(0), baseSha, delta: inf.data });
    } else {
      const inf = inflateAt(buf, pos); pos = inf.next;
      entries.push({ off: start, typeNum, data: inf.data });
    }
  }
  return entries;
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let p = 0;
  const readVarint = (): number => { let r = 0, s = 0; for (;;) { const b = delta[p++]; r |= (b & 0x7f) << s; s += 7; if (!(b & 0x80)) break; } return r; };
  readVarint(); readVarint();
  const out: Buffer[] = [];
  while (p < delta.length) {
    const op = delta[p++];
    if (op & 0x80) {
      let off = 0, size = 0;
      for (let i = 0; i < 4; i++) if (op & (1 << i)) off |= delta[p++] << (8 * i);
      for (let i = 0; i < 3; i++) if (op & (0x10 << i)) size |= delta[p++] << (8 * i);
      if (size === 0) size = 0x10000;
      out.push(base.subarray(off, off + size));
    } else if (op) { out.push(delta.subarray(p, p + op)); p += op; }
    else throw new Error("delta opcode 0");
  }
  return Buffer.concat(out);
}
// resolve a pack's entries into (type, data) and store them in the repo
function unpackInto(r: Repo, buf: Buffer): string[] {
  const entries = readPack(buf);
  const byOff = new Map<number, PackEntry>();
  for (const e of entries) byOff.set(e.off, e);
  const resolved = new Map<PackEntry, { type: string; data: Buffer }>();
  const resolve = (e: PackEntry, depth: number): { type: string; data: Buffer } => {
    const done = resolved.get(e); if (done) return done;
    if (depth > 64) throw new Error("delta chain too deep");
    let out: { type: string; data: Buffer };
    if (e.typeNum === 6 || e.typeNum === 7) {
      let base: { type: string; data: Buffer } | undefined;
      if (e.baseOff !== undefined) { const be = byOff.get(e.baseOff); if (be) base = resolve(be, depth + 1); }
      if (!base && e.baseSha) { const o = getObj(r, e.baseSha); if (o) base = o; }
      if (!base) throw new Error("delta base missing");
      out = { type: base.type, data: applyDelta(base.data, e.delta!) };
    } else {
      out = { type: NUM_TYPE[e.typeNum] || "blob", data: e.data };
    }
    resolved.set(e, out);
    return out;
  };
  const shas: string[] = [];
  for (const e of entries) {
    const o = resolve(e, 0);
    shas.push(storeObj(r, o.type, o.data));
  }
  return shas;
}
// objects to send for wants, excluding haves; depth limits commit generations
function collectPackObjects(r: Repo, wants: string[], haves: string[], depth: number | null): { shas: string[]; shallow: string[] } {
  const excluded = new Set<string>();
  const markExcluded = (sha: string): void => {
    const stack = [sha];
    while (stack.length) {
      const c = stack.pop()!;
      if (excluded.has(c)) continue; excluded.add(c);
      for (const p of commitParents(r, c)) stack.push(p);
    }
  };
  for (const h of haves) markExcluded(h);
  const shallow: string[] = [];
  const commits: string[] = [];
  const seen = new Set<string>();
  const queue: { sha: string; d: number }[] = wants.filter((w) => w !== ZERO).map((w) => ({ sha: w, d: 0 }));
  while (queue.length) {
    const { sha, d } = queue.shift()!;
    if (seen.has(sha) || excluded.has(sha)) continue;
    const o = getObj(r, sha); if (!o) continue;
    if (o.type !== "commit") { commits.push(sha); seen.add(sha); continue; }
    seen.add(sha); commits.push(sha);
    const atDepth = depth !== null && d >= depth;
    if (atDepth) { shallow.push(sha); continue; }
    for (const p of commitParents(r, sha)) queue.push({ sha: p, d: d + 1 });
  }
  const out: string[] = [];
  const addTree = (treeSha: string): void => {
    if (seen.has(treeSha)) return; seen.add(treeSha);
    const o = getObj(r, treeSha); if (!o) return;
    out.push(treeSha);
    const d = o.data; let p = 0;
    while (p < d.length) {
      const sp = d.indexOf(0x20, p); const nul = d.indexOf(0, sp);
      if (sp < 0 || nul < 0) break;
      const mode = d.subarray(p, sp).toString("ascii");
      const sha = d.subarray(nul + 1, nul + 21).toString("hex");
      p = nul + 21;
      if (mode === "40000") addTree(sha);
      else if (!seen.has(sha)) { seen.add(sha); out.push(sha); }
    }
  };
  const ordered = [...commits];
  for (const c of commits) { const t = commitTree(r, c); if (t) addTree(t); }
  return { shas: [...ordered, ...out.filter((s) => !ordered.includes(s))], shallow };
}
function sidebandPack(pack: Buffer): Buffer {
  const parts: Buffer[] = [];
  for (let i = 0; i < pack.length; i += 65519) {
    const chunk = Buffer.concat([Buffer.from([1]), pack.subarray(i, i + 65519)]);
    parts.push(pktLine(chunk));
  }
  parts.push(FLUSH);
  return Buffer.concat(parts);
}
function rawPktPack(pack: Buffer): Buffer {
  const parts: Buffer[] = [];
  for (let i = 0; i < pack.length; i += 65516) parts.push(pktLine(pack.subarray(i, i + 65516)));
  parts.push(FLUSH);
  return Buffer.concat(parts);
}

// ---------- git smart HTTP ----------
const UPLOAD_CAPS = "multi_ack thin-pack side-band side-band-64k ofs-delta shallow deepen-since deepen-not deepen-relative no-progress include-tag multi_ack_detailed allow-tip-sha1-in-want allow-reachable-sha1-in-want agent=forge/1.0";
const RECEIVE_CAPS = "report-status side-band-64k delete-refs ofs-delta agent=forge/1.0";
function headSha(r: Repo): string { return r.refs.get(`refs/heads/${r.defaultBranch}`) || ZERO; }
function allRefs(r: Repo): { name: string; sha: string }[] {
  const out: { name: string; sha: string }[] = [];
  const heads = [...r.refs.entries()].filter(([n]) => n.startsWith("refs/heads/")).sort();
  const tags = [...r.refs.entries()].filter(([n]) => n.startsWith("refs/tags/")).sort();
  for (const [n, s] of [...heads, ...tags]) out.push({ name: n, sha: s });
  return out;
}
function v0Advert(r: Repo, service: string): Buffer {
  const caps = service === "git-upload-pack" ? UPLOAD_CAPS + ` symref=HEAD:refs/heads/${r.defaultBranch}` : RECEIVE_CAPS + ` symref=HEAD:refs/heads/${r.defaultBranch}`;
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), FLUSH];
  const refs = allRefs(r);
  parts.push(pktLine(`${headSha(r)} HEAD\0${caps}\n`));
  for (const f of refs) parts.push(pktLine(`${f.sha} ${f.name}\n`));
  parts.push(FLUSH);
  return Buffer.concat(parts);
}
function v2Advert(): Buffer {
  return Buffer.concat([
    pktLine("version 2\n"),
    pktLine("ls-refs=unborn\n"),
    pktLine("fetch=shallow wait-for-done\n"),
    pktLine("object-format=sha1\n"),
    pktLine("agent=forge/1.0\n"),
    FLUSH,
  ]);
}
function v2LsRefs(r: Repo, args: string[]): Buffer {
  const prefixes: string[] = [];
  let peel = false, unborn = false, symrefs = false;
  for (const a of args) {
    if (a === "peel") peel = true;
    else if (a === "unborn") unborn = true;
    else if (a === "symrefs") symrefs = true;
    else if (a.startsWith("ref-prefix ")) prefixes.push(a.slice("ref-prefix ".length));
    else if (a.startsWith("ref-prefix=")) prefixes.push(a.slice("ref-prefix=".length));
  }
  void peel;
  const parts: Buffer[] = [];
  const hs = headSha(r);
  const refs = allRefs(r);
  if (hs === ZERO) {
    if (unborn) parts.push(pktLine(`unborn HEAD symref-target:refs/heads/${r.defaultBranch}\n`));
  } else {
    const list = [{ name: "HEAD", sha: hs }, ...refs];
    for (const f of list) {
      if (prefixes.length && !prefixes.some((p) => f.name.startsWith(p))) continue;
      let line = `${f.sha} ${f.name}`;
      if (symrefs && f.name === "HEAD") line += ` symref-target:refs/heads/${r.defaultBranch}`;
      parts.push(pktLine(line + "\n"));
    }
  }
  parts.push(FLUSH);
  return Buffer.concat(parts);
}
function ackFor(r: Repo, wants: string[], haves: string[]): string | null {
  for (const h of haves) for (const w of wants) if (isAncestor(r, h, w)) return h;
  return null;
}
function v2Fetch(r: Repo, args: string[]): Buffer {
  const wants: string[] = []; const haves: string[] = [];
  let deepen: number | null = null; let sideband = false; let done = false;
  for (const a of args) {
    if (a.startsWith("want ")) wants.push(a.slice(5).trim());
    else if (a.startsWith("have ")) haves.push(a.slice(5).trim());
    else if (a === "done") done = true;
    else if (a.startsWith("deepen ")) deepen = parseInt(a.slice(7), 10);
    else if (a === "sideband-all") sideband = true;
  }
  void done;
  const parts: Buffer[] = [];
  const ack = haves.length ? ackFor(r, wants, haves) : null;
  parts.push(pktLine(ack ? `ACK ${ack}\n` : "NAK\n"));
  const { shas, shallow } = collectPackObjects(r, wants, haves, deepen);
  for (const s of shallow) parts.push(pktLine(`shallow ${s}\n`));
  parts.push(pktLine("packfile\n"));
  const pack = writePack(r, shas);
  parts.push(sideband ? sidebandPack(pack) : rawPktPack(pack));
  return Buffer.concat(parts);
}
function v0Upload(r: Repo, body: Buffer): Buffer {
  const pk = new Pkt(body);
  const wants: string[] = []; const haves: string[] = [];
  let deepen: number | null = null; let sideband = false;
  for (;;) {
    const ln = pk.line();
    if (ln === null || ln === "DELIM") break;
    let s = ln.trim();
    const nul = s.indexOf("\0");
    if (nul >= 0) {
      const caps = s.slice(nul + 1);
      if (caps.includes("side-band-64k")) sideband = true;
      s = s.slice(0, nul);
    }
    if (s.startsWith("want ")) wants.push(s.slice(5).trim());
    else if (s.startsWith("have ")) haves.push(s.slice(5).trim());
    else if (s.startsWith("deepen ")) deepen = parseInt(s.slice(7), 10);
    else if (s === "done") break;
  }
  const parts: Buffer[] = [];
  const ack = haves.length ? ackFor(r, wants, haves) : null;
  parts.push(pktLine(ack ? `ACK ${ack}\n` : "NAK\n"));
  const { shas, shallow } = collectPackObjects(r, wants, haves, deepen);
  for (const s of shallow) parts.push(pktLine(`shallow ${s}\n`));
  const pack = writePack(r, shas);
  if (sideband) parts.push(sidebandPack(pack));
  else parts.push(pack);
  return Buffer.concat(parts);
}
function v0Receive(r: Repo, body: Buffer): Buffer {
  const pk = new Pkt(body);
  const cmds: { old: string; nw: string; ref: string }[] = [];
  for (;;) {
    const ln = pk.line();
    if (ln === null) break;
    if (ln === "DELIM") continue;
    let s = ln.trim();
    if (s.startsWith("shallow ") || s.startsWith("unshallow ")) continue;
    const nul = s.indexOf("\0");
    if (nul >= 0) s = s.slice(0, nul);
    const m = s.match(/^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)$/);
    if (m) cmds.push({ old: m[1], nw: m[2], ref: m[3] });
  }
  const packBuf = pk.rest();
  let unpackOk = true;
  if (packBuf.length >= 12) { try { unpackInto(r, packBuf); } catch { unpackOk = false; } }
  const results: { ref: string; ok: boolean; reason: string }[] = [];
  for (const c of cmds) {
    if (c.nw === ZERO) {
      if (r.refs.has(c.ref)) { r.refs.delete(c.ref); results.push({ ref: c.ref, ok: true, reason: "" }); }
      else results.push({ ref: c.ref, ok: false, reason: "no such ref" });
      continue;
    }
    const cur = r.refs.get(c.ref);
    if (c.old === ZERO) {
      if (cur !== undefined) { results.push({ ref: c.ref, ok: false, reason: "already exists" }); continue; }
      r.refs.set(c.ref, c.nw);
      results.push({ ref: c.ref, ok: true, reason: "" });
      continue;
    }
    if (cur !== c.old) { results.push({ ref: c.ref, ok: false, reason: "old value does not match" }); continue; }
    if (!isAncestor(r, c.old, c.nw)) { results.push({ ref: c.ref, ok: false, reason: "non-fast-forward" }); continue; }
    r.refs.set(c.ref, c.nw);
    results.push({ ref: c.ref, ok: true, reason: "" });
  }
  r.fileCache.clear();
  r.pushed_at = TRIAL_NOW; r.updated_at = TRIAL_NOW;
  const parts: Buffer[] = [pktLine(unpackOk ? "unpack ok\n" : "unpack failed\n")];
  for (const res of results) {
    parts.push(pktLine(res.ok ? `ok ${res.ref}\n` : `ng ${res.ref} ${res.reason}\n`));
  }
  parts.push(FLUSH);
  return Buffer.concat(parts);
}

// ---------- REST v3 ----------
type Headers = Record<string, string | string[] | undefined>;
function sendJson(res: http.ServerResponse, status: number, obj: unknown, extra?: Headers): void {
  reqCounter++;
  const body = obj === null ? "" : JSON.stringify(obj);
  res.writeHead(status, {
    "content-type": "application/json",
    "x-github-request-id": `req-${reqCounter}`,
    ...(extra || {}),
  });
  res.end(body);
}
function errJson(res: http.ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message, documentation_url: "https://docs.github.com/rest" });
}
function userObj(lg: string): Record<string, unknown> {
  return { login: lg, id: 1, node_id: nodeId("User", "1"), avatar_url: "", gravatar_id: "", url: `/api/v3/users/${lg}`, html_url: `/${lg}`, type: "User", site_admin: false };
}
function repoObj(r: Repo): Record<string, unknown> {
  const lg = ownerOf(r);
  return {
    id: r.id, node_id: nodeId("Repository", String(r.id)), name: r.name, full_name: `${lg}/${r.name}`,
    owner: userObj(lg), private: false, description: r.description, fork: false,
    created_at: r.created_at, updated_at: r.updated_at, pushed_at: r.pushed_at,
    homepage: "", size: 0, stargazers_count: 0, watchers_count: 0, language: null,
    has_issues: true, has_projects: true, has_downloads: true, has_wiki: true, has_pages: false,
    forks_count: 0, open_issues_count: r.issues.filter((i) => i.state === "open").length,
    license: null, allow_forking: true, is_template: false, topics: [], visibility: "public",
    default_branch: r.defaultBranch, archived: false, disabled: false,
    permissions: { admin: true, maintain: true, push: true, triage: true, pull: true },
    url: `/api/v3/repos/${lg}/${r.name}`, html_url: `/${lg}/${r.name}`,
  };
}
function issueObj(r: Repo, i: Issue): Record<string, unknown> {
  const lg = ownerOf(r);
  return {
    id: i.id, node_id: nodeId("Issue", `${r.id}:${i.number}`), number: i.number,
    title: i.title, body: i.body, state: i.state, locked: false,
    user: userObj(i.user), labels: i.labels.map((l) => ({ id: l.id, node_id: nodeId("Label", `${r.id}:${l.id}`), name: l.name, color: l.color, description: l.description, default: false, url: `/api/v3/repos/${lg}/${r.name}/labels/${encodeURIComponent(l.name)}` })),
    assignee: null, assignees: [], milestone: null, comments: i.comments,
    created_at: i.created_at, updated_at: i.updated_at, closed_at: i.closed_at,
    author_association: "OWNER",
    html_url: `/${lg}/${r.name}/issues/${i.number}`, url: `/api/v3/repos/${lg}/${r.name}/issues/${i.number}`,
    repository_url: `/api/v3/repos/${lg}/${r.name}`, labels_url: `/api/v3/repos/${lg}/${r.name}/issues/${i.number}/labels{/name}`,
    comments_url: `/api/v3/repos/${lg}/${r.name}/issues/${i.number}/comments`, events_url: `/api/v3/repos/${lg}/${r.name}/issues/${i.number}/events`,
  };
}
function prObj(r: Repo, p: Pull): Record<string, unknown> {
  const lg = ownerOf(r);
  const head = { label: `${lg}:${p.head}`, ref: p.head, sha: p.headSha, user: userObj(lg), repo: repoObj(r) };
  const base = { label: `${lg}:${p.base}`, ref: p.base, sha: p.baseSha, user: userObj(lg), repo: repoObj(r) };
  return {
    id: p.id, node_id: nodeId("PullRequest", `${r.id}:${p.number}`), number: p.number,
    title: p.title, body: p.body, state: p.state, locked: false,
    user: userObj(p.user), labels: [], assignee: null, assignees: [], milestone: null,
    head, base, merged: p.merged, mergeable: p.mergeable, mergeable_state: p.mergeable ? "clean" : "dirty",
    merged_at: p.merged_at, merge_commit_sha: p.mergeSha, draft: false,
    created_at: p.created_at, updated_at: p.updated_at, closed_at: p.closed_at,
    html_url: `/${lg}/${r.name}/pull/${p.number}`, url: `/api/v3/repos/${lg}/${r.name}/pulls/${p.number}`,
  };
}
function parseBodyJson(buf: Buffer): { ok: boolean; value: Record<string, unknown> } {
  if (!buf.length) return { ok: true, value: {} };
  try { const v = JSON.parse(buf.toString("utf8")); return { ok: true, value: (v && typeof v === "object" && !Array.isArray(v)) ? v : {} }; }
  catch { return { ok: false, value: {} }; }
}
function pageParams(url: URL): { page: number; perPage: number } {
  const page = Math.max(1, parseInt(url.searchParams.get("page") || "1", 10) || 1);
  const perPage = Math.min(100, Math.max(1, parseInt(url.searchParams.get("per_page") || "30", 10) || 30));
  return { page, perPage };
}
function paginate<T>(res: http.ServerResponse, url: URL, items: T[]): void {
  const { page, perPage } = pageParams(url);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const extra: Headers = {};
  if (start + perPage < items.length) {
    const next = new URL(url.toString()); next.searchParams.set("page", String(page + 1)); next.searchParams.set("per_page", String(perPage));
    extra["link"] = `<${next.toString()}>; rel="next"`;
  }
  sendJson(res, 200, slice, extra);
}
function normalizeBranch(s: string, r: Repo): string {
  const i = s.indexOf(":");
  return i >= 0 ? s.slice(i + 1) : s;
}
function restHandler(req: http.IncomingMessage, res: http.ServerResponse, body: Buffer): void {
  const url = new URL(req.url || "/", "http://x");
  const path = url.pathname;
  const method = req.method || "GET";
  const scopes = { "x-oauth-scopes": "repo, read:org, user" };
  // root
  if (path === "/api/v3/" || path === "/api/v3") {
    if (method !== "GET") return errJson(res, 404, "Not Found");
    return sendJson(res, 200, {
      current_user_url: "/api/v3/user", repository_url: "/api/v3/repos/{owner}/{repo}",
      user_repositories_url: "/api/v3/user/repos", meta_url: "/api/v3/meta",
    }, scopes);
  }
  if (path === "/api/v3/meta") {
    return sendJson(res, 200, { verifiable_password_authentication: true, installed_version: "1.0.0", hooks: [], git: [], pages: [], importer: [], api: [] }, scopes);
  }
  if (path === "/api/v3/user") {
    const lg = login();
    return sendJson(res, 200, { ...userObj(lg), name: lg, email: "forge@example.com", public_repos: repos.size, followers: 0, following: 0, created_at: TRIAL_NOW, updated_at: TRIAL_NOW }, scopes);
  }
  if (path === "/api/v3/user/repos") {
    if (method === "GET") return paginate(res, url, [...repos.values()].map(repoObj));
    if (method === "POST") {
      const parsed = parseBodyJson(body);
      if (!parsed.ok) return errJson(res, 400, "Problems parsing JSON");
      const name = String(parsed.value.name || "").trim();
      if (!name) return errJson(res, 422, "Validation Failed: name is required");
      if (repos.has(name)) return errJson(res, 422, "Validation Failed: name already exists on this account");
      const r = newRepo(name, String(parsed.value.description || ""));
      if (parsed.value.default_branch) r.defaultBranch = String(parsed.value.default_branch);
      return sendJson(res, 201, repoObj(r), scopes);
    }
    return errJson(res, 404, "Not Found");
  }
  const m = path.match(/^\/api\/v3\/repos\/([^/]+)\/([^/]+)(\/.*)?$/);
  if (!m) return errJson(res, 404, "Not Found");
  const [, owner, repoName, rest = ""] = m;
  const r = findRepo(owner, repoName);
  if (!r) return errJson(res, 404, "Not Found");
  const lg = ownerOf(r);
  // repo itself
  if (rest === "" || rest === "/") {
    if (method === "GET") return sendJson(res, 200, repoObj(r), scopes);
    if (method === "PATCH") {
      const parsed = parseBodyJson(body);
      if (!parsed.ok) return errJson(res, 400, "Problems parsing JSON");
      if (parsed.value.description !== undefined) r.description = String(parsed.value.description);
      r.updated_at = TRIAL_NOW;
      return sendJson(res, 200, repoObj(r), scopes);
    }
    if (method === "DELETE") { repos.delete(repoName); res.writeHead(204, { "x-github-request-id": `req-${++reqCounter}` }); return res.end(); }
    return errJson(res, 404, "Not Found");
  }
  // contents
  if (rest.startsWith("/contents")) {
    const fpath = decodeURIComponent(rest.slice("/contents".length).replace(/^\//, ""));
    const parsed = parseBodyJson(body);
    if (method === "GET") {
      if (!fpath) {
        const head = headSha(r);
        const files = head === ZERO ? new Map() : filesOfCommit(r, head);
        const entries: Record<string, unknown>[] = [];
        for (const [p, f] of files) {
          if (p.includes("/")) continue;
          entries.push({ type: "file", encoding: "base64", size: (getObj(r, f.sha)?.data.length || 0), name: p, path: p, content: "", sha: f.sha, url: `/api/v3/repos/${lg}/${repoName}/contents/${p}`, git_url: "", html_url: "", download_url: "" });
        }
        return sendJson(res, 200, entries, scopes);
      }
      const head = headSha(r);
      if (head === ZERO) return errJson(res, 404, "Not Found");
      const files = filesOfCommit(r, head);
      const f = files.get(fpath);
      if (!f) return errJson(res, 404, "Not Found");
      const blob = getObj(r, f.sha);
      const name = fpath.split("/").pop() || fpath;
      return sendJson(res, 200, { type: "file", encoding: "base64", size: blob ? blob.data.length : 0, name, path: fpath, content: blob ? blob.data.toString("base64") : "", sha: f.sha, url: `/api/v3/repos/${lg}/${repoName}/contents/${fpath}`, git_url: "", html_url: "", download_url: "" }, scopes);
    }
    if (method === "PUT") {
      if (!parsed.ok) return errJson(res, 400, "Problems parsing JSON");
      const content = String(parsed.value.content || "");
      const branch = String(parsed.value.branch || r.defaultBranch);
      const ref = `refs/heads/${branch}`;
      const head = r.refs.get(ref) || ZERO;
      const files = head === ZERO ? new Map<string, { mode: string; sha: string }>() : new Map(filesOfCommit(r, head));
      const existing = files.get(fpath);
      if (existing) {
        if (!parsed.value.sha) return errJson(res, 409, "sha is required to update a file");
        if (String(parsed.value.sha) !== existing.sha) return errJson(res, 409, "sha does not match");
      }
      let data: Buffer;
      try { data = Buffer.from(content, "base64"); } catch { return errJson(res, 400, "content is not valid base64"); }
      const blobSha = storeObj(r, "blob", data);
      files.set(fpath, { mode: "100644", sha: blobSha });
      const tree = buildTree(r, files);
      const msg = String(parsed.value.message || (existing ? `Update ${fpath}` : `Create ${fpath}`));
      const commitSha = makeCommit(r, tree, head === ZERO ? [] : [head], msg);
      r.refs.set(ref, commitSha);
      r.fileCache.clear();
      const name = fpath.split("/").pop() || fpath;
      const out = { content: { type: "file", encoding: "base64", size: data.length, name, path: fpath, content: data.toString("base64"), sha: blobSha, url: `/api/v3/repos/${lg}/${repoName}/contents/${fpath}`, git_url: "", html_url: "", download_url: "" }, commit: { sha: commitSha, message: msg, author: { name: "Forge User", email: "forge@example.com", date: TRIAL_NOW }, committer: { name: "Forge User", email: "forge@example.com", date: TRIAL_NOW }, tree: { sha: tree }, parents: head === ZERO ? [] : [{ sha: head }] } };
      return sendJson(res, existing ? 200 : 201, out, scopes);
    }
    if (method === "DELETE") {
      if (!parsed.ok) return errJson(res, 400, "Problems parsing JSON");
      const branch = String(parsed.value.branch || r.defaultBranch);
      const ref = `refs/heads/${branch}`;
      const head = r.refs.get(ref) || ZERO;
      if (head === ZERO) return errJson(res, 404, "Not Found");
      const files = new Map(filesOfCommit(r, head));
      const existing = files.get(fpath);
      if (!existing) return errJson(res, 404, "Not Found");
      if (parsed.value.sha && String(parsed.value.sha) !== existing.sha) return errJson(res, 409, "sha does not match");
      files.delete(fpath);
      const tree = buildTree(r, files);
      const msg = String(parsed.value.message || `Delete ${fpath}`);
      const commitSha = makeCommit(r, tree, [head], msg);
      r.refs.set(ref, commitSha);
      r.fileCache.clear();
      return sendJson(res, 200, { commit: { sha: commitSha, message: msg } }, scopes);
    }
    return errJson(res, 404, "Not Found");
  }
  // labels
  if (rest === "/labels") {
    if (method === "GET") return sendJson(res, 200, r.labels.map((l) => ({ id: l.id, node_id: nodeId("Label", `${r.id}:${l.id}`), name: l.name, color: l.color, description: l.description, default: false, url: `/api/v3/repos/${lg}/${repoName}/labels/${encodeURIComponent(l.name)}` })), scopes);
    if (method === "POST") {
      const parsed = parseBodyJson(body);
      if (!parsed.ok) return errJson(res, 400, "Problems parsing JSON");
      const name = String(parsed.value.name || "").trim();
      if (!name) return errJson(res, 422, "Validation Failed: name is required");
      const l: Label = { id: ++r.labelSeq, name, color: String(parsed.value.color || "ededed"), description: String(parsed.value.description || "") };
      r.labels.push(l);
      return sendJson(res, 201, { id: l.id, node_id: nodeId("Label", `${r.id}:${l.id}`), name: l.name, color: l.color, description: l.description, default: false, url: `/api/v3/repos/${lg}/${repoName}/labels/${encodeURIComponent(l.name)}` }, scopes);
    }
    return errJson(res, 404, "Not Found");
  }
  // issues
  if (rest === "/issues") {
    if (method === "GET") return paginate(res, url, r.issues.map((i) => issueObj(r, i)));
    if (method === "POST") {
      const parsed = parseBodyJson(body);
      if (!parsed.ok) return errJson(res, 400, "Problems parsing JSON");
      const title = String(parsed.value.title || "").trim();
      if (!title) return errJson(res, 422, "Validation Failed: title is required");
      const labelNames: string[] = Array.isArray(parsed.value.labels) ? parsed.value.labels.map((x: unknown) => typeof x === "string" ? x : (x as Record<string, unknown>).name as string) : [];
      const labels: Label[] = [];
      for (const n of labelNames) {
        const found = r.labels.find((l) => l.name === n);
        if (!found) return sendJson(res, 422, { message: "Validation Failed", errors: [{ resource: "Issue", code: "custom", field: "labels", message: `Label does not exist: ${n}` }] }, scopes);
        labels.push(found);
      }
      const issue: Issue = { id: r.id * 100000 + (++r.issueSeq), number: r.issueSeq, title, body: String(parsed.value.body || ""), state: "open", labels, created_at: TRIAL_NOW, updated_at: TRIAL_NOW, closed_at: null, user: login(), comments: 0 };
      r.issues.push(issue);
      return sendJson(res, 201, issueObj(r, issue), scopes);
    }
    return errJson(res, 404, "Not Found");
  }
  const im = rest.match(/^\/issues\/(\d+)$/);
  if (im) {
    const issue = r.issues.find((i) => i.number === Number(im[1]));
    if (!issue) return errJson(res, 404, "Not Found");
    if (method === "GET") return sendJson(res, 200, issueObj(r, issue), scopes);
    return errJson(res, 404, "Not Found");
  }
  // pulls
  if (rest === "/pulls") {
    if (method === "GET") return paginate(res, url, r.pulls.map((p) => prObj(r, p)));
    if (method === "POST") {
      const parsed = parseBodyJson(body);
      if (!parsed.ok) return errJson(res, 400, "Problems parsing JSON");
      const title = String(parsed.value.title || "").trim();
      const head = normalizeBranch(String(parsed.value.head || ""), r);
      const base = normalizeBranch(String(parsed.value.base || r.defaultBranch), r);
      if (!title || !head) return errJson(res, 422, "Validation Failed: title and head are required");
      const headSha = r.refs.get(`refs/heads/${head}`);
      const baseSha = r.refs.get(`refs/heads/${base}`);
      if (!headSha || !baseSha) return sendJson(res, 422, { message: "Validation Failed", errors: [{ resource: "PullRequest", code: "custom", field: "head", message: "Head branch does not exist" }] }, scopes);
      const p: Pull = { id: r.id * 100000 + 50000 + (++r.prSeq), number: r.prSeq, title, body: String(parsed.value.body || ""), state: "open", head, base, headSha, baseSha, merged: false, mergeable: true, mergeSha: null, created_at: TRIAL_NOW, updated_at: TRIAL_NOW, closed_at: null, merged_at: null, user: login() };
      r.pulls.push(p);
      return sendJson(res, 201, prObj(r, p), scopes);
    }
    return errJson(res, 404, "Not Found");
  }
  const pm = rest.match(/^\/pulls\/(\d+)(\/merge)?$/);
  if (pm) {
    const p = r.pulls.find((x) => x.number === Number(pm[1]));
    if (!p) return errJson(res, 404, "Not Found");
    if (pm[2] === "/merge") {
      if (method !== "PUT") return errJson(res, 404, "Not Found");
      if (p.merged || p.state !== "open") return sendJson(res, 405, { message: "Pull Request is not mergeable" }, scopes);
      if (!p.mergeable) return sendJson(res, 405, { message: "Pull Request is not mergeable" }, scopes);
      const baseHead = r.refs.get(`refs/heads/${p.base}`) || ZERO;
      const headTree = commitTree(r, p.headSha);
      if (!headTree) return errJson(res, 422, "Validation Failed: head commit not found");
      const msg = `Merge pull request #${p.number} from ${p.head}`;
      const mergeSha = makeCommit(r, headTree, baseHead === ZERO ? [p.headSha] : [baseHead, p.headSha], msg);
      r.refs.set(`refs/heads/${p.base}`, mergeSha);
      r.fileCache.clear();
      p.merged = true; p.state = "closed"; p.mergeSha = mergeSha; p.merged_at = TRIAL_NOW; p.closed_at = TRIAL_NOW; p.updated_at = TRIAL_NOW;
      return sendJson(res, 200, { sha: mergeSha, merged: true, message: "Pull Request successfully merged" }, scopes);
    }
    if (method === "GET") return sendJson(res, 200, prObj(r, p), scopes);
    return errJson(res, 404, "Not Found");
  }
  // git refs
  const gm = rest.match(/^\/git\/(?:ref|refs)\/(.+)$/);
  if (gm && method === "GET") {
    const refPath = gm[1];
    if (refPath.startsWith("heads/")) {
      const sha = r.refs.get(`refs/${refPath}`);
      if (!sha) return errJson(res, 404, "Not Found");
      return sendJson(res, 200, { ref: `refs/${refPath}`, node_id: nodeId("Ref", `${r.id}:${refPath}`), url: `/api/v3/repos/${lg}/${repoName}/git/refs/${refPath}`, object: { sha, type: "commit", url: `/api/v3/repos/${lg}/${repoName}/git/commits/${sha}` } }, scopes);
    }
    return errJson(res, 404, "Not Found");
  }
  // branches
  const bm = rest.match(/^\/branches\/([^/]+)$/);
  if (bm && method === "GET") {
    const sha = r.refs.get(`refs/heads/${bm[1]}`);
    if (!sha) return errJson(res, 404, "Not Found");
    return sendJson(res, 200, { name: bm[1], commit: { sha, url: `/api/v3/repos/${lg}/${repoName}/commits/${sha}` }, protected: false }, scopes);
  }
  // commits
  if (rest === "/commits" && method === "GET") {
    const head = headSha(r);
    const out: Record<string, unknown>[] = [];
    if (head !== ZERO) {
      const stack = [head]; const seen = new Set<string>();
      while (stack.length && out.length < 30) {
        const c = stack.pop()!;
        if (seen.has(c)) continue; seen.add(c);
        const o = getObj(r, c); if (!o) continue;
        const msg = o.data.toString("utf8").split("\n\n").slice(1).join("\n\n").trim();
        out.push({ sha: c, commit: { message: msg, author: { name: "Forge User", email: "forge@example.com", date: TRIAL_NOW }, committer: { name: "Forge User", email: "forge@example.com", date: TRIAL_NOW }, tree: { sha: commitTree(r, c) } }, parents: commitParents(r, c).map((p) => ({ sha: p })) });
        for (const p of commitParents(r, c)) stack.push(p);
      }
    }
    return sendJson(res, 200, out, scopes);
  }
  const cm = rest.match(/^\/commits\/([^/]+)$/);
  if (cm && method === "GET") {
    const sha = r.refs.get(`refs/heads/${cm[1]}`) || cm[1];
    const o = getObj(r, sha);
    if (!o || o.type !== "commit") return errJson(res, 404, "Not Found");
    const msg = o.data.toString("utf8").split("\n\n").slice(1).join("\n\n").trim();
    return sendJson(res, 200, { sha, commit: { message: msg, author: { name: "Forge User", email: "forge@example.com", date: TRIAL_NOW }, committer: { name: "Forge User", email: "forge@example.com", date: TRIAL_NOW }, tree: { sha: commitTree(r, sha) } }, parents: commitParents(r, sha).map((p) => ({ sha: p })) }, scopes);
  }
  return errJson(res, 404, "Not Found");
}

// ---------- GraphQL ----------
type GqlValue = string | number | boolean | null | GqlValue[] | { [k: string]: GqlValue };
interface GqlField { alias: string | null; name: string; args: Record<string, GqlValue>; sel: GqlField[] | null; frag: string | null; typeCond: string | null }
interface GqlOp { type: string; name: string | null; vars: Record<string, GqlValue>; sel: GqlField[] }
function gqlTokenize(src: string): string[] {
  const toks: string[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (/\s/.test(c) || c === ",") { i++; continue; }
    if (c === "#") { while (i < src.length && src[i] !== "\n") i++; continue; }
    if (src.startsWith("...", i)) { toks.push("..."); i += 3; continue; }
    if ("{}():$![]=@".includes(c)) { toks.push(c); i++; continue; }
    if (c === '"') {
      let j = i + 1; let s = "";
      while (j < src.length && src[j] !== '"') { if (src[j] === "\\") { s += src[j + 1] || ""; j += 2; } else { s += src[j]; j++; } }
      toks.push(JSON.stringify(s)); i = j + 1; continue;
    }
    const m = /^[A-Za-z_][A-Za-z0-9_]*/.exec(src.slice(i)) || /^-?\d+(\.\d+)?/.exec(src.slice(i));
    if (m) { toks.push(m[0]); i += m[0].length; continue; }
    i++;
  }
  return toks;
}
class GqlParser {
  toks: string[]; pos = 0; frags = new Map<string, { typeCond: string; sel: GqlField[] }>();
  constructor(src: string) { this.toks = gqlTokenize(src); }
  peek(): string { return this.toks[this.pos] || ""; }
  next(): string { return this.toks[this.pos++] || ""; }
  expect(t: string): void { if (this.next() !== t) throw new Error(`expected ${t}`); }
  parseValue(vars: Record<string, GqlValue>): GqlValue {
    const t = this.next();
    if (t === "$") return { __var: this.next() } as unknown as GqlValue;
    if (t === "{") { const o: Record<string, GqlValue> = {}; while (this.peek() !== "}") { const k = this.next(); this.expect(":"); o[k] = this.parseValue(vars); } this.expect("}"); return o; }
    if (t === "[") { const a: GqlValue[] = []; while (this.peek() !== "]") a.push(this.parseValue(vars)); this.expect("]"); return a; }
    if (t === "true") return true; if (t === "false") return false; if (t === "null") return null;
    if (t.startsWith('"')) return JSON.parse(t) as string;
    if (/^-?\d+(\.\d+)?$/.test(t)) return Number(t);
    return t; // enum
  }
  parseArgs(vars: Record<string, GqlValue>): Record<string, GqlValue> {
    const args: Record<string, GqlValue> = {};
    this.expect("(");
    while (this.peek() !== ")") { const k = this.next(); this.expect(":"); args[k] = this.parseValue(vars); }
    this.expect(")");
    return args;
  }
  parseSelection(): GqlField[] {
    const fields: GqlField[] = [];
    this.expect("{");
    while (this.peek() !== "}") {
      if (this.peek() === "...") {
        this.next();
        if (this.peek() === "on") { this.next(); const tc = this.next(); const sel = this.parseSelection(); fields.push({ alias: null, name: "", args: {}, sel, frag: null, typeCond: tc }); }
        else { const name = this.next(); fields.push({ alias: null, name: "", args: {}, sel: null, frag: name, typeCond: null }); }
        continue;
      }
      let name = this.next();
      let alias: string | null = null;
      if (this.peek() === ":") { this.next(); alias = name; name = this.next(); }
      let args: Record<string, GqlValue> = {};
      if (this.peek() === "(") args = this.parseArgs({});
      while (this.peek() === "@") { this.next(); this.next(); if (this.peek() === "(") { let d = 0; while (this.pos < this.toks.length) { const t = this.next(); if (t === "(") d++; else if (t === ")") { d--; if (d === 0) break; } } } }
      let sel: GqlField[] | null = null;
      if (this.peek() === "{") sel = this.parseSelection();
      fields.push({ alias, name, args, sel, frag: null, typeCond: null });
    }
    this.expect("}");
    return fields;
  }
  parseDocument(): { ops: GqlOp[] } {
    const ops: GqlOp[] = [];
    while (this.pos < this.toks.length) {
      const t = this.peek();
      if (t === "fragment") {
        this.next(); const name = this.next(); this.expect("on"); const tc = this.next();
        const sel = this.parseSelection();
        this.frags.set(name, { typeCond: tc, sel });
        continue;
      }
      let type = "query"; let name: string | null = null;
      if (t === "query" || t === "mutation" || t === "subscription") { type = this.next(); if (this.peek() !== "{" && this.peek() !== "(") name = this.next(); }
      if (this.peek() === "(") { this.next(); let d = 1; while (d > 0 && this.pos < this.toks.length) { const x = this.next(); if (x === "(") d++; else if (x === ")") d--; } }
      const sel = this.parseSelection();
      ops.push({ type, name, vars: {}, sel });
    }
    return { ops };
  }
}
function resolveVars(v: GqlValue, vars: Record<string, unknown>): unknown {
  if (v && typeof v === "object" && "__var" in (v as Record<string, unknown>)) return vars[(v as Record<string, unknown>).__var as string];
  if (Array.isArray(v)) return v.map((x) => resolveVars(x, vars));
  if (v && typeof v === "object") { const o: Record<string, unknown> = {}; for (const [k, x] of Object.entries(v)) o[k] = resolveVars(x, vars); return o; }
  return v;
}
const ISSUE_FIELDS = ["id", "number", "title", "state", "body"];
const PR_FIELDS = ["id", "number", "headRefName", "baseRefName", "mergeable", "state", "merged", "files"];
const REPO_FIELDS = ["id", "databaseId", "name", "nameWithOwner", "owner", "defaultBranchRef", "viewerPermission", "hasIssuesEnabled", "issue", "issues", "pullRequests", "pullRequest"];
const ISSUE_TYPE: Record<string, string> = { id: "ID", number: "Int", title: "String", state: "IssueState", body: "String" };
const PR_TYPE: Record<string, string> = { id: "ID", number: "Int", headRefName: "String", baseRefName: "String", mergeable: "Boolean", state: "PullRequestState", merged: "Boolean", files: "PullRequestChangedFileConnection" };
const REPO_TYPE: Record<string, string> = { id: "ID", databaseId: "Int", name: "String", nameWithOwner: "String", owner: "RepositoryOwner", defaultBranchRef: "Ref", viewerPermission: "RepositoryPermission", hasIssuesEnabled: "Boolean", issue: "Issue", issues: "IssueConnection", pullRequests: "PullRequestConnection", pullRequest: "PullRequest" };
function typeRef(name: string): Record<string, unknown> { return { kind: "SCALAR", name, ofType: null }; }
function introField(name: string, typeName: string): Record<string, unknown> {
  return { name, description: null, args: [], type: typeRef(typeName), isDeprecated: false, deprecationReason: null };
}
function gqlResolve(op: GqlOp, vars: Record<string, unknown>, errors: { message: string }[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of op.sel) resolveField("Query", null, f, vars, out, errors, op);
  return out;
}
function expandFields(parser: GqlParser, fields: GqlField[]): GqlField[] {
  const out: GqlField[] = [];
  for (const f of fields) {
    if (f.frag) { const frag = parser.frags.get(f.frag); if (frag) out.push(...expandFields(parser, frag.sel)); }
    else if (f.typeCond) { out.push(...expandFields(parser, f.sel || [])); }
    else out.push(f);
  }
  return out;
}
function resolveField(typeName: string, obj: unknown, f: GqlField, vars: Record<string, unknown>, out: Record<string, unknown>, errors: { message: string }[], op: GqlOp): void {
  const key = f.alias || f.name;
  if (f.name === "__typename") { out[key] = typeName; return; }
  const args: Record<string, unknown> = {};
  for (const [k, v] of Object.entries(f.args)) args[k] = resolveVars(v, vars);
  const val = resolveValue(typeName, obj, f.name, args, f.sel, vars, errors, op);
  if (val === undefined) { errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` }); out[key] = null; return; }
  out[key] = val;
}
function resolveValue(typeName: string, obj: unknown, name: string, args: Record<string, unknown>, sel: GqlField[] | null, vars: Record<string, unknown>, errors: { message: string }[], op: GqlOp): unknown {
  // root
  if (typeName === "Query") {
    if (name === "__type") {
      const tn = String(args.name || "");
      if (tn === "Issue") return { kind: "OBJECT", name: "Issue", description: null, fields: ISSUE_FIELDS.map((n) => introField(n, ISSUE_TYPE[n])), interfaces: [], possibleTypes: null, enumValues: null, inputFields: null, ofType: null };
      if (tn === "PullRequest") return { kind: "OBJECT", name: "PullRequest", description: null, fields: PR_FIELDS.map((n) => introField(n, PR_TYPE[n])), interfaces: [], possibleTypes: null, enumValues: null, inputFields: null, ofType: null };
      if (tn === "Repository") return { kind: "OBJECT", name: "Repository", description: null, fields: REPO_FIELDS.map((n) => introField(n, REPO_TYPE[n])), interfaces: [], possibleTypes: null, enumValues: null, inputFields: null, ofType: null };
      if (tn === "SearchType") return { kind: "ENUM", name: "SearchType", description: null, fields: null, interfaces: null, possibleTypes: null, enumValues: ["ISSUE", "REPOSITORY", "USER", "DISCUSSION", "COMMIT", "CODE"].map((n) => ({ name: n, description: null, isDeprecated: false, deprecationReason: null })), inputFields: null, ofType: null };
      return null;
    }
    if (name === "__schema") return { queryType: { name: "Query" }, mutationType: { name: "Mutation" }, subscriptionType: null, types: [], directives: [] };
    if (name === "viewer") return resolveSub("User", { login: login() }, sel, vars, errors, op);
    if (name === "repository") {
      const r = findRepo(String(args.owner || ""), String(args.name || ""));
      if (!r) return null;
      return resolveSub("Repository", r, sel, vars, errors, op);
    }
    if (name === "node") {
      const raw = unb64(String(args.id || ""));
      const m = raw.match(/^(\w+):(.+)$/);
      if (!m) return null;
      if (m[1] === "Repository") { const r = [...repos.values()].find((x) => x.id === Number(m[2])); return r ? resolveSub("Repository", r, sel, vars, errors, op) : null; }
      return null;
    }
    return undefined;
  }
  if (typeName === "Mutation") {
    if (name === "createPullRequest") {
      const input = (args.input || {}) as Record<string, unknown>;
      const rawId = unb64(String(input.repositoryId || ""));
      const m = rawId.match(/^Repository:(\d+)$/);
      const rid = m ? Number(m[1]) : Number(input.repositoryId || 0);
      const r = [...repos.values()].find((x) => x.id === rid);
      if (!r) { errors.push({ message: "Could not resolve to a Repository with the id provided." }); return null; }
      const head = normalizeBranch(String(input.headRefName || ""), r);
      const base = normalizeBranch(String(input.baseRefName || r.defaultBranch), r);
      const headSha = r.refs.get(`refs/heads/${head}`); const baseSha = r.refs.get(`refs/heads/${base}`);
      if (!headSha || !baseSha) { errors.push({ message: "Head or base ref does not exist." }); return null; }
      const p: Pull = { id: r.id * 100000 + 50000 + (++r.prSeq), number: r.prSeq, title: String(input.title || ""), body: String(input.body || ""), state: "open", head, base, headSha, baseSha, merged: false, mergeable: true, mergeSha: null, created_at: TRIAL_NOW, updated_at: TRIAL_NOW, closed_at: null, merged_at: null, user: login() };
      r.pulls.push(p);
      return resolveSub("CreatePullRequestPayload", { pullRequest: p, repo: r }, sel, vars, errors, op);
    }
    if (name === "createIssue") {
      const input = (args.input || {}) as Record<string, unknown>;
      const rawId = unb64(String(input.repositoryId || ""));
      const m = rawId.match(/^Repository:(\d+)$/);
      const rid = m ? Number(m[1]) : Number(input.repositoryId || 0);
      const r = [...repos.values()].find((x) => x.id === rid);
      if (!r) { errors.push({ message: "Could not resolve to a Repository with the id provided." }); return null; }
      const issue: Issue = { id: r.id * 100000 + (++r.issueSeq), number: r.issueSeq, title: String(input.title || ""), body: String(input.body || ""), state: "open", labels: [], created_at: TRIAL_NOW, updated_at: TRIAL_NOW, closed_at: null, user: login(), comments: 0 };
      r.issues.push(issue);
      return resolveSub("CreateIssuePayload", { issue, repo: r }, sel, vars, errors, op);
    }
    return undefined;
  }
  const r = obj as Repo;
  if (typeName === "Repository") {
    const lg = ownerOf(r);
    switch (name) {
      case "id": return nodeId("Repository", String(r.id));
      case "databaseId": return r.id;
      case "name": return r.name;
      case "nameWithOwner": return `${lg}/${r.name}`;
      case "owner": return resolveSub("User", { login: lg }, sel, vars, errors, op);
      case "defaultBranchRef": { const hs = headSha(r); return hs === ZERO ? null : resolveSub("Ref", { name: r.defaultBranch, oid: hs }, sel, vars, errors, op); }
      case "viewerPermission": return "ADMIN";
      case "hasIssuesEnabled": return true;
      case "issue": { const i = r.issues.find((x) => x.number === Number(args.number)); return i ? resolveSub("Issue", { issue: i, repo: r }, sel, vars, errors, op) : null; }
      case "issues": {
        let list = [...r.issues];
        const states = args.states as string[] | undefined;
        if (states) list = list.filter((i) => states.includes(i.state.toUpperCase()));
        const ob = (args.orderBy || {}) as Record<string, unknown>;
        if (ob.field === "CREATED_AT" && ob.direction === "DESC") list.sort((a, b) => b.number - a.number);
        else if (ob.field === "CREATED_AT") list.sort((a, b) => a.number - b.number);
        const first = typeof args.first === "number" ? args.first : list.length;
        const nodes = list.slice(0, first).map((i) => resolveSub("Issue", { issue: i, repo: r }, sel?.find((x) => x.name === "nodes")?.sel || null, vars, errors, op));
        return connResult(sel, nodes, list.length, vars, errors, op);
      }
      case "pullRequest": { const p = r.pulls.find((x) => x.number === Number(args.number)); return p ? resolveSub("PullRequest", { pull: p, repo: r }, sel, vars, errors, op) : null; }
      case "pullRequests": {
        let list = [...r.pulls];
        const states = args.states as string[] | undefined;
        if (states) list = list.filter((p) => states.includes(p.state.toUpperCase()));
        const first = typeof args.first === "number" ? args.first : list.length;
        const nodes = list.slice(0, first).map((p) => resolveSub("PullRequest", { pull: p, repo: r }, sel?.find((x) => x.name === "nodes")?.sel || null, vars, errors, op));
        return connResult(sel, nodes, list.length, vars, errors, op);
      }
      default: return undefined;
    }
  }
  if (typeName === "Issue") {
    const { issue, repo } = obj as { issue: Issue; repo: Repo };
    switch (name) {
      case "id": return nodeId("Issue", `${repo.id}:${issue.number}`);
      case "databaseId": return issue.id;
      case "number": return issue.number;
      case "title": return issue.title;
      case "body": return issue.body;
      case "state": return issue.state.toUpperCase();
      case "createdAt": return issue.created_at;
      case "updatedAt": return issue.updated_at;
      case "closedAt": return issue.closed_at;
      case "author": return resolveSub("User", { login: issue.user }, sel, vars, errors, op);
      case "labels": { const nodes = issue.labels.map((l) => resolveSub("Label", l, sel?.find((x) => x.name === "nodes")?.sel || null, vars, errors, op)); return connResult(sel, nodes, nodes.length, vars, errors, op); }
      case "url": return `/${ownerOf(repo)}/${repo.name}/issues/${issue.number}`;
      default: return undefined;
    }
  }
  if (typeName === "PullRequest") {
    const { pull, repo } = obj as { pull: Pull; repo: Repo };
    switch (name) {
      case "id": return nodeId("PullRequest", `${repo.id}:${pull.number}`);
      case "databaseId": return pull.id;
      case "number": return pull.number;
      case "title": return pull.title;
      case "body": return pull.body;
      case "state": return pull.merged ? "MERGED" : pull.state.toUpperCase();
      case "headRefName": return pull.head;
      case "baseRefName": return pull.base;
      case "mergeable": return pull.mergeable;
      case "merged": return pull.merged;
      case "createdAt": return pull.created_at;
      case "updatedAt": return pull.updated_at;
      case "closedAt": return pull.closed_at;
      case "mergedAt": return pull.merged_at;
      case "author": return resolveSub("User", { login: pull.user }, sel, vars, errors, op);
      case "headRef": return resolveSub("Ref", { name: pull.head, oid: pull.headSha }, sel, vars, errors, op);
      case "baseRef": return resolveSub("Ref", { name: pull.base, oid: pull.baseSha }, sel, vars, errors, op);
      case "files": {
        const baseFiles = pull.baseSha && pull.baseSha !== ZERO ? filesOfCommit(repo, pull.baseSha) : new Map();
        const headFiles = filesOfCommit(repo, pull.headSha);
        const diff = diffFiles(baseFiles, headFiles);
        const nodes = diff.map((d) => resolveSub("PullRequestChangedFile", d, sel?.find((x) => x.name === "nodes")?.sel || null, vars, errors, op));
        return connResult(sel, nodes, nodes.length, vars, errors, op);
      }
      case "url": return `/${ownerOf(repo)}/${repo.name}/pull/${pull.number}`;
      default: return undefined;
    }
  }
  if (typeName === "User") {
    const u = obj as { login: string };
    switch (name) { case "login": return u.login; case "id": return nodeId("User", "1"); case "name": return u.login; default: return undefined; }
  }
  if (typeName === "Ref") {
    const rf = obj as { name: string; oid: string };
    switch (name) { case "name": return rf.name; case "target": return resolveSub("Commit", { oid: rf.oid }, sel, vars, errors, op); default: return undefined; }
  }
  if (typeName === "Commit") {
    const c = obj as { oid: string };
    if (name === "oid") return c.oid;
    return undefined;
  }
  if (typeName === "Label") {
    const l = obj as Label;
    switch (name) { case "id": return nodeId("Label", String(l.id)); case "name": return l.name; case "color": return l.color; case "description": return l.description; default: return undefined; }
  }
  if (typeName === "PullRequestChangedFile") {
    const d = obj as { path: string; status: string };
    switch (name) { case "path": return d.path; case "changeType": return d.status.toUpperCase(); case "additions": return d.status === "added" ? 1 : 0; case "deletions": return d.status === "removed" ? 1 : 0; default: return undefined; }
  }
  if (typeName === "CreatePullRequestPayload" || typeName === "CreateIssuePayload") {
    const pl = obj as { pullRequest?: Pull; issue?: Issue; repo: Repo };
    if (name === "pullRequest" && pl.pullRequest) return resolveSub("PullRequest", { pull: pl.pullRequest, repo: pl.repo }, sel, vars, errors, op);
    if (name === "issue" && pl.issue) return resolveSub("Issue", { issue: pl.issue, repo: pl.repo }, sel, vars, errors, op);
    if (name === "clientMutationId") return null;
    return undefined;
  }
  return undefined;
}
function connResult(sel: GqlField[] | null, nodes: unknown[], total: number, vars: Record<string, unknown>, errors: { message: string }[], op: GqlOp): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  if (!sel) return { nodes, totalCount: total };
  for (const f of sel) {
    if (f.name === "nodes") out.nodes = nodes;
    else if (f.name === "totalCount") out.totalCount = total;
    else if (f.name === "edges") out.edges = (nodes as Record<string, unknown>[]).map((n) => ({ node: n, cursor: "" }));
    else if (f.name === "pageInfo") out.pageInfo = { hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null };
    else if (f.name === "__typename") out.__typename = "Connection";
    else out[f.alias || f.name] = null;
  }
  void vars; void errors; void op;
  return out;
}
function resolveSub(typeName: string, obj: unknown, sel: GqlField[] | null, vars: Record<string, unknown>, errors: { message: string }[], op: GqlOp): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  if (!sel) return out;
  for (const f of sel) resolveField(typeName, obj, f, vars, out, errors, op);
  return out;
}
function graphqlHandler(req: http.IncomingMessage, res: http.ServerResponse, body: Buffer): void {
  let payload: { query?: string; variables?: Record<string, unknown>; operationName?: string };
  try { payload = JSON.parse(body.toString("utf8")); }
  catch { return errJson(res, 400, "Problems parsing JSON"); }
  const query = String(payload.query || "");
  let parser: GqlParser;
  let doc: { ops: GqlOp[] };
  try { parser = new GqlParser(query); doc = parser.parseDocument(); }
  catch { return sendJson(res, 200, { errors: [{ message: "Syntax error in GraphQL query" }] }); }
  const vars = (payload.variables || {}) as Record<string, unknown>;
  const runOp = (op: GqlOp): Record<string, unknown> => {
    const errors: { message: string }[] = [];
    const expanded = expandFields(parser, op.sel);
    const data = gqlResolve({ ...op, sel: expanded }, vars, errors);
    const result: Record<string, unknown> = { data };
    if (errors.length) result.errors = errors;
    return result;
  };
  if (doc.ops.length > 1 && !payload.operationName) {
    return sendJson(res, 200, doc.ops.map(runOp));
  }
  const op = payload.operationName ? doc.ops.find((o) => o.name === payload.operationName) || doc.ops[0] : doc.ops[0];
  if (!op) return sendJson(res, 200, { errors: [{ message: "No operation provided" }] });
  return sendJson(res, 200, runOp(op));
}

// ---------- MCP ----------
const MCP_TOOLS: { name: string; description: string; inputSchema: Record<string, unknown> }[] = [
  { name: "create_repo", description: "Create a new repository for the authenticated user.", inputSchema: { type: "object", properties: { name: { type: "string", description: "Repository name" }, description: { type: "string", description: "Repository description" } }, required: ["name"] } },
  { name: "get_repo", description: "Get a repository by owner and name.", inputSchema: { type: "object", properties: { owner: { type: "string", description: "Repository owner" }, repo: { type: "string", description: "Repository name" }, full_name: { type: "string", description: "owner/repo" } }, required: ["owner", "repo"] } },
  { name: "create_issue", description: "Create an issue in a repository.", inputSchema: { type: "object", properties: { owner: { type: "string" }, repo: { type: "string" }, full_name: { type: "string" }, title: { type: "string", description: "Issue title" }, body: { type: "string", description: "Issue body" } }, required: ["owner", "repo", "title"] } },
  { name: "list_issues", description: "List issues in a repository.", inputSchema: { type: "object", properties: { owner: { type: "string" }, repo: { type: "string" }, full_name: { type: "string" }, state: { type: "string", description: "open, closed or all" } }, required: ["owner", "repo"] } },
  { name: "create_pull_request", description: "Create a pull request in a repository.", inputSchema: { type: "object", properties: { owner: { type: "string" }, repo: { type: "string" }, full_name: { type: "string" }, title: { type: "string" }, head: { type: "string", description: "Head branch" }, base: { type: "string", description: "Base branch" }, body: { type: "string" } }, required: ["owner", "repo", "title", "head", "base"] } },
  { name: "merge_pull_request", description: "Merge a pull request.", inputSchema: { type: "object", properties: { owner: { type: "string" }, repo: { type: "string" }, full_name: { type: "string" }, pull_number: { type: "integer", description: "Pull request number" } }, required: ["owner", "repo", "pull_number"] } },
];
function mcpText(text: string): Record<string, unknown> { return { content: [{ type: "text", text }] }; }
function mcpResolveRepo(args: Record<string, unknown>): Repo | null {
  let owner = String(args.owner || "");
  let repo = String(args.repo || "");
  if (args.full_name) { const parts = String(args.full_name).split("/"); if (parts.length === 2) { owner = parts[0]; repo = parts[1]; } }
  if (!owner || !repo) return null;
  return findRepo(owner, repo);
}
function mcpCallTool(name: string, args: Record<string, unknown>): { result?: Record<string, unknown>; error?: { code: number; message: string } } {
  const tool = MCP_TOOLS.find((t) => t.name === name || name.toLowerCase().endsWith("__" + t.name) || name.toLowerCase() === t.name);
  if (!tool) return { error: { code: -32601, message: `Method not found: ${name}` } };
  const required = (tool.inputSchema.required as string[]) || [];
  const hasFullName = typeof args.full_name === "string" && String(args.full_name).includes("/");
  for (const req of required) {
    if (args[req] === undefined || args[req] === null || args[req] === "") {
      if ((req === "owner" || req === "repo") && hasFullName) continue;
      return { result: { ...mcpText(`Missing required argument: ${req}`), isError: true } };
    }
  }
  switch (tool.name) {
    case "create_repo": {
      const nm = String(args.name || "").trim();
      if (!nm) return { result: { ...mcpText("Missing required argument: name"), isError: true } };
      if (repos.has(nm)) return { result: { ...mcpText(`Repository already exists: ${nm}`), isError: true } };
      const r = newRepo(nm, String(args.description || ""));
      return { result: mcpText(JSON.stringify(repoObj(r))) };
    }
    case "get_repo": {
      const r = mcpResolveRepo(args);
      if (!r) return { result: { ...mcpText("Repository not found"), isError: true } };
      return { result: mcpText(JSON.stringify(repoObj(r))) };
    }
    case "create_issue": {
      const r = mcpResolveRepo(args);
      if (!r) return { result: { ...mcpText("Repository not found"), isError: true } };
      const issue: Issue = { id: r.id * 100000 + (++r.issueSeq), number: r.issueSeq, title: String(args.title || ""), body: String(args.body || ""), state: "open", labels: [], created_at: TRIAL_NOW, updated_at: TRIAL_NOW, closed_at: null, user: login(), comments: 0 };
      r.issues.push(issue);
      return { result: mcpText(JSON.stringify(issueObj(r, issue))) };
    }
    case "list_issues": {
      const r = mcpResolveRepo(args);
      if (!r) return { result: { ...mcpText("Repository not found"), isError: true } };
      const state = String(args.state || "open").toLowerCase();
      const list = state === "all" ? r.issues : r.issues.filter((i) => i.state === state);
      return { result: mcpText(JSON.stringify(list.map((i) => issueObj(r, i)))) };
    }
    case "create_pull_request": {
      const r = mcpResolveRepo(args);
      if (!r) return { result: { ...mcpText("Repository not found"), isError: true } };
      const head = normalizeBranch(String(args.head || ""), r);
      const base = normalizeBranch(String(args.base || r.defaultBranch), r);
      const headSha = r.refs.get(`refs/heads/${head}`); const baseSha = r.refs.get(`refs/heads/${base}`);
      if (!headSha || !baseSha) return { result: { ...mcpText("Head or base branch does not exist"), isError: true } };
      const p: Pull = { id: r.id * 100000 + 50000 + (++r.prSeq), number: r.prSeq, title: String(args.title || ""), body: String(args.body || ""), state: "open", head, base, headSha, baseSha, merged: false, mergeable: true, mergeSha: null, created_at: TRIAL_NOW, updated_at: TRIAL_NOW, closed_at: null, merged_at: null, user: login() };
      r.pulls.push(p);
      return { result: mcpText(JSON.stringify(prObj(r, p))) };
    }
    case "merge_pull_request": {
      const r = mcpResolveRepo(args);
      if (!r) return { result: { ...mcpText("Repository not found"), isError: true } };
      const num = Number(args.pull_number);
      const p = r.pulls.find((x) => x.number === num);
      if (!p) return { result: { ...mcpText("Pull request not found"), isError: true } };
      if (p.merged || p.state !== "open" || !p.mergeable) return { result: { ...mcpText("Pull request is not mergeable"), isError: true } };
      const baseHead = r.refs.get(`refs/heads/${p.base}`) || ZERO;
      const headTree = commitTree(r, p.headSha);
      if (!headTree) return { result: { ...mcpText("Head commit not found"), isError: true } };
      const mergeSha = makeCommit(r, headTree, baseHead === ZERO ? [p.headSha] : [baseHead, p.headSha], `Merge pull request #${p.number} from ${p.head}`);
      r.refs.set(`refs/heads/${p.base}`, mergeSha);
      r.fileCache.clear();
      p.merged = true; p.state = "closed"; p.mergeSha = mergeSha; p.merged_at = TRIAL_NOW; p.closed_at = TRIAL_NOW; p.updated_at = TRIAL_NOW;
      return { result: mcpText(JSON.stringify({ sha: mergeSha, merged: true, message: "Pull Request successfully merged" })) };
    }
    default: return { error: { code: -32601, message: `Method not found: ${name}` } };
  }
}
function mcpHandler(req: http.IncomingMessage, res: http.ServerResponse, body: Buffer): void {
  let msg: { jsonrpc?: string; id?: unknown; method?: string; params?: Record<string, unknown> };
  try { msg = JSON.parse(body.toString("utf8")); }
  catch {
    reqCounter++;
    res.writeHead(400, { "content-type": "application/json", "x-github-request-id": `req-${reqCounter}` });
    return res.end(JSON.stringify({ jsonrpc: "2.0", id: null, error: { code: -32700, message: "Parse error" } }));
  }
  const isNotification = msg.id === undefined || msg.id === null;
  if (isNotification) { res.writeHead(202); return res.end(); }
  const id = msg.id;
  const method = String(msg.method || "");
  const params = (msg.params || {}) as Record<string, unknown>;
  const proto = String((params.protocolVersion as string) || "2026-07-28");
  let result: unknown;
  if (method === "initialize") {
    result = { protocolVersion: proto, capabilities: { tools: { listChanged: false }, resources: {}, prompts: {} }, serverInfo: { name: "github-forge", version: "1.0.0" } };
  } else if (method === "server/discover") {
    result = { supportedVersions: ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"] };
  } else if (method === "ping") {
    result = {};
  } else if (method === "tools/list") {
    result = { tools: MCP_TOOLS };
  } else if (method === "tools/call") {
    const call = mcpCallTool(String(params.name || ""), (params.arguments || {}) as Record<string, unknown>);
    if (call.error) {
      reqCounter++;
      res.writeHead(200, { "content-type": "application/json", "x-github-request-id": `req-${reqCounter}` });
      return res.end(JSON.stringify({ jsonrpc: "2.0", id, error: call.error }));
    }
    result = call.result;
  } else if (method === "resources/list") {
    result = { resources: [] };
  } else if (method === "prompts/list") {
    result = { prompts: [] };
  } else {
    reqCounter++;
    res.writeHead(200, { "content-type": "application/json", "x-github-request-id": `req-${reqCounter}` });
    return res.end(JSON.stringify({ jsonrpc: "2.0", id, error: { code: -32601, message: `Method not found: ${method}` } }));
  }
  reqCounter++;
  res.writeHead(200, { "content-type": "application/json", "mcp-session-id": "forge-session-1", "x-github-request-id": `req-${reqCounter}` });
  res.end(JSON.stringify({ jsonrpc: "2.0", id, result }));
}

// ---------- HTTP server & boot ----------
function authed(req: http.IncomingMessage): boolean {
  const h = req.headers.authorization || "";
  if (!h.startsWith("Bearer ")) return false;
  const tok = h.slice("Bearer ".length).trim();
  if (!tok) return false;
  if (TOKEN) return tok === TOKEN;
  return true;
}
function readBody(req: http.IncomingMessage): Promise<Buffer> {
  return new Promise((resolve) => {
    const chunks: Buffer[] = [];
    req.on("data", (c: Buffer) => { chunks.push(c); if (chunks.reduce((a, b) => a + b.length, 0) > 64 * 1024 * 1024) req.destroy(); });
    req.on("end", () => resolve(Buffer.concat(chunks)));
    req.on("error", () => resolve(Buffer.concat(chunks)));
  });
}
const server = http.createServer(async (req, res) => {
  try {
    const url = new URL(req.url || "/", "http://x");
    const path = url.pathname;
    if (path === "/healthz") { res.writeHead(200, { "content-type": "text/plain" }); res.end("ok"); return; }
    if (!authed(req)) { reqCounter++; res.writeHead(401, { "content-type": "application/json", "x-github-request-id": `req-${reqCounter}` }); res.end(JSON.stringify({ message: "Requires authentication" })); return; }
    const body = await readBody(req);
    if (path === "/api/graphql" && req.method === "POST") { graphqlHandler(req, res, body); return; }
    if (path === "/mcp" && req.method === "POST") { mcpHandler(req, res, body); return; }
    if (path.startsWith("/api/v3")) { restHandler(req, res, body); return; }
    const gm = path.match(/^\/([^/]+)\/([^/]+)\.git\/(.+)$/);
    if (gm) {
      const [, owner, repoName, action] = gm;
      const r = findRepo(owner, repoName);
      if (!r) { reqCounter++; res.writeHead(404, { "content-type": "application/json", "x-github-request-id": `req-${reqCounter}` }); res.end(JSON.stringify({ message: "Not Found" })); return; }
      const v2 = (req.headers["git-protocol"] || "") === "version=2";
      if (action === "info/refs") {
        const service = url.searchParams.get("service") || "";
        if (service === "git-upload-pack") {
          const out = v2 ? v2Advert() : v0Advert(r, "git-upload-pack");
          res.writeHead(200, { "content-type": "application/x-git-upload-pack-advertisement" });
          res.end(out); return;
        }
        if (service === "git-receive-pack") {
          const out = v0Advert(r, "git-receive-pack");
          res.writeHead(200, { "content-type": "application/x-git-receive-pack-advertisement" });
          res.end(out); return;
        }
        res.writeHead(400, { "content-type": "application/json" }); res.end(JSON.stringify({ message: "Bad Request" })); return;
      }
      if (action === "git-upload-pack" && req.method === "POST") {
        if (v2) {
          const pk = new Pkt(body);
          let outParts: Buffer[] = [];
          let curCmd = ""; let curArgs: string[] = [];
          const flushCmd = (): void => {
            if (curCmd === "ls-refs") outParts.push(v2LsRefs(r, curArgs));
            else if (curCmd === "fetch") outParts.push(v2Fetch(r, curArgs));
            curCmd = ""; curArgs = [];
          };
          for (;;) {
            const ln = pk.line();
            if (ln === null) break;
            if (ln === "DELIM") { flushCmd(); continue; }
            const s = ln.trim();
            if (s.startsWith("command=")) { flushCmd(); curCmd = s.slice("command=".length); }
            else if (s) curArgs.push(s);
          }
          flushCmd();
          res.writeHead(200, { "content-type": "application/x-git-upload-pack-result" });
          res.end(Buffer.concat(outParts)); return;
        }
        const out = v0Upload(r, body);
        res.writeHead(200, { "content-type": "application/x-git-upload-pack-result" });
        res.end(out); return;
      }
      if (action === "git-receive-pack" && req.method === "POST") {
        const out = v0Receive(r, body);
        res.writeHead(200, { "content-type": "application/x-git-receive-pack-result" });
        res.end(out); return;
      }
      res.writeHead(404, { "content-type": "application/json" }); res.end(JSON.stringify({ message: "Not Found" })); return;
    }
    errJson(res, 404, "Not Found");
  } catch (e) {
    try { errJson(res, 500, String((e as Error).message || e)); } catch { /* socket gone */ }
  }
});
async function sleep(ms: number): Promise<void> { return new Promise((r) => setTimeout(r, ms)); }
async function register(port: number): Promise<void> {
  if (!ENV_URL) return;
  for (let i = 0; i < 30; i++) {
    try {
      const r = await fetch(`${ENV_URL}/register`, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ port }) });
      if (r.ok) return;
    } catch { /* retry */ }
    await sleep(500);
  }
}
async function pollDone(): Promise<void> {
  if (!ENV_URL) return;
  for (;;) {
    try {
      const r = await fetch(`${ENV_URL}/done`);
      if (r.ok) { const j = (await r.json()) as { done?: boolean }; if (j.done) process.exit(0); }
    } catch { /* keep polling */ }
    await sleep(1000);
  }
}
server.listen(0, "0.0.0.0", () => {
  const addr = server.address();
  const port = typeof addr === "object" && addr ? addr.port : 0;
  register(port).then(() => pollDone());
});

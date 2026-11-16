// github-core-clone-01: a single-process GitHub-compatible git forge.
//
// One in-memory store, four surfaces over it: git smart HTTP (clone/push),
// REST v3, GraphQL v4 and MCP. Standard library only, no git binary, no
// external services. Deterministic by construction: no clock, no randomness
// in any response; every timestamp derives from a fixed epoch plus a
// monotonic sequence number, so the same request sequence always yields
// the same bytes.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------- constants

const ZERO_OID = '0000000000000000000000000000000000000000';
const AGENT = 'forge/1.0';
const IDENTITY = 'Conformance <conformance@make.fun>';
/** Fixed epoch for every timestamp this forge mints (2025-01-01T00:00:00Z). */
const EPOCH_SEC = 1735689600;
/** The one login the suite's token names (the scenario is deterministic). */
const VIEWER = { login: 'adaiversen', id: 1000, name: 'ada iversen', email: 'adaiversen@example.invalid' };
const JSON_TYPE = 'application/json; charset=utf-8';

type GitObjectType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObject { type: GitObjectType; data: Buffer }
interface TreeEntry { mode: string; name: string; oid: string }

// ---------------------------------------------------------------- git objects

function sha1hex(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}

function hashObject(type: GitObjectType, data: Buffer): string {
  const head = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1hex(Buffer.concat([head, data]));
}

const TYPE_CODE: Record<GitObjectType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, GitObjectType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    const nul = data.indexOf(0x00, space + 1);
    if (space < 0 || nul < 0 || nul + 21 > data.length) throw new Error('bad tree entry');
    entries.push({
      mode: data.subarray(offset, space).toString('ascii'),
      name: data.subarray(space + 1, nul).toString('utf8'),
      oid: data.subarray(nul + 1, nul + 21).toString('hex'),
    });
    offset = nul + 21;
  }
  return entries;
}

function compareTreeNames(a: TreeEntry, b: TreeEntry): number {
  const left = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
  const right = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
  return Buffer.compare(left, right);
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
  const view: CommitView = { tree: '', parents: [], author: '', committer: '', message };
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) view.tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) view.parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) view.author = line.slice(7);
    else if (line.startsWith('committer ')) view.committer = line.slice(10);
  }
  return view;
}

function buildCommit(tree: string, parents: readonly string[], message: string, timestampSec: number): Buffer {
  const who = `${IDENTITY} ${timestampSec} +0000`;
  const lines = [`tree ${tree}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${who}`, `committer ${who}`, '');
  return Buffer.from(`${lines.join('\n')}\n${message}`, 'utf8');
}

function parseTag(data: Buffer): { object: string; type: GitObjectType; tag: string; message: string } {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split < 0 ? text : text.slice(0, split);
  const message = split < 0 ? '' : text.slice(split + 2);
  let object = '';
  let type: GitObjectType = 'commit';
  let tag = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim() as GitObjectType;
    else if (line.startsWith('tag ')) tag = line.slice(4).trim();
  }
  return { object, type, tag, message };
}

// ---------------------------------------------------------------- pkt-lines

function pktLine(payload: string | Buffer): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = body.length + 4;
  const head = Buffer.from(len.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, body]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

type Pkt = { kind: 'data'; payload: Buffer } | { kind: 'flush' } | { kind: 'delim' } | { kind: 'response-end' };

/** Decode a whole buffer of pkt-lines. Throws on a malformed header. */
function decodePktLines(buf: Buffer): Pkt[] {
  const out: Pkt[] = [];
  let offset = 0;
  while (offset < buf.length) {
    if (offset + 4 > buf.length) throw new Error('truncated pkt-line');
    const head = buf.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) throw new Error(`invalid pkt-line length ${JSON.stringify(head)}`);
    const len = parseInt(head, 16);
    if (len === 0) { out.push({ kind: 'flush' }); offset += 4; continue; }
    if (len === 1) { out.push({ kind: 'delim' }); offset += 4; continue; }
    if (len === 2) { out.push({ kind: 'response-end' }); offset += 4; continue; }
    if (len < 4 || len > 65520) throw new Error(`bad pkt-line length ${len}`);
    if (offset + len > buf.length) throw new Error('truncated pkt-line');
    out.push({ kind: 'data', payload: buf.subarray(offset + 4, offset + len) });
    offset += len;
  }
  return out;
}

// ---------------------------------------------------------------- packs

function writePackObjectHeader(type: GitObjectType, size: number): Buffer {
  const code = TYPE_CODE[type];
  const bytes: number[] = [];
  let remaining = size;
  let first = (code << 4) | (remaining & 0x0f);
  remaining = Math.floor(remaining / 16);
  while (remaining > 0) {
    bytes.push(first | 0x80);
    first = remaining & 0x7f;
    remaining = Math.floor(remaining / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

function writePack(objects: readonly GitObject[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.allocUnsafe(12);
  header.write('PACK', 0, 4, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const object of objects) {
    parts.push(writePackObjectHeader(object.type, object.data.length));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

function readVarintSize(buffer: Buffer, start: number): { size: number; next: number; first: number } {
  let byte = buffer[start]!;
  const first = byte;
  let size = byte & 0x0f;
  let shift = 4;
  let offset = start + 1;
  while (byte & 0x80) {
    byte = buffer[offset++]!;
    size += (byte & 0x7f) * 2 ** shift;
    shift += 7;
    if (shift > 63) throw new Error('pack size varint too long');
  }
  return { size, next: offset, first };
}

function readOfsDeltaBase(buffer: Buffer, start: number): { baseOffset: number; next: number } {
  let byte = buffer[start]!;
  let offset = start + 1;
  let value = byte & 0x7f;
  while (byte & 0x80) {
    byte = buffer[offset++]!;
    value = ((value + 1) * 128) + (byte & 0x7f);
  }
  return { baseOffset: value, next: offset };
}

function inflateAt(buffer: Buffer, offset: number): { data: Buffer; next: number } {
  const result = inflateSync(buffer.subarray(offset), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
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
      if (offset >= delta.length) throw new Error('delta size varint truncated');
      const byte = delta[offset++]!;
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
    const op = delta[offset++]!;
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) copyOffset |= delta[offset++]! << (bit * 8);
      }
      for (let bit = 0; bit < 3; bit += 1) {
        if (op & (0x10 << bit)) copySize |= delta[offset++]! << (bit * 8);
      }
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op !== 0) {
      delta.copy(out, written, offset, offset + op);
      offset += op;
      written += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  if (written !== targetSize) throw new Error('delta target size mismatch');
  return out;
}

interface RawPackEntry {
  offset: number;
  typeCode: number;
  size: number;
  data: Buffer;
  baseOffset?: number;
  baseOid?: string;
}

/**
 * Parse a packfile and resolve every object (plain, OFS_DELTA, REF_DELTA).
 * `resolveBase` supplies a base object a thin pack leaves out. Returns the
 * objects keyed by oid, in first-appearance order.
 */
function readPack(pack: Buffer, resolveBase?: (oid: string) => GitObject | undefined): Map<string, GitObject> {
  if (pack.length < 32) throw new Error('pack too short');
  if (pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('pack does not start with PACK');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`unsupported pack version ${version}`);
  const declaredCount = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  const trailer = pack.subarray(trailerStart).toString('hex');
  const computed = sha1hex(pack.subarray(0, trailerStart));
  if (trailer !== computed) throw new Error('pack checksum mismatch');
  const raw: RawPackEntry[] = [];
  const byOffset = new Map<number, RawPackEntry>();
  let offset = 12;
  for (let index = 0; index < declaredCount; index += 1) {
    const entryOffset = offset;
    const header = readVarintSize(pack, offset);
    offset = header.next;
    const typeCode = (header.first >> 4) & 0x07;
    const entry: RawPackEntry = { offset: entryOffset, typeCode, size: header.size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      const base = readOfsDeltaBase(pack, offset);
      offset = base.next;
      if (base.baseOffset <= 0 || base.baseOffset > entryOffset) throw new Error('ofs-delta base offset invalid');
      entry.baseOffset = entryOffset - base.baseOffset;
    } else if (typeCode === 7) {
      if (offset + 20 > trailerStart) throw new Error('ref-delta base id truncated');
      entry.baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    } else if (!CODE_TYPE[typeCode]) {
      throw new Error(`pack entry has unknown type code ${typeCode}`);
    }
    const inflated = inflateAt(pack.subarray(0, trailerStart), offset);
    if (inflated.data.length !== header.size) throw new Error('pack entry size mismatch');
    entry.data = inflated.data;
    offset = inflated.next;
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }
  if (offset !== trailerStart) throw new Error('pack has stray bytes before its trailer');
  const objects = new Map<string, GitObject>();
  const resolvedByOid = new Map<string, RawPackEntry>();
  const resolving = new Set<number>();
  const resolve = (entry: RawPackEntry): { type: GitObjectType; data: Buffer; oid: string } => {
    const cached = (entry as RawPackEntry & { resolved?: { type: GitObjectType; data: Buffer; oid: string } }).resolved;
    if (cached) return cached;
    if (resolving.has(entry.offset)) throw new Error('delta cycle');
    resolving.add(entry.offset);
    let type: GitObjectType;
    let data: Buffer;
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset!);
      if (!baseEntry) throw new Error('ofs-delta base not in pack');
      const base = resolve(baseEntry);
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else if (entry.typeCode === 7) {
      const wanted = entry.baseOid!;
      const baseEntry = resolvedByOid.get(wanted);
      if (baseEntry) {
        const base = resolve(baseEntry);
        type = base.type;
        data = applyDelta(base.data, entry.data);
      } else {
        const external = resolveBase?.(wanted);
        if (!external) throw new Error(`ref-delta base ${wanted} not available`);
        type = external.type;
        data = applyDelta(external.data, entry.data);
      }
    } else {
      type = CODE_TYPE[entry.typeCode]!;
      data = entry.data;
    }
    const oid = hashObject(type, data);
    const out = { type, data, oid };
    (entry as RawPackEntry & { resolved?: unknown }).resolved = out;
    resolvedByOid.set(oid, entry);
    resolving.delete(entry.offset);
    return out;
  };
  for (const entry of raw) {
    const resolved = resolve(entry);
    if (!objects.has(resolved.oid)) objects.set(resolved.oid, { type: resolved.type, data: resolved.data });
  }
  return objects;
}

// ---------------------------------------------------------------- the store

/** Monotonic sequence: every created thing takes the next number. Drives all timestamps. */
let seq = 0;
function nextSeq(): number { seq += 1; return seq; }
/** Deterministic ISO timestamp for a sequence number. */
function tsFor(n: number): string { return new Date((EPOCH_SEC + n) * 1000).toISOString(); }
/** Deterministic git timestamp (seconds) for a sequence number. */
function gitTsFor(n: number): number { return EPOCH_SEC + n; }
let reqCounter = 0;
let repoIdSeq = 0;
let globalIdSeq = 0;

interface IssueComment { id: number; body: string; seq: number; createdAt: string; updatedAt: string }
interface Issue {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  labels: string[]; comments: IssueComment[]; seq: number; createdAt: string; updatedAt: string;
  /** Serialized REST view (with trailing newline), null after any mutation. */
  viewCache: string | null;
}
interface Pull {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  merged: boolean; mergedAt: string; mergeCommitSha: string;
  headRef: string; baseRef: string; headSha: string; baseSha: string; baseTreeSha: string;
  seq: number; createdAt: string; updatedAt: string;
}
interface Label { name: string; color: string; description: string }

interface Repo {
  id: number; owner: string; name: string; description: string; private: boolean;
  defaultBranch: string; seq: number; createdAt: string; updatedAt: string;
  objects: Map<string, GitObject>;
  refs: Map<string, string>;
  labels: Map<string, Label>;
  issues: Map<number, Issue>;
  pulls: Map<number, Pull>;
  nextNumber: number;
  /** Bumped on every mutation: invalidates the fetch pack cache. */
  rev: number;
  packCache: Map<string, { rev: number; pack: Buffer; shallow: string[]; unshallow: string[] }>;
  /** v0 advertisements, keyed by service, valid while rev matches. */
  adCache: Map<string, { rev: number; buf: Buffer }>;
  /** ls-refs responses, keyed by the argument string, valid while rev matches. */
  lsCache: Map<string, { rev: number; buf: Buffer }>;
}

const repos = new Map<string, Repo>();

function repoKey(owner: string, name: string): string { return `${owner}/${name}`; }
function findRepo(owner: string, name: string): Repo | undefined {
  if (owner !== VIEWER.login) return undefined;
  return repos.get(repoKey(owner, name));
}

function createRepoRecord(name: string, description: string, isPrivate: boolean): Repo {
  const n = nextSeq();
  const repo: Repo = {
    id: ++repoIdSeq, owner: VIEWER.login, name, description, private: isPrivate,
    defaultBranch: 'main', seq: n, createdAt: tsFor(n), updatedAt: tsFor(n),
    objects: new Map(), refs: new Map(), labels: new Map(),
    issues: new Map(), pulls: new Map(), nextNumber: 1, rev: 0, packCache: new Map(),
    adCache: new Map(), lsCache: new Map(),
  };
  repos.set(repoKey(VIEWER.login, name), repo);
  return repo;
}

function storeObject(repo: Repo, type: GitObjectType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}

function repoObject(repo: Repo, oid: string): GitObject | undefined {
  return repo.objects.get(oid);
}

/** Every object reachable from `roots` (commit -> tree + parents, tag -> target, tree -> entries). */
function collectReachable(repo: Repo, roots: Iterable<string>): Set<string> {
  const seen = new Set<string>();
  const queue: string[] = [];
  for (const root of roots) if (/^[0-9a-f]{40}$/.test(root)) queue.push(root);
  while (queue.length > 0) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (!object) continue;
    seen.add(oid);
    if (object.type === 'commit') {
      const commit = parseCommit(object.data);
      queue.push(commit.tree);
      for (const parent of commit.parents) queue.push(parent);
    } else if (object.type === 'tag') {
      queue.push(parseTag(object.data).object);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) {
        if (entry.mode !== '160000') queue.push(entry.oid);
      }
    }
  }
  return seen;
}

/** True when `ancestor` is reachable from `oid` (or equal), following commit parents. */
function isAncestor(repo: Repo, ancestor: string, oid: string): boolean {
  if (ancestor === oid) return true;
  const seen = new Set<string>();
  const queue = [oid];
  while (queue.length > 0) {
    const current = queue.pop()!;
    if (seen.has(current)) continue;
    seen.add(current);
    const object = repo.objects.get(current);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (parent === ancestor) return true;
      queue.push(parent);
    }
  }
  return false;
}

/** The commit at a ref, or null. Tags resolve to their target commit. */
function refCommit(repo: Repo, ref: string): string | null {
  const oid = repo.refs.get(ref);
  if (!oid) return null;
  const object = repo.objects.get(oid);
  if (!object) return null;
  if (object.type === 'commit') return oid;
  if (object.type === 'tag') {
    const target = parseTag(object.data).object;
    const targetObject = repo.objects.get(target);
    return targetObject && targetObject.type === 'commit' ? target : null;
  }
  return null;
}

/** Flat file listing of a tree: path -> { oid, mode }. */
function flattenTree(repo: Repo, treeOid: string, prefix: string, out: Map<string, { oid: string; mode: string }>): void {
  const object = repo.objects.get(treeOid);
  if (!object || object.type !== 'tree') return;
  for (const entry of parseTree(object.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (entry.mode === '40000') flattenTree(repo, entry.oid, path, out);
    else out.set(path, { oid: entry.oid, mode: entry.mode });
  }
}

function treeOfCommit(repo: Repo, commitOid: string): string | null {
  const object = repo.objects.get(commitOid);
  if (!object || object.type !== 'commit') return null;
  return parseCommit(object.data).tree;
}

/** A tree with `path` set to `blobOid` (creating intermediate trees), other entries kept. */
function treeWithPath(repo: Repo, treeOid: string | null, segments: readonly string[], blobOid: string): string {
  const entries: TreeEntry[] = treeOid === null ? [] : parseTree(repo.objects.get(treeOid)?.data ?? Buffer.alloc(0));
  const head = segments[0]!;
  const rest = segments.slice(1);
  const kept = entries.filter((entry) => entry.name !== head);
  if (rest.length === 0) {
    kept.push({ mode: '100644', name: head, oid: blobOid });
  } else {
    const existing = entries.find((entry) => entry.name === head && entry.mode === '40000');
    const childOid = treeWithPath(repo, existing?.oid ?? null, rest, blobOid);
    kept.push({ mode: '40000', name: head, oid: childOid });
  }
  return storeObject(repo, 'tree', buildTree(kept));
}

/** A tree with `path` removed (pruning trees left empty). Returns null when the tree is empty. */
function treeWithoutPath(repo: Repo, treeOid: string, segments: readonly string[]): string | null {
  const entries = parseTree(repo.objects.get(treeOid)?.data ?? Buffer.alloc(0));
  const head = segments[0]!;
  const rest = segments.slice(1);
  const kept: TreeEntry[] = [];
  for (const entry of entries) {
    if (entry.name !== head) { kept.push(entry); continue; }
    if (rest.length === 0) continue; // drop the file
    if (entry.mode !== '40000') continue;
    const child = treeWithoutPath(repo, entry.oid, rest);
    if (child !== null) kept.push({ mode: '40000', name: head, oid: child });
  }
  if (kept.length === 0) return null;
  return storeObject(repo, 'tree', buildTree(kept));
}

/** Create a commit object on `repo` and store it. Returns its oid. */
function makeCommit(repo: Repo, treeOid: string, parents: readonly string[], message: string): string {
  const n = nextSeq();
  const data = buildCommit(treeOid, parents, message, gitTsFor(n));
  return storeObject(repo, 'commit', data);
}

/** The blob oid at `path` in the tree of `commitOid`, or null. */
function blobAtPath(repo: Repo, commitOid: string, path: string): string | null {
  const treeOid = treeOfCommit(repo, commitOid);
  if (!treeOid) return null;
  const flat = new Map<string, { oid: string; mode: string }>();
  flattenTree(repo, treeOid, '', flat);
  return flat.get(path)?.oid ?? null;
}

/** Walk a ref's first-parent history, newest first. */
function commitWalk(repo: Repo, tip: string, limit: number): string[] {
  const out: string[] = [];
  let current: string | null = tip;
  const seen = new Set<string>();
  while (current !== null && out.length < limit) {
    if (seen.has(current)) break;
    seen.add(current);
    const object = repo.objects.get(current);
    if (!object || object.type !== 'commit') break;
    out.push(current);
    current = parseCommit(object.data).parents[0] ?? null;
  }
  return out;
}

// ---------------------------------------------------------------- fetch planning

interface FetchPlan { objects: GitObject[]; shallow: string[]; unshallow: string[] }

/**
 * The commits and objects a client with `haves` already holds. Traversal
 * from a have stops at the client's shallow boundaries: the client has the
 * boundary commit itself, but not its parents.
 */
function heldClosure(repo: Repo, haves: readonly string[], shallowHeld: readonly string[]): { commits: Set<string>; objects: Set<string> } {
  const commits = new Set<string>();
  const queue = [...haves];
  while (queue.length > 0) {
    const oid = queue.pop()!;
    if (commits.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    commits.add(oid);
    if (shallowHeld.includes(oid)) continue;
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  const objects = new Set<string>();
  const oq = [...commits];
  while (oq.length > 0) {
    const oid = oq.pop()!;
    if (objects.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (!object) continue;
    objects.add(oid);
    if (object.type === 'commit') {
      const commit = parseCommit(object.data);
      oq.push(commit.tree);
      for (const parent of commit.parents) if (commits.has(parent)) oq.push(parent);
    } else if (object.type === 'tag') {
      oq.push(parseTag(object.data).object);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) if (entry.mode !== '160000') oq.push(entry.oid);
    }
  }
  return { commits, objects };
}

/**
 * Which objects a fetch of `wants` (with `haves` already held) must send.
 * Depth counts from the wants: commits at distance <= depth-1 are included,
 * those at exactly depth-1 become shallow boundaries. A client's old shallow
 * boundary whose parents are all included (or already held) stops being shallow.
 */
function planFetch(repo: Repo, wants: readonly string[], haves: readonly string[], depth: number | null, shallowHeld: readonly string[]): FetchPlan {
  const held = heldClosure(repo, haves, shallowHeld);
  // BFS over commit parents from the wants, through held commits too: depth
  // is measured from the wants, and a held commit's parents may still be due.
  const dist = new Map<string, number>();
  const queue: string[] = [];
  for (const want of wants) {
    const object = repo.objects.get(want);
    if (!object) continue;
    const root = object.type === 'tag' ? parseTag(object.data).object : want;
    if (!dist.has(root)) { dist.set(root, 0); queue.push(root); }
  }
  while (queue.length > 0) {
    const oid = queue.shift()!;
    const d = dist.get(oid)!;
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (!dist.has(parent)) { dist.set(parent, d + 1); queue.push(parent); }
    }
  }
  const included = new Set<string>();
  for (const [oid, d] of dist) {
    if (held.commits.has(oid)) continue;
    if (depth !== null && d > depth - 1) continue;
    included.add(oid);
  }
  const shallow: string[] = [];
  if (depth !== null) {
    for (const oid of included) {
      if (dist.get(oid) === depth - 1) shallow.push(oid);
    }
    shallow.sort();
  }
  const unshallow: string[] = [];
  for (const s of shallowHeld) {
    const object = repo.objects.get(s);
    if (!object || object.type !== 'commit') continue;
    const parents = parseCommit(object.data).parents;
    if (parents.length === 0) { unshallow.push(s); continue; }
    if (parents.every((p) => included.has(p) || held.commits.has(p))) unshallow.push(s);
  }
  unshallow.sort();
  // Objects reachable from the included commits (following parents only
  // within the included set) and from non-commit wants, minus what the
  // client already holds.
  const sendRoots = new Set<string>(included);
  for (const want of wants) {
    const object = repo.objects.get(want);
    if (object && object.type !== 'commit') sendRoots.add(want);
  }
  const send = new Set<string>();
  const sq: string[] = [...sendRoots];
  while (sq.length > 0) {
    const oid = sq.pop()!;
    if (send.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (!object) continue;
    send.add(oid);
    if (object.type === 'commit') {
      const commit = parseCommit(object.data);
      sq.push(commit.tree);
      for (const parent of commit.parents) if (included.has(parent)) sq.push(parent);
    } else if (object.type === 'tag') {
      sq.push(parseTag(object.data).object);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) if (entry.mode !== '160000') sq.push(entry.oid);
    }
  }
  const objects: GitObject[] = [];
  const oids = [...send].filter((oid) => !held.objects.has(oid)).sort();
  for (const oid of oids) {
    const object = repo.objects.get(oid);
    if (object) objects.push(object);
  }
  return { objects, shallow, unshallow };
}

/** Cached pack for a fetch: same repo state + same request -> same bytes. */
function cachedFetchPack(repo: Repo, key: string, plan: FetchPlan): Buffer {
  const cached = repo.packCache.get(key);
  if (cached && cached.rev === repo.rev) return cached.pack;
  const pack = writePack(plan.objects);
  repo.packCache.set(key, { rev: repo.rev, pack, shallow: plan.shallow, unshallow: plan.unshallow });
  if (repo.packCache.size > 64) {
    const first = repo.packCache.keys().next().value;
    if (first !== undefined) repo.packCache.delete(first);
  }
  return pack;
}

// ---------------------------------------------------------------- line diff

/** Added/removed line counts between two texts (simple LCS on lines). */
function lineDiff(a: string, b: string): { additions: number; deletions: number } {
  const aLines = a === '' ? [] : a.split('\n');
  const bLines = b === '' ? [] : b.split('\n');
  const n = aLines.length;
  const m = bLines.length;
  if (n * m > 40000) {
    // Large files: fall back to a cheap comparison.
    let additions = 0;
    let deletions = 0;
    const bSet = new Set(bLines);
    for (const line of aLines) if (!bSet.has(line)) deletions += 1;
    const aSet = new Set(aLines);
    for (const line of bLines) if (!aSet.has(line)) additions += 1;
    return { additions, deletions };
  }
  const dp: number[][] = Array.from({ length: n + 1 }, () => new Array<number>(m + 1).fill(0));
  for (let i = n - 1; i >= 0; i -= 1) {
    for (let j = m - 1; j >= 0; j -= 1) {
      dp[i]![j] = aLines[i] === bLines[j] ? dp[i + 1]![j + 1]! + 1 : Math.max(dp[i + 1]![j]!, dp[i]![j + 1]!);
    }
  }
  const common = dp[0]![0]!;
  return { additions: m - common, deletions: n - common };
}

// ---------------------------------------------------------------- HTTP plumbing

// The trial env sets the token before the process starts; cache it once.
const SHOP_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';

function shopToken(): string {
  return SHOP_TOKEN;
}

function authorized(req: IncomingMessage): boolean {
  const token = shopToken();
  if (token === '') return true;
  return req.headers.authorization === `Bearer ${token}`;
}

/** Send an already-serialized JSON document (cached views reuse this). */
function sendJsonText(res: ServerResponse, status: number, text: string, headers: Readonly<Record<string, string>> = {}): void {
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': `req-${++reqCounter}`,
    ...headers,
  });
  res.end(text);
}

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  sendJsonText(res, status, `${JSON.stringify(body)}\n`, headers);
}

function sendNoBody(res: ServerResponse, status: number, headers: Readonly<Record<string, string>> = {}): void {
  res.writeHead(status, { 'x-github-request-id': `req-${++reqCounter}`, ...headers });
  res.end();
}

function sendRaw(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': body.length });
  res.end(body);
}

function jsonError(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let size = 0;
    req.on('data', (chunk: Buffer) => {
      size += chunk.length;
      if (size > 64 * 1024 * 1024) {
        reject(new Error('body too large'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function parseJsonBody(raw: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (raw.length === 0) return { ok: true, value: {} };
  try {
    return { ok: true, value: JSON.parse(raw.toString('utf8')) };
  } catch {
    return { ok: false };
  }
}

function pathOf(req: IncomingMessage): string {
  try {
    return new URL(req.url ?? '/', 'http://entry').pathname;
  } catch {
    return '/';
  }
}

function queryOf(req: IncomingMessage): URLSearchParams {
  try {
    return new URL(req.url ?? '/', 'http://entry').searchParams;
  } catch {
    return new URLSearchParams();
  }
}

function decodeSegment(s: string): string {
  try { return decodeURIComponent(s); } catch { return s; }
}

function splitPath(path: string): string[] {
  return path.split('/').filter((part) => part !== '').map(decodeSegment);
}

/** Paginate `items`; returns the page and the Link header value ('' when one page). */
function paginate<T>(req: IncomingMessage, path: string, query: URLSearchParams, items: readonly T[]): { page: T[]; link: string } {
  const perPageRaw = Number.parseInt(query.get('per_page') ?? '30', 10);
  const perPage = Number.isFinite(perPageRaw) && perPageRaw > 0 ? Math.min(perPageRaw, 100) : 30;
  const pageRaw = Number.parseInt(query.get('page') ?? '1', 10);
  const page = Number.isFinite(pageRaw) && pageRaw > 0 ? pageRaw : 1;
  const total = items.length;
  const pages = Math.max(1, Math.ceil(total / perPage));
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const host = req.headers.host ?? '127.0.0.1';
  const base = `http://${host}${path}`;
  const links: string[] = [];
  const queryFor = (p: number): string => {
    const q = new URLSearchParams(query);
    q.set('page', String(p));
    q.set('per_page', String(perPage));
    return `${base}?${q.toString()}`;
  };
  if (page < pages) links.push(`<${queryFor(page + 1)}>; rel="next"`);
  if (page > 1) links.push(`<${queryFor(page - 1)}>; rel="prev"`);
  if (pages > 1) {
    links.push(`<${queryFor(1)}>; rel="first"`);
    links.push(`<${queryFor(pages)}>; rel="last"`);
  }
  return { page: slice, link: links.join(', ') };
}

// ---------------------------------------------------------------- REST views

function userView(): Record<string, unknown> {
  return {
    login: VIEWER.login, id: VIEWER.id, node_id: `U_${VIEWER.id}`, avatar_url: '',
    name: VIEWER.name, email: VIEWER.email, type: 'User', site_admin: false,
    html_url: `https://github.com/${VIEWER.login}`, url: `/api/v3/users/${VIEWER.login}`,
  };
}

function repoView(repo: Repo): Record<string, unknown> {
  const openCount = [...repo.issues.values()].filter((i) => i.state === 'open').length
    + [...repo.pulls.values()].filter((p) => p.state === 'open').length;
  return {
    id: repo.id, node_id: `R_${repo.id}`, name: repo.name, full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: VIEWER.id, type: 'User' },
    private: repo.private, description: repo.description, default_branch: repo.defaultBranch,
    html_url: `https://github.com/${repo.owner}/${repo.name}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    created_at: repo.createdAt, updated_at: repo.updatedAt, pushed_at: repo.updatedAt,
    has_issues: true, has_projects: true, has_wiki: true, has_pages: false, has_downloads: true,
    forks_count: 0, stargazers_count: 0, watchers_count: 0, open_issues_count: openCount,
    license: null, topics: [], visibility: repo.private ? 'private' : 'public',
    fork: false, archived: false, disabled: false, allow_squash_merge: true,
  };
}

function labelView(label: Label, id: number): Record<string, unknown> {
  return { id, node_id: `L_${id}`, name: label.name, color: label.color, description: label.description, default: false, url: '' };
}

function issueView(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: issue.id, node_id: `I_${issue.id}`, number: issue.number,
    title: issue.title, body: issue.body, state: issue.state,
    labels: issue.labels.map((name) => {
      const label = repo.labels.get(name);
      return label ? { name: label.name, color: label.color, description: label.description } : { name, color: 'ededed', description: '' };
    }),
    user: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
    assignee: null, assignees: [], locked: false,
    comments: issue.comments.length, closed_at: issue.state === 'closed' ? issue.updatedAt : null,
    created_at: issue.createdAt, updated_at: issue.updatedAt,
    html_url: `https://github.com/${repo.owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
  };
}

function commentView(repo: Repo, issue: Issue, comment: IssueComment): Record<string, unknown> {
  return {
    id: comment.id, node_id: `C_${comment.id}`, body: comment.body,
    user: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
    created_at: comment.createdAt, updated_at: comment.updatedAt,
    html_url: `https://github.com/${repo.owner}/${repo.name}/issues/${issue.number}#issuecomment-${comment.id}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/comments/${comment.id}`,
  };
}

function pullView(repo: Repo, pull: Pull): Record<string, unknown> {
  return {
    id: pull.id, node_id: `P_${pull.id}`, number: pull.number,
    title: pull.title, body: pull.body, state: pull.state,
    head: { ref: pull.headRef, sha: pull.headSha, label: `${repo.owner}:${pull.headRef}` },
    base: { ref: pull.baseRef, sha: pull.baseSha, label: `${repo.owner}:${pull.baseRef}` },
    merged: pull.merged, merged_at: pull.merged ? pull.mergedAt : null,
    merge_commit_sha: pull.merged ? pull.mergeCommitSha : null,
    mergeable: prMergeable(repo, pull),
    user: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
    assignee: null, assignees: [], locked: false, draft: false,
    closed_at: pull.state === 'closed' ? pull.updatedAt : null,
    created_at: pull.createdAt, updated_at: pull.updatedAt,
    html_url: `https://github.com/${repo.owner}/${repo.name}/pull/${pull.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}`,
  };
}

/** 'MERGEABLE' | 'CONFLICTING' for a pull request, by three-way tree comparison. */
function prMergeable(repo: Repo, pull: Pull): string {
  if (pull.merged || pull.state === 'closed') return 'UNKNOWN';
  return prConflict(repo, pull) ? 'CONFLICTING' : 'MERGEABLE';
}

function prConflict(repo: Repo, pull: Pull): boolean {
  const baseTip = refCommit(repo, `refs/heads/${pull.baseRef}`);
  const headTip = refCommit(repo, `refs/heads/${pull.headRef}`);
  if (baseTip === null || headTip === null) return false;
  const baseTreeOid = treeOfCommit(repo, pull.baseSha);
  const headTreeOid = treeOfCommit(repo, headTip);
  const currentBaseTreeOid = treeOfCommit(repo, baseTip);
  if (baseTreeOid === null || headTreeOid === null || currentBaseTreeOid === null) return false;
  if (headTreeOid === currentBaseTreeOid) return false;
  const baseFlat = new Map<string, { oid: string; mode: string }>();
  const headFlat = new Map<string, { oid: string; mode: string }>();
  const currentFlat = new Map<string, { oid: string; mode: string }>();
  flattenTree(repo, baseTreeOid, '', baseFlat);
  flattenTree(repo, headTreeOid, '', headFlat);
  flattenTree(repo, currentBaseTreeOid, '', currentFlat);
  const paths = new Set([...baseFlat.keys(), ...headFlat.keys(), ...currentFlat.keys()]);
  for (const path of paths) {
    const baseOid = baseFlat.get(path)?.oid ?? null;
    const headOid = headFlat.get(path)?.oid ?? null;
    const currentOid = currentFlat.get(path)?.oid ?? null;
    const headChanged = headOid !== baseOid;
    const baseChanged = currentOid !== baseOid;
    if (headChanged && baseChanged && headOid !== currentOid) return true;
  }
  return false;
}

/** Squash-merge a pull request onto its base branch. Returns the merge commit oid, or null on conflict. */
function squashMerge(repo: Repo, pull: Pull): string | null {
  const baseTip = refCommit(repo, `refs/heads/${pull.baseRef}`);
  const headTip = refCommit(repo, `refs/heads/${pull.headRef}`);
  if (baseTip === null || headTip === null) return null;
  const headTreeOid = treeOfCommit(repo, headTip);
  const currentBaseTreeOid = treeOfCommit(repo, baseTip);
  if (headTreeOid === null || currentBaseTreeOid === null) return null;
  if (headTreeOid === currentBaseTreeOid) return null;
  if (prConflict(repo, pull)) return null;
  const commitOid = makeCommit(repo, headTreeOid, [baseTip], pull.title);
  repo.refs.set(`refs/heads/${pull.baseRef}`, commitOid);
  repo.rev += 1;
  pull.merged = true;
  pull.state = 'closed';
  pull.mergedAt = tsFor(nextSeq());
  pull.mergeCommitSha = commitOid;
  pull.updatedAt = pull.mergedAt;
  pull.baseSha = commitOid;
  return commitOid;
}

function createIssueRecord(repo: Repo, title: string, body: string, labels: string[]): Issue {
  const n = nextSeq();
  const issue: Issue = {
    id: ++globalIdSeq, number: repo.nextNumber, title, body, state: 'open',
    labels: [...labels], comments: [], seq: n, createdAt: tsFor(n), updatedAt: tsFor(n),
    viewCache: null,
  };
  repo.nextNumber += 1;
  repo.issues.set(issue.number, issue);
  return issue;
}

function createPullRecord(repo: Repo, title: string, body: string, headRef: string, baseRef: string, headSha: string, baseSha: string, baseTreeSha: string): Pull {
  const n = nextSeq();
  const pull: Pull = {
    id: ++globalIdSeq, number: repo.nextNumber, title, body, state: 'open',
    merged: false, mergedAt: '', mergeCommitSha: '',
    headRef, baseRef, headSha, baseSha, baseTreeSha,
    seq: n, createdAt: tsFor(n), updatedAt: tsFor(n),
  };
  repo.nextNumber += 1;
  repo.pulls.set(pull.number, pull);
  return pull;
}

function parseAuthorLine(line: string): { name: string; email: string; date: string } {
  const match = /^(.*?) <([^>]*)> (\d+) ([+-]\d{4})$/.exec(line);
  if (!match) return { name: line, email: '', date: tsFor(0) };
  const ts = Number(match[3]);
  return { name: match[1]!, email: match[2]!, date: new Date(ts * 1000).toISOString() };
}

// ---------------------------------------------------------------- REST handlers

type RestCtx = {
  req: IncomingMessage;
  res: ServerResponse;
  query: URLSearchParams;
  body: unknown;
  segments: string[];
};

function restNotFound(ctx: RestCtx): void {
  jsonError(ctx.res, 404, 'Not Found');
}

function handleRest(ctx: RestCtx): void {
  const { req, res, segments: seg } = ctx;
  const method = req.method ?? 'GET';

  // API root and meta: no auth (GitHub answers them without one).
  if ((method === 'GET') && (seg.length === 2 && seg[0] === 'api' && seg[1] === 'v3')) {
    sendJson(res, 200, {
      current_user_url: '/api/v3/user',
      rate_limit_url: '/api/v3/rate_limit',
      repository_url: '/api/v3/repos/{owner}/{repo}',
    }, { 'x-oauth-scopes': 'repo, read:org' });
    return;
  }
  if (method === 'GET' && seg.length === 3 && seg[0] === 'api' && seg[1] === 'v3' && seg[2] === 'meta') {
    sendJson(res, 200, { installed_version: '1.0.0', verifiable_password_authentication: false });
    return;
  }

  if (!authorized(req)) {
    jsonError(res, 401, 'Bad credentials');
    return;
  }
  if (seg.length < 2 || seg[0] !== 'api' || seg[1] !== 'v3') {
    restNotFound(ctx);
    return;
  }
  const rest = seg.slice(2);

  // GET /api/v3/user
  if (method === 'GET' && rest.length === 1 && rest[0] === 'user') {
    sendJson(res, 200, userView());
    return;
  }

  // POST /api/v3/user/repos  |  GET /api/v3/user/repos
  if (rest.length === 2 && rest[0] === 'user' && rest[1] === 'repos') {
    if (method === 'POST') {
      const body = (ctx.body ?? {}) as Record<string, unknown>;
      const name = typeof body.name === 'string' ? body.name.trim() : '';
      if (name === '' || !/^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$/.test(name)) {
        jsonError(res, 422, 'Invalid repository name');
        return;
      }
      if (repos.has(repoKey(VIEWER.login, name))) {
        jsonError(res, 422, 'Repository already exists');
        return;
      }
      const repo = createRepoRecord(
        name,
        typeof body.description === 'string' ? body.description : '',
        body.private === true,
      );
      sendJson(res, 201, repoView(repo));
      return;
    }
    if (method === 'GET') {
      const all = [...repos.values()].sort((a, b) => a.seq - b.seq).map((repo) => repoView(repo));
      const { page, link } = paginate(req, pathOf(req), ctx.query, all);
      sendJson(res, 200, page, link === '' ? {} : { link });
      return;
    }
    restNotFound(ctx);
    return;
  }

  // /api/v3/repos/{owner}/{repo}[...]
  if (rest.length >= 3 && rest[0] === 'repos') {
    const owner = rest[1]!;
    const name = rest[2]!;
    const repo = findRepo(owner, name);
    if (!repo) {
      restNotFound(ctx);
      return;
    }
    const tail = rest.slice(3);
    handleRepoRest(ctx, repo, tail);
    return;
  }

  restNotFound(ctx);
}

function handleRepoRest(ctx: RestCtx, repo: Repo, tail: string[]): void {
  const { req, res, query, body } = ctx;
  const method = req.method ?? 'GET';
  const b = (body ?? {}) as Record<string, unknown>;

  // GET/PATCH/DELETE /repos/{o}/{r}
  if (tail.length === 0) {
    if (method === 'GET') {
      sendJson(res, 200, repoView(repo));
      return;
    }
    if (method === 'PATCH') {
      if (typeof b.description === 'string') repo.description = b.description;
      if (typeof b.private === 'boolean') repo.private = b.private;
      if (typeof b.default_branch === 'string' && b.default_branch !== '') {
        if (!repo.refs.has(`refs/heads/${b.default_branch}`)) {
          jsonError(res, 422, 'Default branch does not exist');
          return;
        }
        repo.defaultBranch = b.default_branch;
      }
      repo.updatedAt = tsFor(nextSeq());
      sendJson(res, 200, repoView(repo));
      return;
    }
    if (method === 'DELETE') {
      repos.delete(repoKey(repo.owner, repo.name));
      sendNoBody(res, 204);
      return;
    }
    restNotFound(ctx);
    return;
  }

  const head = tail[0]!;

  // Branches
  if (head === 'branches') {
    if (tail.length === 1 && method === 'GET') {
      const names = [...repo.refs.keys()]
        .filter((ref) => ref.startsWith('refs/heads/'))
        .map((ref) => ref.slice('refs/heads/'.length))
        .sort();
      const list = names.map((name) => ({
        name,
        commit: { sha: repo.refs.get(`refs/heads/${name}`) ?? ZERO_OID },
        protected: false,
      }));
      sendJson(res, 200, list);
      return;
    }
    if (tail.length === 2 && method === 'GET') {
      const branch = tail[1]!;
      const oid = repo.refs.get(`refs/heads/${branch}`);
      if (!oid) { restNotFound(ctx); return; }
      sendJson(res, 200, { name: branch, commit: { sha: oid }, protected: false });
      return;
    }
    restNotFound(ctx);
    return;
  }

  // Git Data: refs
  if (head === 'git' && tail[1] === 'refs') {
    if (method === 'GET' && tail.length >= 3) {
      const ref = tail.slice(2).join('/');
      const oid = repo.refs.get(ref);
      if (!oid) { restNotFound(ctx); return; }
      sendJson(res, 200, { ref, object: { sha: oid, type: 'commit', url: '' } });
      return;
    }
    if (method === 'POST' && tail.length === 2) {
      const ref = typeof b.ref === 'string' ? b.ref : '';
      const sha = typeof b.sha === 'string' ? b.sha : '';
      if (!ref.startsWith('refs/') || !/^[0-9a-f]{40}$/.test(sha) || !repo.objects.has(sha)) {
        jsonError(res, 422, 'Invalid ref or sha');
        return;
      }
      if (repo.refs.has(ref)) {
        jsonError(res, 422, 'Reference already exists');
        return;
      }
      repo.refs.set(ref, sha);
      repo.rev += 1;
      sendJson(res, 201, { ref, object: { sha, type: 'commit', url: '' } });
      return;
    }
    restNotFound(ctx);
    return;
  }

  // Commits
  if (head === 'commits') {
    if (method === 'GET' && tail.length === 1) {
      const refParam = query.get('sha') ?? repo.defaultBranch;
      let tip: string | null = null;
      if (/^[0-9a-f]{40}$/.test(refParam)) {
        tip = repo.objects.has(refParam) ? refParam : null;
      } else {
        tip = refCommit(repo, `refs/heads/${refParam}`);
      }
      if (tip === null) { restNotFound(ctx); return; }
      const perPageRaw = Number.parseInt(query.get('per_page') ?? '30', 10);
      const limit = Number.isFinite(perPageRaw) && perPageRaw > 0 ? Math.min(perPageRaw, 100) : 30;
      const walk = commitWalk(repo, tip, limit);
      const list = walk.map((sha) => {
        const commit = parseCommit(repo.objects.get(sha)!.data);
        const author = parseAuthorLine(commit.author);
        const committer = parseAuthorLine(commit.committer);
        return {
          sha,
          commit: {
            message: commit.message,
            author: { name: author.name, email: author.email, date: author.date },
            committer: { name: committer.name, email: committer.email, date: committer.date },
            tree: { sha: commit.tree },
          },
          parents: commit.parents.map((p) => ({ sha: p })),
          author: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
          committer: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
        };
      });
      sendJson(res, 200, list);
      return;
    }
    restNotFound(ctx);
    return;
  }

  // Contents
  if (head === 'contents') {
    const contentPath = tail.slice(1).join('/');
    handleContents(ctx, repo, contentPath);
    return;
  }

  // Labels
  if (head === 'labels') {
    if (method === 'GET' && tail.length === 1) {
      const list = [...repo.labels.values()]
        .sort((a, c) => a.name.localeCompare(c.name))
        .map((label) => labelView(label, 0));
      sendJson(res, 200, list);
      return;
    }
    if (method === 'POST' && tail.length === 1) {
      const name = typeof b.name === 'string' ? b.name.trim() : '';
      if (name === '') { jsonError(res, 422, 'Label name is required'); return; }
      if (repo.labels.has(name)) { jsonError(res, 422, 'Label already exists'); return; }
      const label: Label = {
        name,
        color: typeof b.color === 'string' ? b.color.replace(/^#/, '') : 'ededed',
        description: typeof b.description === 'string' ? b.description : '',
      };
      repo.labels.set(name, label);
      sendJson(res, 201, labelView(label, ++globalIdSeq));
      return;
    }
    restNotFound(ctx);
    return;
  }

  // Issues
  if (head === 'issues') {
    handleIssues(ctx, repo, tail.slice(1));
    return;
  }

  // Pulls
  if (head === 'pulls') {
    handlePulls(ctx, repo, tail.slice(1));
    return;
  }

  restNotFound(ctx);
}

function handleContents(ctx: RestCtx, repo: Repo, contentPath: string): void {
  const { req, res, query, body } = ctx;
  const method = req.method ?? 'GET';
  const b = (body ?? {}) as Record<string, unknown>;

  const resolveTip = (): string | null => {
    const ref = query.get('ref') ?? repo.defaultBranch;
    if (/^[0-9a-f]{40}$/.test(ref)) return repo.objects.has(ref) ? ref : null;
    return refCommit(repo, `refs/heads/${ref}`);
  };

  if (method === 'GET') {
    const tip = resolveTip();
    if (tip === null) { restNotFound(ctx); return; }
    const treeOid = treeOfCommit(repo, tip);
    if (treeOid === null) { restNotFound(ctx); return; }
    if (contentPath === '') {
      const flat = new Map<string, { oid: string; mode: string }>();
      flattenTree(repo, treeOid, '', flat);
      const entries = parseTree(repo.objects.get(treeOid)!.data).map((entry) => ({
        type: entry.mode === '40000' ? 'dir' as const : 'file' as const,
        name: entry.name,
        path: entry.name,
        sha: entry.oid,
        size: entry.mode === '40000' ? 0 : (repo.objects.get(entry.oid)?.data.length ?? 0),
      }));
      sendJson(res, 200, entries);
      return;
    }
    const segments = contentPath.split('/').filter((s) => s !== '');
    let currentTree = treeOid;
    let current: TreeEntry | null = null;
    for (const segment of segments) {
      const entries = parseTree(repo.objects.get(currentTree)?.data ?? Buffer.alloc(0));
      current = entries.find((e) => e.name === segment) ?? null;
      if (!current) { restNotFound(ctx); return; }
      if (current.mode === '40000') currentTree = current.oid;
    }
    if (current === null) { restNotFound(ctx); return; }
    if (current.mode === '40000') {
      const entries = parseTree(repo.objects.get(current.oid)?.data ?? Buffer.alloc(0)).map((entry) => ({
        type: entry.mode === '40000' ? 'dir' as const : 'file' as const,
        name: entry.name,
        path: `${contentPath}/${entry.name}`,
        sha: entry.oid,
        size: entry.mode === '40000' ? 0 : (repo.objects.get(entry.oid)?.data.length ?? 0),
      }));
      sendJson(res, 200, entries);
      return;
    }
    const blob = repo.objects.get(current.oid);
    if (!blob) { restNotFound(ctx); return; }
    const base = contentPath.split('/').pop() ?? contentPath;
    sendJson(res, 200, {
      type: 'file', encoding: 'base64', size: blob.data.length,
      name: base, path: contentPath, content: blob.data.toString('base64'), sha: current.oid,
    });
    return;
  }

  if (method === 'PUT') {
    const message = typeof b.message === 'string' ? b.message : `Update ${contentPath}`;
    const contentB64 = typeof b.content === 'string' ? b.content : '';
    if (contentPath === '') { jsonError(res, 422, 'Path is required'); return; }
    let contentBytes: Buffer;
    try {
      contentBytes = Buffer.from(contentB64.replace(/[\r\n\t ]+/g, ''), 'base64');
    } catch {
      jsonError(res, 400, 'Invalid base64 content');
      return;
    }
    const branch = typeof b.branch === 'string' && b.branch !== '' ? b.branch : repo.defaultBranch;
    const refName = `refs/heads/${branch}`;
    let tip = repo.refs.get(refName) ?? null;
    if (tip === null) {
      // A new branch starts from the default branch's tip (or from nothing).
      tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null;
    }
    const currentBlob = tip !== null ? blobAtPath(repo, tip, contentPath) : null;
    const givenSha = typeof b.sha === 'string' ? b.sha : '';
    if (givenSha !== '') {
      if (currentBlob === null || currentBlob !== givenSha) {
        jsonError(res, 409, 'sha does not match the current blob');
        return;
      }
    }
    const isUpdate = currentBlob !== null;
    const blobOid = storeObject(repo, 'blob', contentBytes);
    const baseTree = tip !== null ? treeOfCommit(repo, tip) : null;
    const newTree = treeWithPath(repo, baseTree, contentPath.split('/'), blobOid);
    const parents = tip !== null ? [tip] : [];
    const commitOid = makeCommit(repo, newTree, parents, message);
    repo.refs.set(refName, commitOid);
    repo.rev += 1;
    const base = contentPath.split('/').pop() ?? contentPath;
    sendJson(res, isUpdate ? 200 : 201, {
      content: { name: base, path: contentPath, sha: blobOid, size: contentBytes.length, encoding: 'base64', type: 'file' },
      commit: { sha: commitOid, message },
    });
    return;
  }

  if (method === 'DELETE') {
    const message = typeof b.message === 'string' ? b.message : `Delete ${contentPath}`;
    const givenSha = typeof b.sha === 'string' ? b.sha : '';
    const branch = typeof b.branch === 'string' && b.branch !== '' ? b.branch : repo.defaultBranch;
    const refName = `refs/heads/${branch}`;
    const tip = repo.refs.get(refName) ?? null;
    if (tip === null) { restNotFound(ctx); return; }
    const currentBlob = blobAtPath(repo, tip, contentPath);
    if (currentBlob === null) { restNotFound(ctx); return; }
    if (givenSha !== '' && givenSha !== currentBlob) {
      jsonError(res, 409, 'sha does not match the current blob');
      return;
    }
    const baseTree = treeOfCommit(repo, tip);
    if (baseTree === null) { restNotFound(ctx); return; }
    const newTree = treeWithoutPath(repo, baseTree, contentPath.split('/'));
    const emptyTree = storeObject(repo, 'tree', buildTree([]));
    const commitOid = makeCommit(repo, newTree ?? emptyTree, [tip], message);
    repo.refs.set(refName, commitOid);
    repo.rev += 1;
    sendJson(res, 200, { commit: { sha: commitOid, message } });
    return;
  }

  restNotFound(ctx);
}

function handleIssues(ctx: RestCtx, repo: Repo, tail: string[]): void {
  const { req, res, query, body } = ctx;
  const method = req.method ?? 'GET';
  const b = (body ?? {}) as Record<string, unknown>;

  // List / create
  if (tail.length === 0) {
    if (method === 'GET') {
      const state = query.get('state') ?? 'open';
      const direction = query.get('direction') ?? 'desc';
      let list = [...repo.issues.values()];
      if (state === 'open') list = list.filter((i) => i.state === 'open');
      else if (state === 'closed') list = list.filter((i) => i.state === 'closed');
      list.sort((a, c) => direction === 'asc' ? a.seq - c.seq : c.seq - a.seq);
      const views = list.map((issue) => issueView(repo, issue));
      const { page, link } = paginate(req, pathOf(req), query, views);
      sendJson(res, 200, page, link === '' ? {} : { link });
      return;
    }
    if (method === 'POST') {
      const title = typeof b.title === 'string' ? b.title : '';
      if (title === '') { jsonError(res, 422, 'Title is required'); return; }
      const labelsRaw = Array.isArray(b.labels) ? b.labels : [];
      const labels: string[] = [];
      for (const entry of labelsRaw) {
        const name = typeof entry === 'string' ? entry : (entry as Record<string, unknown>)?.name;
        if (typeof name !== 'string') continue;
        if (!repo.labels.has(name)) {
          jsonError(res, 422, `Label '${name}' does not exist`);
          return;
        }
        labels.push(name);
      }
      const issue = createIssueRecord(repo, title, typeof b.body === 'string' ? b.body : '', labels);
      sendJson(res, 201, issueView(repo, issue));
      return;
    }
    restNotFound(ctx);
    return;
  }

  const number = Number.parseInt(tail[0]!, 10);
  if (!Number.isInteger(number)) { restNotFound(ctx); return; }
  const issue = repo.issues.get(number);
  if (!issue) { restNotFound(ctx); return; }

  // Comments
  if (tail.length === 2 && tail[1] === 'comments') {
    if (method === 'GET') {
      sendJson(res, 200, issue.comments.map((c) => commentView(repo, issue, c)));
      return;
    }
    if (method === 'POST') {
      const text = typeof b.body === 'string' ? b.body : '';
      if (text === '') { jsonError(res, 422, 'Body is required'); return; }
      const n = nextSeq();
      const comment: IssueComment = {
        id: ++globalIdSeq, body: text, seq: n, createdAt: tsFor(n), updatedAt: tsFor(n),
      };
      issue.comments.push(comment);
      issue.viewCache = null;
      sendJson(res, 201, commentView(repo, issue, comment));
      return;
    }
    restNotFound(ctx);
    return;
  }

  if (tail.length === 1) {
    if (method === 'GET') {
      if (issue.viewCache === null) {
        issue.viewCache = `${JSON.stringify(issueView(repo, issue))}\n`;
      }
      sendJsonText(res, 200, issue.viewCache);
      return;
    }
    if (method === 'PATCH') {
      if (typeof b.title === 'string') issue.title = b.title;
      if (typeof b.body === 'string') issue.body = b.body;
      if (b.state === 'open' || b.state === 'closed') issue.state = b.state;
      if (Array.isArray(b.labels)) {
        const labels: string[] = [];
        for (const entry of b.labels) {
          const name = typeof entry === 'string' ? entry : (entry as Record<string, unknown>)?.name;
          if (typeof name !== 'string') continue;
          if (!repo.labels.has(name)) {
            jsonError(res, 422, `Label '${name}' does not exist`);
            return;
          }
          labels.push(name);
        }
        issue.labels = labels;
      }
      issue.updatedAt = tsFor(nextSeq());
      issue.viewCache = null;
      sendJson(res, 200, issueView(repo, issue));
      return;
    }
    restNotFound(ctx);
    return;
  }

  restNotFound(ctx);
}

function handlePulls(ctx: RestCtx, repo: Repo, tail: string[]): void {
  const { req, res, query, body } = ctx;
  const method = req.method ?? 'GET';
  const b = (body ?? {}) as Record<string, unknown>;

  // List / create
  if (tail.length === 0) {
    if (method === 'GET') {
      const state = query.get('state') ?? 'open';
      let list = [...repo.pulls.values()];
      if (state === 'open') list = list.filter((p) => p.state === 'open');
      else if (state === 'closed') list = list.filter((p) => p.state === 'closed');
      list.sort((a, c) => c.seq - a.seq);
      const views = list.map((pull) => pullView(repo, pull));
      const { page, link } = paginate(req, pathOf(req), query, views);
      sendJson(res, 200, page, link === '' ? {} : { link });
      return;
    }
    if (method === 'POST') {
      const head = typeof b.head === 'string' ? b.head : '';
      const base = typeof b.base === 'string' ? b.base : '';
      const title = typeof b.title === 'string' ? b.title : '';
      if (head === '' || base === '' || title === '') {
        jsonError(res, 422, 'head, base and title are required');
        return;
      }
      const headTip = refCommit(repo, `refs/heads/${head}`);
      const baseTip = refCommit(repo, `refs/heads/${base}`);
      if (headTip === null || baseTip === null) {
        jsonError(res, 422, 'head or base branch does not exist');
        return;
      }
      const duplicate = [...repo.pulls.values()].find(
        (p) => p.state === 'open' && p.headRef === head && p.baseRef === base,
      );
      if (duplicate) {
        jsonError(res, 422, 'A pull request already exists for this head and base');
        return;
      }
      const baseTree = treeOfCommit(repo, baseTip) ?? storeObject(repo, 'tree', buildTree([]));
      const pull = createPullRecord(
        repo, title, typeof b.body === 'string' ? b.body : '', head, base, headTip, baseTip, baseTree,
      );
      sendJson(res, 201, pullView(repo, pull));
      return;
    }
    restNotFound(ctx);
    return;
  }

  const number = Number.parseInt(tail[0]!, 10);
  if (!Number.isInteger(number)) { restNotFound(ctx); return; }
  const pull = repo.pulls.get(number);
  if (!pull) { restNotFound(ctx); return; }

  // Files
  if (tail.length === 2 && tail[1] === 'files') {
    if (method !== 'GET') { restNotFound(ctx); return; }
    const baseTreeOid = treeOfCommit(repo, pull.baseSha);
    const headTreeOid = treeOfCommit(repo, pull.headSha);
    const baseFlat = new Map<string, { oid: string; mode: string }>();
    const headFlat = new Map<string, { oid: string; mode: string }>();
    if (baseTreeOid) flattenTree(repo, baseTreeOid, '', baseFlat);
    if (headTreeOid) flattenTree(repo, headTreeOid, '', headFlat);
    const paths = new Set([...baseFlat.keys(), ...headFlat.keys()]);
    const files: Record<string, unknown>[] = [];
    for (const path of [...paths].sort()) {
      const baseEntry = baseFlat.get(path);
      const headEntry = headFlat.get(path);
      if (baseEntry?.oid === headEntry?.oid) continue;
      let status: string;
      let additions = 0;
      let deletions = 0;
      if (!baseEntry) {
        status = 'added';
        const text = repo.objects.get(headEntry!.oid)?.data.toString('utf8') ?? '';
        additions = text === '' ? 0 : text.split('\n').length;
        if (additions === 0) additions = 1;
      } else if (!headEntry) {
        status = 'removed';
        const text = repo.objects.get(baseEntry.oid)?.data.toString('utf8') ?? '';
        deletions = text === '' ? 0 : text.split('\n').length;
      } else {
        status = 'modified';
        const a = repo.objects.get(baseEntry.oid)?.data.toString('utf8') ?? '';
        const c = repo.objects.get(headEntry.oid)?.data.toString('utf8') ?? '';
        const diff = lineDiff(a, c);
        additions = diff.additions;
        deletions = diff.deletions;
        if (additions === 0 && deletions === 0) { additions = 1; }
      }
      files.push({
        sha: headEntry?.oid ?? baseEntry?.oid ?? '',
        filename: path, status, additions, deletions, changes: additions + deletions,
      });
    }
    sendJson(res, 200, files);
    return;
  }

  // Merge
  if (tail.length === 2 && tail[1] === 'merge') {
    if (method !== 'PUT') { restNotFound(ctx); return; }
    if (pull.merged) {
      jsonError(res, 405, 'Pull request is already merged');
      return;
    }
    if (pull.state === 'closed') {
      jsonError(res, 405, 'Pull request is closed');
      return;
    }
    const merged = squashMerge(repo, pull);
    if (merged === null) {
      jsonError(res, 405, 'Merge conflict: the head and base both changed the same files');
      return;
    }
    sendJson(res, 200, { sha: merged, merged: true, message: 'Pull request successfully merged' });
    return;
  }

  if (tail.length === 1) {
    if (method === 'GET') {
      sendJson(res, 200, pullView(repo, pull));
      return;
    }
    if (method === 'PATCH') {
      if (typeof b.title === 'string') pull.title = b.title;
      if (typeof b.body === 'string') pull.body = b.body;
      if (b.state === 'closed' && pull.state === 'open') pull.state = 'closed';
      pull.updatedAt = tsFor(nextSeq());
      sendJson(res, 200, pullView(repo, pull));
      return;
    }
    restNotFound(ctx);
    return;
  }

  restNotFound(ctx);
}

// ---------------------------------------------------------------- git smart HTTP

interface AdvertisedRef { name: string; oid: string; peeled?: string; symrefTarget?: string; unborn?: boolean }

function allRefs(repo: Repo): AdvertisedRef[] {
  const refs: AdvertisedRef[] = [];
  const defaultTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null;
  if (defaultTip !== null) {
    refs.push({ name: 'HEAD', oid: defaultTip, symrefTarget: `refs/heads/${repo.defaultBranch}` });
  }
  const heads = [...repo.refs.keys()]
    .filter((ref) => ref.startsWith('refs/heads/'))
    .sort();
  for (const ref of heads) refs.push({ name: ref, oid: repo.refs.get(ref)! });
  const tags = [...repo.refs.keys()]
    .filter((ref) => ref.startsWith('refs/tags/'))
    .sort();
  for (const ref of tags) {
    const oid = repo.refs.get(ref)!;
    const object = repo.objects.get(oid);
    let peeled: string | undefined;
    if (object && object.type === 'tag') peeled = parseTag(object.data).object;
    refs.push({ name: ref, oid, peeled });
  }
  return refs;
}

function advertiseV0(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const caps = service === 'git-upload-pack'
    ? `symref=HEAD:refs/heads/${repo.defaultBranch} side-band-64k shallow thin-pack ofs-delta multi_ack agent=${AGENT}`
    : `symref=HEAD:refs/heads/${repo.defaultBranch} report-status side-band-64k delete-refs ofs-delta agent=${AGENT}`;
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const defaultTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null;
  if (defaultTip === null && repo.refs.size === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    const headOid = defaultTip ?? ZERO_OID;
    parts.push(pktLine(`${headOid} HEAD\0${caps}\n`));
    for (const ref of allRefs(repo)) {
      if (ref.name === 'HEAD') continue;
      parts.push(pktLine(`${ref.oid} ${ref.name}\n`));
      if (ref.peeled) parts.push(pktLine(`${ref.peeled} ${ref.name}^{}\n`));
    }
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function advertiseV2(): Buffer {
  return Buffer.concat([
    pktLine('# service=git-upload-pack\n'),
    PKT_FLUSH,
    pktLine('version 2\n'),
    pktLine(`agent=${AGENT}\n`),
    pktLine('ls-refs=unborn\n'),
    pktLine('fetch=shallow\n'),
    pktLine('object-format=sha1\n'),
    PKT_FLUSH,
  ]);
}

/** The v2 advertisement is constant; build it once and reuse the Buffer. */
const AD_V2 = advertiseV2();

/** v0 advertisement for a repo+service, cached while repo.rev matches. */
function advertiseV0Cached(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const cached = repo.adCache.get(service);
  if (cached && cached.rev === repo.rev) return cached.buf;
  const buf = advertiseV0(repo, service);
  repo.adCache.set(service, { rev: repo.rev, buf });
  return buf;
}

function sidebandPackets(pack: Buffer): Buffer[] {
  const parts: Buffer[] = [];
  const maxData = 65515;
  for (let offset = 0; offset < pack.length; offset += maxData) {
    const chunk = pack.subarray(offset, Math.min(offset + maxData, pack.length));
    const payload = Buffer.concat([Buffer.from([1]), chunk]);
    parts.push(pktLine(payload));
  }
  return parts;
}

function handleGit(ctx: RestCtx, owner: string, repoName: string, tail: string[]): void {
  const { req, res, query, body } = ctx;
  const method = req.method ?? 'GET';
  if (!authorized(req)) {
    jsonError(res, 401, 'Bad credentials');
    return;
  }
  const repo = findRepo(owner, repoName);
  if (!repo) {
    jsonError(res, 404, 'Not Found');
    return;
  }
  const rawBody = body as Buffer;

  // GET info/refs
  if (method === 'GET' && tail.length === 2 && tail[0] === 'info' && tail[1] === 'refs') {
    const service = query.get('service') ?? '';
    if (service === 'git-upload-pack') {
      const wantsV2 = (req.headers['git-protocol'] ?? '') === 'version=2';
      if (wantsV2) {
        sendRaw(res, 200, AD_V2, 'application/x-git-upload-pack-advertisement');
      } else {
        sendRaw(res, 200, advertiseV0Cached(repo, 'git-upload-pack'), 'application/x-git-upload-pack-advertisement');
      }
      return;
    }
    if (service === 'git-receive-pack') {
      sendRaw(res, 200, advertiseV0Cached(repo, 'git-receive-pack'), 'application/x-git-receive-pack-advertisement');
      return;
    }
    jsonError(res, 400, 'service is required');
    return;
  }

  // POST git-upload-pack
  if (method === 'POST' && tail.length === 1 && tail[0] === 'git-upload-pack') {
    handleUploadPack(ctx, repo, rawBody);
    return;
  }

  // POST git-receive-pack
  if (method === 'POST' && tail.length === 1 && tail[0] === 'git-receive-pack') {
    handleReceivePack(ctx, repo, rawBody);
    return;
  }

  jsonError(res, 404, 'Not Found');
}

function handleUploadPack(ctx: RestCtx, repo: Repo, rawBody: Buffer): void {
  const { res } = ctx;
  let packets: Pkt[];
  try {
    packets = decodePktLines(rawBody);
  } catch {
    jsonError(res, 400, 'malformed pkt-line stream');
    return;
  }
  const lines: string[] = [];
  for (const packet of packets) {
    if (packet.kind === 'data') lines.push(packet.payload.toString('utf8'));
  }
  if (lines.length === 0) {
    jsonError(res, 400, 'empty upload-pack request');
    return;
  }
  const first = lines[0]!;
  if (first.startsWith('command=')) {
    handleUploadPackV2(ctx, repo, lines);
    return;
  }
  handleUploadPackV0(ctx, repo, lines);
}

function handleUploadPackV2(ctx: RestCtx, repo: Repo, lines: string[]): void {
  const { res } = ctx;
  const command = lines[0]!.slice('command='.length).trim();
  // Split args at the delim marker: lines carry no marker (decode drops control
  // packets), so command args are identified by position: everything up to the
  // first arg keyword after the command line is a command argument.
  const args = lines.slice(1);
  const commandArgs = new Set(['agent', 'object-format']);
  const rest: string[] = [];
  for (const line of args) {
    const trimmed = line.trim();
    const key = trimmed.split('=')[0]!;
    if (commandArgs.has(key) && rest.length === 0) continue;
    rest.push(trimmed);
  }

  if (command === 'ls-refs') {
    const cacheKey = rest.join('\n');
    const cached = repo.lsCache.get(cacheKey);
    if (cached && cached.rev === repo.rev) {
      sendRaw(res, 200, cached.buf, 'application/x-git-upload-pack-result');
      return;
    }
    const peel = rest.includes('peel');
    const symrefs = rest.includes('symrefs');
    const unborn = rest.includes('unborn');
    const prefixes = rest.filter((a) => a.startsWith('ref-prefix ')).map((a) => a.slice('ref-prefix '.length));
    const keep = (name: string): boolean => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
    const parts: Buffer[] = [];
    const defaultTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null;
    if (symrefs && keep('HEAD')) {
      if (defaultTip !== null) {
        parts.push(pktLine(`${defaultTip} HEAD symref-target:refs/heads/${repo.defaultBranch}\n`));
      } else if (unborn) {
        parts.push(pktLine(`unborn HEAD symref-target:refs/heads/${repo.defaultBranch}\n`));
      }
    }
    for (const ref of allRefs(repo)) {
      if (ref.name === 'HEAD') continue;
      if (!keep(ref.name)) continue;
      let line = `${ref.oid} ${ref.name}`;
      if (ref.peeled && peel) line += ` peeled:${ref.peeled}`;
      parts.push(pktLine(`${line}\n`));
    }
    parts.push(PKT_FLUSH);
    const buf = Buffer.concat(parts);
    repo.lsCache.set(cacheKey, { rev: repo.rev, buf });
    sendRaw(res, 200, buf, 'application/x-git-upload-pack-result');
    return;
  }

  if (command === 'fetch') {
    const wants: string[] = [];
    const haves: string[] = [];
    const shallowHeld: string[] = [];
    let depth: number | null = null;
    for (const arg of rest) {
      if (arg.startsWith('want ')) wants.push(arg.slice(5).trim());
      else if (arg.startsWith('have ')) haves.push(arg.slice(5).trim());
      else if (arg.startsWith('shallow ')) shallowHeld.push(arg.slice(8).trim());
      else if (arg.startsWith('deepen ')) depth = Number.parseInt(arg.slice(7).trim(), 10);
    }
    if (depth !== null && (!Number.isFinite(depth) || depth < 1)) depth = null;
    const cacheKey = `${repo.id}|${wants.join(',')}|${haves.join(',')}|${depth ?? ''}|${shallowHeld.join(',')}`;
    const cached = repo.packCache.get(cacheKey);
    let pack: Buffer;
    let shallow: string[];
    let unshallow: string[];
    if (cached && cached.rev === repo.rev) {
      pack = cached.pack;
      shallow = cached.shallow;
      unshallow = cached.unshallow;
    } else {
      const plan = planFetch(repo, wants, haves, depth, shallowHeld);
      pack = writePack(plan.objects);
      shallow = plan.shallow;
      unshallow = plan.unshallow;
      repo.packCache.set(cacheKey, { rev: repo.rev, pack, shallow, unshallow });
      if (repo.packCache.size > 64) {
        const first = repo.packCache.keys().next().value;
        if (first !== undefined) repo.packCache.delete(first);
      }
    }
    const parts: Buffer[] = [];
    if (shallow.length > 0 || unshallow.length > 0) {
      parts.push(pktLine('shallow-info\n'));
      for (const oid of shallow) parts.push(pktLine(`shallow ${oid}\n`));
      for (const oid of unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
      parts.push(PKT_DELIM);
    }
    if (pack.length > 32) {
      parts.push(pktLine('packfile\n'));
      parts.push(...sidebandPackets(pack));
    }
    parts.push(PKT_FLUSH);
    sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
    return;
  }

  jsonError(res, 400, `unknown v2 command ${command}`);
}

function handleUploadPackV0(ctx: RestCtx, repo: Repo, lines: string[]): void {
  const { res } = ctx;
  const wants: string[] = [];
  const haves: string[] = [];
  const shallowHeld: string[] = [];
  let depth: number | null = null;
  for (const line of lines) {
    const trimmed = line.trim();
    if (trimmed.startsWith('want ')) {
      const rest = trimmed.slice(5).trim();
      const oid = rest.split(' ')[0]!;
      wants.push(oid);
    } else if (trimmed.startsWith('have ')) {
      haves.push(trimmed.slice(5).trim());
    } else if (trimmed.startsWith('shallow ')) {
      shallowHeld.push(trimmed.slice(8).trim());
    } else if (trimmed.startsWith('deepen ')) {
      depth = Number.parseInt(trimmed.slice(7).trim(), 10);
    }
  }
  if (depth !== null && (!Number.isFinite(depth) || depth < 1)) depth = null;
  const plan = planFetch(repo, wants, haves, depth, shallowHeld);
  const parts: Buffer[] = [pktLine('NAK\n')];
  for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
  if (plan.objects.length > 0) {
    const pack = writePack(plan.objects);
    parts.push(...sidebandPackets(pack));
  }
  parts.push(PKT_FLUSH);
  sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
}

function handleReceivePack(ctx: RestCtx, repo: Repo, rawBody: Buffer): void {
  const { res } = ctx;
  const sendReport = (sideband: boolean, unpackOk: boolean, unpackDetail: string, results: { ref: string; ok: boolean; reason: string }[]): void => {
    const lines: Buffer[] = [pktLine(`unpack ${unpackOk ? 'ok' : unpackDetail}\n`)];
    for (const result of results) {
      lines.push(pktLine(result.ok ? `ok ${result.ref}\n` : `ng ${result.ref} ${result.reason}\n`));
    }
    const inner = Buffer.concat(lines);
    if (sideband) {
      const parts: Buffer[] = [];
      for (let offset = 0; offset < inner.length; offset += 65515) {
        const chunk = inner.subarray(offset, Math.min(offset + 65515, inner.length));
        parts.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
      }
      parts.push(PKT_FLUSH);
      sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-receive-pack-result');
    } else {
      sendRaw(res, 200, Buffer.concat([...lines, PKT_FLUSH]), 'application/x-git-receive-pack-result');
    }
  };

  // Split the command list (pkt-lines up to the first flush) from the pack bytes.
  let offset = 0;
  const commands: { oldOid: string; newOid: string; ref: string; caps: string }[] = [];
  let sideband = false;
  let packStart = rawBody.length;
  try {
    let first = true;
    while (offset < rawBody.length) {
      if (offset + 4 > rawBody.length) throw new Error('truncated pkt-line');
      const head = rawBody.subarray(offset, offset + 4).toString('ascii');
      if (!/^[0-9a-fA-F]{4}$/.test(head)) throw new Error('invalid pkt-line length');
      const len = parseInt(head, 16);
      if (len === 0) { offset += 4; packStart = offset; break; }
      if (len < 4 || len > 65520 || offset + len > rawBody.length) throw new Error('bad pkt-line');
      const payload = rawBody.subarray(offset + 4, offset + len).toString('utf8');
      offset += len;
      let text = payload;
      let caps = '';
      if (first) {
        const nul = text.indexOf('\0');
        if (nul >= 0) { caps = text.slice(nul + 1); text = text.slice(0, nul); }
        first = false;
      }
      const match = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)\n?$/.exec(text.trim());
      if (!match) throw new Error('bad receive-pack command line');
      commands.push({ oldOid: match[1]!, newOid: match[2]!, ref: match[3]!, caps });
      if (caps.includes('side-band-64k')) sideband = true;
    }
    if (commands.length === 0) throw new Error('no commands');
  } catch {
    sendReport(false, false, 'error', []);
    return;
  }

  // Unpack the pack (when one was sent) before touching any ref.
  const packBytes = rawBody.subarray(packStart);
  let unpackOk = true;
  let unpackDetail = 'ok';
  if (packBytes.length > 0) {
    try {
      const objects = readPack(packBytes, (oid) => repo.objects.get(oid));
      let added = false;
      for (const [oid, object] of objects) {
        if (!repo.objects.has(oid)) { repo.objects.set(oid, object); added = true; }
      }
      if (added) repo.rev += 1;
    } catch (err) {
      unpackOk = false;
      unpackDetail = err instanceof Error ? err.message.replace(/[\r\n]+/g, ' ') : 'unpack failed';
    }
  }

  const results: { ref: string; ok: boolean; reason: string }[] = [];
  if (!unpackOk) {
    for (const command of commands) results.push({ ref: command.ref, ok: false, reason: 'unpack failed' });
    sendReport(sideband, false, unpackDetail, results);
    return;
  }
  for (const command of commands) {
    const { oldOid, newOid, ref } = command;
    if (!ref.startsWith('refs/')) {
      results.push({ ref, ok: false, reason: 'invalid ref' });
      continue;
    }
    const current = repo.refs.get(ref) ?? null;
    if (newOid === ZERO_OID) {
      // Delete.
      if (current === null) {
        results.push({ ref, ok: false, reason: 'remote ref does not exist' });
      } else {
        repo.refs.delete(ref);
        repo.rev += 1;
        results.push({ ref, ok: true, reason: '' });
      }
      continue;
    }
    const object = repo.objects.get(newOid);
    if (!object) {
      results.push({ ref, ok: false, reason: 'object not found' });
      continue;
    }
    if (ref.startsWith('refs/heads/') && object.type !== 'commit') {
      results.push({ ref, ok: false, reason: 'object is not a commit' });
      continue;
    }
    if (oldOid === ZERO_OID) {
      // Create.
      if (current !== null) {
        results.push({ ref, ok: false, reason: 'already exists' });
      } else {
        repo.refs.set(ref, newOid);
        repo.rev += 1;
        results.push({ ref, ok: true, reason: '' });
      }
      continue;
    }
    // Update: fast-forward only.
    if (current === null) {
      results.push({ ref, ok: false, reason: 'remote ref does not exist' });
    } else if (current !== oldOid) {
      results.push({ ref, ok: false, reason: 'non-fast-forward' });
    } else if (!isAncestor(repo, oldOid, newOid)) {
      results.push({ ref, ok: false, reason: 'non-fast-forward' });
    } else {
      repo.refs.set(ref, newOid);
      repo.rev += 1;
      results.push({ ref, ok: true, reason: '' });
    }
  }
  sendReport(sideband, true, 'ok', results);
}

// ---------------------------------------------------------------- GraphQL

type GqlValue =
  | { kind: 'string'; value: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'variable'; name: string }
  | { kind: 'list'; items: GqlValue[] }
  | { kind: 'object'; fields: Record<string, GqlValue> };

interface GqlSelection {
  kind: 'field' | 'fragment' | 'inline';
  name?: string;
  alias?: string;
  typeCondition?: string;
  args?: Record<string, GqlValue>;
  selections?: GqlSelection[];
}

interface GqlOperation {
  kind: 'query' | 'mutation';
  name?: string;
  variables: Record<string, GqlValue | undefined>;
  selections: GqlSelection[];
}

interface GqlDocument {
  operations: GqlOperation[];
  fragments: Map<string, { typeCondition: string; selections: GqlSelection[] }>;
}

class GqlParser {
  private pos = 0;
  private readonly src: string;
  constructor(src: string) { this.src = src; }

  private skipIgnored(): void {
    for (;;) {
      while (this.pos < this.src.length && /[\s,]/.test(this.src[this.pos]!)) this.pos += 1;
      if (this.src[this.pos] === '#') {
        while (this.pos < this.src.length && this.src[this.pos] !== '\n') this.pos += 1;
        continue;
      }
      break;
    }
  }

  private peek(): string {
    this.skipIgnored();
    return this.src[this.pos] ?? '';
  }

  private expect(ch: string): void {
    this.skipIgnored();
    if (this.src[this.pos] !== ch) throw new Error(`expected ${ch} at ${this.pos}`);
    this.pos += 1;
  }

  private readName(): string {
    this.skipIgnored();
    const match = /^[A-Za-z_][A-Za-z0-9_]*/.exec(this.src.slice(this.pos));
    if (!match) throw new Error(`expected name at ${this.pos}`);
    this.pos += match[0].length;
    return match[0];
  }

  private readString(): string {
    this.skipIgnored();
    if (this.src[this.pos] !== '"') throw new Error(`expected string at ${this.pos}`);
    this.pos += 1;
    let out = '';
    while (this.pos < this.src.length) {
      const ch = this.src[this.pos]!;
      if (ch === '"') { this.pos += 1; return out; }
      if (ch === '\\') {
        const esc = this.src[this.pos + 1]!;
        const map: Record<string, string> = { n: '\n', t: '\t', r: '\r', '"': '"', '\\': '\\', '/': '/' };
        out += map[esc] ?? esc;
        this.pos += 2;
        continue;
      }
      out += ch;
      this.pos += 1;
    }
    throw new Error('unterminated string');
  }

  private readNumber(): GqlValue {
    this.skipIgnored();
    const match = /^-?\d+(\.\d+)?([eE][+-]?\d+)?/.exec(this.src.slice(this.pos));
    if (!match) throw new Error(`expected number at ${this.pos}`);
    this.pos += match[0].length;
    const text = match[0];
    return text.includes('.') || /[eE]/.test(text)
      ? { kind: 'float', value: Number(text) }
      : { kind: 'int', value: Number(text) };
  }

  parseValue(): GqlValue {
    this.skipIgnored();
    const ch = this.src[this.pos]!;
    if (ch === '$') {
      this.pos += 1;
      return { kind: 'variable', name: this.readName() };
    }
    if (ch === '"') return { kind: 'string', value: this.readString() };
    if (ch === '[') {
      this.pos += 1;
      const items: GqlValue[] = [];
      while (this.peek() !== ']') items.push(this.parseValue());
      this.expect(']');
      return { kind: 'list', items };
    }
    if (ch === '{') {
      this.pos += 1;
      const fields: Record<string, GqlValue> = {};
      while (this.peek() !== '}') {
        const name = this.readName();
        this.expect(':');
        fields[name] = this.parseValue();
      }
      this.expect('}');
      return { kind: 'object', fields };
    }
    if (ch === '-' || /[0-9]/.test(ch)) return this.readNumber();
    const name = this.readName();
    if (name === 'true') return { kind: 'boolean', value: true };
    if (name === 'false') return { kind: 'boolean', value: false };
    if (name === 'null') return { kind: 'null' };
    return { kind: 'enum', value: name };
  }

  private parseArguments(): Record<string, GqlValue> {
    const args: Record<string, GqlValue> = {};
    if (this.peek() !== '(') return args;
    this.pos += 1;
    while (this.peek() !== ')') {
      const name = this.readName();
      this.expect(':');
      args[name] = this.parseValue();
    }
    this.expect(')');
    return args;
  }

  private skipDirectives(): void {
    while (this.peek() === '@') {
      this.pos += 1;
      this.readName();
      this.parseArguments();
    }
  }

  parseSelectionSet(): GqlSelection[] {
    this.expect('{');
    const selections: GqlSelection[] = [];
    while (this.peek() !== '}') {
      if (this.peek() === '.') {
        // ...Name or ... on Type { ... }
        this.pos += 3; // '...'
        this.skipIgnored();
        if (this.src.slice(this.pos, this.pos + 2) === 'on') {
          this.pos += 2;
          const typeCondition = this.readName();
          this.skipDirectives();
          selections.push({ kind: 'inline', typeCondition, selections: this.parseSelectionSet() });
        } else {
          const name = this.readName();
          this.skipDirectives();
          selections.push({ kind: 'fragment', name });
        }
        continue;
      }
      const first = this.readName();
      let alias: string | undefined;
      let name = first;
      if (this.peek() === ':') {
        this.pos += 1;
        alias = first;
        name = this.readName();
      }
      const args = this.parseArguments();
      this.skipDirectives();
      const sub = this.peek() === '{' ? this.parseSelectionSet() : undefined;
      selections.push({ kind: 'field', name, alias, args, selections: sub });
    }
    this.expect('}');
    return selections;
  }

  parseDocument(): GqlDocument {
    const operations: GqlOperation[] = [];
    const fragments = new Map<string, { typeCondition: string; selections: GqlSelection[] }>();
    while (this.peek() !== '') {
      if (this.peek() === '{') {
        operations.push({ kind: 'query', variables: {}, selections: this.parseSelectionSet() });
        continue;
      }
      const keyword = this.readName();
      if (keyword === 'fragment') {
        const name = this.readName();
        const on = this.readName();
        if (on !== 'on') throw new Error('fragment needs "on"');
        const typeCondition = this.readName();
        this.skipDirectives();
        fragments.set(name, { typeCondition, selections: this.parseSelectionSet() });
        continue;
      }
      if (keyword === 'query' || keyword === 'mutation') {
        let name: string | undefined;
        if (/[A-Za-z_]/.test(this.peek())) name = this.readName();
        const variables: Record<string, GqlValue | undefined> = {};
        if (this.peek() === '(') {
          this.pos += 1;
          while (this.peek() !== ')') {
            if (this.peek() === '$') this.pos += 1;
            const varName = this.readName();
            this.expect(':');
            this.readName(); // type name (possibly with []/!)
            while (this.peek() === '[' || this.peek() === ']' || this.peek() === '!') this.pos += 1;
            if (this.peek() === '=') {
              this.pos += 1;
              variables[varName] = this.parseValue();
            } else {
              variables[varName] = undefined;
            }
          }
          this.expect(')');
        }
        this.skipDirectives();
        operations.push({ kind: keyword, name, variables, selections: this.parseSelectionSet() });
        continue;
      }
      throw new Error(`unexpected document keyword ${keyword}`);
    }
    return { operations, fragments };
  }
}

function evalGqlValue(node: GqlValue, variables: Record<string, unknown>): unknown {
  switch (node.kind) {
    case 'string': case 'int': case 'float': case 'boolean': return node.value;
    case 'null': return null;
    case 'enum': return node.value;
    case 'variable': return variables[node.name];
    case 'list': return node.items.map((item) => evalGqlValue(item, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const [key, value] of Object.entries(node.fields)) out[key] = evalGqlValue(value, variables);
      return out;
    }
  }
}

function evalArgs(args: Record<string, GqlValue> | undefined, variables: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  if (!args) return out;
  for (const [key, value] of Object.entries(args)) out[key] = evalGqlValue(value, variables);
  return out;
}

// ---------------------------------------------------------------- GraphQL values

type GqlObj =
  | { t: 'Query' }
  | { t: 'Mutation' }
  | { t: 'User'; login: string; id: number; name: string; email: string }
  | { t: 'Repository'; repo: Repo }
  | { t: 'Issue'; repo: Repo; issue: Issue }
  | { t: 'PullRequest'; repo: Repo; pull: Pull }
  | { t: 'IssueComment'; repo: Repo; issue: Issue; comment: IssueComment }
  | { t: 'Ref'; name: string; oid: string | null }
  | { t: 'GitObject'; oid: string }
  | { t: 'Label'; label: Label }
  | { t: 'PageInfo'; hasNextPage: boolean; hasPreviousPage: boolean; startCursor: string | null; endCursor: string | null }
  | { t: 'IssueConnection'; nodes: GqlObj[]; pageInfo: GqlObj }
  | { t: 'PullRequestConnection'; nodes: GqlObj[]; pageInfo: GqlObj }
  | { t: 'IssueCommentConnection'; nodes: GqlObj[]; pageInfo: GqlObj }
  | { t: 'ChangedFileConnection'; nodes: GqlObj[]; pageInfo: GqlObj }
  | { t: 'ChangedFile'; path: string }
  | { t: 'CommentEdge'; node: GqlObj; cursor: string }
  | { t: 'CreateIssuePayload'; issue: GqlObj | null }
  | { t: 'CloseIssuePayload'; issue: GqlObj | null }
  | { t: 'CreatePullRequestPayload'; pullRequest: GqlObj | null }
  | { t: 'MergePullRequestPayload'; pullRequest: GqlObj | null }
  | { t: 'AddCommentPayload'; commentEdge: GqlObj | null }
  | { t: '__Type'; name: string; kind: string; fields: string[]; enumValues: string[] }
  | { t: '__Field'; name: string }
  | { t: '__EnumValue'; name: string }
  | { t: '__Schema' };

function gid(type: string, parts: (string | number)[]): string {
  return Buffer.from([type, ...parts.map(String)].join(':'), 'utf8').toString('base64');
}

function decodeGid(id: string): { type: string; parts: string[] } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const parts = text.split(':');
    const type = parts.shift();
    if (!type || parts.length === 0) return null;
    return { type, parts };
  } catch {
    return null;
  }
}

function cursorFor(seqNum: number): string {
  return Buffer.from(`cursor:${seqNum}`, 'utf8').toString('base64');
}

function cursorSeq(cursor: unknown): number | null {
  if (typeof cursor !== 'string' || cursor === '') return null;
  try {
    const text = Buffer.from(cursor, 'base64').toString('utf8');
    const match = /^cursor:(\d+)$/.exec(text);
    return match ? Number(match[1]) : null;
  } catch {
    return null;
  }
}

const ISSUE_FIELDS = ['id', 'number', 'title', 'body', 'state', 'url', 'createdAt', 'updatedAt', 'author', 'labels', 'comments', 'repository', 'databaseId'];
const PR_FIELDS = ['id', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRef', 'baseRef', 'files', 'mergedAt', 'createdAt', 'updatedAt', 'author', 'repository'];
const REPO_FIELDS = ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'description', 'private', 'url', 'createdAt', 'updatedAt', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequest', 'pullRequests'];
const USER_FIELDS = ['login', 'id', 'name', 'email', 'avatarUrl', 'url'];
const TYPE_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', '__type', '__schema'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  User: USER_FIELDS,
  Repository: REPO_FIELDS,
  Issue: ISSUE_FIELDS,
  PullRequest: PR_FIELDS,
  IssueComment: ['id', 'body', 'createdAt', 'updatedAt', 'author'],
  Ref: ['name', 'prefix', 'target'],
  GitObject: ['oid'],
  Label: ['id', 'name', 'color', 'description'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  IssueCommentConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  ChangedFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  ChangedFile: ['path'],
  CommentEdge: ['node', 'cursor'],
  CreateIssuePayload: ['issue', 'clientMutationId'],
  CloseIssuePayload: ['issue', 'clientMutationId'],
  CreatePullRequestPayload: ['pullRequest', 'clientMutationId'],
  MergePullRequestPayload: ['pullRequest', 'clientMutationId'],
  AddCommentPayload: ['commentEdge', 'clientMutationId'],
  __Type: ['name', 'kind', 'description', 'fields', 'enumValues', 'inputFields', 'interfaces', 'possibleTypes', 'ofType', 'specifiedByURL'],
  __Field: ['name', 'description', 'args', 'type'],
  __EnumValue: ['name', 'description', 'isDeprecated', 'deprecationReason'],
  __Schema: ['queryType', 'mutationType', 'types', 'directives'],
};

function issueStateGql(issue: Issue): string {
  return issue.state === 'open' ? 'OPEN' : 'CLOSED';
}

function pullStateGql(pull: Pull): string {
  if (pull.merged) return 'MERGED';
  return pull.state === 'open' ? 'OPEN' : 'CLOSED';
}

function viewerUser(): GqlObj {
  return { t: 'User', login: VIEWER.login, id: VIEWER.id, name: VIEWER.name, email: VIEWER.email };
}

function findRepoByGid(id: string): Repo | null {
  const decoded = decodeGid(id);
  if (!decoded || decoded.type !== 'Repository') return null;
  const dbId = Number(decoded.parts[0]);
  for (const repo of repos.values()) if (repo.id === dbId) return repo;
  return null;
}

function findIssueByGid(id: string): { repo: Repo; issue: Issue } | null {
  const decoded = decodeGid(id);
  if (!decoded || decoded.type !== 'Issue') return null;
  const dbId = Number(decoded.parts[0]);
  const number = Number(decoded.parts[1]);
  for (const repo of repos.values()) {
    if (repo.id !== dbId) continue;
    const issue = repo.issues.get(number);
    return issue ? { repo, issue } : null;
  }
  return null;
}

function findPullByGid(id: string): { repo: Repo; pull: Pull } | null {
  const decoded = decodeGid(id);
  if (!decoded || decoded.type !== 'PullRequest') return null;
  const dbId = Number(decoded.parts[0]);
  const number = Number(decoded.parts[1]);
  for (const repo of repos.values()) {
    if (repo.id !== dbId) continue;
    const pull = repo.pulls.get(number);
    return pull ? { repo, pull } : null;
  }
  return null;
}

interface PageSlice<T> { nodes: T[]; hasNextPage: boolean; endCursor: string | null }

function paginateGql<T extends { seq: number }>(items: T[], args: Record<string, unknown>, orderDesc: boolean): PageSlice<T> {
  let list = [...items].sort((a, b) => orderDesc ? b.seq - a.seq : a.seq - b.seq);
  const afterSeq = cursorSeq(args.after);
  if (afterSeq !== null) {
    list = list.filter((item) => orderDesc ? item.seq < afterSeq : item.seq > afterSeq);
  }
  const first = typeof args.first === 'number' && args.first >= 0 ? Math.trunc(args.first) : list.length;
  const nodes = list.slice(0, first);
  const hasNextPage = list.length > nodes.length;
  const endCursor = nodes.length > 0 ? cursorFor(nodes[nodes.length - 1]!.seq) : null;
  return { nodes, hasNextPage, endCursor };
}

function connectionOf<T extends { seq: number }>(kind: 'IssueConnection' | 'PullRequestConnection' | 'IssueCommentConnection' | 'ChangedFileConnection', wrap: (item: T) => GqlObj, items: T[], args: Record<string, unknown>, orderDesc: boolean): GqlObj {
  const slice = paginateGql(items, args, orderDesc);
  const pageInfo: GqlObj = {
    t: 'PageInfo',
    hasNextPage: slice.hasNextPage,
    hasPreviousPage: false,
    startCursor: slice.nodes.length > 0 ? cursorFor(slice.nodes[0]!.seq) : null,
    endCursor: slice.endCursor,
  };
  const nodes = slice.nodes.map(wrap);
  return { t: kind, nodes, pageInfo } as GqlObj;
}

function issueConnection(repo: Repo, args: Record<string, unknown>): GqlObj {
  let items = [...repo.issues.values()];
  if (Array.isArray(args.states)) {
    const wanted = new Set((args.states as unknown[]).map((s) => String(s)));
    items = items.filter((issue) => wanted.has(issueStateGql(issue)));
  }
  let orderDesc = false;
  const orderBy = args.orderBy as Record<string, unknown> | undefined;
  if (orderBy && typeof orderBy.direction === 'string') {
    orderDesc = orderBy.direction === 'DESC';
  }
  if (orderBy && orderBy.field === 'COMMENTS') {
    items = [...items].sort((a, b) => orderDesc ? b.comments.length - a.comments.length : a.comments.length - b.comments.length);
    // paginateGql re-sorts by seq; handle COMMENTS ordering inline instead.
    const afterSeq = cursorSeq(args.after);
    let list = items;
    if (afterSeq !== null) {
      // Cursor for COMMENTS order is not seq-based; fall back to seq filtering on the same order.
      list = items.filter((item) => orderDesc ? item.seq < afterSeq : item.seq > afterSeq);
    }
    const first = typeof args.first === 'number' && args.first >= 0 ? Math.trunc(args.first) : list.length;
    const nodes = list.slice(0, first);
    const pageInfo: GqlObj = {
      t: 'PageInfo', hasNextPage: list.length > nodes.length, hasPreviousPage: false,
      startCursor: nodes.length > 0 ? cursorFor(nodes[0]!.seq) : null,
      endCursor: nodes.length > 0 ? cursorFor(nodes[nodes.length - 1]!.seq) : null,
    };
    return { t: 'IssueConnection', nodes: nodes.map((issue) => ({ t: 'Issue', repo, issue }) as GqlObj), pageInfo };
  }
  return connectionOf('IssueConnection', (issue) => ({ t: 'Issue', repo, issue }) as GqlObj, items, args, orderDesc);
}

function pullConnection(repo: Repo, args: Record<string, unknown>): GqlObj {
  let items = [...repo.pulls.values()];
  if (Array.isArray(args.states)) {
    const wanted = new Set((args.states as unknown[]).map((s) => String(s)));
    items = items.filter((pull) => wanted.has(pullStateGql(pull)));
  } else {
    items = items.filter((pull) => pull.state === 'open');
  }
  return connectionOf('PullRequestConnection', (pull) => ({ t: 'PullRequest', repo, pull }) as GqlObj, items, args, false);
}

/** Resolve one field of one object. Returns {value} or {error}. */
function resolveField(obj: GqlObj, field: string, args: Record<string, unknown>): { value: unknown } | { error: string } {
  switch (obj.t) {
    case 'Query': {
      if (field === 'viewer') return { value: viewerUser() };
      if (field === 'repository') {
        const owner = args.owner as string;
        const name = args.name as string;
        const repo = typeof owner === 'string' && typeof name === 'string' ? findRepo(owner, name) : undefined;
        return { value: repo ? ({ t: 'Repository', repo } as GqlObj) : null };
      }
      if (field === 'node') {
        const id = args.id as string;
        if (typeof id !== 'string') return { value: null };
        const decoded = decodeGid(id);
        if (!decoded) return { value: null };
        if (decoded.type === 'Repository') {
          const repo = findRepoByGid(id);
          return { value: repo ? ({ t: 'Repository', repo } as GqlObj) : null };
        }
        if (decoded.type === 'Issue') {
          const found = findIssueByGid(id);
          return { value: found ? ({ t: 'Issue', repo: found.repo, issue: found.issue } as GqlObj) : null };
        }
        if (decoded.type === 'PullRequest') {
          const found = findPullByGid(id);
          return { value: found ? ({ t: 'PullRequest', repo: found.repo, pull: found.pull } as GqlObj) : null };
        }
        return { value: null };
      }
      if (field === '__type') {
        const name = args.name as string;
        if (name === 'Issue') return { value: { t: '__Type', name: 'Issue', kind: 'OBJECT', fields: ISSUE_FIELDS, enumValues: [] } as GqlObj };
        if (name === 'PullRequest') return { value: { t: '__Type', name: 'PullRequest', kind: 'OBJECT', fields: PR_FIELDS, enumValues: [] } as GqlObj };
        if (name === 'Repository') return { value: { t: '__Type', name: 'Repository', kind: 'OBJECT', fields: REPO_FIELDS, enumValues: [] } as GqlObj };
        if (name === 'SearchType') return { value: { t: '__Type', name: 'SearchType', kind: 'ENUM', fields: [], enumValues: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'] } as GqlObj };
        return { value: null };
      }
      if (field === '__schema') return { value: { t: '__Schema' } as GqlObj };
      return { error: `Cannot query field "${field}" on type "Query".` };
    }
    case 'Mutation': {
      if (field === 'createIssue') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const repo = typeof input.repositoryId === 'string' ? findRepoByGid(input.repositoryId) : null;
        if (!repo) return { error: 'Could not resolve to a Repository with the given id.' };
        const issue = createIssueRecord(repo, String(input.title ?? ''), typeof input.body === 'string' ? input.body : '', []);
        return { value: { t: 'CreateIssuePayload', issue: { t: 'Issue', repo, issue } as GqlObj } as GqlObj };
      }
      if (field === 'closeIssue') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const found = typeof input.issueId === 'string' ? findIssueByGid(input.issueId) : null;
        if (!found) return { error: 'Could not resolve to an Issue with the given id.' };
        found.issue.state = 'closed';
        found.issue.updatedAt = tsFor(nextSeq());
        found.issue.viewCache = null;
        return { value: { t: 'CloseIssuePayload', issue: { t: 'Issue', repo: found.repo, issue: found.issue } as GqlObj } as GqlObj };
      }
      if (field === 'createPullRequest') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const repo = typeof input.repositoryId === 'string' ? findRepoByGid(input.repositoryId) : null;
        if (!repo) return { error: 'Could not resolve to a Repository with the given id.' };
        const headRef = String(input.headRefName ?? '');
        const baseRef = String(input.baseRefName ?? '');
        const headTip = refCommit(repo, `refs/heads/${headRef}`);
        const baseTip = refCommit(repo, `refs/heads/${baseRef}`);
        if (headTip === null || baseTip === null) return { error: 'head or base branch does not exist.' };
        const duplicate = [...repo.pulls.values()].find((p) => p.state === 'open' && p.headRef === headRef && p.baseRef === baseRef);
        if (duplicate) return { error: 'A pull request already exists for this head and base.' };
        const baseTree = treeOfCommit(repo, baseTip) ?? storeObject(repo, 'tree', buildTree([]));
        const pull = createPullRecord(repo, String(input.title ?? ''), '', headRef, baseRef, headTip, baseTip, baseTree);
        return { value: { t: 'CreatePullRequestPayload', pullRequest: { t: 'PullRequest', repo, pull } as GqlObj } as GqlObj };
      }
      if (field === 'mergePullRequest') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const found = typeof input.pullRequestId === 'string' ? findPullByGid(input.pullRequestId) : null;
        if (!found) return { error: 'Could not resolve to a PullRequest with the given id.' };
        if (found.pull.merged) return { error: 'Pull request is already merged.' };
        const merged = squashMerge(found.repo, found.pull);
        if (merged === null) return { error: 'Merge conflict: the head and base both changed the same files.' };
        return { value: { t: 'MergePullRequestPayload', pullRequest: { t: 'PullRequest', repo: found.repo, pull: found.pull } as GqlObj } as GqlObj };
      }
      if (field === 'addComment') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const found = typeof input.subjectId === 'string' ? findIssueByGid(input.subjectId) : null;
        if (!found) return { error: 'Could not resolve to an Issue with the given id.' };
        const n = nextSeq();
        const comment: IssueComment = {
          id: ++globalIdSeq, body: typeof input.body === 'string' ? input.body : '',
          seq: n, createdAt: tsFor(n), updatedAt: tsFor(n),
        };
        found.issue.comments.push(comment);
        found.issue.viewCache = null;
        const node: GqlObj = { t: 'IssueComment', repo: found.repo, issue: found.issue, comment };
        return { value: { t: 'AddCommentPayload', commentEdge: { t: 'CommentEdge', node, cursor: cursorFor(n) } as GqlObj } as GqlObj };
      }
      return { error: `Cannot query field "${field}" on type "Mutation".` };
    }
    case 'User': {
      if (field === 'login') return { value: obj.login };
      if (field === 'id') return { value: obj.id };
      if (field === 'name') return { value: obj.name };
      if (field === 'email') return { value: obj.email };
      if (field === 'avatarUrl') return { value: '' };
      if (field === 'url') return { value: `https://github.com/${obj.login}` };
      return { error: `Cannot query field "${field}" on type "User".` };
    }
    case 'Repository': {
      const repo = obj.repo;
      if (field === 'id') return { value: gid('Repository', [repo.id]) };
      if (field === 'databaseId') return { value: repo.id };
      if (field === 'name') return { value: repo.name };
      if (field === 'nameWithOwner') return { value: `${repo.owner}/${repo.name}` };
      if (field === 'owner') return { value: viewerUser() };
      if (field === 'description') return { value: repo.description };
      if (field === 'private') return { value: repo.private };
      if (field === 'url') return { value: `https://github.com/${repo.owner}/${repo.name}` };
      if (field === 'createdAt') return { value: repo.createdAt };
      if (field === 'updatedAt') return { value: repo.updatedAt };
      if (field === 'defaultBranchRef') {
        return { value: { t: 'Ref', name: repo.defaultBranch, oid: repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null } as GqlObj };
      }
      if (field === 'viewerPermission') return { value: 'ADMIN' };
      if (field === 'hasIssuesEnabled') return { value: true };
      if (field === 'issue') {
        const number = args.number as number;
        const issue = typeof number === 'number' ? repo.issues.get(number) : undefined;
        return { value: issue ? ({ t: 'Issue', repo, issue } as GqlObj) : null };
      }
      if (field === 'issues') return { value: issueConnection(repo, args) };
      if (field === 'pullRequest') {
        const number = args.number as number;
        const pull = typeof number === 'number' ? repo.pulls.get(number) : undefined;
        return { value: pull ? ({ t: 'PullRequest', repo, pull } as GqlObj) : null };
      }
      if (field === 'pullRequests') return { value: pullConnection(repo, args) };
      return { error: `Cannot query field "${field}" on type "Repository".` };
    }
    case 'Issue': {
      const { repo, issue } = obj;
      if (field === 'id') return { value: gid('Issue', [repo.id, issue.number]) };
      if (field === 'databaseId') return { value: issue.id };
      if (field === 'number') return { value: issue.number };
      if (field === 'title') return { value: issue.title };
      if (field === 'body') return { value: issue.body };
      if (field === 'state') return { value: issueStateGql(issue) };
      if (field === 'url') return { value: `https://github.com/${repo.owner}/${repo.name}/issues/${issue.number}` };
      if (field === 'createdAt') return { value: issue.createdAt };
      if (field === 'updatedAt') return { value: issue.updatedAt };
      if (field === 'author') return { value: viewerUser() };
      if (field === 'repository') return { value: { t: 'Repository', repo } as GqlObj };
      if (field === 'labels') {
        const nodes = issue.labels.map((name) => {
          const label = repo.labels.get(name) ?? { name, color: 'ededed', description: '' };
          return { t: 'Label', label } as GqlObj;
        });
        const pageInfo: GqlObj = { t: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null };
        return { value: { t: 'IssueConnection', nodes, pageInfo } as GqlObj };
      }
      if (field === 'comments') {
        return { value: connectionOf('IssueCommentConnection', (comment) => ({ t: 'IssueComment', repo, issue, comment }) as GqlObj, issue.comments, args, false) };
      }
      return { error: `Cannot query field "${field}" on type "Issue".` };
    }
    case 'PullRequest': {
      const { repo, pull } = obj;
      if (field === 'id') return { value: gid('PullRequest', [repo.id, pull.number]) };
      if (field === 'number') return { value: pull.number };
      if (field === 'title') return { value: pull.title };
      if (field === 'body') return { value: pull.body };
      if (field === 'state') return { value: pullStateGql(pull) };
      if (field === 'merged') return { value: pull.merged };
      if (field === 'mergeable') return { value: prMergeable(repo, pull) };
      if (field === 'headRefName') return { value: pull.headRef };
      if (field === 'baseRefName') return { value: pull.baseRef };
      if (field === 'headRef') return { value: { t: 'Ref', name: pull.headRef, oid: pull.headSha } as GqlObj };
      if (field === 'baseRef') return { value: { t: 'Ref', name: pull.baseRef, oid: pull.baseSha } as GqlObj };
      if (field === 'mergedAt') return { value: pull.merged ? pull.mergedAt : null };
      if (field === 'createdAt') return { value: pull.createdAt };
      if (field === 'updatedAt') return { value: pull.updatedAt };
      if (field === 'author') return { value: viewerUser() };
      if (field === 'repository') return { value: { t: 'Repository', repo } as GqlObj };
      if (field === 'files') {
        const baseTreeOid = treeOfCommit(repo, pull.baseSha);
        const headTreeOid = treeOfCommit(repo, pull.headSha);
        const baseFlat = new Map<string, { oid: string; mode: string }>();
        const headFlat = new Map<string, { oid: string; mode: string }>();
        if (baseTreeOid) flattenTree(repo, baseTreeOid, '', baseFlat);
        if (headTreeOid) flattenTree(repo, headTreeOid, '', headFlat);
        const paths = [...new Set([...baseFlat.keys(), ...headFlat.keys()])]
          .filter((path) => baseFlat.get(path)?.oid !== headFlat.get(path)?.oid)
          .sort();
        const nodes = paths.map((path) => ({ t: 'ChangedFile', path }) as GqlObj);
        const first = typeof args.first === 'number' ? Math.trunc(args.first) : nodes.length;
        const sliced = nodes.slice(0, first);
        const pageInfo: GqlObj = {
          t: 'PageInfo', hasNextPage: nodes.length > sliced.length, hasPreviousPage: false,
          startCursor: null, endCursor: null,
        };
        return { value: { t: 'ChangedFileConnection', nodes: sliced, pageInfo } as GqlObj };
      }
      return { error: `Cannot query field "${field}" on type "PullRequest".` };
    }
    case 'IssueComment': {
      if (field === 'id') return { value: gid('IssueComment', [obj.repo.id, obj.issue.number, obj.comment.id]) };
      if (field === 'body') return { value: obj.comment.body };
      if (field === 'createdAt') return { value: obj.comment.createdAt };
      if (field === 'updatedAt') return { value: obj.comment.updatedAt };
      if (field === 'author') return { value: viewerUser() };
      return { error: `Cannot query field "${field}" on type "IssueComment".` };
    }
    case 'Ref': {
      if (field === 'name') return { value: obj.name };
      if (field === 'prefix') return { value: 'refs/heads/' };
      if (field === 'target') return { value: obj.oid === null ? null : ({ t: 'GitObject', oid: obj.oid } as GqlObj) };
      return { error: `Cannot query field "${field}" on type "Ref".` };
    }
    case 'GitObject': {
      if (field === 'oid') return { value: obj.oid };
      return { error: `Cannot query field "${field}" on type "GitObject".` };
    }
    case 'Label': {
      if (field === 'id') return { value: gid('Label', [obj.label.name]) };
      if (field === 'name') return { value: obj.label.name };
      if (field === 'color') return { value: obj.label.color };
      if (field === 'description') return { value: obj.label.description };
      return { error: `Cannot query field "${field}" on type "Label".` };
    }
    case 'PageInfo': {
      if (field === 'hasNextPage') return { value: obj.hasNextPage };
      if (field === 'hasPreviousPage') return { value: obj.hasPreviousPage };
      if (field === 'startCursor') return { value: obj.startCursor };
      if (field === 'endCursor') return { value: obj.endCursor };
      return { error: `Cannot query field "${field}" on type "PageInfo".` };
    }
    case 'IssueConnection': case 'PullRequestConnection': case 'IssueCommentConnection': case 'ChangedFileConnection': {
      if (field === 'nodes') return { value: obj.nodes };
      if (field === 'edges') {
        return { value: obj.nodes.map((node) => ({ t: 'CommentEdge', node, cursor: '' }) as GqlObj) };
      }
      if (field === 'pageInfo') return { value: obj.pageInfo };
      if (field === 'totalCount') return { value: obj.nodes.length };
      return { error: `Cannot query field "${field}" on type "${obj.t}".` };
    }
    case 'ChangedFile': {
      if (field === 'path') return { value: obj.path };
      return { error: `Cannot query field "${field}" on type "ChangedFile".` };
    }
    case 'CommentEdge': {
      if (field === 'node') return { value: obj.node };
      if (field === 'cursor') return { value: obj.cursor };
      return { error: `Cannot query field "${field}" on type "CommentEdge".` };
    }
    case 'CreateIssuePayload': {
      if (field === 'issue') return { value: obj.issue };
      if (field === 'clientMutationId') return { value: null };
      return { error: `Cannot query field "${field}" on type "CreateIssuePayload".` };
    }
    case 'CloseIssuePayload': {
      if (field === 'issue') return { value: obj.issue };
      if (field === 'clientMutationId') return { value: null };
      return { error: `Cannot query field "${field}" on type "CloseIssuePayload".` };
    }
    case 'CreatePullRequestPayload': {
      if (field === 'pullRequest') return { value: obj.pullRequest };
      if (field === 'clientMutationId') return { value: null };
      return { error: `Cannot query field "${field}" on type "CreatePullRequestPayload".` };
    }
    case 'MergePullRequestPayload': {
      if (field === 'pullRequest') return { value: obj.pullRequest };
      if (field === 'clientMutationId') return { value: null };
      return { error: `Cannot query field "${field}" on type "MergePullRequestPayload".` };
    }
    case 'AddCommentPayload': {
      if (field === 'commentEdge') return { value: obj.commentEdge };
      if (field === 'clientMutationId') return { value: null };
      return { error: `Cannot query field "${field}" on type "AddCommentPayload".` };
    }
    case '__Type': {
      if (field === 'name') return { value: obj.name };
      if (field === 'kind') return { value: obj.kind };
      if (field === 'description') return { value: null };
      if (field === 'fields') return { value: obj.fields.map((name) => ({ t: '__Field', name }) as GqlObj) };
      if (field === 'enumValues') return { value: obj.enumValues.map((name) => ({ t: '__EnumValue', name }) as GqlObj) };
      if (field === 'inputFields') return { value: [] };
      if (field === 'interfaces') return { value: [] };
      if (field === 'possibleTypes') return { value: [] };
      if (field === 'ofType') return { value: null };
      if (field === 'specifiedByURL') return { value: null };
      return { error: `Cannot query field "${field}" on type "__Type".` };
    }
    case '__Field': {
      if (field === 'name') return { value: obj.name };
      if (field === 'description') return { value: null };
      if (field === 'args') return { value: [] };
      if (field === 'type') return { value: null };
      return { error: `Cannot query field "${field}" on type "__Field".` };
    }
    case '__EnumValue': {
      if (field === 'name') return { value: obj.name };
      if (field === 'description') return { value: null };
      if (field === 'isDeprecated') return { value: false };
      if (field === 'deprecationReason') return { value: null };
      return { error: `Cannot query field "${field}" on type "__EnumValue".` };
    }
    case '__Schema': {
      if (field === 'queryType') return { value: { t: '__Type', name: 'Query', kind: 'OBJECT', fields: TYPE_FIELDS.Query!, enumValues: [] } as GqlObj };
      if (field === 'mutationType') return { value: { t: '__Type', name: 'Mutation', kind: 'OBJECT', fields: TYPE_FIELDS.Mutation!, enumValues: [] } as GqlObj };
      if (field === 'types') return { value: [] };
      if (field === 'directives') return { value: [] };
      return { error: `Cannot query field "${field}" on type "__Schema".` };
    }
  }
}

function isGqlObj(value: unknown): value is GqlObj {
  return typeof value === 'object' && value !== null && typeof (value as { t?: unknown }).t === 'string';
}

interface ExecState {
  errors: { message: string }[];
  doc: GqlDocument;
  variables: Record<string, unknown>;
}

/** Execute a selection set against an object, returning its JSON shape. */
function execSelections(state: ExecState, obj: GqlObj, selections: GqlSelection[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const selection of selections) {
    if (selection.kind === 'fragment') {
      const fragment = state.doc.fragments.get(selection.name!);
      if (!fragment) {
        state.errors.push({ message: `Unknown fragment "${selection.name}".` });
        continue;
      }
      if (fragment.typeCondition !== obj.t && fragment.typeCondition !== 'Node') continue;
      Object.assign(out, execSelections(state, obj, fragment.selections));
      continue;
    }
    if (selection.kind === 'inline') {
      if (selection.typeCondition && selection.typeCondition !== obj.t && selection.typeCondition !== 'Node') continue;
      Object.assign(out, execSelections(state, obj, selection.selections ?? []));
      continue;
    }
    const fieldName = selection.name!;
    const key = selection.alias ?? fieldName;
    if (fieldName === '__typename') {
      out[key] = obj.t;
      continue;
    }
    const allowed = TYPE_FIELDS[obj.t];
    if (!allowed?.includes(fieldName)) {
      state.errors.push({ message: `Cannot query field "${fieldName}" on type "${obj.t}".` });
      continue;
    }
    const args = evalArgs(selection.args, state.variables);
    const resolved = resolveField(obj, fieldName, args);
    if ('error' in resolved) {
      state.errors.push({ message: resolved.error });
      continue;
    }
    out[key] = execValue(state, resolved.value, selection.selections);
  }
  return out;
}

function execValue(state: ExecState, value: unknown, selections: GqlSelection[] | undefined): unknown {
  if (value === null || value === undefined) return null;
  if (Array.isArray(value)) return value.map((item) => execValue(state, item, selections));
  if (isGqlObj(value)) {
    if (!selections || selections.length === 0) return {};
    return execSelections(state, value, selections);
  }
  return value;
}

function executeOperation(doc: GqlDocument, operation: GqlOperation, variables: Record<string, unknown>): { data: unknown; errors?: { message: string }[] } {
  const state: ExecState = { errors: [], doc, variables };
  // Apply variable defaults.
  for (const [name, defaultValue] of Object.entries(operation.variables)) {
    if (state.variables[name] === undefined && defaultValue !== undefined) {
      state.variables[name] = evalGqlValue(defaultValue, state.variables);
    }
  }
  const root: GqlObj = operation.kind === 'mutation' ? { t: 'Mutation' } : { t: 'Query' };
  const data = execSelections(state, root, operation.selections);
  if (state.errors.length > 0) {
    return { data: null, errors: state.errors };
  }
  return { data };
}

function executeGraphQL(query: string, variables: Record<string, unknown>): { data: unknown; errors?: { message: string }[] } {
  let doc: GqlDocument;
  try {
    doc = new GqlParser(query).parseDocument();
  } catch (err) {
    return { data: null, errors: [{ message: err instanceof Error ? err.message : 'GraphQL syntax error' }] };
  }
  if (doc.operations.length === 0) {
    return { data: null, errors: [{ message: 'No operation in document.' }] };
  }
  return executeOperation(doc, doc.operations[0]!, variables);
}

// ---------------------------------------------------------------- MCP

const MCP_SERVER_INFO = { name: 'github-core-clone-01', version: '1.0.0' };
const MCP_SUPPORTED_VERSIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];

const MCP_TOOLS: Record<string, unknown>[] = [
  {
    name: 'create_repo',
    description: 'Create a repository owned by the viewer.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The repository name.' },
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
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
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
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
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
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Open a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        body: { type: 'string', description: 'The pull request body.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request with a squash merge.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'integer', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

const MCP_TOOL_REQUIRED: Record<string, string[]> = {
  create_repo: ['name'],
  get_repo: ['owner', 'repo'],
  create_issue: ['owner', 'repo', 'title'],
  list_issues: ['owner', 'repo'],
  create_pull_request: ['owner', 'repo', 'title', 'head', 'base'],
  merge_pull_request: ['owner', 'repo', 'pull_number'],
};

interface McpToolOutcome {
  isError: boolean;
  value: Record<string, unknown>;
}

function mcpToolCall(name: string, args: Record<string, unknown>): McpToolOutcome {
  const err = (message: string): McpToolOutcome => ({ isError: true, value: { error: message } });
  if (name === 'create_repo') {
    const repoName = typeof args.name === 'string' ? args.name.trim() : '';
    if (repoName === '') return err('name is required');
    if (repos.has(repoKey(VIEWER.login, repoName))) return err('Repository already exists');
    const repo = createRepoRecord(repoName, typeof args.description === 'string' ? args.description : '', args.private === true);
    const view = repoView(repo) as Record<string, unknown>;
    view.full_name = `${repo.owner}/${repo.name}`;
    return { isError: false, value: view };
  }
  const owner = typeof args.owner === 'string' ? args.owner : '';
  const repoName = typeof args.repo === 'string' ? args.repo : '';
  const repo = owner !== '' && repoName !== '' ? findRepo(owner, repoName) : undefined;
  if (!repo) return err(`Repository ${owner}/${repoName} not found`);
  if (name === 'get_repo') {
    const view = repoView(repo) as Record<string, unknown>;
    view.full_name = `${repo.owner}/${repo.name}`;
    return { isError: false, value: view };
  }
  if (name === 'create_issue') {
    const title = typeof args.title === 'string' ? args.title : '';
    const issue = createIssueRecord(repo, title, typeof args.body === 'string' ? args.body : '', []);
    return { isError: false, value: issueView(repo, issue) as Record<string, unknown> };
  }
  if (name === 'list_issues') {
    const state = typeof args.state === 'string' ? args.state : 'open';
    let list = [...repo.issues.values()];
    if (state === 'open') list = list.filter((i) => i.state === 'open');
    else if (state === 'closed') list = list.filter((i) => i.state === 'closed');
    list.sort((a, b) => b.seq - a.seq);
    return { isError: false, value: { issues: list.map((issue) => issueView(repo, issue)), total_count: list.length } };
  }
  if (name === 'create_pull_request') {
    const head = typeof args.head === 'string' ? args.head : '';
    const base = typeof args.base === 'string' ? args.base : '';
    const title = typeof args.title === 'string' ? args.title : '';
    const headTip = refCommit(repo, `refs/heads/${head}`);
    const baseTip = refCommit(repo, `refs/heads/${base}`);
    if (headTip === null || baseTip === null) return err('head or base branch does not exist');
    const duplicate = [...repo.pulls.values()].find((p) => p.state === 'open' && p.headRef === head && p.baseRef === base);
    if (duplicate) return err('A pull request already exists for this head and base');
    const baseTree = treeOfCommit(repo, baseTip) ?? storeObject(repo, 'tree', buildTree([]));
    const pull = createPullRecord(repo, title, typeof args.body === 'string' ? args.body : '', head, base, headTip, baseTip, baseTree);
    return { isError: false, value: pullView(repo, pull) as Record<string, unknown> };
  }
  if (name === 'merge_pull_request') {
    const number = typeof args.pull_number === 'number' ? args.pull_number : Number(args.pull_number);
    const pull = repo.pulls.get(number);
    if (!pull) return err(`Pull request #${number} not found`);
    if (pull.merged) return err('Pull request is already merged');
    if (pull.state !== 'open') return err('Pull request is closed');
    const merged = squashMerge(repo, pull);
    if (merged === null) return err('Merge conflict: the head and base both changed the same files');
    return { isError: false, value: { number: pull.number, merged: true, state: 'closed', sha: merged } };
  }
  return err(`Unknown tool: ${name}`);
}

function handleMcp(ctx: RestCtx, rawBody: Buffer): void {
  const { req, res } = ctx;
  if (!authorized(req)) {
    jsonError(res, 401, 'Bad credentials');
    return;
  }
  const text = rawBody.toString('utf8');
  let parsed: unknown;
  try {
    parsed = JSON.parse(text);
  } catch {
    const idMatch = /"id"\s*:\s*("[^"]*"|\d+)/.exec(text);
    let id: unknown = null;
    if (idMatch) {
      const raw = idMatch[1]!;
      id = raw.startsWith('"') ? raw.slice(1, -1) : Number(raw);
    }
    sendJson(res, 400, { jsonrpc: '2.0', id, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (typeof parsed !== 'object' || parsed === null || Array.isArray(parsed)) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32600, message: 'Invalid Request' } });
    return;
  }
  const body = parsed as Record<string, unknown>;
  const method = typeof body.method === 'string' ? body.method : '';
  const id = body.id as string | number | undefined;
  // Notifications carry no id: acknowledge with an empty 202.
  if (id === undefined) {
    sendNoBody(res, 202);
    return;
  }
  const ok = (result: unknown): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, result });
  };
  const fail = (code: number, message: string): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, error: { code, message } });
  };
  const params = (body.params ?? {}) as Record<string, unknown>;
  if (method === 'server/discover') {
    ok({
      supportedVersions: MCP_SUPPORTED_VERSIONS,
      capabilities: { tools: {} },
      serverInfo: MCP_SERVER_INFO,
      _meta: { 'io.modelcontextprotocol/serverInfo': MCP_SERVER_INFO },
    });
    return;
  }
  if (method === 'initialize') {
    const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25';
    ok({
      protocolVersion: requested,
      capabilities: { tools: {} },
      serverInfo: MCP_SERVER_INFO,
    });
    return;
  }
  if (method === 'ping') {
    ok({});
    return;
  }
  if (method === 'tools/list') {
    ok({ tools: MCP_TOOLS });
    return;
  }
  if (method === 'tools/call') {
    const toolName = typeof params.name === 'string' ? params.name : '';
    const args = (params.arguments ?? {}) as Record<string, unknown>;
    if (!MCP_TOOL_REQUIRED[toolName]) {
      fail(-32602, `Unknown tool: ${toolName}`);
      return;
    }
    const missing = MCP_TOOL_REQUIRED[toolName]!.filter((key) => args[key] === undefined || args[key] === '');
    if (missing.length > 0) {
      fail(-32602, `Missing required arguments: ${missing.join(', ')}`);
      return;
    }
    const outcome = mcpToolCall(toolName, args);
    ok({
      content: [{ type: 'text', text: JSON.stringify(outcome.value) }],
      structuredContent: outcome.value,
      isError: outcome.isError,
    });
    return;
  }
  fail(-32601, `Method not found: ${method}`);
}

// ---------------------------------------------------------------- GraphQL HTTP

function handleGraphQL(ctx: RestCtx, rawBody: Buffer): void {
  const { req, res } = ctx;
  if (!authorized(req)) {
    jsonError(res, 401, 'Bad credentials');
    return;
  }
  const parsed = parseJsonBody(rawBody);
  if (!parsed.ok) {
    sendJson(res, 400, { errors: [{ message: 'Invalid JSON in request body' }] });
    return;
  }
  const value = parsed.value;
  if (Array.isArray(value)) {
    const results = value.map((entry) => {
      if (typeof entry !== 'object' || entry === null) return { data: null, errors: [{ message: 'Invalid operation' }] };
      const record = entry as Record<string, unknown>;
      const query = typeof record.query === 'string' ? record.query : '';
      const variables = (record.variables ?? {}) as Record<string, unknown>;
      return executeGraphQL(query, variables);
    });
    sendJson(res, 200, results);
    return;
  }
  if (typeof value !== 'object' || value === null) {
    sendJson(res, 400, { errors: [{ message: 'Invalid operation' }] });
    return;
  }
  const record = value as Record<string, unknown>;
  const query = typeof record.query === 'string' ? record.query : '';
  const variables = (record.variables ?? {}) as Record<string, unknown>;
  sendJson(res, 200, executeGraphQL(query, variables));
}

// ---------------------------------------------------------------- the server

/** Build the server. It binds nothing until the caller listens; the entry listens on an ephemeral port. */
export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void handleRequest(req, res).catch(() => {
      try {
        jsonError(res, 500, 'Internal Server Error');
      } catch {
        // The peer went away; nothing to write to.
      }
    });
  });
}

async function handleRequest(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const method = req.method ?? 'GET';
  // Parse the URL once; the old pathOf/queryOf helpers each parsed it anew.
  let url: URL;
  try {
    url = new URL(req.url ?? '/', 'http://entry');
  } catch {
    url = new URL('http://entry/');
  }
  const path = url.pathname;
  const query = url.searchParams;
  const segments = splitPath(path);

  // The env's boot check calls this twice: 200 {"ok":true}.
  if (method === 'GET' && path === '/healthz') {
    sendJson(res, 200, { ok: true });
    return;
  }

  // Git smart HTTP: /{owner}/{repo}.git/...
  if (segments.length >= 2 && segments[1]!.endsWith('.git')) {
    const owner = segments[0]!;
    const repoName = segments[1]!.slice(0, -4);
    const rawBody = method === 'POST' ? await readBody(req) : Buffer.alloc(0);
    handleGit({ req, res, query, body: rawBody, segments }, owner, repoName, segments.slice(2));
    return;
  }

  // GraphQL v4.
  if (segments.length === 2 && segments[0] === 'api' && segments[1] === 'graphql') {
    if (method !== 'POST') {
      jsonError(res, 404, 'Not Found');
      return;
    }
    const rawBody = await readBody(req);
    handleGraphQL({ req, res, query, body: rawBody, segments }, rawBody);
    return;
  }

  // MCP over streamable HTTP.
  if (segments.length === 1 && segments[0] === 'mcp') {
    if (method !== 'POST') {
      jsonError(res, 404, 'Not Found');
      return;
    }
    const rawBody = await readBody(req);
    handleMcp({ req, res, query, body: rawBody, segments }, rawBody);
    return;
  }

  // REST v3.
  if (segments.length >= 2 && segments[0] === 'api' && segments[1] === 'v3') {
    let body: unknown = {};
    if (method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE') {
      const rawBody = await readBody(req);
      const parsed = parseJsonBody(rawBody);
      if (!parsed.ok) {
        jsonError(res, 400, 'Invalid JSON in request body');
        return;
      }
      body = parsed.value;
    }
    handleRest({ req, res, query, body, segments });
    return;
  }

  // Everything else: GitHub's 404 body.
  sendJson(res, 404, { message: 'Not Found' });
}

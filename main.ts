// main.ts is mend, the CLI SPEC.md specifies (MIT). It does all of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write, plus line matching at
// three tiers (section 5), unified diffs (section 6), SEARCH/REPLACE blocks (section 7) and V4A patches
// (section 8). Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to
// runner.ts (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file's lines, its own line break, and whether it ends with one (SPEC.md section 3). */
interface FileState {
  lines: string[];
  br: string;
  final: boolean;
}

function splitFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const final = text.endsWith(br);
  const parts = text.split(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}

function joinFile(f: FileState): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.final ? f.br : '');
}

const trimEndWS = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWS = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWS = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
};

function eqAt(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trimEndWS(a) === trimEndWS(b);
  return trimWS(a) === trimWS(b);
}

function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  for (let i = 0; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!eqAt(lines[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0, 1 or 2) at which O occurs in lines, with its positions; null when none. */
function findTier(lines: string[], o: string[], strict: boolean): { tier: number; pos: number[] } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    const pos = occurrences(lines, o, t);
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

/** One line of N: `text`, and the O index it mirrors when it is a context line, else -1. */
interface NLine {
  text: string;
  ctx: number;
}

/** Build the lines that replace O at `at`: context lines are the file's own matched lines; at tier 2 every
 * other line is re-indented from O's first line's leading whitespace to the file's (SPEC.md section 5). */
function buildReplacement(file: FileState, at: number, tier: number, o: string[], n: NLine[]): string[] {
  const out: string[] = [];
  const f = leadWS(file.lines[at] ?? '');
  const p = leadWS(o[0] ?? '');
  for (const nl of n) {
    if (nl.ctx >= 0) {
      out.push(file.lines[at + nl.ctx]!);
      continue;
    }
    const t = nl.text;
    if (tier === 2 && t !== '' && t.trim() !== '' && t.startsWith(p)) out.push(f + t.slice(p.length));
    else out.push(t);
  }
  return out;
}

/** First line at or after `from` equal to `anchor` at the first tier where one is; -1 when none. */
function findAnchor(lines: string[], from: number, anchor: string, strict: boolean): number {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    for (let i = from; i < lines.length; i++) {
      if (eqAt(lines[i]!, anchor, t)) return i;
    }
  }
  return -1;
}

/** First occurrence of O at or after `from`, at the first tier with one; for an end-of-file chunk only an
 * occurrence ending at the file's last line counts. Null when none. */
function findFirstAtOrAfter(
  lines: string[],
  from: number,
  o: string[],
  strict: boolean,
  eof: boolean,
): { at: number; tier: number } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    for (let i = from; i + o.length <= lines.length; i++) {
      if (eof && i + o.length !== lines.length) continue;
      let ok = true;
      for (let j = 0; j < o.length; j++) {
        if (!eqAt(lines[i + j]!, o[j]!, t)) {
          ok = false;
          break;
        }
      }
      if (ok) return { at: i, tier: t };
    }
  }
  return null;
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: [string, string][] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ------------------------------------------------------------------ */
/* Unified diffs (SPEC.md section 6)                                  */
/* ------------------------------------------------------------------ */

interface Hunk {
  a: number;
  c: number;
  o: string[];
  n: NLine[];
  /** a `\` line follows the hunk's last context or `+` line */
  noNl: boolean;
  /** a `\` line follows the hunk's last `+` line */
  plusNoNl: boolean;
}

interface USection {
  oldP: string | null;
  newP: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  diffOld: string | null;
  diffNew: string | null;
  isCreate: boolean;
  isDelete: boolean;
  hasPair: boolean;
  hunks: Hunk[];
}

/** The path after `--- ` / `+++ `: text after four characters, up to the first tab, trimmed, leading a/ or b/ off. */
function diffPath(l: string): string {
  let p = l.slice(4).split('\t')[0].trim();
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

const DIFF_GIT_RE = /^diff --git a\/(\S+) b\/(\S+)$/;
const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(.*)$/;

function parseHunkBody(lines: string[], i: number): { hunk: Hunk; next: number } {
  const m = HUNK_RE.exec(lines[i]!);
  const a = Number(m![1]);
  const c = Number(m![3]);
  const body: string[] = [];
  let j = i + 1;
  while (j < lines.length) {
    const l = lines[j]!;
    if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
    if (l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+' || l[0] === '\\') {
      body.push(l);
      j++;
    } else break;
  }
  while (body.length > 0 && body[body.length - 1] === '') body.pop();
  const o: string[] = [];
  const n: NLine[] = [];
  let lastCtxOrPlus = -1;
  let lastPlus = -1;
  for (let b = 0; b < body.length; b++) {
    const l = body[b]!;
    if (l === '') {
      o.push('');
      n.push({ text: '', ctx: o.length - 1 });
      lastCtxOrPlus = b;
    } else if (l[0] === ' ') {
      const t = l.slice(1);
      o.push(t);
      n.push({ text: t, ctx: o.length - 1 });
      lastCtxOrPlus = b;
    } else if (l[0] === '-') {
      o.push(l.slice(1));
    } else if (l[0] === '+') {
      n.push({ text: l.slice(1), ctx: -1 });
      lastCtxOrPlus = b;
      lastPlus = b;
    }
  }
  const noNl = lastCtxOrPlus >= 0 && body[lastCtxOrPlus + 1] !== undefined && body[lastCtxOrPlus + 1]![0] === '\\';
  const plusNoNl = lastPlus >= 0 && body[lastPlus + 1] !== undefined && body[lastPlus + 1]![0] === '\\';
  return { hunk: { a, c, o, n, noNl, plusNoNl }, next: j };
}

function parseUnified(lines: string[]): USection[] {
  const sections: USection[] = [];
  let cur: USection | null = null;
  let inHeader = false;
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    const ln = i + 1;
    if (l.startsWith('diff --git ')) {
      const m = DIFF_GIT_RE.exec(l);
      if (!m) throw new Exit2(`error: parse ${ln}`);
      cur = {
        oldP: null, newP: null, renameFrom: null, renameTo: null,
        diffOld: m[1]!, diffNew: m[2]!, isCreate: false, isDelete: false, hasPair: false, hunks: [],
      };
      sections.push(cur);
      inHeader = true;
      i++;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && inHeader && !cur.hasPair) {
        cur.oldP = diffPath(l);
        cur.newP = diffPath(lines[i + 1]!);
        cur.hasPair = true;
        i += 2;
        continue;
      }
      cur = {
        oldP: diffPath(l), newP: diffPath(lines[i + 1]!), renameFrom: null, renameTo: null,
        diffOld: null, diffNew: null, isCreate: false, isDelete: false, hasPair: true, hunks: [],
      };
      sections.push(cur);
      inHeader = true;
      i += 2;
      continue;
    }
    if (l.startsWith('--- ') && cur !== null && inHeader) throw new Exit2(`error: parse ${ln + 1}`);
    if (l.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${ln}`);
      if (!HUNK_RE.test(l)) throw new Exit2(`error: parse ${ln}`);
      const r = parseHunkBody(lines, i);
      cur.hunks.push(r.hunk);
      inHeader = false;
      i = r.next;
      continue;
    }
    if (cur !== null && inHeader) {
      if (l.startsWith('rename from ')) cur.renameFrom = l.slice('rename from '.length).trim();
      else if (l.startsWith('rename to ')) cur.renameTo = l.slice('rename to '.length).trim();
      else if (l.startsWith('new file mode')) cur.isCreate = true;
      else if (l.startsWith('deleted file mode')) cur.isDelete = true;
      i++;
      continue;
    }
    i++;
  }
  return sections;
}

/** Apply a section's hunks in order to a file's lines; d tracks the running length delta. */
function applyHunks(file: FileState, hunks: Hunk[], strict: boolean, failPath: string): FileState {
  const cur: FileState = { lines: [...file.lines], br: file.br, final: file.final };
  let d = 0;
  for (const h of hunks) {
    if (h.o.length === 0) {
      let pos = h.a + d;
      if (pos < 0) pos = 0;
      if (pos > cur.lines.length) pos = cur.lines.length;
      const atEnd = pos === cur.lines.length;
      cur.lines.splice(pos, 0, ...h.n.map((x) => x.text));
      if (atEnd) cur.final = !h.noNl;
      d += h.n.length;
      continue;
    }
    const found = findTier(cur.lines, h.o, strict);
    if (!found) throw new Fail('no-match', failPath);
    const target = h.a - 1 + d;
    let best = found.pos[0]!;
    let bestDist = Math.abs(best - target);
    for (const p of found.pos) {
      const dist = Math.abs(p - target);
      if (dist < bestDist) {
        best = p;
        bestDist = dist;
      }
    }
    const at = best;
    const touchesEnd = at + h.o.length === cur.lines.length;
    const rep = buildReplacement(cur, at, found.tier, h.o, h.n);
    cur.lines.splice(at, h.o.length, ...rep);
    if (touchesEnd) cur.final = !h.noNl;
    d += h.n.length - h.o.length;
  }
  return cur;
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections = parseUnified(lines);
  return sections.map((s) => {
    const oldRaw = s.oldP ?? s.renameFrom ?? s.diffOld;
    const newRaw = s.newP ?? s.renameTo ?? s.diffNew;
    const oldP = oldRaw === '/dev/null' ? null : oldRaw;
    const newP = newRaw === '/dev/null' ? null : newRaw;
    const kind = oldP === null || s.isCreate ? 'create' : newP === null || s.isDelete ? 'delete' : oldP !== newP ? 'move' : 'change';
    return (tree: Tree) => {
      if (kind === 'create') {
        const p = newP!;
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        const plus: string[] = [];
        let lastPlusNoNl = false;
        for (const h of s.hunks) {
          for (const nl of h.n) if (nl.ctx < 0) plus.push(nl.text);
          if (h.n.some((nl) => nl.ctx < 0)) lastPlusNoNl = h.plusNoNl;
        }
        tree.now.set(p, plus.length === 0 ? '' : plus.join('\n') + (lastPlusNoNl ? '' : '\n'));
        return;
      }
      if (kind === 'delete') {
        const p = oldP!;
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
        return;
      }
      if (kind === 'move') {
        const o = oldP!;
        const n = newP!;
        if (!safe(o)) throw new Fail('unsafe', o);
        if (!safe(n)) throw new Fail('unsafe', n);
        const before = tree.get(o);
        if (before === null) throw new Fail('missing', o);
        if (tree.get(n) !== null) throw new Fail('exists', n);
        const done = applyHunks(splitFile(before), s.hunks, strict, o);
        tree.now.set(o, null);
        tree.now.set(n, joinFile(done));
        tree.moves.push([o, n]);
        return;
      }
      const p = oldP!;
      if (!safe(p)) throw new Fail('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const done = applyHunks(splitFile(before), s.hunks, strict, p);
      tree.now.set(p, joinFile(done));
    };
  });
}

/* ------------------------------------------------------------------ */
/* SEARCH/REPLACE blocks (SPEC.md section 7)                          */
/* ------------------------------------------------------------------ */

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const f = splitFile(before);
    const found = findTier(f.lines, oldLines, strict);
    if (!found) throw new Fail('no-match', path);
    if (found.pos.length > 1) throw new Fail('ambiguous', path);
    const at = found.pos[0]!;
    const rep = buildReplacement(f, at, found.tier, oldLines, newLines.map((t) => ({ text: t, ctx: -1 })));
    f.lines.splice(at, oldLines.length, ...rep);
    tree.now.set(path, joinFile(f));
  };
}

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let prevEnd = 0;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLn = i + 1;
    let path: string | null = null;
    for (let j = i - 1; j >= prevEnd; j--) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLn}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = i + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchLn}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchLn}`);
    const oldLines = lines.slice(i + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push(srEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* V4A patches (SPEC.md section 8)                                    */
/* ------------------------------------------------------------------ */

interface VChunk {
  anchor: string | null;
  eof: boolean;
  body: string[];
}

function v4aAddEdit(path: string, lines: string[]): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) !== null) throw new Fail('exists', path);
    tree.now.set(path, lines.length === 0 ? '' : lines.join('\n') + '\n');
  };
}

function v4aDeleteEdit(path: string): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) === null) throw new Fail('missing', path);
    tree.now.set(path, null);
  };
}

function v4aUpdateEdit(path: string, moveTo: string | null, chunks: VChunk[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const f = splitFile(before);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null) {
        const idx = findAnchor(f.lines, cursor, ch.anchor, strict);
        if (idx < 0) throw new Fail('no-match', path);
        cursor = idx + 1;
      }
      const o: string[] = [];
      const n: NLine[] = [];
      for (const l of ch.body) {
        if (l === '') {
          o.push('');
          n.push({ text: '', ctx: o.length - 1 });
        } else if (l[0] === ' ') {
          const t = l.slice(1);
          o.push(t);
          n.push({ text: t, ctx: o.length - 1 });
        } else if (l[0] === '-') {
          o.push(l.slice(1));
        } else if (l[0] === '+') {
          n.push({ text: l.slice(1), ctx: -1 });
        }
      }
      if (o.length === 0) {
        const pos = ch.eof ? f.lines.length : cursor;
        f.lines.splice(pos, 0, ...n.map((x) => x.text));
        cursor = pos + n.length;
      } else {
        const found = findFirstAtOrAfter(f.lines, cursor, o, strict, ch.eof);
        if (!found) throw new Fail('no-match', path);
        const rep = buildReplacement(f, found.at, found.tier, o, n);
        f.lines.splice(found.at, o.length, ...rep);
        cursor = found.at + rep.length;
      }
    }
    const out = joinFile(f);
    if (moveTo !== null) {
      tree.now.set(path, null);
      tree.now.set(moveTo, out);
      tree.moves.push([path, moveTo]);
    } else {
      tree.now.set(path, out);
    }
  };
}

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i]!;
    const ln = i + 1;
    if (blank(l)) {
      i++;
      continue;
    }
    if (l.startsWith('*** Add File: ')) {
      const path = l.slice('*** Add File: '.length).trim();
      i++;
      const raw: [string, number][] = [];
      while (i < last) {
        const m = lines[i]!;
        if (m.startsWith('+') || blank(m)) {
          raw.push([m, i + 1]);
          i++;
          continue;
        }
        break;
      }
      while (raw.length > 0 && blank(raw[raw.length - 1]![0])) raw.pop();
      const fl: string[] = [];
      for (const [m, mln] of raw) {
        if (m.startsWith('+')) fl.push(m.slice(1));
        else if (m === '') fl.push('');
        else throw new Exit2(`error: parse ${mln}`);
      }
      edits.push(v4aAddEdit(path, fl));
      continue;
    }
    if (l.startsWith('*** Delete File: ')) {
      const path = l.slice('*** Delete File: '.length).trim();
      i++;
      edits.push(v4aDeleteEdit(path));
      continue;
    }
    if (l.startsWith('*** Update File: ')) {
      const path = l.slice('*** Update File: '.length).trim();
      const updateLn = ln;
      i++;
      let moveTo: string | null = null;
      if (i < last && lines[i]!.startsWith('*** Move to: ')) {
        moveTo = lines[i]!.slice('*** Move to: '.length).trim();
        i++;
      }
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      let firstChunk = true;
      const finalize = () => {
        if (cur !== null) {
          while (cur.body.length > 0 && blank(cur.body[cur.body.length - 1]!)) cur.body.pop();
          chunks.push(cur);
          cur = null;
        }
      };
      while (i < last) {
        const m = lines[i]!;
        const mln = i + 1;
        if (m.startsWith('@@')) {
          finalize();
          const anchor = m.slice(2).trim();
          cur = { anchor: anchor === '' ? null : anchor, eof: false, body: [] };
          firstChunk = false;
          i++;
          continue;
        }
        if (m.trim() === '*** End of File') {
          if (cur === null) throw new Exit2(`error: parse ${mln}`);
          cur.eof = true;
          finalize();
          i++;
          continue;
        }
        if (m.startsWith('*** ')) break;
        if (m === '' || m[0] === ' ' || m[0] === '-' || m[0] === '+') {
          if (cur === null) {
            if (!firstChunk) {
              if (blank(m)) {
                i++;
                continue;
              }
              throw new Exit2(`error: parse ${mln}`);
            }
            cur = { anchor: null, eof: false, body: [] };
            firstChunk = false;
          }
          cur.body.push(m);
          i++;
          continue;
        }
        throw new Exit2(`error: parse ${mln}`);
      }
      finalize();
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLn}`);
      edits.push(v4aUpdateEdit(path, moveTo, chunks, strict));
      continue;
    }
    throw new Exit2(`error: parse ${ln}`);
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* Running the CLI (SPEC.md sections 1, 2 and 10)                     */
/* ------------------------------------------------------------------ */

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  interface Row {
    key: string;
    line: string;
    write: () => void;
  }
  const rows: Row[] = [];
  const changed: { path: string; was: string | null; now: string | null }[] = [];
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    changed.push({ path: p, was, now });
  }
  const usedOld = new Set<string>();
  const usedNew = new Set<string>();
  const moveRows: Row[] = [];
  for (const [o, n] of tree.moves) {
    const oc = changed.find((c) => c.path === o);
    const nc = changed.find((c) => c.path === n);
    if (oc && nc && oc.was !== null && oc.now === null && nc.was === null && nc.now !== null) {
      usedOld.add(o);
      usedNew.add(n);
      const content = nc.now!;
      moveRows.push({
        key: n,
        line: `R ${o} -> ${n}`,
        write: () => {
          rmSync(o, { force: true });
          mkdirSync(dirname(n), { recursive: true });
          writeFileSync(n, content);
        },
      });
    }
  }
  for (const c of changed) {
    if (usedOld.has(c.path) || usedNew.has(c.path)) continue;
    const kindRow = c.was === null ? 'A' : c.now === null ? 'D' : 'M';
    const p = c.path;
    const content = c.now;
    rows.push({
      key: p,
      line: `${kindRow} ${p}`,
      write: () => {
        if (content === null) rmSync(p, { force: true });
        else {
          mkdirSync(dirname(p), { recursive: true });
          writeFileSync(p, content);
        }
      },
    });
  }
  rows.push(...moveRows);
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) for (const r of rows) r.write();
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}

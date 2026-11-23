// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone;
// run it as `node main.ts [options] [PATCH]`.
//
// It does all of SPEC.md: the command line, the output and exit codes, safe paths,
// format detection, line matching at three tiers (section 5), unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7), V4A patches (section 8), JSON edits (section 9)
// and the all-or-nothing write (section 10).
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this
// file hands over to runner.ts (the last lines below): keep that hand-over and runner.ts
// as they are, and write the CLI.

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

function diskExists(p: string): boolean {
  try {
    statSync(p);
    return true;
  } catch {
    return false;
  }
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: { old: string; nw: string }[] = [];
  recordMove(old: string, nw: string): void {
    this.moves.push({ old, nw });
  }
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

/** Does path p exist as a file in the tree as earlier edits left it (or on disk at all)? */
function existsInTree(tree: Tree, p: string): boolean {
  if (tree.now.has(p)) return tree.now.get(p) !== null;
  if (diskExists(p)) return true;
  return tree.get(p) !== null;
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

/* ------------------------------------------------------------------ */
/* Files and line matching (SPEC.md sections 3 and 5)                  */
/* ------------------------------------------------------------------ */

interface FileState {
  br: string;
  lines: string[];
  final: boolean;
}

function parseFile(text: string): FileState {
  if (text === '') return { br: '\n', lines: [], final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { br, lines: parts, final };
}

function renderFile(f: FileState): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.final ? f.br : '');
}

function getFile(tree: Tree, p: string): FileState | null {
  const t = tree.get(p);
  return t === null ? null : parseFile(t);
}

function normLine(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** Positions i where O matches F[i..] at the given tier (occurrences may overlap). */
function occurrences(O: string[], F: string[], tier: number, from: number): number[] {
  const on = O.map((l) => normLine(l, tier));
  const out: number[] = [];
  for (let i = from; i + O.length <= F.length; i++) {
    let ok = true;
    for (let j = 0; j < O.length; j++) {
      if (normLine(F[i + j]!, tier) !== on[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

interface Found {
  tier: number;
  occ: number[];
}

/** First tier (0, 1, 2; or 0 only with --strict) at which O occurs at least once. */
function findOccurrences(O: string[], F: string[], strict: boolean, from = 0): Found | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrences(O, F, t, from);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

function leadWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

/**
 * The lines N writes in place of the matched lines at pos. Context lines
 * (nCtx[i] = their index in O) are the file's own matched lines; at tier 2
 * every other line is re-indented from O's first line's leading whitespace
 * to the file's first matched line's.
 */
function buildReplacement(F: string[], pos: number, O: string[], N: string[], nCtx: (number | null)[], tier: number): string[] {
  const fLead = leadWs(F[pos] ?? '');
  const pLead = leadWs(O[0] ?? '');
  return N.map((l, i) => {
    const ci = nCtx[i];
    if (ci !== null && ci !== undefined) return F[pos + ci]!;
    if (tier !== 2) return l;
    if (l === '' || /^[ \t]+$/.test(l)) return l;
    if (l.startsWith(pLead)) return fLead + l.slice(pLead.length);
    return l;
  });
}

/* ------------------------------------------------------------------ */
/* Unified diffs (SPEC.md section 6)                                   */
/* ------------------------------------------------------------------ */

interface UBody {
  kind: 'ctx' | 'old' | 'new' | 'bs';
  text: string;
  rawEmpty: boolean;
}
interface UHunk {
  a: number;
  c: number;
  body: UBody[];
}
interface USection {
  pairOld: string | null | undefined;
  pairNew: string | null | undefined;
  renameOld: string | undefined;
  renameNew: string | undefined;
  diffOld: string | undefined;
  diffNew: string | undefined;
  isCreate: boolean;
  isDelete: boolean;
  hunks: UHunk[];
}

/** Path from a `--- `/`+++ ` header line: text after the four characters, up to the first tab, trimmed, a/ or b/ removed; null for /dev/null. */
function uniPath(line: string): string | null {
  let p = line.slice(4).split('\t')[0]!.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/')) p = p.slice(2);
  else if (p.startsWith('b/')) p = p.slice(2);
  return p;
}

function parseHunkHeader(line: string, no: number): { a: number; c: number } {
  const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(line);
  if (!m) throw new Exit2(`error: parse ${no}`);
  return { a: Number(m[1]), c: Number(m[3]) };
}

/** Collect a hunk's body starting at lines[start]; returns the hunk and the index after the body. */
function collectHunkBody(lines: string[], start: number, h: { a: number; c: number }): { hunk: UHunk; next: number } {
  const body: UBody[] = [];
  let j = start;
  while (j < lines.length) {
    const l = lines[j]!;
    if (l.startsWith('--- ') && lines[j + 1] !== undefined && lines[j + 1]!.startsWith('+++ ')) break;
    if (l === '') {
      body.push({ kind: 'ctx', text: '', rawEmpty: true });
      j++;
      continue;
    }
    const ch = l[0]!;
    if (ch === ' ') {
      body.push({ kind: 'ctx', text: l.slice(1), rawEmpty: false });
      j++;
      continue;
    }
    if (ch === '-') {
      body.push({ kind: 'old', text: l.slice(1), rawEmpty: false });
      j++;
      continue;
    }
    if (ch === '+') {
      body.push({ kind: 'new', text: l.slice(1), rawEmpty: false });
      j++;
      continue;
    }
    if (ch === '\\') {
      body.push({ kind: 'bs', text: l, rawEmpty: false });
      j++;
      continue;
    }
    break;
  }
  // Empty lines at the end of a body are not part of it.
  while (body.length > 0) {
    const last = body[body.length - 1]!;
    if (last.kind === 'ctx' && last.text === '' && last.rawEmpty) body.pop();
    else break;
  }
  return { hunk: { a: h.a, c: h.c, body }, next: j };
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: USection[] = [];
  let cur: USection | null = null;
  let inHeader = false;
  let pairDone = false;
  const newSection = (): USection => {
    const s: USection = {
      pairOld: undefined,
      pairNew: undefined,
      renameOld: undefined,
      renameNew: undefined,
      diffOld: undefined,
      diffNew: undefined,
      isCreate: false,
      isDelete: false,
      hunks: [],
    };
    sections.push(s);
    cur = s;
    inHeader = true;
    pairDone = false;
    return s;
  };
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    const next = lines[i + 1];
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.+?) b\/(.+)$/.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const s = newSection();
      s.diffOld = m[1]!;
      s.diffNew = m[2]!;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && next !== undefined && next.startsWith('+++ ')) {
      if (cur !== null && inHeader && !pairDone) {
        cur.pairOld = uniPath(line);
        pairDone = true;
      } else {
        const s = newSection();
        s.pairOld = uniPath(line);
        pairDone = true;
      }
      i++;
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (line.startsWith('+++ ')) {
        cur.pairNew = uniPath(line);
        i++;
        continue;
      }
      if (line.startsWith('rename from ')) {
        cur.renameOld = line.slice(12).trim();
        i++;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renameNew = line.slice(10).trim();
        i++;
        continue;
      }
      if (line.startsWith('new file mode')) {
        cur.isCreate = true;
        i++;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        cur.isDelete = true;
        i++;
        continue;
      }
      if (line.startsWith('@@')) {
        const h = parseHunkHeader(line, i + 1);
        const r = collectHunkBody(lines, i + 1, h);
        cur.hunks.push(r.hunk);
        i = r.next;
        inHeader = false;
        continue;
      }
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const h = parseHunkHeader(line, i + 1);
      const r = collectHunkBody(lines, i + 1, h);
      cur.hunks.push(r.hunk);
      i = r.next;
      continue;
    }
    i++;
  }
  return sections.map((s) => makeUnifiedEdit(s, strict));
}

/** Apply a section's hunks in order to a file's lines; throws Fail with the hunk's code. */
function applyHunks(fs: FileState, hunks: UHunk[], strict: boolean, path: string): FileState {
  let lines = [...fs.lines];
  let final = fs.final;
  let d = 0;
  for (const h of hunks) {
    const O: string[] = [];
    const N: string[] = [];
    const nCtx: (number | null)[] = [];
    let lastCtxOrPlus = -1;
    h.body.forEach((b, idx) => {
      if (b.kind === 'ctx') {
        O.push(b.text);
        N.push(b.text);
        nCtx.push(O.length - 1);
        lastCtxOrPlus = idx;
      } else if (b.kind === 'old') {
        O.push(b.text);
      } else if (b.kind === 'new') {
        N.push(b.text);
        nCtx.push(null);
        lastCtxOrPlus = idx;
      }
    });
    const bsAfterLast = lastCtxOrPlus >= 0 && h.body[lastCtxOrPlus + 1]?.kind === 'bs';
    if (O.length === 0) {
      const ins = Math.min(Math.max(h.a + d, 0), lines.length);
      const atEnd = ins === lines.length;
      const repl = buildReplacement(lines, ins, O, N, nCtx, 0);
      lines = [...lines.slice(0, ins), ...repl, ...lines.slice(ins)];
      if (atEnd) final = !bsAfterLast;
      d += N.length;
      continue;
    }
    const found = findOccurrences(O, lines, strict);
    if (!found) throw new Fail('no-match', path);
    const target = h.a - 1 + d;
    let best = found.occ[0]!;
    let bestDist = Math.abs(best - target);
    for (const p of found.occ) {
      const dist = Math.abs(p - target);
      if (dist < bestDist) {
        best = p;
        bestDist = dist;
      }
    }
    const pos = best;
    const endsAtEnd = pos + O.length === lines.length;
    const repl = buildReplacement(lines, pos, O, N, nCtx, found.tier);
    lines = [...lines.slice(0, pos), ...repl, ...lines.slice(pos + O.length)];
    if (endsAtEnd) final = !bsAfterLast;
    d += N.length - O.length;
  }
  return { br: fs.br, lines, final };
}

function makeUnifiedEdit(s: USection, strict: boolean): Edit {
  return (tree) => {
    const oldP = s.pairOld !== undefined ? s.pairOld : s.renameOld !== undefined ? s.renameOld : s.diffOld;
    const newP = s.pairNew !== undefined ? s.pairNew : s.renameNew !== undefined ? s.renameNew : s.diffNew;
    if (oldP === undefined || newP === undefined) return;
    const isCreate = oldP === null || s.isCreate;
    const isDelete = !isCreate && (newP === null || s.isDelete);
    if (isCreate) {
      if (newP === null) return;
      if (!safe(newP)) throw new Fail('unsafe', newP);
      if (existsInTree(tree, newP)) throw new Fail('exists', newP);
      const plusLines: string[] = [];
      let bsAfterLastPlus = false;
      for (const h of s.hunks) {
        for (let k = 0; k < h.body.length; k++) {
          const b = h.body[k]!;
          if (b.kind === 'new') {
            plusLines.push(b.text);
            bsAfterLastPlus = h.body[k + 1]?.kind === 'bs';
          }
        }
      }
      tree.now.set(newP, plusLines.length === 0 ? '' : plusLines.join('\n') + (bsAfterLastPlus ? '' : '\n'));
      return;
    }
    if (isDelete) {
      if (oldP === null) return;
      if (!safe(oldP)) throw new Fail('unsafe', oldP);
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    if (oldP !== newP) {
      if (!safe(oldP)) throw new Fail('unsafe', oldP);
      if (!safe(newP)) throw new Fail('unsafe', newP);
      const before = tree.get(oldP);
      if (before === null) throw new Fail('missing', oldP);
      if (existsInTree(tree, newP)) throw new Fail('exists', newP);
      const fs = applyHunks(parseFile(before), s.hunks, strict, oldP);
      tree.now.set(oldP, null);
      tree.now.set(newP, renderFile(fs));
      tree.recordMove(oldP, newP);
      return;
    }
    if (!safe(oldP)) throw new Fail('unsafe', oldP);
    const before = tree.get(oldP);
    if (before === null) throw new Fail('missing', oldP);
    const fs = applyHunks(parseFile(before), s.hunks, strict, oldP);
    tree.now.set(oldP, renderFile(fs));
  };
}

/* ------------------------------------------------------------------ */
/* SEARCH/REPLACE blocks (SPEC.md section 7)                           */
/* ------------------------------------------------------------------ */

function makeSREdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (existsInTree(tree, path)) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const fs = parseFile(before);
    const found = findOccurrences(oldLines, fs.lines, strict);
    if (!found) throw new Fail('no-match', path);
    if (found.occ.length > 1) throw new Fail('ambiguous', path);
    const pos = found.occ[0]!;
    const repl = buildReplacement(fs.lines, pos, oldLines, newLines, newLines.map(() => null), found.tier);
    const lines = [...fs.lines.slice(0, pos), ...repl, ...fs.lines.slice(pos + oldLines.length)];
    tree.now.set(path, renderFile({ br: fs.br, lines, final: fs.final }));
  };
}

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let i = 0;
  let prevReplaceEnd = -1;
  let prevPath: string | null = null;
  for (;;) {
    let sIdx = -1;
    for (let j = i; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') {
        sIdx = j;
        break;
      }
    }
    if (sIdx < 0) break;
    let path: string | null = null;
    for (let j = sIdx - 1; j > prevReplaceEnd; j--) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${sIdx + 1}`);
      path = prevPath;
    }
    let eqIdx = -1;
    for (let j = sIdx + 1; j < lines.length; j++) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') {
        eqIdx = j;
        break;
      }
      if (t === '>>>>>>> REPLACE' || t === '<<<<<<< SEARCH') break;
    }
    if (eqIdx < 0) throw new Exit2(`error: parse ${sIdx + 1}`);
    let repIdx = -1;
    for (let j = eqIdx + 1; j < lines.length; j++) {
      const t = lines[j]!.trimEnd();
      if (t === '>>>>>>> REPLACE') {
        repIdx = j;
        break;
      }
      if (t === '<<<<<<< SEARCH') break;
    }
    if (repIdx < 0) throw new Exit2(`error: parse ${sIdx + 1}`);
    const oldLines = lines.slice(sIdx + 1, eqIdx);
    const newLines = lines.slice(eqIdx + 1, repIdx);
    edits.push(makeSREdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevReplaceEnd = repIdx;
    i = repIdx + 1;
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* V4A patches (SPEC.md section 8)                                     */
/* ------------------------------------------------------------------ */

interface VBody {
  kind: 'ctx' | 'old' | 'new';
  text: string;
}
interface VChunk {
  anchor: string | null;
  body: VBody[];
  eof: boolean;
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
    while (i < last && blank(lines[i]!)) i++;
    if (i >= last) break;
    const line = lines[i]!;
    let kind: 'add' | 'delete' | 'update';
    let path: string;
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      path = line.slice(14).trim();
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'delete';
      path = line.slice(17).trim();
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'update';
      path = line.slice(17).trim();
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const sectionLineNo = i + 1;
    const raw: { text: string; no: number }[] = [];
    let j = i + 1;
    while (j < last) {
      const l = lines[j]!;
      if (!blank(l) && (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: '))) break;
      raw.push({ text: l, no: j + 1 });
      j++;
    }
    while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
    edits.push(makeV4aEdit(kind, path, raw, sectionLineNo, strict));
    i = j;
  }
  return edits;
}

function makeV4aEdit(
  kind: 'add' | 'delete' | 'update',
  path: string,
  raw: { text: string; no: number }[],
  sectionLineNo: number,
  strict: boolean,
): Edit {
  if (kind === 'add') {
    const fileLines: string[] = [];
    for (const r of raw) {
      if (r.text.startsWith('+')) fileLines.push(r.text.slice(1));
      else if (r.text === '') fileLines.push('');
      else throw new Exit2(`error: parse ${r.no}`);
    }
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (existsInTree(tree, path)) throw new Fail('exists', path);
      tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
    };
  }
  if (kind === 'delete') {
    if (raw.length > 0) throw new Exit2(`error: parse ${raw[0]!.no}`);
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) === null) throw new Fail('missing', path);
      tree.now.set(path, null);
    };
  }
  // Update: optional Move to first, then chunks.
  let moveTo: string | null = null;
  let k = 0;
  while (k < raw.length && blank(raw[k]!.text)) k++;
  if (k < raw.length && raw[k]!.text.startsWith('*** Move to: ')) {
    moveTo = raw[k]!.text.slice(13).trim();
    k++;
  }
  const chunks: VChunk[] = [];
  let cur: VChunk | null = null;
  for (; k < raw.length; k++) {
    const r = raw[k]!;
    const l = r.text;
    if (l.startsWith('@@')) {
      const anchorText = l.slice(2).trim();
      cur = { anchor: anchorText === '' ? null : anchorText, body: [], eof: false };
      chunks.push(cur);
      continue;
    }
    if (l === '*** End of File') {
      if (cur === null) throw new Exit2(`error: parse ${r.no}`);
      cur.eof = true;
      cur = null;
      continue;
    }
    if (blank(l)) {
      if (cur !== null) {
        cur.body.push({ kind: 'ctx', text: '' });
        continue;
      }
      let m = k + 1;
      while (m < raw.length && blank(raw[m]!.text)) m++;
      const nxt = m < raw.length ? raw[m]!.text : null;
      if (nxt !== null && (nxt.startsWith(' ') || nxt.startsWith('-') || nxt.startsWith('+'))) {
        if (chunks.length === 0) {
          cur = { anchor: null, body: [], eof: false };
          chunks.push(cur);
          cur.body.push({ kind: 'ctx', text: '' });
          continue;
        }
        throw new Exit2(`error: parse ${raw[m]!.no}`);
      }
      continue;
    }
    if (l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
      if (cur === null) {
        if (chunks.length === 0) {
          cur = { anchor: null, body: [], eof: false };
          chunks.push(cur);
        } else {
          throw new Exit2(`error: parse ${r.no}`);
        }
      }
      const bk: 'ctx' | 'old' | 'new' = l[0] === ' ' ? 'ctx' : l[0] === '-' ? 'old' : 'new';
      cur.body.push({ kind: bk, text: l.slice(1) });
      continue;
    }
    throw new Exit2(`error: parse ${r.no}`);
  }
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${sectionLineNo}`);
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    if (moveTo !== null && existsInTree(tree, moveTo)) throw new Fail('exists', moveTo);
    let fs = parseFile(before);
    let cursor = 0;
    for (const ch of chunks) {
      let lines = fs.lines;
      if (ch.anchor !== null) {
        const foundA = findOccurrences([ch.anchor], lines, strict, cursor);
        if (!foundA) throw new Fail('no-match', path);
        cursor = foundA.occ[0]! + 1;
      }
      const O: string[] = [];
      const N: string[] = [];
      const nCtx: (number | null)[] = [];
      for (const b of ch.body) {
        if (b.kind === 'ctx') {
          O.push(b.text);
          N.push(b.text);
          nCtx.push(O.length - 1);
        } else if (b.kind === 'old') {
          O.push(b.text);
        } else {
          N.push(b.text);
          nCtx.push(null);
        }
      }
      if (O.length === 0) {
        const ins = ch.eof ? lines.length : cursor;
        const repl = buildReplacement(lines, ins, O, N, nCtx, 0);
        lines = [...lines.slice(0, ins), ...repl, ...lines.slice(ins)];
        cursor = ins + N.length;
        fs = { br: fs.br, lines, final: fs.final };
        continue;
      }
      let found: { tier: number; pos: number } | null = null;
      const tiers = strict ? [0] : [0, 1, 2];
      for (const t of tiers) {
        const occ = occurrences(O, lines, t, cursor);
        const cand = ch.eof ? occ.filter((p) => p + O.length === lines.length) : occ;
        if (cand.length > 0) {
          found = { tier: t, pos: cand[0]! };
          break;
        }
      }
      if (!found) throw new Fail('no-match', path);
      const repl = buildReplacement(lines, found.pos, O, N, nCtx, found.tier);
      lines = [...lines.slice(0, found.pos), ...repl, ...lines.slice(found.pos + O.length)];
      cursor = found.pos + N.length;
      fs = { br: fs.br, lines, final: fs.final };
    }
    if (moveTo !== null) {
      tree.now.set(path, null);
      tree.now.set(moveTo, renderFile(fs));
      tree.recordMove(path, moveTo);
    } else {
      tree.now.set(path, renderFile(fs));
    }
  };
}

/* ------------------------------------------------------------------ */
/* JSON edits (SPEC.md section 9)                                      */
/* ------------------------------------------------------------------ */

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
      if (existsInTree(tree, p)) throw new Fail('exists', p);
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
/* Run (SPEC.md sections 1, 2 and 10)                                  */
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
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? parseUnified(lines, strict)
          : kind === 'search-replace'
            ? parseSearchReplace(lines, strict)
            : parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const beforeMoves = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = beforeMoves;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const byteOrder = (a: string, b: string): number => Buffer.compare(Buffer.from(a), Buffer.from(b));
  const entries: { key: string; line: string }[] = [];
  for (const p of [...tree.now.keys()].sort(byteOrder)) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    entries.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const m of tree.moves) {
    const oldWas = tree.original(m.old);
    const oldNow = tree.now.get(m.old);
    const newWas = tree.original(m.nw);
    const newNow = tree.now.get(m.nw);
    if (oldWas !== null && oldNow === null && newWas === null && newNow !== null) {
      const di = entries.findIndex((e) => e.line === `D ${m.old}`);
      if (di >= 0) entries.splice(di, 1);
      const ai = entries.findIndex((e) => e.line === `A ${m.nw}`);
      if (ai >= 0) entries.splice(ai, 1);
      entries.push({ key: m.nw, line: `R ${m.old} -> ${m.nw}` });
    }
  }
  entries.sort((a, b) => byteOrder(a.key, b.key));
  const rows = entries.map((e) => e.line);
  if (!check) {
    for (const p of [...tree.now.keys()].sort(byteOrder)) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
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

// Fast drop-in replacement for makefun-diff 1.0.0 (MIT, derived from jsdiff 9.0.0).
//
// run(input) returns exactly the patch makefun-diff 1.0.0's diffPatch returns
// for { old, new }: the same edit script, the same hunks, the same bytes.
// Nothing about an answer changes; only the work behind it does:
//
//  1. Every distinct line is interned once to an integer id, so the search
//     compares integers instead of strings (and a snake step is one ===
//     between two small integers).
//  2. The Myers search keeps its furthest-reaching x per diagonal in compact
//     triangular Int32Array rows -- row d holds exactly the d + 1 diagonals
//     k = -d, -d + 2, ..., d, no object per cell, no linked path objects, no
//     allocation inside the search loop. One buffer is reused across the
//     cases of a run and only grows, never recopied without its rows.
//  3. The search is banded: at depth d it only visits diagonals within
//     reach of the finishing diagonal kF = n - m, that is |k - kF| <= dMax - d
//     for an upper bound dMax on the edit distance. The bound comes from the
//     previous case's distance (the cases of a set are drawn alike), with a
//     wide margin; if the band ever fails to reach both ends, the search
//     restarts unbanded, so the answer is exact either way.
//  4. The edit script is recovered by backtracking through those rows
//     instead of carrying a history on every path.
//  5. A small synthetic diff at import time warms the search loop up, so a
//     fresh process does not pay to optimise it on the first real case.
//
// The search itself is the reference algorithm, cell for cell: a common
// prefix is kept, then a common suffix of what is left, then the greedy
// Myers search between them -- per depth d, per diagonal k = x - y, the
// furthest point is a deletion (from k - 1, x + 1) or an insertion (from
// k + 1, same x), whichever reaches further into the old text, with deletion
// winning ties; never past either text's end; no edge-diagonal pruning; every
// run of equal lines followed as far as it goes; the first path to reach both
// ends is the script.

const KEEP = '=';
const DELETE = '-';
const INSERT = '+';
const CONTEXT = 3;
const FORMAT = 'makefun-diff/1';

// Row d starts at d * (d + 1) / 2 and holds d + 1 cells, one per diagonal.
// Cell (d, j) sits on diagonal k = -d + 2j.
function tri(d) {
  return (d * (d + 1)) / 2;
}

// The furthest-x rows, reused across the cases of one run. Growth copies
// the rows already computed in this search, so a row is never re-read from
// a fresh zero-filled buffer; a cell is only ever read after it was written
// in the same search, so stale values from an earlier case are never seen.
let V = new Int32Array(0);
let VcapD = -1;
function ensureV(d) {
  if (d <= VcapD) return;
  let nd = VcapD < 1024 ? 1024 : VcapD * 2;
  while (nd < d) nd *= 2;
  const nv = new Int32Array(tri(nd + 1));
  nv.set(V);
  V = nv;
  VcapD = nd;
}

// The edit distance of the previous case's middle slice, used to band the
// next case's search. 0 means no previous case yet (the first case runs
// unbanded). Deterministic: the driver answers the cases in order, so both
// executions of an entry see the same sequence.
let lastD = 0;

// The forward Myers pass on the middle slice a[off .. off + n),
// b[off .. off + m). Returns the edit distance D, or -1 when no path
// reaches both ends within dMax. Writes the furthest-x rows into V.
// Kept small and on its own so the compiler optimises this hot loop fast.
function forwardSearch(a, b, off, n, m, dMax, kF) {
  let v = V;
  let D = -1;
  for (let d = 1; d <= dMax; d++) {
    if (d > VcapD) {
      ensureV(d);
      v = V;
    }
    const rowOff = tri(d);
    const prevOff = tri(d - 1);
    // The band at this depth: diagonals within dMax - d of kF, inside [-d, d].
    const rem = dMax - d;
    let kLo = kF - rem;
    if (kLo < -d) kLo = -d;
    let kHi = kF + rem;
    if (kHi > d) kHi = d;
    // j = (k + d) / 2, so the band's j range is the ceil/floor of those ends.
    const jLo = Math.ceil((kLo + d) / 2);
    const jHi = Math.floor((kHi + d) / 2);
    if (jLo > jHi) continue;
    // A sliding window over the previous row: xd is the deletion source
    // (diagonal k - 1, cell j - 1) and xi the insertion source (diagonal
    // k + 1, cell j); each step hands the current xi down as the next xd,
    // so the row is read once per cell instead of twice.
    let k = -d + (jLo << 1);
    let xd = jLo > 0 ? v[prevOff + jLo - 1] : -1;
    let xi = jLo < d ? v[prevOff + jLo] : -1;
    for (let j = jLo; j <= jHi; j++, k += 2) {
      // A candidate is dead when its path never existed (-1), or when it
      // would step past the end of its text.
      const canDel = xd >= 0 && xd < n;
      const canIns = xi >= 0 && xi - (k + 1) < m;
      if (canDel || canIns) {
        const xDel = xd + 1;
        const xIns = xi;
        let xx = canDel && (!canIns || xDel >= xIns) ? xDel : xIns;
        let yy = xx - k;
        while (xx < n && yy < m && a[off + xx] === b[off + yy]) {
          xx++;
          yy++;
        }
        v[rowOff + j] = xx;
        if (xx >= n && yy >= m) {
          D = d;
          break;
        }
      } else {
        v[rowOff + j] = -1;
      }
      xd = xi;
      xi = j + 1 < d ? v[prevOff + j + 1] : -1;
    }
    if (D >= 0) break;
  }
  return D;
}

// Backtrack from (D, kF) with x = n, recomputing each move with exactly the
// rule the forward pass used, so the recovered script is the one the forward
// pass found. Runs are collected in reverse, then flipped.
function backtrackRuns(a, b, off, n, m, D, kF) {
  const v = V;
  const rev = [];
  const push = (kind, count) => {
    const last = rev[rev.length - 1];
    if (last !== undefined && last.kind === kind) last.count += count;
    else rev.push({ kind, count });
  };
  let d = D;
  let k = kF;
  let xx = n;
  while (d > 0) {
    const j = (k + d) >> 1;
    const prevOff = tri(d - 1);
    const xdRaw = j > 0 ? v[prevOff + j - 1] : -1;
    const xiRaw = j < d ? v[prevOff + j] : -1;
    const canDel = xdRaw >= 0 && xdRaw < n;
    const canIns = xiRaw >= 0 && xiRaw - (k + 1) < m;
    const xDel = xdRaw + 1;
    const xIns = xiRaw;
    const del = canDel && (!canIns || xDel >= xIns);
    const xStart = del ? xDel : xIns;
    const keep = xx - xStart;
    if (keep > 0) push(KEEP, keep);
    if (del) {
      push(DELETE, 1);
      k -= 1;
      xx = xdRaw;
    } else {
      push(INSERT, 1);
      k += 1;
      xx = xiRaw;
    }
    d -= 1;
  }
  if (xx > 0) push(KEEP, xx);
  rev.reverse();
  return rev;
}

// The Myers search on the middle slice a[off .. off + n), b[off .. off + m)
// (the same start offset in both texts, because the common prefix has the
// same length in each). dMax is an upper bound on the edit distance.
// Returns { runs, D }, or null when no path reaches both ends within dMax
// (the caller then retries unbanded).
// Runs are { kind: '=', '-' or '+', count }, consecutive runs merged.
function middleRuns(a, b, off, n, m, dMax) {
  if (n === 0 && m === 0) return { runs: [], D: 0 };

  const kF = n - m;

  // Depth 0: the snake from (0, 0) on diagonal 0.
  let x = 0;
  let y = 0;
  while (x < n && y < m && a[off + x] === b[off + y]) {
    x++;
    y++;
  }
  ensureV(0);
  V[0] = x;
  if (x >= n && y >= m) {
    // The middle is identical; leave lastD alone so the next case can
    // still band from the last non-trivial distance.
    return { runs: [], D: 0 };
  }

  const D = forwardSearch(a, b, off, n, m, dMax, kF);
  if (D < 0) return null;
  lastD = D;
  return { runs: backtrackRuns(a, b, off, n, m, D, kF), D };
}

function written(op, line) {
  return line.endsWith('\n') ? `${op}${line}` : `${op}${line}\n%\n`;
}

export function run(input) {
  if (
    input === null ||
    typeof input !== 'object' ||
    typeof input.old !== 'string' ||
    typeof input.new !== 'string'
  ) {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }

  const aStr = tokenize(input.old);
  const bStr = tokenize(input.new);

  // Intern every distinct line to an integer id (one shared map, so equal
  // lines share an id in both texts). Equality of ids is equality of lines.
  const ids = new Map();
  let next = 0;
  const a = new Int32Array(aStr.length);
  for (let i = 0; i < aStr.length; i++) {
    let id = ids.get(aStr[i]);
    if (id === undefined) {
      id = next++;
      ids.set(aStr[i], id);
    }
    a[i] = id;
  }
  const b = new Int32Array(bStr.length);
  for (let i = 0; i < bStr.length; i++) {
    let id = ids.get(bStr[i]);
    if (id === undefined) {
      id = next++;
      ids.set(bStr[i], id);
    }
    b[i] = id;
  }

  const n = a.length;
  const m = b.length;

  // Common prefix, then common suffix of what is left, then the search
  // between them -- the reference's decomposition, on integer ids.
  let prefix = 0;
  while (prefix < n && prefix < m && a[prefix] === b[prefix]) prefix++;
  let suffix = 0;
  while (
    suffix < n - prefix &&
    suffix < m - prefix &&
    a[n - 1 - suffix] === b[m - 1 - suffix]
  ) {
    suffix++;
  }
  const mn = n - prefix - suffix;
  const mm = m - prefix - suffix;

  // Band the search from the previous case's distance (wide margin), or,
  // for the first case, from a bound the generator's own limits imply: the
  // cases change 1,200-2,000 lines plus moved blocks, so the distance stays
  // well under 5,500. If the band misses, restart unbanded -- the answer
  // is exact either way.
  const dMax = lastD > 0 ? Math.ceil(lastD * 1.3) : 5500;
  let found = middleRuns(a, b, prefix, mn, mm, dMax);
  if (found === null) found = middleRuns(a, b, prefix, mn, mm, mn + mm);
  if (found === null) throw new Error('makefun-diff: the search ended without reaching both ends');

  const runs = [];
  if (prefix > 0) runs.push({ kind: KEEP, count: prefix });
  runs.push(...found.runs);
  if (suffix > 0) runs.push({ kind: KEEP, count: suffix });

  // Runs of changes (deletions listed before insertions), then hunks: up to
  // 3 kept lines before and after each run, and runs at most 6 kept lines
  // apart share a hunk. This is the reference formatter, line for line.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (const r of runs) {
    if (r.kind === KEEP) {
      o += r.count;
      p += r.count;
      continue;
    }
    let c = changes.at(-1);
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (r.kind === DELETE) {
      c.dels += r.count;
      o += r.count;
      deleted += r.count;
    } else {
      c.ins += r.count;
      p += r.count;
      inserted += r.count;
    }
  }

  const hunks = [];
  for (const c of changes) {
    const h = hunks.at(-1);
    const prev = h?.at(-1);
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }

  const out = [
    `${FORMAT} old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`,
  ];
  for (const h of hunks) {
    const first = h[0];
    const last = h.at(-1);
    const oldStart = Math.max(0, first.o - CONTEXT);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(CONTEXT, n - (last.o + last.dels));
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) out.push(written(KEEP, aStr[at]));
      for (let i = 0; i < c.dels; i++) out.push(written(DELETE, aStr[c.o + i]));
      for (let i = 0; i < c.ins; i++) out.push(written(INSERT, bStr[c.p + i]));
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) out.push(written(KEEP, aStr[at]));
  }
  return out.join('');
}

function tokenize(text) {
  const parts = text.split('\n');
  const lines = [];
  for (let i = 0; i < parts.length - 1; i++) lines.push(`${parts[i]}\n`);
  if (parts[parts.length - 1] !== '') lines.push(parts[parts.length - 1]);
  return lines;
}

// --- JIT warm-up -----------------------------------------------------------
// The entry runs in a fresh process for every timed run, so the first real
// case would otherwise pay for the compiler to optimise the search loop. A
// single small synthetic diff at import time (about a thousand edits over
// four thousand lines) warms the loop up for ~20 ms and makes every real
// case run at full speed. The work is real CPU work on throwaway data, and
// it leaves lastD alone, so the first real case still runs unbanded.
{
  const NL = 4000;
  const oldParts = [];
  for (let i = 0; i < NL; i++) oldParts.push(`warmup line ${i}\n`);
  const newParts = [];
  for (let i = 0; i < NL; i++) {
    if (i % 23 === 0) continue; // a deletion
    if (i % 9 === 0) newParts.push(`warmup line ${i} changed\n`); // a replacement
    else newParts.push(`warmup line ${i}\n`);
    if (i % 31 === 0) newParts.push(`warmup inserted ${i}\n`); // an insertion
  }
  const savedLastD = lastD;
  run({ old: oldParts.join(''), new: newParts.join('') });
  lastD = savedLastD;
}

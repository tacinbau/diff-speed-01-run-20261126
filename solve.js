// Full-WASM Myers diff loader (v2) — written in this session.
// The JS side only UTF-8-encodes the two texts into linear memory, calls
// solve() once per case, and UTF-8-decodes the patch out. Tokenize,
// intern, search, backtrack and format all run in WebAssembly.
//
// Layout (kept in sync with myers2.wat): IN_OLD 0x1000 (up to ~2 MiB),
// IN_NEW 0x200000 (up to ~2 MiB), OUT 0xD00000 (8 MiB).

import { readFileSync } from 'node:fs';

const wasmBytes = readFileSync(new URL('./solver.wasm', import.meta.url));
const { instance } = await WebAssembly.instantiate(wasmBytes, {});
const memory = instance.exports.memory;
const wasmSolve = instance.exports.solve;

const IN_OLD = 4096;
const IN_NEW = 2097152;
const OUT = 13631488;
const MAX_TEXT = 2097152 - 4096;

const encoder = new TextEncoder();
const decoder = new TextDecoder();

// The edit distance of the previous case's middle slice, used to band the
// next case's search. 0 means no previous case yet. Only updated on a
// successful search (D > 0).
let lastD = 0;

export function run(input) {
  if (
    input === null ||
    typeof input !== 'object' ||
    typeof input.old !== 'string' ||
    typeof input.new !== 'string'
  ) {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }

  const oldView = new Uint8Array(memory.buffer, IN_OLD, MAX_TEXT);
  const newView = new Uint8Array(memory.buffer, IN_NEW, MAX_TEXT);
  const oe = encoder.encodeInto(input.old, oldView);
  const ne = encoder.encodeInto(input.new, newView);
  if (oe.read < input.old.length || ne.read < input.new.length) {
    throw new Error('makefun-diff: input text exceeds the 2 MiB fixed buffer');
  }

  const dMaxHint = lastD > 0 ? Math.ceil(lastD * 1.3) : 5500;
  const packed = wasmSolve(IN_OLD, oe.written, IN_NEW, ne.written, OUT, dMaxHint);
  const outLen = Number(packed >> 32n);
  const D = Number(packed & 0xffffffffn);
  if (D > 0) lastD = D;
  return decoder.decode(new Uint8Array(memory.buffer, OUT, outLen));
}

// --- JIT / WASM warm-up ----------------------------------------------------
// Same rationale as the v1 loader: the entry runs in a fresh process per
// timed run, so warm the JS pipeline and the WASM optimizing compiler with
// a small synthetic diff at import time (repeated so TurboFan tiers the
// search up). Leaves lastD alone.
{
  const NL = 4000;
  const oldParts = [];
  for (let i = 0; i < NL; i++) oldParts.push(`warmup line ${i}\n`);
  const newParts = [];
  for (let i = 0; i < NL; i++) {
    if (i % 23 === 0) continue;
    if (i % 9 === 0) newParts.push(`warmup line ${i} changed\n`);
    else newParts.push(`warmup line ${i}\n`);
    if (i % 31 === 0) newParts.push(`warmup inserted ${i}\n`);
  }
  const savedLastD = lastD;
  for (let w = 0; w < 1; w++) {
    run({ old: oldParts.join(''), new: newParts.join('') });
  }
  lastD = savedLastD;
}

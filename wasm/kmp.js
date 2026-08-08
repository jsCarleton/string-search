'use strict';

const fs = require('fs');
const path = require('path');

/**
 * Loads the KMP WebAssembly module and returns a `search(text, pattern)`
 * function backed by it. `search` writes both strings into the module's
 * linear memory and returns the index of the first match, or -1.
 */
async function loadKmp(wasmPath = path.join(__dirname, 'kmp.wasm')) {
  const bytes = fs.readFileSync(wasmPath);
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const { memory, build_lps, kmp_search } = instance.exports;

  function search(text, pattern) {
    const textBytes = Buffer.from(text, 'utf8');
    const patBytes = Buffer.from(pattern, 'utf8');

    // Linear memory layout: text, then pattern, then the i32 lps scratch
    // buffer (4 bytes per pattern byte), each 8-byte aligned.
    const textPtr = 0;
    const patPtr = align8(textPtr + textBytes.length);
    const lpsPtr = align8(patPtr + patBytes.length);
    const neededBytes = lpsPtr + patBytes.length * 4;

    growMemoryIfNeeded(memory, neededBytes);

    const mem = new Uint8Array(memory.buffer);
    mem.set(textBytes, textPtr);
    mem.set(patBytes, patPtr);

    return kmp_search(textPtr, textBytes.length, patPtr, patBytes.length, lpsPtr);
  }

  return { search, instance };
}

function align8(offset) {
  return (offset + 7) & ~7;
}

function growMemoryIfNeeded(memory, neededBytes) {
  const pageSize = 65536;
  const availableBytes = memory.buffer.byteLength;
  if (neededBytes > availableBytes) {
    const morePages = Math.ceil((neededBytes - availableBytes) / pageSize);
    memory.grow(morePages);
  }
}

module.exports = { loadKmp };

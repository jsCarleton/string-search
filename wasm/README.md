# KMP in WebAssembly

`kmp.wat` is a hand-written WebAssembly Text (WAT) module implementing the
Knuth-Morris-Pratt string matching algorithm.

## Exports

- `memory` — the module's linear memory, used to pass strings in.
- `build_lps(patPtr, patLen, lpsPtr)` — fills an i32 array at `lpsPtr` with
  the pattern's failure table (longest proper prefix that is also a
  suffix, per position).
- `kmp_search(textPtr, textLen, patPtr, patLen, lpsPtr) -> i32` — returns
  the index of the first occurrence of the pattern in the text, or `-1` if
  it does not occur. `lpsPtr` must point to scratch space of at least
  `4 * patLen` bytes; `kmp_search` calls `build_lps` internally.

The caller owns memory layout: write the text bytes and pattern bytes into
`memory` at whatever offsets you like (see `kmp.js` for an example), then
call `kmp_search` with those offsets and lengths.

## Build

```sh
npm run build   # requires wat2wasm (brew install wabt)
```

## Test

```sh
npm test
```

`kmp.js` is a small Node loader (`loadKmp()`) that handles encoding
strings into memory and exposes a plain `search(text, pattern)` function
for convenience/testing.

## Formal proof

`proof/` contains an in-progress Rocq/Coq proof that this module is
correct, checked directly against WasmCert-Coq's mechanized WebAssembly
semantics (not just an abstract model of the algorithm). See
[`proof/README.md`](proof/README.md) for the plan and current status.

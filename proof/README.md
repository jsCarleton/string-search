# Formal correctness proof of kmp.wasm

A Rocq/Coq proof that `../wasm/kmp.wasm` (the compiled KMP module) is correct,
checked against [WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq),
a mechanized formalization of WebAssembly's real reduction semantics —
not against an abstract model of the algorithm. There is no program
logic (Hoare-style reasoning) available for this semantics, so loop
correctness is proved directly by induction over the small-step
reduction relation.

## Requirements

- The `WasmCert-Coq` opam switch (`opam switch WasmCert-Coq`), providing
  `coqc` 8.20.1 and the `coq-wasm` library (`From Wasm Require Import ...`).
- A local checkout of [WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq)
  is not required to compile these files — only the installed library.

```sh
eval $(opam env --switch=WasmCert-Coq)
coqc KMPBytes.v && coqc CoreLemmas.v && coqc KMPSpec.v
```

## The plan

The proof is built in layers, each committed independently once it
compiles clean (`coqc` exit 0) with **zero `Admitted`/`admit`**:

1. **Embed and parse the real bytecode** (`KMPBytes.v`) — the literal
   compiled bytes of `kmp.wasm` are embedded as a Coq byte-list literal
   and run through WasmCert-Coq's certified binary parser
   (`run_parse_module`). Every later theorem is about *this* parsed
   module, so it's a proof about the actual shipped artifact, not a
   hand-transcribed approximation of it.

2. **Core reduction lemmas** (`CoreLemmas.v`) — structural lemmas
   derived from the reduction relation's context-filling machinery
   (`r_label` / `lfill`), most importantly `reduce_prefix`: reducing the
   front of an instruction sequence reduces the whole sequence, with any
   fixed suffix left untouched. This is what makes it possible to reason
   about a straight-line run of instructions one step at a time instead
   of re-deriving evaluation-context congruence by hand every time.
   Also instantiates WasmCert-Coq's abstract `host` typeclass with its
   own "no host functions" instance, since `kmp.wasm` has no imports.

3. **Declarative specification** (`KMPSpec.v`) — states what "correct"
   means for each function, in plain mathematics with no reference to
   the KMP algorithm itself:
   - `occurs_at` / `is_first_occurrence` — substring occurrence, the
     spec for `kmp_search`.
   - `is_border` / `is_lps` / `is_failure_table` — the failure ("lps")
     table as the length of the longest proper border of each prefix,
     the spec for `build_lps`. `is_lps_unique` confirms this pins down
     a unique value, so it fully specifies the function.

4. **`build_lps` loop correctness** *(in progress)* — prove that
   executing `build_lps`'s instruction sequence (as parsed in step 1,
   from a real reduction-relation initial state: pattern bytes in
   memory, bounded length) reduces, via `reduce_trans`, to a final state
   whose memory satisfies `is_failure_table` from step 3. By strong
   induction on the decreasing measure `patLen - i`.

5. **`kmp_search` loop correctness** *(planned)* — same shape, against
   `is_first_occurrence` / `does_not_occur`, additionally reasoning
   through `kmp_search`'s internal call into `build_lps` (step 4 as a
   lemma) and a KMP potential-function argument (`2*i - j` strictly
   increases every step) for termination.

6. **Real instantiation** *(planned)* — use WasmCert-Coq's
   `interp_instantiate_sound` to connect the parsed module (step 1) to
   an actual store/instance, so the final top-level theorem is stated
   about invoking the real exported `kmp_search` function, not an
   assumed environment. Explicit hypotheses (length bounds, memory
   layout / non-aliasing) are documented at the theorem, not hidden.

Steps 4–6 are the bulk of the remaining work: each loop iteration
unfolds through roughly 15–20 chained instruction-level reduction steps
(locals get/set, i32 binops/relops with explicit range side-conditions
for wraparound semantics, byte-level load/store), which then feed a
loop-invariant induction.

## Status

| File | Status |
|---|---|
| `KMPBytes.v` | done |
| `CoreLemmas.v` | done |
| `KMPSpec.v` | done |
| `build_lps` correctness | not started |
| `kmp_search` correctness | not started |
| Real instantiation / top-level theorem | not started |

## Why this scope

An earlier alternative — proving correctness of a Coq model transcribed
instruction-for-instruction from `kmp.wat`, rather than the actual
parsed `.wasm` bytes reduced under WasmCert-Coq's real semantics — was
considered and rejected in favor of the harder, real-bytecode version.
That tradeoff (much larger scope, real risk of not finishing) was made
explicitly and knowingly.

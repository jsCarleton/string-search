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
coqc KMPBytes.v && coqc CoreLemmas.v && coqc KMPSpec.v && coqc KMPFailureRec.v && coqc MemLemmas.v
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

4. **`build_lps` loop correctness** *(in progress)*, split into two
   parts:
   - 4a. **The failure-function recurrence, in pure math** (`KMPFailureRec.v`,
     done) — independent of WebAssembly entirely: proves the classical
     fact that justifies the algorithm's backtracking step (falling
     back to `table[len-1]` on a mismatch rather than recomputing from
     scratch). Built on a "border chain" lemma (borders of borders) and
     a fuel-bounded reference recurrence `cand`/`cand_correct` that is
     proved to compute exactly the `is_lps` spec value at each position,
     given the loop invariant `is_border` + `ruled_out_above` ("no
     larger border has been missed yet").
   - 4b. **The wasm loop implements that recurrence** *(in progress)* —
     show `build_lps`'s actual instruction sequence (as parsed in step
     1), executed via `reduce_trans` from a real initial configuration
     (pattern bytes in memory, bounded length), maintains the same
     `is_border` + `ruled_out_above` invariant at each `loop` iteration
     and its final memory state matches `cand`'s output, hence (by 4a)
     `is_failure_table`. Split further:
     - **Memory reasoning** (`MemLemmas.v`, done) — what
       `i32.load8_u`/`i32.store`/`i32.load` do to WasmCert-Coq's
       abstract `Memory` typeclass: single-byte read/write
       (`write_bytes_in`/`_out`, `load8_u_ok`), the i32 store/load round
       trip (`store_i32_effect`, `load_i32_after_store` — built from
       CompCert's type-agnostic `decode_encode_int` plus
       `Wasm_int.Int32`'s own `repr`/`unsigned` round trip, since
       `Wasm_int.Int32.int` and CompCert's `Integers.Int.int` are
       distinct types from separate functor instantiations), and
       non-interference outside a store's range
       (`mem_lookup_after_store_i32_disjoint`).
     - **Instruction-level reduction lemmas** *(not started)* — lifting
       `CoreLemmas.v`'s composition lemma through each concrete
       instruction `build_lps` uses (locals get/set, i32 const/binop/
       relop/testop, `block`/`loop`/`br_if`/`br`/`if`), using
       `MemLemmas.v` for the load/store steps.
     - **The loop induction itself** *(not started)* — one per-iteration
       lemma (chaining the instruction-level steps above) proved by
       strong induction on the KMP loop's own measure, mirroring
       `KMPFailureRec.v`'s `cand_fuel` structure step for step.

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
| `KMPFailureRec.v` (failure-recurrence math, step 4a) | done |
| `MemLemmas.v` (memory reasoning, step 4b) | done |
| Instruction-level reduction lemmas (step 4b) | not started |
| `build_lps` loop induction (step 4b) | not started |
| `kmp_search` correctness | not started |
| Real instantiation / top-level theorem | not started |

## Why this scope

An earlier alternative — proving correctness of a Coq model transcribed
instruction-for-instruction from `kmp.wat`, rather than the actual
parsed `.wasm` bytes reduced under WasmCert-Coq's real semantics — was
considered and rejected in favor of the harder, real-bytecode version.
That tradeoff (much larger scope, real risk of not finishing) was made
explicitly and knowingly.

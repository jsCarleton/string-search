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
coqc KMPBytes.v && coqc CoreLemmas.v && coqc KMPSpec.v && coqc KMPFailureRec.v && \
  coqc MemLemmas.v && coqc BuildLps.v && coqc BuildLpsLoop.v && \
  coqc Int32Facts.v && coqc BuildLpsExit.v && coqc BuildLpsCmp.v && coqc BuildLpsMatch.v && \
  coqc BuildLpsMismatch.v && coqc BuildLpsIterate.v && coqc BuildLpsMemTable.v && \
  coqc BuildLpsInduction.v && coqc BuildLpsInit.v && coqc BuildLpsRun.v && coqc BuildLpsTop.v
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

4. **`build_lps` loop correctness** *(done)*, split into two
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
   - 4b. **The wasm loop implements that recurrence** *(done)* —
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
     - **Instruction-level reduction and the prologue** (`BuildLps.v`,
       done) — lifting `CoreLemmas.v`'s composition lemmas through
       each concrete instruction `build_lps` uses. `build_lps_es_split`
       anchors to the actual parsed body (`vm_compute`, not a
       transcription); `build_lps_patLen_zero` proves the early-return
       case (`patLen = 0`) fully, including hand-constructing the
       `lholed`/`lfill` witness for `rs_return` at the right label
       nesting depth -- the first proof of *actual kmp.wasm code*
       reducing under the real semantics, not just supporting
       infrastructure.
     - **The main loop** *(done)*. `BuildLpsLoop.v` extracts the
       loop's exact instruction shape (init sequence, loop body) by
       `vm_compute` against the real bytecode. `Int32Facts.v` gives the
       loop proof a clean `Z`-arithmetic interface to i32 comparisons/
       arithmetic (`enc : Z -> i32` plus round-trip and operation
       lemmas), for values (counters, offsets) known to stay well
       within signed range. `BuildLpsExit.v` proves loop entry
       (`block`+`loop`, via `r_block` then `r_loop`) and the exit path
       (`i >= patLen`, so the check's `br_if 1` escapes both the loop's
       own label and the enclosing block's label in one `rs_br` step,
       collapsing the call frame to `[]`). `BuildLpsCmp.v` proves the
       next 9 instructions: loading `p[i]` and `p[len]` via
       `i32.load8_u` (`MemLemmas.v`'s `load8_u_value`) and comparing
       them — the shared prefix both branches below start from.
       `BuildLpsMatch.v` proves the match branch in full (`len++;
       lps[i] := len; i++`, including the real `i32.store`).
       `BuildLpsMismatch.v` proves the mismatch branch: the nested
       `len != 0` check (`ROI_ne`'s `app_relop` unfolds through the
       mixin field `Wasm_int.int_ne`, one layer deeper than `ROI_eq`/
       `ROI_ge`, which land straight on `Wasm_int.Int32.eq`/`.lt`);
       backtrack (`len := lps[len-1]`, a real `i32.load` reading a
       table entry written by an *earlier* iteration, via a new
       `MemLemmas.v` lemma `load_i32_value` taking a bare `read_bytes`
       fact rather than `load_i32_after_store`'s `store`-based one);
       and give-up (`lps[i] := 0; i++`, structurally `BuildLpsMatch.v`'s
       store-then-increment segments with `0` in place of `len+1`).
       Assembling `if`/`block`/label entry into the taken branch (shared
       by both the match and mismatch branches, and generic enough to
       land in `CoreLemmas.v` as `reduce_trans_if_true`/
       `reduce_trans_if_false`) needed one new piece of congruence
       plumbing: `rs_if_true`/`rs_if_false` turn the `if` into a
       `block`, `r_block` opens it into an `AI_label`, the branch body
       runs to `[::]` inside that label via `reduce_trans_label1'`, and
       `rs_label_const` (vacuously, on the empty value list) collapses
       the now-empty label away -- so the whole `if` resolves straight
       to `[::]` with no leftover wrapper for the caller to unwrap.
       `BuildLpsIterate.v` closes the loop: `build_lps_check_continue`
       is the mirror image of `BuildLpsExit.v`'s exit case (`i < patLen`,
       so `br_if 1` is a no-op instead of firing); `loop_body_to_reentry`
       is the generic (branch-independent) "close out one pass" step --
       `br 0` targets the loop's own label, and per `r_loop`'s
       definition that label's continuation content is literally the
       `loop` instruction itself, so `rs_br` at a trivial
       (`LH_base [::] [::]`) context hands back `[loop ...]`, which one
       more `r_loop` step turns back into the same labelled shape
       `loop_entry_cfg` expects. Chaining check + load/compare + branch
       + reentry gives three theorems, one per outcome
       (`build_lps_iterate_match`/`_backtrack`/`_giveup`), each proving
       a full non-exiting pass reduces `loop_entry_cfg f` all the way
       back to `loop_entry_cfg` of the updated locals/memory -- the
       three cases the eventual per-iteration induction will case on.
       `BuildLpsMemTable.v` adds the memory-level plumbing needed next:
       the bridge between the WASM-level `lps` array (four bytes per entry, at
       `lpsPtr + 4*j`) and `KMPFailureRec.v`'s plain `table : list nat`.
       `lps_mem_matches m lpsPtr table n` says the two agree below `n`;
       `lps_mem_matches_extend` shows writing a new entry (as the match/
       give-up branches do) extends this from `n` to `n+1`, via a new
       `read_bytes_write_bytes_disjoint` non-interference lemma (the
       four-byte-range analogue of `MemLemmas.v`'s single-byte
       `write_bytes_out`) applied to every earlier, untouched slot.
       Getting this file to compile surfaced a sharper form of a
       recurring gotcha: `ssrnat`'s `+`/`<=`/`<` overrides are not
       reliably escaped by a `%coq_nat` or `%nat` scope delimiter on the
       *outer* expression -- `lia` would fail on goals as simple as
       `m < m + n'.+1` with "Cannot find witness" even though the goal
       *displays* using Peano notation, because the delimiter doesn't
       propagate into subterms the way it looks like it should. The
       reliable fix is the one used throughout this proof: name the
       operations directly (`Nat.lt`, `Nat.le`, `Nat.add`) instead of
       leaning on notation at all. `BuildLpsMemTable.v` also adds
       `pat_mem_matches`, the read-only counterpart bridging the
       pattern bytes in memory to the plain `p : list byte`
       `KMPFailureRec.v` reasons about (no "extend" lemma needed, since
       the pattern never changes across the loop).

       `BuildLpsInduction.v` closes step 4b's hardest remaining piece:
       `build_lps_group_fuel` is structural induction on a `fuel`
       parameter that mirrors `KMPFailureRec.v`'s `cand_fuel` recursion
       instruction for instruction -- `build_lps_iterate_backtrack` *is*
       `cand_fuel`'s recursive call, and `build_lps_iterate_match`/
       `_giveup` are its two base cases -- so the theorem proves the
       WASM loop computes exactly `cand_fuel`'s value while performing
       the matching real `reduce_trans`, for an arbitrary run of
       zero-or-more backtracks followed by a match or give-up. One
       subtlety the proof had to account for: `build_lps_iterate_
       backtrack`'s resulting frame sets *both* the `len` *and* the
       scratch `tmp` local to the backtracked-to value (matching the
       real WAT, which reuses `tmp` as scratch and never resets it) --
       so unlike every other quantity, `tmpN` cannot be fixed across the
       induction and had to move into the per-recursive-call
       quantification (existentially in the conclusion, universally in
       the hypothesis) rather than staying a top-level parameter.
       `BuildLpsInit.v` proves the prologue's `patLen <> 0` case
       (mirroring `BuildLps.v`'s `patLen = 0` case) and the loop's
       7-instruction init sequence (`lps[0] := 0; len := 0; i := 1`),
       but deliberately stops short of chaining them into
       `loop_entry_cfg` — doing so surfaced a real structural gap: the
       actual function-call convention (`r_invoke_native`, confirmed in
       `opsem.v`) wraps a called function's body in an extra label
       beyond what `loop_entry_cfg` (and everything built on it since,
       through `BuildLpsInduction.v`) assumes. Every `br 1` witness
       built so far escapes exactly 2 labels (loop + block); connecting
       to a real call needs them one layer deeper. This is exactly the
       kind of seam step 6 (real instantiation) exists to handle, and
       is called out explicitly there rather than patched in a hurry
       across already-verified files.

       **`BuildLpsRun.v` completes step 4b**: `build_lps_run`, by
       induction on the number of positions remaining, chains
       `build_lps_group_fuel` (one call per position) through to
       `build_lps_exit` (once `i` reaches `length p`), producing a
       theorem that covers the *entire* loop from any valid entry point
       through to completion. `build_lps_run_is_failure_table` restates
       the result directly against `KMPSpec.is_failure_table`. Getting
       here required three more invariants to be threaded explicitly
       through `build_lps_group_fuel`'s conclusion that weren't needed
       within a single position but are needed to *chain* positions:
       memory length is preserved (`operations.mem_length m' =
       operations.mem_length m`, via `MemLemmas.v`'s
       `write_bytes_mem_length`), the pattern buffer survives a write
       into the disjoint `lps` output array (`pat_mem_matches m' patPtr
       p`, via a new non-aliasing hypothesis between the two regions and
       `write_bytes_out`'s non-interference), and the scratch `tmp`
       local stays in range (`small tmpN'`). Each was a mechanical
       three-branch addition (match/give-up/backtrack) once identified,
       but none were visible until the outer induction actually tried to
       *use* the group theorem's output as the next call's input.

       **Closing the label-depth seam** (`BuildLpsTop.v`, completes step
       4b): every theorem from `BuildLpsIterate.v` through
       `BuildLpsRun.v` first got an additive `_bare` companion — the
       identical fact, proved the identical way, but without the
       `AI_frame 0 _ f0` wrapping the original theorems carried only so
       later files would have something frame-shaped to plug into each
       other (`build_lps_iterate_match_bare`/`_backtrack_bare`/
       `_giveup_bare`, `build_lps_exit_bare`, `build_lps_group_fuel_bare`,
       `build_lps_run_bare`). Every pre-existing theorem's statement was
       left byte-for-byte unchanged — each became, where applicable, a
       one-line corollary of its `_bare` sibling via `reduce_trans_frame'`
       — so this was zero-risk to everything already verified.
       `build_lps_correct` then chains the unframed facts start to
       finish (`build_lps_patLen_nonzero_pre`, `build_lps_init_store`,
       `build_lps_init_locals`, `build_lps_loop_entry`,
       `build_lps_run_bare`) into one `reduce_trans` fact with no framing
       at all, and lifts *that* through exactly one label
       (`reduce_trans_label1'`) plus the calling frame
       (`reduce_trans_frame'`) — the same "lift through a congruence
       label, then collapse via `rs_label_const`/`rs_local_const`"
       technique `BuildLps.v`'s `build_lps_patLen_zero` already used
       end-to-end for the early-return case. The result is stated
       directly against the real `r_invoke_native` call shape
       (`AI_frame 0 f_entry [AI_label 0 [::] (to_e_list build_lps_body)]`,
       confirmed against `opsem.v:244-255`) reducing all the way to
       `[::]`, for any nonempty pattern — `build_lps`'s genuine top-level
       correctness theorem, not one that assumes away the calling
       convention.

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
   (The label-depth seam noted under `BuildLpsInit.v` above — connecting
   `r_invoke_native`'s real calling convention to the loop-level
   reasoning — is already closed, for `build_lps`, by `BuildLpsTop.v`;
   what's left here is the analogous instantiation step for the whole
   module/store, plus the same connection for `kmp_search` once step 5
   is done.)

Steps 5–6 are the bulk of the remaining work: each loop iteration
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
| `BuildLps.v`: prologue / early return (step 4b) | done |
| `BuildLpsLoop.v`: loop instruction shape, ground truth (step 4b) | done |
| `Int32Facts.v`: small-value i32 arithmetic (step 4b) | done |
| `BuildLpsExit.v`: loop entry + exit path (step 4b) | done |
| `BuildLpsCmp.v`: load p[i]/p[len] + compare (step 4b) | done |
| `BuildLpsMatch.v`: match branch (step 4b) | done |
| `BuildLpsMismatch.v`: mismatch branch (backtrack / give-up) (step 4b) | done |
| `BuildLpsIterate.v`: loop continuation (`br 0`), per-outcome iterate theorems (step 4b) | done |
| `BuildLpsMemTable.v`: WASM `lps` array &harr; Coq `table : list nat` bridge, plus read-only `pat_mem_matches` (step 4b) | done |
| `BuildLpsInduction.v`: `build_lps_group_fuel`, per-group induction matching `cand_fuel` (step 4b) | done |
| `BuildLpsInit.v`: prologue `patLen<>0` case + 7-instr init sequence, unchained (step 4b) | done |
| `BuildLpsRun.v`: outer induction over `i`, `is_failure_table` (step 4b) | done |
| `BuildLpsTop.v`: `build_lps_correct`, real call-shaped top-level theorem (step 4b) | done |
| `kmp_search` correctness | not started |
| Real instantiation / top-level theorem | not started |

## Why this scope

An earlier alternative — proving correctness of a Coq model transcribed
instruction-for-instruction from `kmp.wat`, rather than the actual
parsed `.wasm` bytes reduced under WasmCert-Coq's real semantics — was
considered and rejected in favor of the harder, real-bytecode version.
That tradeoff (much larger scope, real risk of not finishing) was made
explicitly and knowingly.

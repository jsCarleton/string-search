(** Ground truth for build_lps's main loop, extracted from the actual
    parsed bytecode (KMPBytes.v via BuildLps.v) by [vm_compute] rather
    than transcribed by hand. This isolates the loop's exact instruction
    shape -- the 7-instruction init sequence ([lps[0] := 0; len := 0;
    i := 1]) followed by the [block [loop ...]] -- so the reduction
    proof (in progress) can refer to it symbolically instead of re-doing
    this extraction inline. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.

(** [build_lps_es_rest] (everything after the 3-instruction prologue,
    from BuildLps.v) is the 7-instruction init sequence followed by the
    single [block [loop ...]] instruction. *)
Definition build_lps_init_es : list administrative_instruction :=
  Eval vm_compute in List.firstn 7 build_lps_es_rest.

Definition build_lps_block_es : administrative_instruction :=
  Eval vm_compute in List.nth 7 build_lps_es_rest (AI_basic BI_nop).

Lemma build_lps_es_rest_split : build_lps_es_rest = build_lps_init_es ++ [build_lps_block_es].
Proof. vm_compute. reflexivity. Qed.

(** The init sequence, spelled out: [lps[0] := 0; len := 0; i := 1]. *)
Lemma build_lps_init_es_eq :
  build_lps_init_es =
    [AI_basic (BI_local_get 2); AI_basic (BI_const_num (VAL_int32 zero32));
     AI_basic (BI_store T_i32 None (Build_memarg 0 2));
     AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 3);
     AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_local_set 4)].
Proof. vm_compute. reflexivity. Qed.

(** The loop body (15 instructions): the exit check ([i >= patLen] via
    [br_if 1]), the two byte loads and comparison, and the match/
    mismatch branches ending in [br 0]. *)
Definition build_lps_loop_body : list basic_instruction :=
  Eval vm_compute in
  match build_lps_block_es with
  | AI_basic (BI_block _ [BI_loop _ lb]) => lb
  | _ => []
  end.

Lemma build_lps_block_es_eq :
  build_lps_block_es =
    AI_basic (BI_block (BT_valtype None) [BI_loop (BT_valtype None) build_lps_loop_body]).
Proof. vm_compute. reflexivity. Qed.

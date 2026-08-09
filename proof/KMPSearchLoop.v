(** Ground truth for kmp_search's main body, extracted from the actual
    parsed bytecode (KMPBytes.v via KMPSearch.v) by [vm_compute] rather
    than transcribed by hand -- the [kmp_search] analogue of
    [BuildLpsLoop.v]. [kmp_search_es_rest] (everything after the
    3-instruction prologue) splits into: the call into [build_lps] (4
    instructions), the 2-local init sequence ([i := 0; j := 0], 4
    instructions), the single [block [loop ...]] instruction, and the
    final fallback [i32.const -1] (the implicit "not found" return
    value once the loop falls through). *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps Int32Facts KMPSearch.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.

Definition kmp_search_call_es : list administrative_instruction :=
  Eval vm_compute in List.firstn 4 kmp_search_es_rest.

Definition kmp_search_after_call_es : list administrative_instruction :=
  Eval vm_compute in List.skipn 4 kmp_search_es_rest.

Definition kmp_search_init_es : list administrative_instruction :=
  Eval vm_compute in List.firstn 4 kmp_search_after_call_es.

Definition kmp_search_after_init_es : list administrative_instruction :=
  Eval vm_compute in List.skipn 4 kmp_search_after_call_es.

Definition kmp_search_block_es : administrative_instruction :=
  Eval vm_compute in List.nth 0 kmp_search_after_init_es (AI_basic BI_nop).

(** The final fallback: [i32.const -1], reached only once the loop
    exits via [br_if 1] (no match found before [i >= textLen]). *)
Definition kmp_search_final_es : list administrative_instruction :=
  Eval vm_compute in List.skipn 1 kmp_search_after_init_es.

Lemma kmp_search_es_rest_split :
  kmp_search_es_rest = kmp_search_call_es ++ kmp_search_init_es ++ [kmp_search_block_es] ++ kmp_search_final_es.
Proof. vm_compute. reflexivity. Qed.

Lemma kmp_search_call_es_eq :
  kmp_search_call_es =
    [AI_basic (BI_local_get 2); AI_basic (BI_local_get 3);
     AI_basic (BI_local_get 4); AI_basic (BI_call 0)].
Proof. vm_compute. reflexivity. Qed.

(** The init sequence, spelled out: [i := 0; j := 0]. *)
Lemma kmp_search_init_es_eq :
  kmp_search_init_es =
    [AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 5);
     AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 6)].
Proof. vm_compute. reflexivity. Qed.

Lemma kmp_search_final_es_eq :
  kmp_search_final_es = [AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (-1))))].
Proof. vm_compute. reflexivity. Qed.

(** The loop body (18 instructions): the exit check ([i >= textLen] via
    [br_if 1]), the two byte loads and comparison, and the match/
    mismatch branches (match possibly returning early), ending in
    [br 0]. *)
Definition kmp_search_loop_body : list basic_instruction :=
  Eval vm_compute in
  match kmp_search_block_es with
  | AI_basic (BI_block _ [BI_loop _ lb]) => lb
  | _ => []
  end.

Lemma kmp_search_block_es_eq :
  kmp_search_block_es =
    AI_basic (BI_block (BT_valtype None) [BI_loop (BT_valtype None) kmp_search_loop_body]).
Proof. vm_compute. reflexivity. Qed.

(** The configuration reached immediately after (re-)entering the loop:
    the block's label wrapping the loop's own label wrapping the loop
    body -- the [kmp_search] analogue of [BuildLpsExit.v]'s
    [loop_entry_cfg]. *)
Definition search_loop_entry_cfg (f : frame) : list administrative_instruction :=
  [AI_label 0 [] [AI_label 0 [AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
                    (to_e_list kmp_search_loop_body)]].

(** locals 0..6 = textPtr, textLen, patPtr, patLen, lpsPtr, i, j. *)
Definition search_frame (inst : moduleinst) (textPtr textLenN patPtr patLenN lpsPtr iN jN : Z) : frame :=
  Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
               VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
               VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 (enc iN));
               VAL_num (VAL_int32 (enc jN))] inst.

Lemma search_loop_entry : forall hs s f,
  reduce_trans (hs, s, f, [kmp_search_block_es]) (hs, s, f, search_loop_entry_cfg f).
Proof.
  move=> hs s f.
  rewrite kmp_search_block_es_eq.
  have HBlk : reduce hs s f [:: AI_basic (BI_block (BT_valtype None) [BI_loop (BT_valtype None) kmp_search_loop_body])]
                      hs s f [:: AI_label 0 [::] (to_e_list [BI_loop (BT_valtype None) kmp_search_loop_body])].
  { apply r_block with (vs := [::]) (n := 0%nat) (m := 0%nat) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  have HLoop : reduce hs s f [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
                       hs s f [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
                                    (to_e_list kmp_search_loop_body)].
  { apply r_loop with (vs := [::]) (n := 0%nat) (m := 0%nat) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  have HLoop' := reduce_label1 _ _ _ _ _ _ _ _ 0 [::] HLoop.
  apply: (reduce_trans_trans _ (hs,s,f,_) _).
  - exact: (reduce_trans_step _ _ _ _ _ _ _ _ HBlk).
  - exact: (reduce_trans_step _ _ _ _ _ _ _ _ HLoop').
Qed.

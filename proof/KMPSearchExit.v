(** [kmp_search]'s loop exit path: the [i >= textLen] check succeeding,
    so [br_if 1] escapes the loop entirely -- the [kmp_search] analogue
    of [BuildLpsExit.v]'s exit case. Structurally identical technique
    (same [rs_br] witness shape, one label between the [br]'s occurrence
    and its target), adapted for kmp_search's local indices ([i] is
    local 5, not build_lps's local 4) and for landing on
    [kmp_search_final_es] (the trailing [i32.const -1] fallback) rather
    than [::], since kmp_search's loop isn't the last thing in the
    function body. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps Int32Facts KMPSearch KMPSearchLoop.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** The loop body's first 4 instructions ([local.get 5; local.get 1;
    i32.ge_s; br_if 1], i.e. the [i >= textLen] exit check), spelled out
    against the real bytecode via [vm_compute]; [search_loop_after_check_es]
    is everything after. *)
Definition search_loop_body_es : list administrative_instruction :=
  Eval vm_compute in to_e_list kmp_search_loop_body.
Definition search_loop_after_check_es : list administrative_instruction :=
  Eval vm_compute in List.skipn 4 search_loop_body_es.

Lemma search_loop_body_es_split :
  to_e_list kmp_search_loop_body =
    [AI_basic (BI_local_get 5%N); AI_basic (BI_local_get 1%N);
     AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] ++ search_loop_after_check_es.
Proof. vm_compute. reflexivity. Qed.

(** [_bare] version, following [BuildLpsExit.v]'s [build_lps_exit_bare]
    naming: the same fact without any [AI_frame]/ambient-caller wrapping.
    Lands on [kmp_search_final_es] (not [::]), since escaping the loop's
    block only drains the block itself -- the trailing
    [i32.const -1] fallback that follows the block in the function body
    is untouched, carried through the whole chain as a fixed suffix. *)
Lemma kmp_search_exit_bare : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN,
  small textPtr -> small textLenN -> small patPtr -> small patLenN -> small lpsPtr -> small iN -> small jN ->
  textLenN <= iN ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  reduce_trans (hs, s, f, search_loop_entry_cfg f ++ kmp_search_final_es) (hs, s, f, kmp_search_final_es).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hge f.
  rewrite /search_loop_entry_cfg.
  (* local.get 5 (i) *)
  have HA : reduce hs s f [:: AI_basic (BI_local_get 5%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 5%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 1%N); AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] HA.
  simpl in HA'.
  (* local.get 1 (textLen) *)
  have HB : reduce hs s f [:: AI_basic (BI_local_get 1%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc textLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc textLenN))) (j := 1%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc iN))] _ _ _ _ _
    [:: AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] HB.
  simpl in HB'.
  (* i32.ge_s: true, since textLenN <= iN *)
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN))); AI_basic (BI_const_num (VAL_int32 (enc textLenN)));
                              AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S)))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 one32))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (enc iN)) (VAL_int32 (enc textLenN)) T_i32 (Relop_i (ROI_ge SX_S)).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc iN)) (VAL_int32 (enc textLenN)) T_i32 (Relop_i (ROI_ge SX_S)) Htc) as Hstep.
    move: Hstep.
    rewrite /app_relop /=.
    have Hlt : Wasm_int.Int32.lt (enc iN) (enc textLenN) = false.
    { rewrite /Wasm_int.Int32.lt (enc_signed iN Hp6) (enc_signed textLenN Hp2).
      case: (Coqlib.zlt iN textLenN) => Hz; [lia | reflexivity]. }
    rewrite Hlt /=.
    move=> H. exact H. }
  have HC' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_br_if 1%N)] HC.
  simpl in HC'.
  (* br_if 1: fires, since the top of stack is true (one32) *)
  have HD : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_br_if 1%N)]
                    hs s f [:: AI_basic (BI_br 1%N)].
  { apply reduce_simple_reduce.
    apply rs_br_if_true.
    rewrite /one32.
    move=> Hz.
    have : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 1) = Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 0).
    { f_equal. exact Hz. }
    vm_compute. lia. }
  rewrite search_loop_body_es_split.
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC'.
  have Step4 := reduce_trans_step _ _ _ _ _ _ _ _ HD.
  have Chain12 := reduce_trans_trans _ _ _ Step1 Step2.
  have Chain123 := reduce_trans_trans _ _ _ Chain12 Step3.
  have Hchain := reduce_trans_trans _ _ _ Chain123 Step4.
  have Hchain' := reduce_trans_prefix' _ _ _ _ _ _ _ _ search_loop_after_check_es Hchain.
  (* br 1, now visible inside the loop label (itself inside the block
     label), collapses both directly to [] via rs_br: the loop label is
     the sole layer between the br's occurrence and its target, the
     block label. *)
  have Hbr : reduce hs s f
    [:: AI_label 0 [::]
          [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
                ([:: AI_basic (BI_br 1%N)] ++ search_loop_after_check_es)]]
    hs s f [::].
  { apply reduce_simple_reduce.
    apply (@rs_br 0 [::] [::] 1
      [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
            ([:: AI_basic (BI_br 1%N)] ++ search_loop_after_check_es)]
      (LH_rec [::] 0 [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
               (LH_base [::] search_loop_after_check_es) [::]));
      try reflexivity. }
  have HlabLoop := reduce_trans_label1' _ _ _ _ _ _ _ _ 0
    [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)] Hchain'.
  have HlabBlock := reduce_trans_label1' _ _ _ _ _ _ _ _ 0 [::] HlabLoop.
  have Hcollapse := reduce_trans_trans _ _ _ HlabBlock (reduce_trans_step _ _ _ _ _ _ _ _ Hbr).
  have Hcollapse' := reduce_trans_prefix' _ _ _ _ _ _ _ _ kmp_search_final_es Hcollapse.
  rewrite List.app_nil_l in Hcollapse'.
  exact Hcollapse'.
Qed.

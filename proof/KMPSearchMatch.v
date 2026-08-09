(** [kmp_search]'s match branch (bytes equal): [i++; j++], then check
    whether [j] has reached [patLen]. Unlike [build_lps]'s match branch
    (which stores a new [lps] entry between its two increments), this
    one is a bare pair of local increments -- but it's followed by an
    extra nested check/[if] that [build_lps]'s match branch doesn't
    have, since finding the full pattern here means the search is done.
    This file covers the "not done yet" sub-case (j+1 <> patLen), which
    behaves like an ordinary loop continuation; the "done" sub-case
    (an explicit [return], escaping every enclosing label including the
    ones outside this file's reach) is handled separately. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps Int32Facts KMPSearch KMPSearchLoop
  KMPSearchExit KMPSearchCmp.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

Definition search_match_body_es : list administrative_instruction := Eval vm_compute in
  match search_loop_after_cmp_es with
  | AI_basic (BI_if _ mb _) :: _ => List.map AI_basic mb
  | _ => []
  end.

Lemma search_match_body_es_eq :
  search_match_body_es =
    [AI_basic (BI_local_get 5%N); AI_basic (BI_const_num (VAL_int32 one32));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 5%N);
     AI_basic (BI_local_get 6%N); AI_basic (BI_const_num (VAL_int32 one32));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 6%N);
     AI_basic (BI_local_get 6%N); AI_basic (BI_local_get 3%N); AI_basic (BI_relop T_i32 (Relop_i ROI_eq));
     AI_basic (BI_if (BT_valtype None)
       [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])].
Proof. vm_compute. reflexivity. Qed.

(** [i++]: [local 5 := local 5 + 1]. *)
Lemma search_seg1_i_inc : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN,
  small iN -> small (iN+1) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  let f1 := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) jN in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 5%N); AI_basic (BI_const_num (VAL_int32 one32));
        AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 5%N)])
    (hs, s, f1, [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN Hs1 Hs2 f f1.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 5%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 5%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_local_set 5%N)] HA.
  simpl in HA'.
  have HB : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN))); AI_basic (BI_const_num (VAL_int32 one32));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (iN+1))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc iN)) (VAL_int32 one32) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Hone : one32 = enc 1 by reflexivity.
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc iN)) (VAL_int32 one32) = Some (VAL_int32 (enc (iN+1))).
    { rewrite /app_binop /= Hone. f_equal. f_equal.
      have Hs1' : small 1 by rewrite /small; lia.
      exact: (add_enc iN 1 Hs1 Hs1' Hs2). }
    pose proof (@rs_binop_success (VAL_int32 (enc iN)) (VAL_int32 one32) (VAL_int32 (enc (iN+1)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HB' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_local_set 5%N)] HB.
  simpl in HB'.
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (iN+1)))); AI_basic (BI_local_set 5%N)]
                    hs s f1 [::].
  { pose proof (@r_local_set _ _ _ f f1 5%N (VAL_num (VAL_int32 (enc (iN+1)))) s (VAL_num (VAL_int32 (enc iN))) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f1 /search_frame /=. reflexivity.
    - rewrite /f /=. by [].
    - rewrite /f /f1 /search_frame /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  exact: (reduce_trans_trans _ _ _ C12 Step3).
Qed.

(** [j++]: [local 6 := local 6 + 1]. *)
Lemma search_seg2_j_inc : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN,
  small jN -> small (jN+1) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  let f1 := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN (jN+1) in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 6%N); AI_basic (BI_const_num (VAL_int32 one32));
        AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 6%N)])
    (hs, s, f1, [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN Hs1 Hs2 f f1.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 6%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc jN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc jN))) (j := 6%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_local_set 6%N)] HA.
  simpl in HA'.
  have HB : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc jN))); AI_basic (BI_const_num (VAL_int32 one32));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (jN+1))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc jN)) (VAL_int32 one32) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Hone : one32 = enc 1 by reflexivity.
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc jN)) (VAL_int32 one32) = Some (VAL_int32 (enc (jN+1))).
    { rewrite /app_binop /= Hone. f_equal. f_equal.
      have Hs1' : small 1 by rewrite /small; lia.
      exact: (add_enc jN 1 Hs1 Hs1' Hs2). }
    pose proof (@rs_binop_success (VAL_int32 (enc jN)) (VAL_int32 one32) (VAL_int32 (enc (jN+1)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HB' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_local_set 6%N)] HB.
  simpl in HB'.
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (jN+1)))); AI_basic (BI_local_set 6%N)]
                    hs s f1 [::].
  { pose proof (@r_local_set _ _ _ f f1 6%N (VAL_num (VAL_int32 (enc (jN+1)))) s (VAL_num (VAL_int32 (enc jN))) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f1 /search_frame /=. reflexivity.
    - rewrite /f /=. by [].
    - rewrite /f /f1 /search_frame /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  exact: (reduce_trans_trans _ _ _ C12 Step3).
Qed.

(** The "not done yet" sub-case: after [i++;j++], [j+1 <> patLenN], so
    the inner [if]'s check is false and its (empty) false branch drains
    to [::] via [CoreLemmas.reduce_trans_if_false]. *)
Lemma kmp_search_match_continue : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN,
  small iN -> small (iN+1) -> small jN -> small (jN+1) -> small patLenN -> jN + 1 <> patLenN ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) (jN+1) in
  reduce_trans (hs, s, f, search_match_body_es) (hs, s, f', [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN Hi Hi1 Hj Hj1 Hpat Hne f f'.
  rewrite search_match_body_es_eq.
  have Hseg1 := search_seg1_i_inc hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN Hi Hi1.
  simpl in Hseg1.
  have Hseg2 := search_seg2_j_inc hs s inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) jN Hj Hj1.
  simpl in Hseg2.
  set f1 := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) jN.
  have Hseg1' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 6%N); AI_basic (BI_const_num (VAL_int32 one32));
        AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 6%N);
        AI_basic (BI_local_get 6%N); AI_basic (BI_local_get 3%N); AI_basic (BI_relop T_i32 (Relop_i ROI_eq));
        AI_basic (BI_if (BT_valtype None)
          [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])] Hseg1.
  rewrite List.app_nil_l in Hseg1'.
  have Hseg2' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 6%N); AI_basic (BI_local_get 3%N); AI_basic (BI_relop T_i32 (Relop_i ROI_eq));
        AI_basic (BI_if (BT_valtype None)
          [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])] Hseg2.
  rewrite List.app_nil_l in Hseg2'.
  have Hchain12 := reduce_trans_trans _ _ _ Hseg1' Hseg2'.
  (* local.get 6; local.get 3; relop eq -- false, since j+1 <> patLenN *)
  have HD : reduce hs s f' [:: AI_basic (BI_local_get 6%N)] hs s f' [:: AI_basic (BI_const_num (VAL_int32 (enc (jN+1))))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc (jN+1)))) (j := 6%N). reflexivity. }
  have HD' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 3%N); AI_basic (BI_relop T_i32 (Relop_i ROI_eq));
        AI_basic (BI_if (BT_valtype None)
          [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])] HD.
  simpl in HD'.
  have HE : reduce hs s f' [:: AI_basic (BI_local_get 3%N)] hs s f' [:: AI_basic (BI_const_num (VAL_int32 (enc patLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patLenN))) (j := 3%N). reflexivity. }
  have HE' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc (jN+1)))] _ _ _ _ _
    [:: AI_basic (BI_relop T_i32 (Relop_i ROI_eq));
        AI_basic (BI_if (BT_valtype None)
          [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])] HE.
  simpl in HE'.
  have HF : reduce hs s f' [:: AI_basic (BI_const_num (VAL_int32 (enc (jN+1)))); AI_basic (BI_const_num (VAL_int32 (enc patLenN)));
                               AI_basic (BI_relop T_i32 (Relop_i ROI_eq))]
                    hs s f' [:: AI_basic (BI_const_num (VAL_int32 zero32))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (enc (jN+1))) (VAL_int32 (enc patLenN)) T_i32 (Relop_i ROI_eq).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc (jN+1))) (VAL_int32 (enc patLenN)) T_i32 (Relop_i ROI_eq) Htc) as Hstep.
    move: Hstep. rewrite /app_relop /=.
    have Heq : Wasm_int.Int32.eq (enc (jN+1)) (enc patLenN) = false.
    { rewrite /Wasm_int.Int32.eq (enc_unsigned (jN+1) Hj1) (enc_unsigned patLenN Hpat).
      case: (Coqlib.zeq (jN+1) patLenN) => Hz; [exfalso; apply Hne; exact Hz | reflexivity]. }
    rewrite Heq /=.
    move=> H. exact H. }
  have HF' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None)
          [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])] HF.
  simpl in HF'.
  have HG : reduce_trans (hs, s, f', [:: AI_basic (BI_const_num (VAL_int32 zero32));
                                          AI_basic (BI_if (BT_valtype None)
                                            [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])])
                          (hs, s, f', [::]).
  { apply: (reduce_trans_if_false hs s f' zero32
      [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [] hs s f').
    - reflexivity.
    - apply: Relations.Relation_Operators.rt_refl. }
  have Chain_DEF := reduce_trans_trans _ _ _ (reduce_trans_trans _ _ _ (reduce_trans_step _ _ _ _ _ _ _ _ HD') (reduce_trans_step _ _ _ _ _ _ _ _ HE')) (reduce_trans_trans _ _ _ (reduce_trans_step _ _ _ _ _ _ _ _ HF') HG).
  exact: (reduce_trans_trans _ _ _ Hchain12 Chain_DEF).
Qed.

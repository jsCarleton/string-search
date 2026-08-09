(** [kmp_search]'s match branch, final sub-case: [text[i] = pat[j]] and
    [j+1 = patLen], so the whole pattern has been found and the branch
    fires an explicit [return (i+1) - (j+1)]. Unlike every other
    "one iteration" theorem in this proof, [return] (per [rs_return]'s
    definition, opsem.v) reduces the *entire* enclosing [AI_frame] in a
    single step, so this theorem is necessarily stated at the fully
    wrapped, real-call-shaped level from the start -- there is no
    frame-free "_bare" version to build the way
    [KMPSearchIterate.v]'s continuation theorems were. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps Int32Facts KMPSearch KMPSearchLoop
  KMPSearchExit KMPSearchCmp KMPSearchMatch KMPSearchIterate.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** [i++;j++] then the inner check fires TRUE (j+1 = patLen): the [if]
    becomes a [block] becomes a fresh label wrapping [local.get 5;
    local.get 6; i32.sub; return], which is then run one step further
    (the load/load/sub) to expose the actual return value,
    [(i+1)-(j+1)], still sitting one label deep. *)
Lemma kmp_search_match_body_to_return : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN,
  small iN -> small (iN+1) -> small jN -> small (jN+1) -> jN <= iN -> jN + 1 = patLenN ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) (jN+1) in
  reduce_trans (hs, s, f, search_match_body_es)
    (hs, s, f', [:: AI_label 0 [::] [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1))))); AI_basic BI_return]]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN Hi Hi1 Hj Hj1 Hji Heq f f'.
  rewrite search_match_body_es_eq.
  have Hseg1 := search_seg1_i_inc hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN Hi Hi1.
  simpl in Hseg1.
  have Hseg2 := search_seg2_j_inc hs s inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) jN Hj Hj1.
  simpl in Hseg2.
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
  set f1 := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) (jN+1).
  (* local.get 6; local.get 3; relop eq -- true, since j+1 = patLenN *)
  have HD : reduce hs s f1 [:: AI_basic (BI_local_get 6%N)] hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (jN+1))))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc (jN+1)))) (j := 6%N). reflexivity. }
  have HD' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 3%N); AI_basic (BI_relop T_i32 (Relop_i ROI_eq));
        AI_basic (BI_if (BT_valtype None)
          [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])] HD.
  simpl in HD'.
  have HE : reduce hs s f1 [:: AI_basic (BI_local_get 3%N)] hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc patLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patLenN))) (j := 3%N). reflexivity. }
  have HE' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc (jN+1)))] _ _ _ _ _
    [:: AI_basic (BI_relop T_i32 (Relop_i ROI_eq));
        AI_basic (BI_if (BT_valtype None)
          [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])] HE.
  simpl in HE'.
  have HF : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (jN+1)))); AI_basic (BI_const_num (VAL_int32 (enc patLenN)));
                               AI_basic (BI_relop T_i32 (Relop_i ROI_eq))]
                    hs s f1 [:: AI_basic (BI_const_num (VAL_int32 one32))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (enc (jN+1))) (VAL_int32 (enc patLenN)) T_i32 (Relop_i ROI_eq).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc (jN+1))) (VAL_int32 (enc patLenN)) T_i32 (Relop_i ROI_eq) Htc) as Hstep.
    move: Hstep. rewrite /app_relop /=.
    have Heqb : Wasm_int.Int32.eq (enc (jN+1)) (enc patLenN) = true.
    { rewrite /Wasm_int.Int32.eq (enc_unsigned (jN+1) Hj1) -Heq (enc_unsigned (jN+1) Hj1).
      case: (Coqlib.zeq (jN+1) (jN+1)) => Hz; [reflexivity | exfalso; lia]. }
    rewrite Heqb /=.
    move=> H. exact H. }
  have HF' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None)
          [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])] HF.
  simpl in HF'.
  (* the "if" takes its true branch, becoming block[local.get5;local.get6;sub;return] *)
  have HG : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 one32));
                               AI_basic (BI_if (BT_valtype None)
                                 [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] [])]
                    hs s f1 [:: AI_basic (BI_block (BT_valtype None)
                                 [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return])].
  { apply reduce_simple_reduce.
    apply rs_if_true.
    rewrite /one32.
    move=> Hz.
    have : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 1) = Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 0).
    { f_equal. exact Hz. }
    vm_compute. lia. }
  have HH : reduce hs s f1 [:: AI_basic (BI_block (BT_valtype None)
                                 [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return])]
                    hs s f1 [:: AI_label 0 [::] [:: AI_basic (BI_local_get 5%N); AI_basic (BI_local_get 6%N);
                                                     AI_basic (BI_binop T_i32 (Binop_i BOI_sub)); AI_basic BI_return]].
  { apply r_block with (vs := [::]) (n := 0%nat) (m := 0%nat) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  (* now inside the fresh label, run local.get5;local.get6;sub to completion *)
  have HI : reduce hs s f1 [:: AI_basic (BI_local_get 5%N)] hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (iN+1))))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc (iN+1)))) (j := 5%N). reflexivity. }
  have HI' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 6%N); AI_basic (BI_binop T_i32 (Binop_i BOI_sub)); AI_basic BI_return] HI.
  simpl in HI'.
  have HJ : reduce hs s f1 [:: AI_basic (BI_local_get 6%N)] hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (jN+1))))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc (jN+1)))) (j := 6%N). reflexivity. }
  have HJ' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc (iN+1)))] _ _ _ _ _
    [:: AI_basic (BI_binop T_i32 (Binop_i BOI_sub)); AI_basic BI_return] HJ.
  simpl in HJ'.
  have Hji1 : jN + 1 <= iN + 1 by lia.
  have HK : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (iN+1)))); AI_basic (BI_const_num (VAL_int32 (enc (jN+1))));
                               AI_basic (BI_binop T_i32 (Binop_i BOI_sub))]
                    hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1)))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc (iN+1))) (VAL_int32 (enc (jN+1))) T_i32 (Binop_i BOI_sub).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_sub) (VAL_int32 (enc (iN+1))) (VAL_int32 (enc (jN+1))) = Some (VAL_int32 (enc ((iN+1)-(jN+1)))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (sub_enc (iN+1) (jN+1) Hi1 Hj1 Hji1). }
    pose proof (@rs_binop_success (VAL_int32 (enc (iN+1))) (VAL_int32 (enc (jN+1))) (VAL_int32 (enc ((iN+1)-(jN+1))))
      (Binop_i BOI_sub) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HK' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic BI_return] HK.
  simpl in HK'.
  have Cinner : reduce_trans (hs, s, f1, [:: AI_basic (BI_local_get 5%N); AI_basic (BI_local_get 6%N);
                                              AI_basic (BI_binop T_i32 (Binop_i BOI_sub)); AI_basic BI_return])
                              (hs, s, f1, [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1))))); AI_basic BI_return]).
  { have C1 := reduce_trans_trans _ _ _ (reduce_trans_step _ _ _ _ _ _ _ _ HI') (reduce_trans_step _ _ _ _ _ _ _ _ HJ').
    exact: (reduce_trans_trans _ _ _ C1 (reduce_trans_step _ _ _ _ _ _ _ _ HK')). }
  have Cinner' := reduce_trans_label1' _ _ _ _ _ _ _ _ 0 [::] Cinner.
  have Chain_DFGH := reduce_trans_trans _ _ _
    (reduce_trans_trans _ _ _ (reduce_trans_step _ _ _ _ _ _ _ _ HD') (reduce_trans_step _ _ _ _ _ _ _ _ HE'))
    (reduce_trans_trans _ _ _
      (reduce_trans_trans _ _ _ (reduce_trans_step _ _ _ _ _ _ _ _ HF') (reduce_trans_step _ _ _ _ _ _ _ _ HG))
      (reduce_trans_step _ _ _ _ _ _ _ _ HH)).
  have Chain_all := reduce_trans_trans _ _ _ Chain_DFGH Cinner'.
  exact: (reduce_trans_trans _ _ _ Hchain12 Chain_all).
Qed.

(** The outer [if] (comparing [text[i]] and [pat[j]]) taking its true
    branch, landing on [kmp_search_match_body_to_return]'s pre-return
    configuration one label deeper -- the "no collapse" analogue of
    [CoreLemmas.reduce_trans_if_true], needed because the match branch
    doesn't drain to [::] in this sub-case. *)
Lemma kmp_search_outer_if_to_return : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN,
  small iN -> small (iN+1) -> small jN -> small (jN+1) -> jN <= iN -> jN + 1 = patLenN ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) (jN+1) in
  reduce_trans (hs, s, f, [:: AI_basic (BI_const_num (VAL_int32 one32));
                              AI_basic (BI_if (BT_valtype None) search_match_bi search_mismatch_bi)])
    (hs, s, f', [:: AI_label 0 [::] [:: AI_label 0 [::]
          [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1))))); AI_basic BI_return]]]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN Hi Hi1 Hj Hj1 Hji Heq f f'.
  have Hif : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 one32));
                               AI_basic (BI_if (BT_valtype None) search_match_bi search_mismatch_bi)]
                    hs s f [:: AI_basic (BI_block (BT_valtype None) search_match_bi)].
  { apply reduce_simple_reduce.
    apply rs_if_true.
    rewrite /one32.
    move=> Hz.
    have : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 1) = Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 0).
    { f_equal. exact Hz. }
    vm_compute. lia. }
  have Hblock : reduce hs s f [:: AI_basic (BI_block (BT_valtype None) search_match_bi)]
                       hs s f [:: AI_label 0 [::] (to_e_list search_match_bi)].
  { apply r_block with (vs := [::]) (n := 0%nat) (m := 0%nat) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  rewrite search_match_bi_eq in Hblock.
  have Hret := kmp_search_match_body_to_return hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN
    Hi Hi1 Hj Hj1 Hji Heq.
  simpl in Hret.
  have Hlabel := reduce_trans_label1' _ _ _ _ _ _ _ _ 0 [::] Hret.
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ Hif.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ Hblock.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  exact: (reduce_trans_trans _ _ _ C12 Hlabel).
Qed.

(** The full assembly: starting from the real function-call
    configuration (matching [r_invoke_native] exactly, as
    [BuildLpsTop.v]'s [build_lps_correct] did for [build_lps]), running
    one loop iteration that finds the whole pattern collapses the
    entire frame directly to the return value [(i+1)-(j+1)] via
    [rs_return] -- a single step spanning five nested labels (inner
    if, outer if, loop, block, function-body), the deepest [lholed]
    witness built anywhere in this proof. *)
Theorem kmp_search_match_return : forall hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi bj,
  small textPtr -> small textLenN -> small patPtr -> small patLenN -> small lpsPtr -> small iN -> small jN ->
  iN < textLenN -> jN <= iN -> jN + 1 = patLenN ->
  small (textPtr + iN) -> small (patPtr + jN) -> small (iN+1) -> small (jN+1) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  mem_lookup (Z.to_N (textPtr + iN)) m.(meminst_data) = Some bi ->
  N.lt (Z.to_N (textPtr + iN)) (operations.mem_length m) ->
  mem_lookup (Z.to_N (patPtr + jN)) m.(meminst_data) = Some bj ->
  N.lt (Z.to_N (patPtr + jN)) (operations.mem_length m) ->
  bi = bj ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  reduce_trans (hs, s, f0, [:: AI_frame 1 f [:: AI_label 1 [::] (search_loop_entry_cfg f)]])
               (hs, s, f0, [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1)))))]).
Proof.
  move=> hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi bj
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hlt Hji Heq HaddTI HaddPJ Hi1 Hj1 Hmems Hlkm Hlkbi Hbndi Hlkbj Hbndj Hbeq f.
  set f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) (jN+1).
  have Hcheck := kmp_search_check_continue hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hlt.
  simpl in Hcheck.
  have Hcheck' := reduce_trans_prefix' _ _ _ _ _ _ _ _ search_loop_after_check_es Hcheck.
  simpl in Hcheck'.
  rewrite search_loop_after_check_es_eq in Hcheck'.
  have Hcmp := kmp_search_load_cmp hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi bj
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 HaddTI HaddPJ Hmems Hlkm Hlkbi Hbndi Hlkbj Hbndj.
  simpl in Hcmp.
  have Heqdec : (if Integers.Byte.eq_dec bi bj then one32 else zero32) = one32.
  { case: (Integers.Byte.eq_dec bi bj) => Heqd; [reflexivity | exfalso; exact: Heqd Hbeq]. }
  rewrite Heqdec in Hcmp.
  have Hcmp' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None) search_match_bi search_mismatch_bi); AI_basic (BI_br 0%N)] Hcmp.
  simpl in Hcmp'.
  have Hout := kmp_search_outer_if_to_return hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN
    Hp6 Hi1 Hp7 Hj1 Hji Heq.
  simpl in Hout.
  have Hout' := reduce_trans_prefix' _ _ _ _ _ _ _ _ [:: AI_basic (BI_br 0%N)] Hout.
  simpl in Hout'.
  have Cbody : reduce_trans (hs, s, f, search_loop_body_es)
    (hs, s, f', [:: AI_label 0 [::] [:: AI_label 0 [::]
          [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1))))); AI_basic BI_return]]] ++ [:: AI_basic (BI_br 0%N)]).
  { rewrite search_loop_body_es_full_split.
    have C12 := reduce_trans_trans _ _ _ Hcheck' Hcmp'.
    exact: (reduce_trans_trans _ _ _ C12 Hout'). }
  have HlabLoop := reduce_trans_label1' _ _ _ _ _ _ _ _ 0
    [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)] Cbody.
  have HlabBlock := reduce_trans_label1' _ _ _ _ _ _ _ _ 0 [::] HlabLoop.
  have HlabFunc := reduce_trans_label1' _ _ _ _ _ _ _ _ 1 [::] HlabBlock.
  have Hfr := reduce_trans_frame' _ _ _ _ _ _ _ _ 1 f0 HlabFunc.
  simpl in Hfr.
  have Hret : reduce hs s f0
    [:: AI_frame 1 f' [:: AI_label 1 [::]
          [:: AI_label 0 [::]
                [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
                      ([:: AI_label 0 [::] [:: AI_label 0 [::]
                            [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1))))); AI_basic BI_return]]]
                       ++ [:: AI_basic (BI_br 0%N)])]]]]
    hs s f0 [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1)))))].
  { apply reduce_simple_reduce.
    apply (rs_return (n := 1) (i := 5)
      (vs := [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1)))))])
      (es := [:: AI_label 1 [::]
          [:: AI_label 0 [::]
                [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
                      ([:: AI_label 0 [::] [:: AI_label 0 [::]
                            [:: AI_basic (BI_const_num (VAL_int32 (enc ((iN+1)-(jN+1))))); AI_basic BI_return]]]
                       ++ [:: AI_basic (BI_br 0%N)])]]])
      (lh := LH_rec [::] 1 [::]
               (LH_rec [::] 0 [::]
                  (LH_rec [::] 0 [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
                     (LH_rec [::] 0 [::]
                        (LH_rec [::] 0 [::] (LH_base [::] [::]) [::])
                     [:: AI_basic (BI_br 0%N)])
                  [::])
               [::])
            [::]));
      try reflexivity; try done. }
  exact: (reduce_trans_trans _ _ _ Hfr (reduce_trans_step _ _ _ _ _ _ _ _ Hret)).
Qed.

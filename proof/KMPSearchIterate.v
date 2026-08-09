(** [kmp_search]'s per-iteration "continue" step: when the loop does
    NOT exit ([i < textLen]) and the match branch doesn't find the full
    pattern, running one full iteration (check, load+compare, match/
    mismatch branch) and looping back via [br 0] returns to
    [search_loop_entry_cfg] with updated locals. The [kmp_search]
    analogue of [BuildLpsIterate.v]. The match branch's "found the full
    pattern" sub-case (an explicit [return]) is handled separately, in
    [KMPSearchMatchReturn.v] -- it doesn't return to
    [search_loop_entry_cfg] at all, so it doesn't fit this file's shape. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps Int32Facts KMPSearch KMPSearchLoop
  KMPSearchExit KMPSearchCmp KMPSearchMatch KMPSearchMismatch.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

Lemma search_loop_body_es_eq_to_e_list : search_loop_body_es = to_e_list kmp_search_loop_body.
Proof. vm_compute. reflexivity. Qed.

(** Mirror image of [KMPSearchExit.v]'s [kmp_search_exit_bare]: when
    [iN < textLenN], the exit check's [i32.ge_s] is false, so [br_if 1]
    is a no-op and the check's four instructions simply drain to [::],
    leaving [search_loop_after_check_es] to run. *)
Lemma kmp_search_check_continue : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN,
  small textPtr -> small textLenN -> small patPtr -> small patLenN -> small lpsPtr -> small iN -> small jN ->
  iN < textLenN ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 5%N); AI_basic (BI_local_get 1%N);
        AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)])
    (hs, s, f, [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hlt f.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 5%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 5%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 1%N); AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] HA.
  simpl in HA'.
  have HB : reduce hs s f [:: AI_basic (BI_local_get 1%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc textLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc textLenN))) (j := 1%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc iN))] _ _ _ _ _
    [:: AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] HB.
  simpl in HB'.
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN))); AI_basic (BI_const_num (VAL_int32 (enc textLenN)));
                              AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S)))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (enc iN)) (VAL_int32 (enc textLenN)) T_i32 (Relop_i (ROI_ge SX_S)).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc iN)) (VAL_int32 (enc textLenN)) T_i32 (Relop_i (ROI_ge SX_S)) Htc) as Hstep.
    move: Hstep.
    rewrite /app_relop /=.
    have Hlt' : Wasm_int.Int32.lt (enc iN) (enc textLenN) = true.
    { rewrite /Wasm_int.Int32.lt (enc_signed iN Hp6) (enc_signed textLenN Hp2).
      case: (Coqlib.zlt iN textLenN) => Hz; [reflexivity | lia]. }
    rewrite Hlt' /=.
    move=> H. exact H. }
  have HC' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_br_if 1%N)] HC.
  simpl in HC'.
  have HD : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_br_if 1%N)]
                    hs s f [::].
  { apply reduce_simple_reduce.
    apply rs_br_if_false.
    reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC'.
  have Step4 := reduce_trans_step _ _ _ _ _ _ _ _ HD.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  have C123 := reduce_trans_trans _ _ _ C12 Step3.
  exact: (reduce_trans_trans _ _ _ C123 Step4).
Qed.

(** The generic "close out one loop pass" step, independent of which
    branch was taken -- the [kmp_search] analogue of
    [BuildLpsIterate.v]'s [loop_body_to_reentry]. *)
Lemma search_loop_body_to_reentry : forall hs s f hs' s' f',
  reduce_trans (hs, s, f, search_loop_body_es) (hs', s', f', [:: AI_basic (BI_br 0%N)]) ->
  reduce_trans (hs, s, f, search_loop_entry_cfg f) (hs', s', f', search_loop_entry_cfg f').
Proof.
  move=> hs s f hs' s' f' Hbody.
  rewrite /search_loop_entry_cfg -search_loop_body_es_eq_to_e_list.
  have Hlab1 := reduce_trans_label1' _ _ _ _ _ _ _ _ 0
    [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)] Hbody.
  have Hbr : reduce hs' s' f'
      [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)] [:: AI_basic (BI_br 0%N)]]
      hs' s' f' [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)].
  { apply reduce_simple_reduce.
    apply (@rs_br 0 [::] [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)] 0
      [:: AI_basic (BI_br 0%N)] (LH_base [::] [::])); try reflexivity. }
  have Hstep1 := reduce_trans_trans _ _ _ Hlab1 (reduce_trans_step _ _ _ _ _ _ _ _ Hbr).
  have Hlab2 := reduce_trans_label1' _ _ _ _ _ _ _ _ 0 [::] Hstep1.
  have HLoop : reduce hs' s' f' [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
                       hs' s' f' [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) kmp_search_loop_body)]
                                    (to_e_list kmp_search_loop_body)].
  { apply r_loop with (vs := [::]) (n := 0%nat) (m := 0%nat) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  have HLoop' := reduce_label1 _ _ _ _ _ _ _ _ 0 [::] HLoop.
  exact: (reduce_trans_trans _ _ _ Hlab2 (reduce_trans_step _ _ _ _ _ _ _ _ HLoop')).
Qed.

(** Bare-instruction copies of the match/mismatch branch bodies, for use
    as [BI_if]'s branch arguments. *)
Definition search_match_bi : list basic_instruction :=
  [BI_local_get 5%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 5%N;
   BI_local_get 6%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 6%N;
   BI_local_get 6%N; BI_local_get 3%N; BI_relop T_i32 (Relop_i ROI_eq);
   BI_if (BT_valtype None)
     [BI_local_get 5%N; BI_local_get 6%N; BI_binop T_i32 (Binop_i BOI_sub); BI_return] []].

Definition search_mismatch_bi : list basic_instruction :=
  [BI_local_get 6%N; BI_const_num (VAL_int32 zero32); BI_relop T_i32 (Relop_i ROI_ne);
   BI_if (BT_valtype None)
     [BI_local_get 4%N; BI_local_get 6%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
      BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
      BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 6%N]
     [BI_local_get 5%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 5%N]].

Lemma search_match_bi_eq : to_e_list search_match_bi = search_match_body_es.
Proof. rewrite search_match_body_es_eq. vm_compute. reflexivity. Qed.

Lemma search_mismatch_bi_eq : to_e_list search_mismatch_bi = search_mismatch_body_es.
Proof. rewrite search_mismatch_body_es_eq. vm_compute. reflexivity. Qed.

Lemma search_loop_after_check_es_eq :
  search_loop_after_check_es =
    search_loop_load_cmp_es ++ [:: AI_basic (BI_if (BT_valtype None) search_match_bi search_mismatch_bi); AI_basic (BI_br 0%N)].
Proof. vm_compute. reflexivity. Qed.

Lemma search_loop_body_es_full_split :
  search_loop_body_es =
    [:: AI_basic (BI_local_get 5%N); AI_basic (BI_local_get 1%N);
        AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)]
    ++ search_loop_load_cmp_es
    ++ [:: AI_basic (BI_if (BT_valtype None) search_match_bi search_mismatch_bi); AI_basic (BI_br 0%N)].
Proof. vm_compute. reflexivity. Qed.

(** One full non-exiting iteration taking the match branch's "not done
    yet" sub-case ([text[i] = pat[j]], [j+1 <> patLen]): the loop
    reduces from [search_loop_entry_cfg f] back to
    [search_loop_entry_cfg f'], with [i] and [j] both incremented. *)
Lemma kmp_search_iterate_match_continue : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi,
  small textPtr -> small textLenN -> small patPtr -> small patLenN -> small lpsPtr -> small iN -> small jN ->
  iN < textLenN ->
  small (textPtr + iN) -> small (patPtr + jN) ->
  small (iN+1) -> small (jN+1) -> jN + 1 <> patLenN ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  mem_lookup (Z.to_N (textPtr + iN)) m.(meminst_data) = Some bi ->
  N.lt (Z.to_N (textPtr + iN)) (operations.mem_length m) ->
  mem_lookup (Z.to_N (patPtr + jN)) m.(meminst_data) = Some bi ->
  N.lt (Z.to_N (patPtr + jN)) (operations.mem_length m) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) (jN+1) in
  reduce_trans (hs, s, f, search_loop_entry_cfg f) (hs, s, f', search_loop_entry_cfg f').
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hlt HaddTI HaddPJ Hq1 Hq2 Hne Hmems Hlkm Hlkbi Hbndi Hlkbj Hbndj f f'.
  have Hcheck := kmp_search_check_continue hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hlt.
  simpl in Hcheck.
  have Hcheck' := reduce_trans_prefix' _ _ _ _ _ _ _ _ search_loop_after_check_es Hcheck.
  simpl in Hcheck'.
  rewrite search_loop_after_check_es_eq in Hcheck'.
  have Hcmp := kmp_search_load_cmp hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi bi
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 HaddTI HaddPJ Hmems Hlkm Hlkbi Hbndi Hlkbj Hbndj.
  simpl in Hcmp.
  have Heqdec : (if Integers.Byte.eq_dec bi bi then one32 else zero32) = one32.
  { case: (Integers.Byte.eq_dec bi bi) => Heq; [reflexivity | exfalso; exact: Heq erefl]. }
  rewrite Heqdec in Hcmp.
  have Hcmp' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None) search_match_bi search_mismatch_bi); AI_basic (BI_br 0%N)] Hcmp.
  simpl in Hcmp'.
  have Hpat : small patLenN by exact Hp4.
  have Hmatch := kmp_search_match_continue hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN
    Hp6 Hq1 Hp7 Hq2 Hpat Hne.
  simpl in Hmatch.
  rewrite -search_match_bi_eq in Hmatch.
  have Hone_ne0 : one32 <> Wasm_int.int_zero i32m.
  { rewrite /Wasm_int.int_zero /= /one32.
    move=> Hc. have := f_equal (@Wasm_int.Int32.unsigned) Hc. by vm_compute. }
  have Hif := reduce_trans_if_true hs s f one32 search_match_bi search_mismatch_bi hs s f' Hone_ne0 Hmatch.
  simpl in Hif.
  have Hif' := reduce_trans_prefix' _ _ _ _ _ _ _ _ [:: AI_basic (BI_br 0%N)] Hif.
  simpl in Hif'.
  have Cbody : reduce_trans (hs, s, f, search_loop_body_es) (hs, s, f', [:: AI_basic (BI_br 0%N)]).
  { rewrite search_loop_body_es_full_split.
    have C12 := reduce_trans_trans _ _ _ Hcheck' Hcmp'.
    exact: (reduce_trans_trans _ _ _ C12 Hif'). }
  exact: (search_loop_body_to_reentry hs s f hs s f' Cbody).
Qed.

(** One full non-exiting iteration taking the mismatch branch's
    backtrack sub-case ([text[i] <> pat[j]], [j <> 0]): the loop reduces
    from [search_loop_entry_cfg f] back to [search_loop_entry_cfg f'],
    with [j] set to the previously-recorded [lps[j-1]] and [i]
    unchanged. *)
Lemma kmp_search_iterate_backtrack : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi bj prevJN,
  small textPtr -> small textLenN -> small patPtr -> small patLenN -> small lpsPtr -> small iN -> small jN ->
  iN < textLenN -> bi <> bj ->
  small (textPtr + iN) -> small (patPtr + jN) ->
  1 <= jN -> small (jN - 1) -> small ((jN - 1) * 4) -> small (lpsPtr + (jN - 1) * 4) -> small prevJN ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  mem_lookup (Z.to_N (textPtr + iN)) m.(meminst_data) = Some bi ->
  N.lt (Z.to_N (textPtr + iN)) (operations.mem_length m) ->
  mem_lookup (Z.to_N (patPtr + jN)) m.(meminst_data) = Some bj ->
  N.lt (Z.to_N (patPtr + jN)) (operations.mem_length m) ->
  read_bytes m (Z.to_N (lpsPtr + (jN - 1) * 4)) 4 = Some (serialise_num (VAL_int32 (enc prevJN))) ->
  N.le (Z.to_N (lpsPtr + (jN - 1) * 4) + 4) (operations.mem_length m) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN prevJN in
  reduce_trans (hs, s, f, search_loop_entry_cfg f) (hs, s, f', search_loop_entry_cfg f').
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi bj prevJN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hlt Hne HaddTI HaddPJ Hq1 Hq2 Hq3 Hq4 Hq5 Hmems Hlkm Hlkbi Hbndi Hlkbj Hbndj Hrb Hbound f f'.
  have Hcheck := kmp_search_check_continue hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hlt.
  simpl in Hcheck.
  have Hcheck' := reduce_trans_prefix' _ _ _ _ _ _ _ _ search_loop_after_check_es Hcheck.
  simpl in Hcheck'.
  rewrite search_loop_after_check_es_eq in Hcheck'.
  have Hcmp := kmp_search_load_cmp hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi bj
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 HaddTI HaddPJ Hmems Hlkm Hlkbi Hbndi Hlkbj Hbndj.
  simpl in Hcmp.
  have Heqdec : (if Integers.Byte.eq_dec bi bj then one32 else zero32) = zero32.
  { case: (Integers.Byte.eq_dec bi bj) => Heq; [exfalso; exact: Hne Heq | reflexivity]. }
  rewrite Heqdec in Hcmp.
  have Hcmp' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None) search_match_bi search_mismatch_bi); AI_basic (BI_br 0%N)] Hcmp.
  simpl in Hcmp'.
  have Hmismatch := kmp_search_mismatch_branch_backtrack hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m prevJN
    Hp5 Hp7 Hq1 Hq2 Hq3 Hq4 Hq5 Hmems Hlkm Hrb Hbound.
  simpl in Hmismatch.
  rewrite -search_mismatch_bi_eq in Hmismatch.
  have Hzero_eq0 : zero32 = Wasm_int.int_zero i32m by reflexivity.
  have Hif := reduce_trans_if_false hs s f zero32 search_match_bi search_mismatch_bi hs s f' Hzero_eq0 Hmismatch.
  simpl in Hif.
  have Hif' := reduce_trans_prefix' _ _ _ _ _ _ _ _ [:: AI_basic (BI_br 0%N)] Hif.
  simpl in Hif'.
  have Cbody : reduce_trans (hs, s, f, search_loop_body_es) (hs, s, f', [:: AI_basic (BI_br 0%N)]).
  { rewrite search_loop_body_es_full_split.
    have C12 := reduce_trans_trans _ _ _ Hcheck' Hcmp'.
    exact: (reduce_trans_trans _ _ _ C12 Hif'). }
  exact: (search_loop_body_to_reentry hs s f hs s f' Cbody).
Qed.

(** One full non-exiting iteration taking the mismatch branch's
    give-up sub-case ([text[i] <> pat[j]], [j = 0]): the loop reduces
    from [search_loop_entry_cfg f] back to [search_loop_entry_cfg f2],
    with [i] incremented and [j] unchanged (still 0). *)
Lemma kmp_search_iterate_giveup : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN memaddr m bi bj,
  small textPtr -> small textLenN -> small patPtr -> small patLenN -> small lpsPtr -> small iN ->
  iN < textLenN -> bi <> bj ->
  small (textPtr + iN) -> small (patPtr + 0) ->
  small (iN+1) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  mem_lookup (Z.to_N (textPtr + iN)) m.(meminst_data) = Some bi ->
  N.lt (Z.to_N (textPtr + iN)) (operations.mem_length m) ->
  mem_lookup (Z.to_N (patPtr + 0)) m.(meminst_data) = Some bj ->
  N.lt (Z.to_N (patPtr + 0)) (operations.mem_length m) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN 0 in
  let f2 := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) 0 in
  reduce_trans (hs, s, f, search_loop_entry_cfg f) (hs, s, f2, search_loop_entry_cfg f2).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN memaddr m bi bj
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hlt Hne HaddTI HaddPJ Hq1 Hmems Hlkm Hlkbi Hbndi Hlkbj Hbndj f f2.
  have Hs0 : small 0 by rewrite /small; lia.
  have Hcheck := kmp_search_check_continue hs s inst textPtr textLenN patPtr patLenN lpsPtr iN 0
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hs0 Hlt.
  simpl in Hcheck.
  have Hcheck' := reduce_trans_prefix' _ _ _ _ _ _ _ _ search_loop_after_check_es Hcheck.
  simpl in Hcheck'.
  rewrite search_loop_after_check_es_eq in Hcheck'.
  have Hcmp := kmp_search_load_cmp hs s inst textPtr textLenN patPtr patLenN lpsPtr iN 0 memaddr m bi bj
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hs0 HaddTI HaddPJ Hmems Hlkm Hlkbi Hbndi Hlkbj Hbndj.
  simpl in Hcmp.
  have Heqdec : (if Integers.Byte.eq_dec bi bj then one32 else zero32) = zero32.
  { case: (Integers.Byte.eq_dec bi bj) => Heq; [exfalso; exact: Hne Heq | reflexivity]. }
  rewrite Heqdec in Hcmp.
  have Hcmp' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None) search_match_bi search_mismatch_bi); AI_basic (BI_br 0%N)] Hcmp.
  simpl in Hcmp'.
  have Hmismatch := kmp_search_mismatch_branch_giveup hs s inst textPtr textLenN patPtr patLenN lpsPtr iN Hp6 Hq1.
  simpl in Hmismatch.
  rewrite -search_mismatch_bi_eq in Hmismatch.
  have Hzero_eq0 : zero32 = Wasm_int.int_zero i32m by reflexivity.
  have Hif := reduce_trans_if_false hs s f zero32 search_match_bi search_mismatch_bi hs s f2 Hzero_eq0 Hmismatch.
  simpl in Hif.
  have Hif' := reduce_trans_prefix' _ _ _ _ _ _ _ _ [:: AI_basic (BI_br 0%N)] Hif.
  simpl in Hif'.
  have Cbody : reduce_trans (hs, s, f, search_loop_body_es) (hs, s, f2, [:: AI_basic (BI_br 0%N)]).
  { rewrite search_loop_body_es_full_split.
    have C12 := reduce_trans_trans _ _ _ Hcheck' Hcmp'.
    exact: (reduce_trans_trans _ _ _ C12 Hif'). }
  exact: (search_loop_body_to_reentry hs s f hs s f2 Cbody).
Qed.

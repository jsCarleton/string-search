(** [build_lps]'s per-iteration "continue" step: when the loop does
    NOT exit ([i < patLen]), running one full iteration (check, load+
    compare, match/mismatch branch) and looping back via [br 0] returns
    to [loop_entry_cfg] with updated locals/memory. Combines
    BuildLpsExit.v (loop entry/exit machinery), BuildLpsCmp.v (load p[i]/
    p[len] + compare), and BuildLpsMatch.v/BuildLpsMismatch.v (the three
    branch outcomes), closing the loop of [reduce_trans] facts needed
    for the eventual per-iteration induction. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps BuildLpsLoop Int32Facts
  BuildLpsExit BuildLpsCmp BuildLpsMatch BuildLpsMismatch.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** [loop_body_es] is [Eval vm_compute]d, but [loop_entry_cfg] spells
    the same instructions out as [to_e_list build_lps_loop_body]
    unevaluated; the two are convertible, but we need an explicit
    equation to [rewrite] with. *)
Lemma loop_body_es_eq_to_e_list : loop_body_es = to_e_list build_lps_loop_body.
Proof. vm_compute. reflexivity. Qed.

(** Mirror image of [BuildLpsExit.v]'s [build_lps_exit]: when
    [iN < patLenN], the exit check's [i32.ge_s] is false, so [br_if 1]
    is a no-op and the check's four instructions simply drain to [::],
    leaving [loop_after_check_es] to run. *)
Lemma build_lps_check_continue : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN,
  small patPtr -> small patLenN -> small lpsPtr -> small lenN -> small iN -> small tmpN ->
  iN < patLenN ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_local_get 1%N);
        AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)])
    (hs, s, f, [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hlt f.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 4%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 4%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 1%N); AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] HA.
  simpl in HA'.
  have HB : reduce hs s f [:: AI_basic (BI_local_get 1%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patLenN))) (j := 1%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc iN))] _ _ _ _ _
    [:: AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] HB.
  simpl in HB'.
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN))); AI_basic (BI_const_num (VAL_int32 (enc patLenN)));
                              AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S)))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (enc iN)) (VAL_int32 (enc patLenN)) T_i32 (Relop_i (ROI_ge SX_S)).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc iN)) (VAL_int32 (enc patLenN)) T_i32 (Relop_i (ROI_ge SX_S)) Htc) as Hstep.
    move: Hstep.
    rewrite /app_relop /=.
    have Hlt' : Wasm_int.Int32.lt (enc iN) (enc patLenN) = true.
    { rewrite /Wasm_int.Int32.lt (enc_signed iN Hp5) (enc_signed patLenN Hp2).
      case: (Coqlib.zlt iN patLenN) => Hz; [reflexivity | lia]. }
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
    branch was taken: given the loop body reduces (with the [br 0] at
    the very end) to a specific new local/store state, looping back via
    [br 0] (targeting the loop's own label, so [rs_br] hands back the
    loop's continuation -- literally the [loop] instruction itself, per
    [r_loop]'s definition of a loop's label content) and re-entering via
    [r_loop] reaches [loop_entry_cfg] with the new state. *)
Lemma loop_body_to_reentry : forall hs s f hs' s' f',
  reduce_trans (hs, s, f, loop_body_es) (hs', s', f', [:: AI_basic (BI_br 0%N)]) ->
  reduce_trans (hs, s, f, loop_entry_cfg f) (hs', s', f', loop_entry_cfg f').
Proof.
  move=> hs s f hs' s' f' Hbody.
  rewrite /loop_entry_cfg -loop_body_es_eq_to_e_list.
  have Hlab1 := reduce_trans_label1' _ _ _ _ _ _ _ _ 0
    [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)] Hbody.
  have Hbr : reduce hs' s' f'
      [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)] [:: AI_basic (BI_br 0%N)]]
      hs' s' f' [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)].
  { apply reduce_simple_reduce.
    apply (@rs_br 0 [::] [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)] 0
      [:: AI_basic (BI_br 0%N)] (LH_base [::] [::])); try reflexivity. }
  have Hstep1 := reduce_trans_trans _ _ _ Hlab1 (reduce_trans_step _ _ _ _ _ _ _ _ Hbr).
  have Hlab2 := reduce_trans_label1' _ _ _ _ _ _ _ _ 0 [::] Hstep1.
  have HLoop : reduce hs' s' f' [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)]
                       hs' s' f' [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)]
                                    (to_e_list build_lps_loop_body)].
  { apply r_loop with (vs := [::]) (n := 0%nat) (m := 0%nat) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  have HLoop' := reduce_label1 _ _ _ _ _ _ _ _ 0 [::] HLoop.
  exact: (reduce_trans_trans _ _ _ Hlab2 (reduce_trans_step _ _ _ _ _ _ _ _ HLoop')).
Qed.

(** Bare-instruction (non-administrative) copies of the match/mismatch
    branch bodies, for use as [BI_if]'s branch arguments -- the same
    literals as [match_body_es_eq]/[mismatch_body_es_eq]'s RHS, minus
    the [AI_basic] wrapper. *)
Definition match_bi : list basic_instruction :=
  [BI_local_get 3%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 3%N;
   BI_local_get 2%N; BI_local_get 4%N; BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl);
   BI_binop T_i32 (Binop_i BOI_add); BI_local_get 3%N; BI_store T_i32 None (Build_memarg 0%N 2%N);
   BI_local_get 4%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 4%N].

Definition mismatch_bi : list basic_instruction :=
  [BI_local_get 3%N; BI_const_num (VAL_int32 zero32); BI_relop T_i32 (Relop_i ROI_ne);
   BI_if (BT_valtype None)
     [BI_local_get 2%N; BI_local_get 3%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
      BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
      BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 5%N; BI_local_get 5%N; BI_local_set 3%N]
     [BI_local_get 2%N; BI_local_get 4%N; BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl);
      BI_binop T_i32 (Binop_i BOI_add); BI_const_num (VAL_int32 zero32); BI_store T_i32 None (Build_memarg 0%N 2%N);
      BI_local_get 4%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 4%N]].

Lemma match_bi_eq : to_e_list match_bi = match_body_es.
Proof. rewrite match_body_es_eq. vm_compute. reflexivity. Qed.

Lemma mismatch_bi_eq : to_e_list mismatch_bi = mismatch_body_es.
Proof. rewrite mismatch_body_es_eq. vm_compute. reflexivity. Qed.

(** [loop_after_check_es] (everything after the exit check) is the
    load/compare followed by the outer [if]/[br 0]. *)
Lemma loop_after_check_es_eq :
  loop_after_check_es =
    loop_load_cmp_es ++ [:: AI_basic (BI_if (BT_valtype None) match_bi mismatch_bi); AI_basic (BI_br 0%N)].
Proof. vm_compute. reflexivity. Qed.

(** [loop_body_es] entirely, split into its four pieces: exit check,
    load+compare, the outer [if], and [br 0]. *)
Lemma loop_body_es_full_split :
  loop_body_es =
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_local_get 1%N);
        AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)]
    ++ loop_load_cmp_es
    ++ [:: AI_basic (BI_if (BT_valtype None) match_bi mismatch_bi); AI_basic (BI_br 0%N)].
Proof. vm_compute. reflexivity. Qed.

(** One full non-exiting iteration taking the match branch
    ([p[i] = p[len]]): the loop reduces from [loop_entry_cfg f] all the
    way back to [loop_entry_cfg f2], with [len] and [i] both
    incremented and [lps[i]] updated in memory. *)
Theorem build_lps_iterate_match : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m b f0,
  small patPtr -> small patLenN -> small lpsPtr -> small lenN -> small iN -> small tmpN ->
  iN < patLenN ->
  small (patPtr + iN) -> small (patPtr + lenN) ->
  small (lenN+1) -> small (iN+1) -> small (iN*4) -> small (lpsPtr + iN*4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  mem_lookup (Z.to_N (patPtr + iN)) m.(meminst_data) = Some b ->
  N.lt (Z.to_N (patPtr + iN)) (operations.mem_length m) ->
  mem_lookup (Z.to_N (patPtr + lenN)) m.(meminst_data) = Some b ->
  N.lt (Z.to_N (patPtr + lenN)) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + iN*4) + 4) (operations.mem_length m) ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  let f2 := loop_frame inst patPtr patLenN lpsPtr (lenN+1) (iN+1) tmpN in
  exists s' m',
    lookup_N s'.(s_mems) memaddr = Some m'
    /\ write_bytes (meminst_data m) (Z.to_N (lpsPtr + iN*4)) (serialise_num (VAL_int32 (enc (lenN+1)))) = Some (meminst_data m')
    /\ reduce_trans (hs, s, f0, [:: AI_frame 0 f (loop_entry_cfg f)])
                     (hs, s', f0, [:: AI_frame 0 f2 (loop_entry_cfg f2)]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m b f0
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hlt HaddPI HaddPL Hq1 Hq2 Hq3 Hq4 Hmems Hlkm Hlkb1 Hbnd1 Hlkb2 Hbnd2 Hbound f f2.
  have Hcheck := build_lps_check_continue hs s inst patPtr patLenN lpsPtr lenN iN tmpN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hlt.
  simpl in Hcheck.
  have Hcheck' := reduce_trans_prefix' _ _ _ _ _ _ _ _ loop_after_check_es Hcheck.
  simpl in Hcheck'.
  rewrite loop_after_check_es_eq in Hcheck'.
  have Hcmp := build_lps_load_cmp hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m b b
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 HaddPI HaddPL Hmems Hlkm Hlkb1 Hbnd1 Hlkb2 Hbnd2.
  simpl in Hcmp.
  have Heqdec : (if Integers.Byte.eq_dec b b then one32 else zero32) = one32.
  { case: (Integers.Byte.eq_dec b b) => Heq; [reflexivity | exfalso; exact: Heq erefl]. }
  rewrite Heqdec in Hcmp.
  have Hcmp' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None) match_bi mismatch_bi); AI_basic (BI_br 0%N)] Hcmp.
  simpl in Hcmp'.
  have Hmatch := build_lps_match_branch hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m
    Hp1 Hp3 Hp4 Hp5 Hp6 Hq1 Hq2 Hq3 Hq4 Hmems Hlkm Hbound.
  simpl in Hmatch.
  destruct Hmatch as [s' [m' [Hlkm' [Hwr' Hmatchbody]]]].
  rewrite -match_bi_eq in Hmatchbody.
  have Hone_ne0 : one32 <> Wasm_int.int_zero i32m.
  { rewrite /Wasm_int.int_zero /= /one32.
    move=> Hc. have := f_equal (@Wasm_int.Int32.unsigned) Hc. by vm_compute. }
  have Hif := reduce_trans_if_true hs s f one32 match_bi mismatch_bi hs s' f2 Hone_ne0 Hmatchbody.
  simpl in Hif.
  have Hif' := reduce_trans_prefix' _ _ _ _ _ _ _ _ [:: AI_basic (BI_br 0%N)] Hif.
  simpl in Hif'.
  have Cbody : reduce_trans (hs, s, f, loop_body_es) (hs, s', f2, [:: AI_basic (BI_br 0%N)]).
  { rewrite loop_body_es_full_split.
    have C12 := reduce_trans_trans _ _ _ Hcheck' Hcmp'.
    exact: (reduce_trans_trans _ _ _ C12 Hif'). }
  have Creentry := loop_body_to_reentry hs s f hs s' f2 Cbody.
  exists s', m'. split; [exact Hlkm' |]. split; [exact Hwr' |].
  exact: (reduce_trans_frame' _ _ _ _ _ _ _ _ 0 f0 Creentry).
Qed.

(** [zero32] is [Wasm_int.int_zero i32m] -- shared by both mismatch
    sub-cases below, since the outer [p[i] <> p[len]] check always
    pushes [zero32] before the outer [if]. *)
Lemma zero32_is_int_zero : zero32 = Wasm_int.int_zero i32m.
Proof. reflexivity. Qed.

(** One full non-exiting iteration taking the mismatch branch's
    backtrack sub-case ([p[i] <> p[len]], [len <> 0]): the loop reduces
    from [loop_entry_cfg f] back to [loop_entry_cfg f'], with [len] set
    to the previously-recorded [lps[len-1]] and [i] unchanged. *)
Theorem build_lps_iterate_backtrack : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m bi blen prevLenN f0,
  small patPtr -> small patLenN -> small lpsPtr -> small lenN -> small iN -> small tmpN ->
  iN < patLenN -> bi <> blen ->
  small (patPtr + iN) -> small (patPtr + lenN) ->
  1 <= lenN -> small (lenN - 1) -> small ((lenN - 1) * 4) -> small (lpsPtr + (lenN - 1) * 4) -> small prevLenN ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  mem_lookup (Z.to_N (patPtr + iN)) m.(meminst_data) = Some bi ->
  N.lt (Z.to_N (patPtr + iN)) (operations.mem_length m) ->
  mem_lookup (Z.to_N (patPtr + lenN)) m.(meminst_data) = Some blen ->
  N.lt (Z.to_N (patPtr + lenN)) (operations.mem_length m) ->
  read_bytes m (Z.to_N (lpsPtr + (lenN - 1) * 4)) 4 = Some (serialise_num (VAL_int32 (enc prevLenN))) ->
  N.le (Z.to_N (lpsPtr + (lenN - 1) * 4) + 4) (operations.mem_length m) ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  let f' := loop_frame inst patPtr patLenN lpsPtr prevLenN iN prevLenN in
  reduce_trans (hs, s, f0, [:: AI_frame 0 f (loop_entry_cfg f)])
               (hs, s, f0, [:: AI_frame 0 f' (loop_entry_cfg f')]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m bi blen prevLenN f0
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hlt Hne HaddPI HaddPL Hq1 Hq2 Hq3 Hq4 Hq5 Hmems Hlkm Hlkbi Hbndi Hlkblen Hbndlen Hrb Hbound f f'.
  have Hcheck := build_lps_check_continue hs s inst patPtr patLenN lpsPtr lenN iN tmpN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hlt.
  simpl in Hcheck.
  have Hcheck' := reduce_trans_prefix' _ _ _ _ _ _ _ _ loop_after_check_es Hcheck.
  simpl in Hcheck'.
  rewrite loop_after_check_es_eq in Hcheck'.
  have Hcmp := build_lps_load_cmp hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m bi blen
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 HaddPI HaddPL Hmems Hlkm Hlkbi Hbndi Hlkblen Hbndlen.
  simpl in Hcmp.
  have Heqdec : (if Integers.Byte.eq_dec bi blen then one32 else zero32) = zero32.
  { case: (Integers.Byte.eq_dec bi blen) => Heq; [exfalso; exact: Hne Heq | reflexivity]. }
  rewrite Heqdec in Hcmp.
  have Hcmp' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None) match_bi mismatch_bi); AI_basic (BI_br 0%N)] Hcmp.
  simpl in Hcmp'.
  have Hback := build_lps_mismatch_branch_backtrack hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m prevLenN
    Hp3 Hp4 Hq1 Hq2 Hq3 Hq4 Hq5 Hmems Hlkm Hrb Hbound.
  simpl in Hback.
  rewrite -mismatch_bi_eq in Hback.
  have Hif := reduce_trans_if_false hs s f zero32 match_bi mismatch_bi hs s f' zero32_is_int_zero Hback.
  simpl in Hif.
  have Hif' := reduce_trans_prefix' _ _ _ _ _ _ _ _ [:: AI_basic (BI_br 0%N)] Hif.
  simpl in Hif'.
  have Cbody : reduce_trans (hs, s, f, loop_body_es) (hs, s, f', [:: AI_basic (BI_br 0%N)]).
  { rewrite loop_body_es_full_split.
    have C12 := reduce_trans_trans _ _ _ Hcheck' Hcmp'.
    exact: (reduce_trans_trans _ _ _ C12 Hif'). }
  have Creentry := loop_body_to_reentry hs s f hs s f' Cbody.
  exact: (reduce_trans_frame' _ _ _ _ _ _ _ _ 0 f0 Creentry).
Qed.

(** One full non-exiting iteration taking the mismatch branch's
    give-up sub-case ([p[i] <> p[len]], [len = 0]): the loop reduces
    from [loop_entry_cfg f] back to [loop_entry_cfg f2], with
    [lps[i] := 0] and [i] incremented; [len] stays [0]. *)
Theorem build_lps_iterate_giveup : forall hs s inst patPtr patLenN lpsPtr iN tmpN memaddr m bi blen f0,
  small patPtr -> small patLenN -> small lpsPtr -> small iN -> small tmpN ->
  iN < patLenN -> bi <> blen ->
  small (patPtr + iN) -> small (patPtr + 0) ->
  small (iN+1) -> small (iN*4) -> small (lpsPtr + iN*4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  mem_lookup (Z.to_N (patPtr + iN)) m.(meminst_data) = Some bi ->
  N.lt (Z.to_N (patPtr + iN)) (operations.mem_length m) ->
  mem_lookup (Z.to_N (patPtr + 0)) m.(meminst_data) = Some blen ->
  N.lt (Z.to_N (patPtr + 0)) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + iN*4) + 4) (operations.mem_length m) ->
  let f := loop_frame inst patPtr patLenN lpsPtr 0 iN tmpN in
  let f2 := loop_frame inst patPtr patLenN lpsPtr 0 (iN+1) tmpN in
  exists s' m',
    lookup_N s'.(s_mems) memaddr = Some m'
    /\ write_bytes (meminst_data m) (Z.to_N (lpsPtr + iN*4)) (serialise_num (VAL_int32 zero32)) = Some (meminst_data m')
    /\ reduce_trans (hs, s, f0, [:: AI_frame 0 f (loop_entry_cfg f)])
                     (hs, s', f0, [:: AI_frame 0 f2 (loop_entry_cfg f2)]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr iN tmpN memaddr m bi blen f0
    Hp1 Hp2 Hp3 Hp5 Hp6 Hlt Hne HaddPI HaddPL Hq2 Hq3 Hq4 Hmems Hlkm Hlkbi Hbndi Hlkblen Hbndlen Hbound f f2.
  have Hs0 : small 0 by rewrite /small; lia.
  have Hcheck := build_lps_check_continue hs s inst patPtr patLenN lpsPtr 0 iN tmpN
    Hp1 Hp2 Hp3 Hs0 Hp5 Hp6 Hlt.
  simpl in Hcheck.
  have Hcheck' := reduce_trans_prefix' _ _ _ _ _ _ _ _ loop_after_check_es Hcheck.
  simpl in Hcheck'.
  rewrite loop_after_check_es_eq in Hcheck'.
  have Hcmp := build_lps_load_cmp hs s inst patPtr patLenN lpsPtr 0 iN tmpN memaddr m bi blen
    Hp1 Hp2 Hp3 Hs0 Hp5 Hp6 HaddPI HaddPL Hmems Hlkm Hlkbi Hbndi Hlkblen Hbndlen.
  simpl in Hcmp.
  have Heqdec : (if Integers.Byte.eq_dec bi blen then one32 else zero32) = zero32.
  { case: (Integers.Byte.eq_dec bi blen) => Heq; [exfalso; exact: Hne Heq | reflexivity]. }
  rewrite Heqdec in Hcmp.
  have Hcmp' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None) match_bi mismatch_bi); AI_basic (BI_br 0%N)] Hcmp.
  simpl in Hcmp'.
  have Hgiveup := build_lps_mismatch_branch_giveup hs s inst patPtr patLenN lpsPtr iN tmpN memaddr m
    Hp3 Hp5 Hq2 Hq3 Hq4 Hmems Hlkm Hbound.
  simpl in Hgiveup.
  destruct Hgiveup as [s' [m' [Hlkm' [Hwr' Hgiveupbody]]]].
  rewrite -mismatch_bi_eq in Hgiveupbody.
  have Hif := reduce_trans_if_false hs s f zero32 match_bi mismatch_bi hs s' f2 zero32_is_int_zero Hgiveupbody.
  simpl in Hif.
  have Hif' := reduce_trans_prefix' _ _ _ _ _ _ _ _ [:: AI_basic (BI_br 0%N)] Hif.
  simpl in Hif'.
  have Cbody : reduce_trans (hs, s, f, loop_body_es) (hs, s', f2, [:: AI_basic (BI_br 0%N)]).
  { rewrite loop_body_es_full_split.
    have C12 := reduce_trans_trans _ _ _ Hcheck' Hcmp'.
    exact: (reduce_trans_trans _ _ _ C12 Hif'). }
  have Creentry := loop_body_to_reentry hs s f hs s' f2 Cbody.
  exists s', m'. split; [exact Hlkm' |]. split; [exact Hwr' |].
  exact: (reduce_trans_frame' _ _ _ _ _ _ _ _ 0 f0 Creentry).
Qed.

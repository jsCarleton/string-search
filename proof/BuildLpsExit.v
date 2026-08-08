(** [build_lps]'s main loop: entering it, and the exit path (the
    [i >= patLen] check succeeding, so [br_if 1] escapes the loop
    entirely). The "continue" path -- executing one iteration's body and
    looping back via [br 0] -- is built separately on top of this, since
    it is substantially larger (the match/mismatch branches).

    Throughout, loop counters/pointers are represented as [Z] via
    [Int32Facts.enc] rather than raw [i32], with [small] side conditions
    keeping every value comfortably inside signed range (see
    Int32Facts.v's header comment for why). *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps BuildLpsLoop Int32Facts.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** The configuration reached immediately after (re-)entering the loop:
    the block's label wrapping the loop's own label wrapping the loop
    body. This is both the target of the initial [block]/[loop] entry
    and the state each iteration returns to via [br 0]. *)
Definition loop_entry_cfg (f : frame) : list administrative_instruction :=
  [AI_label 0 [] [AI_label 0 [AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)]
                    (to_e_list build_lps_loop_body)]].

(** locals 0..5 = patPtr, patLen, lpsPtr, len, i, tmp (the last used only
    as scratch inside the backtracking branch, proved later). *)
Definition loop_frame (inst : moduleinst) (patPtr patLenN lpsPtr lenN iN tmpN : Z) : frame :=
  Build_frame [VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
               VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 (enc lenN));
               VAL_num (VAL_int32 (enc iN)); VAL_num (VAL_int32 (enc tmpN))] inst.

(** [block [loop ...]] (the single instruction ending BuildLps.v's
    [build_lps_es_rest]) reduces, via [r_block] then [r_loop], to
    [loop_entry_cfg]. *)
Lemma build_lps_loop_entry : forall hs s f,
  reduce_trans (hs, s, f, [build_lps_block_es]) (hs, s, f, loop_entry_cfg f).
Proof.
  move=> hs s f.
  rewrite build_lps_block_es_eq.
  have HBlk : reduce hs s f [:: AI_basic (BI_block (BT_valtype None) [BI_loop (BT_valtype None) build_lps_loop_body])]
                      hs s f [:: AI_label 0 [::] (to_e_list [BI_loop (BT_valtype None) build_lps_loop_body])].
  { apply r_block with (vs := [::]) (n := 0%nat) (m := 0%nat) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  have HLoop : reduce hs s f [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)]
                       hs s f [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)]
                                    (to_e_list build_lps_loop_body)].
  { apply r_loop with (vs := [::]) (n := 0%nat) (m := 0%nat) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  have HLoop' := reduce_label1 _ _ _ _ _ _ _ _ 0 [::] HLoop.
  apply: (reduce_trans_trans _ (hs,s,f,_) _).
  - exact: (reduce_trans_step _ _ _ _ _ _ _ _ HBlk).
  - exact: (reduce_trans_step _ _ _ _ _ _ _ _ HLoop').
Qed.

(** The loop body's first 4 instructions ([local.get 4; local.get 1;
    i32.ge_s; br_if 1], i.e. the [i >= patLen] exit check), spelled out
    against the real bytecode via [vm_compute]; [loop_after_check_es] is
    everything after. *)
Definition loop_body_es : list administrative_instruction := Eval vm_compute in to_e_list build_lps_loop_body.
Definition loop_after_check_es : list administrative_instruction := Eval vm_compute in List.skipn 4 loop_body_es.

Lemma loop_body_es_split :
  to_e_list build_lps_loop_body =
    [AI_basic (BI_local_get 4%N); AI_basic (BI_local_get 1%N);
     AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] ++ loop_after_check_es.
Proof. vm_compute. reflexivity. Qed.

(** Exit case: once [i >= patLen], the check's [br_if 1] fires,
    escaping both the loop's own label and the enclosing block's label
    (as [rs_br] with a 1-label-deep [lholed] witness -- the loop label
    sits between the [br]'s occurrence and its target, the block label),
    which then collapses the whole call frame to [] (0 results). *)
Lemma build_lps_exit : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN f0,
  small patPtr -> small patLenN -> small lpsPtr -> small lenN -> small iN -> small tmpN ->
  patLenN <= iN ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  reduce_trans (hs, s, f0, [:: AI_frame 0 f (loop_entry_cfg f)])
               (hs, s, f0, [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN f0
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hge f.
  rewrite /loop_entry_cfg.
  (* local.get 4 *)
  have HA : reduce hs s f [:: AI_basic (BI_local_get 4%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 4%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 1%N); AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] HA.
  simpl in HA'.
  (* local.get 1 -- the i-value from HA stays on the stack as a fixed prefix *)
  have HB : reduce hs s f [:: AI_basic (BI_local_get 1%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patLenN))) (j := 1%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc iN))] _ _ _ _ _
    [:: AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S))); AI_basic (BI_br_if 1%N)] HB.
  simpl in HB'.
  (* i32.ge_s: true, since patLenN <= iN *)
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN))); AI_basic (BI_const_num (VAL_int32 (enc patLenN)));
                              AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_S)))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 one32))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (enc iN)) (VAL_int32 (enc patLenN)) T_i32 (Relop_i (ROI_ge SX_S)).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc iN)) (VAL_int32 (enc patLenN)) T_i32 (Relop_i (ROI_ge SX_S)) Htc) as Hstep.
    move: Hstep.
    rewrite /app_relop /=.
    have Hlt : Wasm_int.Int32.lt (enc iN) (enc patLenN) = false.
    { rewrite /Wasm_int.Int32.lt (enc_signed iN Hp5) (enc_signed patLenN Hp2).
      case: (Coqlib.zlt iN patLenN) => Hz; [lia | reflexivity]. }
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
  rewrite loop_body_es_split.
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC'.
  have Step4 := reduce_trans_step _ _ _ _ _ _ _ _ HD.
  have Chain12 := reduce_trans_trans _ _ _ Step1 Step2.
  have Chain123 := reduce_trans_trans _ _ _ Chain12 Step3.
  have Hchain := reduce_trans_trans _ _ _ Chain123 Step4.
  have Hchain' := reduce_trans_prefix' _ _ _ _ _ _ _ _ loop_after_check_es Hchain.
  (* br 1, now visible inside the loop label (itself inside the block
     label), collapses both directly to [] via rs_br: the loop label is
     the sole layer between the br's occurrence and its target, the
     block label. *)
  have Hbr : reduce hs s f
    [:: AI_label 0 [::]
          [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)]
                ([:: AI_basic (BI_br 1%N)] ++ loop_after_check_es)]]
    hs s f [::].
  { apply reduce_simple_reduce.
    apply (@rs_br 0 [::] [::] 1
      [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)]
            ([:: AI_basic (BI_br 1%N)] ++ loop_after_check_es)]
      (LH_rec [::] 0 [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)]
               (LH_base [::] loop_after_check_es) [::]));
      try reflexivity. }
  have HlabLoop := reduce_trans_label1' _ _ _ _ _ _ _ _ 0
    [:: AI_basic (BI_loop (BT_valtype None) build_lps_loop_body)] Hchain'.
  have HlabBlock := reduce_trans_label1' _ _ _ _ _ _ _ _ 0 [::] HlabLoop.
  have Hlab2 := reduce_trans_trans _ _ _ HlabBlock (reduce_trans_step _ _ _ _ _ _ _ _ Hbr).
  have Hfr := reduce_trans_frame' _ _ _ _ _ _ _ _ 0 f0 Hlab2.
  (* Finally, the call frame -- now holding [] -- collapses to [] (0 results). *)
  have Hcollapse : reduce hs s f0 [:: AI_frame 0 f [::]] hs s f0 [::].
  { apply reduce_simple_reduce.
    apply (@rs_local_const [::] 0 f); by []. }
  apply: (reduce_trans_trans _ (hs,s,f0,_) _).
  - exact: Hfr.
  - exact: (reduce_trans_step _ _ _ _ _ _ _ _ Hcollapse).
Qed.

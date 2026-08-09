(** [build_lps]'s loop match branch (taken when [p[i] = p[len]]):
    [len++; lps[i] := len; i++]. Continues BuildLpsCmp.v, whose
    comparison result selects this branch. Proved in three segments
    (each its own local-variable/memory update), then assembled into
    [build_lps_match_branch]. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps BuildLpsLoop Int32Facts BuildLpsExit BuildLpsCmp.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

Definition match_body_es : list administrative_instruction := Eval vm_compute in
  match loop_after_cmp_es with
  | AI_basic (BI_if _ mb _) :: _ => List.map AI_basic mb
  | _ => []
  end.

Lemma match_body_es_eq :
  match_body_es =
    [AI_basic (BI_local_get 3%N); AI_basic (BI_const_num (VAL_int32 one32));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 3%N);
     AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 4%N);
     AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_local_get 3%N); AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N));
     AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 one32));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)].
Proof. vm_compute. reflexivity. Qed.

(** Segment 1: [len++] (locals 0-3: local.get 3; const 1; add; local.set 3). *)
Lemma seg1_len_inc : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN,
  small lenN -> small (lenN+1) ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  let f1 := loop_frame inst patPtr patLenN lpsPtr (lenN+1) iN tmpN in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 3%N); AI_basic (BI_const_num (VAL_int32 one32));
        AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 3%N)])
    (hs, s, f1, [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN Hs1 Hs2 f f1.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 3%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lenN))) (j := 3%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_local_set 3%N)] HA.
  simpl in HA'.
  have HB : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lenN))); AI_basic (BI_const_num (VAL_int32 one32));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lenN+1))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc lenN)) (VAL_int32 one32) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Hone : one32 = enc 1 by reflexivity.
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc lenN)) (VAL_int32 one32) = Some (VAL_int32 (enc (lenN+1))).
    { rewrite /app_binop /= Hone. f_equal. f_equal.
      have Hs1' : small 1 by rewrite /small; lia.
      exact: (add_enc lenN 1 Hs1 Hs1'). }
    pose proof (@rs_binop_success (VAL_int32 (enc lenN)) (VAL_int32 one32) (VAL_int32 (enc (lenN+1)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HB' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_local_set 3%N)] HB.
  simpl in HB'.
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lenN+1)))); AI_basic (BI_local_set 3%N)]
                    hs s f1 [::].
  { pose proof (@r_local_set _ _ _ f f1 3%N (VAL_num (VAL_int32 (enc (lenN+1)))) s (VAL_num (VAL_int32 zero32)) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f1 /loop_frame /=. reflexivity.
    - rewrite /f /loop_frame /=. by [].
    - rewrite /f /f1 /loop_frame /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  have C123 := reduce_trans_trans _ _ _ C12 Step3.
  exact: C123.
Qed.

(** Segment 2: [lps[i] := len] (locals.get 2/4; const 2; shl; add; local.get
    3; store -- computing address [lpsPtr + 4*i] and storing the
    post-segment-1 [len]). *)
Lemma seg2_store_len : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m,
  small lpsPtr -> small iN -> small (lenN+1) -> small (iN*4) -> small (lpsPtr + iN*4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (lpsPtr + iN*4) + 4) (operations.mem_length m) ->
  let f1 := loop_frame inst patPtr patLenN lpsPtr (lenN+1) iN tmpN in
  exists s' m',
    lookup_N s'.(s_mems) memaddr = Some m'
    /\ write_bytes (meminst_data m) (Z.to_N (lpsPtr + iN*4)) (serialise_num (VAL_int32 (enc (lenN+1)))) = Some (meminst_data m')
    /\ reduce_trans (hs, s, f1,
         [:: AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 4%N);
             AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
             AI_basic (BI_binop T_i32 (Binop_i BOI_add));
             AI_basic (BI_local_get 3%N); AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))])
         (hs, s', f1, [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m
    Hp1 Hp2 Hp3 Hp4 Hp5 Hmems Hlkm Hbound f1.
  have Hsmem : smem s inst = Some m.
  { rewrite /smem Hmems /=. rewrite Hlkm. reflexivity. }
  have HA : reduce hs s f1 [:: AI_basic (BI_local_get 2%N)] hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lpsPtr))) (j := 2%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 (enc 2)));
     AI_basic (BI_binop T_i32 (Binop_i BOI_shl)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_local_get 3%N); AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))] HA.
  simpl in HA'.
  have HB : reduce hs s f1 [:: AI_basic (BI_local_get 4%N)] hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 4%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_get 3%N);
     AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))] HB.
  simpl in HB'.
  have HC : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc iN))); AI_basic (BI_const_num (VAL_int32 (enc 2)));
                               AI_basic (BI_binop T_i32 (Binop_i BOI_shl))]
                    hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (iN*4))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc iN)) (VAL_int32 (enc 2)) T_i32 (Binop_i BOI_shl).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_shl) (VAL_int32 (enc iN)) (VAL_int32 (enc 2)) = Some (VAL_int32 (enc (iN*4))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (shl2_enc iN Hp2 Hp4). }
    pose proof (@rs_binop_success (VAL_int32 (enc iN)) (VAL_int32 (enc 2)) (VAL_int32 (enc (iN*4)))
      (Binop_i BOI_shl) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HC' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_get 3%N);
     AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))] HC.
  simpl in HC'.
  have HD : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr))); AI_basic (BI_const_num (VAL_int32 (enc (iN*4))));
                               AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (lpsPtr + iN*4))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc (iN*4))) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc (iN*4))) = Some (VAL_int32 (enc (lpsPtr + iN*4))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (add_enc lpsPtr (iN*4) Hp1 Hp4 Hp5). }
    pose proof (@rs_binop_success (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc (iN*4))) (VAL_int32 (enc (lpsPtr + iN*4)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HD' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 3%N); AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))] HD.
  simpl in HD'.
  have HE : reduce hs s f1 [:: AI_basic (BI_local_get 3%N)] hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (lenN+1))))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc (lenN+1)))) (j := 3%N). reflexivity. }
  have HE' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc (lpsPtr + iN*4)))] _ _ _ _ _
    [:: AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))] HE.
  simpl in HE'.
  have Haddr_N : Wasm_int.N_of_uint i32m (enc (lpsPtr + iN*4)) = Z.to_N (lpsPtr + iN*4).
  { rewrite /Wasm_int.N_of_uint /=. f_equal.
    apply Wasm_int.Int32.Z_mod_modulus_id.
    move: Hp5. rewrite /small.
    have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
    rewrite Hmod. lia. }
  have Hbound4 : N.le (Z.to_N (lpsPtr + iN*4) + 4) (operations.mem_length m) by exact Hbound.
  have [m' [Hst [Htype Hwr]]] := store_i32_effect m (Z.to_N (lpsPtr + iN*4)) (enc (lenN+1)) Hbound4.
  have HF : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (lpsPtr + iN*4))));
                               AI_basic (BI_const_num (VAL_int32 (enc (lenN+1))));
                               AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))]
                    hs (upd_s_mem s (set_nth m' s.(s_mems) (N.to_nat memaddr) m')) f1 [::].
  { pose proof (@r_store_success _ _ _ T_i32 (VAL_int32 (enc (lenN+1))) s f1 (enc (lpsPtr+iN*4))
      (Build_memarg 0%N 2%N) (upd_s_mem s (set_nth m' s.(s_mems) (N.to_nat memaddr) m')) hs) as Hstep.
    apply Hstep.
    rewrite /smem_store /f1 /loop_frame /=. rewrite Hmems /=. rewrite Hlkm.
    have Haddr_N2 : Z.to_N (Wasm_int.Int32.Z_mod_modulus (lpsPtr + iN*4)) = Z.to_N (lpsPtr + iN*4).
    { f_equal. apply Wasm_int.Int32.Z_mod_modulus_id.
      move: Hp5. rewrite /small.
      have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
      rewrite Hmod. lia. }
    rewrite Haddr_N2.
    rewrite /serialise_num /= in Hst.
    rewrite Hst. reflexivity. }
  exists (upd_s_mem s (set_nth m' s.(s_mems) (N.to_nat memaddr) m')), m'.
  have Hidx : Nat.lt (N.to_nat memaddr) (length s.(s_mems)).
  { move: Hlkm. rewrite /lookup_N. move=> H.
    case: (Nat.lt_ge_cases (N.to_nat memaddr) (length s.(s_mems))) => Hc; [exact Hc |].
    exfalso.
    have Hnone : List.nth_error s.(s_mems) (N.to_nat memaddr) = None.
    { apply List.nth_error_None. exact Hc. }
    rewrite Hnone in H. discriminate. }
  have nth_error_set_nth_eq : forall (A : Type) (d : A) (l : list A) (k : nat) (v : A),
    (k < length l)%coq_nat -> List.nth_error (set_nth d l k v) k = Some v.
  { clear. move=> A d l. elim: l => [| x l' IH] k v Hk /=.
    - exfalso. simpl in Hk. lia.
    - case: k Hk => [| k'] Hk /=.
      + reflexivity.
      + apply: IH. simpl in Hk. lia. }
  split.
  { rewrite /lookup_N /=. apply nth_error_set_nth_eq. exact Hidx. }
  split.
  { exact Hwr. }
  { have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
    have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
    have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC'.
    have Step4 := reduce_trans_step _ _ _ _ _ _ _ _ HD'.
    have Step5 := reduce_trans_step _ _ _ _ _ _ _ _ HE'.
    have Step6 := reduce_trans_step _ _ _ _ _ _ _ _ HF.
    have C12 := reduce_trans_trans _ _ _ Step1 Step2.
    have C123 := reduce_trans_trans _ _ _ C12 Step3.
    have C1234 := reduce_trans_trans _ _ _ C123 Step4.
    have C12345 := reduce_trans_trans _ _ _ C1234 Step5.
    have C123456 := reduce_trans_trans _ _ _ C12345 Step6.
    exact: C123456. }
Qed.

(** Segment 3: [i++] (local.get 4; const 1; add; local.set 4). *)
Lemma seg3_i_inc : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN,
  small iN -> small (iN+1) ->
  let f1 := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  let f2 := loop_frame inst patPtr patLenN lpsPtr lenN (iN+1) tmpN in
  reduce_trans (hs, s, f1,
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 one32));
        AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)])
    (hs, s, f2, [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN Hs1 Hs2 f1 f2.
  have HA : reduce hs s f1 [:: AI_basic (BI_local_get 4%N)] hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 4%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_local_set 4%N)] HA.
  simpl in HA'.
  have HB : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc iN))); AI_basic (BI_const_num (VAL_int32 one32));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (iN+1))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc iN)) (VAL_int32 one32) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Hone : one32 = enc 1 by reflexivity.
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc iN)) (VAL_int32 one32) = Some (VAL_int32 (enc (iN+1))).
    { rewrite /app_binop /= Hone. f_equal. f_equal.
      have Hs1' : small 1 by rewrite /small; lia.
      exact: (add_enc iN 1 Hs1 Hs1'). }
    pose proof (@rs_binop_success (VAL_int32 (enc iN)) (VAL_int32 one32) (VAL_int32 (enc (iN+1)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HB' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_local_set 4%N)] HB.
  simpl in HB'.
  have HC : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc (iN+1)))); AI_basic (BI_local_set 4%N)]
                    hs s f2 [::].
  { pose proof (@r_local_set _ _ _ f1 f2 4%N (VAL_num (VAL_int32 (enc (iN+1)))) s (VAL_num (VAL_int32 zero32)) hs) as Hstep.
    apply Hstep.
    - rewrite /f1 /f2 /loop_frame /=. reflexivity.
    - rewrite /f1 /loop_frame /=. by [].
    - rewrite /f1 /f2 /loop_frame /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  have C123 := reduce_trans_trans _ _ _ C12 Step3.
  exact: C123.
Qed.

(** The full match branch: chains the three segments above. Note the
    [small] side conditions on the *sums* [lenN+1], [iN+1], [iN*4],
    [lpsPtr+iN*4] -- individually-small inputs don't bound these, so
    the caller (the eventual per-iteration/induction lemma) must carry
    them as loop-invariant bounds on the pattern/lps-table size. *)
Theorem build_lps_match_branch : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m,
  small patPtr -> small lpsPtr -> small lenN -> small iN -> small tmpN ->
  small (lenN+1) -> small (iN+1) -> small (iN*4) -> small (lpsPtr + iN*4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (lpsPtr + iN*4) + 4) (operations.mem_length m) ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  let f2 := loop_frame inst patPtr patLenN lpsPtr (lenN+1) (iN+1) tmpN in
  exists s' m',
    lookup_N s'.(s_mems) memaddr = Some m'
    /\ write_bytes (meminst_data m) (Z.to_N (lpsPtr + iN*4)) (serialise_num (VAL_int32 (enc (lenN+1)))) = Some (meminst_data m')
    /\ reduce_trans (hs, s, f, match_body_es) (hs, s', f2, [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hp8 Hp9 Hmems Hlkm Hbound f f2.
  rewrite match_body_es_eq.
  have Hseg1 := seg1_len_inc hs s inst patPtr patLenN lpsPtr lenN iN tmpN Hp3 Hp6.
  simpl in Hseg1.
  have [s' [m' [Hlkm' [Hwr' Hseg2]]]] :=
    seg2_store_len hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m Hp2 Hp4 Hp6 Hp8 Hp9 Hmems Hlkm Hbound.
  simpl in Hseg2.
  have Hseg3 := seg3_i_inc hs s' inst patPtr patLenN lpsPtr (lenN+1) iN tmpN Hp4 Hp7.
  simpl in Hseg3.
  exists s', m'.
  split; [exact Hlkm' |]. split; [exact Hwr' |].
  have Hseg1' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    ([:: AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 4%N);
         AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
         AI_basic (BI_binop T_i32 (Binop_i BOI_add));
         AI_basic (BI_local_get 3%N); AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))]
      ++ [:: AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 one32));
              AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)])
    Hseg1.
  simpl in Hseg1'.
  have Hseg2' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 one32));
        AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)]
    Hseg2.
  simpl in Hseg2'.
  have C12 := reduce_trans_trans _ _ _ Hseg1' Hseg2'.
  have C123 := reduce_trans_trans _ _ _ C12 Hseg3.
  exact: C123.
Qed.

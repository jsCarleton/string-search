(** [build_lps]'s loop mismatch branch (taken when [p[i] <> p[len]]):
    either backtrack via [len := lps[len-1]] (when [len <> 0]) or give
    up on this position ([lps[i] := 0; i++], when [len = 0]). Continues
    BuildLpsCmp.v/BuildLpsMatch.v; together with the match branch this
    covers the full body reached after the [p[i] = p[len]] comparison. *)
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

Definition mismatch_body_es : list administrative_instruction := Eval vm_compute in
  match loop_after_cmp_es with
  | AI_basic (BI_if _ _ mmb) :: _ => List.map AI_basic mmb
  | _ => []
  end.

Lemma mismatch_body_es_eq :
  mismatch_body_es =
    [AI_basic (BI_local_get 3%N); AI_basic (BI_const_num (VAL_int32 zero32));
     AI_basic (BI_relop T_i32 (Relop_i ROI_ne));
     AI_basic (BI_if (BT_valtype None)
       [BI_local_get 2%N; BI_local_get 3%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
        BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
        BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 5%N; BI_local_get 5%N; BI_local_set 3%N]
       [BI_local_get 2%N; BI_local_get 4%N; BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl);
        BI_binop T_i32 (Binop_i BOI_add); BI_const_num (VAL_int32 zero32);
        BI_store T_i32 None (Build_memarg 0%N 2%N); BI_local_get 4%N; BI_const_num (VAL_int32 one32);
        BI_binop T_i32 (Binop_i BOI_add); BI_local_set 4%N])].
Proof. vm_compute. reflexivity. Qed.

(** Step 0: [len != 0] check, producing the boolean that selects the
    backtrack (nonzero) vs. give-up (zero) sub-branch below. *)
Lemma seg0_ne_check : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN,
  small lenN ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 3%N); AI_basic (BI_const_num (VAL_int32 zero32));
        AI_basic (BI_relop T_i32 (Relop_i ROI_ne))])
    (hs, s, f, [:: AI_basic (BI_const_num (VAL_int32 (if Z.eq_dec lenN 0 then zero32 else one32)))]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN Hp1 f.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 3%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lenN))) (j := 3%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_relop T_i32 (Relop_i ROI_ne))] HA.
  simpl in HA'.
  have Hs0 : small 0 by rewrite /small; lia.
  have HB : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lenN))); AI_basic (BI_const_num (VAL_int32 zero32));
                              AI_basic (BI_relop T_i32 (Relop_i ROI_ne))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (if Z.eq_dec lenN 0 then zero32 else one32)))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (enc lenN)) (VAL_int32 zero32) T_i32 (Relop_i ROI_ne).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc lenN)) (VAL_int32 zero32) T_i32 (Relop_i ROI_ne) Htc) as Hstep.
    move: Hstep. rewrite /app_relop /= /Wasm_int.int_ne /=.
    have Heqb : Wasm_int.Int32.eq (enc lenN) zero32 = (if Z.eq_dec lenN 0 then true else false).
    { rewrite /Wasm_int.Int32.eq (enc_unsigned lenN Hp1).
      have -> : zero32 = enc 0 by reflexivity.
      rewrite (enc_unsigned 0 Hs0).
      case: (Coqlib.zeq lenN 0) => Hz; case: (Z.eq_dec lenN 0) => Heq; try reflexivity; exfalso; lia. }
    rewrite Heqb.
    case: (Z.eq_dec lenN 0) => Heq /=; move=> H; exact H. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB.
  exact: (reduce_trans_trans _ _ _ Step1 Step2).
Qed.

(** Backtrack sub-branch (taken when [len <> 0]): [len := lps[len-1]],
    i.e. [tmp := load(lpsPtr + 4*(len-1)); len := tmp]. Unlike
    [BuildLpsMatch.v]'s stores, this *reads* a table entry written by
    an earlier loop iteration, so the caller supplies what's there via
    a bare [read_bytes] fact (through [Int32Facts.v]'s [load_i32_value]),
    not a [store]-based one. *)
Lemma seg_backtrack : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m prevLenN,
  small lpsPtr -> small lenN -> 1 <= lenN -> small (lenN - 1) -> small ((lenN - 1) * 4) ->
  small (lpsPtr + (lenN - 1) * 4) -> small prevLenN ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  read_bytes m (Z.to_N (lpsPtr + (lenN - 1) * 4)) 4 = Some (serialise_num (VAL_int32 (enc prevLenN))) ->
  N.le (Z.to_N (lpsPtr + (lenN - 1) * 4) + 4) (operations.mem_length m) ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  let f' := loop_frame inst patPtr patLenN lpsPtr prevLenN iN prevLenN in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 3%N); AI_basic (BI_const_num (VAL_int32 one32));
        AI_basic (BI_binop T_i32 (Binop_i BOI_sub)); AI_basic (BI_const_num (VAL_int32 (enc 2)));
        AI_basic (BI_binop T_i32 (Binop_i BOI_shl)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
        AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N)); AI_basic (BI_local_set 5%N);
        AI_basic (BI_local_get 5%N); AI_basic (BI_local_set 3%N)])
    (hs, s, f', [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m prevLenN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hmems Hlkm Hrb Hbound f f'.
  have Hsmem : smem s inst = Some m.
  { rewrite /smem Hmems /=. rewrite Hlkm. reflexivity. }
  (* local.get 2 : lpsPtr *)
  have HA : reduce hs s f [:: AI_basic (BI_local_get 2%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lpsPtr))) (j := 2%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 3%N); AI_basic (BI_const_num (VAL_int32 one32));
     AI_basic (BI_binop T_i32 (Binop_i BOI_sub)); AI_basic (BI_const_num (VAL_int32 (enc 2)));
     AI_basic (BI_binop T_i32 (Binop_i BOI_shl)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N)); AI_basic (BI_local_set 5%N);
     AI_basic (BI_local_get 5%N); AI_basic (BI_local_set 3%N)] HA.
  simpl in HA'.
  (* local.get 3 : len *)
  have HB : reduce hs s f [:: AI_basic (BI_local_get 3%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lenN))) (j := 3%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_binop T_i32 (Binop_i BOI_sub));
     AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N));
     AI_basic (BI_local_set 5%N); AI_basic (BI_local_get 5%N); AI_basic (BI_local_set 3%N)] HB.
  simpl in HB'.
  (* i32.sub : len - 1 *)
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lenN))); AI_basic (BI_const_num (VAL_int32 one32));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_sub))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lenN - 1))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc lenN)) (VAL_int32 one32) T_i32 (Binop_i BOI_sub).
    { rewrite /binop_typecheck. done. }
    have Hone : one32 = enc 1 by reflexivity.
    have Happ : app_binop (Binop_i BOI_sub) (VAL_int32 (enc lenN)) (VAL_int32 one32) = Some (VAL_int32 (enc (lenN - 1))).
    { rewrite /app_binop /= Hone. f_equal. f_equal.
      have Hs1' : small 1 by rewrite /small; lia.
      exact: (sub_enc lenN 1 Hp2 Hs1' Hp3). }
    pose proof (@rs_binop_success (VAL_int32 (enc lenN)) (VAL_int32 one32) (VAL_int32 (enc (lenN - 1)))
      (Binop_i BOI_sub) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HC' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N));
     AI_basic (BI_local_set 5%N); AI_basic (BI_local_get 5%N); AI_basic (BI_local_set 3%N)] HC.
  simpl in HC'.
  (* i32.shl 2 : (len-1)*4 *)
  have HD : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lenN - 1)))); AI_basic (BI_const_num (VAL_int32 (enc 2)));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_shl))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc ((lenN - 1) * 4))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc (lenN - 1))) (VAL_int32 (enc 2)) T_i32 (Binop_i BOI_shl).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_shl) (VAL_int32 (enc (lenN - 1))) (VAL_int32 (enc 2)) = Some (VAL_int32 (enc ((lenN - 1) * 4))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (shl2_enc (lenN - 1) Hp4 Hp5). }
    pose proof (@rs_binop_success (VAL_int32 (enc (lenN - 1))) (VAL_int32 (enc 2)) (VAL_int32 (enc ((lenN - 1) * 4)))
      (Binop_i BOI_shl) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HD' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N));
     AI_basic (BI_local_set 5%N); AI_basic (BI_local_get 5%N); AI_basic (BI_local_set 3%N)] HD.
  simpl in HD'.
  (* i32.add : lpsPtr + (len-1)*4 *)
  have HE : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr))); AI_basic (BI_const_num (VAL_int32 (enc ((lenN - 1) * 4))));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lpsPtr + (lenN - 1) * 4))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc ((lenN - 1) * 4))) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc ((lenN - 1) * 4))) = Some (VAL_int32 (enc (lpsPtr + (lenN - 1) * 4))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (add_enc lpsPtr ((lenN - 1) * 4) Hp1 Hp5 Hp6). }
    pose proof (@rs_binop_success (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc ((lenN - 1) * 4))) (VAL_int32 (enc (lpsPtr + (lenN - 1) * 4)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HE' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N)); AI_basic (BI_local_set 5%N);
     AI_basic (BI_local_get 5%N); AI_basic (BI_local_set 3%N)] HE.
  simpl in HE'.
  (* i32.load : lps[len-1] *)
  have Haddr_N : Wasm_int.N_of_uint i32m (enc (lpsPtr + (lenN - 1) * 4)) = Z.to_N (lpsPtr + (lenN - 1) * 4).
  { rewrite /Wasm_int.N_of_uint /=. f_equal.
    apply Wasm_int.Int32.Z_mod_modulus_id.
    move: Hp6. rewrite /small.
    have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
    rewrite Hmod. lia. }
  have [Hload Hdeser] := load_i32_value m (Z.to_N (lpsPtr + (lenN - 1) * 4)) (enc prevLenN) Hrb Hbound.
  have HF : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lpsPtr + (lenN - 1) * 4))));
                              AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc prevLenN)))].
  { have Hld : load m (Wasm_int.N_of_uint i32m (enc (lpsPtr + (lenN - 1) * 4))) 0%N (tnum_length T_i32) = Some (serialise_num (VAL_int32 (enc prevLenN))).
    { rewrite Haddr_N. exact Hload. }
    pose proof (@r_load_success _ _ _ s f T_i32 (serialise_num (VAL_int32 (enc prevLenN))) (enc (lpsPtr + (lenN - 1) * 4))
      (Build_memarg 0%N 2%N) m hs Hsmem Hld) as Hstep.
    rewrite Hdeser in Hstep.
    exact: Hstep. }
  have HF' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_set 5%N); AI_basic (BI_local_get 5%N); AI_basic (BI_local_set 3%N)] HF.
  simpl in HF'.
  (* local.set 5 : tmp := prevLen *)
  set f1 := loop_frame inst patPtr patLenN lpsPtr lenN iN prevLenN.
  have HG : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc prevLenN))); AI_basic (BI_local_set 5%N)]
                    hs s f1 [::].
  { pose proof (@r_local_set _ _ _ f f1 5%N (VAL_num (VAL_int32 (enc prevLenN))) s (VAL_num (VAL_int32 zero32)) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f1 /loop_frame /=. reflexivity.
    - rewrite /f /loop_frame /=. by [].
    - rewrite /f /f1 /loop_frame /=. reflexivity. }
  have HG' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 5%N); AI_basic (BI_local_set 3%N)] HG.
  simpl in HG'.
  (* local.get 5 ; local.set 3 : len := tmp (= prevLen) *)
  have HH : reduce hs s f1 [:: AI_basic (BI_local_get 5%N)] hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc prevLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc prevLenN))) (j := 5%N). reflexivity. }
  have HH' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_local_set 3%N)] HH.
  simpl in HH'.
  have HI : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 (enc prevLenN))); AI_basic (BI_local_set 3%N)]
                    hs s f' [::].
  { pose proof (@r_local_set _ _ _ f1 f' 3%N (VAL_num (VAL_int32 (enc prevLenN))) s (VAL_num (VAL_int32 zero32)) hs) as Hstep.
    apply Hstep.
    - rewrite /f1 /f' /loop_frame /=. reflexivity.
    - rewrite /f1 /loop_frame /=. by [].
    - rewrite /f1 /f' /loop_frame /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC'.
  have Step4 := reduce_trans_step _ _ _ _ _ _ _ _ HD'.
  have Step5 := reduce_trans_step _ _ _ _ _ _ _ _ HE'.
  have Step6 := reduce_trans_step _ _ _ _ _ _ _ _ HF'.
  have Step7 := reduce_trans_step _ _ _ _ _ _ _ _ HG'.
  have Step8 := reduce_trans_step _ _ _ _ _ _ _ _ HH'.
  have Step9 := reduce_trans_step _ _ _ _ _ _ _ _ HI.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  have C123 := reduce_trans_trans _ _ _ C12 Step3.
  have C1234 := reduce_trans_trans _ _ _ C123 Step4.
  have C12345 := reduce_trans_trans _ _ _ C1234 Step5.
  have C123456 := reduce_trans_trans _ _ _ C12345 Step6.
  have C1234567 := reduce_trans_trans _ _ _ C123456 Step7.
  have C12345678 := reduce_trans_trans _ _ _ C1234567 Step8.
  have C123456789 := reduce_trans_trans _ _ _ C12345678 Step9.
  exact: C123456789.
Qed.

(** Give-up sub-branch (taken when [len = 0]): [lps[i] := 0; i++].
    Structurally the same as [BuildLpsMatch.v]'s [seg2_store_len] +
    [seg3_i_inc], but storing [0] at address [lpsPtr + 4*i] (not
    [lpsPtr + 4*i] with the post-increment [len]) and *not* changing
    [len]. *)
Lemma seg_giveup : forall hs s inst patPtr patLenN lpsPtr iN tmpN memaddr m,
  small lpsPtr -> small iN -> small (iN+1) -> small (iN*4) -> small (lpsPtr + iN*4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (lpsPtr + iN*4) + 4) (operations.mem_length m) ->
  let f := loop_frame inst patPtr patLenN lpsPtr 0 iN tmpN in
  let f2 := loop_frame inst patPtr patLenN lpsPtr 0 (iN+1) tmpN in
  exists s' m',
    lookup_N s'.(s_mems) memaddr = Some m'
    /\ write_bytes (meminst_data m) (Z.to_N (lpsPtr + iN*4)) (serialise_num (VAL_int32 zero32)) = Some (meminst_data m')
    /\ reduce_trans (hs, s, f,
         [:: AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 4%N);
             AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
             AI_basic (BI_binop T_i32 (Binop_i BOI_add));
             AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N));
             AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 one32));
             AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)])
         (hs, s', f2, [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr iN tmpN memaddr m
    Hp1 Hp2 Hp3 Hp4 Hp5 Hmems Hlkm Hbound f f2.
  have Hsmem : smem s inst = Some m.
  { rewrite /smem Hmems /=. rewrite Hlkm. reflexivity. }
  have HA : reduce hs s f [:: AI_basic (BI_local_get 2%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lpsPtr))) (j := 2%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 (enc 2)));
     AI_basic (BI_binop T_i32 (Binop_i BOI_shl)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N));
     AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 one32));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)] HA.
  simpl in HA'.
  have HB : reduce hs s f [:: AI_basic (BI_local_get 4%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 4%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_const_num (VAL_int32 zero32));
     AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N)); AI_basic (BI_local_get 4%N);
     AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)] HB.
  simpl in HB'.
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN))); AI_basic (BI_const_num (VAL_int32 (enc 2)));
                               AI_basic (BI_binop T_i32 (Binop_i BOI_shl))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (iN*4))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc iN)) (VAL_int32 (enc 2)) T_i32 (Binop_i BOI_shl).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_shl) (VAL_int32 (enc iN)) (VAL_int32 (enc 2)) = Some (VAL_int32 (enc (iN*4))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (shl2_enc iN Hp2 Hp4). }
    pose proof (@rs_binop_success (VAL_int32 (enc iN)) (VAL_int32 (enc 2)) (VAL_int32 (enc (iN*4)))
      (Binop_i BOI_shl) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HC' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_const_num (VAL_int32 zero32));
     AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N)); AI_basic (BI_local_get 4%N);
     AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)] HC.
  simpl in HC'.
  have HD : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr))); AI_basic (BI_const_num (VAL_int32 (enc (iN*4))));
                               AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lpsPtr + iN*4))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc (iN*4))) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc (iN*4))) = Some (VAL_int32 (enc (lpsPtr + iN*4))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (add_enc lpsPtr (iN*4) Hp1 Hp4 Hp5). }
    pose proof (@rs_binop_success (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc (iN*4))) (VAL_int32 (enc (lpsPtr + iN*4)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HD' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N));
     AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 one32));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)] HD.
  simpl in HD'.
  have Haddr_N : Wasm_int.N_of_uint i32m (enc (lpsPtr + iN*4)) = Z.to_N (lpsPtr + iN*4).
  { rewrite /Wasm_int.N_of_uint /=. f_equal.
    apply Wasm_int.Int32.Z_mod_modulus_id.
    move: Hp5. rewrite /small.
    have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
    rewrite Hmod. lia. }
  have Hbound4 : N.le (Z.to_N (lpsPtr + iN*4) + 4) (operations.mem_length m) by exact Hbound.
  have [m' [Hst [Htype Hwr]]] := store_i32_effect m (Z.to_N (lpsPtr + iN*4)) zero32 Hbound4.
  have HE : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lpsPtr + iN*4))));
                               AI_basic (BI_const_num (VAL_int32 zero32));
                               AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))]
                    hs (upd_s_mem s (set_nth m' s.(s_mems) (N.to_nat memaddr) m')) f [::].
  { pose proof (@r_store_success _ _ _ T_i32 (VAL_int32 zero32) s f (enc (lpsPtr+iN*4))
      (Build_memarg 0%N 2%N) (upd_s_mem s (set_nth m' s.(s_mems) (N.to_nat memaddr) m')) hs) as Hstep.
    apply Hstep.
    rewrite /smem_store /f /loop_frame /=. rewrite Hmems /=. rewrite Hlkm.
    have Haddr_N2 : Z.to_N (Wasm_int.Int32.Z_mod_modulus (lpsPtr + iN*4)) = Z.to_N (lpsPtr + iN*4).
    { f_equal. apply Wasm_int.Int32.Z_mod_modulus_id.
      move: Hp5. rewrite /small.
      have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
      rewrite Hmod. lia. }
    rewrite Haddr_N2.
    rewrite /serialise_num /= in Hst.
    rewrite Hst. reflexivity. }
  set s' := upd_s_mem s (set_nth m' s.(s_mems) (N.to_nat memaddr) m').
  have HE' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_const_num (VAL_int32 one32));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 4%N)] HE.
  simpl in HE'.
  have HF : reduce hs s' f [:: AI_basic (BI_local_get 4%N)] hs s' f [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 4%N). reflexivity. }
  have HF' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_local_set 4%N)] HF.
  simpl in HF'.
  have HG : reduce hs s' f [:: AI_basic (BI_const_num (VAL_int32 (enc iN))); AI_basic (BI_const_num (VAL_int32 one32));
                                AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s' f [:: AI_basic (BI_const_num (VAL_int32 (enc (iN+1))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc iN)) (VAL_int32 one32) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Hone : one32 = enc 1 by reflexivity.
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc iN)) (VAL_int32 one32) = Some (VAL_int32 (enc (iN+1))).
    { rewrite /app_binop /= Hone. f_equal. f_equal.
      have Hs1' : small 1 by rewrite /small; lia.
      exact: (add_enc iN 1 Hp2 Hs1' Hp3). }
    pose proof (@rs_binop_success (VAL_int32 (enc iN)) (VAL_int32 one32) (VAL_int32 (enc (iN+1)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HG' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_local_set 4%N)] HG.
  simpl in HG'.
  have HH : reduce hs s' f [:: AI_basic (BI_const_num (VAL_int32 (enc (iN+1)))); AI_basic (BI_local_set 4%N)]
                    hs s' f2 [::].
  { pose proof (@r_local_set _ _ _ f f2 4%N (VAL_num (VAL_int32 (enc (iN+1)))) s' (VAL_num (VAL_int32 zero32)) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f2 /loop_frame /=. reflexivity.
    - rewrite /f /loop_frame /=. by [].
    - rewrite /f /f2 /loop_frame /=. reflexivity. }
  exists s', m'.
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
    have Step6 := reduce_trans_step _ _ _ _ _ _ _ _ HF'.
    have Step7 := reduce_trans_step _ _ _ _ _ _ _ _ HG'.
    have Step8 := reduce_trans_step _ _ _ _ _ _ _ _ HH.
    have C12 := reduce_trans_trans _ _ _ Step1 Step2.
    have C123 := reduce_trans_trans _ _ _ C12 Step3.
    have C1234 := reduce_trans_trans _ _ _ C123 Step4.
    have C12345 := reduce_trans_trans _ _ _ C1234 Step5.
    have C123456 := reduce_trans_trans _ _ _ C12345 Step6.
    have C1234567 := reduce_trans_trans _ _ _ C123456 Step7.
    have C12345678 := reduce_trans_trans _ _ _ C1234567 Step8.
    exact: C12345678. }
Qed.

(** The full mismatch branch: [seg0_ne_check] selects backtrack (when
    [len <> 0]) or give-up (when [len = 0]) via [reduce_trans_if_true]/
    [reduce_trans_if_false] (CoreLemmas.v), running the corresponding
    sub-branch to completion. Note this is stated as two separate
    theorems (rather than one existential over both cases) since the
    two sub-branches have different side-condition shapes (backtrack
    reads a previously-written table entry; give-up writes one). *)
Theorem build_lps_mismatch_branch_backtrack : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m prevLenN,
  small lpsPtr -> small lenN -> 1 <= lenN -> small (lenN - 1) -> small ((lenN - 1) * 4) ->
  small (lpsPtr + (lenN - 1) * 4) -> small prevLenN ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  read_bytes m (Z.to_N (lpsPtr + (lenN - 1) * 4)) 4 = Some (serialise_num (VAL_int32 (enc prevLenN))) ->
  N.le (Z.to_N (lpsPtr + (lenN - 1) * 4) + 4) (operations.mem_length m) ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  let f' := loop_frame inst patPtr patLenN lpsPtr prevLenN iN prevLenN in
  reduce_trans (hs, s, f, mismatch_body_es) (hs, s, f', [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m prevLenN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hmems Hlkm Hrb Hbound f f'.
  rewrite mismatch_body_es_eq.
  have Hne := seg0_ne_check hs s inst patPtr patLenN lpsPtr lenN iN tmpN Hp2.
  simpl in Hne.
  have Hne' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None)
         [BI_local_get 2%N; BI_local_get 3%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
          BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
          BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 5%N; BI_local_get 5%N; BI_local_set 3%N]
         [BI_local_get 2%N; BI_local_get 4%N; BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl);
          BI_binop T_i32 (Binop_i BOI_add); BI_const_num (VAL_int32 zero32); BI_store T_i32 None (Build_memarg 0%N 2%N);
          BI_local_get 4%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 4%N])]
    Hne.
  simpl in Hne'.
  have Hback := seg_backtrack hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m prevLenN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hmems Hlkm Hrb Hbound.
  simpl in Hback.
  have Hlen_ne0 : (if Z.eq_dec lenN 0 then zero32 else one32) <> Wasm_int.int_zero i32m.
  { case: (Z.eq_dec lenN 0) => Heq.
    - exfalso. lia.
    - rewrite /Wasm_int.int_zero /= /one32 /zero32.
      move=> Hc. have := f_equal (@Wasm_int.Int32.unsigned) Hc. by vm_compute. }
  have Hif := reduce_trans_if_true hs s f (if Z.eq_dec lenN 0 then zero32 else one32)
    [BI_local_get 2%N; BI_local_get 3%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
     BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
     BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 5%N; BI_local_get 5%N; BI_local_set 3%N]
    [BI_local_get 2%N; BI_local_get 4%N; BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl);
     BI_binop T_i32 (Binop_i BOI_add); BI_const_num (VAL_int32 zero32); BI_store T_i32 None (Build_memarg 0%N 2%N);
     BI_local_get 4%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 4%N]
    hs s f' Hlen_ne0 Hback.
  simpl in Hif.
  exact: (reduce_trans_trans _ _ _ Hne' Hif).
Qed.

Theorem build_lps_mismatch_branch_giveup : forall hs s inst patPtr patLenN lpsPtr iN tmpN memaddr m,
  small lpsPtr -> small iN -> small (iN+1) -> small (iN*4) -> small (lpsPtr + iN*4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (lpsPtr + iN*4) + 4) (operations.mem_length m) ->
  let f := loop_frame inst patPtr patLenN lpsPtr 0 iN tmpN in
  let f2 := loop_frame inst patPtr patLenN lpsPtr 0 (iN+1) tmpN in
  exists s' m',
    lookup_N s'.(s_mems) memaddr = Some m'
    /\ write_bytes (meminst_data m) (Z.to_N (lpsPtr + iN*4)) (serialise_num (VAL_int32 zero32)) = Some (meminst_data m')
    /\ reduce_trans (hs, s, f, mismatch_body_es) (hs, s', f2, [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr iN tmpN memaddr m
    Hp1 Hp2 Hp3 Hp4 Hp5 Hmems Hlkm Hbound f f2.
  rewrite mismatch_body_es_eq.
  have Hne := seg0_ne_check hs s inst patPtr patLenN lpsPtr 0 iN tmpN.
  have Hs0 : small 0 by rewrite /small; lia.
  have Hne' := Hne Hs0.
  simpl in Hne'.
  have Hne'' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None)
         [BI_local_get 2%N; BI_local_get 3%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
          BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
          BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 5%N; BI_local_get 5%N; BI_local_set 3%N]
         [BI_local_get 2%N; BI_local_get 4%N; BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl);
          BI_binop T_i32 (Binop_i BOI_add); BI_const_num (VAL_int32 zero32); BI_store T_i32 None (Build_memarg 0%N 2%N);
          BI_local_get 4%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 4%N])]
    Hne'.
  simpl in Hne''.
  have [s' [m' [Hlkm' [Hwr' Hgiveup]]]] :=
    seg_giveup hs s inst patPtr patLenN lpsPtr iN tmpN memaddr m Hp1 Hp2 Hp3 Hp4 Hp5 Hmems Hlkm Hbound.
  simpl in Hgiveup.
  have Hz0 : (if Z.eq_dec 0 0 then zero32 else one32) = Wasm_int.int_zero i32m.
  { case: (Z.eq_dec 0 0) => Heq; [reflexivity | exfalso; exact: Heq erefl]. }
  have Hif := reduce_trans_if_false hs s f (if Z.eq_dec 0 0 then zero32 else one32)
    [BI_local_get 2%N; BI_local_get 3%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
     BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
     BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 5%N; BI_local_get 5%N; BI_local_set 3%N]
    [BI_local_get 2%N; BI_local_get 4%N; BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl);
     BI_binop T_i32 (Binop_i BOI_add); BI_const_num (VAL_int32 zero32); BI_store T_i32 None (Build_memarg 0%N 2%N);
     BI_local_get 4%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 4%N]
    hs s' f2 Hz0 Hgiveup.
  simpl in Hif.
  exists s', m'. split; [exact Hlkm' |]. split; [exact Hwr' |].
  exact: (reduce_trans_trans _ _ _ Hne'' Hif).
Qed.

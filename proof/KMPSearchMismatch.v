(** [kmp_search]'s loop mismatch branch (taken when [text[i] <> pat[j]]):
    either backtrack via [j := lps[j-1]] (when [j <> 0]) or give up on
    this position ([i++], when [j = 0]). The [kmp_search] analogue of
    [BuildLpsMismatch.v], and simpler on both sub-branches: backtrack
    here is a single [local.set] (no scratch register, unlike
    [build_lps]'s two-step [tmp := ...; len := tmp]), and give-up
    touches no memory at all (just [i++] -- there is no per-position
    table to write here, unlike [build_lps]'s [lps[i] := 0]). *)
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

Definition search_mismatch_body_es : list administrative_instruction := Eval vm_compute in
  match search_loop_after_cmp_es with
  | AI_basic (BI_if _ _ mmb) :: _ => List.map AI_basic mmb
  | _ => []
  end.

Lemma search_mismatch_body_es_eq :
  search_mismatch_body_es =
    [AI_basic (BI_local_get 6%N); AI_basic (BI_const_num (VAL_int32 zero32));
     AI_basic (BI_relop T_i32 (Relop_i ROI_ne));
     AI_basic (BI_if (BT_valtype None)
       [BI_local_get 4%N; BI_local_get 6%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
        BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
        BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 6%N]
       [BI_local_get 5%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 5%N])].
Proof. vm_compute. reflexivity. Qed.

(** Step 0: [j != 0] check, producing the boolean that selects the
    backtrack (nonzero) vs. give-up (zero) sub-branch below. *)
Lemma search_seg0_ne_check : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN,
  small jN ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 6%N); AI_basic (BI_const_num (VAL_int32 zero32));
        AI_basic (BI_relop T_i32 (Relop_i ROI_ne))])
    (hs, s, f, [:: AI_basic (BI_const_num (VAL_int32 (if Z.eq_dec jN 0 then zero32 else one32)))]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN Hp1 f.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 6%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc jN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc jN))) (j := 6%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_relop T_i32 (Relop_i ROI_ne))] HA.
  simpl in HA'.
  have Hs0 : small 0 by rewrite /small; lia.
  have HB : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc jN))); AI_basic (BI_const_num (VAL_int32 zero32));
                              AI_basic (BI_relop T_i32 (Relop_i ROI_ne))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (if Z.eq_dec jN 0 then zero32 else one32)))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (enc jN)) (VAL_int32 zero32) T_i32 (Relop_i ROI_ne).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc jN)) (VAL_int32 zero32) T_i32 (Relop_i ROI_ne) Htc) as Hstep.
    move: Hstep. rewrite /app_relop /= /Wasm_int.int_ne /=.
    have Heqb : Wasm_int.Int32.eq (enc jN) zero32 = (if Z.eq_dec jN 0 then true else false).
    { rewrite /Wasm_int.Int32.eq (enc_unsigned jN Hp1).
      have -> : zero32 = enc 0 by reflexivity.
      rewrite (enc_unsigned 0 Hs0).
      case: (Coqlib.zeq jN 0) => Hz; case: (Z.eq_dec jN 0) => Heq; try reflexivity; exfalso; lia. }
    rewrite Heqb.
    case: (Z.eq_dec jN 0) => Heq /=; move=> H; exact H. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB.
  exact: (reduce_trans_trans _ _ _ Step1 Step2).
Qed.

(** Backtrack sub-branch (taken when [j <> 0]): [j := lps[j-1]]. Unlike
    [build_lps]'s backtrack, there is no scratch register in play --
    [local.set 6] applies the loaded value directly. *)
Lemma search_seg_backtrack : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m prevJN,
  small lpsPtr -> small jN -> 1 <= jN -> small (jN - 1) -> small ((jN - 1) * 4) ->
  small (lpsPtr + (jN - 1) * 4) -> small prevJN ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  read_bytes m (Z.to_N (lpsPtr + (jN - 1) * 4)) 4 = Some (serialise_num (VAL_int32 (enc prevJN))) ->
  N.le (Z.to_N (lpsPtr + (jN - 1) * 4) + 4) (operations.mem_length m) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN prevJN in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_local_get 6%N); AI_basic (BI_const_num (VAL_int32 one32));
        AI_basic (BI_binop T_i32 (Binop_i BOI_sub)); AI_basic (BI_const_num (VAL_int32 (enc 2)));
        AI_basic (BI_binop T_i32 (Binop_i BOI_shl)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
        AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N)); AI_basic (BI_local_set 6%N)])
    (hs, s, f', [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m prevJN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hmems Hlkm Hrb Hbound f f'.
  have Hsmem : smem s inst = Some m.
  { rewrite /smem Hmems /=. rewrite Hlkm. reflexivity. }
  (* local.get 4 : lpsPtr *)
  have HA : reduce hs s f [:: AI_basic (BI_local_get 4%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lpsPtr))) (j := 4%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 6%N); AI_basic (BI_const_num (VAL_int32 one32));
     AI_basic (BI_binop T_i32 (Binop_i BOI_sub)); AI_basic (BI_const_num (VAL_int32 (enc 2)));
     AI_basic (BI_binop T_i32 (Binop_i BOI_shl)); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N)); AI_basic (BI_local_set 6%N)] HA.
  simpl in HA'.
  (* local.get 6 : j *)
  have HB : reduce hs s f [:: AI_basic (BI_local_get 6%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc jN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc jN))) (j := 6%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_binop T_i32 (Binop_i BOI_sub));
     AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N));
     AI_basic (BI_local_set 6%N)] HB.
  simpl in HB'.
  (* i32.sub : j - 1 *)
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc jN))); AI_basic (BI_const_num (VAL_int32 one32));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_sub))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (jN - 1))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc jN)) (VAL_int32 one32) T_i32 (Binop_i BOI_sub).
    { rewrite /binop_typecheck. done. }
    have Hone : one32 = enc 1 by reflexivity.
    have Happ : app_binop (Binop_i BOI_sub) (VAL_int32 (enc jN)) (VAL_int32 one32) = Some (VAL_int32 (enc (jN - 1))).
    { rewrite /app_binop /= Hone. f_equal. f_equal.
      have Hs1' : small 1 by rewrite /small; lia.
      exact: (sub_enc jN 1 Hp2 Hs1' Hp3). }
    pose proof (@rs_binop_success (VAL_int32 (enc jN)) (VAL_int32 one32) (VAL_int32 (enc (jN - 1)))
      (Binop_i BOI_sub) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HC' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 (enc 2))); AI_basic (BI_binop T_i32 (Binop_i BOI_shl));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N));
     AI_basic (BI_local_set 6%N)] HC.
  simpl in HC'.
  (* i32.shl 2 : (j-1)*4 *)
  have HD : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (jN - 1)))); AI_basic (BI_const_num (VAL_int32 (enc 2)));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_shl))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc ((jN - 1) * 4))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc (jN - 1))) (VAL_int32 (enc 2)) T_i32 (Binop_i BOI_shl).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_shl) (VAL_int32 (enc (jN - 1))) (VAL_int32 (enc 2)) = Some (VAL_int32 (enc ((jN - 1) * 4))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (shl2_enc (jN - 1) Hp4 Hp5). }
    pose proof (@rs_binop_success (VAL_int32 (enc (jN - 1))) (VAL_int32 (enc 2)) (VAL_int32 (enc ((jN - 1) * 4)))
      (Binop_i BOI_shl) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HD' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc lpsPtr))] _ _ _ _ _
    [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N));
     AI_basic (BI_local_set 6%N)] HD.
  simpl in HD'.
  (* i32.add : lpsPtr + (j-1)*4 *)
  have HE : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr))); AI_basic (BI_const_num (VAL_int32 (enc ((jN - 1) * 4))));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lpsPtr + (jN - 1) * 4))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc ((jN - 1) * 4))) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc ((jN - 1) * 4))) = Some (VAL_int32 (enc (lpsPtr + (jN - 1) * 4))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (add_enc lpsPtr ((jN - 1) * 4) Hp1 Hp5 Hp6). }
    pose proof (@rs_binop_success (VAL_int32 (enc lpsPtr)) (VAL_int32 (enc ((jN - 1) * 4))) (VAL_int32 (enc (lpsPtr + (jN - 1) * 4)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HE' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N)); AI_basic (BI_local_set 6%N)] HE.
  simpl in HE'.
  (* i32.load : lps[j-1] *)
  have Haddr_N : Wasm_int.N_of_uint i32m (enc (lpsPtr + (jN - 1) * 4)) = Z.to_N (lpsPtr + (jN - 1) * 4).
  { rewrite /Wasm_int.N_of_uint /=. f_equal.
    apply Wasm_int.Int32.Z_mod_modulus_id.
    move: Hp6. rewrite /small.
    have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
    rewrite Hmod. lia. }
  have [Hload Hdeser] := load_i32_value m (Z.to_N (lpsPtr + (jN - 1) * 4)) (enc prevJN) Hrb Hbound.
  have HF : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (lpsPtr + (jN - 1) * 4))));
                              AI_basic (BI_load T_i32 None (Build_memarg 0%N 2%N))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc prevJN)))].
  { have Hld : load m (Wasm_int.N_of_uint i32m (enc (lpsPtr + (jN - 1) * 4))) 0%N (tnum_length T_i32) = Some (serialise_num (VAL_int32 (enc prevJN))).
    { rewrite Haddr_N. exact Hload. }
    pose proof (@r_load_success _ _ _ s f T_i32 (serialise_num (VAL_int32 (enc prevJN))) (enc (lpsPtr + (jN - 1) * 4))
      (Build_memarg 0%N 2%N) m hs Hsmem Hld) as Hstep.
    rewrite Hdeser in Hstep.
    exact: Hstep. }
  have HF' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_local_set 6%N)] HF.
  simpl in HF'.
  (* local.set 6 : j := prevJ *)
  have HG : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc prevJN))); AI_basic (BI_local_set 6%N)]
                    hs s f' [::].
  { pose proof (@r_local_set _ _ _ f f' 6%N (VAL_num (VAL_int32 (enc prevJN))) s (VAL_num (VAL_int32 (enc jN))) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f' /search_frame /=. reflexivity.
    - rewrite /f /search_frame /=. by [].
    - rewrite /f /f' /search_frame /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC'.
  have Step4 := reduce_trans_step _ _ _ _ _ _ _ _ HD'.
  have Step5 := reduce_trans_step _ _ _ _ _ _ _ _ HE'.
  have Step6 := reduce_trans_step _ _ _ _ _ _ _ _ HF'.
  have Step7 := reduce_trans_step _ _ _ _ _ _ _ _ HG.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  have C123 := reduce_trans_trans _ _ _ C12 Step3.
  have C1234 := reduce_trans_trans _ _ _ C123 Step4.
  have C12345 := reduce_trans_trans _ _ _ C1234 Step5.
  have C123456 := reduce_trans_trans _ _ _ C12345 Step6.
  exact: (reduce_trans_trans _ _ _ C123456 Step7).
Qed.

(** Give-up sub-branch (taken when [j = 0]): just [i++]. No memory
    write at all, unlike [build_lps]'s give-up ([lps[i] := 0; i++]). *)
Lemma search_seg_giveup : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN,
  small iN -> small (iN+1) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN 0 in
  let f2 := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) 0 in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_local_get 5%N); AI_basic (BI_const_num (VAL_int32 one32));
        AI_basic (BI_binop T_i32 (Binop_i BOI_add)); AI_basic (BI_local_set 5%N)])
    (hs, s, f2, [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN Hp1 Hp2 f f2.
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
      exact: (add_enc iN 1 Hp1 Hs1' Hp2). }
    pose proof (@rs_binop_success (VAL_int32 (enc iN)) (VAL_int32 one32) (VAL_int32 (enc (iN+1)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HB' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_local_set 5%N)] HB.
  simpl in HB'.
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (iN+1)))); AI_basic (BI_local_set 5%N)]
                    hs s f2 [::].
  { pose proof (@r_local_set _ _ _ f f2 5%N (VAL_num (VAL_int32 (enc (iN+1)))) s (VAL_num (VAL_int32 (enc iN))) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f2 /search_frame /=. reflexivity.
    - rewrite /f /search_frame /=. by [].
    - rewrite /f /f2 /search_frame /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  exact: (reduce_trans_trans _ _ _ C12 Step3).
Qed.

(** The full mismatch branch, as two theorems (backtrack / give-up),
    mirroring [BuildLpsMismatch.v]'s split (the two sub-branches have
    different side-condition shapes: backtrack reads a previously-
    written table entry, give-up doesn't touch memory at all). *)
Theorem kmp_search_mismatch_branch_backtrack : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m prevJN,
  small lpsPtr -> small jN -> 1 <= jN -> small (jN - 1) -> small ((jN - 1) * 4) ->
  small (lpsPtr + (jN - 1) * 4) -> small prevJN ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  read_bytes m (Z.to_N (lpsPtr + (jN - 1) * 4)) 4 = Some (serialise_num (VAL_int32 (enc prevJN))) ->
  N.le (Z.to_N (lpsPtr + (jN - 1) * 4) + 4) (operations.mem_length m) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN prevJN in
  reduce_trans (hs, s, f, search_mismatch_body_es) (hs, s, f', [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m prevJN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hmems Hlkm Hrb Hbound f f'.
  rewrite search_mismatch_body_es_eq.
  have Hne := search_seg0_ne_check hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN Hp2.
  simpl in Hne.
  have Hne' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None)
         [BI_local_get 4%N; BI_local_get 6%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
          BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
          BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 6%N]
         [BI_local_get 5%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 5%N])]
    Hne.
  simpl in Hne'.
  have Hback := search_seg_backtrack hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m prevJN
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 Hmems Hlkm Hrb Hbound.
  simpl in Hback.
  have Hjn_ne0 : (if Z.eq_dec jN 0 then zero32 else one32) <> Wasm_int.int_zero i32m.
  { case: (Z.eq_dec jN 0) => Heq.
    - exfalso. lia.
    - rewrite /Wasm_int.int_zero /= /one32 /zero32.
      move=> Hc. have := f_equal (@Wasm_int.Int32.unsigned) Hc. by vm_compute. }
  have Hif := reduce_trans_if_true hs s f (if Z.eq_dec jN 0 then zero32 else one32)
    [BI_local_get 4%N; BI_local_get 6%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
     BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
     BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 6%N]
    [BI_local_get 5%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 5%N]
    hs s f' Hjn_ne0 Hback.
  simpl in Hif.
  exact: (reduce_trans_trans _ _ _ Hne' Hif).
Qed.

Theorem kmp_search_mismatch_branch_giveup : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN,
  small iN -> small (iN+1) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN 0 in
  let f2 := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (iN+1) 0 in
  reduce_trans (hs, s, f, search_mismatch_body_es) (hs, s, f2, [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN Hp1 Hp2 f f2.
  rewrite search_mismatch_body_es_eq.
  have Hne := search_seg0_ne_check hs s inst textPtr textLenN patPtr patLenN lpsPtr iN 0.
  have Hs0 : small 0 by rewrite /small; lia.
  have Hne' := Hne Hs0.
  simpl in Hne'.
  have Hne'' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None)
         [BI_local_get 4%N; BI_local_get 6%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
          BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
          BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 6%N]
         [BI_local_get 5%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 5%N])]
    Hne'.
  simpl in Hne''.
  have Hgiveup := search_seg_giveup hs s inst textPtr textLenN patPtr patLenN lpsPtr iN Hp1 Hp2.
  simpl in Hgiveup.
  have Hz0 : (if Z.eq_dec 0 0 then zero32 else one32) = Wasm_int.int_zero i32m.
  { case: (Z.eq_dec 0 0) => Heq; [reflexivity | exfalso; exact: Heq erefl]. }
  have Hif := reduce_trans_if_false hs s f (if Z.eq_dec 0 0 then zero32 else one32)
    [BI_local_get 4%N; BI_local_get 6%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_sub);
     BI_const_num (VAL_int32 (enc 2)); BI_binop T_i32 (Binop_i BOI_shl); BI_binop T_i32 (Binop_i BOI_add);
     BI_load T_i32 None (Build_memarg 0%N 2%N); BI_local_set 6%N]
    [BI_local_get 5%N; BI_const_num (VAL_int32 one32); BI_binop T_i32 (Binop_i BOI_add); BI_local_set 5%N]
    hs s f2 Hz0 Hgiveup.
  simpl in Hif.
  exact: (reduce_trans_trans _ _ _ Hne'' Hif).
Qed.

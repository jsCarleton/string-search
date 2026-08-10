(** [kmp_search]'s prologue [patLen <> 0] case (mirroring
    [BuildLpsInit.v]'s [build_lps_patLen_nonzero_pre]) and its init
    sequence ([i := 0; j := 0], the analogue of
    [BuildLpsInit.v]'s [build_lps_init_locals]) -- simpler here since,
    unlike [build_lps]'s [len := 0; i := 1], both locals are set to the
    same literal (0), and neither store touches memory. *)
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

(** The [if (patLen == 0) return 0] check, when [patLen <> 0]: [i32.eqz]
    is false, so [if] takes its (empty) else branch, which drains to
    [::] immediately -- mirrors [BuildLpsInit.v]'s
    [build_lps_patLen_nonzero_pre] exactly, adjusted for [patLen]
    sitting at local index 3 (not 1) and the frame's 7 locals (not 6). *)
Lemma kmp_search_patLen_nonzero_pre : forall s inst hs f textPtr textLenN patPtr patLenN lpsPtr l5 l6,
  small patLenN -> patLenN <> 0 ->
  f = Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                    VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                    VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 l5);
                    VAL_num (VAL_int32 l6)] inst ->
  reduce_trans (hs, s, f, [:: AI_basic (BI_local_get 3%N); AI_basic (BI_testop T_i32 TO_eqz);
                              AI_basic (BI_if (BT_valtype None)
                                [BI_const_num (VAL_int32 zero32); BI_return] [])])
               (hs, s, f, [::]).
Proof.
  move=> s inst hs f textPtr textLenN patPtr patLenN lpsPtr l5 l6 Hsmall Hne Hf.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 3%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patLenN))) (j := 3%N). rewrite Hf. reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_testop T_i32 TO_eqz);
        AI_basic (BI_if (BT_valtype None) [BI_const_num (VAL_int32 zero32); BI_return] [])] HA.
  have Hs0 : small 0 by rewrite /small; lia.
  have Heqz : app_testop_i i32m TO_eqz (enc patLenN) = false.
  { rewrite /app_testop_i /Wasm_int.int_eqz /=.
    have -> : Wasm_int.Int32.eq zero32 (enc patLenN) = false.
    { rewrite /Wasm_int.Int32.eq.
      have -> : zero32 = enc 0 by reflexivity.
      rewrite (enc_unsigned 0 Hs0) (enc_unsigned patLenN Hsmall).
      case: (Coqlib.zeq 0 patLenN) => Hz; [exfalso; lia | reflexivity]. }
    reflexivity. }
  have HB : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patLenN))); AI_basic (BI_testop T_i32 TO_eqz)]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32))].
  { apply reduce_simple_reduce.
    have := rs_testop_i32 (enc patLenN) TO_eqz.
    rewrite Heqz /=.
    move=> H. exact H. }
  have HB' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None) [BI_const_num (VAL_int32 zero32); BI_return] [])] HB.
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32));
                              AI_basic (BI_if (BT_valtype None) [BI_const_num (VAL_int32 zero32); BI_return] [])]
                    hs s f [:: AI_basic (BI_block (BT_valtype None) [])].
  { apply reduce_simple_reduce.
    apply rs_if_false. reflexivity. }
  have HD : reduce hs s f [:: AI_basic (BI_block (BT_valtype None) [])]
                    hs s f [:: AI_label 0 [::] [::]].
  { apply r_block with (vs := [::]) (n := 0%nat) (m := 0%nat) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  have HE : reduce hs s f [:: AI_label 0 [::] [::]] hs s f [::].
  { apply reduce_simple_reduce. apply rs_label_const. done. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC.
  have Step4 := reduce_trans_step _ _ _ _ _ _ _ _ HD.
  have Step5 := reduce_trans_step _ _ _ _ _ _ _ _ HE.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  have C123 := reduce_trans_trans _ _ _ C12 Step3.
  have C1234 := reduce_trans_trans _ _ _ C123 Step4.
  exact: (reduce_trans_trans _ _ _ C1234 Step5).
Qed.

Lemma kmp_search_init_locals : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr l5 l6,
  let f := Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                         VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                         VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 l5);
                         VAL_num (VAL_int32 l6)] inst in
  let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr 0 0 in
  reduce_trans (hs, s, f, kmp_search_init_es) (hs, s, f', [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr l5 l6 f f'.
  rewrite kmp_search_init_es_eq.
  set f1 := Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                          VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                          VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                          VAL_num (VAL_int32 l6)] inst.
  have HA : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 5%N)]
                    hs s f1 [::].
  { pose proof (@r_local_set _ _ _ f f1 5%N (VAL_num (VAL_int32 zero32)) s (VAL_num (VAL_int32 l5)) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f1 /=. reflexivity.
    - rewrite /f /=. by [].
    - rewrite /f /f1 /=. reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 6%N)] HA.
  have HB : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 6%N)]
                    hs s f' [::].
  { pose proof (@r_local_set _ _ _ f1 f' 6%N (VAL_num (VAL_int32 zero32)) s (VAL_num (VAL_int32 l6)) hs) as Hstep.
    apply Hstep.
    - rewrite /f1 /f' /search_frame /=. reflexivity.
    - rewrite /f1 /=. by [].
    - rewrite /f1 /f' /search_frame /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB.
  exact: (reduce_trans_trans _ _ _ Step1 Step2).
Qed.

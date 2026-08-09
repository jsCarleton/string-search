(** The prologue's [patLen <> 0] case (mirror image of [BuildLps.v]'s
    [build_lps_patLen_zero]) and the loop's 7-instruction init sequence
    ([lps[0] := 0; len := 0; i := 1]): three self-contained instruction-
    level reduction facts, each proven against the real bytecode.

    NOT yet assembled into a single "function entry to loop_entry_cfg"
    theorem, and deliberately so: doing that surfaced a real structural
    question this file leaves open rather than resolving in a hurry.
    [build_lps_patLen_zero] (BuildLps.v) starts from the actual calling
    convention (confirmed against [r_invoke_native], opsem.v:244-255):
    invoking a function wraps its body in an extra label,
    [AI_frame m f' [AI_label m [::] (to_e_list body)]]. But
    [BuildLpsExit.v]'s [loop_entry_cfg] and every theorem built on it
    since (through [BuildLpsInduction.v]) instead use
    [AI_frame 0 f (loop_entry_cfg f)] directly -- one label shallower.
    [loop_entry_cfg]'s own outer label is the [block]'s label (confirmed
    from [build_lps_loop_entry]'s proof, via [r_block]), not the
    function-body label; reduction inside a [block] can't make a label
    around it vanish, so this is a genuine extra label, not just a
    presentational choice, and every [br 1] witness built so far
    (2 labels: loop + block) would need re-deriving one layer deeper to
    close the gap. Resolving this belongs with step 6 (real
    instantiation) in the README's plan, where the actual calling
    convention gets connected to this loop-level reasoning; it needs
    care, not a rushed patch across already-verified files. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps BuildLpsLoop Int32Facts BuildLpsExit.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** The [if (patLen == 0) return] check, when [patLen <> 0]: [i32.eqz]
    is false, so [if] takes its (empty) else branch, which drains to
    [::] immediately. *)
Lemma build_lps_patLen_nonzero_pre : forall s inst hs f patPtr patLenN lpsPtr l3 l4 l5,
  small patLenN -> patLenN <> 0 ->
  f = Build_frame [VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                    VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 l3);
                    VAL_num (VAL_int32 l4); VAL_num (VAL_int32 l5)] inst ->
  reduce_trans (hs, s, f, [:: AI_basic (BI_local_get 1%N); AI_basic (BI_testop T_i32 TO_eqz);
                              AI_basic (BI_if (BT_valtype None) [BI_return] [])])
               (hs, s, f, [::]).
Proof.
  move=> s inst hs f patPtr patLenN lpsPtr l3 l4 l5 Hsmall Hne Hf.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 1%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patLenN))) (j := 1%N). rewrite Hf. reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_testop T_i32 TO_eqz); AI_basic (BI_if (BT_valtype None) [BI_return] [])] HA.
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
  have HB' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_if (BT_valtype None) [BI_return] [])] HB.
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32));
                              AI_basic (BI_if (BT_valtype None) [BI_return] [])]
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

(** The init sequence's store: [lps[0] := 0]. *)
Lemma build_lps_init_store : forall hs s inst patPtr patLenN lpsPtr l3 l4 l5 memaddr m,
  small lpsPtr ->
  let f := Build_frame [VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                         VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 l3);
                         VAL_num (VAL_int32 l4); VAL_num (VAL_int32 l5)] inst in
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N lpsPtr + 4) (operations.mem_length m) ->
  exists s' m',
    lookup_N s'.(s_mems) memaddr = Some m'
    /\ write_bytes (meminst_data m) (Z.to_N lpsPtr) (serialise_num (VAL_int32 zero32)) = Some (meminst_data m')
    /\ reduce_trans (hs, s, f,
         [:: AI_basic (BI_local_get 2%N); AI_basic (BI_const_num (VAL_int32 zero32));
             AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))])
         (hs, s', f, [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr l3 l4 l5 memaddr m Hlp f Hmems Hlkm Hbound.
  have Hsmem : smem s inst = Some m.
  { rewrite /smem Hmems /=. rewrite Hlkm. reflexivity. }
  have HA : reduce hs s f [:: AI_basic (BI_local_get 2%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lpsPtr))) (j := 2%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))] HA.
  have [m' [Hst [Htype Hwr]]] := store_i32_effect m (Z.to_N lpsPtr) zero32 Hbound.
  have HB : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr)));
                               AI_basic (BI_const_num (VAL_int32 zero32));
                               AI_basic (BI_store T_i32 None (Build_memarg 0%N 2%N))]
                    hs (upd_s_mem s (set_nth m' s.(s_mems) (N.to_nat memaddr) m')) f [::].
  { pose proof (@r_store_success _ _ _ T_i32 (VAL_int32 zero32) s f (enc lpsPtr)
      (Build_memarg 0%N 2%N) (upd_s_mem s (set_nth m' s.(s_mems) (N.to_nat memaddr) m')) hs) as Hstep.
    apply Hstep.
    rewrite /smem_store /f /=. rewrite Hmems /=. rewrite Hlkm.
    have HaddrN2 : Z.to_N (Wasm_int.Int32.Z_mod_modulus lpsPtr) = Z.to_N lpsPtr.
    { f_equal. apply Wasm_int.Int32.Z_mod_modulus_id.
      move: Hlp. rewrite /small.
      have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
      rewrite Hmod. lia. }
    rewrite HaddrN2.
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
    have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB.
    exact: (reduce_trans_trans _ _ _ Step1 Step2). }
Qed.

(** The init sequence's two [local.set]s: [len := 0; i := 1]. Unlike
    [seg1_len_inc]/[seg3_i_inc] in [BuildLpsMatch.v]/[BuildLpsIterate.v],
    the values being stored are literal constants already on the
    instruction stream (not [local.get]-loaded), so there is no
    separate "push" reduction step before each [local.set]. *)
Lemma build_lps_init_locals : forall hs s inst patPtr patLenN lpsPtr l3 l4 l5,
  let f := Build_frame [VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                         VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 l3);
                         VAL_num (VAL_int32 l4); VAL_num (VAL_int32 l5)] inst in
  let f' := Build_frame [VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                          VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                          VAL_num (VAL_int32 one32); VAL_num (VAL_int32 l5)] inst in
  reduce_trans (hs, s, f,
    [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 3%N);
        AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_local_set 4%N)])
    (hs, s, f', [::]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr l3 l4 l5 f f'.
  set f1 := Build_frame [VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                          VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                          VAL_num (VAL_int32 l4); VAL_num (VAL_int32 l5)] inst.
  have HA : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 3%N)]
                    hs s f1 [::].
  { pose proof (@r_local_set _ _ _ f f1 3%N (VAL_num (VAL_int32 zero32)) s (VAL_num (VAL_int32 l3)) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f1 /=. reflexivity.
    - rewrite /f /=. by [].
    - rewrite /f /f1 /=. reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_local_set 4%N)] HA.
  have HB : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_local_set 4%N)]
                    hs s f' [::].
  { pose proof (@r_local_set _ _ _ f1 f' 4%N (VAL_num (VAL_int32 one32)) s (VAL_num (VAL_int32 l4)) hs) as Hstep.
    apply Hstep.
    - rewrite /f1 /f' /=. reflexivity.
    - rewrite /f1 /=. by [].
    - rewrite /f1 /f' /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB.
  exact: (reduce_trans_trans _ _ _ Step1 Step2).
Qed.

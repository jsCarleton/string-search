(** Closing the label-depth seam documented in [BuildLpsInit.v]: the
    real function-call entry configuration -- [AI_frame 0 f_entry
    [AI_label 0 [::] (to_e_list build_lps_body)]], matching
    [r_invoke_native] exactly (opsem.v:244-255) -- reduces all the way
    to [::], for any nonempty pattern. This chains the prologue
    ([build_lps_patLen_nonzero_pre]), the init sequence
    ([build_lps_init_store]/[build_lps_init_locals]), loop entry
    ([build_lps_loop_entry]), and the whole loop
    ([build_lps_run_bare]) into one unframed [reduce_trans] fact, then
    lifts it through the extra function-body label (via
    [reduce_trans_label1']) and the calling frame (via
    [reduce_trans_frame']) using the same "lift, then collapse via
    [rs_label_const]/[rs_local_const]" technique already used end-to-end
    in [BuildLps.v]'s [build_lps_patLen_zero]. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith Arith.PeanoNat.
Require Import KMPSpec KMPFailureRec CoreLemmas MemLemmas BuildLps BuildLpsLoop
  Int32Facts BuildLpsExit BuildLpsInit BuildLpsMemTable BuildLpsRun.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

Theorem build_lps_correct : forall hs s inst f0 patPtr patLenN lpsPtr memaddr m (p : list byte)
    (qPtr : Z) (q : list byte),
  small patPtr -> small lpsPtr ->
  patLenN = Z.of_nat (length p) ->
  Nat.lt 0 (length p) ->
  small (Z.of_nat (length p)) ->
  small (Z.of_nat (length p) * 4) ->
  small (patPtr + Z.of_nat (length p)) ->
  small (lpsPtr + Z.of_nat (length p) * 4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (patPtr + Z.of_nat (length p))) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + Z.of_nat (length p) * 4) + 4) (operations.mem_length m) ->
  pat_mem_matches m patPtr p ->
  (patPtr + Z.of_nat (length p) <= lpsPtr \/ lpsPtr + Z.of_nat (length p) * 4 <= patPtr) ->
  (* A second, caller-supplied buffer disjoint from the [lps] output
     array -- e.g. [kmp_search]'s own [text] -- that survives the whole
     call unchanged; see [BuildLpsInduction.v]'s [build_lps_group_fuel_bare]
     for where this is actually tracked. *)
  small qPtr -> small (Z.of_nat (length q)) ->
  pat_mem_matches m qPtr q ->
  (qPtr + Z.of_nat (length q) <= lpsPtr \/ lpsPtr + Z.of_nat (length p) * 4 <= qPtr) ->
  let f_entry := Build_frame [VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                               VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                               VAL_num (VAL_int32 zero32); VAL_num (VAL_int32 zero32)] inst in
  exists s' m' table',
    is_failure_table p table'
    /\ lookup_N s'.(s_mems) memaddr = Some m'
    /\ lps_mem_matches m' lpsPtr table' (length p)
    /\ pat_mem_matches m' patPtr p
    /\ pat_mem_matches m' qPtr q
    /\ operations.mem_length m' = operations.mem_length m
    /\ reduce_trans (hs, s, f0, [:: AI_frame 0 f_entry [:: AI_label 0 [::] (to_e_list build_lps_body)]])
                     (hs, s', f0, [::]).
Proof.
  move=> hs s inst f0 patPtr patLenN lpsPtr memaddr m p qPtr q
    Hpp Hlp HpatLen Hnz Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm Hmempat Hmemlps Hpmm Hnoalias
    Hqp Hqlen Hqmm Hqnoalias f_entry.
  have HpatLen_small : small patLenN by rewrite HpatLen.
  have Hne : patLenN <> 0 by rewrite HpatLen; lia.
  (* Prologue: patLen <> 0, so the early-return check falls through. *)
  have Hpre := build_lps_patLen_nonzero_pre s inst hs f_entry patPtr patLenN lpsPtr
    zero32 zero32 zero32 HpatLen_small Hne erefl.
  have Hpre' := reduce_trans_prefix' _ _ _ _ _ _ _ _ build_lps_es_rest Hpre.
  rewrite List.app_nil_l in Hpre'.
  rewrite -build_lps_es_split in Hpre'.
  rewrite build_lps_es_rest_split build_lps_init_es_eq in Hpre'.
  (* Init store: lps[0] := 0. *)
  have Hbound0 : N.le (Z.to_N lpsPtr + 4) (operations.mem_length m).
  { move: Hmemlps Hlp Hnz; rewrite /small; lia. }
  have [s1 [m1 [Hlkm1 [Hwr1 Hstore]]]] := build_lps_init_store hs s inst patPtr patLenN lpsPtr
    zero32 zero32 zero32 memaddr m Hlp Hmems Hlkm Hbound0.
  have Hstore' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    ([:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 3%N);
         AI_basic (BI_const_num (VAL_int32 one32)); AI_basic (BI_local_set 4%N)] ++ [build_lps_block_es])
    Hstore.
  rewrite List.app_nil_l in Hstore'.
  (* Init locals: len := 0; i := 1. *)
  have Hlocals := build_lps_init_locals hs s1 inst patPtr patLenN lpsPtr zero32 zero32 zero32.
  set f_loop0 := Build_frame [VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                               VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                               VAL_num (VAL_int32 one32); VAL_num (VAL_int32 zero32)] inst in Hlocals.
  have Hlocals' := reduce_trans_prefix' _ _ _ _ _ _ _ _ [:: build_lps_block_es] Hlocals.
  rewrite List.app_nil_l in Hlocals'.
  have Heq_floop : f_loop0 = loop_frame inst patPtr patLenN lpsPtr 0 1 0.
  { rewrite /f_loop0 /loop_frame. reflexivity. }
  rewrite Heq_floop in Hlocals'.
  (* Combine prologue + store + locals into one unframed chain up to
     the [block [loop ...]] instruction. *)
  have Hchain1 := reduce_trans_trans _ _ _ Hstore' Hlocals'.
  have Hchain2 := reduce_trans_trans _ _ _ Hpre' Hchain1.
  (* Enter the loop. *)
  have Hentry := build_lps_loop_entry hs s1 (loop_frame inst patPtr patLenN lpsPtr 0 1 0).
  have Hchain3 := reduce_trans_trans _ _ _ Hchain2 Hentry.
  (* Run the whole loop, starting from position i = 1 (position 0's lps
     entry, 0, was already written directly by the init sequence). *)
  have Hlmm0 : lps_mem_matches m lpsPtr [:: 0%nat] 0 by move=> j v Hj Hnth; exfalso; lia.
  have Hnth0 : nth_error [:: 0%nat] 0 = Some 0%nat by reflexivity.
  have Henc0 : enc (Z.of_nat 0) = zero32 by reflexivity.
  have Hwr1' : write_bytes (meminst_data m) (Z.to_N (lpsPtr + Z.of_nat 0 * 4))
      (serialise_num (VAL_int32 (enc (Z.of_nat 0)))) = Some (meminst_data m1).
  { rewrite Henc0. have -> : lpsPtr + Z.of_nat 0 * 4 = lpsPtr by lia. exact Hwr1. }
  have Hlmm1 : lps_mem_matches m1 lpsPtr [:: 0%nat] 1.
  { apply: (lps_mem_matches_extend m lpsPtr [:: 0%nat] 0 0%nat m1 Hlmm0 Hnth0 _ _ Hwr1').
    - move: Hlp; rewrite /small; lia.
    - move=> j Hj. exfalso. lia. }
  have HmemLen1 : operations.mem_length m1 = operations.mem_length m := write_bytes_mem_length _ _ _ _ Hwr1.
  have Hmempat1 : N.le (Z.to_N (patPtr + Z.of_nat (length p))) (operations.mem_length m1).
  { rewrite HmemLen1. exact Hmempat. }
  have Hmemlps1 : N.le (Z.to_N (lpsPtr + Z.of_nat (length p) * 4) + 4) (operations.mem_length m1).
  { rewrite HmemLen1. exact Hmemlps. }
  have Hdisjoint_addr0 : forall j : N,
    (Z.to_N patPtr <= j)%N -> (j < Z.to_N patPtr + N.of_nat (length p))%N ->
    (j < Z.to_N lpsPtr \/ Z.to_N lpsPtr + N.of_nat 4 <= j)%N.
  { move=> j Hj1 Hj2.
    move: Hpp Hlp Hlenp; rewrite /small; move=> Hpp0 Hlp0 Hlenp0.
    case: Hnoalias => Hna; lia. }
  have Hpmm1 : pat_mem_matches m1 patPtr p.
  { move=> j c Hnth.
    have Hlk := Hpmm j c Hnth.
    have Hj_lt : Nat.lt j (length p) by apply /nth_error_Some; rewrite Hnth.
    have Hj1 : (Z.to_N patPtr <= Z.to_N (patPtr + Z.of_nat j))%N.
    { move: Hpp; rewrite /small; lia. }
    have Hj2 : (Z.to_N (patPtr + Z.of_nat j) < Z.to_N patPtr + N.of_nat (length p))%N.
    { move: Hpp Hlenp; rewrite /small; lia. }
    have Hdisj := Hdisjoint_addr0 (Z.to_N (patPtr + Z.of_nat j)) Hj1 Hj2.
    have Hbslen : length (serialise_num (VAL_int32 zero32)) = 4%nat.
    { rewrite /serialise_num /serialise_i32. apply: Memdata.encode_int_length. }
    rewrite -Hbslen in Hdisj.
    rewrite (write_bytes_out (serialise_num (VAL_int32 zero32)) (meminst_data m) (Z.to_N lpsPtr)
      (meminst_data m1) (Z.to_N (patPtr + Z.of_nat j)) Hwr1 Hdisj).
    exact Hlk. }
  have Hqmm1 : pat_mem_matches m1 qPtr q.
  { move=> j c Hnth.
    have Hlk := Hqmm j c Hnth.
    have Hj_lt : Nat.lt j (length q) by apply /nth_error_Some; rewrite Hnth.
    have Hj1 : (Z.to_N qPtr <= Z.to_N (qPtr + Z.of_nat j))%N.
    { move: Hqp; rewrite /small; lia. }
    have Hj2 : (Z.to_N (qPtr + Z.of_nat j) < Z.to_N qPtr + N.of_nat (length q))%N.
    { move: Hqp Hqlen; rewrite /small; lia. }
    have Hdisj0 : (Z.to_N (qPtr + Z.of_nat j) < Z.to_N lpsPtr \/ Z.to_N lpsPtr + N.of_nat 4 <= Z.to_N (qPtr + Z.of_nat j))%N.
    { move: Hqp Hlp Hqlen Hj1 Hj2; rewrite /small; move=> Hqp0 Hlp0 Hqlen0 Hj1' Hj2'.
      case: Hqnoalias => Hna; lia. }
    have Hbslen : length (serialise_num (VAL_int32 zero32)) = 4%nat.
    { rewrite /serialise_num /serialise_i32. apply: Memdata.encode_int_length. }
    rewrite -Hbslen in Hdisj0.
    rewrite (write_bytes_out (serialise_num (VAL_int32 zero32)) (meminst_data m) (Z.to_N lpsPtr)
      (meminst_data m1) (Z.to_N (qPtr + Z.of_nat j)) Hwr1 Hdisj0).
    exact Hlk. }
  have Htcb1 : table_correct_below p [:: 0%nat] 1.
  { move=> j k Hj Hnth.
    have Hj0 : j = 0%nat by lia.
    subst j. simpl in Hnth. inversion Hnth; subst k.
    exact: (lps_zero_correct p Hnz). }
  have Hilps1 : Nat.lt 1 (length p) -> is_lps p 1 0%nat := fun _ => lps_zero_correct p Hnz.
  have Hik1 : Nat.add 1 (Nat.sub (length p) 1) = length p by lia.
  have Hsmall0 : small (Z.of_nat 0) by rewrite /small; lia.
  have Hrun := build_lps_run_bare (Nat.sub (length p) 1) hs s1 inst patPtr patLenN lpsPtr 0 memaddr m1 p
    [:: 0%nat] 1 0%nat qPtr q
    Hpp Hlp HpatLen Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm1 Hmempat1 Hmemlps1 Hpmm1 Hnoalias
    Hqp Hqlen Hqmm1 Hqnoalias
    Hik1 erefl Htcb1 Hlmm1 Hilps1 Hsmall0 Hsmall0.
  simpl in Hrun.
  move: Hrun => [s' [m' [table' [f' [Htlen' [Htcb' [Hlkm' [Hlmm' [Hpmm' [Hqmm' [HmemLen1' Hred']]]]]]]]]]].
  have Hchain4 := reduce_trans_trans _ _ _ Hchain3 Hred'.
  (* [Hchain4] is the full unframed fact: entry frame's body reduces to
     [::]. Lift it through the function-body label, then the calling
     frame, then collapse both wrappers to nothing. *)
  have Hlab := reduce_trans_label1' _ _ _ _ _ _ _ _ 0 [::] Hchain4.
  have Hfr := reduce_trans_frame' _ _ _ _ _ _ _ _ 0 f0 Hlab.
  have Hcollapse1 : reduce hs s' f' [:: AI_label 0 [::] [::]] hs s' f' [::].
  { apply reduce_simple_reduce. apply rs_label_const. done. }
  have Hcollapse1' := reduce_trans_frame' _ _ _ _ _ _ _ _ 0 f0
    (reduce_trans_step _ _ _ _ _ _ _ _ Hcollapse1).
  have Hcollapse2 : reduce hs s' f0 [:: AI_frame 0 f' [::]] hs s' f0 [::].
  { apply reduce_simple_reduce. apply (@rs_local_const [::] 0 f'); by []. }
  have Hfinal := reduce_trans_trans _ _ _ Hfr Hcollapse1'.
  have Hfinal' := reduce_trans_trans _ _ _ Hfinal (reduce_trans_step _ _ _ _ _ _ _ _ Hcollapse2).
  exists s', m', table'.
  split.
  { split; [exact Htlen' |].
    move=> j k Hnth.
    have Hj_lt : Nat.lt j (length p).
    { have := List.nth_error_Some table' j.
      rewrite Htlen'. move=> [Hn _]. apply Hn. rewrite Hnth. discriminate. }
    exact: (Htcb' j k Hj_lt Hnth). }
  split; [exact Hlkm' |]. split; [exact Hlmm' |]. split; [exact Hpmm' |]. split; [exact Hqmm' |].
  split; [rewrite HmemLen1' HmemLen1; reflexivity |]. exact Hfinal'.
Qed.

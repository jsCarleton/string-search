(** The per-iteration induction tying [build_lps]'s loop to
    [KMPFailureRec.v]'s reference recurrence: running one "group" of
    the loop (the exit-check having already passed, followed by zero
    or more backtracks and finally a match or give-up) computes exactly
    [cand_fuel]'s value and performs the corresponding real
    [reduce_trans]. Structural induction on [fuel] mirrors
    [cand_fuel]'s own recursion exactly: [BuildLpsIterate.v]'s
    [build_lps_iterate_backtrack] is the recursive call, and
    [build_lps_iterate_match]/[_giveup] are the two base cases. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith Arith.PeanoNat.
Require Import KMPSpec KMPFailureRec CoreLemmas MemLemmas BuildLps BuildLpsLoop
  Int32Facts BuildLpsExit BuildLpsCmp BuildLpsMatch BuildLpsMismatch BuildLpsIterate BuildLpsMemTable.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

Theorem build_lps_group_fuel :
  forall hs s inst patPtr patLenN lpsPtr memaddr m (p : list byte) (table : list nat) (i : nat) f0,
  small patPtr -> small lpsPtr ->
  patLenN = Z.of_nat (length p) ->
  small (Z.of_nat (length p)) ->
  small (Z.of_nat (length p) * 4) ->
  small (patPtr + Z.of_nat (length p)) ->
  small (lpsPtr + Z.of_nat (length p) * 4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (patPtr + Z.of_nat (length p))) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + Z.of_nat (length p) * 4) + 4) (operations.mem_length m) ->
  pat_mem_matches m patPtr p ->
  (* The pattern buffer and the [lps] output array don't overlap --
     needed so a match/give-up branch's write into [lps] can't disturb
     [pat_mem_matches], which the *next* group call (chained by
     [BuildLpsRun.v]) needs re-established for the *new* memory [m']. *)
  (patPtr + Z.of_nat (length p) <= lpsPtr \/ lpsPtr + Z.of_nat (length p) * 4 <= patPtr) ->
  Nat.lt i (length p) ->
  length table = i ->
  table_correct_below p table i ->
  (* [tmpN] is pure scratch: [build_lps_iterate_backtrack] overwrites it
     with the backtracked-to length, so unlike every other parameter it
     is *not* fixed across the induction -- it varies with [len]/[fuel],
     which is why it is quantified here rather than above. *)
  forall fuel tmpN len, small tmpN -> Nat.lt len fuel -> Nat.lt len i ->
    is_border p i len -> ruled_out_above p i len ->
    lps_mem_matches m lpsPtr table i ->
    let f := loop_frame inst patPtr patLenN lpsPtr (Z.of_nat len) (Z.of_nat i) tmpN in
    exists s' m' tmpN',
      lookup_N s'.(s_mems) memaddr = Some m'
      /\ lps_mem_matches m' lpsPtr (table ++ [cand_fuel p table i fuel len]) (S i)
      /\ operations.mem_length m' = operations.mem_length m
      /\ pat_mem_matches m' patPtr p
      /\ small tmpN'
      /\ let f' := loop_frame inst patPtr patLenN lpsPtr (Z.of_nat (cand_fuel p table i fuel len)) (Z.of_nat (S i)) tmpN' in
         reduce_trans (hs, s, f0, [:: AI_frame 0 f (loop_entry_cfg f)])
                       (hs, s', f0, [:: AI_frame 0 f' (loop_entry_cfg f')]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr memaddr m p table i f0
    Hpp Hlp HpatLen Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm Hmempat Hmemlps Hpmm Hnoalias Hilt Htlen Htcb.
  have HpatLen_small : small patLenN by rewrite HpatLen.
  elim=> [| fuel' IH] tmpN len Hstp Hfuel Hlt Hborder Hruled Hlmm.
  - exfalso. lia.
  - simpl.
    have Hlen_lenp : Nat.lt len (length p) by lia.
    destruct (nth_error p len) as [cl|] eqn:Hcl; last first.
    { exfalso. apply nth_error_None in Hcl. lia. }
    destruct (nth_error p i) as [ci|] eqn:Hci; last first.
    { exfalso. apply nth_error_None in Hci. lia. }
    have Hmem_cl := Hpmm len cl Hcl.
    have Hmem_ci := Hpmm i ci Hci.
    have Hi_small : small (Z.of_nat i) by move: Hlenp; rewrite /small; lia.
    have Hlen_small : small (Z.of_nat len) by move: Hlenp; rewrite /small; lia.
    have HpatI_small : small (patPtr + Z.of_nat i) by move: Hpatb Hpp; rewrite /small; lia.
    have HpatLenIdx_small : small (patPtr + Z.of_nat len) by move: Hpatb Hpp; rewrite /small; lia.
    have HpatI_bound : N.lt (Z.to_N (patPtr + Z.of_nat i)) (operations.mem_length m).
    { move: Hmempat Hpp; rewrite /small; lia. }
    have HpatLenIdx_bound : N.lt (Z.to_N (patPtr + Z.of_nat len)) (operations.mem_length m).
    { move: Hmempat Hpp; rewrite /small; lia. }
    have Hi_lt_patLen : Z.of_nat i < patLenN by rewrite HpatLen; lia.
    have HiZ4_small : small (Z.of_nat i * 4) by move: Hlenp4; rewrite /small; lia.
    have HlpsI4_small : small (lpsPtr + Z.of_nat i * 4) by move: Hlpsb Hlp; rewrite /small; lia.
    have HlpsI4_bound : N.le (Z.to_N (lpsPtr + Z.of_nat i * 4) + 4) (operations.mem_length m).
    { move: Hmemlps Hlp; rewrite /small; lia. }
    have Hiplus1_small : small (Z.of_nat i + 1) by move: Hlenp; rewrite /small; lia.
    (* The [lps[i]] write address is disjoint from every pattern-byte
       address, so any write there leaves [pat_mem_matches] intact --
       shared by both the match and give-up branches below, since both
       write to the same address [lpsPtr + i*4]. *)
    have Hdisjoint_addr : forall j : N,
      (Z.to_N patPtr <= j)%N -> (j < Z.to_N patPtr + N.of_nat (length p))%N ->
      (j < Z.to_N (lpsPtr + Z.of_nat i * 4) \/ Z.to_N (lpsPtr + Z.of_nat i * 4) + N.of_nat 4 <= j)%N.
    { move=> j Hj1 Hj2.
      move: Hpp Hlp Hlenp; rewrite /small; move=> Hpp0 Hlp0 Hlenp0.
      have HiZ : Z.of_nat i < Z.of_nat (length p) by lia.
      case: Hnoalias => Hna; lia. }
    have Hpmm_preserved : forall m' bs, write_bytes (meminst_data m) (Z.to_N (lpsPtr + Z.of_nat i * 4)) bs = Some (meminst_data m') ->
      length bs = 4%nat -> pat_mem_matches m' patPtr p.
    { move=> m' bs Hwr Hbslen j c Hnth.
      have Hlk := Hpmm j c Hnth.
      have Hj_lt : Nat.lt j (length p) by apply /nth_error_Some; rewrite Hnth.
      have Hj1 : (Z.to_N patPtr <= Z.to_N (patPtr + Z.of_nat j))%N.
      { move: Hpp; rewrite /small; lia. }
      have Hj2 : (Z.to_N (patPtr + Z.of_nat j) < Z.to_N patPtr + N.of_nat (length p))%N.
      { move: Hpp Hlenp; rewrite /small; lia. }
      have Hdisj := Hdisjoint_addr (Z.to_N (patPtr + Z.of_nat j)) Hj1 Hj2.
      rewrite -Hbslen in Hdisj.
      rewrite (write_bytes_out bs (meminst_data m) (Z.to_N (lpsPtr + Z.of_nat i * 4)) (meminst_data m') (Z.to_N (patPtr + Z.of_nat j)) Hwr Hdisj).
      exact Hlk. }
    case: (byte_eq_dec cl ci) => Hcmp.
    + (* Match: [cl = ci], result is [S len]. *)
      subst cl.
      have Hlenplus1_small : small (Z.of_nat len + 1) by move: Hlenp; rewrite /small; lia.
      have [s' [m' [Hlkm' [Hwr' Hred]]]] :=
        build_lps_iterate_match hs s inst patPtr patLenN lpsPtr (Z.of_nat len) (Z.of_nat i) tmpN memaddr m ci f0
          Hpp HpatLen_small Hlp Hlen_small Hi_small Hstp Hi_lt_patLen
          HpatI_small HpatLenIdx_small Hlenplus1_small Hiplus1_small HiZ4_small HlpsI4_small
          Hmems Hlkm Hmem_ci HpatI_bound Hmem_cl HpatLenIdx_bound HlpsI4_bound.
      have HmemLen := write_bytes_mem_length _ _ _ _ Hwr'.
      have Hbslen : length (serialise_num (VAL_int32 (enc (Z.of_nat len + 1)))) = 4%nat.
      { rewrite /serialise_num /serialise_i32. apply: Memdata.encode_int_length. }
      have Hpmm' := Hpmm_preserved m' _ Hwr' Hbslen.
      exists s', m', tmpN.
      split; [exact Hlkm' |].
      split.
      * have Hlmm_ext : lps_mem_matches m lpsPtr (table ++ [S len]) i.
        { move=> j v' Hj Hnth'.
          rewrite List.nth_error_app1 in Hnth'; [| lia].
          exact: (Hlmm j v' Hj Hnth'). }
        have Hnth : nth_error (table ++ [S len]) i = Some (S len).
        { rewrite -Htlen List.nth_error_app2; [| lia]. rewrite Htlen Nat.sub_diag /=. reflexivity. }
        have HlenN1 : Z.of_nat len + 1 = Z.of_nat (S len) by lia.
        rewrite HlenN1 in Hwr'.
        apply: (lps_mem_matches_extend m lpsPtr (table ++ [S len]) i (S len) m' Hlmm_ext Hnth HlpsI4_small _ Hwr').
        move=> j Hj. move: Hlpsb Hlp; rewrite /small; lia.
      * split; [exact HmemLen |].
        split; [exact Hpmm' |].
        split; [exact Hstp |].
        simpl.
        have -> : Z.pos (Pos.of_succ_nat len) = Z.of_nat len + 1 by lia.
        have -> : Z.pos (Pos.of_succ_nat i) = Z.of_nat i + 1 by lia.
        exact Hred.
    + (* Mismatch: [cl <> ci]. *)
      have Hcmp' : ci <> cl by congruence.
      case: len Hlt Hborder Hruled Hlmm Hlen_lenp Hcl Hmem_cl Hfuel HpatLenIdx_small HpatLenIdx_bound Hlen_small
        => [| len'] Hlt Hborder Hruled Hlmm Hlen_lenp Hcl Hmem_cl Hfuel HpatLenIdx_small HpatLenIdx_bound Hlen_small.
      * (* len = 0: give up, result 0. *)
        have HpatZ_small : small (patPtr + Z.of_nat 0) by move: Hpatb Hpp; rewrite /small; lia.
        have HpatZ_bound : N.lt (Z.to_N (patPtr + Z.of_nat 0)) (operations.mem_length m).
        { move: Hmempat Hpp; rewrite /small; lia. }
        have Hmem_c0 : mem_lookup (Z.to_N (patPtr + 0)) m.(meminst_data) = Some cl.
        { have -> : (patPtr + 0) = (patPtr + Z.of_nat 0) by lia. exact Hmem_cl. }
        have Hbound0 : N.lt (Z.to_N (patPtr + 0)) (operations.mem_length m).
        { have -> : (patPtr + 0) = (patPtr + Z.of_nat 0) by lia. exact HpatZ_bound. }
        have [s' [m' [Hlkm' [Hwr' Hred]]]] :=
          build_lps_iterate_giveup hs s inst patPtr patLenN lpsPtr (Z.of_nat i) tmpN memaddr m ci cl f0
            Hpp HpatLen_small Hlp Hi_small Hstp Hi_lt_patLen Hcmp'
            HpatI_small HpatZ_small Hiplus1_small HiZ4_small HlpsI4_small
            Hmems Hlkm Hmem_ci HpatI_bound Hmem_c0 Hbound0 HlpsI4_bound.
        have HmemLen := write_bytes_mem_length _ _ _ _ Hwr'.
        have Hbslen : length (serialise_num (VAL_int32 zero32)) = 4%nat.
        { rewrite /serialise_num /serialise_i32. apply: Memdata.encode_int_length. }
        have Hpmm' := Hpmm_preserved m' _ Hwr' Hbslen.
        exists s', m', tmpN.
        split; [exact Hlkm' |].
        split.
        { have Hlmm_ext : lps_mem_matches m lpsPtr (table ++ [0%nat]) i.
          { move=> j v' Hj Hnth'.
            rewrite List.nth_error_app1 in Hnth'; [| lia].
            exact: (Hlmm j v' Hj Hnth'). }
          have Hnth : nth_error (table ++ [0%nat]) i = Some 0%nat.
          { rewrite -Htlen List.nth_error_app2; [| lia]. rewrite Htlen Nat.sub_diag /=. reflexivity. }
          have Hz : zero32 = enc (Z.of_nat 0) by reflexivity.
          rewrite Hz in Hwr'.
          apply: (lps_mem_matches_extend m lpsPtr (table ++ [0%nat]) i 0%nat m' Hlmm_ext Hnth HlpsI4_small _ Hwr').
          move=> j Hj. move: Hlpsb Hlp; rewrite /small; lia. }
        { split; [exact HmemLen |].
          split; [exact Hpmm' |].
          split; [exact Hstp |].
          simpl.
          have -> : Z.pos (Pos.of_succ_nat i) = Z.of_nat i + 1 by lia.
          exact Hred. }
      * (* len = S len': backtrack to [table[len']]. *)
        have Hlen'_i : Nat.lt len' i by lia.
        have Hlen'_tab : Nat.lt len' (length table) by lia.
        have [v Htv] : exists v, nth_error table len' = Some v.
        { destruct (nth_error table len') as [v|] eqn:E; [by exists v |].
          exfalso. apply nth_error_None in E. lia. }
        have Hvdef : nth_default 0%nat table len' = v by rewrite /nth_default Htv.
        have Htcb' : is_lps p (S len') v := Htcb len' v Hlen'_i Htv.
        have Hborder_Slen' : is_border p (S len') v := proj1 Htcb'.
        have Hv_lt : Nat.lt v (S len') by have [_ [? _]] := Htcb'; lia.
        have Hv_le : Nat.le v (S len') by lia.
        have Hborder_new : is_border p i v.
        { have Hbc := border_chain p i (S len') v Hborder Hv_le.
          apply Hbc. exact Hborder_Slen'. }
        have Hruled_new : ruled_out_above p i v.
        { move=> b Hb_border Hvb Hbi.
          case: (Nat.le_gt_cases (S len') b) => Hcase.
          - case: (Nat.eq_dec b (S len')) => Heqb.
            + subst b. rewrite Hcl Hci. move=> Heq. apply Hcmp'. inversion Heq. reflexivity.
            + apply: Hruled; [exact Hb_border | lia | exact Hbi].
          - exfalso.
            have Hb_le : Nat.le b (S len') by lia.
            have Hbc2 := border_chain p i (S len') b Hborder Hb_le.
            have Hborder_b : is_border p (S len') b.
            { apply Hbc2. exact Hb_border. }
            have Hb_proper : Nat.lt b (S len') by lia.
            have [_ [_ Hmax]] := Htcb'.
            have := Hmax b Hborder_b Hb_proper.
            lia. }
        have Hv_small : small (Z.of_nat v) by move: Hlenp; rewrite /small; lia.
        have HaddrEq : Z.of_nat (S len') - 1 = Z.of_nat len' by lia.
        have Hlen'_small : small (Z.of_nat (S len') - 1).
        { rewrite HaddrEq. move: Hlenp; rewrite /small; lia. }
        have Hlen'4_small : small ((Z.of_nat (S len') - 1) * 4).
        { rewrite HaddrEq. move: Hlenp4; rewrite /small; lia. }
        have HlpsLen'4_small : small (lpsPtr + (Z.of_nat (S len') - 1) * 4).
        { rewrite HaddrEq. move: Hlpsb Hlp; rewrite /small; lia. }
        have HlpsLen'4_bound : N.le (Z.to_N (lpsPtr + (Z.of_nat (S len') - 1) * 4) + 4) (operations.mem_length m).
        { rewrite HaddrEq. move: Hmemlps Hlp; rewrite /small; lia. }
        have Hlmm_v := Hlmm len' v Hlen'_i Htv.
        have Hlmm_v' : read_bytes m (Z.to_N (lpsPtr + (Z.of_nat (S len') - 1) * 4)) 4
                     = Some (serialise_num (VAL_int32 (enc (Z.of_nat v)))).
        { rewrite HaddrEq. exact Hlmm_v. }
        have HSlen'_ge1 : 1 <= Z.of_nat (S len') by lia.
        have Hback := build_lps_iterate_backtrack hs s inst patPtr patLenN lpsPtr (Z.of_nat (S len'))
          (Z.of_nat i) tmpN memaddr m ci cl (Z.of_nat v) f0
          Hpp HpatLen_small Hlp Hlen_small Hi_small Hstp Hi_lt_patLen Hcmp'
          HpatI_small HpatLenIdx_small
          HSlen'_ge1 Hlen'_small Hlen'4_small HlpsLen'4_small Hv_small
          Hmems Hlkm Hmem_ci HpatI_bound Hmem_cl HpatLenIdx_bound Hlmm_v' HlpsLen'4_bound.
        have HrIH := IH (Z.of_nat v) v Hv_small (ltac:(lia)) (ltac:(lia)) Hborder_new Hruled_new Hlmm.
        move: HrIH => [s'' [m'' [tmpN'' [Hlkm'' [Hlmm'' [HmemLen'' [Hpmm'' [Hstp'' Hred'']]]]]]]].
        exists s'', m'', tmpN''.
        rewrite Hvdef.
        split; [exact Hlkm'' |]. split; [exact Hlmm'' |]. split; [exact HmemLen'' |]. split; [exact Hpmm'' |].
        split; [exact Hstp'' |].
        exact: (reduce_trans_trans _ _ _ Hback Hred'').
Qed.

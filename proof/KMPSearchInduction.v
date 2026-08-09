(** The per-position induction tying [kmp_search]'s loop to
    [KMPSearchRec.v]'s invariants: running the loop starting from
    position [i] (possibly backtracking [j] several times against
    [pat]'s already-known failure table) either reaches position
    [S i] with the invariants re-established there, or finds the whole
    pattern and returns -- mirroring [BuildLpsInduction.v]'s
    [build_lps_group_fuel], but with an extra disjunctive outcome since
    [kmp_search], unlike [build_lps], can exit mid-position via
    [return]. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith Arith.PeanoNat.
Require Import KMPSpec KMPFailureRec KMPSearchRec CoreLemmas MemLemmas BuildLps BuildLpsLoop
  BuildLpsMemTable Int32Facts KMPSearch KMPSearchLoop KMPSearchExit KMPSearchCmp
  KMPSearchMatch KMPSearchMismatch KMPSearchIterate KMPSearchMatchReturn.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** [_bare] on the "continue" side (mirroring [BuildLpsIterate.v]'s
    pattern), fully wrapped on the "return" side (unavoidable, since
    [rs_return] inherently needs the frame). *)
Theorem kmp_search_group_fuel :
  forall hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m (txt pat : text) (table : list nat) (i : nat),
  small textPtr -> small patPtr -> small lpsPtr ->
  textLenN = Z.of_nat (length txt) -> patLenN = Z.of_nat (length pat) ->
  small (Z.of_nat (length txt)) -> small (Z.of_nat (length pat)) -> small (Z.of_nat (length pat) * 4) ->
  small (textPtr + Z.of_nat (length txt)) -> small (patPtr + Z.of_nat (length pat)) ->
  small (lpsPtr + Z.of_nat (length pat) * 4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (textPtr + Z.of_nat (length txt))) (operations.mem_length m) ->
  N.le (Z.to_N (patPtr + Z.of_nat (length pat))) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + Z.of_nat (length pat) * 4)) (operations.mem_length m) ->
  pat_mem_matches m textPtr txt -> pat_mem_matches m patPtr pat ->
  is_failure_table pat table -> lps_mem_matches m lpsPtr table (length pat) ->
  Nat.lt i (length txt) ->
  forall fuel j, small (Z.of_nat j) -> Nat.lt j fuel -> Nat.lt j (length pat) ->
    search_matches txt pat i j -> search_no_occ_before txt pat (i - j) ->
    let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (Z.of_nat i) (Z.of_nat j) in
    (exists j',
       small (Z.of_nat j') /\ Nat.lt j' (length pat) /\
       search_matches txt pat (S i) j' /\ search_no_occ_before txt pat (S i - j') /\
       let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (Z.of_nat (S i)) (Z.of_nat j') in
       reduce_trans (hs, s, f, search_loop_entry_cfg f) (hs, s, f', search_loop_entry_cfg f'))
    \/ (exists v,
       is_first_occurrence txt pat v /\
       reduce_trans (hs, s, f0, [:: AI_frame 1 f [:: AI_label 1 [::] (search_loop_entry_cfg f)]])
                     (hs, s, f0, [:: AI_basic (BI_const_num (VAL_int32 (enc (Z.of_nat v))))])).
Proof.
  move=> hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m txt pat table i
    Hp1 Hp2 Hp3 HtextLen HpatLen Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
    Hmems Hlkm Hmemt Hmemp Hmemlps Htmt Htmp Hift Hlmm Hilt.
  have HtextLen_small : small textLenN by rewrite HtextLen.
  have HpatLen_small : small patLenN by rewrite HpatLen.
  elim=> [| fuel' IH] j Hj_small Hfuel Hjlt Hm Hno f.
  - exfalso. lia.
  - have Hji : Nat.le j i by have [_ [Hji0 _]] := Hm.
    have Hi_small : small (Z.of_nat i) by move: Hlent; rewrite /small; lia.
    destruct (nth_error txt i) as [ci|] eqn:Hci; last first.
    { exfalso. apply nth_error_None in Hci. lia. }
    destruct (nth_error pat j) as [cj|] eqn:Hcj; last first.
    { exfalso. apply nth_error_None in Hcj. lia. }
    have Hmem_ci := Htmt i ci Hci.
    have HtextI_small : small (textPtr + Z.of_nat i) by move: Htextb Hp1; rewrite /small; lia.
    have HtextI_bound : N.lt (Z.to_N (textPtr + Z.of_nat i)) (operations.mem_length m).
    { move: Hmemt Hp1; rewrite /small; lia. }
    have Hi_lt_textLen : Z.of_nat i < textLenN by rewrite HtextLen; lia.
    case: (byte_eq_dec ci cj) => Hcmp.
    + (* Match: text[i] = pat[j]. *)
      subst cj.
      have Hj_lt_patLen : Nat.lt j (length pat).
      { apply /nth_error_Some; rewrite Hcj; discriminate. }
      have Hmem_cj := Htmp j ci Hcj.
      have HpatJ_small : small (patPtr + Z.of_nat j) by move: Hpatb Hp2; rewrite /small; lia.
      have HpatJ_bound : N.lt (Z.to_N (patPtr + Z.of_nat j)) (operations.mem_length m).
      { move: Hmemp Hp2; rewrite /small; lia. }
      have Hji1_small : small (Z.of_nat i + 1) by move: Hlent; rewrite /small; lia.
      have Hjj1_small : small (Z.of_nat j + 1) by move: Hlenp; rewrite /small; lia.
      case: (Nat.eq_dec (S j) (length pat)) => Heos.
      * (* Full pattern found: return. *)
        right.
        have Hji_le : Z.of_nat j <= Z.of_nat i by lia.
        have Hheq : Z.of_nat j + 1 = Z.of_nat (S j) by lia.
        have Hret := kmp_search_match_return hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr
          (Z.of_nat i) (Z.of_nat j) memaddr m ci ci
          Hp1 HtextLen_small Hp2 HpatLen_small Hp3 Hi_small Hj_small
          Hi_lt_textLen Hji_le (ltac:(rewrite HpatLen; lia))
          HtextI_small HpatJ_small Hji1_small Hjj1_small
          Hmems Hlkm Hmem_ci HtextI_bound Hmem_cj HpatJ_bound erefl.
        exists (Nat.sub (Nat.add i 1) (Nat.add j 1)).
        split.
        { have HmS : search_matches txt pat (S i) (S j) := search_matches_extend txt pat i j ci Hm Hci Hcj.
          have Heqn : Nat.sub (Nat.add i 1) (Nat.add j 1) = Nat.sub (S i) (S j) by lia.
          rewrite Heqn.
          exact: (search_matches_is_first_occurrence txt pat i j HmS (ltac:(lia)) (ltac:(lia)) Hno). }
        { have -> : Z.of_nat (Nat.sub (Nat.add i 1) (Nat.add j 1)) = Z.of_nat i + 1 - (Z.of_nat j + 1) by lia.
          exact Hret. }
      * (* Match but not done: continue to (S i, S j). *)
        left.
        have Hjj1_ne : Nat.add j 1 <> length pat by lia.
        have Hcont := kmp_search_iterate_match_continue hs s inst textPtr textLenN patPtr patLenN lpsPtr
          (Z.of_nat i) (Z.of_nat j) memaddr m ci
          Hp1 HtextLen_small Hp2 HpatLen_small Hp3 Hi_small Hj_small
          Hi_lt_textLen HtextI_small HpatJ_small Hji1_small Hjj1_small
          (ltac:(rewrite HpatLen; lia))
          Hmems Hlkm Hmem_ci HtextI_bound Hmem_cj HpatJ_bound.
        exists (S j).
        split; [move: Hlenp; rewrite /small; lia |].
        split; [lia |].
        split; [exact: (search_matches_extend txt pat i j ci Hm Hci Hcj) |].
        split.
        { exact Hno. }
        { have -> : Z.of_nat (S j) = Z.of_nat j + 1 by lia.
          have -> : Z.of_nat (S i) = Z.of_nat i + 1 by lia.
          exact Hcont. }
    + (* Mismatch: text[i] <> pat[j]. *)
      have Hlenpat_pos : Nat.lt 0 (length pat) by lia.
      have Hf_eq : f = search_frame inst textPtr textLenN patPtr patLenN lpsPtr (Z.of_nat i) (Z.of_nat j) by [].
      rewrite Hf_eq.
      clear Hf_eq f.
      case: j Hj_small Hfuel Hjlt Hm Hno Hji Hcj Hmem_ci Hcmp
        => [| j'] Hj_small Hfuel Hjlt Hm Hno Hji Hcj Hmem_ci Hcmp.
      * (* j = 0: give up, i -> S i, j stays 0. *)
        have Hjb0_small : small (patPtr + 0) by move: Hp2; rewrite /small; lia.
        have Hji1_small : small (Z.of_nat i + 1) by move: Hlent; rewrite /small; lia.
        have Hmem_c0 := Htmp 0%nat cj Hcj.
        have HpatZ_bound : N.lt (Z.to_N (patPtr + 0)) (operations.mem_length m).
        { move: Hmemp Hp2 Hlenp; rewrite /small; lia. }
        have Hcmp' : ci <> cj by exact Hcmp.
        have Hgu := kmp_search_iterate_giveup hs s inst textPtr textLenN patPtr patLenN lpsPtr
          (Z.of_nat i) memaddr m ci cj
          Hp1 HtextLen_small Hp2 HpatLen_small Hp3 Hi_small
          Hi_lt_textLen Hcmp' HtextI_small Hjb0_small Hji1_small
          Hmems Hlkm Hmem_ci HtextI_bound Hmem_c0 HpatZ_bound.
        left.
        exists 0%nat.
        split; [rewrite /small; lia |].
        split; [exact Hlenpat_pos |].
        split; [exact: (search_matches_zero txt pat (S i) (ltac:(lia))) |].
        split.
        { exact: (search_no_occ_giveup txt pat i ci cj Hno Hci Hcj Hcmp). }
        { have -> : Z.of_nat (S i) = Z.of_nat i + 1 by lia.
          have -> : Z.of_nat 0 = 0 by lia.
          exact Hgu. }
      * (* j = S j': backtrack to table[j']. *)
        have Hj'_lt : Nat.lt j' (length table) by have [Hift0 _] := Hift; lia.
        have [v Htv] : exists v, nth_error table j' = Some v.
        { destruct (nth_error table j') as [v|] eqn:E; [by exists v |].
          exfalso. apply nth_error_None in E. lia. }
        have Hislps : is_lps pat (S j') v := (proj2 Hift) j' v Htv.
        have Hv_lt : Nat.lt v (S j') by have [_ [? _]] := Hislps; lia.
        have Hv_small : small (Z.of_nat v) by move: Hlenp; rewrite /small; lia.
        have HaddrEq : Z.of_nat (S j') - 1 = Z.of_nat j' by lia.
        have Hj'_small : small (Z.of_nat (S j') - 1).
        { rewrite HaddrEq. move: Hlenp; rewrite /small; lia. }
        have Hj'4_small : small ((Z.of_nat (S j') - 1) * 4).
        { rewrite HaddrEq. move: Hlenp4; rewrite /small; lia. }
        have HlpsJ'4_small : small (lpsPtr + (Z.of_nat (S j') - 1) * 4).
        { rewrite HaddrEq. move: Hp3 Hlpsb; rewrite /small; lia. }
        have HjSj'_small : small (Z.of_nat (S j')) by move: Hlenp; rewrite /small; lia.
        have HpatSj'_small : small (patPtr + Z.of_nat (S j')) by move: Hpatb Hp2; rewrite /small; lia.
        have HpatSj'_bound : N.lt (Z.to_N (patPtr + Z.of_nat (S j'))) (operations.mem_length m).
        { move: Hmemp Hp2 Hlenp; rewrite /small; lia. }
        have Hmem_cSj' := Htmp (S j') cj Hcj.
        have Hj'_lt_pat : Nat.lt j' (length pat) by have [Hift0 _] := Hift; lia.
        have Hlmm_v : read_bytes m (Z.to_N (lpsPtr + (Z.of_nat (S j') - 1) * 4)) 4
                    = Some (serialise_num (VAL_int32 (enc (Z.of_nat v)))).
        { rewrite HaddrEq. exact: (Hlmm j' v Hj'_lt_pat Htv). }
        have HlpsJ'4_bound : N.le (Z.to_N (lpsPtr + (Z.of_nat (S j') - 1) * 4) + 4) (operations.mem_length m).
        { rewrite HaddrEq. move: Hmemlps Hp3 Hlpsb Hlenp; rewrite /small; lia. }
        have Hcmp' : ci <> cj by exact Hcmp.
        have Hback := kmp_search_iterate_backtrack hs s inst textPtr textLenN patPtr patLenN lpsPtr
          (Z.of_nat i) (Z.of_nat (S j')) memaddr m ci cj (Z.of_nat v)
          Hp1 HtextLen_small Hp2 HpatLen_small Hp3 Hi_small HjSj'_small
          Hi_lt_textLen Hcmp' HtextI_small HpatSj'_small
          (ltac:(lia)) Hj'_small Hj'4_small HlpsJ'4_small Hv_small
          Hmems Hlkm Hmem_ci HtextI_bound Hmem_cSj' HpatSj'_bound
          Hlmm_v HlpsJ'4_bound.
        simpl in Hback.
        have HrIH := IH v Hv_small (ltac:(lia)) (ltac:(have [Hift0 _] := Hift; lia))
          (search_matches_backtrack txt pat i (S j') v Hm (proj1 Hislps))
          (search_no_occ_backtrack txt pat i (S j') v ci cj Hm Hno Hislps Hci Hcj Hcmp).
        simpl in HrIH.
        destruct HrIH as [HrIHL|HrIHR].
        + move: HrIHL => [j'' [Hj''_small [Hj''_lt [Hm'' [Hno'' Hred'']]]]].
          left.
          exists j''.
          split; [exact Hj''_small |]. split; [exact Hj''_lt |]. split; [exact Hm'' |]. split; [exact Hno'' |].
          exact: (reduce_trans_trans _ _ _ Hback Hred'').
        + move: HrIHR => [w [Hfound Hredw]].
          right.
          exists w.
          split; [exact Hfound |].
          have HbackLab := reduce_trans_label1' _ _ _ _ _ _ _ _ 1 [::] Hback.
          have HbackFr := reduce_trans_frame' _ _ _ _ _ _ _ _ 1 f0 HbackLab.
          exact: (reduce_trans_trans _ _ _ HbackFr Hredw).
Qed.

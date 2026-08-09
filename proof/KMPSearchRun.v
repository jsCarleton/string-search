(** The outer induction over [i]: chains [kmp_search_group_fuel]
    (one call per text position) together with [kmp_search_exit_bare]
    (the final step, once [i] reaches [length txt]) into a single
    theorem covering the *entire* loop, from wherever it's entered
    (any [i], with the right invariants) through to completion --
    either [does_not_occur] (the loop runs out of text) or
    [is_first_occurrence] (some position returns). The [kmp_search]
    analogue of [BuildLpsRun.v]. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith Arith.PeanoNat.
Require Import KMPSpec KMPFailureRec KMPSearchRec CoreLemmas MemLemmas BuildLps BuildLpsLoop
  BuildLpsMemTable Int32Facts KMPSearch KMPSearchLoop KMPSearchExit KMPSearchCmp
  KMPSearchMatch KMPSearchMismatch KMPSearchIterate KMPSearchMatchReturn KMPSearchInduction.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

Theorem kmp_search_run : forall k hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m
    (txt pat : text) (table : list nat) (i j : nat),
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
  Nat.add i k = length txt ->
  small (Z.of_nat j) -> Nat.lt j (length pat) ->
  search_matches txt pat i j -> search_no_occ_before txt pat (i - j) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr (Z.of_nat i) (Z.of_nat j) in
  (does_not_occur txt pat /\
     reduce_trans (hs, s, f0, [:: AI_frame 1 f [:: AI_label 1 [::] (search_loop_entry_cfg f ++ kmp_search_final_es)]])
                  (hs, s, f0, [:: AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (-1))))]))
  \/ (exists v, is_first_occurrence txt pat v /\
     reduce_trans (hs, s, f0, [:: AI_frame 1 f [:: AI_label 1 [::] (search_loop_entry_cfg f ++ kmp_search_final_es)]])
                  (hs, s, f0, [:: AI_basic (BI_const_num (VAL_int32 (enc (Z.of_nat v))))])).
Proof.
  elim=> [| k' IH] hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m txt pat table i j
    Hp1 Hp2 Hp3 HtextLen HpatLen Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
    Hmems Hlkm Hmemt Hmemp Hmemlps Htmt Htmp Hift Hlmm Hik Hj_small Hjlt Hm Hno f.
  - (* k = 0: i = length txt, the loop exits. *)
    have Hi_eq : i = length txt by lia.
    have Hi_small : small (Z.of_nat i) by move: Hlent; rewrite /small; lia.
    have HtextLen_small : small textLenN by rewrite HtextLen.
    have Hge : textLenN <= Z.of_nat i by rewrite HtextLen Hi_eq; lia.
    have HpatLen_small : small patLenN by rewrite HpatLen.
    have Hexit := kmp_search_exit_bare hs s inst textPtr textLenN patPtr patLenN lpsPtr (Z.of_nat i) (Z.of_nat j)
      Hp1 HtextLen_small Hp2 HpatLen_small Hp3 Hi_small Hj_small Hge.
    simpl in Hexit.
    have HexitLab := reduce_trans_label1' _ _ _ _ _ _ _ _ 1 [::] Hexit.
    have HexitFr := reduce_trans_frame' _ _ _ _ _ _ _ _ 1 f0 HexitLab.
    have Hcollapse1 : reduce hs s f [:: AI_label 1 [::] kmp_search_final_es] hs s f kmp_search_final_es.
    { apply reduce_simple_reduce. apply rs_label_const. done. }
    have Hcollapse1' := reduce_frame _ _ _ _ _ _ _ _ 1 f0 Hcollapse1.
    have Hcollapse2 : reduce hs s f0 [:: AI_frame 1 f kmp_search_final_es] hs s f0 kmp_search_final_es.
    { apply reduce_simple_reduce. apply (@rs_local_const kmp_search_final_es 1 f); by []. }
    have Hfinal := reduce_trans_trans _ _ _ HexitFr (reduce_trans_step _ _ _ _ _ _ _ _ Hcollapse1').
    have Hfinal' := reduce_trans_trans _ _ _ Hfinal (reduce_trans_step _ _ _ _ _ _ _ _ Hcollapse2).
    rewrite kmp_search_final_es_eq in Hfinal'.
    left.
    split; [exact: (search_no_occ_before_does_not_occur txt pat i j Hi_eq Hjlt Hno) | exact Hfinal'].
  - (* k = S k': process position i, then recurse at S i. *)
    have Hi_lt : Nat.lt i (length txt) by lia.
    have Hgf := kmp_search_group_fuel hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m txt pat table i
      Hp1 Hp2 Hp3 HtextLen HpatLen Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
      Hmems Hlkm Hmemt Hmemp Hmemlps Htmt Htmp Hift Hlmm Hi_lt
      (S j) j Hj_small (ltac:(lia)) Hjlt Hm Hno.
    simpl in Hgf.
    destruct Hgf as [HgfL | HgfR].
    + move: HgfL => [j' [Hj'_small [Hj'_lt [Hm' [Hno' Hred']]]]].
      have Hred'' := reduce_trans_prefix' _ _ _ _ _ _ _ _ kmp_search_final_es Hred'.
      have HredLab := reduce_trans_label1' _ _ _ _ _ _ _ _ 1 [::] Hred''.
      have HredFr := reduce_trans_frame' _ _ _ _ _ _ _ _ 1 f0 HredLab.
      have Hik' : Nat.add (S i) k' = length txt by lia.
      have HrIH := IH hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m txt pat table (S i) j'
        Hp1 Hp2 Hp3 HtextLen HpatLen Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
        Hmems Hlkm Hmemt Hmemp Hmemlps Htmt Htmp Hift Hlmm Hik' Hj'_small Hj'_lt Hm' Hno'.
      simpl in HrIH.
      destruct HrIH as [[Hnocc HredIH] | [w [Hfound HredIH]]].
      * left. split; [exact Hnocc |]. exact: (reduce_trans_trans _ _ _ HredFr HredIH).
      * right. exists w. split; [exact Hfound |]. exact: (reduce_trans_trans _ _ _ HredFr HredIH).
    + move: HgfR => [v [Hfound Hredv]].
      right. exists v. split; [exact Hfound | exact Hredv].
Qed.

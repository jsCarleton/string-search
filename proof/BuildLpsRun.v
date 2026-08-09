(** The outer induction over [i]: chains [build_lps_group_fuel]
    (one call per position) together with [build_lps_exit] (the final
    step, once [i] reaches [length p]) into a single theorem covering
    the *entire* loop, from wherever it's entered (any [i], with the
    right invariants) through to completion, producing a table
    satisfying [KMPSpec.is_failure_table]. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith Arith.PeanoNat.
Require Import KMPSpec KMPFailureRec CoreLemmas MemLemmas BuildLps BuildLpsLoop
  Int32Facts BuildLpsExit BuildLpsCmp BuildLpsMatch BuildLpsMismatch BuildLpsIterate
  BuildLpsMemTable BuildLpsInduction.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** Induction on [k], the number of positions remaining ([i + k =
    length p]): each step is one call to [build_lps_group_fuel]
    (processing position [i], via [cand]'s value there, matching
    [cand_correct]'s own math fact for the same position) followed by
    the induction hypothesis at [S i]; the base case ([k = 0], [i =
    length p]) is [build_lps_exit]. *)
Theorem build_lps_run : forall k hs s inst patPtr patLenN lpsPtr tmpN memaddr m (p : list byte) (table : list nat) (i len : nat) f0,
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
  (patPtr + Z.of_nat (length p) <= lpsPtr \/ lpsPtr + Z.of_nat (length p) * 4 <= patPtr) ->
  Nat.add i k = length p ->
  length table = i ->
  table_correct_below p table i ->
  lps_mem_matches m lpsPtr table i ->
  (Nat.lt i (length p) -> is_lps p i len) ->
  small (Z.of_nat len) ->
  small tmpN ->
  let f := loop_frame inst patPtr patLenN lpsPtr (Z.of_nat len) (Z.of_nat i) tmpN in
  exists s' m' table',
    length table' = length p
    /\ table_correct_below p table' (length p)
    /\ lookup_N s'.(s_mems) memaddr = Some m'
    /\ lps_mem_matches m' lpsPtr table' (length p)
    /\ reduce_trans (hs, s, f0, [:: AI_frame 0 f (loop_entry_cfg f)]) (hs, s', f0, [::]).
Proof.
  elim=> [| k' IH] hs s inst patPtr patLenN lpsPtr tmpN memaddr m p table i len f0
    Hpp Hlp HpatLen Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm Hmempat Hmemlps Hpmm Hnoalias
    Hik Htlen Htcb Hlmm Hilps Hlen_small Htp_small f.
  - (* k = 0: i = length p, the loop exits. *)
    have Hi_eq : i = length p by lia.
    have HpatLen_small : small patLenN by rewrite HpatLen.
    have Hi_small : small (Z.of_nat i) by move: Hlenp; rewrite /small; lia.
    have Hge : patLenN <= Z.of_nat i by rewrite HpatLen Hi_eq; lia.
    have Hred := build_lps_exit hs s inst patPtr patLenN lpsPtr (Z.of_nat len) (Z.of_nat i) tmpN f0
      Hpp HpatLen_small Hlp Hlen_small Hi_small Htp_small Hge.
    simpl in Hred.
    exists s, m, table.
    split; [rewrite -Hi_eq; exact Htlen |].
    split; [rewrite -Hi_eq; exact Htcb |].
    split; [exact Hlkm |].
    split; [rewrite -Hi_eq; exact Hlmm |].
    exact Hred.
  - (* k = S k': process position i, then recurse at S i. *)
    have Hi_lt : Nat.lt i (length p) by lia.
    have Hilps' : is_lps p i len := Hilps Hi_lt.
    have Hborder : is_border p i len := proj1 Hilps'.
    have Hruled : ruled_out_above p i len := ruled_out_above_of_is_lps p i len Hilps'.
    have Hlt_i : Nat.lt len i by have [_ [? _]] := Hilps'; lia.
    have Htab_le : Nat.le i (length table) by lia.
    have Hlen_fuel : Nat.lt len (length p) by lia.
    have [s'' [m'' [tmpN'' [Hlkm'' [Hlmm'' [HmemLen'' [Hpmm'' [Htp_small'' Hred'']]]]]]]] :=
      build_lps_group_fuel hs s inst patPtr patLenN lpsPtr memaddr m p table i f0
        Hpp Hlp HpatLen Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm Hmempat Hmemlps Hpmm Hnoalias
        Hi_lt Htlen Htcb (length p) tmpN len Htp_small Hlen_fuel Hlt_i Hborder Hruled Hlmm.
    simpl in Hred''.
    set v := cand_fuel p table i (length p) len.
    have Hcand_eq : cand p table i len = v by rewrite /cand /v.
    have Hcorrect := cand_correct p table i Hi_lt Htab_le Htcb len Hlt_i Hborder Hruled.
    rewrite Hcand_eq in Hcorrect.
    have Htcb' := table_correct_below_extend p table i v Htlen Htcb Hcorrect.
    have Hv_le : Nat.le v i by have [_ [? _]] := Hcorrect; lia.
    have Hv_small : small (Z.of_nat v) by move: Hlenp; rewrite /small; lia.
    have Htlen' : length (table ++ [v]) = S i by rewrite List.length_app Htlen /=; lia.
    have Hik' : Nat.add (S i) k' = length p by lia.
    have Hmempat'' : N.le (Z.to_N (patPtr + Z.of_nat (length p))) (operations.mem_length m'').
    { rewrite HmemLen''. exact Hmempat. }
    have Hmemlps'' : N.le (Z.to_N (lpsPtr + Z.of_nat (length p) * 4) + 4) (operations.mem_length m'').
    { rewrite HmemLen''. exact Hmemlps. }
    have HrIH := IH hs s'' inst patPtr patLenN lpsPtr tmpN'' memaddr m'' p (table ++ [v]) (S i) v f0
      Hpp Hlp HpatLen Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm'' Hmempat'' Hmemlps'' Hpmm'' Hnoalias
      Hik' Htlen' Htcb' Hlmm'' (fun _ => Hcorrect) Hv_small Htp_small''.
    move: HrIH => [s' [m' [table' [Htlen'' [Htcb'' [Hlkm' [Hlmm' Hred']]]]]]].
    exists s', m', table'.
    split; [exact Htlen'' |]. split; [exact Htcb'' |]. split; [exact Hlkm' |]. split; [exact Hlmm' |].
    exact: (reduce_trans_trans _ _ _ Hred'' Hred').
Qed.

(** Corollary, phrased directly against [KMPSpec.is_failure_table]. *)
Theorem build_lps_run_is_failure_table : forall k hs s inst patPtr patLenN lpsPtr tmpN memaddr m (p : list byte) (table : list nat) (i len : nat) f0,
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
  (patPtr + Z.of_nat (length p) <= lpsPtr \/ lpsPtr + Z.of_nat (length p) * 4 <= patPtr) ->
  Nat.add i k = length p ->
  length table = i ->
  table_correct_below p table i ->
  lps_mem_matches m lpsPtr table i ->
  (Nat.lt i (length p) -> is_lps p i len) ->
  small (Z.of_nat len) ->
  small tmpN ->
  let f := loop_frame inst patPtr patLenN lpsPtr (Z.of_nat len) (Z.of_nat i) tmpN in
  exists s' m' table',
    is_failure_table p table'
    /\ lookup_N s'.(s_mems) memaddr = Some m'
    /\ lps_mem_matches m' lpsPtr table' (length p)
    /\ reduce_trans (hs, s, f0, [:: AI_frame 0 f (loop_entry_cfg f)]) (hs, s', f0, [::]).
Proof.
  move=> k hs s inst patPtr patLenN lpsPtr tmpN memaddr m p table i len f0
    Hpp Hlp HpatLen Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm Hmempat Hmemlps Hpmm Hnoalias
    Hik Htlen Htcb Hlmm Hilps Hlen_small Htp_small f.
  have [s' [m' [table' [Htlen' [Htcb' [Hlkm' [Hlmm' Hred']]]]]]] :=
    build_lps_run k hs s inst patPtr patLenN lpsPtr tmpN memaddr m p table i len f0
      Hpp Hlp HpatLen Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm Hmempat Hmemlps Hpmm Hnoalias
      Hik Htlen Htcb Hlmm Hilps Hlen_small Htp_small.
  exists s', m', table'.
  split.
  { split; [exact Htlen' |].
    move=> j k0 Hnth.
    have Hj_lt : Nat.lt j (length p).
    { have := List.nth_error_Some table' j.
      rewrite Htlen'. move=> [Hn _]. apply Hn. rewrite Hnth. discriminate. }
    exact: (Htcb' j k0 Hj_lt Hnth). }
  split; [exact Hlkm' |]. split; [exact Hlmm' |]. exact Hred'.
Qed.

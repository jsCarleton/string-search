(** The classical mathematics behind the KMP failure-function recurrence,
    entirely independent of WebAssembly: why is it correct, when p[i]
    doesn't extend the current candidate border of length [len], to fall
    back to [table[len-1]] rather than something else? *)
From Wasm Require Import bytes.
From Coq Require Import List Lia Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import KMPSpec.
Import ListNotations.

(** ** Small list lemmas *)

Lemma firstn_cons_S : forall (A : Type) (x : A) l n, firstn (S n) (x :: l) = x :: firstn n l.
Proof. reflexivity. Qed.

Lemma firstn_S_r : forall (l : text) n c,
  nth_error l n = Some c -> firstn (S n) l = firstn n l ++ [c].
Proof.
  induction l as [| x l' IH]; intros n c Hnth.
  - destruct n; simpl in Hnth; discriminate.
  - destruct n as [| n'].
    + simpl in Hnth. inversion Hnth; subst. reflexivity.
    + simpl in Hnth.
      rewrite firstn_cons_S firstn_cons_S.
      rewrite (IH n' c Hnth).
      reflexivity.
Qed.

Lemma app_singleton_inv : forall {A : Type} (l1 l2 : list A) (a b : A),
  length l1 = length l2 -> l1 ++ [a] = l2 ++ [b] -> l1 = l2 /\ a = b.
Proof.
  move=> A l1 l2 a b Hlen Heq.
  have Hf : firstn (length l1) (l1 ++ [a]) = firstn (length l1) (l2 ++ [b])
    by rewrite Heq.
  have Hs : skipn (length l1) (l1 ++ [a]) = skipn (length l1) (l2 ++ [b])
    by rewrite Heq.
  rewrite firstn_app Nat.sub_diag /= app_nil_r firstn_all in Hf.
  rewrite Hlen firstn_app Nat.sub_diag /= app_nil_r firstn_all in Hf.
  rewrite skipn_app Nat.sub_diag /= in Hs.
  rewrite Hlen skipn_app Nat.sub_diag /= in Hs.
  rewrite Hf skipn_all in Hs.
  simpl in Hs.
  split; [exact Hf | congruence].
Qed.

(** ** The border chain lemma *)

Lemma border_suffix_eq : forall (p : text) (n b k : nat),
  is_border p n b -> k <= b ->
  skipn (n - k) (firstn n p) = skipn (b - k) (firstn b p).
Proof.
  move=> p n b k [[Hbn Hnl] Heq] Hk.
  rewrite Heq skipn_skipn.
  f_equal. lia.
Qed.

Lemma border_chain : forall (p : text) (n b k : nat),
  is_border p n b -> k <= b ->
  is_border p b k <-> is_border p n k.
Proof.
  move=> p n b k Hb Hk.
  have Heq := border_suffix_eq p n b k Hb Hk.
  destruct Hb as [[Hbn Hbl] _].
  rewrite /is_border. split.
  - move=> [[Hkb _] Hfk]. split; [lia | rewrite Hfk Heq //].
  - move=> [[Hkn _] Hfk]. split; [lia | rewrite Hfk -Heq //].
Qed.

(** ** Extending / shrinking a border by one character *)

Lemma border_extend : forall (p : text) (i len : nat) (c : byte),
  is_border p i len ->
  nth_error p len = Some c ->
  nth_error p i = Some c ->
  is_border p (S i) (S len).
Proof.
  move=> p i len c [[Hlen Hil] Heq] Hlc Hic.
  have Hi_lt : i < length p by apply /nth_error_Some; rewrite Hic.
  split; [lia |].
  rewrite (firstn_S_r p i c Hic) (firstn_S_r p len c Hlc).
  rewrite skipn_app.
  have -> : (i - len) - length (firstn i p) = 0 by rewrite length_firstn; lia.
  simpl.
  rewrite Heq.
  reflexivity.
Qed.

Lemma border_shrink : forall (p : text) (i b : nat),
  is_border p (S i) (S b) ->
  is_border p i b /\ nth_error p b = nth_error p i.
Proof.
  move=> p i b [[Hbi Hil] Heq].
  have Hi_lt : i < length p by lia.
  have Hb_lt : b < length p by lia.
  destruct (nth_error p i) as [ci|] eqn:Hic; last first.
  { exfalso. apply nth_error_None in Hic. lia. }
  destruct (nth_error p b) as [cb|] eqn:Hbc; last first.
  { exfalso. apply nth_error_None in Hbc. lia. }
  rewrite (firstn_S_r p i ci Hic) (firstn_S_r p b cb Hbc) in Heq.
  have Hlen_eq : length (firstn b p) = length (skipn (S i - S b) (firstn i p)).
  { rewrite length_firstn length_skipn length_firstn. lia. }
  rewrite skipn_app in Heq.
  have Hib : S i - S b - length (firstn i p) = 0 by rewrite length_firstn; lia.
  rewrite Hib /= in Heq.
  have [Hfeq Hceq] := app_singleton_inv _ _ _ _ Hlen_eq Heq.
  split.
  - split; [lia | exact Hfeq].
  - congruence.
Qed.

(** ** The reference recurrence *)

Fixpoint cand_fuel (p : text) (table : list nat) (i : nat) (fuel len : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match nth_error p len, nth_error p i with
    | Some cl, Some ci =>
      if byte_eq_dec cl ci then S len
      else match len with
           | 0 => 0
           | S len' => cand_fuel p table i fuel' (nth_default 0 table len')
           end
    | _, _ => 0
    end
  end.

Definition cand (p : text) (table : list nat) (i len : nat) : nat :=
  cand_fuel p table i (length p) len.

Definition table_correct_below (p : text) (table : list nat) (i : nat) : Prop :=
  forall j k, j < i -> nth_error table j = Some k -> is_lps p (S j) k.

(** [b < i] restricts this to *proper* borders (matching [is_lps]'s own
    [k < n]): without it, the trivial "whole prefix" border [b = i] is
    always a live counterexample ([is_border p i i] holds unconditionally,
    making [nth_error p i <> nth_error p i] impossible), so the predicate
    could never actually be established by a caller -- only ever
    consumed, never produced. Every use site below already has [b < i]
    on hand, so this only weakens (eases) what needs proving. *)
Definition ruled_out_above (p : text) (i len : nat) : Prop :=
  forall b, is_border p i b -> len < b -> b < i -> nth_error p b <> nth_error p i.

Lemma cand_correct_fuel : forall (p : text) (table : list nat) (i : nat),
  i < length p ->
  i <= length table ->
  table_correct_below p table i ->
  forall fuel len, len < fuel -> len < i ->
    is_border p i len ->
    ruled_out_above p i len ->
    is_lps p (S i) (cand_fuel p table i fuel len).
Proof.
  move=> p table i Hi Hpop Htc.
  elim=> [| fuel' IH] len Hfuel Hlt Hborder Hruled.
  - lia.
  - rewrite /=.
    destruct (nth_error p i) as [ci|] eqn:Hic; last first.
    { exfalso. apply nth_error_None in Hic. lia. }
    have Hlen_lt : len < length p by lia.
    destruct (nth_error p len) as [cl|] eqn:Hcl; last first.
    { exfalso. apply nth_error_None in Hcl. lia. }
    case: (byte_eq_dec cl ci) => Hcmp.
    + (* match: extend *)
      subst cl.
      have Hext := border_extend p i len ci Hborder Hcl Hic.
      simpl.
      rewrite /is_lps. split; [exact Hext | split; [lia |]].
      move=> k' Hb' Hk'lt.
      case: k' Hb' Hk'lt => [| b'] Hb' Hk'lt; [lia |].
      have [Hbord Hmatch] := border_shrink p i b' Hb'.
      case: (Nat.le_gt_cases b' len) => Hcase; [lia |].
      have Hne := Hruled b' Hbord Hcase (ltac:(lia)).
      exfalso. exact: (Hne Hmatch).
    + (* mismatch *)
      simpl.
      case: len Hfuel Hlt Hborder Hruled Hlen_lt Hcl => [| len'] Hfuel Hlt Hborder Hruled Hlen_lt Hcl.
      * (* len = 0: give up, answer is 0. We already compared p[0] to
           p[i] above (that comparison is what put us in this mismatch
           branch), so unlike an untested candidate, b'=0 is directly
           ruled out by Hcl/Hic/Hcmp; b'>0 is ruled out by Hruled. *)
        simpl.
        rewrite /is_lps. split; [apply: is_border_zero; lia | split; [lia |]].
        move=> k' Hb' Hk'lt.
        case: k' Hb' Hk'lt => [| b'] Hb' Hk'lt; [lia |].
        have [Hbord Hmatch] := border_shrink p i b' Hb'.
        case: (Nat.eq_dec b' 0) => Hb'0.
        - exfalso. subst b'. congruence.
        - have Hne := Hruled b' Hbord (ltac:(lia)) (ltac:(lia)).
          exfalso. exact: (Hne Hmatch).
      * (* len = S len': backtrack to table[len'] *)
        simpl.
        have Hlen'_i : len' < i by lia.
        have Hlen'_tab : len' < length table by lia.
        have [v Htv] : exists v, nth_error table len' = Some v.
        { destruct (nth_error table len') as [v|] eqn:E; [by exists v |].
          exfalso. apply nth_error_None in E. lia. }
        have Hvdef : nth_default 0 table len' = v by rewrite /nth_default Htv.
        have Htcb : is_lps p (S len') v := Htc len' v Hlen'_i Htv.
        have Hborder_Slen' : is_border p (S len') v := proj1 Htcb.
        have Hv_lt : v < S len' by have [_ [? _]] := Htcb; lia.
        have Hv_le : v <= S len' by lia.
        have Hborder_new : is_border p i v.
        { have Hbc := border_chain p i (S len') v Hborder Hv_le.
          apply Hbc. exact Hborder_Slen'. }
        have Hruled_new : ruled_out_above p i v.
        { move=> b Hb_border Hvb Hbi.
          case: (Nat.le_gt_cases (S len') b) => Hcase.
          - case: (Nat.eq_dec b (S len')) => Heqb.
            + subst b. rewrite Hcl Hic. congruence.
            + apply: Hruled; [exact Hb_border | lia | exact Hbi].
          - exfalso.
            have Hb_le : b <= S len' by lia.
            have Hbc2 := border_chain p i (S len') b Hborder Hb_le.
            have Hborder_b : is_border p (S len') b.
            { apply Hbc2. exact Hb_border. }
            have Hb_proper : b < S len' by lia.
            have [_ [_ Hmax]] := Htcb.
            have := Hmax b Hborder_b Hb_proper.
            lia. }
        have Hv_fuel : v < fuel' by lia.
        have Hv_i : v < i by lia.
        rewrite Hvdef.
        exact: (IH v Hv_fuel Hv_i Hborder_new Hruled_new).
Qed.

Theorem cand_correct : forall (p : text) (table : list nat) (i : nat),
  i < length p ->
  i <= length table ->
  table_correct_below p table i ->
  forall len, len < i ->
    is_border p i len ->
    ruled_out_above p i len ->
    is_lps p (S i) (cand p table i len).
Proof.
  move=> p table i Hi Hpop Htc len Hlt Hborder Hruled.
  apply: (cand_correct_fuel p table i Hi Hpop Htc (length p) len).
  - lia.
  - exact Hlt.
  - exact Hborder.
  - exact Hruled.
Qed.

(** The bridge the outer per-position induction needs: [is_lps]'s own
    maximality clause is exactly enough to derive [ruled_out_above] for
    the *same* [i]/[len] -- for [b < i] with [len < b], [is_border p i
    b] together with maximality forces [b <= len], contradicting
    [len < b], so the conclusion follows vacuously. (Without the [b < i]
    restriction on [ruled_out_above] this would be false: the
    unrestricted version can never be proved, only assumed -- see that
    definition's comment.) *)
Lemma ruled_out_above_of_is_lps : forall p i len, is_lps p i len -> ruled_out_above p i len.
Proof.
  move=> p i len [Hborder [Hlt Hmax]] b Hb_border Hlb Hbi.
  exfalso.
  have Hble := Hmax b Hb_border Hbi.
  lia.
Qed.

(** Base case: at [i = 0], [table[0] = 0] unconditionally (no previous
    entries to consult), matching what the wasm code hard-codes. *)
Theorem lps_zero_correct : forall (p : text), 0 < length p -> is_lps p 1 0.
Proof.
  move=> p Hp.
  rewrite /is_lps. split; [apply: is_border_zero; lia | split; [lia |]].
  move=> k' Hb' Hk'lt. lia.
Qed.

(** The pure-math core of [kmp_search]'s correctness, independent of
    WebAssembly entirely -- the [kmp_search] analogue of
    [KMPFailureRec.v]. States and proves the classical KMP search
    invariant: at every point in the scan, [j] is the length of the
    longest prefix of [pat] that is currently a suffix of the scanned
    text, and no occurrence of [pat] has been missed. Built directly on
    [KMPFailureRec.v]'s border-chain lemmas ([border_suffix_eq] proves
    exactly the "borders compose" fact this file needs to justify the
    backtracking step, [Wc]/j' := lps[j-1]). *)
From Wasm Require Import bytes.
From Coq Require Import List Lia Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import KMPSpec KMPFailureRec.
Import ListNotations.

(** ** The match invariant: [pat[0..j)] is a suffix of [txt[0..i)] *)

Definition search_matches (txt pat : text) (i j : nat) : Prop :=
  j <= length pat /\ j <= i /\
  firstn j pat = skipn (i - j) (firstn i txt).

(** Backtracking preserves [search_matches]: if [pat[0..j)] matches
    [txt]'s suffix ending at [i], and [j'] is a border of [pat[0..j)]
    (in particular, [j' = lps[j-1]]), then [pat[0..j')] matches too --
    a border is a suffix of [pat[0..j)], hence (composing with
    [search_matches]'s own suffix relation) a suffix of [txt]'s
    [i]-ending window as well. *)
Lemma search_matches_backtrack : forall txt pat i j j',
  search_matches txt pat i j ->
  is_border pat j j' ->
  search_matches txt pat i j'.
Proof.
  move=> txt pat i j j' [Hjlen [Hji Heq]] Hb.
  have Hb' := Hb.
  destruct Hb' as [[Hj'j Hj'len] Heqb].
  split; [lia |]. split; [lia |].
  rewrite Heqb Heq skipn_skipn.
  f_equal. lia.
Qed.

(** The empty match ([j = 0]) is always the *shortest* possible border
    target, so [search_matches] holds trivially: [firstn 0 pat = []],
    and [skipn i (firstn i txt) = []] too. *)
Lemma search_matches_zero : forall txt pat i, i <= length txt -> search_matches txt pat i 0.
Proof.
  move=> txt pat i Hi.
  split; [lia |]. split; [lia |].
  rewrite /= Nat.sub_0_r.
  rewrite skipn_all2; [reflexivity | rewrite length_firstn; lia].
Qed.

(** Extending the match by one character (the "match, continue" and
    "match, return" transitions): if [txt[i] = pat[j]], the match grows
    by exactly one. *)
Lemma search_matches_extend : forall txt pat i j c,
  search_matches txt pat i j ->
  nth_error txt i = Some c ->
  nth_error pat j = Some c ->
  search_matches txt pat (S i) (S j).
Proof.
  move=> txt pat i j c [Hjlen [Hji Heq]] Hti Hpj.
  have Hi_lt : i < length txt by apply /nth_error_Some; rewrite Hti.
  have Hj_lt : j < length pat by apply /nth_error_Some; rewrite Hpj.
  split; [lia |]. split; [lia |].
  rewrite (firstn_S_r pat j c Hpj) (firstn_S_r txt i c Hti).
  rewrite skipn_app.
  have -> : (S i - S j) - length (firstn i txt) = 0 by rewrite length_firstn; lia.
  simpl.
  rewrite Heq.
  reflexivity.
Qed.

(** For [k <= j], having a [k]-length match at [i] (given the
    [j]-length match already established) is *equivalent* to [k] being
    a border of [pat]'s own [j]-prefix -- once the longer [j]-match
    pins the text window down to exactly [pat[0..j)], any shorter valid
    match at the same [i] is purely a question about [pat]'s own
    internal structure, not about [txt] at all. This is what lets
    [is_lps]'s maximality (a fact about [pat] alone) control which [k]
    can possibly work at [i]. *)
Lemma search_matches_le_iff_border : forall txt pat i j k,
  search_matches txt pat i j -> k <= j ->
  (search_matches txt pat i k <-> is_border pat j k).
Proof.
  move=> txt pat i j k [Hjlen [Hji Heqj]] Hkj.
  split.
  - move=> [Hklen [Hki Heqk]].
    split; [split; [exact Hkj | lia] |].
    rewrite Heqj skipn_skipn.
    have -> : (j - k) + (i - j) = i - k by lia.
    exact Heqk.
  - move=> [[Hkj' Hjlen'] Heqb].
    split; [lia |]. split; [lia |].
    rewrite Heqb Heqj skipn_skipn.
    f_equal. lia.
Qed.

(** The [d]-th character of an occurrence at [i''] (for [d] within
    [pat]'s length) is exactly [pat]'s [d]-th character -- the
    element-wise unpacking of [occurs_at]'s whole-window equality,
    needed to extract single-character contradictions from a
    hypothesised occurrence. *)
Lemma occurs_at_char : forall txt pat i d c,
  occurs_at txt pat i -> nth_error pat d = Some c ->
  nth_error txt (i + d) = Some c.
Proof.
  move=> txt pat i d c [Hbound Heq] Hd.
  have Hd_lt : d < length pat by apply /nth_error_Some; rewrite Hd.
  have := f_equal (fun l => nth_error l d) Heq.
  rewrite (nth_error_firstn (length pat) (skipn i txt) d).
  have -> : (d <? length pat) = true by apply /Nat.ltb_lt.
  rewrite nth_error_skipn.
  rewrite Hd.
  by [].
Qed.

(** ** No occurrence has been missed *)

(** No occurrence of [pat] starts anywhere before [bound]. *)
Definition search_no_occ_before (txt pat : text) (bound : nat) : Prop :=
  forall i', i' < bound -> ~ occurs_at txt pat i'.

(** Extending the match ([i -> S i], [j -> S j]) doesn't change the
    ruled-out range at all: [(S i) - (S j) = i - j]. *)
Lemma search_no_occ_extend : forall txt pat i j,
  search_no_occ_before txt pat (i - j) -> search_no_occ_before txt pat (S i - S j).
Proof. move=> txt pat i j H. by have -> : S i - S j = i - j by lia. Qed.

(** Give-up ([i -> S i], [j] stays [0]): the ruled-out range grows by
    exactly one position, [i] itself, which the mismatch
    [text[i] <> pat[0]] rules out directly ([occurs_at] at [i] would
    need [text[i] = pat[0]], the very first character). *)
Lemma search_no_occ_giveup : forall txt pat i c1 c2,
  search_no_occ_before txt pat (i - 0) ->
  nth_error txt i = Some c1 -> nth_error pat 0 = Some c2 -> c1 <> c2 ->
  search_no_occ_before txt pat (S i - 0).
Proof.
  move=> txt pat i c1 c2 Hno Hti Hp0 Hne i' Hi' Hocc.
  have Hi'' : i' < S i by lia.
  case: (Nat.eq_dec i' i) => Heq.
  - subst i'.
    have Hchar := occurs_at_char txt pat i 0 c2 Hocc Hp0.
    rewrite Nat.add_0_r Hti in Hchar. inversion Hchar; subst.
    exact: Hne erefl.
  - apply: (Hno i' (ltac:(lia)) Hocc).
Qed.

(** The [m]-th character of [pat]'s [j]-prefix, for [m < j], read off
    directly from [txt] via [search_matches]'s suffix equation. *)
Lemma search_matches_char : forall txt pat i j m,
  search_matches txt pat i j -> m < j ->
  nth_error pat m = nth_error txt (i - j + m).
Proof.
  move=> txt pat i j m [Hjlen [Hji Heq]] Hm.
  have := f_equal (fun l => nth_error l m) Heq.
  rewrite (nth_error_firstn j pat m).
  have -> : (m <? j) = true by apply /Nat.ltb_lt.
  rewrite (nth_error_skipn (i - j) (firstn i txt) m).
  rewrite (nth_error_firstn i txt (i - j + m)).
  have -> : (i - j + m <? i) = true by apply /Nat.ltb_lt; lia.
  by [].
Qed.

(** Backtracking ([i] unchanged, [j -> j' = lps[j-1]]): the ruled-out
    range grows from [i - j] to [i - j']. Every newly-covered position
    [i'] (with [i - j <= i' < i - j']) is ruled out: writing
    [d := i' - (i - j)] (so [0 <= d < j - j']), an occurrence at [i']
    would make [j - d] a border of [pat]'s [j]-prefix (comparing
    [pat]'s own characters, read off two ways -- via the occurrence and
    via the established [j]-match -- both ultimately pointing at the
    same [txt] characters) that is either [j] itself (when [d = 0],
    directly contradicting the mismatch [text[i] <> pat[j]] that
    triggered the backtrack) or strictly between [j'] and [j] (when
    [d > 0], contradicting [is_lps]'s maximality -- [j'] is supposed to
    be the *longest* proper border). *)
Lemma search_no_occ_backtrack : forall txt pat i j j' c1 c2,
  search_matches txt pat i j ->
  search_no_occ_before txt pat (i - j) ->
  is_lps pat j j' ->
  nth_error txt i = Some c1 -> nth_error pat j = Some c2 -> c1 <> c2 ->
  search_no_occ_before txt pat (i - j').
Proof.
  move=> txt pat i j j' c1 c2 Hm Hno [Hborder [Hj'j Hlpsmax]] Hti Hpj Hne i' Hi' Hocc.
  have [Hjlen [Hji Heqj]] := Hm.
  case: (Nat.le_gt_cases (i - j) i') => Hcase; last first.
  { exact: (Hno i' Hcase Hocc). }
  set d := i' - (i - j).
  have Hd_hi : d < j - j' by rewrite /d; lia.
  have Hi'_eq : i' = (i - j) + d by rewrite /d; lia.
  have Hpat_eq : forall k, k < j - d -> nth_error pat k = nth_error pat (d + k).
  { move=> k Hk.
    have Hk_len : k < length pat by lia.
    destruct (nth_error pat k) as [pk|] eqn:Hpk; last first.
    { exfalso. apply nth_error_None in Hpk. lia. }
    have Hlhs : nth_error pat k = nth_error txt (i - j + k) := search_matches_char txt pat i j k Hm (ltac:(lia)).
    have Hrhs : nth_error pat (d + k) = nth_error txt (i - j + (d + k)) := search_matches_char txt pat i j (d+k) Hm (ltac:(lia)).
    have Hocc_char : nth_error txt (i' + k) = nth_error pat k.
    { rewrite Hpk. exact: (occurs_at_char txt pat i' k pk Hocc Hpk). }
    clear Hlhs.
    rewrite Hrhs.
    have -> : i - j + (d + k) = i' + k by lia.
    by rewrite Hocc_char. }
  have Hjd_border : is_border pat j (j - d).
  { split; [split; lia |].
    apply: nth_error_ext => m.
    have -> : j - (j - d) = d by lia.
    rewrite (nth_error_firstn (j-d) pat m) (nth_error_skipn d (firstn j pat) m)
      (nth_error_firstn j pat (d+m)).
    case: (Nat.ltb_spec m (j-d)) => Hm1.
    - have -> : (d + m <? j) = true by apply /Nat.ltb_lt; lia.
      exact: (Hpat_eq m Hm1).
    - have -> : (d + m <? j) = false by apply /Nat.ltb_ge; lia.
      reflexivity. }
  case: (Nat.eq_dec d 0) => Hd0.
  - exfalso. apply Hne.
    have Hchar := occurs_at_char txt pat i' j c2 Hocc Hpj.
    have Heqi : i' + j = i by lia.
    rewrite Heqi Hti in Hchar.
    congruence.
  - have Hjd_lt : j - d < j by lia.
    have Hjd_gt : j' < j - d by lia.
    have := Hlpsmax (j - d) Hjd_border Hjd_lt.
    lia.
Qed.

(** ** Connecting the invariants to [KMPSpec]'s correctness predicates *)

(** Firing the [return] (extending the match to [pat]'s full length)
    lands exactly on a genuine occurrence, at [(S i) - (S j)]: once
    [S j = length pat], [search_matches]'s own equation *is*
    [occurs_at]'s defining equation, just needing [skipn]/[firstn] to
    commute ([skipn_firstn_comm]) to match shapes. *)
Lemma search_matches_occurs_at_return : forall txt pat i j,
  search_matches txt pat (S i) (S j) -> S i <= length txt -> S j = length pat ->
  occurs_at txt pat (S i - S j).
Proof.
  move=> txt pat i j [Hjlen [Hji Heq]] Hib Hjeq.
  split; [lia |].
  rewrite skipn_firstn_comm in Heq.
  have Heq' : S i - (S i - S j) = S j by lia.
  rewrite Heq' Hjeq in Heq.
  rewrite Hjeq -Heq.
  exact: firstn_all.
Qed.

(** The final "found it" theorem: with the match and no-missed-
    occurrence invariants both in hand at the point the whole pattern
    is matched, [(S i) - (S j)] is exactly [pat]'s first occurrence. *)
Theorem search_matches_is_first_occurrence : forall txt pat i j,
  search_matches txt pat (S i) (S j) -> S i <= length txt -> S j = length pat ->
  search_no_occ_before txt pat (i - j) ->
  is_first_occurrence txt pat (S i - S j).
Proof.
  move=> txt pat i j Hm Hib Hjeq Hno.
  split; [exact: (search_matches_occurs_at_return txt pat i j Hm Hib Hjeq) |].
  move=> j0 Hj0.
  apply: (Hno j0 (ltac:(lia))).
Qed.

(** The final "not found" theorem: if the scan reaches the end of
    [txt] ([i = length txt]) with the running match strictly shorter
    than [pat] (guaranteed by construction -- reaching [j = length pat]
    fires a [return] immediately, so the scan never re-checks the exit
    condition in that state), the no-missed-occurrence invariant alone
    already covers *every* candidate position: any [i'] with
    [occurs_at txt pat i'] satisfies [i' + length pat <= length txt],
    hence [i' <= length txt - length pat < length txt - j]. *)
Theorem search_no_occ_before_does_not_occur : forall txt pat i j,
  i = length txt -> j < length pat ->
  search_no_occ_before txt pat (i - j) ->
  does_not_occur txt pat.
Proof.
  move=> txt pat i j Hi Hjlt Hno i' Hocc.
  have [Hbound _] := Hocc.
  apply: (Hno i' (ltac:(lia)) Hocc).
Qed.

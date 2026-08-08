(** The mathematical specification that kmp.wasm is proved correct against.
    Deliberately independent of the KMP algorithm itself (no failure-
    function recurrence, no loop) -- this is "what correct means", stated
    the way a reader would define it without having seen the algorithm.
    Later files prove the actual wasm code satisfies this spec. *)
From Wasm Require Import bytes.
From Coq Require Import List Lia Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrfun ssrbool.
Import ListNotations.

Definition text := list byte.

(** ** Substring occurrence (spec for kmp_search) *)

(** [pat] occurs in [txt] starting at index [i]: the length-[length pat]
    window of [txt] beginning at [i] equals [pat] exactly. *)
Definition occurs_at (txt pat : text) (i : nat) : Prop :=
  i + length pat <= length txt /\
  firstn (length pat) (skipn i txt) = pat.

(** [i] is the *first* occurrence of [pat] in [txt]: it occurs at [i], and
    no smaller index is an occurrence. *)
Definition is_first_occurrence (txt pat : text) (i : nat) : Prop :=
  occurs_at txt pat i /\ forall j, j < i -> ~ occurs_at txt pat j.

(** The empty pattern trivially occurs everywhere; by the usual convention
    (matching e.g. Python/JS/C's [find]/[strstr]) its first occurrence is
    index 0. kmp.wasm special-cases this and returns 0 directly. *)
Lemma occurs_at_empty : forall txt, occurs_at txt [] 0.
Proof. move=> txt. rewrite /occurs_at /=. split; [lia | reflexivity]. Qed.

Lemma is_first_occurrence_empty : forall txt, is_first_occurrence txt [] 0.
Proof.
  move=> txt. split; [exact: occurs_at_empty | lia].
Qed.

(** No occurrence exists anywhere in the text. *)
Definition does_not_occur (txt pat : text) : Prop :=
  forall j, ~ occurs_at txt pat j.

(** ** Borders and the KMP failure ("lps") function (spec for build_lps) *)

(** [k] is a border of the length-[n] prefix of [p]: a proper (if [k<n])
    prefix of that length that is also its suffix. *)
Definition is_border (p : text) (n k : nat) : Prop :=
  k <= n <= length p /\
  firstn k p = skipn (n - k) (firstn n p).

(** The empty border (length 0) is always valid, for any nonempty prefix:
    [firstn 0 p = []] and [skipn n (firstn n p) = []]. *)
Lemma is_border_zero : forall p n, n <= length p -> is_border p n 0.
Proof.
  move=> p n Hn. rewrite /is_border. split; [lia|].
  rewrite /= Nat.sub_0_r.
  rewrite skipn_all2; [reflexivity | rewrite length_firstn; lia].
Qed.

(** [k] is *the* KMP failure value at prefix length [n] (i.e. [lps[n-1]]
    in the usual 0-indexed array, here stated directly against prefix
    length for clarity): [k] is a proper border ([k < n]) and no proper
    border is longer. Since [0] is always a proper border of any
    prefix of length [n >= 1], this predicate is satisfiable, and it
    pins down a unique [k] (the maximum), so it fully specifies the
    failure function. *)
Definition is_lps (p : text) (n k : nat) : Prop :=
  is_border p n k /\ k < n /\
  (forall k', is_border p n k' -> k' < n -> k' <= k).

Lemma is_lps_unique : forall p n k1 k2,
  is_lps p n k1 -> is_lps p n k2 -> k1 = k2.
Proof.
  move=> p n k1 k2 [Hb1 [Hlt1 Hmax1]] [Hb2 [Hlt2 Hmax2]].
  have H12 := Hmax1 k2 Hb2 Hlt2.
  have H21 := Hmax2 k1 Hb1 Hlt1.
  lia.
Qed.

(** The full failure table for pattern [p]: [table] has one entry per
    position of [p], and entry [i] is the KMP failure value at prefix
    length [i+1] (i.e. the standard [lps[i]]). *)
Definition is_failure_table (p : text) (table : list nat) : Prop :=
  length table = length p /\
  forall i k, nth_error table i = Some k -> is_lps p (S i) k.

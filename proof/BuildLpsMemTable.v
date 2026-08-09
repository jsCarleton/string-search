(** The bridge between [build_lps]'s WebAssembly-level memory (the
    [lps] output array, four bytes per entry) and [KMPFailureRec.v]'s
    purely mathematical [table : list nat]: [lps_mem_matches] says the
    two agree on the first [n] entries, and is what the per-iteration
    theorems in [BuildLpsIterate.v] need to hand to
    [KMPFailureRec.v]'s [table_correct_below]/[cand]. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith Arith.PeanoNat.
Require Import MemLemmas Int32Facts.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** Non-interference for [read_bytes] (not just single-byte
    [mem_lookup]) under a disjoint [write_bytes] -- the four-byte-range
    analogue of [MemLemmas.v]'s [write_bytes_out], needed because each
    [lps] table entry occupies 4 bytes, not 1. *)
(** Stated via [Nat.le]/[Nat.lt]/[Nat.add] explicitly, not the bare
    [<=]/[<]/[+] notations: under [ssrnat] those notations resolve to
    the boolean [leq]/[ltn]/[addn], which [lia] does not understand,
    even inside a [%coq_nat]-scoped expression (the delimiter does not
    reliably override [+] here). *)
Lemma In_iota0 : forall n m off, List.In off (iota m n) -> Nat.le m off /\ Nat.lt off (Nat.add m n).
Proof.
  induction n as [| n' IH]; intros m off Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst off. split; lia.
    + specialize (IH (S m) off Hin). destruct IH as [IH1 IH2]. split; lia.
Qed.

Lemma read_bytes_write_bytes_disjoint : forall (m m' : meminst) bs (addr addr2 : N) (len2 : nat),
  write_bytes (meminst_data m) addr bs = Some (meminst_data m') ->
  (addr2 + N.of_nat len2 <= addr \/ addr + N.of_nat (length bs) <= addr2)%N ->
  read_bytes m' addr2 len2 = read_bytes m addr2 len2.
Proof.
  move=> m m' bs addr addr2 len2 Hwr Hdisj.
  rewrite /read_bytes.
  have Heq : List.map (fun off => mem_lookup (addr2 + N.of_nat off)%N (meminst_data m')) (iota 0 len2)
           = List.map (fun off => mem_lookup (addr2 + N.of_nat off)%N (meminst_data m)) (iota 0 len2).
  { apply: List.map_ext_in => off Hin.
    have [_ Hlt] := In_iota0 len2 0 off Hin.
    apply: (write_bytes_out bs (meminst_data m) addr (meminst_data m') (addr2 + N.of_nat off)%N Hwr).
    lia. }
  rewrite Heq. reflexivity.
Qed.

(** [m]'s [lps] array (base pointer [lpsPtr]) agrees with the
    mathematical [table] on all entries below [n]: entry [j] is stored,
    little-endian, as the four bytes at [lpsPtr + 4*j]. Bounds are
    stated via [Nat.lt]/[Nat.le] explicitly rather than bare [<]/[<=]
    -- see [In_iota0]'s comment above for why. *)
Definition lps_mem_matches (m : meminst) (lpsPtr : Z) (table : list nat) (n : nat) : Prop :=
  forall j v, Nat.lt j n -> nth_error table j = Some v ->
    read_bytes m (Z.to_N (lpsPtr + Z.of_nat j * 4)) 4 = Some (serialise_num (VAL_int32 (enc (Z.of_nat v)))).

(** Shrinking [n] (the usual monotonicity of a "matches up to" predicate). *)
Lemma lps_mem_matches_le : forall m lpsPtr table n n',
  lps_mem_matches m lpsPtr table n -> Nat.le n' n -> lps_mem_matches m lpsPtr table n'.
Proof.
  move=> m lpsPtr table n n' Hm Hle j v Hj Hnth.
  apply: Hm; [lia | exact Hnth].
Qed.

(** Extending the invariant by one entry: after storing [enc v] at the
    new slot [lpsPtr + 4*n] (as [build_lps]'s match/give-up branches
    do), and appending [v] to [table] at position [n], the invariant
    now covers [n+1]. The disjointness side condition
    ([small (lpsPtr + Z.of_nat n * 4)], keeping every earlier slot's
    address comfortably in range) is what lets
    [read_bytes_write_bytes_disjoint] show earlier entries are
    untouched by the new write. *)
Lemma lps_mem_matches_extend : forall m lpsPtr table n v m',
  lps_mem_matches m lpsPtr table n ->
  nth_error table n = Some v ->
  small (lpsPtr + Z.of_nat n * 4) ->
  (forall j, Nat.lt j n -> small (lpsPtr + Z.of_nat j * 4)) ->
  write_bytes (meminst_data m) (Z.to_N (lpsPtr + Z.of_nat n * 4)) (serialise_num (VAL_int32 (enc (Z.of_nat v))))
    = Some (meminst_data m') ->
  lps_mem_matches m' lpsPtr table (S n).
Proof.
  move=> m lpsPtr table n v m' Hm Hnth Hsmall Hsmall_below Hwr j v' Hj Hnth'.
  have Hlen4 : length (serialise_num (VAL_int32 (enc (Z.of_nat v)))) = 4%nat.
  { rewrite /serialise_num /serialise_i32. apply: Memdata.encode_int_length. }
  case: (Nat.eq_dec j n) => Hjn.
  - subst j. rewrite Hnth' in Hnth. inversion Hnth; subst v'.
    have Hrb := read_bytes_after_write (serialise_num (VAL_int32 (enc (Z.of_nat v)))) m'.(meminst_type)
      (meminst_data m) (Z.to_N (lpsPtr + Z.of_nat n * 4)) (meminst_data m') Hwr.
    rewrite Hlen4 in Hrb.
    have -> : m' = Build_meminst m'.(meminst_type) m'.(meminst_data) by destruct m'.
    exact Hrb.
  - have Hjlt : Nat.lt j n by lia.
    have Hj_small := Hsmall_below j Hjlt.
    have H1 : 0 <= lpsPtr + Z.of_nat j * 4 by move: Hj_small; rewrite /small; lia.
    have H2 : 0 <= lpsPtr + Z.of_nat n * 4 by move: Hsmall; rewrite /small; lia.
    have H3 : lpsPtr + Z.of_nat j * 4 + 4 <= lpsPtr + Z.of_nat n * 4 by lia.
    have Hdisj : (Z.to_N (lpsPtr + Z.of_nat j * 4) + N.of_nat 4 <= Z.to_N (lpsPtr + Z.of_nat n * 4)
               \/ Z.to_N (lpsPtr + Z.of_nat n * 4) + N.of_nat (length (serialise_num (VAL_int32 (enc (Z.of_nat v)))))
                    <= Z.to_N (lpsPtr + Z.of_nat j * 4))%N.
    { left. lia. }
    have Heq := read_bytes_write_bytes_disjoint m m'
      (serialise_num (VAL_int32 (enc (Z.of_nat v)))) (Z.to_N (lpsPtr + Z.of_nat n * 4))
      (Z.to_N (lpsPtr + Z.of_nat j * 4)) 4 Hwr Hdisj.
    rewrite Heq.
    apply: Hm; [exact Hjlt | exact Hnth'].
Qed.

(** [m] holds the pattern [p] as raw bytes at [patPtr], one byte per
    entry. Unlike [lps_mem_matches], this never changes across
    [build_lps]'s loop (the pattern is read-only), so there is no
    corresponding "extend" lemma -- it is established once, by the
    caller, from the initial memory layout. *)
Definition pat_mem_matches (m : meminst) (patPtr : Z) (p : list byte) : Prop :=
  forall j c, nth_error p j = Some c ->
    mem_lookup (Z.to_N (patPtr + Z.of_nat j)) m.(meminst_data) = Some c.

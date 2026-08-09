(** Byte- and i32-level memory reasoning for kmp.wasm's proof: what
    [i32.load8_u] and [i32.store]/[i32.load] actually do to the abstract
    [Memory] typeclass's [mem_lookup]/[mem_update], built from first
    principles (WasmCert-Coq has no ready-made lemmas at this level). Two
    kinds of fact live here:
    - single-byte load/write, built directly from the [Memory] typeclass
      axioms (mem_lookup_ib/oob, mem_update_lookup(_ne), mem_update_ib);
    - i32 store/load round-trip, via CompCert's byte-level
      [encode_int]/[decode_int] (used by [serialise_num]/
      [wasm_deserialise]) composed with [Wasm_int.Int32]'s own
      [repr]/[unsigned] round-trip fact -- note [Wasm_int.Int32.int] and
      CompCert's own [Integers.Int.int] are distinct (if isomorphic)
      types from separate functor instantiations, so CompCert's
      Int-specific round-trip lemmas don't apply directly; the general,
      type-agnostic [Memdata.decode_encode_int] does. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
From compcert Require Memdata Integers.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.

(** ** Single-byte read ([i32.load8_u]) *)

Lemma read_bytes_one : forall m addr b,
  mem_lookup addr m.(meminst_data) = Some b ->
  read_bytes m addr 1 = Some [b].
Proof.
  move=> m addr b Hlk.
  rewrite /read_bytes /=.
  rewrite N.add_0_r Hlk /=.
  reflexivity.
Qed.

Lemma load8_u_ok : forall m addr b,
  mem_lookup addr m.(meminst_data) = Some b ->
  N.lt addr (operations.mem_length m) ->
  load_packed SX_U m addr 0 (tp_length Tp_i8) (tnum_length T_i32) = Some (bytes_takefill #00 4 [b]).
Proof.
  move=> m addr b Hlk Hbound.
  rewrite /load_packed /load /=.
  rewrite N.add_0_r.
  have -> : (addr + 1 <=? operations.mem_length m) = true.
  { apply /N.leb_le. lia. }
  rewrite (read_bytes_one m addr b Hlk) /=.
  reflexivity.
Qed.

(** ** Byte-range write, and non-interference outside it *)

Lemma write_bytes_out : forall bs m addr m' j,
  write_bytes m addr bs = Some m' ->
  (j < addr \/ addr + N.of_nat (length bs) <= j) ->
  mem_lookup j m' = mem_lookup j m.
Proof.
  elim=> [| b bs' IH] m addr m' j /=.
  - move=> [] <- _. reflexivity.
  - destruct (mem_update addr b m) as [m1|] eqn:Hup; last discriminate.
    move=> Hwr Hj.
    simpl in Hj.
    have Hne : j <> addr by lia.
    have Hj1 : j < addr + 1 \/ addr + 1 + N.of_nat (length bs') <= j by lia.
    rewrite (IH m1 (addr+1) m' j Hwr Hj1).
    apply mem_update_lookup_ne with (i := j) (i' := addr) (b := b); [exact Hne | exact Hup].
Qed.

Lemma write_bytes_in : forall bs m addr m' k b,
  write_bytes m addr bs = Some m' ->
  List.nth_error bs k = Some b ->
  mem_lookup (addr + N.of_nat k) m' = Some b.
Proof.
  elim=> [| b0 bs' IH] m addr m' k b /=.
  - move=> _. by case: k.
  - destruct (mem_update addr b0 m) as [m1|] eqn:Hup; last discriminate.
    move=> Hwr.
    case: k => [| k'] /=.
    + move=> [] <-.
      rewrite N.add_0_r.
      have Hout : mem_lookup addr m' = mem_lookup addr m1.
      { apply: (write_bytes_out bs' m1 (addr+1) m' addr Hwr). left. lia. }
      rewrite Hout.
      apply mem_update_lookup with (mem := m) (mem' := m1) (i := addr) (b := b0). exact Hup.
    + move=> Hnth.
      have -> : addr + N.of_nat (S k') = (addr + 1) + N.of_nat k' by lia.
      exact: (IH m1 (addr+1) m' k' b Hwr Hnth).
Qed.


Lemma write_bytes_read_bytes : forall bs m addr m',
  write_bytes m addr bs = Some m' ->
  List.map (fun off => mem_lookup (addr + N.of_nat off) m') (iota 0 (length bs)) = List.map (@Some byte) bs.
Proof.
  elim=> [| b bs' IH] m addr m' /=.
  - reflexivity.
  - destruct (mem_update addr b m) as [m1|] eqn:Hup; last discriminate.
    move=> Hwr.
    rewrite N.add_0_r.
    have Hb : mem_lookup addr m' = Some b.
    { have Hout : mem_lookup addr m' = mem_lookup addr m1.
      { apply: (write_bytes_out bs' m1 (addr+1) m' addr Hwr). left. lia. }
      rewrite Hout.
      apply mem_update_lookup with (mem:=m) (mem':=m1) (i:=addr) (b:=b). exact Hup. }
    rewrite Hb. f_equal.
    have Hiota : iota 1 (length bs') = map (addn 1) (iota 0 (length bs')).
    { have H := iotaDl 1 0 (length bs'). rewrite addn0 in H. exact H. }
    rewrite Hiota List.map_map.
    rewrite -(IH m1 (addr+1) m' Hwr).
    apply: List.map_ext => x.
    f_equal.
    rewrite Nat2N.inj_add.
    replace (N.of_nat 1) with 1%N by reflexivity.
    lia.
Qed.

Lemma those0_map_Some : forall (l : list byte), those0 (List.map (@Some byte) l) = Some l.
Proof.
  elim=> [| x l' IH] //=.
  rewrite IH //=.
Qed.

Lemma read_bytes_after_write : forall bs mt m addr m',
  write_bytes m addr bs = Some m' ->
  read_bytes (Build_meminst mt m') addr (length bs) = Some bs.
Proof.
  move=> bs mt m addr m' Hwr.
  rewrite /read_bytes /=.
  rewrite (write_bytes_read_bytes bs m addr m' Hwr).
  rewrite -those_those0.
  exact: those0_map_Some.
Qed.

Lemma write_bytes_total : forall bs m addr,
  N.le (addr + N.of_nat (length bs)) (memory.mem_length m) ->
  exists m', write_bytes m addr bs = Some m'.
Proof.
  elim=> [| b bs' IH] m addr /=.
  - move=> _. by exists m.
  - move=> Hbound.
    have Hin : N.lt addr (memory.mem_length m) by lia.
    have Hne : mem_update addr b m <> None.
    { apply mem_update_ib with (mem := m) (i := addr) (b := b). exact Hin. }
    destruct (mem_update addr b m) as [m1|] eqn:Hup; [| congruence].
    have Hlen1 := @mem_update_length _ addr b m m1 Hup.
    have Hbound1 : N.le ((addr+1) + N.of_nat (length bs')) (memory.mem_length m1).
    { rewrite Hlen1. simpl in Hbound. lia. }
    exact: (IH m1 (addr+1) Hbound1).
Qed.

(** ** i32 store/load round trip *)

Lemma store_i32_effect : forall (m : meminst) addr (v : i32),
  N.le (addr + 4) (operations.mem_length m) ->
  exists m',
    store m addr 0 (serialise_num (VAL_int32 v)) 4 = Some m'
    /\ meminst_type m' = meminst_type m
    /\ write_bytes (meminst_data m) addr (serialise_num (VAL_int32 v)) = Some (meminst_data m').
Proof.
  move=> m addr v Hbound.
  rewrite /store.
  have Hlen4 : length (serialise_num (VAL_int32 v)) = 4%nat.
  { rewrite /serialise_num /serialise_i32. apply: Memdata.encode_int_length. }
  have Htf : bytes_takefill #00 4 (serialise_num (VAL_int32 v)) = serialise_num (VAL_int32 v).
  { unfold bytes_takefill. rewrite Hlen4.
    have -> : Nat.ltb 4 4 = false by reflexivity.
    rewrite -Hlen4. apply List.firstn_all. }
  rewrite Htf.
  have -> : (addr + 0 + N.of_nat 4 <=? operations.mem_length m) = true.
  { apply /N.leb_le. simpl. lia. }
  rewrite /write_bytes_meminst.
  rewrite N.add_0_r.
  have Hbound4 : N.le (addr + N.of_nat (length (serialise_num (VAL_int32 v)))) (operations.mem_length m).
  { rewrite Hlen4. simpl. lia. }
  have [md' Hwr] := write_bytes_total (serialise_num (VAL_int32 v)) (meminst_data m) addr Hbound4.
  rewrite Hwr.
  eexists. split; [reflexivity | split; reflexivity].
Qed.

Lemma write_bytes_mem_length : forall bs m addr m',
  write_bytes m addr bs = Some m' -> memory.mem_length m' = memory.mem_length m.
Proof.
  elim=> [| b bs' IH] m addr m' /=.
  - move=> [] <-. reflexivity.
  - destruct (mem_update addr b m) as [m1|] eqn:Hup; last discriminate.
    move=> Hwr.
    rewrite (IH m1 (addr+1) m' Hwr).
    apply mem_update_length with (mem := m) (mem' := m1) (i := addr) (b := b). exact Hup.
Qed.

Lemma load_i32_after_store : forall (m : meminst) addr (v : i32) m',
  store m addr 0 (serialise_num (VAL_int32 v)) 4 = Some m' ->
  load m' addr 0 4 = Some (serialise_num (VAL_int32 v))
  /\ wasm_deserialise (serialise_num (VAL_int32 v)) T_i32 = VAL_int32 v.
Proof.
  move=> m addr v m' Hst.
  move: Hst. rewrite /store.
  have Hlen4 : length (serialise_num (VAL_int32 v)) = 4%nat.
  { rewrite /serialise_num /serialise_i32. apply: Memdata.encode_int_length. }
  have Htf : bytes_takefill #00 4 (serialise_num (VAL_int32 v)) = serialise_num (VAL_int32 v).
  { unfold bytes_takefill. rewrite Hlen4.
    have -> : Nat.ltb 4 4 = false by reflexivity.
    rewrite -Hlen4. apply List.firstn_all. }
  rewrite Htf.
  destruct (addr + 0 + N.of_nat 4 <=? operations.mem_length m) eqn:Hle; last discriminate.
  rewrite /write_bytes_meminst.
  destruct (write_bytes (meminst_data m) (addr + 0) (serialise_num (VAL_int32 v))) as [md'|] eqn:Hwr;
    last discriminate.
  move=> [] Heqm'.
  split.
  - rewrite /load.
    have Hlen' : operations.mem_length m' = operations.mem_length m.
    { rewrite -Heqm' /operations.mem_length /=.
      rewrite (write_bytes_mem_length _ _ _ _ Hwr).
      reflexivity. }
    rewrite Hlen'.
    have -> : (addr + (0 + 4) <=? operations.mem_length m) = true.
    { move: Hle. rewrite N.add_0_r. move=> Hle2. apply /N.leb_le. move: Hle2 => /N.leb_le. lia. }
    rewrite -Heqm'.
    rewrite N.add_0_r.
    rewrite N.add_0_r in Hwr.
    have H := read_bytes_after_write (serialise_num (VAL_int32 v)) (meminst_type m) (meminst_data m) addr md' Hwr.
    rewrite Hlen4 in H.
    exact H.
  - rewrite /wasm_deserialise /serialise_num /serialise_i32.
    f_equal.
    rewrite Memdata.decode_encode_int.
    have Hrange := Wasm_int.Int32.unsigned_range v.
    have Hmod : two_p (Z.of_nat 4 * 8) = Wasm_int.Int32.modulus by vm_compute; reflexivity.
    rewrite Hmod.
    rewrite Z.mod_small; [| exact Hrange].
    have H := Wasm_int.Int32.int_of_Z_Z_of_uint v.
    rewrite /Wasm_int.int_of_Z /Wasm_int.Z_of_uint /= in H.
    exact H.
Qed.

(** ** Non-interference: an i32 store leaves bytes outside its range
      untouched (single-byte reads, e.g. pattern bytes, and other i32
      slots, e.g. earlier lps entries). *)

Lemma mem_lookup_after_store_i32_disjoint : forall (m : meminst) addr v m' j b,
  store m addr 0 (serialise_num (VAL_int32 v)) 4 = Some m' ->
  (j < addr \/ addr + 4 <= j) ->
  mem_lookup j (meminst_data m) = Some b ->
  mem_lookup j (meminst_data m') = Some b.
Proof.
  move=> m addr v m' j b Hst Hj Hlk.
  move: Hst. rewrite /store.
  have Hlen4 : length (serialise_num (VAL_int32 v)) = 4%nat.
  { rewrite /serialise_num /serialise_i32. apply: Memdata.encode_int_length. }
  destruct (addr + 0 + N.of_nat 4 <=? operations.mem_length m) eqn:Hle; last discriminate.
  rewrite /write_bytes_meminst.
  destruct (write_bytes (meminst_data m) (addr + 0)
              (bytes_takefill #00 4 (serialise_num (VAL_int32 v)))) as [md'|] eqn:Hwr;
    last discriminate.
  move=> [] <- /=.
  have Htf : bytes_takefill #00 4 (serialise_num (VAL_int32 v)) = serialise_num (VAL_int32 v).
  { unfold bytes_takefill. rewrite Hlen4.
    have -> : Nat.ltb 4 4 = false by reflexivity.
    rewrite -Hlen4. apply List.firstn_all. }
  have Hlen_tf : length (bytes_takefill #00 4 (serialise_num (VAL_int32 v))) = 4%nat.
  { rewrite Htf. exact Hlen4. }
  have Hj' : j < addr + 0 \/ addr + 0 + N.of_nat (length (bytes_takefill #00 4 (serialise_num (VAL_int32 v)))) <= j.
  { rewrite Hlen_tf N.add_0_r. exact Hj. }
  rewrite (write_bytes_out _ _ _ _ _ Hwr Hj').
  exact Hlk.
Qed.

(** ** [i32.load8_u]'s value, in terms of the loaded byte *)

Lemma load8_u_deserialise : forall (b : byte),
  wasm_deserialise (bytes_takefill #00 4 [b]) T_i32 = VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned b)).
Proof.
  move=> b.
  rewrite /wasm_deserialise /bytes_takefill /= /Memdata.decode_int /Memdata.rev_if_be.
  have Hbe : Archi.big_endian = false by vm_compute; reflexivity.
  rewrite Hbe /Memdata.int_of_bytes /=.
  have H0 : Integers.Byte.unsigned #00 = 0%Z by reflexivity.
  rewrite H0.
  do 2 f_equal. lia.
Qed.

(** Combines [load8_u_ok] and [load8_u_deserialise]: reading a byte via
    [i32.load8_u] yields exactly its unsigned value, zero-extended. *)
Lemma load8_u_value : forall (m : meminst) addr b,
  mem_lookup addr m.(meminst_data) = Some b ->
  N.lt addr (operations.mem_length m) ->
  exists bs, load_packed SX_U m addr 0 (tp_length Tp_i8) (tnum_length T_i32) = Some bs
    /\ wasm_deserialise bs T_i32 = VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned b)).
Proof.
  move=> m addr b Hlk Hbound.
  exists (bytes_takefill #00 4 [b]).
  split.
  - exact: (load8_u_ok m addr b Hlk Hbound).
  - exact: load8_u_deserialise.
Qed.

(** ** [i32.load]'s value: an in-range address whose four bytes are
      exactly a previously-serialised i32 loads back that i32 (the
      backtrack step of [build_lps] reads a *previously written* [lps]
      entry, not one it just stored, so this is stated from a bare
      [read_bytes] fact rather than [load_i32_after_store]'s [store]
      hypothesis). *)
Lemma load_i32_value : forall (m : meminst) addr v,
  read_bytes m addr 4 = Some (serialise_num (VAL_int32 v)) ->
  N.le (addr + 4) (operations.mem_length m) ->
  load m addr 0 4 = Some (serialise_num (VAL_int32 v))
  /\ wasm_deserialise (serialise_num (VAL_int32 v)) T_i32 = VAL_int32 v.
Proof.
  move=> m addr v Hrb Hbound.
  split.
  - rewrite /load.
    have -> : (addr + (0 + 4) <=? operations.mem_length m) = true.
    { apply /N.leb_le. lia. }
    rewrite N.add_0_r. exact Hrb.
  - rewrite /wasm_deserialise /serialise_num /serialise_i32.
    f_equal.
    rewrite Memdata.decode_encode_int.
    have Hrange := Wasm_int.Int32.unsigned_range v.
    have Hmod : two_p (Z.of_nat 4 * 8) = Wasm_int.Int32.modulus by vm_compute; reflexivity.
    rewrite Hmod.
    rewrite Z.mod_small; [| exact Hrange].
    have H := Wasm_int.Int32.int_of_Z_Z_of_uint v.
    rewrite /Wasm_int.int_of_Z /Wasm_int.Z_of_uint /= in H.
    exact H.
Qed.

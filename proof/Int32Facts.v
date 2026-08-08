(** Small i32 arithmetic facts, for values known to stay well within
    signed range throughout (loop counters, memory offsets bounded by
    realistic pattern/text lengths). Represents natural numbers as i32
    via [enc], and relates [enc]-encoded arithmetic/comparisons back to
    plain [N]/[nat] arithmetic. *)
From Wasm Require Import datatypes operations opsem numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia ZArith.
Open Scope Z_scope.

(** Comfortably below 2^31 (and 2^32), enough head-room for a shl-by-2
    (multiply by 4) to also stay in range for anything we encode. *)
Definition small (z : Z) : Prop := 0 <= z < 1073741824 (* 2^30 *).

Definition enc (z : Z) : i32 := Wasm_int.Int32.repr z.

Lemma i32_modulus : Wasm_int.Int32.modulus = 4294967296.
Proof. vm_compute. reflexivity. Qed.

Lemma i32_half_modulus : Wasm_int.Int32.half_modulus = 2147483648.
Proof. vm_compute. reflexivity. Qed.

Lemma enc_unsigned : forall z, small z -> Wasm_int.Int32.unsigned (enc z) = z.
Proof.
  move=> z [Hlo Hhi]. rewrite /enc.
  rewrite Wasm_int.Int32.unsigned_repr; [reflexivity |].
  rewrite /Wasm_int.Int32.max_unsigned i32_modulus. lia.
Qed.

Lemma enc_signed : forall z, small z -> Wasm_int.Int32.signed (enc z) = z.
Proof.
  move=> z Hs. rewrite /Wasm_int.Int32.signed enc_unsigned; [| exact Hs].
  rewrite i32_half_modulus.
  case: Coqlib.zlt => Hz; [reflexivity |]. exfalso. move: Hs Hz. rewrite /small. lia.
Qed.

Lemma enc_inj : forall z1 z2, small z1 -> small z2 -> enc z1 = enc z2 -> z1 = z2.
Proof.
  move=> z1 z2 Hs1 Hs2 Heq.
  have H := f_equal Wasm_int.Int32.unsigned Heq.
  rewrite (enc_unsigned z1 Hs1) (enc_unsigned z2 Hs2) in H. exact H.
Qed.

Lemma ge_s_iff : forall z1 z2, small z1 -> small z2 ->
  Wasm_int.int_ge_s i32m (enc z1) (enc z2) = true <-> z2 <= z1.
Proof.
  move=> z1 z2 Hs1 Hs2.
  rewrite /Wasm_int.int_ge_s /= /Wasm_int.Int32.lt.
  rewrite (enc_signed z2 Hs2) (enc_signed z1 Hs1).
  case: (Coqlib.zlt z1 z2) => Hz.
  - split; [discriminate | lia].
  - split; [lia | reflexivity].
Qed.

Lemma eq_i32_iff : forall z1 z2, small z1 -> small z2 ->
  Wasm_int.int_eq i32m (enc z1) (enc z2) = true <-> z1 = z2.
Proof.
  move=> z1 z2 Hs1 Hs2.
  rewrite /Wasm_int.int_eq /= /Wasm_int.Int32.eq (enc_unsigned z1 Hs1) (enc_unsigned z2 Hs2).
  case: (Coqlib.zeq z1 z2) => Hz.
  - split; [move=> _; exact Hz | reflexivity].
  - split; [discriminate | move=> Heq; exfalso; exact: Hz].
Qed.

Lemma ne_i32_iff : forall z1 z2, small z1 -> small z2 ->
  Wasm_int.int_ne i32m (enc z1) (enc z2) = true <-> z1 <> z2.
Proof.
  move=> z1 z2 Hs1 Hs2.
  rewrite /Wasm_int.int_ne /Wasm_int.int_eq /= /Wasm_int.Int32.eq
          (enc_unsigned z1 Hs1) (enc_unsigned z2 Hs2).
  case: (Coqlib.zeq z1 z2) => Hz /=.
  - split; [discriminate | move=> Hne; exfalso; exact: Hne].
  - split; [move=> _; exact Hz | reflexivity].
Qed.

Lemma add_enc : forall z1 z2, small z1 -> small z2 -> small (z1 + z2) ->
  Wasm_int.int_add i32m (enc z1) (enc z2) = enc (z1 + z2).
Proof.
  move=> z1 z2 Hs1 Hs2 Hs12.
  rewrite /Wasm_int.int_add /= /enc /Wasm_int.Int32.iadd /Wasm_int.Int32.add.
  rewrite (Wasm_int.Int32.unsigned_repr z1);
    [| rewrite /Wasm_int.Int32.max_unsigned i32_modulus; move: Hs1; rewrite /small; lia].
  rewrite (Wasm_int.Int32.unsigned_repr z2);
    [| rewrite /Wasm_int.Int32.max_unsigned i32_modulus; move: Hs2; rewrite /small; lia].
  reflexivity.
Qed.

Lemma sub_enc : forall z1 z2, small z1 -> small z2 -> z2 <= z1 ->
  Wasm_int.int_sub i32m (enc z1) (enc z2) = enc (z1 - z2).
Proof.
  move=> z1 z2 Hs1 Hs2 Hle.
  rewrite /Wasm_int.int_sub /= /enc /Wasm_int.Int32.isub /Wasm_int.Int32.sub.
  rewrite (Wasm_int.Int32.unsigned_repr z1);
    [| rewrite /Wasm_int.Int32.max_unsigned i32_modulus; move: Hs1; rewrite /small; lia].
  rewrite (Wasm_int.Int32.unsigned_repr z2);
    [| rewrite /Wasm_int.Int32.max_unsigned i32_modulus; move: Hs2; rewrite /small; lia].
  reflexivity.
Qed.

Lemma shl2_enc : forall z, small z -> small (z * 4) ->
  Wasm_int.int_shl i32m (enc z) (enc 2) = enc (z * 4).
Proof.
  move=> z Hs Hs4.
  rewrite /Wasm_int.int_shl /= /enc /Wasm_int.Int32.ishl /Wasm_int.Int32.shl.
  have H2 : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 2) = 2.
  { rewrite Wasm_int.Int32.unsigned_repr; [reflexivity |].
    rewrite /Wasm_int.Int32.max_unsigned i32_modulus. lia. }
  rewrite H2.
  rewrite (Wasm_int.Int32.unsigned_repr z);
    [| rewrite /Wasm_int.Int32.max_unsigned i32_modulus; move: Hs; rewrite /small; lia].
  f_equal.
  rewrite Z.shiftl_mul_pow2; [| lia].
  reflexivity.
Qed.

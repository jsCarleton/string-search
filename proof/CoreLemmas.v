(** Reusable structural lemmas about WasmCert-Coq's reduction relation
    ([reduce] / [reduce_trans], theories/opsem.v), used throughout the
    kmp.wasm correctness proof.

    [kmp.wasm] has no imports, so we instantiate the abstract [host] with
    the "no host functions" instance WasmCert-Coq itself uses for its
    extracted interpreter (extraction_instance.v: host_function := void). *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope list_scope.

(** Reducing the front of an instruction sequence reduces the whole
    sequence, leaving any fixed suffix untouched. This is the sequential-
    composition congruence rule; it follows from [r_label] instantiated
    at the trivial (zero-label, empty value-prefix) context, since
    [lfill (LH_base nil suffix) es = es ++ suffix]. *)
Lemma reduce_prefix : forall hs s f es hs' s' f' es' suffix,
  reduce hs s f es hs' s' f' es' ->
  reduce hs s f (es ++ suffix) hs' s' f' (es' ++ suffix).
Proof.
  move=> hs s f es hs' s' f' es' suffix Hred.
  eapply r_label with (lh := LH_base nil suffix).
  - exact: Hred.
  - reflexivity.
  - reflexivity.
Qed.

(** Append [suffix] to the instruction component of a configuration tuple. *)
Definition cfg_append (suffix: seq administrative_instruction)
                       (cfg: host_state * store_record * frame * seq administrative_instruction) :=
  let '(hs, s, f, es) := cfg in (hs, s, f, es ++ suffix).

(** [reduce_trans] lifted through a fixed suffix, by induction on the
    reflexive-transitive closure. *)
Lemma reduce_trans_prefix : forall cfg cfg' suffix,
  reduce_trans cfg cfg' ->
  reduce_trans (cfg_append suffix cfg) (cfg_append suffix cfg').
Proof.
  move=> cfg cfg' suffix Htrans.
  induction Htrans as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz].
  - apply: Relations.Relation_Operators.rt_step.
    destruct x as [[[hs s] f] es]; destruct y as [[[hs' s'] f'] es'].
    exact: reduce_prefix.
  - exact: Relations.Relation_Operators.rt_refl.
  - apply: (Relations.Relation_Operators.rt_trans _ _ _ (cfg_append suffix y)).
    + exact: IHxy.
    + exact: IHyz.
Qed.

(** The specialised, 8-variable-explicit form most call sites want. *)
Lemma reduce_trans_prefix' : forall hs s f es hs' s' f' es' suffix,
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  reduce_trans (hs, s, f, es ++ suffix) (hs', s', f', es' ++ suffix).
Proof.
  move=> hs s f es hs' s' f' es' suffix Htrans.
  exact: (reduce_trans_prefix (hs, s, f, es) (hs', s', f', es') suffix Htrans).
Qed.

(** A single [reduce] step lifts into [reduce_trans]. *)
Lemma reduce_trans_step : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' ->
  reduce_trans (hs, s, f, es) (hs', s', f', es').
Proof. move=> *. exact: Relations.Relation_Operators.rt_step. Qed.

(** [reduce_trans] is transitive. *)
Lemma reduce_trans_trans : forall cfg1 cfg2 cfg3,
  reduce_trans cfg1 cfg2 ->
  reduce_trans cfg2 cfg3 ->
  reduce_trans cfg1 cfg3.
Proof.
  move=> cfg1 cfg2 cfg3 H1 H2.
  exact: (Relations.Relation_Operators.rt_trans _ _ cfg1 cfg2 cfg3 H1 H2).
Qed.

(** [reduce_simple] steps lift directly into [reduce]. *)
Lemma reduce_simple_reduce : forall hs s f es es',
  reduce_simple es es' ->
  reduce hs s f es hs s f es'.
Proof. move=> *. exact: r_simple. Qed.

(** A single [reduce] step inside a frame lifts to a step of the whole
    framed configuration (the frame-congruence rule [r_frame]). *)
Lemma reduce_frame : forall hs s f es hs' s' f' es' n f0,
  reduce hs s f es hs' s' f' es' ->
  reduce hs s f0 [:: AI_frame n f es] hs' s' f0 [:: AI_frame n f' es'].
Proof. move=> *. exact: r_frame. Qed.

(** ... and [reduce_trans] inside a frame lifts to [reduce_trans] of the
    whole framed configuration, by induction on the closure -- the
    frame analogue of [reduce_trans_prefix]. *)
Definition cfg_frame (n: nat) (f0: frame)
                      (cfg: host_state * store_record * frame * seq administrative_instruction) :=
  let '(hs, s, f, es) := cfg in (hs, s, f0, [:: AI_frame n f es]).

Lemma reduce_trans_frame : forall cfg cfg' n f0,
  reduce_trans cfg cfg' ->
  reduce_trans (cfg_frame n f0 cfg) (cfg_frame n f0 cfg').
Proof.
  move=> cfg cfg' n f0 Htrans.
  induction Htrans as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz].
  - apply: Relations.Relation_Operators.rt_step.
    destruct x as [[[hs s] f] es]; destruct y as [[[hs' s'] f'] es'].
    exact: reduce_frame.
  - exact: Relations.Relation_Operators.rt_refl.
  - apply: (Relations.Relation_Operators.rt_trans _ _ _ (cfg_frame n f0 y)).
    + exact: IHxy.
    + exact: IHyz.
Qed.

Lemma reduce_trans_frame' : forall hs s f es hs' s' f' es' n f0,
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  reduce_trans (hs, s, f0, [:: AI_frame n f es]) (hs', s', f0, [:: AI_frame n f' es']).
Proof.
  move=> hs s f es hs' s' f' es' n f0 Htrans.
  exact: (reduce_trans_frame (hs, s, f, es) (hs', s', f', es') n f0 Htrans).
Qed.

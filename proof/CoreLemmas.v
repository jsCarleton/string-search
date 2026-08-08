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

(** As [reduce_prefix], but also keeping a fixed prefix of already-
    evaluated constant values in place -- e.g. an operand already on the
    stack, waiting for a binop/relop that hasn't been reached yet. Also
    via [r_label], now at [LH_base vs suffix] (nonempty [vs]). *)
Lemma reduce_ctx : forall hs s f vs es hs' s' f' es' suffix,
  reduce hs s f es hs' s' f' es' ->
  reduce hs s f (v_to_e_list vs ++ es ++ suffix) hs' s' f' (v_to_e_list vs ++ es' ++ suffix).
Proof.
  move=> hs s f vs es hs' s' f' es' suffix Hred.
  eapply r_label with (lh := LH_base vs suffix).
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

(** A single [reduce] step inside a single enclosing label lifts to a
    step of the labelled configuration (via [r_label] at the
    one-label, empty-prefix/suffix context). *)
Lemma reduce_label1 : forall hs s f es hs' s' f' es' n lbl,
  reduce hs s f es hs' s' f' es' ->
  reduce hs s f [:: AI_label n lbl es] hs' s' f' [:: AI_label n lbl es'].
Proof.
  move=> hs s f es hs' s' f' es' n lbl Hred.
  eapply r_label with (lh := LH_rec [::] n lbl (LH_base [::] [::]) [::]).
  - exact: Hred.
  - rewrite /= cats0. reflexivity.
  - rewrite /= cats0. reflexivity.
Qed.

Definition cfg_label (n: nat) (lbl: seq administrative_instruction)
                      (cfg: host_state * store_record * frame * seq administrative_instruction) :=
  let '(hs, s, f, es) := cfg in (hs, s, f, [:: AI_label n lbl es]).

Lemma reduce_trans_label1 : forall cfg cfg' n lbl,
  reduce_trans cfg cfg' ->
  reduce_trans (cfg_label n lbl cfg) (cfg_label n lbl cfg').
Proof.
  move=> cfg cfg' n lbl Htrans.
  induction Htrans as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz].
  - apply: Relations.Relation_Operators.rt_step.
    destruct x as [[[hs s] f] es]; destruct y as [[[hs' s'] f'] es'].
    exact: reduce_label1.
  - exact: Relations.Relation_Operators.rt_refl.
  - apply: (Relations.Relation_Operators.rt_trans _ _ _ (cfg_label n lbl y)).
    + exact: IHxy.
    + exact: IHyz.
Qed.

Lemma reduce_trans_label1' : forall hs s f es hs' s' f' es' n lbl,
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  reduce_trans (hs, s, f, [:: AI_label n lbl es]) (hs', s', f', [:: AI_label n lbl es']).
Proof.
  move=> hs s f es hs' s' f' es' n lbl Htrans.
  exact: (reduce_trans_label1 (hs, s, f, es) (hs', s', f', es') n lbl Htrans).
Qed.

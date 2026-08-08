(** Correctness of [build_lps]'s actual compiled instruction sequence
    (as parsed from the real kmp.wasm bytes in KMPBytes.v), reasoned
    about via WasmCert-Coq's real small-step [reduce]/[reduce_trans]
    relation. This file starts with the function's early-return prologue
    (the [if (patLen == 0) return] check); the main loop is built on top
    of this in later files, reusing the same techniques. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.

Definition kmp_module : module :=
  match kmp_module_opt with
  | Some m => m
  | None => Build_module nil nil nil nil nil nil nil None nil nil
  end.

Definition build_lps_func : module_func :=
  List.nth 0 (mod_funcs kmp_module) (Build_module_func 0%N nil nil).

Definition build_lps_body : expr := modfunc_body build_lps_func.

Definition zero32 := Wasm_int.Int32.repr 0.
Definition one32 := Wasm_int.Int32.repr 1.

(** The parsed body, computed once and split into its 3-instruction
    prologue plus the rest, both grounded by [vm_compute] against the
    real parsed bytecode (no hand-transcription). *)
Definition build_lps_es_c : list administrative_instruction := Eval vm_compute in to_e_list build_lps_body.
Definition build_lps_es_rest : list administrative_instruction := Eval vm_compute in List.skipn 3 build_lps_es_c.

Lemma build_lps_es_split :
  to_e_list build_lps_body =
    [AI_basic (BI_local_get 1); AI_basic (BI_testop T_i32 TO_eqz);
     AI_basic (BI_if (BT_valtype None) [BI_return] [])] ++ build_lps_es_rest.
Proof. vm_compute. reflexivity. Qed.

(** If the pattern is empty (local 1, [patLen], is zero), [build_lps]
    returns immediately without touching memory: the prologue's
    [if (patLen == 0) return] fires. Matches [KMPSpec.is_failure_table]
    trivially, since the empty pattern has an empty failure table. *)
Lemma build_lps_patLen_zero : forall (s : store_record) (inst : moduleinst) hs (f0 : frame)
    (patPtr lpsPtr : i32),
  let f := Build_frame [VAL_num (VAL_int32 patPtr); VAL_num (VAL_int32 zero32);
                         VAL_num (VAL_int32 lpsPtr); VAL_num (VAL_int32 zero32);
                         VAL_num (VAL_int32 zero32); VAL_num (VAL_int32 zero32)] inst in
  reduce_trans (hs, s, f0, [:: AI_frame 0 f [:: AI_label 0 [::] (to_e_list build_lps_body)]])
               (hs, s, f0, [::]).
Proof.
  move=> s inst hs f0 patPtr lpsPtr f.
  rewrite build_lps_es_split.
  set rest := build_lps_es_rest.
  (* Step A: local.get 1 pushes patLen (= 0). *)
  have HA : reduce hs s f [:: AI_basic (BI_local_get 1)] hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32))].
  { apply r_local_get with (v := VAL_num (VAL_int32 zero32)) (j := 1%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_testop T_i32 TO_eqz); AI_basic (BI_if (BT_valtype None) [BI_return] [])] HA.
  (* Step B: i32.eqz on 0 is true (1). *)
  have Heqz : app_testop_i i32m TO_eqz zero32 = true.
  { vm_compute. reflexivity. }
  have HB : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_testop T_i32 TO_eqz)]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 one32))].
  { apply reduce_simple_reduce.
    have := rs_testop_i32 zero32 TO_eqz.
    rewrite Heqz /=.
    move=> H. exact H. }
  have HB' := reduce_prefix _ _ _ _ _ _ _ _ [:: AI_basic (BI_if (BT_valtype None) [BI_return] [])] HB.
  (* Step C: the "if" takes its true branch, becoming block[return]. *)
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 one32));
                              AI_basic (BI_if (BT_valtype None) [BI_return] [])]
                    hs s f [:: AI_basic (BI_block (BT_valtype None) [BI_return])].
  { apply reduce_simple_reduce.
    apply rs_if_true.
    rewrite /one32.
    move=> Hz.
    have : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 1) = Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 0).
    { f_equal. exact Hz. }
    vm_compute. lia. }
  (* Step D: the "block" opens a fresh (0-arity) label around [return]. *)
  have HD : reduce hs s f [:: AI_basic (BI_block (BT_valtype None) [BI_return])]
                    hs s f [:: AI_label 0 [::] [:: AI_basic BI_return]].
  { apply r_block with (vs := [::]) (n := 0) (m := 0) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  have Hpre : reduce_trans (hs, s, f, [AI_basic (BI_local_get 1); AI_basic (BI_testop T_i32 TO_eqz);
                                        AI_basic (BI_if (BT_valtype None) [BI_return] [])])
                            (hs, s, f, [AI_label 0 [] [AI_basic BI_return]]).
  { apply: (reduce_trans_trans _ (hs,s,f,_) _).
    - exact: (reduce_trans_step _ _ _ _ _ _ _ _ HA').
    - apply: (reduce_trans_trans _ (hs,s,f,_) _).
      + exact: (reduce_trans_step _ _ _ _ _ _ _ _ HB').
      + apply: (reduce_trans_trans _ (hs,s,f,_) _).
        * exact: (reduce_trans_step _ _ _ _ _ _ _ _ HC).
        * exact: (reduce_trans_step _ _ _ _ _ _ _ _ HD). }
  have Hpre' := reduce_trans_prefix' _ _ _ _ _ _ _ _ rest Hpre.
  have Hlab := reduce_trans_label1' _ _ _ _ _ _ _ _ 0 [::] Hpre'.
  have Hfr := reduce_trans_frame' _ _ _ _ _ _ _ _ 0 f0 Hlab.
  (* Final step: BI_return, now visible two labels deep inside the call
     frame, collapses the whole frame directly to [] (0 return values)
     via rs_return -- the witness [lh] mirrors that 2-label nesting
     (outer function-body label, inner if-block label) with [rest]
     as the untouched suffix outside both. *)
  have Hret : reduce hs s f0
    [:: AI_frame 0 f [:: AI_label 0 [::] ([:: AI_label 0 [::] [:: AI_basic BI_return]] ++ rest)]]
    hs s f0 [::].
  { apply reduce_simple_reduce.
    apply (rs_return (n := 0) (i := 2) (vs := [::]) (es :=
      [:: AI_label 0 [::] ([:: AI_label 0 [::] [:: AI_basic BI_return]] ++ rest)])
      (lh := LH_rec [::] 0 [::] (LH_rec [::] 0 [::] (LH_base [::] [::]) rest) [::]));
      try reflexivity. }
  apply: (reduce_trans_trans _ (hs,s,f0,_) _).
  - exact: Hfr.
  - exact: (reduce_trans_step _ _ _ _ _ _ _ _ Hret).
Qed.

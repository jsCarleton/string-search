(** Correctness of [kmp_search]'s actual compiled instruction sequence
    (as parsed from the real kmp.wasm bytes in KMPBytes.v), reasoned
    about via WasmCert-Coq's real small-step [reduce]/[reduce_trans]
    relation -- the [kmp_search] analogue of [BuildLps.v]. This file
    starts with the function's early-return prologue (the
    [if (patLen == 0) return 0] check, mirroring [build_lps]'s own
    early return except this one returns a value); the main loop is
    built on top of this in later files, reusing [build_lps]'s
    techniques throughout. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.

Definition kmp_search_func : module_func :=
  List.nth 1 (mod_funcs kmp_module) (Build_module_func 0%N nil nil).

Definition kmp_search_body : expr := modfunc_body kmp_search_func.

(** Sanity check that [kmp_search_func] really is the second function in
    the parsed module (not the fallback default from an out-of-range
    [List.nth]) and that it's a distinct function from [build_lps_func]:
    the module has exactly 2 functions, and their bodies differ. *)
Lemma kmp_module_two_funcs : length (mod_funcs kmp_module) = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma kmp_search_func_distinct : kmp_search_body <> build_lps_body.
Proof. vm_compute. discriminate. Qed.

(** The parsed body, computed once and split into its 3-instruction
    prologue plus the rest, both grounded by [vm_compute] against the
    real parsed bytecode (no hand-transcription). Unlike [build_lps]'s
    prologue (a bare [return], 0 values), [kmp_search]'s prologue
    returns a value ([i32.const 0]), so the [if] branch is
    [[i32.const 0, return]] rather than just [[return]]. *)
Definition kmp_search_es_c : list administrative_instruction := Eval vm_compute in to_e_list kmp_search_body.
Definition kmp_search_es_rest : list administrative_instruction := Eval vm_compute in List.skipn 3 kmp_search_es_c.

Lemma kmp_search_es_split :
  to_e_list kmp_search_body =
    [AI_basic (BI_local_get 3); AI_basic (BI_testop T_i32 TO_eqz);
     AI_basic (BI_if (BT_valtype None) [BI_const_num (VAL_int32 zero32); BI_return] [])] ++ kmp_search_es_rest.
Proof. vm_compute. reflexivity. Qed.

(** If the pattern is empty (local 3, [patLen], is zero), [kmp_search]
    returns [0] immediately without touching memory or calling
    [build_lps]: the prologue's [if (patLen == 0) return 0] fires.
    Matches [KMPSpec.is_first_occurrence_empty] (the empty pattern's
    first occurrence is index 0, by convention). *)
Lemma kmp_search_patLen_zero : forall (s : store_record) (inst : moduleinst) hs (f0 : frame)
    (textPtr textLenN patPtr lpsPtr : i32),
  let f := Build_frame [VAL_num (VAL_int32 textPtr); VAL_num (VAL_int32 textLenN);
                         VAL_num (VAL_int32 patPtr); VAL_num (VAL_int32 zero32);
                         VAL_num (VAL_int32 lpsPtr); VAL_num (VAL_int32 zero32);
                         VAL_num (VAL_int32 zero32)] inst in
  reduce_trans (hs, s, f0, [:: AI_frame 1 f [:: AI_label 1 [::] (to_e_list kmp_search_body)]])
               (hs, s, f0, [:: AI_basic (BI_const_num (VAL_int32 zero32))]).
Proof.
  move=> s inst hs f0 textPtr textLenN patPtr lpsPtr f.
  rewrite kmp_search_es_split.
  set rest := kmp_search_es_rest.
  (* Step A: local.get 3 pushes patLen (= 0). *)
  have HA : reduce hs s f [:: AI_basic (BI_local_get 3)] hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32))].
  { apply r_local_get with (v := VAL_num (VAL_int32 zero32)) (j := 3%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_testop T_i32 TO_eqz); AI_basic (BI_if (BT_valtype None)
        [BI_const_num (VAL_int32 zero32); BI_return] [])] HA.
  (* Step B: i32.eqz on 0 is true (1). *)
  have Heqz : app_testop_i i32m TO_eqz zero32 = true.
  { vm_compute. reflexivity. }
  have HB : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_testop T_i32 TO_eqz)]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 one32))].
  { apply reduce_simple_reduce.
    have := rs_testop_i32 zero32 TO_eqz.
    rewrite Heqz /=.
    move=> H. exact H. }
  have HB' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_if (BT_valtype None) [BI_const_num (VAL_int32 zero32); BI_return] [])] HB.
  (* Step C: the "if" takes its true branch, becoming block[const 0; return]. *)
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 one32));
                              AI_basic (BI_if (BT_valtype None) [BI_const_num (VAL_int32 zero32); BI_return] [])]
                    hs s f [:: AI_basic (BI_block (BT_valtype None) [BI_const_num (VAL_int32 zero32); BI_return])].
  { apply reduce_simple_reduce.
    apply rs_if_true.
    rewrite /one32.
    move=> Hz.
    have : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 1) = Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 0).
    { f_equal. exact Hz. }
    vm_compute. lia. }
  (* Step D: the "block" opens a fresh (0-arity) label around [const 0; return]. *)
  have HD : reduce hs s f [:: AI_basic (BI_block (BT_valtype None) [BI_const_num (VAL_int32 zero32); BI_return])]
                    hs s f [:: AI_label 0 [::] [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic BI_return]].
  { apply r_block with (vs := [::]) (n := 0) (m := 0) (t1s := [::]) (t2s := [::]); try reflexivity; try done. }
  have Hpre : reduce_trans (hs, s, f, [AI_basic (BI_local_get 3); AI_basic (BI_testop T_i32 TO_eqz);
                                        AI_basic (BI_if (BT_valtype None)
                                          [BI_const_num (VAL_int32 zero32); BI_return] [])])
                            (hs, s, f, [AI_label 0 [] [AI_basic (BI_const_num (VAL_int32 zero32));
                                                        AI_basic BI_return]]).
  { apply: (reduce_trans_trans _ (hs,s,f,_) _).
    - exact: (reduce_trans_step _ _ _ _ _ _ _ _ HA').
    - apply: (reduce_trans_trans _ (hs,s,f,_) _).
      + exact: (reduce_trans_step _ _ _ _ _ _ _ _ HB').
      + apply: (reduce_trans_trans _ (hs,s,f,_) _).
        * exact: (reduce_trans_step _ _ _ _ _ _ _ _ HC).
        * exact: (reduce_trans_step _ _ _ _ _ _ _ _ HD). }
  have Hpre' := reduce_trans_prefix' _ _ _ _ _ _ _ _ rest Hpre.
  have Hlab := reduce_trans_label1' _ _ _ _ _ _ _ _ 1 [::] Hpre'.
  have Hfr := reduce_trans_frame' _ _ _ _ _ _ _ _ 1 f0 Hlab.
  (* Final step: BI_return, now visible two labels deep inside the call
     frame (outer function-body label, inner if-block label), collapses
     the whole frame directly to the pushed return value [0] -- the
     witness [lh] mirrors that 2-label nesting, matching
     [build_lps_patLen_zero]'s [Hret] exactly except the returned value
     list is [zero32] instead of empty. *)
  have Hret : reduce hs s f0
    [:: AI_frame 1 f [:: AI_label 1 [::] ([:: AI_label 0 [::]
          [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic BI_return]] ++ rest)]]
    hs s f0 [:: AI_basic (BI_const_num (VAL_int32 zero32))].
  { apply reduce_simple_reduce.
    apply (rs_return (n := 1) (i := 2) (vs := [:: AI_basic (BI_const_num (VAL_int32 zero32))]) (es :=
      [:: AI_label 1 [::] ([:: AI_label 0 [::]
            [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic BI_return]] ++ rest)])
      (lh := LH_rec [::] 1 [::] (LH_rec [::] 0 [::] (LH_base [::] [::]) rest) [::]));
      try reflexivity; try done. }
  apply: (reduce_trans_trans _ (hs,s,f0,_) _).
  - exact: Hfr.
  - exact: (reduce_trans_step _ _ _ _ _ _ _ _ Hret).
Qed.

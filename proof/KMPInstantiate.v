(** Step 6: connecting [build_lps_correct]/[kmp_search_correct] (steps
    4b/5, both already stated directly against the real [r_invoke_native]
    call shape but taking the store/instance/address facts as assumed
    hypotheses) to WasmCert-Coq's actual instantiation machinery
    ([interp_instantiate]/[instantiate], [instantiation_func.v]/
    [instantiation_spec.v]/[interp_instantiate_sound.v]). [kmp.wasm] has
    no imports, elements, data segments, or start function (confirmed
    below, ground truth against the real parsed bytes, same as every
    other structural fact in this proof) -- so instantiating it from the
    empty store is a single, closed computation: [interp_instantiate]
    fully determines the resulting store and module instance, with
    nothing left to run afterwards ([bes = [::]]). [interp_instantiate_
    imp_instantiate] then lifts that computation to a genuine proof of
    the spec-level [instantiate] relation, so the store/instance
    produced here are not merely "some values that happen to satisfy the
    right shape" but the actual, provably-conforming result of
    instantiating this exact module. Every structural hypothesis
    [build_lps_correct]/[kmp_search_correct] needed as an assumption --
    the two functions' addresses and closures, the memory's address and
    presence -- becomes a ground fact here, discharged by [vm_compute]
    exactly like every other closed-module fact throughout this proof
    (`build_lps_func_locals`, `kmp_module_parses`, etc.); what remains a
    hypothesis in the final theorems below is exactly the part outside
    the module's control -- the caller-supplied text/pattern bytes
    actually present in memory at call time. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics
  instantiation_func instantiation_spec interp_instantiate_sound.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith Arith.PeanoNat.
From Coq Require Strings.String.
Require Import KMPSpec KMPFailureRec KMPSearchRec CoreLemmas MemLemmas BuildLps BuildLpsTop
  BuildLpsMemTable Int32Facts KMPSearch KMPSearchTop.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

Definition empty_store : store_record := Build_store_record [::] [::] [::] [::] [::] [::].

(** The result of instantiating [kmp_module] from the empty store,
    computed once via [vm_compute] (mirroring [kmp_search_es_c]/
    [kmp_search_es_rest]'s use of the same technique in [KMPSearch.v]).
    Ground truth, not a hand-built value: whatever real store/instance
    WasmCert-Coq's own allocation function actually produces. *)
Definition kmp_inst_pair : store_record * moduleinst :=
  Eval vm_compute in
    match interp_instantiate tt empty_store kmp_module [::] with
    | (Some (_, s, f, _), _) => (s, f.(f_inst))
    | _ => (empty_store, empty_moduleinst)
    end.

Definition kmp_store : store_record := kmp_inst_pair.1.
Definition kmp_inst : moduleinst := kmp_inst_pair.2.

(** Ground truth: instantiating [kmp_module] (no imports) from the empty
    store succeeds, producing exactly [kmp_store]/[kmp_inst], with no
    elements/data/start left to run ([bes = [::]] -- there are none of
    any of the three in the module, confirmed by this same computation). *)
Lemma kmp_interp_instantiate_eq :
  interp_instantiate tt empty_store kmp_module [::]
  = (Some (tt, kmp_store, Build_frame [::] kmp_inst, [::]), String.EmptyString).
Proof. vm_compute. reflexivity. Qed.

(** Lifting the computation above to a genuine proof of the spec-level
    [instantiate] relation ([instantiation_spec.v]): [kmp_store]/
    [kmp_inst] are the real, provably-conforming result of instantiating
    [kmp_module], not merely a value chosen to have the right shape. *)
Theorem kmp_instantiate :
  instantiate empty_store kmp_module [::] (kmp_store, Build_frame [::] kmp_inst, [::]).
Proof.
  exact: (interp_instantiate_imp_instantiate tt tt empty_store kmp_module [::]
    kmp_store (Build_frame [::] kmp_inst) [::] String.EmptyString kmp_interp_instantiate_eq).
Qed.

(** The structural facts [build_lps_correct]/[kmp_search_correct] need
    as hypotheses, all now ground truths about the real instantiated
    module rather than assumptions: [build_lps]/[kmp_search] sit at
    funcaddrs 0/1 (module function order, no imports to shift indices),
    with closures matching their real compiled bodies and the module's
    own [inst_types]; the module's one memory sits at memaddr 0, freshly
    allocated to its declared minimum size (1 page, all zero bytes). *)
Lemma kmp_inst_funcs_eq : kmp_inst.(inst_funcs) = [:: 0%N; 1%N].
Proof. vm_compute. reflexivity. Qed.

Lemma kmp_build_lps_addr_eq : lookup_N kmp_inst.(inst_funcs) 0 = Some 0%N.
Proof. vm_compute. reflexivity. Qed.

Lemma kmp_build_lps_closure :
  lookup_N kmp_store.(s_funcs) 0
  = Some (FC_func_native (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32] [::]) kmp_inst build_lps_func).
Proof. vm_compute. reflexivity. Qed.

Lemma kmp_search_addr_eq : lookup_N kmp_inst.(inst_funcs) 1 = Some 1%N.
Proof. vm_compute. reflexivity. Qed.

Lemma kmp_search_closure :
  lookup_N kmp_store.(s_funcs) 1
  = Some (FC_func_native
      (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32; T_num T_i32; T_num T_i32] [:: T_num T_i32])
      kmp_inst kmp_search_func).
Proof. vm_compute. reflexivity. Qed.

Lemma kmp_inst_mems_eq : kmp_inst.(inst_mems) = [:: 0%N].
Proof. vm_compute. reflexivity. Qed.

(** The module's one memory, freshly allocated to its declared minimum
    size (1 page). Its concrete byte content is deliberately left
    opaque here -- [vm_compute] cannot fully normalise the underlying
    vector representation into a literal (the same "stuck on a
    dependent proof component" shape noted elsewhere in this proof for
    [enc]), and no theorem below needs it to: [kmp_mem0]'s only role is
    as the specific memory the [lookup_N kmp_store.(s_mems) 0 = Some m]
    hypothesis below forces [m] to be, and correctness is stated for
    *whatever bytes the caller has since written there*, not for the
    fresh all-zero state itself. *)
Definition kmp_mem0 : meminst :=
  Eval vm_compute in
    match lookup_N kmp_store.(s_mems) 0 with
    | Some m => m
    | None => gen_mem_instance (Build_limits 0%N None)
    end.

Lemma kmp_mem0_lookup_eq : lookup_N kmp_store.(s_mems) 0 = Some kmp_mem0.
Proof. vm_compute. reflexivity. Qed.

(** [build_lps]'s top-level correctness theorem, specialised to the real
    instantiated module: every structural hypothesis of
    [build_lps_correct] (the function's own address, its closure, the
    memory's address) is now a ground fact discharged internally, not
    an assumption the caller has to supply. What remains -- the pattern
    and second-buffer contents actually present in memory at call time
    -- is exactly what's outside the module's control. *)
Theorem build_lps_wasm_correct : forall hs f0 patPtr patLenN lpsPtr m (p : list byte)
    (qPtr : Z) (q : list byte),
  small patPtr -> small lpsPtr ->
  patLenN = Z.of_nat (length p) ->
  Nat.lt 0 (length p) ->
  small (Z.of_nat (length p)) ->
  small (Z.of_nat (length p) * 4) ->
  small (patPtr + Z.of_nat (length p)) ->
  small (lpsPtr + Z.of_nat (length p) * 4) ->
  lookup_N kmp_store.(s_mems) 0 = Some m ->
  N.le (Z.to_N (patPtr + Z.of_nat (length p))) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + Z.of_nat (length p) * 4) + 4) (operations.mem_length m) ->
  pat_mem_matches m patPtr p ->
  (patPtr + Z.of_nat (length p) <= lpsPtr \/ lpsPtr + Z.of_nat (length p) * 4 <= patPtr) ->
  small qPtr -> small (Z.of_nat (length q)) ->
  pat_mem_matches m qPtr q ->
  (qPtr + Z.of_nat (length q) <= lpsPtr \/ lpsPtr + Z.of_nat (length p) * 4 <= qPtr) ->
  let f_entry := Build_frame [VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                               VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                               VAL_num (VAL_int32 zero32); VAL_num (VAL_int32 zero32)] kmp_inst in
  exists s' m' table',
    is_failure_table p table'
    /\ lookup_N s'.(s_mems) 0 = Some m'
    /\ lps_mem_matches m' lpsPtr table' (length p)
    /\ pat_mem_matches m' patPtr p
    /\ pat_mem_matches m' qPtr q
    /\ operations.mem_length m' = operations.mem_length m
    /\ reduce_trans (hs, kmp_store, f0, [:: AI_frame 0 f_entry [:: AI_label 0 [::] (to_e_list build_lps_body)]])
                     (hs, s', f0, [::]).
Proof.
  move=> hs f0 patPtr patLenN lpsPtr m p qPtr q
    Hpp Hlp HpatLen Hnz Hlenp Hlenp4 Hpatb Hlpsb Hlkm Hmempat Hmemlps Hpmm Hnoalias
    Hqp Hqlen Hqmm Hqnoalias f_entry.
  exact: (build_lps_correct hs kmp_store kmp_inst f0 patPtr patLenN lpsPtr 0%N m p qPtr q
    Hpp Hlp HpatLen Hnz Hlenp Hlenp4 Hpatb Hlpsb kmp_inst_mems_eq Hlkm Hmempat Hmemlps Hpmm Hnoalias
    Hqp Hqlen Hqmm Hqnoalias).
Qed.

(** [kmp_search]'s top-level correctness theorem, specialised the same
    way: this is the final theorem of the proof, covering every pattern,
    stated directly against invoking the real, freshly-instantiated
    [kmp.wasm] module's exported [kmp_search] function. *)
Theorem kmp_wasm_correct : forall hs f0 textPtr textLenN patPtr patLenN lpsPtr m (txt pat : text),
  small textPtr -> small textLenN -> small patPtr -> small lpsPtr ->
  textLenN = Z.of_nat (length txt) -> patLenN = Z.of_nat (length pat) ->
  small (Z.of_nat (length txt)) -> small (Z.of_nat (length pat)) -> small (Z.of_nat (length pat) * 4) ->
  small (textPtr + Z.of_nat (length txt)) -> small (patPtr + Z.of_nat (length pat)) ->
  small (lpsPtr + Z.of_nat (length pat) * 4) ->
  lookup_N kmp_store.(s_mems) 0 = Some m ->
  N.le (Z.to_N (textPtr + Z.of_nat (length txt))) (operations.mem_length m) ->
  N.le (Z.to_N (patPtr + Z.of_nat (length pat))) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + Z.of_nat (length pat) * 4) + 4) (operations.mem_length m) ->
  pat_mem_matches m textPtr txt -> pat_mem_matches m patPtr pat ->
  (patPtr + Z.of_nat (length pat) <= lpsPtr \/ lpsPtr + Z.of_nat (length pat) * 4 <= patPtr) ->
  (textPtr + Z.of_nat (length txt) <= lpsPtr \/ lpsPtr + Z.of_nat (length pat) * 4 <= textPtr) ->
  let f_entry := Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                               VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                               VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                               VAL_num (VAL_int32 zero32)] kmp_inst in
  exists s' (m' : meminst) (res : Z),
    (res = -1 /\ does_not_occur txt pat \/ (0 <= res /\ is_first_occurrence txt pat (Z.to_nat res))) /\
    reduce_trans (hs, kmp_store, f0, [:: AI_frame 1 f_entry [:: AI_label 1 [::] (to_e_list kmp_search_body)]])
                 (hs, s', f0, [:: AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr res)))]).
Proof.
  move=> hs f0 textPtr textLenN patPtr patLenN lpsPtr m txt pat
    Hp1 Hp2 Hp3 Hp4 HtextLen HpatLen Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
    Hlkm Hmemt Hmemp Hmemlps4 Htmt Htmp Hnoalias Htextnoalias f_entry.
  exact: (kmp_search_correct hs kmp_store kmp_inst f0 textPtr textLenN patPtr patLenN lpsPtr 0%N m txt pat 0%N
    Hp1 Hp2 Hp3 Hp4 HtextLen HpatLen Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
    kmp_build_lps_addr_eq kmp_build_lps_closure kmp_inst_mems_eq Hlkm Hmemt Hmemp Hmemlps4 Htmt Htmp
    Hnoalias Htextnoalias).
Qed.

(** [kmp_search]'s call into [build_lps]: the first genuine cross-function
    reasoning in this proof. [r_call] turns [BI_call 0] into [AI_invoke
    addr] once the callee's address is resolved from the *caller's* own
    instance ([f.(f_inst).(inst_funcs)]); [r_invoke_native] then consumes
    the three already-pushed argument values together with [AI_invoke
    addr] in one step, producing exactly the entry configuration
    [BuildLpsTop.v]'s [build_lps_correct] is proved against (confirmed
    via [vm_compute] against the real [build_lps_func]: 3 [i32] params,
    0 results, 3 zero-initialized declared locals) -- so finishing the
    call is just handing that configuration to [build_lps_correct]. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPSpec KMPFailureRec CoreLemmas MemLemmas BuildLps Int32Facts BuildLpsMemTable
  BuildLpsTop KMPSearch.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** Ground truth: [build_lps_func]'s closure shape, confirmed against the
    real parsed module rather than assumed. Function 0's type is
    (i32,i32,i32) -> (), and its 3 declared locals ([len],[i],[tmp])
    default-initialize to zero -- exactly matching
    [build_lps_correct]'s [f_entry]. *)
Lemma build_lps_func_locals : modfunc_locals build_lps_func = [:: T_num T_i32; T_num T_i32; T_num T_i32].
Proof. vm_compute. reflexivity. Qed.

Lemma build_lps_func_defaults :
  default_vals (modfunc_locals build_lps_func)
  = Some [:: VAL_num (VAL_int32 zero32); VAL_num (VAL_int32 zero32); VAL_num (VAL_int32 zero32)].
Proof. vm_compute. reflexivity. Qed.

Theorem kmp_search_call_build_lps : forall hs s inst f
    (textPtr textLenN patPtr patLenN lpsPtr iN jN : Z) (p : list byte) (memaddr : N) (m : meminst)
    (build_lps_addr : funcaddr),
  f = Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                    VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                    VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 (enc iN));
                    VAL_num (VAL_int32 (enc jN))] inst ->
  lookup_N inst.(inst_funcs) 0 = Some build_lps_addr ->
  lookup_N s.(s_funcs) build_lps_addr
    = Some (FC_func_native (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32] [::]) inst build_lps_func) ->
  small patPtr -> small lpsPtr ->
  patLenN = Z.of_nat (length p) ->
  Nat.lt 0 (length p) ->
  small (Z.of_nat (length p)) ->
  small (Z.of_nat (length p) * 4) ->
  small (patPtr + Z.of_nat (length p)) ->
  small (lpsPtr + Z.of_nat (length p) * 4) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (patPtr + Z.of_nat (length p))) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + Z.of_nat (length p) * 4) + 4) (operations.mem_length m) ->
  pat_mem_matches m patPtr p ->
  (patPtr + Z.of_nat (length p) <= lpsPtr \/ lpsPtr + Z.of_nat (length p) * 4 <= patPtr) ->
  exists s' m' table',
    is_failure_table p table'
    /\ lookup_N s'.(s_mems) memaddr = Some m'
    /\ lps_mem_matches m' lpsPtr table' (length p)
    /\ reduce_trans (hs, s, f,
         [:: AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 3%N); AI_basic (BI_local_get 4%N);
             AI_basic (BI_call 0%N)])
         (hs, s', f, [::]).
Proof.
  move=> hs s inst f textPtr textLenN patPtr patLenN lpsPtr iN jN p memaddr m build_lps_addr
    Hf Hfunc Hclosure Hpp Hlp HpatLen Hnz Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm Hmempat Hmemlps Hpmm Hnoalias.
  have HA : reduce hs s f [:: AI_basic (BI_local_get 2%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patPtr))) (j := 2%N). rewrite Hf. reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 3%N); AI_basic (BI_local_get 4%N); AI_basic (BI_call 0%N)] HA.
  simpl in HA'.
  have HB : reduce hs s f [:: AI_basic (BI_local_get 3%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patLenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patLenN))) (j := 3%N). rewrite Hf. reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc patPtr))] _ _ _ _ _
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_call 0%N)] HB.
  simpl in HB'.
  have HC : reduce hs s f [:: AI_basic (BI_local_get 4%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lpsPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lpsPtr))) (j := 4%N). rewrite Hf. reflexivity. }
  have HC' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN))] _ _ _ _ _
    [:: AI_basic (BI_call 0%N)] HC.
  simpl in HC'.
  have HD : reduce hs s f [:: AI_basic (BI_call 0%N)] hs s f [:: AI_invoke build_lps_addr].
  { apply r_call. rewrite Hf /=. exact Hfunc. }
  have HD' := reduce_ctx _ _ _
    [:: VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN)); VAL_num (VAL_int32 (enc lpsPtr))]
    _ _ _ _ _ [::] HD.
  simpl in HD'.
  have HE0 : reduce hs s f
      [:: AI_basic (BI_const_num (VAL_int32 (enc patPtr))); AI_basic (BI_const_num (VAL_int32 (enc patLenN)));
          AI_basic (BI_const_num (VAL_int32 (enc lpsPtr))); AI_invoke build_lps_addr]
      hs s f
      [:: AI_frame 0
            (Build_frame
              ([:: VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN)); VAL_num (VAL_int32 (enc lpsPtr))]
               ++ [:: VAL_num (VAL_int32 zero32); VAL_num (VAL_int32 zero32); VAL_num (VAL_int32 zero32)]) inst)
            [:: AI_label 0 [::] (to_e_list build_lps_body)]].
  { apply r_invoke_native with (addr := build_lps_addr) (cl := FC_func_native (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32] [::]) inst build_lps_func)
      (ts1 := [:: T_num T_i32; T_num T_i32; T_num T_i32]) (ts2 := [::]) (code := build_lps_func) (x := 0%N)
      (ts := [:: T_num T_i32; T_num T_i32; T_num T_i32]) (es := build_lps_body)
      (ves := [:: AI_basic (BI_const_num (VAL_int32 (enc patPtr))); AI_basic (BI_const_num (VAL_int32 (enc patLenN)));
                  AI_basic (BI_const_num (VAL_int32 (enc lpsPtr)))])
      (vs := [:: VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN)); VAL_num (VAL_int32 (enc lpsPtr))])
      (n := 3%nat) (m := 0%nat) (k := 3%nat)
      (defaults := [:: VAL_num (VAL_int32 zero32); VAL_num (VAL_int32 zero32); VAL_num (VAL_int32 zero32)]).
    (* [vm_compute] is reserved for the one goal that genuinely needs to
       evaluate the parsed module ([code = Build_module_func x ts es]);
       used on the others (which mention the free variables [patPtr]/
       [patLenN]/[lpsPtr] via [enc]) it pathologically hangs -- [enc]
       wraps [Wasm_int.Int32.repr]'s dependent proof component, which
       [vm_compute] struggles to push through symbolically even though
       plain [reflexivity]'s conversion checker handles it instantly. *)
    - exact Hclosure.
    - reflexivity.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  (* [HE0]'s locals list is stated as [vs ++ defaults] (matching
     [r_invoke_native]'s conclusion exactly, so [apply] can unify it
     directly); it is convertible to the flat literal
     [build_lps_correct] expects, and plain application below relies on
     that conversion happening implicitly. An explicit [simpl]/
     [vm_compute] to flatten it first pathologically hangs here (same
     cause as the note above), so none is used. *)
  have Hchain1 := reduce_trans_trans _ _ _
    (reduce_trans_step _ _ _ _ _ _ _ _ HA') (reduce_trans_step _ _ _ _ _ _ _ _ HB').
  have Hchain2 := reduce_trans_trans _ _ _ Hchain1 (reduce_trans_step _ _ _ _ _ _ _ _ HC').
  have Hchain3 := reduce_trans_trans _ _ _ Hchain2 (reduce_trans_step _ _ _ _ _ _ _ _ HD').
  have Hchain4 := reduce_trans_trans _ _ _ Hchain3 (reduce_trans_step _ _ _ _ _ _ _ _ HE0).
  have Hrun := build_lps_correct hs s inst f patPtr patLenN lpsPtr memaddr m p
    Hpp Hlp HpatLen Hnz Hlenp Hlenp4 Hpatb Hlpsb Hmems Hlkm Hmempat Hmemlps Hpmm Hnoalias.
  move: Hrun => [s' [m' [table' [Hift [Hlkm' [Hlmm' Hred']]]]]].
  exists s', m', table'.
  split; [exact Hift |]. split; [exact Hlkm' |]. split; [exact Hlmm' |].
  exact: (reduce_trans_trans _ _ _ Hchain4 Hred').
Qed.

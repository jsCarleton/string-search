(** [kmp_search]'s top-level correctness theorem, assembled from every
    piece built so far -- the [kmp_search] analogue of [BuildLpsTop.v].
    Chains the prologue ([kmp_search_patLen_nonzero_pre]), the call into
    [build_lps] ([kmp_search_call_build_lps], itself built on
    [BuildLpsTop.v]'s [build_lps_correct]), the init sequence
    ([kmp_search_init_locals]), loop entry ([search_loop_entry]), and
    the whole loop ([kmp_search_run]) into one theorem stated directly
    against the real [r_invoke_native] call shape, covering both the
    empty-pattern case ([kmp_search_patLen_zero], the early return) and
    the general case. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith Arith.PeanoNat.
Require Import KMPSpec KMPFailureRec KMPSearchRec CoreLemmas MemLemmas BuildLps BuildLpsTop
  BuildLpsMemTable Int32Facts KMPSearch KMPSearchLoop KMPSearchExit KMPSearchCall
  KMPSearchInit KMPSearchRun.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(** The [patLen <> 0] case: chains prologue, call, init, and the whole
    loop into a single real-call-shaped theorem. *)
Theorem kmp_search_correct_nonempty : forall hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr
    memaddr m (txt pat : text) (build_lps_addr : funcaddr),
  small textPtr -> small textLenN -> small patPtr -> small lpsPtr ->
  textLenN = Z.of_nat (length txt) -> patLenN = Z.of_nat (length pat) ->
  Nat.lt 0 (length pat) ->
  small (Z.of_nat (length txt)) -> small (Z.of_nat (length pat)) -> small (Z.of_nat (length pat) * 4) ->
  small (textPtr + Z.of_nat (length txt)) -> small (patPtr + Z.of_nat (length pat)) ->
  small (lpsPtr + Z.of_nat (length pat) * 4) ->
  lookup_N inst.(inst_funcs) 0 = Some build_lps_addr ->
  lookup_N s.(s_funcs) build_lps_addr
    = Some (FC_func_native (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32] [::]) inst build_lps_func) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (textPtr + Z.of_nat (length txt))) (operations.mem_length m) ->
  N.le (Z.to_N (patPtr + Z.of_nat (length pat))) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + Z.of_nat (length pat) * 4) + 4) (operations.mem_length m) ->
  pat_mem_matches m textPtr txt -> pat_mem_matches m patPtr pat ->
  (patPtr + Z.of_nat (length pat) <= lpsPtr \/ lpsPtr + Z.of_nat (length pat) * 4 <= patPtr) ->
  (textPtr + Z.of_nat (length txt) <= lpsPtr \/ lpsPtr + Z.of_nat (length pat) * 4 <= textPtr) ->
  let f_entry := Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                               VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                               VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                               VAL_num (VAL_int32 zero32)] inst in
  exists s' (m' : meminst) (res : Z),
    (res = -1 /\ does_not_occur txt pat \/ (0 <= res /\ is_first_occurrence txt pat (Z.to_nat res))) /\
    reduce_trans (hs, s, f0, [:: AI_frame 1 f_entry [:: AI_label 1 [::] (to_e_list kmp_search_body)]])
                 (hs, s', f0, [:: AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr res)))]).
Proof.
  move=> hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m txt pat build_lps_addr
    Hp1 Hp2 Hp3 Hp4 HtextLen HpatLen Hnz Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
    Hfunc Hclosure Hmems Hlkm Hmemt Hmemp Hmemlps4 Htmt Htmp Hnoalias Htextnoalias f_entry.
  have HtextLen_small : small textLenN by rewrite HtextLen.
  have HpatLen_small : small patLenN by rewrite HpatLen.
  have Hne : patLenN <> 0 by rewrite HpatLen; lia.
  (* Prologue: patLen <> 0, so the early-return check falls through. *)
  have Hpre := kmp_search_patLen_nonzero_pre s inst hs f_entry textPtr textLenN patPtr patLenN lpsPtr
    zero32 zero32 HpatLen_small Hne erefl.
  have Hpre' := reduce_trans_prefix' _ _ _ _ _ _ _ _ kmp_search_es_rest Hpre.
  rewrite List.app_nil_l in Hpre'.
  rewrite -kmp_search_es_split in Hpre'.
  rewrite kmp_search_es_rest_split in Hpre'.
  (* Call build_lps. *)
  have Hmemlps : N.le (Z.to_N (lpsPtr + Z.of_nat (length pat) * 4)) (operations.mem_length m) by lia.
  have Hcall := kmp_search_call_build_lps hs s inst f_entry textPtr textLenN patPtr patLenN lpsPtr 0 0 txt pat memaddr m
    build_lps_addr erefl Hfunc Hclosure Hp3 Hp4 HpatLen Hnz Hlenp Hlenp4 Hpatb Hlpsb
    Hmems Hlkm Hmemp Hmemlps4 Htmp Hnoalias
    Hp1 Hlent Htmt Htextnoalias.
  move: Hcall => [s1 [m1 [table [Hift [Hlkm1 [Hlmm1 [Hpmm1 [Htmt1 [HmemLen1 Hcall_red]]]]]]]]].
  have Hcall' := reduce_trans_prefix' _ _ _ _ _ _ _ _
    (kmp_search_init_es ++ [:: kmp_search_block_es] ++ kmp_search_final_es) Hcall_red.
  rewrite List.app_nil_l in Hcall'.
  (* Init: i := 0; j := 0. *)
  have Hinit := kmp_search_init_locals hs s1 inst textPtr textLenN patPtr patLenN lpsPtr zero32 zero32.
  set f_loop0 := search_frame inst textPtr textLenN patPtr patLenN lpsPtr 0 0 in Hinit.
  have Heq_floop : Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                                 VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                                 VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                                 VAL_num (VAL_int32 zero32)] inst = f_loop0.
  { rewrite /f_loop0 /search_frame. reflexivity. }
  have Hinit' := reduce_trans_prefix' _ _ _ _ _ _ _ _ ([:: kmp_search_block_es] ++ kmp_search_final_es) Hinit.
  rewrite Heq_floop in Hinit'.
  (* Combine prologue + call + init into one chain up to the [block]. *)
  have Hchain1 := reduce_trans_trans _ _ _ Hcall' Hinit'.
  have Hchain2 := reduce_trans_trans _ _ _ Hpre' Hchain1.
  (* Enter the loop. *)
  have Hentry := search_loop_entry hs s1 f_loop0.
  have Hentry' := reduce_trans_prefix' _ _ _ _ _ _ _ _ kmp_search_final_es Hentry.
  have Hchain3 := reduce_trans_trans _ _ _ Hchain2 Hentry'.
  (* [Hchain3] is still the unframed chain (active frame [f_entry]/
     [f_loop0] directly, no [AI_frame]/[AI_label] wrapper) -- unlike
     [build_lps_run_bare], [kmp_search_run] is stated in the already-
     wrapped shape (matching this theorem's own conclusion), so lift
     [Hchain3] through the function-body label and the calling frame
     before it can be chained with [Hrun]'s [Hred]. *)
  have Hchain3Lab := reduce_trans_label1' _ _ _ _ _ _ _ _ 1 [::] Hchain3.
  have Hchain3Fr := reduce_trans_frame' _ _ _ _ _ _ _ _ 1 f0 Hchain3Lab.
  (* Run the whole loop, starting from i = 0, j = 0. *)
  have Hm0 : search_matches txt pat 0 0 := search_matches_zero txt pat 0 (Nat.le_0_l _).
  have Hno0 : search_no_occ_before txt pat (Nat.sub 0 0) by move=> i' Hi'; exfalso; lia.
  have Hsmall0 : small (Z.of_nat 0) by rewrite /small; lia.
  (* [m1]'s bounds/preservation facts derive from [m]'s via [HmemLen1]
     (build_lps's own memory-length preservation, now exposed by
     [kmp_search_call_build_lps]); [Hpmm1]/[Htmt1] (also newly exposed)
     give the pattern/text buffers' own contents preserved into [m1]. *)
  have Hmemt1 : N.le (Z.to_N (textPtr + Z.of_nat (length txt))) (operations.mem_length m1).
  { rewrite HmemLen1. exact Hmemt. }
  have Hmemp1 : N.le (Z.to_N (patPtr + Z.of_nat (length pat))) (operations.mem_length m1).
  { rewrite HmemLen1. exact Hmemp. }
  have Hmemlps1 : N.le (Z.to_N (lpsPtr + Z.of_nat (length pat) * 4)) (operations.mem_length m1).
  { rewrite HmemLen1. exact Hmemlps. }
  have Hrun := kmp_search_run (length txt) hs s1 inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m1
    txt pat table 0 0
    Hp1 Hp3 Hp4 HtextLen HpatLen Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
    Hmems Hlkm1 Hmemt1 Hmemp1 Hmemlps1 Htmt1 Hpmm1 Hift Hlmm1
    (ltac:(lia)) Hsmall0 Hnz Hm0 Hno0.
  simpl in Hrun.
  destruct Hrun as [[Hnocc Hred] | [v [Hfound Hred]]].
  - exists s1, m1, (-1).
    split; [left; split; [reflexivity | exact Hnocc] |].
    exact: (reduce_trans_trans _ _ _ Hchain3Fr Hred).
  - exists s1, m1, (Z.of_nat v).
    split; [right; split; [lia | rewrite Nat2Z.id; exact Hfound] |].
    exact: (reduce_trans_trans _ _ _ Hchain3Fr Hred).
Qed.

(** The fully general top-level theorem: every hypothesis of
    [kmp_search_correct_nonempty] except [Nat.lt 0 (length pat)],
    covering EVERY pattern by case-splitting on whether it's empty
    ([kmp_search_patLen_zero], instantiated at [enc textPtr]/[enc
    textLenN]/[enc patPtr]/[enc lpsPtr] with [patLenN]'s slot forced to
    [zero32] by [HpatLen]) or not (handed straight to
    [kmp_search_correct_nonempty]). *)
Theorem kmp_search_correct : forall hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr
    memaddr m (txt pat : text) (build_lps_addr : funcaddr),
  small textPtr -> small textLenN -> small patPtr -> small lpsPtr ->
  textLenN = Z.of_nat (length txt) -> patLenN = Z.of_nat (length pat) ->
  small (Z.of_nat (length txt)) -> small (Z.of_nat (length pat)) -> small (Z.of_nat (length pat) * 4) ->
  small (textPtr + Z.of_nat (length txt)) -> small (patPtr + Z.of_nat (length pat)) ->
  small (lpsPtr + Z.of_nat (length pat) * 4) ->
  lookup_N inst.(inst_funcs) 0 = Some build_lps_addr ->
  lookup_N s.(s_funcs) build_lps_addr
    = Some (FC_func_native (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32] [::]) inst build_lps_func) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  N.le (Z.to_N (textPtr + Z.of_nat (length txt))) (operations.mem_length m) ->
  N.le (Z.to_N (patPtr + Z.of_nat (length pat))) (operations.mem_length m) ->
  N.le (Z.to_N (lpsPtr + Z.of_nat (length pat) * 4) + 4) (operations.mem_length m) ->
  pat_mem_matches m textPtr txt -> pat_mem_matches m patPtr pat ->
  (patPtr + Z.of_nat (length pat) <= lpsPtr \/ lpsPtr + Z.of_nat (length pat) * 4 <= patPtr) ->
  (textPtr + Z.of_nat (length txt) <= lpsPtr \/ lpsPtr + Z.of_nat (length pat) * 4 <= textPtr) ->
  let f_entry := Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                               VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                               VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                               VAL_num (VAL_int32 zero32)] inst in
  exists s' (m' : meminst) (res : Z),
    (res = -1 /\ does_not_occur txt pat \/ (0 <= res /\ is_first_occurrence txt pat (Z.to_nat res))) /\
    reduce_trans (hs, s, f0, [:: AI_frame 1 f_entry [:: AI_label 1 [::] (to_e_list kmp_search_body)]])
                 (hs, s', f0, [:: AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr res)))]).
Proof.
  move=> hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m txt pat build_lps_addr
    Hp1 Hp2 Hp3 Hp4 HtextLen HpatLen Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
    Hfunc Hclosure Hmems Hlkm Hmemt Hmemp Hmemlps4 Htmt Htmp Hnoalias Htextnoalias f_entry.
  case: (Nat.eq_dec (length pat) 0) => Hlen.
  - (* Empty pattern: the prologue's early return fires with result 0,
       matching [is_first_occurrence_empty]'s convention. *)
    have Hpat_nil : pat = [::] := proj1 (List.length_zero_iff_nil pat) Hlen.
    have HpatLen0 : patLenN = 0 by rewrite HpatLen Hlen.
    have f_entry_eq : f_entry =
      Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                    VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 zero32);
                    VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                    VAL_num (VAL_int32 zero32)] inst.
    { rewrite /f_entry HpatLen0. reflexivity. }
    have Hred := kmp_search_patLen_zero s inst hs f0 (enc textPtr) (enc textLenN) (enc patPtr) (enc lpsPtr).
    rewrite -f_entry_eq in Hred.
    exists s, m, 0.
    split.
    + right. split; [lia |]. rewrite Hpat_nil. exact: is_first_occurrence_empty.
    + exact Hred.
  - (* Nonempty pattern: hand off to [kmp_search_correct_nonempty]. *)
    have Hnz : Nat.lt 0 (length pat) by lia.
    exact: (kmp_search_correct_nonempty hs s inst f0 textPtr textLenN patPtr patLenN lpsPtr memaddr m txt pat
      build_lps_addr Hp1 Hp2 Hp3 Hp4 HtextLen HpatLen Hnz Hlent Hlenp Hlenp4 Htextb Hpatb Hlpsb
      Hfunc Hclosure Hmems Hlkm Hmemt Hmemp Hmemlps4 Htmt Htmp Hnoalias Htextnoalias).
Qed.

(** [kmp_search]'s loop body, continued from KMPSearchExit.v: the 9
    instructions after the [i >= textLen] exit check -- loading
    [text[i]] and [pat[j]] via [i32.load8_u] (MemLemmas.v) and comparing
    them. The [kmp_search] analogue of [BuildLpsCmp.v]'s
    [build_lps_load_cmp], with the same technique throughout (same 9
    instructions, same shape), just reading from two separate buffers
    ([textPtr]/[i] and [patPtr]/[j]) instead of one buffer at two
    offsets ([patPtr]/[i] and [patPtr]/[len]). *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps Int32Facts KMPSearch KMPSearchLoop KMPSearchExit.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

Definition search_loop_load_cmp_es : list administrative_instruction :=
  Eval vm_compute in List.firstn 9 search_loop_after_check_es.
Definition search_loop_after_cmp_es : list administrative_instruction :=
  Eval vm_compute in List.skipn 9 search_loop_after_check_es.

Lemma search_loop_after_check_es_split :
  search_loop_after_check_es = search_loop_load_cmp_es ++ search_loop_after_cmp_es.
Proof. vm_compute. reflexivity. Qed.

Lemma search_loop_load_cmp_es_eq :
  search_loop_load_cmp_es =
    [AI_basic (BI_local_get 0%N); AI_basic (BI_local_get 5%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 6%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))].
Proof. vm_compute. reflexivity. Qed.

(** [text[i]] and [pat[j]] are loaded via [i32.load8_u] (so the caller
    must supply which bytes are actually there, [bi]/[bj], and that the
    addresses are in-bounds) and compared. *)
Lemma kmp_search_load_cmp : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi bj,
  small textPtr -> small textLenN -> small patPtr -> small patLenN -> small lpsPtr -> small iN -> small jN ->
  small (textPtr + iN) -> small (patPtr + jN) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  mem_lookup (Z.to_N (textPtr + iN)) m.(meminst_data) = Some bi ->
  N.lt (Z.to_N (textPtr + iN)) (operations.mem_length m) ->
  mem_lookup (Z.to_N (patPtr + jN)) m.(meminst_data) = Some bj ->
  N.lt (Z.to_N (patPtr + jN)) (operations.mem_length m) ->
  let f := search_frame inst textPtr textLenN patPtr patLenN lpsPtr iN jN in
  reduce_trans (hs, s, f, search_loop_load_cmp_es)
    (hs, s, f, [:: AI_basic (BI_const_num (VAL_int32 (if Integers.Byte.eq_dec bi bj then one32 else zero32)))]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr iN jN memaddr m bi bj
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 Hp7 HaddTI HaddPJ Hmems Hlkm Hlki Hbndi Hlkj Hbndj f.
  rewrite search_loop_load_cmp_es_eq.
  have Hsmem : smem s inst = Some m.
  { rewrite /smem Hmems /=. rewrite Hlkm. reflexivity. }
  (* local.get 0 : textPtr *)
  have HA : reduce hs s f [:: AI_basic (BI_local_get 0%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc textPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc textPtr))) (j := 0%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 5%N); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 6%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HA.
  simpl in HA'.
  (* local.get 5 : i, with textPtr kept on stack *)
  have HB : reduce hs s f [:: AI_basic (BI_local_get 5%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 5%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc textPtr))] _ _ _ _ _
    [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 6%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HB.
  simpl in HB'.
  (* i32.add : textPtr + i *)
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc textPtr))); AI_basic (BI_const_num (VAL_int32 (enc iN)));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (textPtr + iN))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc textPtr)) (VAL_int32 (enc iN)) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc textPtr)) (VAL_int32 (enc iN)) = Some (VAL_int32 (enc (textPtr + iN))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (add_enc textPtr iN Hp1 Hp6 HaddTI). }
    pose proof (@rs_binop_success (VAL_int32 (enc textPtr)) (VAL_int32 (enc iN)) (VAL_int32 (enc (textPtr + iN)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HC' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 6%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HC.
  simpl in HC'.
  (* i32.load8_u : text[i] *)
  have HaddTI_N : Wasm_int.N_of_uint i32m (enc (textPtr + iN)) = Z.to_N (textPtr + iN).
  { rewrite /Wasm_int.N_of_uint /=.
    f_equal.
    apply Wasm_int.Int32.Z_mod_modulus_id.
    move: HaddTI. rewrite /small.
    have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
    rewrite Hmod. lia. }
  have [bs [Hbsload Hbsval]] := load8_u_value m (Z.to_N (textPtr + iN)) bi Hlki Hbndi.
  have HD : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (textPtr + iN))));
                              AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi))))].
  { have Hld : load_packed SX_U m (Wasm_int.N_of_uint i32m (enc (textPtr+iN))) 0%N (tp_length Tp_i8) (tnum_length T_i32) = Some bs.
    { rewrite HaddTI_N. exact Hbsload. }
    pose proof (@r_load_packed_success _ _ _ s f T_i32 Tp_i8 (enc (textPtr+iN)) (Build_memarg 0%N 0%N) m bs SX_U hs
      Hsmem Hld) as Hstep.
    rewrite Hbsval in Hstep.
    exact: Hstep. }
  have HD' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 2%N); AI_basic (BI_local_get 6%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HD.
  simpl in HD'.
  (* local.get 2 : patPtr, with text[i]'s value kept on stack *)
  have HE : reduce hs s f [:: AI_basic (BI_local_get 2%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patPtr))) (j := 2%N). reflexivity. }
  have HE' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi)))] _ _ _ _ _
    [:: AI_basic (BI_local_get 6%N); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N)); AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HE.
  simpl in HE'.
  (* local.get 6 : j *)
  have HF : reduce hs s f [:: AI_basic (BI_local_get 6%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc jN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc jN))) (j := 6%N). reflexivity. }
  have HF' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi))); VAL_num (VAL_int32 (enc patPtr))]
    _ _ _ _ _ [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N)); AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HF.
  simpl in HF'.
  (* i32.add : patPtr + j *)
  have HG : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patPtr))); AI_basic (BI_const_num (VAL_int32 (enc jN)));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (patPtr + jN))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc patPtr)) (VAL_int32 (enc jN)) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc patPtr)) (VAL_int32 (enc jN)) = Some (VAL_int32 (enc (patPtr + jN))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (add_enc patPtr jN Hp3 Hp7 HaddPJ). }
    pose proof (@rs_binop_success (VAL_int32 (enc patPtr)) (VAL_int32 (enc jN)) (VAL_int32 (enc (patPtr + jN)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HG' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi)))] _ _ _ _ _
    [:: AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N)); AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HG.
  simpl in HG'.
  (* i32.load8_u : pat[j] *)
  have HaddPJ_N : Wasm_int.N_of_uint i32m (enc (patPtr + jN)) = Z.to_N (patPtr + jN).
  { rewrite /Wasm_int.N_of_uint /=.
    f_equal.
    apply Wasm_int.Int32.Z_mod_modulus_id.
    move: HaddPJ. rewrite /small.
    have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
    rewrite Hmod. lia. }
  have [bs2 [Hbsload2 Hbsval2]] := load8_u_value m (Z.to_N (patPtr + jN)) bj Hlkj Hbndj.
  have HH : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (patPtr + jN))));
                              AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bj))))].
  { have Hld2 : load_packed SX_U m (Wasm_int.N_of_uint i32m (enc (patPtr+jN))) 0%N (tp_length Tp_i8) (tnum_length T_i32) = Some bs2.
    { rewrite HaddPJ_N. exact Hbsload2. }
    pose proof (@r_load_packed_success _ _ _ s f T_i32 Tp_i8 (enc (patPtr+jN)) (Build_memarg 0%N 0%N) m bs2 SX_U hs
      Hsmem Hld2) as Hstep.
    rewrite Hbsval2 in Hstep.
    exact: Hstep. }
  have HH' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi)))] _ _ _ _ _
    [:: AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HH.
  simpl in HH'.
  have Hbmod : Integers.Byte.modulus = 256 by vm_compute; reflexivity.
  have Hbyte_small : forall bb : byte, small (Integers.Byte.unsigned bb).
  { move=> bb. rewrite /small. have := Integers.Byte.unsigned_range bb. rewrite Hbmod. lia. }
  have HI : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi))));
                              AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bj))));
                              AI_basic (BI_relop T_i32 (Relop_i ROI_eq))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (if Integers.Byte.eq_dec bi bj then one32 else zero32)))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi)))
                 (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bj))) T_i32 (Relop_i ROI_eq).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc (Integers.Byte.unsigned bi))) (VAL_int32 (enc (Integers.Byte.unsigned bj)))
      T_i32 (Relop_i ROI_eq) Htc) as Hstep.
    move: Hstep. rewrite /app_relop /=.
    have Heqb : Wasm_int.Int32.eq (enc (Integers.Byte.unsigned bi)) (enc (Integers.Byte.unsigned bj))
                = (if Integers.Byte.eq_dec bi bj then true else false).
    { rewrite /Wasm_int.Int32.eq (enc_unsigned _ (Hbyte_small bi)) (enc_unsigned _ (Hbyte_small bj)).
      case: (Coqlib.zeq (Integers.Byte.unsigned bi) (Integers.Byte.unsigned bj)) => Hz;
        case: (Integers.Byte.eq_dec bi bj) => Heq; try reflexivity.
      - exfalso. apply Heq. rewrite -(Integers.Byte.repr_unsigned bi) -(Integers.Byte.repr_unsigned bj) Hz. reflexivity.
      - exfalso. apply Hz. rewrite Heq. reflexivity. }
    rewrite Heqb.
    case: (Integers.Byte.eq_dec bi bj) => Heq /=; move=> H; exact H. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB'.
  have Step3 := reduce_trans_step _ _ _ _ _ _ _ _ HC'.
  have Step4 := reduce_trans_step _ _ _ _ _ _ _ _ HD'.
  have Step5 := reduce_trans_step _ _ _ _ _ _ _ _ HE'.
  have Step6 := reduce_trans_step _ _ _ _ _ _ _ _ HF'.
  have Step7 := reduce_trans_step _ _ _ _ _ _ _ _ HG'.
  have Step8 := reduce_trans_step _ _ _ _ _ _ _ _ HH'.
  have Step9 := reduce_trans_step _ _ _ _ _ _ _ _ HI.
  have C12 := reduce_trans_trans _ _ _ Step1 Step2.
  have C123 := reduce_trans_trans _ _ _ C12 Step3.
  have C1234 := reduce_trans_trans _ _ _ C123 Step4.
  have C12345 := reduce_trans_trans _ _ _ C1234 Step5.
  have C123456 := reduce_trans_trans _ _ _ C12345 Step6.
  have C1234567 := reduce_trans_trans _ _ _ C123456 Step7.
  have C12345678 := reduce_trans_trans _ _ _ C1234567 Step8.
  have C123456789 := reduce_trans_trans _ _ _ C12345678 Step9.
  exact: C123456789.
Qed.

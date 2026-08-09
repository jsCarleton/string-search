(** [build_lps]'s loop body, continued from BuildLpsExit.v: the 9
    instructions after the [i >= patLen] exit check -- loading [p[i]]
    and [p[len]] via [i32.load8_u] (MemLemmas.v) and comparing them.
    This is common to both the match and mismatch branches that follow
    (not yet proved); those branch on this comparison's result. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps BuildLpsLoop Int32Facts BuildLpsExit.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

(* First 9 instructions of loop_after_check_es: load p[i], load p[len], compare *)
Definition loop_load_cmp_es : list administrative_instruction := Eval vm_compute in List.firstn 9 loop_after_check_es.
Definition loop_after_cmp_es : list administrative_instruction := Eval vm_compute in List.skipn 9 loop_after_check_es.

Lemma loop_after_check_es_split :
  loop_after_check_es = loop_load_cmp_es ++ loop_after_cmp_es.
Proof. vm_compute. reflexivity. Qed.

Lemma loop_load_cmp_es_eq :
  loop_load_cmp_es =
    [AI_basic (BI_local_get 0%N); AI_basic (BI_local_get 4%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_local_get 0%N); AI_basic (BI_local_get 3%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))].
Proof. vm_compute. reflexivity. Qed.

(** [p[i]] and [p[len]] are loaded via [i32.load8_u] (so the caller must
    supply which bytes are actually there, [bi]/[blen], and that the
    addresses are in-bounds) and compared; the two extra [small]
    hypotheses on the *sums* [patPtr + iN] / [patPtr + lenN] are needed
    since [small patPtr] and [small iN] alone don't bound their sum. *)
Lemma build_lps_load_cmp : forall hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m bi blen,
  small patPtr -> small patLenN -> small lpsPtr -> small lenN -> small iN -> small tmpN ->
  small (patPtr + iN) -> small (patPtr + lenN) ->
  inst.(inst_mems) = [memaddr] ->
  lookup_N s.(s_mems) memaddr = Some m ->
  mem_lookup (Z.to_N (patPtr + iN)) m.(meminst_data) = Some bi ->
  N.lt (Z.to_N (patPtr + iN)) (operations.mem_length m) ->
  mem_lookup (Z.to_N (patPtr + lenN)) m.(meminst_data) = Some blen ->
  N.lt (Z.to_N (patPtr + lenN)) (operations.mem_length m) ->
  let f := loop_frame inst patPtr patLenN lpsPtr lenN iN tmpN in
  reduce_trans (hs, s, f, loop_load_cmp_es)
    (hs, s, f, [:: AI_basic (BI_const_num (VAL_int32 (if Integers.Byte.eq_dec bi blen then one32 else zero32)))]).
Proof.
  move=> hs s inst patPtr patLenN lpsPtr lenN iN tmpN memaddr m bi blen
    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 HaddPI HaddPL Hmems Hlkm Hlki Hbndi Hlklen Hbndlen f.
  rewrite loop_load_cmp_es_eq.
  have Hsmem : smem s inst = Some m.
  { rewrite /smem Hmems /=. rewrite Hlkm. reflexivity. }
  (* local.get 0 : patPtr *)
  have HA : reduce hs s f [:: AI_basic (BI_local_get 0%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patPtr))) (j := 0%N). reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 4%N); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_local_get 0%N); AI_basic (BI_local_get 3%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HA.
  simpl in HA'.
  (* local.get 4 : i, with patPtr kept on stack *)
  have HB : reduce hs s f [:: AI_basic (BI_local_get 4%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc iN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc iN))) (j := 4%N). reflexivity. }
  have HB' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (enc patPtr))] _ _ _ _ _
    [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_local_get 0%N); AI_basic (BI_local_get 3%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HB.
  simpl in HB'.
  (* i32.add : patPtr + i *)
  have HC : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patPtr))); AI_basic (BI_const_num (VAL_int32 (enc iN)));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (patPtr + iN))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc patPtr)) (VAL_int32 (enc iN)) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc patPtr)) (VAL_int32 (enc iN)) = Some (VAL_int32 (enc (patPtr + iN))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (add_enc patPtr iN Hp1 Hp5 HaddPI). }
    pose proof (@rs_binop_success (VAL_int32 (enc patPtr)) (VAL_int32 (enc iN)) (VAL_int32 (enc (patPtr + iN)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HC' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_local_get 0%N); AI_basic (BI_local_get 3%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HC.
  simpl in HC'.
  (* i32.load8_u : p[i] *)
  have HaddPI_N : Wasm_int.N_of_uint i32m (enc (patPtr + iN)) = Z.to_N (patPtr + iN).
  { rewrite /Wasm_int.N_of_uint /=.
    f_equal.
    apply Wasm_int.Int32.Z_mod_modulus_id.
    move: HaddPI. rewrite /small.
    have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
    rewrite Hmod. lia. }
  have [bs [Hbsload Hbsval]] := load8_u_value m (Z.to_N (patPtr + iN)) bi Hlki Hbndi.
  have HD : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (patPtr + iN))));
                              AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi))))].
  { have Hld : load_packed SX_U m (Wasm_int.N_of_uint i32m (enc (patPtr+iN))) 0%N (tp_length Tp_i8) (tnum_length T_i32) = Some bs.
    { rewrite HaddPI_N. exact Hbsload. }
    pose proof (@r_load_packed_success _ _ _ s f T_i32 Tp_i8 (enc (patPtr+iN)) (Build_memarg 0%N 0%N) m bs SX_U hs
      Hsmem Hld) as Hstep.
    rewrite Hbsval in Hstep.
    exact: Hstep. }
  have HD' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_local_get 0%N); AI_basic (BI_local_get 3%N);
     AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N));
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HD.
  simpl in HD'.
  (* local.get 0 : patPtr (again), with p[i]'s value kept on stack *)
  have HE : reduce hs s f [:: AI_basic (BI_local_get 0%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patPtr)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc patPtr))) (j := 0%N). reflexivity. }
  have HE' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi)))] _ _ _ _ _
    [:: AI_basic (BI_local_get 3%N); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N)); AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HE.
  simpl in HE'.
  (* local.get 3 : len *)
  have HF : reduce hs s f [:: AI_basic (BI_local_get 3%N)] hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc lenN)))].
  { apply r_local_get with (v := VAL_num (VAL_int32 (enc lenN))) (j := 3%N). reflexivity. }
  have HF' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi))); VAL_num (VAL_int32 (enc patPtr))]
    _ _ _ _ _ [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N)); AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HF.
  simpl in HF'.
  (* i32.add : patPtr + len *)
  have HG : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc patPtr))); AI_basic (BI_const_num (VAL_int32 (enc lenN)));
                              AI_basic (BI_binop T_i32 (Binop_i BOI_add))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (patPtr + lenN))))].
  { apply reduce_simple_reduce.
    have Htc : binop_typecheck (VAL_int32 (enc patPtr)) (VAL_int32 (enc lenN)) T_i32 (Binop_i BOI_add).
    { rewrite /binop_typecheck. done. }
    have Happ : app_binop (Binop_i BOI_add) (VAL_int32 (enc patPtr)) (VAL_int32 (enc lenN)) = Some (VAL_int32 (enc (patPtr + lenN))).
    { rewrite /app_binop /=. f_equal. f_equal. exact: (add_enc patPtr lenN Hp1 Hp4 HaddPL). }
    pose proof (@rs_binop_success (VAL_int32 (enc patPtr)) (VAL_int32 (enc lenN)) (VAL_int32 (enc (patPtr + lenN)))
      (Binop_i BOI_add) T_i32 Htc Happ) as Hstep.
    exact: Hstep. }
  have HG' := reduce_ctx _ _ _ [:: VAL_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi)))] _ _ _ _ _
    [:: AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N)); AI_basic (BI_relop T_i32 (Relop_i ROI_eq))] HG.
  simpl in HG'.
  (* i32.load8_u : p[len] *)
  have HaddPL_N : Wasm_int.N_of_uint i32m (enc (patPtr + lenN)) = Z.to_N (patPtr + lenN).
  { rewrite /Wasm_int.N_of_uint /=.
    f_equal.
    apply Wasm_int.Int32.Z_mod_modulus_id.
    move: HaddPL. rewrite /small.
    have Hmod : Wasm_int.Int32.modulus = 4294967296 by vm_compute; reflexivity.
    rewrite Hmod. lia. }
  have [bs2 [Hbsload2 Hbsval2]] := load8_u_value m (Z.to_N (patPtr + lenN)) blen Hlklen Hbndlen.
  have HH : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 (enc (patPtr + lenN))));
                              AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned blen))))].
  { have Hld2 : load_packed SX_U m (Wasm_int.N_of_uint i32m (enc (patPtr+lenN))) 0%N (tp_length Tp_i8) (tnum_length T_i32) = Some bs2.
    { rewrite HaddPL_N. exact Hbsload2. }
    pose proof (@r_load_packed_success _ _ _ s f T_i32 Tp_i8 (enc (patPtr+lenN)) (Build_memarg 0%N 0%N) m bs2 SX_U hs
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
                              AI_basic (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned blen))));
                              AI_basic (BI_relop T_i32 (Relop_i ROI_eq))]
                    hs s f [:: AI_basic (BI_const_num (VAL_int32 (if Integers.Byte.eq_dec bi blen then one32 else zero32)))].
  { apply reduce_simple_reduce.
    have Htc : relop_typecheck (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned bi)))
                 (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned blen))) T_i32 (Relop_i ROI_eq).
    { rewrite /relop_typecheck. done. }
    pose proof (@rs_relop (VAL_int32 (enc (Integers.Byte.unsigned bi))) (VAL_int32 (enc (Integers.Byte.unsigned blen)))
      T_i32 (Relop_i ROI_eq) Htc) as Hstep.
    move: Hstep. rewrite /app_relop /=.
    have Heqb : Wasm_int.Int32.eq (enc (Integers.Byte.unsigned bi)) (enc (Integers.Byte.unsigned blen))
                = (if Integers.Byte.eq_dec bi blen then true else false).
    { rewrite /Wasm_int.Int32.eq (enc_unsigned _ (Hbyte_small bi)) (enc_unsigned _ (Hbyte_small blen)).
      case: (Coqlib.zeq (Integers.Byte.unsigned bi) (Integers.Byte.unsigned blen)) => Hz;
        case: (Integers.Byte.eq_dec bi blen) => Heq; try reflexivity.
      - exfalso. apply Heq. rewrite -(Integers.Byte.repr_unsigned bi) -(Integers.Byte.repr_unsigned blen) Hz. reflexivity.
      - exfalso. apply Hz. rewrite Heq. reflexivity. }
    rewrite Heqb.
    case: (Integers.Byte.eq_dec bi blen) => Heq /=; move=> H; exact H. }
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

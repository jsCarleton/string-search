(** [kmp_search]'s init sequence ([i := 0; j := 0]), the analogue of
    [BuildLpsInit.v]'s [build_lps_init_locals] -- simpler here since,
    unlike [build_lps]'s [len := 0; i := 1], both locals are set to the
    same literal (0), and neither store touches memory. *)
From Wasm Require Import datatypes operations opsem extraction_instance memory_vec memory numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import BinNat Lia List NArith.Nnat ZArith.
Require Import KMPBytes CoreLemmas MemLemmas BuildLps Int32Facts KMPSearch KMPSearchLoop.
Import ListNotations.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope N_scope.
Open Scope Z_scope.

Lemma kmp_search_init_locals : forall hs s inst textPtr textLenN patPtr patLenN lpsPtr l5 l6,
  let f := Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                         VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                         VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 l5);
                         VAL_num (VAL_int32 l6)] inst in
  let f' := search_frame inst textPtr textLenN patPtr patLenN lpsPtr 0 0 in
  reduce_trans (hs, s, f, kmp_search_init_es) (hs, s, f', [::]).
Proof.
  move=> hs s inst textPtr textLenN patPtr patLenN lpsPtr l5 l6 f f'.
  rewrite kmp_search_init_es_eq.
  set f1 := Build_frame [VAL_num (VAL_int32 (enc textPtr)); VAL_num (VAL_int32 (enc textLenN));
                          VAL_num (VAL_int32 (enc patPtr)); VAL_num (VAL_int32 (enc patLenN));
                          VAL_num (VAL_int32 (enc lpsPtr)); VAL_num (VAL_int32 zero32);
                          VAL_num (VAL_int32 l6)] inst.
  have HA : reduce hs s f [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 5%N)]
                    hs s f1 [::].
  { pose proof (@r_local_set _ _ _ f f1 5%N (VAL_num (VAL_int32 zero32)) s (VAL_num (VAL_int32 l5)) hs) as Hstep.
    apply Hstep.
    - rewrite /f /f1 /=. reflexivity.
    - rewrite /f /=. by [].
    - rewrite /f /f1 /=. reflexivity. }
  have HA' := reduce_prefix _ _ _ _ _ _ _ _
    [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 6%N)] HA.
  have HB : reduce hs s f1 [:: AI_basic (BI_const_num (VAL_int32 zero32)); AI_basic (BI_local_set 6%N)]
                    hs s f' [::].
  { pose proof (@r_local_set _ _ _ f1 f' 6%N (VAL_num (VAL_int32 zero32)) s (VAL_num (VAL_int32 l6)) hs) as Hstep.
    apply Hstep.
    - rewrite /f1 /f' /search_frame /=. reflexivity.
    - rewrite /f1 /=. by [].
    - rewrite /f1 /f' /search_frame /=. reflexivity. }
  have Step1 := reduce_trans_step _ _ _ _ _ _ _ _ HA'.
  have Step2 := reduce_trans_step _ _ _ _ _ _ _ _ HB.
  exact: (reduce_trans_trans _ _ _ Step1 Step2).
Qed.

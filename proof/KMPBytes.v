From Wasm Require Import datatypes binary_format_parser.
Require Import Strings.Byte.
Open Scope list_scope.

(** The exact, compiled bytes of ../wasm/kmp.wasm, produced by
    [wat2wasm kmp.wat -o kmp.wasm]. Embedding the literal binary
    (rather than a hand-transcribed instruction list) means every theorem
    proved about [kmp_module] below is a theorem about the actual shipped
    artifact, not a paraphrase of it. *)
Definition kmp_wasm_bytes : list Byte.byte :=
  x00 :: x61 :: x73 :: x6d :: x01 :: x00 :: x00 :: x00 :: x01 :: x10 :: x02 :: x60 ::
  x03 :: x7f :: x7f :: x7f :: x00 :: x60 :: x05 :: x7f :: x7f :: x7f :: x7f :: x7f ::
  x01 :: x7f :: x03 :: x03 :: x02 :: x00 :: x01 :: x05 :: x03 :: x01 :: x00 :: x01 ::
  x07 :: x23 :: x03 :: x06 :: x6d :: x65 :: x6d :: x6f :: x72 :: x79 :: x02 :: x00 ::
  x09 :: x62 :: x75 :: x69 :: x6c :: x64 :: x5f :: x6c :: x70 :: x73 :: x00 :: x00 ::
  x0a :: x6b :: x6d :: x70 :: x5f :: x73 :: x65 :: x61 :: x72 :: x63 :: x68 :: x00 ::
  x01 :: x0a :: x8d :: x02 :: x02 :: x8a :: x01 :: x01 :: x03 :: x7f :: x20 :: x01 ::
  x45 :: x04 :: x40 :: x0f :: x0b :: x20 :: x02 :: x41 :: x00 :: x36 :: x02 :: x00 ::
  x41 :: x00 :: x21 :: x03 :: x41 :: x01 :: x21 :: x04 :: x02 :: x40 :: x03 :: x40 ::
  x20 :: x04 :: x20 :: x01 :: x4e :: x0d :: x01 :: x20 :: x00 :: x20 :: x04 :: x6a ::
  x2d :: x00 :: x00 :: x20 :: x00 :: x20 :: x03 :: x6a :: x2d :: x00 :: x00 :: x46 ::
  x04 :: x40 :: x20 :: x03 :: x41 :: x01 :: x6a :: x21 :: x03 :: x20 :: x02 :: x20 ::
  x04 :: x41 :: x02 :: x74 :: x6a :: x20 :: x03 :: x36 :: x02 :: x00 :: x20 :: x04 ::
  x41 :: x01 :: x6a :: x21 :: x04 :: x05 :: x20 :: x03 :: x41 :: x00 :: x47 :: x04 ::
  x40 :: x20 :: x02 :: x20 :: x03 :: x41 :: x01 :: x6b :: x41 :: x02 :: x74 :: x6a ::
  x28 :: x02 :: x00 :: x21 :: x05 :: x20 :: x05 :: x21 :: x03 :: x05 :: x20 :: x02 ::
  x20 :: x04 :: x41 :: x02 :: x74 :: x6a :: x41 :: x00 :: x36 :: x02 :: x00 :: x20 ::
  x04 :: x41 :: x01 :: x6a :: x21 :: x04 :: x0b :: x0b :: x0c :: x00 :: x0b :: x0b ::
  x0b :: x7f :: x01 :: x02 :: x7f :: x20 :: x03 :: x45 :: x04 :: x40 :: x41 :: x00 ::
  x0f :: x0b :: x20 :: x02 :: x20 :: x03 :: x20 :: x04 :: x10 :: x00 :: x41 :: x00 ::
  x21 :: x05 :: x41 :: x00 :: x21 :: x06 :: x02 :: x40 :: x03 :: x40 :: x20 :: x05 ::
  x20 :: x01 :: x4e :: x0d :: x01 :: x20 :: x00 :: x20 :: x05 :: x6a :: x2d :: x00 ::
  x00 :: x20 :: x02 :: x20 :: x06 :: x6a :: x2d :: x00 :: x00 :: x46 :: x04 :: x40 ::
  x20 :: x05 :: x41 :: x01 :: x6a :: x21 :: x05 :: x20 :: x06 :: x41 :: x01 :: x6a ::
  x21 :: x06 :: x20 :: x06 :: x20 :: x03 :: x46 :: x04 :: x40 :: x20 :: x05 :: x20 ::
  x06 :: x6b :: x0f :: x0b :: x05 :: x20 :: x06 :: x41 :: x00 :: x47 :: x04 :: x40 ::
  x20 :: x04 :: x20 :: x06 :: x41 :: x01 :: x6b :: x41 :: x02 :: x74 :: x6a :: x28 ::
  x02 :: x00 :: x21 :: x06 :: x05 :: x20 :: x05 :: x41 :: x01 :: x6a :: x21 :: x05 ::
  x0b :: x0b :: x0c :: x00 :: x0b :: x0b :: x41 :: x7f :: x0b ::
  nil.

Definition kmp_module_opt : option module := run_parse_module kmp_wasm_bytes.

(* Sanity check: the embedded bytes are well-formed and parse successfully. *)
Lemma kmp_module_parses : exists m, kmp_module_opt = Some m.
Proof. eexists. vm_compute. reflexivity. Qed.

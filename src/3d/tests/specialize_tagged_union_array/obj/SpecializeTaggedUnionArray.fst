module SpecializeTaggedUnionArray
open EverParse3d.Prelude
open EverParse3d.Actions.All
open EverParse3d.Interpreter
open SpecializeTaggedUnionArray.ExternalAPI
module T = FStar.Tactics
module A = EverParse3d.Actions.All
module P = EverParse3d.Prelude
#set-options "--fuel 0 --ifuel 0 --ext optimize_let_vc"

[@@ specialize; noextract_to "krml"]
noextract
let def__PAYLOAD_0 =
  ((T_dep_pair_with_refinement "f0"
        (DT_IType UInt32)
        (fun f0 ->
            ((((f0 = (EverParse3d.Prelude.uint8_to_uint32 0uy)) ||
                  (f0 = (EverParse3d.Prelude.uint8_to_uint32 2uy))) ||
                (f0 = (EverParse3d.Prelude.uint8_to_uint32 4uy))) ||
              (f0 = (EverParse3d.Prelude.uint8_to_uint32 6uy))))
        (fun f0 ->
            (T_pair "___alignment_padding_0"
                true
                (T_with_comment "___alignment_padding_0"
                    (T_nlist "___alignment_padding_0"
                        4ul
                        (Some 4)
                        true
                        (T_denoted "___alignment_padding_0.element" (DT_IType UInt8)))
                    "Validating field ___alignment_padding_0")
                true
                (T_with_comment "ptr" (T_denoted "ptr" (DT_IType UInt64)) "Validating field ptr"))))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__PAYLOAD_0:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    (and_then_kind (filter_kind kind____UINT32)
        (and_then_kind (kind_nlist kind____UINT8 (Some 4)) kind____UINT64))

[@@ specialize; noextract_to "krml"]
noextract
let def'__PAYLOAD_0:typ kind__PAYLOAD_0 Trivial Trivial Trivial false false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ -> (coerce_validator [`%kind__PAYLOAD_0])))
    (def__PAYLOAD_0)

[@@ noextract_to "krml"]
noextract
let type__PAYLOAD_0 = (as_type (def'__PAYLOAD_0))

[@@ noextract_to "krml"]
noextract
let parser__PAYLOAD_0 = (as_parser (def'__PAYLOAD_0))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate__PAYLOAD_0 = as_validator "_PAYLOAD_0" (def'__PAYLOAD_0)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__PAYLOAD_0:dtyp kind__PAYLOAD_0 false false Trivial Trivial Trivial =
  mk_dtyp_app kind__PAYLOAD_0 Trivial Trivial Trivial (type__PAYLOAD_0)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__PAYLOAD_0]];
                  T.trefl ())))
        (parser__PAYLOAD_0)) None false false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser__PAYLOAD_0; `%type__PAYLOAD_0; `%coerce]];
                  T.trefl ())))
        (validate__PAYLOAD_0))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ normalize_for_extraction specialization_steps]
let copy_bytes (numbytes: (___UINT64)) =
  probe_action_as_probe_m <| (Probe_action_atomic (Atomic_probe_and_copy numbytes ___ProbeAndCopy))

[@@ normalize_for_extraction specialization_steps]
let skip_bytes_write (numbytes: (___UINT64)) =
  probe_action_as_probe_m <| (Probe_action_atomic (Atomic_probe_skip_write numbytes))

[@@ normalize_for_extraction specialization_steps]
let skip_bytes_read (numbytes: (___UINT64)) =
  probe_action_as_probe_m <| (Probe_action_atomic (Atomic_probe_skip_read numbytes))

[@@ normalize_for_extraction specialization_steps]
let read_and_coerce_pointer (fieldname: (string)) =
  probe_action_as_probe_m <|
  (Probe_action_let fieldname
      (Atomic_probe_and_read ___ProbeAndReadU32)
      (fun ptr32 ->
          (Probe_action_let fieldname
              (Atomic_probe_call_pure (___UlongToPtr ptr32))
              (fun ptr64 -> (Probe_action_atomic (Atomic_probe_write_at_offset ptr64 ___WriteU64))))
      ))

[@@ normalize_for_extraction specialization_steps]
let ___specialized32____probe_PAYLOAD_0 =
  probe_action_as_probe_m <|
  (Probe_action_seq "f0"
      (Probe_action_var (copy_bytes 4uL))
      (Probe_action_seq "alignment"
          (Probe_action_var (skip_bytes_write 4uL))
          (Probe_action_seq "ptr"
              (Probe_action_var (read_and_coerce_pointer "ptr"))
              (Probe_action_atomic (Atomic_probe_return ())))))

[@@ specialize; noextract_to "krml"]
noextract
let def__PAYLOAD_DEFAULT =
  ((T_with_comment "ptr1" (T_denoted "ptr1" (DT_IType UInt64)) "Validating field ptr1")
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__PAYLOAD_DEFAULT:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    kind____UINT64

[@@ specialize; noextract_to "krml"]
noextract
let def'__PAYLOAD_DEFAULT:typ kind__PAYLOAD_DEFAULT Trivial Trivial Trivial false true =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (coerce_validator [`%kind__PAYLOAD_DEFAULT])))
    (def__PAYLOAD_DEFAULT)

[@@ noextract_to "krml"]
noextract
let type__PAYLOAD_DEFAULT = (as_type (def'__PAYLOAD_DEFAULT))

[@@ noextract_to "krml"]
noextract
let parser__PAYLOAD_DEFAULT = (as_parser (def'__PAYLOAD_DEFAULT))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate__PAYLOAD_DEFAULT = as_validator "_PAYLOAD_DEFAULT" (def'__PAYLOAD_DEFAULT)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__PAYLOAD_DEFAULT:dtyp kind__PAYLOAD_DEFAULT false true Trivial Trivial Trivial =
  mk_dtyp_app kind__PAYLOAD_DEFAULT Trivial Trivial Trivial (type__PAYLOAD_DEFAULT)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__PAYLOAD_DEFAULT]];
                  T.trefl ())))
        (parser__PAYLOAD_DEFAULT)) (Some (as_reader (def__PAYLOAD_DEFAULT))) false true
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser__PAYLOAD_DEFAULT; `%type__PAYLOAD_DEFAULT; `%coerce]];
                  T.trefl ())))
        (validate__PAYLOAD_DEFAULT))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ normalize_for_extraction specialization_steps]
let ___specialized32____probe_PAYLOAD_DEFAULT =
  probe_action_as_probe_m <|
  (Probe_action_seq "ptr1"
      (Probe_action_var (read_and_coerce_pointer "ptr1"))
      (Probe_action_atomic (Atomic_probe_return ())))

[@@ specialize; noextract_to "krml"]
noextract
let def__PAYLOAD (___Tag: (___UINT64)) =
  ((T_cases (___Tag = (EverParse3d.Prelude.uint8_to_uint64 0uy))
        (T_with_comment "p0" (T_denoted "p0" (dtyp__PAYLOAD_0)) "Validating field p0")
        (T_pair "pdef"
            true
            (T_with_comment "pdef" (T_denoted "pdef" (DT_IType UInt64)) "Validating field pdef")
            true
            (T_with_comment "___alignment_padding_1"
                (T_nlist "___alignment_padding_1"
                    8ul
                    (Some 8)
                    true
                    (T_denoted "___alignment_padding_1.element" (DT_IType UInt8)))
                "Validating field ___alignment_padding_1")))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__PAYLOAD:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    (glb kind__PAYLOAD_0 (and_then_kind kind____UINT64 (kind_nlist kind____UINT8 (Some 8))))

[@@ specialize; noextract_to "krml"]
noextract
let def'__PAYLOAD (___Tag: (___UINT64)) : typ kind__PAYLOAD Trivial Trivial Trivial false false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ -> (coerce_validator [`%kind__PAYLOAD])))
    (def__PAYLOAD ___Tag)

[@@ noextract_to "krml"]
noextract
let type__PAYLOAD (___Tag: (___UINT64)) = (as_type (def'__PAYLOAD ___Tag))

[@@ noextract_to "krml"]
noextract
let parser__PAYLOAD (___Tag: (___UINT64)) = (as_parser (def'__PAYLOAD ___Tag))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate__PAYLOAD (___Tag: (___UINT64)) = as_validator "_PAYLOAD" (def'__PAYLOAD ___Tag)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__PAYLOAD (___Tag: (___UINT64)) : dtyp kind__PAYLOAD false false Trivial Trivial Trivial =
  mk_dtyp_app kind__PAYLOAD Trivial Trivial Trivial (type__PAYLOAD ___Tag)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__PAYLOAD]];
                  T.trefl ())))
        (parser__PAYLOAD ___Tag)) None false false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser__PAYLOAD; `%type__PAYLOAD; `%coerce]];
                  T.trefl ())))
        (validate__PAYLOAD ___Tag))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ normalize_for_extraction specialization_steps]
let ___specialized32____probe_PAYLOAD (___Tag: (___UINT64)) =
  probe_action_as_probe_m <|
  (Probe_action_ite (___Tag = (EverParse3d.Prelude.uint8_to_uint64 0uy))
      (Probe_action_seq "p0"
          (Probe_action_var ___specialized32____probe_PAYLOAD_0)
          (Probe_action_atomic (Atomic_probe_return ())))
      (Probe_action_seq "__union_case_"
          (Probe_action_seq "pdef"
              (Probe_action_var ___specialized32____probe_PAYLOAD_DEFAULT)
              (Probe_action_seq "alignment"
                  (Probe_action_var (skip_bytes_read 4uL))
                  (Probe_action_seq "alignment"
                      (Probe_action_var (skip_bytes_write 8uL))
                      (Probe_action_atomic (Atomic_probe_return ())))))
          (Probe_action_atomic (Atomic_probe_return ()))))

[@@ specialize; noextract_to "krml"]
noextract
let def__WRAPPER =
  ((T_dep_pair "Tag"
        (DT_IType UInt64)
        (fun ___Tag ->
            (T_with_comment "payload"
                (T_denoted "payload" (dtyp__PAYLOAD ___Tag))
                "Validating field payload")))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__WRAPPER:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    (and_then_kind kind____UINT64 kind__PAYLOAD)

[@@ specialize; noextract_to "krml"]
noextract
let def'__WRAPPER:typ kind__WRAPPER Trivial Trivial Trivial false false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ -> (coerce_validator [`%kind__WRAPPER])))
    (def__WRAPPER)

[@@ noextract_to "krml"]
noextract
let type__WRAPPER = (as_type (def'__WRAPPER))

[@@ noextract_to "krml"]
noextract
let parser__WRAPPER = (as_parser (def'__WRAPPER))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate__WRAPPER = as_validator "_WRAPPER" (def'__WRAPPER)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__WRAPPER:dtyp kind__WRAPPER false false Trivial Trivial Trivial =
  mk_dtyp_app kind__WRAPPER Trivial Trivial Trivial (type__WRAPPER)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__WRAPPER]];
                  T.trefl ())))
        (parser__WRAPPER)) None false false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser__WRAPPER; `%type__WRAPPER; `%coerce]];
                  T.trefl ())))
        (validate__WRAPPER))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ normalize_for_extraction specialization_steps]
let ___specialized32____probe_WRAPPER =
  probe_action_as_probe_m <|
  (Probe_action_let "Tag"
      (Atomic_probe_and_read ___ProbeAndReadU64)
      (fun ___Tag ->
          (Probe_action_seq "Tag"
              (Probe_action_atomic (Atomic_probe_write_at_offset ___Tag ___WriteU64))
              (Probe_action_seq "payload"
                  (Probe_action_var (___specialized32____probe_PAYLOAD ___Tag))
                  (Probe_action_atomic (Atomic_probe_return ()))))))

[@@ specialize; noextract_to "krml"]
noextract
let def__WRAPPER_ARRAY (___Count: (___UINT16)) =
  ((T_with_comment "Chunks"
        (T_nlist "Chunks"
            (EverParse3d.Prelude.u32_mul (FStar.Range.mk_range "src/SpecializeTaggedUnionArray.3d"
                    49
                    30
                    49
                    30)
                24ul
                (EverParse3d.Prelude.uint16_to_uint32 ___Count))
            None
            true
            (T_denoted "Chunks.element" (dtyp__WRAPPER)))
        "Validating field Chunks")
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__WRAPPER_ARRAY:P.parser_kind false WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    (kind_nlist kind__WRAPPER None)

[@@ specialize; noextract_to "krml"]
noextract
let def'__WRAPPER_ARRAY (___Count: (___UINT16))
    : typ kind__WRAPPER_ARRAY Trivial Trivial Trivial false false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ -> (coerce_validator [`%kind__WRAPPER_ARRAY]))
    )
    (def__WRAPPER_ARRAY ___Count)

[@@ noextract_to "krml"]
noextract
let type__WRAPPER_ARRAY (___Count: (___UINT16)) = (as_type (def'__WRAPPER_ARRAY ___Count))

[@@ noextract_to "krml"]
noextract
let parser__WRAPPER_ARRAY (___Count: (___UINT16)) = (as_parser (def'__WRAPPER_ARRAY ___Count))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate__WRAPPER_ARRAY (___Count: (___UINT16)) =
  as_validator "_WRAPPER_ARRAY" (def'__WRAPPER_ARRAY ___Count)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__WRAPPER_ARRAY (___Count: (___UINT16))
    : dtyp kind__WRAPPER_ARRAY false false Trivial Trivial Trivial =
  mk_dtyp_app kind__WRAPPER_ARRAY Trivial Trivial Trivial (type__WRAPPER_ARRAY ___Count)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__WRAPPER_ARRAY]];
                  T.trefl ())))
        (parser__WRAPPER_ARRAY ___Count)) None false false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser__WRAPPER_ARRAY; `%type__WRAPPER_ARRAY; `%coerce]];
                  T.trefl ())))
        (validate__WRAPPER_ARRAY ___Count))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ normalize_for_extraction specialization_steps]
let ___specialized32____probe_WRAPPER_ARRAY (___Count: (___UINT16)) =
  probe_action_as_probe_m <|
  (Probe_action_array
      (EverParse3d.Prelude.uint32_to_uint64 (EverParse3d.Prelude.u32_mul (FStar.Range.mk_range "src/SpecializeTaggedUnionArray.3d"
                  49
                  30
                  49
                  30)
              16ul
              (EverParse3d.Prelude.uint16_to_uint32 ___Count)))
      (Probe_action_seq "Chunks"
          (Probe_action_var ___specialized32____probe_WRAPPER)
          (Probe_action_atomic (Atomic_probe_return ()))))

[@@ specialize; noextract_to "krml"]
noextract
let def__WRAPPER_64
      (___probe_Chunks: ((___UINT16) -> (probe_m_unit)))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
     =
  ((t_probe_then_validate UInt64
        false
        "Chunks"
        ___ProbeInit
        (EverParse3d.Prelude.uint32_to_uint64 (EverParse3d.Prelude.u32_mul (FStar.Range.mk_range "src/SpecializeTaggedUnionArray.3d"
                    55
                    16
                    55
                    16)
                24ul
                (EverParse3d.Prelude.uint16_to_uint32 ___Count)))
        (___probe_Chunks ___Count)
        ___Out
        as_u64_identity
        (dtyp__WRAPPER_ARRAY ___Count))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__WRAPPER_64:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    kind____UINT64

[@@ specialize; noextract_to "krml"]
noextract
let def'__WRAPPER_64
      (___probe_Chunks: ((___UINT16) -> (probe_m_unit)))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
    : typ kind__WRAPPER_64
      (NonTrivial (A.copy_buffer_inv ___Out))
      Trivial
      (NonTrivial (A.copy_buffer_loc ___Out))
      true
      false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ -> (coerce_validator [`%kind__WRAPPER_64])))
    (def__WRAPPER_64 ___probe_Chunks ___Count ___Out)

[@@ noextract_to "krml"]
noextract
let type__WRAPPER_64
      (___probe_Chunks: ((___UINT16) -> (probe_m_unit)))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
     = (as_type (def'__WRAPPER_64 ___probe_Chunks ___Count ___Out))

[@@ noextract_to "krml"]
noextract
let parser__WRAPPER_64
      (___probe_Chunks: ((___UINT16) -> (probe_m_unit)))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
     = (as_parser (def'__WRAPPER_64 ___probe_Chunks ___Count ___Out))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate__WRAPPER_64
      (___probe_Chunks: ((___UINT16) -> (probe_m_unit)))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
     = as_validator "_WRAPPER_64" (def'__WRAPPER_64 ___probe_Chunks ___Count ___Out)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__WRAPPER_64
      (___probe_Chunks: ((___UINT16) -> (probe_m_unit)))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
    : dtyp kind__WRAPPER_64
      true
      false
      (NonTrivial (A.copy_buffer_inv ___Out))
      Trivial
      (NonTrivial (A.copy_buffer_loc ___Out)) =
  mk_dtyp_app kind__WRAPPER_64 (NonTrivial (A.copy_buffer_inv ___Out)) Trivial
    (NonTrivial (A.copy_buffer_loc ___Out)) (type__WRAPPER_64 ___probe_Chunks ___Count ___Out)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__WRAPPER_64]];
                  T.trefl ())))
        (parser__WRAPPER_64 ___probe_Chunks ___Count ___Out)) None true false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser__WRAPPER_64; `%type__WRAPPER_64; `%coerce]];
                  T.trefl ())))
        (validate__WRAPPER_64 ___probe_Chunks ___Count ___Out))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ specialize; noextract_to "krml"]
noextract
let def____specialized_WRAPPER_32 (___Count: (___UINT16)) (___Out: (___EVERPARSE_COPY_BUFFER_T)) =
  ((t_probe_then_validate UInt64
        false
        "Chunks"
        ___ProbeInit
        (EverParse3d.Prelude.uint32_to_uint64 (EverParse3d.Prelude.u32_mul (FStar.Range.mk_range "src/SpecializeTaggedUnionArray.3d"
                    55
                    16
                    55
                    16)
                24ul
                (EverParse3d.Prelude.uint16_to_uint32 ___Count)))
        (___specialized32____probe_WRAPPER_ARRAY ___Count)
        ___Out
        as_u64_identity
        (dtyp__WRAPPER_ARRAY ___Count))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind____specialized_WRAPPER_32:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    kind____UINT64

[@@ specialize; noextract_to "krml"]
noextract
let def'____specialized_WRAPPER_32 (___Count: (___UINT16)) (___Out: (___EVERPARSE_COPY_BUFFER_T))
    : typ kind____specialized_WRAPPER_32
      (NonTrivial (A.copy_buffer_inv ___Out))
      Trivial
      (NonTrivial (A.copy_buffer_loc ___Out))
      true
      false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (coerce_validator [`%kind____specialized_WRAPPER_32])))
    (def____specialized_WRAPPER_32 ___Count ___Out)

[@@ noextract_to "krml"]
noextract
let type____specialized_WRAPPER_32 (___Count: (___UINT16)) (___Out: (___EVERPARSE_COPY_BUFFER_T)) =
  (as_type (def'____specialized_WRAPPER_32 ___Count ___Out))

[@@ noextract_to "krml"]
noextract
let parser____specialized_WRAPPER_32 (___Count: (___UINT16)) (___Out: (___EVERPARSE_COPY_BUFFER_T)) =
  (as_parser (def'____specialized_WRAPPER_32 ___Count ___Out))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate____specialized_WRAPPER_32
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
     = as_validator "___specialized_WRAPPER_32" (def'____specialized_WRAPPER_32 ___Count ___Out)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp____specialized_WRAPPER_32 (___Count: (___UINT16)) (___Out: (___EVERPARSE_COPY_BUFFER_T))
    : dtyp kind____specialized_WRAPPER_32
      true
      false
      (NonTrivial (A.copy_buffer_inv ___Out))
      Trivial
      (NonTrivial (A.copy_buffer_loc ___Out)) =
  mk_dtyp_app kind____specialized_WRAPPER_32 (NonTrivial (A.copy_buffer_inv ___Out)) Trivial
    (NonTrivial (A.copy_buffer_loc ___Out)) (type____specialized_WRAPPER_32 ___Count ___Out)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type____specialized_WRAPPER_32]];
                  T.trefl ())))
        (parser____specialized_WRAPPER_32 ___Count ___Out)) None true false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [
                      delta_only [
                          `%parser____specialized_WRAPPER_32;
                          `%type____specialized_WRAPPER_32;
                          `%coerce
                        ]
                    ];
                  T.trefl ())))
        (validate____specialized_WRAPPER_32 ___Count ___Out))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ normalize_for_extraction specialization_steps]
let ___MAIN____probe__WRAPPER_64_0_WRAPPER_ARRAY (____arg0: (___UINT16)) =
  probe_action_as_probe_m <| (Probe_action_copy_init_sz ___ProbeAndCopy)

[@@ specialize; noextract_to "krml"]
noextract
let def__MAIN
      (___Requestor32: (___Bool))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
     =
  ((T_drop
      (T_cases ___Requestor32
          (T_with_comment "w32"
              (T_denoted "w32" (dtyp____specialized_WRAPPER_32 ___Count ___Out))
              "Validating field w32")
          (T_with_comment "w64"
              (T_denoted "w64"
                  (dtyp__WRAPPER_64 ___MAIN____probe__WRAPPER_64_0_WRAPPER_ARRAY ___Count ___Out))
              "Validating field w64")))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__MAIN:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    (glb kind____specialized_WRAPPER_32 kind__WRAPPER_64)

[@@ specialize; noextract_to "krml"]
noextract
let def'__MAIN
      (___Requestor32: (___Bool))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
    : typ kind__MAIN
      (NonTrivial (A.conj_inv (A.copy_buffer_inv ___Out) (A.copy_buffer_inv ___Out)))
      Trivial
      (NonTrivial (A.eloc_union (A.copy_buffer_loc ___Out) (A.copy_buffer_loc ___Out)))
      true
      false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ -> (coerce_validator [`%kind__MAIN])))
    (def__MAIN ___Requestor32 ___Count ___Out)

[@@ noextract_to "krml"]
noextract
let type__MAIN
      (___Requestor32: (___Bool))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
     = (as_type (def'__MAIN ___Requestor32 ___Count ___Out))

[@@ noextract_to "krml"]
noextract
let parser__MAIN
      (___Requestor32: (___Bool))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
     = (as_parser (def'__MAIN ___Requestor32 ___Count ___Out))
[@@ normalize_for_extraction specialization_steps]
let validate__MAIN
      (___Requestor32: (___Bool))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
     = as_validator "_MAIN" (def'__MAIN ___Requestor32 ___Count ___Out)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__MAIN
      (___Requestor32: (___Bool))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
    : dtyp kind__MAIN
      true
      false
      (NonTrivial (A.conj_inv (A.copy_buffer_inv ___Out) (A.copy_buffer_inv ___Out)))
      Trivial
      (NonTrivial (A.eloc_union (A.copy_buffer_loc ___Out) (A.copy_buffer_loc ___Out))) =
  mk_dtyp_app kind__MAIN
    (NonTrivial (A.conj_inv (A.copy_buffer_inv ___Out) (A.copy_buffer_inv ___Out))) Trivial
    (NonTrivial (A.eloc_union (A.copy_buffer_loc ___Out) (A.copy_buffer_loc ___Out)))
    (type__MAIN ___Requestor32 ___Count ___Out)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__MAIN]];
                  T.trefl ())))
        (parser__MAIN ___Requestor32 ___Count ___Out)) None true false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser__MAIN; `%type__MAIN; `%coerce]];
                  T.trefl ())))
        (validate__MAIN ___Requestor32 ___Count ___Out))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))


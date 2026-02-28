module SpecializeVLArray
open EverParse3d.Prelude
open EverParse3d.Actions.All
open EverParse3d.Interpreter
open SpecializeVLArray.ExternalAPI
module T = FStar.Tactics
module A = EverParse3d.Actions.All
module P = EverParse3d.Prelude
#set-options "--fuel 0 --ifuel 0 --ext optimize_let_vc"

[@@ specialize; noextract_to "krml"]
noextract
let def____USHORT =
  ((T_denoted "missing" (DT_IType UInt16))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind____USHORT:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    kind____UINT16

[@@ specialize; noextract_to "krml"]
noextract
let def'____USHORT:typ kind____USHORT Trivial Trivial Trivial false true =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ -> (coerce_validator [`%kind____USHORT])))
    (def____USHORT)

[@@ noextract_to "krml"]
noextract
let type____USHORT = (as_type (def'____USHORT))

[@@ noextract_to "krml"]
noextract
let parser____USHORT = (as_parser (def'____USHORT))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate____USHORT = as_validator "___USHORT" (def'____USHORT)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp____USHORT:dtyp kind____USHORT false true Trivial Trivial Trivial =
  mk_dtyp_app kind____USHORT Trivial Trivial Trivial (type____USHORT)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type____USHORT]];
                  T.trefl ())))
        (parser____USHORT)) (Some (as_reader (def____USHORT))) false true
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser____USHORT; `%type____USHORT; `%coerce]];
                  T.trefl ())))
        (validate____USHORT))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ specialize; noextract_to "krml"]
noextract
let def____UNINTERPRETED =
  ((T_denoted "missing" (DT_IType UInt8))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind____UNINTERPRETED:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    kind____UINT8

[@@ specialize; noextract_to "krml"]
noextract
let def'____UNINTERPRETED:typ kind____UNINTERPRETED Trivial Trivial Trivial false true =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (coerce_validator [`%kind____UNINTERPRETED])))
    (def____UNINTERPRETED)

[@@ noextract_to "krml"]
noextract
let type____UNINTERPRETED = (as_type (def'____UNINTERPRETED))

[@@ noextract_to "krml"]
noextract
let parser____UNINTERPRETED = (as_parser (def'____UNINTERPRETED))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate____UNINTERPRETED = as_validator "___UNINTERPRETED" (def'____UNINTERPRETED)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp____UNINTERPRETED:dtyp kind____UNINTERPRETED false true Trivial Trivial Trivial =
  mk_dtyp_app kind____UNINTERPRETED Trivial Trivial Trivial (type____UNINTERPRETED)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type____UNINTERPRETED]];
                  T.trefl ())))
        (parser____UNINTERPRETED)) (Some (as_reader (def____UNINTERPRETED))) false true
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser____UNINTERPRETED; `%type____UNINTERPRETED; `%coerce]];
                  T.trefl ())))
        (validate____UNINTERPRETED))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ specialize; noextract_to "krml"]
noextract
let def__UNKNOWN_HEADER_64 =
  ((T_pair "NameLength"
        true
        (T_with_comment "NameLength"
            (T_denoted "NameLength" (DT_IType UInt16))
            "Validating field NameLength")
        true
        (T_pair "RawValueLength"
            true
            (T_with_comment "RawValueLength"
                (T_denoted "RawValueLength" (DT_IType UInt16))
                "Validating field RawValueLength")
            true
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
                (T_pair "pName"
                    true
                    (T_with_comment "pName"
                        (T_denoted "pName" (DT_IType UInt64))
                        "Validating field pName")
                    true
                    (T_with_comment "pRawValue"
                        (T_denoted "pRawValue" (DT_IType UInt64))
                        "Validating field pRawValue")))))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__UNKNOWN_HEADER_64:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    (and_then_kind kind____UINT16
        (and_then_kind kind____UINT16
            (and_then_kind (kind_nlist kind____UINT8 (Some 4))
                (and_then_kind kind____UINT64 kind____UINT64))))

[@@ specialize; noextract_to "krml"]
noextract
let def'__UNKNOWN_HEADER_64:typ kind__UNKNOWN_HEADER_64 Trivial Trivial Trivial false false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (coerce_validator [`%kind__UNKNOWN_HEADER_64])))
    (def__UNKNOWN_HEADER_64)

[@@ noextract_to "krml"]
noextract
let type__UNKNOWN_HEADER_64 = (as_type (def'__UNKNOWN_HEADER_64))

[@@ noextract_to "krml"]
noextract
let parser__UNKNOWN_HEADER_64 = (as_parser (def'__UNKNOWN_HEADER_64))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate__UNKNOWN_HEADER_64 = as_validator "_UNKNOWN_HEADER_64" (def'__UNKNOWN_HEADER_64)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__UNKNOWN_HEADER_64:dtyp kind__UNKNOWN_HEADER_64 false false Trivial Trivial Trivial =
  mk_dtyp_app kind__UNKNOWN_HEADER_64 Trivial Trivial Trivial (type__UNKNOWN_HEADER_64)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__UNKNOWN_HEADER_64]];
                  T.trefl ())))
        (parser__UNKNOWN_HEADER_64)) None false false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [
                      delta_only [`%parser__UNKNOWN_HEADER_64; `%type__UNKNOWN_HEADER_64; `%coerce]
                    ];
                  T.trefl ())))
        (validate__UNKNOWN_HEADER_64))
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
let ___specialized32____probe_UNKNOWN_HEADER_64 =
  probe_action_as_probe_m <|
  (Probe_action_seq "NameLength"
      (Probe_action_var (copy_bytes 4uL))
      (Probe_action_seq "alignment"
          (Probe_action_var (skip_bytes_write 4uL))
          (Probe_action_seq "pName"
              (Probe_action_var (read_and_coerce_pointer "pName"))
              (Probe_action_seq "pRawValue"
                  (Probe_action_var (read_and_coerce_pointer "pRawValue"))
                  (Probe_action_atomic (Atomic_probe_return ()))))))

[@@ specialize; noextract_to "krml"]
noextract
let def__UNKNOWN_HEADERS_INTERNAL_64 (___UnknownHeaderCount: (___UINT16)) =
  ((T_with_comment "UnknownHeaders"
        (T_nlist "UnknownHeaders"
            (EverParse3d.Prelude.u32_mul (FStar.Range.mk_range "src/SpecializeVLArray.3d"
                    23
                    45
                    23
                    45)
                24ul
                (EverParse3d.Prelude.uint16_to_uint32 ___UnknownHeaderCount))
            None
            true
            (T_denoted "UnknownHeaders.element" (dtyp__UNKNOWN_HEADER_64)))
        "Validating field UnknownHeaders")
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__UNKNOWN_HEADERS_INTERNAL_64:P.parser_kind false WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    (kind_nlist kind__UNKNOWN_HEADER_64 None)

[@@ specialize; noextract_to "krml"]
noextract
let def'__UNKNOWN_HEADERS_INTERNAL_64 (___UnknownHeaderCount: (___UINT16))
    : typ kind__UNKNOWN_HEADERS_INTERNAL_64 Trivial Trivial Trivial false false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (coerce_validator [`%kind__UNKNOWN_HEADERS_INTERNAL_64])))
    (def__UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount)

[@@ noextract_to "krml"]
noextract
let type__UNKNOWN_HEADERS_INTERNAL_64 (___UnknownHeaderCount: (___UINT16)) =
  (as_type (def'__UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount))

[@@ noextract_to "krml"]
noextract
let parser__UNKNOWN_HEADERS_INTERNAL_64 (___UnknownHeaderCount: (___UINT16)) =
  (as_parser (def'__UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate__UNKNOWN_HEADERS_INTERNAL_64 (___UnknownHeaderCount: (___UINT16)) =
  as_validator "_UNKNOWN_HEADERS_INTERNAL_64"
    (def'__UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__UNKNOWN_HEADERS_INTERNAL_64 (___UnknownHeaderCount: (___UINT16))
    : dtyp kind__UNKNOWN_HEADERS_INTERNAL_64 false false Trivial Trivial Trivial =
  mk_dtyp_app kind__UNKNOWN_HEADERS_INTERNAL_64 Trivial Trivial Trivial
    (type__UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__UNKNOWN_HEADERS_INTERNAL_64]];
                  T.trefl ())))
        (parser__UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount)) None false false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [
                      delta_only [
                          `%parser__UNKNOWN_HEADERS_INTERNAL_64;
                          `%type__UNKNOWN_HEADERS_INTERNAL_64;
                          `%coerce
                        ]
                    ];
                  T.trefl ())))
        (validate__UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ normalize_for_extraction specialization_steps]
let ___specialized32____probe_UNKNOWN_HEADERS_INTERNAL_64 (___UnknownHeaderCount: (___UINT16)) =
  probe_action_as_probe_m <|
  (Probe_action_array
      (EverParse3d.Prelude.uint32_to_uint64 (EverParse3d.Prelude.u32_mul (FStar.Range.mk_range "src/SpecializeVLArray.3d"
                  23
                  45
                  23
                  45)
              12ul
              (EverParse3d.Prelude.uint16_to_uint32 ___UnknownHeaderCount)))
      (Probe_action_seq "UnknownHeaders"
          (Probe_action_var ___specialized32____probe_UNKNOWN_HEADER_64)
          (Probe_action_atomic (Atomic_probe_return ()))))

[@@ specialize; noextract_to "krml"]
noextract
let def__UNKNOWN_HEADERS_64
      (___probe_pUnknownHeaders: ((___UINT16) -> (probe_m_unit)))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  ((t_probe_then_validate UInt64
        false
        "pUnknownHeaders"
        ___ProbeInit
        (EverParse3d.Prelude.uint32_to_uint64 (EverParse3d.Prelude.u32_mul (FStar.Range.mk_range "src/SpecializeVLArray.3d"
                    33
                    35
                    33
                    35)
                24ul
                (EverParse3d.Prelude.uint16_to_uint32 ___UnknownHeaderCount)))
        (___probe_pUnknownHeaders ___UnknownHeaderCount)
        ___UnknownHeaderProbe
        as_u64_identity
        (dtyp__UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__UNKNOWN_HEADERS_64:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    kind____UINT64

[@@ specialize; noextract_to "krml"]
noextract
let def'__UNKNOWN_HEADERS_64
      (___probe_pUnknownHeaders: ((___UINT16) -> (probe_m_unit)))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
    : typ kind__UNKNOWN_HEADERS_64
      (NonTrivial (A.copy_buffer_inv ___UnknownHeaderProbe))
      Trivial
      (NonTrivial (A.copy_buffer_loc ___UnknownHeaderProbe))
      true
      false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (coerce_validator [`%kind__UNKNOWN_HEADERS_64])))
    (def__UNKNOWN_HEADERS_64 ___probe_pUnknownHeaders ___UnknownHeaderCount ___UnknownHeaderProbe)

[@@ noextract_to "krml"]
noextract
let type__UNKNOWN_HEADERS_64
      (___probe_pUnknownHeaders: ((___UINT16) -> (probe_m_unit)))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  (as_type (def'__UNKNOWN_HEADERS_64 ___probe_pUnknownHeaders
          ___UnknownHeaderCount
          ___UnknownHeaderProbe))

[@@ noextract_to "krml"]
noextract
let parser__UNKNOWN_HEADERS_64
      (___probe_pUnknownHeaders: ((___UINT16) -> (probe_m_unit)))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  (as_parser (def'__UNKNOWN_HEADERS_64 ___probe_pUnknownHeaders
          ___UnknownHeaderCount
          ___UnknownHeaderProbe))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate__UNKNOWN_HEADERS_64
      (___probe_pUnknownHeaders: ((___UINT16) -> (probe_m_unit)))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  as_validator "_UNKNOWN_HEADERS_64"
    (def'__UNKNOWN_HEADERS_64 ___probe_pUnknownHeaders ___UnknownHeaderCount ___UnknownHeaderProbe)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__UNKNOWN_HEADERS_64
      (___probe_pUnknownHeaders: ((___UINT16) -> (probe_m_unit)))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
    : dtyp kind__UNKNOWN_HEADERS_64
      true
      false
      (NonTrivial (A.copy_buffer_inv ___UnknownHeaderProbe))
      Trivial
      (NonTrivial (A.copy_buffer_loc ___UnknownHeaderProbe)) =
  mk_dtyp_app kind__UNKNOWN_HEADERS_64 (NonTrivial (A.copy_buffer_inv ___UnknownHeaderProbe))
    Trivial (NonTrivial (A.copy_buffer_loc ___UnknownHeaderProbe))
    (type__UNKNOWN_HEADERS_64 ___probe_pUnknownHeaders ___UnknownHeaderCount ___UnknownHeaderProbe)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__UNKNOWN_HEADERS_64]];
                  T.trefl ())))
        (parser__UNKNOWN_HEADERS_64 ___probe_pUnknownHeaders
            ___UnknownHeaderCount
            ___UnknownHeaderProbe)) None true false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [
                      delta_only [
                          `%parser__UNKNOWN_HEADERS_64;
                          `%type__UNKNOWN_HEADERS_64;
                          `%coerce
                        ]
                    ];
                  T.trefl ())))
        (validate__UNKNOWN_HEADERS_64 ___probe_pUnknownHeaders
            ___UnknownHeaderCount
            ___UnknownHeaderProbe))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ specialize; noextract_to "krml"]
noextract
let def____specialized_UNKNOWN_HEADERS_32
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  ((t_probe_then_validate UInt64
        false
        "pUnknownHeaders"
        ___ProbeInit
        (EverParse3d.Prelude.uint32_to_uint64 (EverParse3d.Prelude.u32_mul (FStar.Range.mk_range "src/SpecializeVLArray.3d"
                    33
                    35
                    33
                    35)
                24ul
                (EverParse3d.Prelude.uint16_to_uint32 ___UnknownHeaderCount)))
        (___specialized32____probe_UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount)
        ___UnknownHeaderProbe
        as_u64_identity
        (dtyp__UNKNOWN_HEADERS_INTERNAL_64 ___UnknownHeaderCount))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind____specialized_UNKNOWN_HEADERS_32:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    kind____UINT64

[@@ specialize; noextract_to "krml"]
noextract
let def'____specialized_UNKNOWN_HEADERS_32
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
    : typ kind____specialized_UNKNOWN_HEADERS_32
      (NonTrivial (A.copy_buffer_inv ___UnknownHeaderProbe))
      Trivial
      (NonTrivial (A.copy_buffer_loc ___UnknownHeaderProbe))
      true
      false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (coerce_validator [`%kind____specialized_UNKNOWN_HEADERS_32])))
    (def____specialized_UNKNOWN_HEADERS_32 ___UnknownHeaderCount ___UnknownHeaderProbe)

[@@ noextract_to "krml"]
noextract
let type____specialized_UNKNOWN_HEADERS_32
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  (as_type (def'____specialized_UNKNOWN_HEADERS_32 ___UnknownHeaderCount ___UnknownHeaderProbe))

[@@ noextract_to "krml"]
noextract
let parser____specialized_UNKNOWN_HEADERS_32
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  (as_parser (def'____specialized_UNKNOWN_HEADERS_32 ___UnknownHeaderCount ___UnknownHeaderProbe))
[@@ normalize_for_extraction specialization_steps; CInline]
let validate____specialized_UNKNOWN_HEADERS_32
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  as_validator "___specialized_UNKNOWN_HEADERS_32"
    (def'____specialized_UNKNOWN_HEADERS_32 ___UnknownHeaderCount ___UnknownHeaderProbe)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp____specialized_UNKNOWN_HEADERS_32
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
    : dtyp kind____specialized_UNKNOWN_HEADERS_32
      true
      false
      (NonTrivial (A.copy_buffer_inv ___UnknownHeaderProbe))
      Trivial
      (NonTrivial (A.copy_buffer_loc ___UnknownHeaderProbe)) =
  mk_dtyp_app kind____specialized_UNKNOWN_HEADERS_32
    (NonTrivial (A.copy_buffer_inv ___UnknownHeaderProbe)) Trivial
    (NonTrivial (A.copy_buffer_loc ___UnknownHeaderProbe))
    (type____specialized_UNKNOWN_HEADERS_32 ___UnknownHeaderCount ___UnknownHeaderProbe)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type____specialized_UNKNOWN_HEADERS_32]];
                  T.trefl ())))
        (parser____specialized_UNKNOWN_HEADERS_32 ___UnknownHeaderCount ___UnknownHeaderProbe)) None
    true false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [
                      delta_only [
                          `%parser____specialized_UNKNOWN_HEADERS_32;
                          `%type____specialized_UNKNOWN_HEADERS_32;
                          `%coerce
                        ]
                    ];
                  T.trefl ())))
        (validate____specialized_UNKNOWN_HEADERS_32 ___UnknownHeaderCount ___UnknownHeaderProbe))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))

[@@ normalize_for_extraction specialization_steps]
let ___UNKNOWN_HEADERS____probe__UNKNOWN_HEADERS_64_0_UNKNOWN_HEADERS_INTERNAL_64
      (____arg0: (___UINT16))
     = probe_action_as_probe_m <| (Probe_action_copy_init_sz ___ProbeAndCopy)

[@@ specialize; noextract_to "krml"]
noextract
let def__UNKNOWN_HEADERS
      (___Requestor32: (___Bool))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  ((T_drop
      (T_cases ___Requestor32
          (T_with_comment "pUnknownHeaders32"
              (T_denoted "pUnknownHeaders32"
                  (dtyp____specialized_UNKNOWN_HEADERS_32 ___UnknownHeaderCount
                      ___UnknownHeaderProbe))
              "Validating field pUnknownHeaders32")
          (T_cases (___Requestor32 = false)
              (T_with_comment "pUnknownHeaders64"
                  (T_denoted "pUnknownHeaders64"
                      (dtyp__UNKNOWN_HEADERS_64 ___UNKNOWN_HEADERS____probe__UNKNOWN_HEADERS_64_0_UNKNOWN_HEADERS_INTERNAL_64
                          ___UnknownHeaderCount
                          ___UnknownHeaderProbe))
                  "Validating field pUnknownHeaders64")
              (T_false "_x_0"))))
    <:
    Tot (typ _ _ _ _ _ _)
    by
    (T.norm [delta_attr [`%specialize]; zeta; iota; primops];
      T.smt ()))

[@@ noextract_to "krml"]
inline_for_extraction noextract
let kind__UNKNOWN_HEADERS:P.parser_kind true WeakKindStrongPrefix =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%weak_kind_glb]; zeta; iota; primops];
              T.trefl ())))
    (glb kind____specialized_UNKNOWN_HEADERS_32 (glb kind__UNKNOWN_HEADERS_64 impos_kind))

[@@ specialize; noextract_to "krml"]
noextract
let def'__UNKNOWN_HEADERS
      (___Requestor32: (___Bool))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
    : typ kind__UNKNOWN_HEADERS
      (NonTrivial
        (A.conj_inv (A.copy_buffer_inv ___UnknownHeaderProbe)
            (A.copy_buffer_inv ___UnknownHeaderProbe)))
      Trivial
      (NonTrivial
        (A.eloc_union (A.copy_buffer_loc ___UnknownHeaderProbe)
            (A.copy_buffer_loc ___UnknownHeaderProbe)))
      true
      false =
  coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (coerce_validator [`%kind__UNKNOWN_HEADERS])))
    (def__UNKNOWN_HEADERS ___Requestor32 ___UnknownHeaderCount ___UnknownHeaderProbe)

[@@ noextract_to "krml"]
noextract
let type__UNKNOWN_HEADERS
      (___Requestor32: (___Bool))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     = (as_type (def'__UNKNOWN_HEADERS ___Requestor32 ___UnknownHeaderCount ___UnknownHeaderProbe))

[@@ noextract_to "krml"]
noextract
let parser__UNKNOWN_HEADERS
      (___Requestor32: (___Bool))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  (as_parser (def'__UNKNOWN_HEADERS ___Requestor32 ___UnknownHeaderCount ___UnknownHeaderProbe))
[@@ normalize_for_extraction specialization_steps]
let validate__UNKNOWN_HEADERS
      (___Requestor32: (___Bool))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
     =
  as_validator "_UNKNOWN_HEADERS"
    (def'__UNKNOWN_HEADERS ___Requestor32 ___UnknownHeaderCount ___UnknownHeaderProbe)

[@@ specialize; noextract_to "krml"]
noextract
let dtyp__UNKNOWN_HEADERS
      (___Requestor32: (___Bool))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
    : dtyp kind__UNKNOWN_HEADERS
      true
      false
      (NonTrivial
        (A.conj_inv (A.copy_buffer_inv ___UnknownHeaderProbe)
            (A.copy_buffer_inv ___UnknownHeaderProbe)))
      Trivial
      (NonTrivial
        (A.eloc_union (A.copy_buffer_loc ___UnknownHeaderProbe)
            (A.copy_buffer_loc ___UnknownHeaderProbe))) =
  mk_dtyp_app kind__UNKNOWN_HEADERS
    (NonTrivial
      (A.conj_inv (A.copy_buffer_inv ___UnknownHeaderProbe)
          (A.copy_buffer_inv ___UnknownHeaderProbe))) Trivial
    (NonTrivial
      (A.eloc_union (A.copy_buffer_loc ___UnknownHeaderProbe)
          (A.copy_buffer_loc ___UnknownHeaderProbe)))
    (type__UNKNOWN_HEADERS ___Requestor32 ___UnknownHeaderCount ___UnknownHeaderProbe)
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%type__UNKNOWN_HEADERS]];
                  T.trefl ())))
        (parser__UNKNOWN_HEADERS ___Requestor32 ___UnknownHeaderCount ___UnknownHeaderProbe)) None
    true false
    (coerce (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
                (T.norm [delta_only [`%parser__UNKNOWN_HEADERS; `%type__UNKNOWN_HEADERS; `%coerce]];
                  T.trefl ())))
        (validate__UNKNOWN_HEADERS ___Requestor32 ___UnknownHeaderCount ___UnknownHeaderProbe))
    (FStar.Tactics.Effect.synth_by_tactic (fun _ ->
            (T.norm [delta_only [`%Some?]; iota];
              T.trefl ())))


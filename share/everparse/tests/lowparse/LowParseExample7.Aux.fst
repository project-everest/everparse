module LowParseExample7.Aux

(* TLS ClientHello spec — pure spec, no Low*.
   Ported from tests/lowparse/LowParseExample7.Aux.fst
   Keeps type definitions, parsers and serializers for basic types.
   Dropped dsum-based extension parsing and set_binders
   (use internal APIs not compatible with CMI). *)

module LP = LowParse.Spec
module B32 = FStar.Bytes
module U32 = FStar.UInt32
module L = FStar.List.Tot

// NOTE: parse_bounded_vlbytes_t is only the vlbytes payload, it does not include its length
type binders = LP.parse_bounded_vlbytes_t 0 65535
let parse_binders : LP.parser _ binders = LP.parse_bounded_vlbytes 0 65535
let serialize_binders: LP.serializer parse_binders = LP.serialize_bounded_vlbytes 0 65535

type pre_shared_key_extension = (U32.t * binders)
let parse_pre_shared_key_extension : LP.parser _ pre_shared_key_extension = LP.nondep_then LP.parse_u32 parse_binders
let serialize_pre_shared_key_extension : LP.serializer parse_pre_shared_key_extension = LP.serialize_nondep_then LP.serialize_u32 serialize_binders

type extension_type = | PreSharedKeyExtension_t

inline_for_extraction
let extension_enum : LP.enum extension_type U32.t =
  let l : list (extension_type * U32.t) = [
    PreSharedKeyExtension_t, 18ul;
  ]
  in
  assert_norm (L.noRepeats (LP.list_map fst l) /\ L.noRepeats (LP.list_map snd l));
  l

type cipher_suites = LP.parse_bounded_vldata_strong_t 0 65535 (LP.serialize_list _ (LP.serialize_flbytes 2))
let parse_cipher_suites : LP.parser _ cipher_suites = LP.parse_bounded_vldata_strong 0 65535 (LP.serialize_list _ (LP.serialize_flbytes 2))
let serialize_cipher_suites : LP.serializer parse_cipher_suites = LP.serialize_bounded_vldata_strong 0 65535 (LP.serialize_list _ (LP.serialize_flbytes 2))

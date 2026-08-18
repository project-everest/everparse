module CDDL.Pulse.Bundle.Misc
include CDDL.Pulse.Bundle.Base
include CDDL.Pulse.Parse.Misc
include CDDL.Pulse.Serialize.Misc
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module EqTest = CDDL.Spec.EqTest

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_uint
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_int64: read_uint64_t vmatch)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_uint;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_copyful_pure_as_zero_copy (impl_copyful_uint cbor_destr_int64);
  b_serializer = impl_serialize_uint cbor_serialize cbor_mk_int64 cbor_elim_int64;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_nint
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_int64: read_uint64_t vmatch)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_nint;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_copyful_pure_as_zero_copy (impl_copyful_nint cbor_destr_int64);
  b_serializer = impl_serialize_nint cbor_serialize cbor_mk_int64 cbor_elim_int64;
}

module U64 = FStar.UInt64

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_int_range_uint64
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_int64: read_uint64_t vmatch)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
  (lo hi: U64.t)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_int_range_uint64 lo hi;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_copyful_pure_as_zero_copy (impl_copyful_int_range_uint64 cbor_destr_int64 lo hi);
  b_serializer = impl_serialize_int_range_uint64 cbor_serialize cbor_mk_int64 cbor_elim_int64 lo hi;
}

module I64 = FStar.Int64

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_int_range_int64
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_destr_int64: read_uint64_t vmatch)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
  (lo hi: I64.t)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_int_range_int64 lo hi;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_copyful_pure_as_zero_copy (impl_copyful_int_range_int64 cbor_get_major_type cbor_destr_int64 lo hi);
  b_serializer = impl_serialize_int_range_int64 cbor_serialize cbor_mk_int64 cbor_elim_int64 lo hi;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_int_range_neg_int64
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_int64: read_uint64_t vmatch)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
  (lo hi: U64.t)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_int_range_neg_int64 lo hi;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_copyful_pure_as_zero_copy (impl_copyful_int_range_neg_int64 cbor_destr_int64 lo hi);
  b_serializer = impl_serialize_int_range_neg_int64 cbor_serialize cbor_mk_int64 cbor_elim_int64 lo hi;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_bytes
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_string: get_string_t vmatch)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_string: mk_string_t vmatch)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_bstr;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_zero_copy_bytes cbor_destr_string;
  b_serializer = impl_serialize_bstr cbor_serialize cbor_mk_string false;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_text
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_string: get_string_t vmatch)
  (impl_utf8_correct: impl_utf8_correct_t)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_string: mk_string_t vmatch)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_tstr;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_zero_copy_text cbor_destr_string;
  b_serializer = impl_serialize_tstr impl_utf8_correct cbor_serialize cbor_mk_string false;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_str_size
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_string: get_string_t vmatch)
  (impl_utf8_correct: impl_utf8_correct_t)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_string: mk_string_t vmatch)
  (mt: major_type_byte_string_or_text_string)
  (lo hi: U64.t)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = (spec_str_size mt lo hi);
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_zero_copy_str_size cbor_destr_string mt lo hi;
  b_serializer = impl_serialize_str_size impl_utf8_correct cbor_serialize cbor_mk_string false mt lo hi;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_simple
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_simple: read_simple_value_t vmatch)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_simple: mk_simple_t vmatch)
  (cbor_elim_simple: elim_simple_t vmatch)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_simple;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_copyful_pure_as_zero_copy (impl_copyful_simple cbor_destr_simple);
  b_serializer = impl_serialize_simple cbor_serialize cbor_mk_simple cbor_elim_simple;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_bool
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_simple: read_simple_value_t vmatch)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_simple: mk_simple_t vmatch)
  (cbor_elim_simple: elim_simple_t vmatch)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_bool;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_copyful_pure_as_zero_copy (impl_copyful_bool cbor_destr_simple);
  b_serializer = impl_serialize_bool cbor_serialize cbor_mk_simple cbor_elim_simple;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_tagged_some
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_get_tagged_payload: get_tagged_payload_t vmatch)
  (cbor_serialize_tagged_tag: cbor_det_serialize_tag_t)
  (tag: U64.t)
  (b: bundle vmatch)
: bundle vmatch
= match b with
  | Mkbundle b_typ b_spec_type b_spec_type_eq b_spec b_impl_type b_rel b_parser b_serializer ->
{
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = b_spec_type_eq;
  b_spec = spec_tag_some tag b_spec;
  b_impl_type = b_impl_type;
  b_rel = _;
  b_parser = impl_zero_copy_tagged_some cbor_get_tagged_payload tag b_parser;
  b_serializer = impl_serialize_tagged_some cbor_serialize_tagged_tag tag b_serializer;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_tagged_none
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_get_tagged_tag: get_tagged_tag_t vmatch)
  (cbor_get_tagged_payload: get_tagged_payload_t vmatch)
  (cbor_serialize_tagged_tag: cbor_det_serialize_tag_t)
  (b: bundle vmatch)
: bundle vmatch
= match b with
  | Mkbundle b_typ b_spec_type b_spec_type_eq b_spec b_impl_type b_rel b_parser b_serializer ->
{
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.pair_eq (EqTest.eqtype_eq _) (b_spec_type_eq);
  b_spec = spec_tag_none b_spec;
  b_impl_type = (U64.t & b_impl_type);
  b_rel = _;
  b_parser = impl_zero_copy_tagged_none cbor_get_tagged_tag cbor_get_tagged_payload b_parser;
  b_serializer = impl_serialize_tagged_none cbor_serialize_tagged_tag b_serializer;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_det_cbor
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (#vmatch': perm -> cbor_t -> cbor -> slprop)
  (cbor_destr_string: get_string_t vmatch)
  (cbor_det_parse: cbor_det_parse_t vmatch')
  (cbor_serialize_string: cbor_det_serialize_string_t)
  (b: bundle vmatch')
: bundle vmatch
= match b with
  | Mkbundle b_typ b_spec_type b_spec_type_eq b_spec b_impl_type b_rel b_parser b_serializer ->
{
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = b_spec_type_eq;
  b_spec = spec_bstr_cbor_det b_spec;
  b_impl_type = b_impl_type;
  b_rel = _;
  b_parser = impl_zero_copy_det_cbor cbor_destr_string cbor_det_parse b_spec b_parser;
  b_serializer = impl_serialize_bstr_cbor_det cbor_serialize_string b_serializer;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_any
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_serialize: cbor_det_serialize_t vmatch)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_any;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_zero_copy_any vmatch;
  b_serializer = impl_serialize_any cbor_serialize;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_literal
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> cbor -> slprop)
  (cbor_serialize: cbor_det_serialize_t vmatch)
  (# [@@@erasable] l: Ghost.erased cbor)
  (w: with_cbor_literal_t vmatch l)
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = spec_literal l;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_zero_copy_unit vmatch _;
  b_serializer = impl_serialize_literal cbor_serialize w;
}

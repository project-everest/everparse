module CDDL.Pulse.AST.Parse.ElemType
include CDDL.Pulse.Parse.Misc
include CDDL.Pulse.AST.Types
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module AST = CDDL.Spec.AST.Base
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

[@@AST.sem_attr]
let impl_zero_copy_elem_type
  (#ty: Type0)
  (vmatch: (perm -> ty -> cbor -> slprop))
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_destr_int64: read_uint64_t vmatch)
  (cbor_get_string: get_string_t vmatch)
  (cbor_destr_simple: read_simple_value_t vmatch)
  (l: AST.elem_typ { AST.wf_elem_typ l })
: Tot (impl_zero_copy_parse vmatch (AST.spec_of_elem_typ l ()).parser (rel_elem_type_sem vmatch (AST.target_type_of_elem_typ l)))
= match l returns (impl_zero_copy_parse vmatch (AST.spec_of_elem_typ l ()).parser (rel_elem_type_sem vmatch (AST.target_type_of_elem_typ l))) with
  | AST.ELiteral l -> impl_zero_copy_unit vmatch _
  | AST.EBool -> impl_copyful_pure_as_zero_copy (impl_copyful_bool cbor_destr_simple)
  | AST.ESimple -> impl_copyful_pure_as_zero_copy (impl_copyful_simple cbor_destr_simple)
  | AST.EByteString -> impl_zero_copy_bytes cbor_get_string
  | AST.ETextString -> impl_zero_copy_text cbor_get_string
  | AST.EUInt -> impl_copyful_pure_as_zero_copy (impl_copyful_uint cbor_destr_int64)
  | AST.ENInt -> impl_copyful_pure_as_zero_copy (impl_copyful_nint cbor_destr_int64)
  | AST.EAlwaysFalse -> impl_zero_copy_always_false vmatch _
  | AST.EAny -> (impl_zero_copy_any vmatch)

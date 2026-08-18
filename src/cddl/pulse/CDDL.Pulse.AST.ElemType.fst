module CDDL.Pulse.AST.ElemType
include CDDL.Pulse.Misc
include CDDL.Pulse.AST.Literal
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
let impl_elem_type
  (#ty: Type0)
  (#vmatch: (perm -> ty -> cbor -> slprop))
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_destr_int64: read_uint64_t vmatch)
  (cbor_get_string: get_string_t vmatch)
  (cbor_destr_simple: read_simple_value_t vmatch)
  (l: AST.elem_typ { AST.wf_elem_typ l })
: Tot (impl_typ vmatch (AST.elem_typ_sem l))
= match l with
  | AST.ELiteral l -> impl_literal vmatch cbor_get_major_type cbor_destr_int64 cbor_get_string cbor_destr_simple l
  | AST.EBool -> impl_bool cbor_get_major_type cbor_destr_simple
  | AST.ESimple -> impl_simple cbor_get_major_type
  | AST.EByteString -> impl_bytes cbor_get_major_type
  | AST.ETextString -> impl_text cbor_get_major_type
  | AST.EUInt -> impl_uint cbor_get_major_type
  | AST.ENInt -> impl_neg_int cbor_get_major_type
  | AST.EAlwaysFalse -> impl_always_false _
  | AST.EAny -> impl_any _

module EverParse3d.CAbi.Public

module B = EverParse3d.CAbi.Boolean
module E = EverParse3d.ErrorCode
module P = EverParse3d.Lowstar.Public
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module X = EverParse3d.InputStream.LowstarExtern.Types

[@@FStar.Attributes.rename_let "EVERPARSE_BASE_T"; FStar.Attributes.custard_no_unfold]
type base_t = X.input_buffer

let error_code_is_range_okay (size offset access_size: U32.t) : B.t =
  B.of_bool (E.is_range_okay size offset access_size)

[@@FStar.Attributes.rename_let "EverParseIsError"; FStar.Attributes.CInline]
let is_error (position_or_error: U64.t) : B.t =
  B.of_bool (P.is_error position_or_error)

[@@FStar.Attributes.rename_let "EverParseIsSuccess"; FStar.Attributes.CInline]
let is_success (position_or_error: U64.t) : B.t =
  B.of_bool (P.is_success position_or_error)

[@@FStar.Attributes.rename_let "EverParseIsRangeOkay"; FStar.Attributes.CInline]
let is_range_okay (size offset access_size: U32.t) : B.t =
  B.of_bool (P.is_range_okay size offset access_size)

[@@FStar.Attributes.rename_let "EverParseCheckConstraintOk"; FStar.Attributes.CInline]
let check_constraint_ok (ok: B.t)
  (position: U64.t { U64.v position < pow2 60 }) : U64.t =
  P.check_constraint_ok (B.to_bool ok) position

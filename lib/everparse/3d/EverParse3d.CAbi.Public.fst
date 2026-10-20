module EverParse3d.CAbi.Public

module B = EverParse3d.CAbi.Boolean
module E = EverParse3d.ErrorCode
module P = EverParse3d.Lowstar.Public
module U32 = FStar.UInt32
module U64 = FStar.UInt64

let error_code_is_range_okay (size offset access_size: U32.t) : B.t =
  B.of_bool (E.is_range_okay size offset access_size)

let is_error (position_or_error: U64.t) : B.t =
  B.of_bool (P.is_error position_or_error)

let is_success (position_or_error: U64.t) : B.t =
  B.of_bool (P.is_success position_or_error)

let is_range_okay (size offset access_size: U32.t) : B.t =
  B.of_bool (P.is_range_okay size offset access_size)

let check_constraint_ok (ok: B.t)
  (position: U64.t { U64.v position < pow2 60 }) : U64.t =
  P.check_constraint_ok (B.to_bool ok) position

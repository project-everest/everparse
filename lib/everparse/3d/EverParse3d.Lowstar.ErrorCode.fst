module EverParse3d.Lowstar.ErrorCode
open FStar.Mul

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module C = FStar.Int.Cast.Full
module E = EverParse3d.ErrorCode

let position_limit = 1152921504606846976

inline_for_extraction
let legacy_kind (status: U8.t)
  : Tot (r: U64.t {
      U64.v r < 16 /\
      (r == 0UL <==> status == E.validator_success) /\
      (r == 5UL <==> status == E.validator_error_action_failed) /\
      (U8.v status >= 2 /\ U8.v status <= 8 ==> U64.v r == U8.v status)
    })
  = if status = 0uy || (U8.gte status 2uy && U8.lte status 8uy)
    then C.uint8_to_uint64 status
    else 15UL

inline_for_extraction
let pack (status: U8.t) (position: U64.t { U64.v position < position_limit })
  : Tot (r: U64.t {
      U64.v r == U64.v (legacy_kind status) * position_limit + U64.v position
    })
  = U64.add (U64.mul (legacy_kind status) 1152921504606846976UL) position

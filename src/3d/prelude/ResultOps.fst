module ResultOps
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module LPL = LowParse.Low.Base
module BF = LowParse.BitFields
let result = U64.t
let field_id = x:U64.t{ 0 < U64.v x /\ U64.v x < pow2 16}
let field_id_of_result (result:result) : U64.t =
  LowParse.Low.Base.get_validator_error_code result
let result_is_error(result:result) : bool =
  let open U64 in
  result >^ LPL.validator_max_length
let error_kind_of_result (result:result) : U64.t =
  LowParse.Low.Base.get_validator_error_kind result
let error_reason_of_result (code:U64.t) : string =
  match error_kind_of_result code with
  | 1uL -> "generic error"
  | 2uL -> "not enough data"
  | 3uL -> "impossible"
  | 4uL -> "list size not multiple of element size"
  | 5uL -> "action failed"
  | 6uL -> "constraint failed"
  | 7uL -> "unexpected padding"
  | _ -> "unspecified"

[@ CMacro ]
let validator_error_action_failed : LPL.validator_error = normalize_term (LPL.set_validator_error_kind 0uL 5uL)

[@ CMacro ]
let validator_error_constraint_failed : LPL.validator_error = normalize_term (LPL.set_validator_error_kind 0uL 6uL)

[@ CInline ]
let check_constraint_ok (ok:bool) (position:U64.t) : Tot U64.t =
      if ok
      then position
      else validator_error_constraint_failed

[@ CInline ]
let check_constraint_ok_with_field_id (ok:bool) (startPosition: LPL.pos_t) (endPosition:U64.t) (fieldId: field_id) : Tot U64.t =
      if ok
      then endPosition
      else LPL.set_validator_error_pos_and_code validator_error_constraint_failed startPosition fieldId

////////////////////////////////////////////////////////////////////////////////
// Some generic helpers
////////////////////////////////////////////////////////////////////////////////
[@ CInline ]
let is_range_okay (size offset access_size:U32.t)
  : bool
  = let open U32 in
    size >=^ access_size &&
    size -^ access_size >=^ offset

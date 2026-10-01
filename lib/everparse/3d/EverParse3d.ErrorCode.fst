module EverParse3d.ErrorCode
module U8 = FStar.UInt8

[@@CMacro]
let validator_success = 0uy

[@@CMacro]
let validator_error_action_failed = 1uy

[@ CMacro ]
let validator_error_not_enough_data = 2uy

[@ CMacro ]
let validator_error_impossible = 3uy

[@ CMacro ]
let validator_error_list_size_not_multiple = 4uy

[@ CMacro ]
let validator_error_constraint_failed = 5uy

[@ CMacro ]
let validator_error_unexpected_padding = 6uy

[@ CMacro ]
let validator_error_probe_failed = 7uy

let error_reason_of_result (code:U8.t) : string =
  match code with
  | 0uy -> "success"
  | 1uy -> "action failed"
  | 2uy -> "not enough data"
  | 3uy -> "impossible"
  | 4uy -> "list size not multiple of element size"
  | 5uy -> "constraint failed"
  | 6uy -> "unexpected padding"
  | 7uy -> "probe failed"
  | _ -> "unspecified"

// Some generic helpers

module U32 = FStar.UInt32

let is_range_okay (size offset access_size: U32.t)
  : bool
  = let open U32 in
    size >=^ access_size &&
    size -^ access_size >=^ offset

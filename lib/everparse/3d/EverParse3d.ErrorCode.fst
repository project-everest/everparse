module EverParse3d.ErrorCode
module U8 = FStar.UInt8

// The 8-bit validator status codes, common to all runtime profiles. Not
// inline_for_extraction: extracted once into the runtime EverParse.h as
// macros, which generated validators refer to by name.

[@@CMacro; FStar.Attributes.rename_let "EVERPARSE_STATUS_SUCCESS"]
let validator_success = 0uy

[@@CMacro; FStar.Attributes.rename_let "EVERPARSE_STATUS_ERROR_ACTION_FAILED"]
let validator_error_action_failed = 5uy

[@@CMacro; FStar.Attributes.rename_let "EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA"]
let validator_error_not_enough_data = 2uy

[@@CMacro; FStar.Attributes.rename_let "EVERPARSE_STATUS_ERROR_IMPOSSIBLE"]
let validator_error_impossible = 3uy

[@@CMacro; FStar.Attributes.rename_let "EVERPARSE_STATUS_ERROR_LIST_SIZE_NOT_MULTIPLE"]
let validator_error_list_size_not_multiple = 4uy

[@@CMacro; FStar.Attributes.rename_let "EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED"]
let validator_error_constraint_failed = 6uy

[@@CMacro; FStar.Attributes.rename_let "EVERPARSE_STATUS_ERROR_UNEXPECTED_PADDING"]
let validator_error_unexpected_padding = 7uy

[@@CMacro; FStar.Attributes.rename_let "EVERPARSE_STATUS_ERROR_PROBE_FAILED"]
let validator_error_probe_failed = 8uy

noextract
let is_validation_error (code:U8.t) : bool =
  code <> validator_success && code <> validator_error_action_failed

// Not inline_for_extraction: extracted once into the runtime EverParse.h as a
// static inline function, rather than duplicated at every validator call site.
[@@FStar.Attributes.CInline]
let error_reason_of_result (code:U8.t) : string =
  match code with
  | 0uy -> "success"
  | 2uy -> "not enough data"
  | 3uy -> "impossible"
  | 4uy -> "list size not multiple of element size"
  | 5uy -> "action failed"
  | 6uy -> "constraint failed"
  | 7uy -> "unexpected padding"
  | 8uy -> "probe failed"
  | _ -> "unspecified"

// Some generic helpers

module U32 = FStar.UInt32

let is_range_okay (size offset access_size: U32.t)
  : bool
  = let open U32 in
    size >=^ access_size &&
    size -^ access_size >=^ offset

module EverParse3d.Lowstar.Public
open Pulse.Lib.Pervasives
#lang-pulse

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module BF = LowParse.BitFields
module R = Pulse.Lib.Reference

[@@CMacro]
let validator_max_length = 1152921504606846975UL

let is_error (positionOrError: U64.t) = U64.gt positionOrError validator_max_length
let is_success (positionOrError: U64.t) = U64.lte positionOrError validator_max_length

let set_validator_error_pos (error: U64.t)
  (position: U64.t { U64.v position < pow2 60 }) : U64.t =
  BF.uint64.BF.set_bitfield error 0 60 position

let get_validator_error_pos (x: U64.t) : U64.t =
  BF.uint64.BF.get_bitfield x 0 60

let set_validator_error_kind (error: U64.t)
  (code: U64.t { U64.v code < pow2 4 }) : U64.t =
  BF.uint64.BF.set_bitfield error 60 64 code

let get_validator_error_kind (error: U64.t) : U64.t =
  BF.uint64.BF.get_bitfield error 60 64

[@@CMacro]
let validator_error_generic = 1152921504606846976UL
[@@CMacro]
let validator_error_not_enough_data = 2305843009213693952UL
[@@CMacro]
let validator_error_impossible = 3458764513820540928UL
[@@CMacro]
let validator_error_list_size_not_multiple = 4611686018427387904UL
[@@CMacro]
let validator_error_action_failed = 5764607523034234880UL
[@@CMacro]
let validator_error_constraint_failed = 6917529027641081856UL
[@@CMacro]
let validator_error_unexpected_padding = 8070450532247928832UL
[@@CMacro]
let validator_error_probe_failed = 9223372036854775808UL

let error_reason_of_result (code: U64.t) : string =
  match get_validator_error_kind code with
  | 1UL -> "generic error"
  | 2UL -> "not enough data"
  | 3UL -> "impossible"
  | 4UL -> "list size not multiple of element size"
  | 5UL -> "action failed"
  | 6UL -> "constraint failed"
  | 7UL -> "unexpected padding"
  | 8UL -> "probe failed"
  | _ -> "unspecified"

let check_constraint_ok (ok: bool)
  (position: U64.t { U64.v position < pow2 60 }) : U64.t =
  if ok then position
  else set_validator_error_pos validator_error_constraint_failed position

let is_range_okay (size offset access_size: U32.t) : bool =
  U32.gte size access_size && U32.gte (U32.sub size access_size) offset

noeq type error_frame = {
  filled: bool;
  start_pos: U64.t;
  typename_s: string;
  fieldname: string;
  reason: string;
  error_code: U64.t;
}

noextract inline_for_extraction
fn record_error
  (typename_s fieldname reason: string)
  (error_code: U64.t) (context: R.ref error_frame) (start_pos: U64.t)
  (#frame: Ghost.erased error_frame)
requires R.pts_to context (Ghost.reveal frame)
returns _: unit
ensures R.pts_to context
  (if (Ghost.reveal frame).filled then Ghost.reveal frame else
    { filled = true; start_pos = start_pos; typename_s = typename_s;
      fieldname = fieldname; reason = reason; error_code = error_code })
{
  let frame = !context;
  if (not frame.filled) {
    context := { filled = true; start_pos = start_pos; typename_s = typename_s;
      fieldname = fieldname; reason = reason; error_code = error_code };
  }
}

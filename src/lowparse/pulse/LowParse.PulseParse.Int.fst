module LowParse.PulseParse.Int
#lang-pulse
include LowParse.Spec.Int
include LowParse.Spec.Int32le
include LowParse.Spec.ConstInt32
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module U32 = FStar.UInt32

inline_for_extraction
let validate_u64_le
: LPS.validator parse_u64_le
= LPS.validate_total_constant_size parse_u64_le 8sz

inline_for_extraction
let jump_u64_le
: LPS.jumper parse_u64_le
= LPS.jump_constant_size parse_u64_le 8sz

inline_for_extraction
let validate_int32le
: LPS.validator parse_int32le
= LPS.validate_total_constant_size parse_int32le 4sz

inline_for_extraction
let jump_int32le
: LPS.jumper parse_int32le
= LPS.jump_constant_size parse_int32le 4sz

inline_for_extraction
fn validate_constint32le
  (v: U32.t)
  (r: PPB.leaf_reader parse_int32le)
: LPS.validator (parse_constint32le (U32.v v))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_constint32le_unfold (U32.v v) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size parse_int32le 4sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (U32.eq x v) {
      true
    } else {
      poffset := offset_val;
      false
    }
  } else {
    false
  }
}

inline_for_extraction
let jump_constint32le
  (v: nat { 0 <= v /\ v < 4294967296 })
: Tot (LPS.jumper (parse_constint32le v))
= LPS.jump_constant_size (parse_constint32le v) 4sz

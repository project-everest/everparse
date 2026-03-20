module LowParse.PulseParse.BoundedInt
#lang-pulse
include LowParse.Spec.BoundedInt
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module R = Pulse.Lib.Reference
module U32 = FStar.UInt32
module U16 = FStar.UInt16

(* Simple constant-size validators *)

inline_for_extraction noextract
let validate_bounded_integer (i: integer_size)
: Tot (LPS.validator (parse_bounded_integer i))
= LPS.validate_total_constant_size (parse_bounded_integer i) (SZ.uint_to_t i)

inline_for_extraction
let validate_bounded_integer' (i: U32.t { 1 <= U32.v i /\ U32.v i <= 4 })
  (_: squash (FStar.SizeT.fits_u64))
: Tot (LPS.validator (parse_bounded_integer (U32.v i)))
= FStar.SizeT.fits_u64_implies_fits_32 ();
  LPS.validate_total_constant_size (parse_bounded_integer (U32.v i)) (FStar.SizeT.uint32_to_sizet i)

inline_for_extraction noextract
let validate_bounded_integer_le (i: integer_size)
: Tot (LPS.validator (parse_bounded_integer_le i))
= LPS.validate_total_constant_size (parse_bounded_integer_le i) (SZ.uint_to_t i)

inline_for_extraction
let validate_u16_le
: LPS.validator parse_u16_le
= LPS.validate_total_constant_size parse_u16_le 2sz

inline_for_extraction
let validate_u32_le
: LPS.validator parse_u32_le
= LPS.validate_total_constant_size parse_u32_le 4sz

(* Bounded int32 validators (BE) — specialized per size *)

#push-options "--z3rlimit 16"

inline_for_extraction
fn validate_bounded_int32_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
  (r: PPB.leaf_reader (parse_bounded_integer 1))
: LPS.validator (parse_bounded_int32 (U32.v min32) (U32.v max32))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size (parse_bounded_integer 1) 1sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) {
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
fn validate_bounded_int32_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
  (r: PPB.leaf_reader (parse_bounded_integer 2))
: LPS.validator (parse_bounded_int32 (U32.v min32) (U32.v max32))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size (parse_bounded_integer 2) 2sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) {
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
fn validate_bounded_int32_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
  (r: PPB.leaf_reader (parse_bounded_integer 3))
: LPS.validator (parse_bounded_int32 (U32.v min32) (U32.v max32))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size (parse_bounded_integer 3) 3sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) {
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
fn validate_bounded_int32_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (r: PPB.leaf_reader (parse_bounded_integer 4))
: LPS.validator (parse_bounded_int32 (U32.v min32) (U32.v max32))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size (parse_bounded_integer 4) 4sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) {
      true
    } else {
      poffset := offset_val;
      false
    }
  } else {
    false
  }
}

(* Bounded int32 validators (LE) — specialized per size *)

inline_for_extraction
fn validate_bounded_int32_le_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
  (r: PPB.leaf_reader (parse_bounded_integer_le 1))
: LPS.validator (parse_bounded_int32_le (U32.v min32) (U32.v max32))
=
  (input: S.slice byte) (poffset: R.ref SZ.t) (#offset: Ghost.erased SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_le_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size (parse_bounded_integer_le 1) 1sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) { true } else { poffset := offset_val; false }
  } else { false }
}

inline_for_extraction
fn validate_bounded_int32_le_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
  (r: PPB.leaf_reader (parse_bounded_integer_le 2))
: LPS.validator (parse_bounded_int32_le (U32.v min32) (U32.v max32))
=
  (input: S.slice byte) (poffset: R.ref SZ.t) (#offset: Ghost.erased SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_le_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size (parse_bounded_integer_le 2) 2sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) { true } else { poffset := offset_val; false }
  } else { false }
}

inline_for_extraction
fn validate_bounded_int32_le_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
  (r: PPB.leaf_reader (parse_bounded_integer_le 3))
: LPS.validator (parse_bounded_int32_le (U32.v min32) (U32.v max32))
=
  (input: S.slice byte) (poffset: R.ref SZ.t) (#offset: Ghost.erased SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_le_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size (parse_bounded_integer_le 3) 3sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) { true } else { poffset := offset_val; false }
  } else { false }
}

inline_for_extraction
fn validate_bounded_int32_le_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (r: PPB.leaf_reader (parse_bounded_integer_le 4))
: LPS.validator (parse_bounded_int32_le (U32.v min32) (U32.v max32))
=
  (input: S.slice byte) (poffset: R.ref SZ.t) (#offset: Ghost.erased SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_le_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size (parse_bounded_integer_le 4) 4sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) { true } else { poffset := offset_val; false }
  } else { false }
}

(* Fixed-size LE bounded int32 validator *)

inline_for_extraction
fn validate_bounded_int32_le_fixed_size
  (min32: U32.t)
  (max32: U32.t { U32.v min32 <= U32.v max32 })
  (r: PPB.leaf_reader parse_u32_le)
: LPS.validator (parse_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_le_fixed_size_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = LPS.validate_total_constant_size parse_u32_le 4sz input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) {
      true
    } else {
      poffset := offset_val;
      false
    }
  } else {
    false
  }
}

(* Generic bounded int32 validators — caller provides sz and sub-validators *)

inline_for_extraction
fn validate_bounded_int32'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: integer_size { sz == log256' (U32.v max32) })
  (v_base: LPS.validator (parse_bounded_integer sz))
  (r: PPB.leaf_reader (parse_bounded_integer sz))
: LPS.validator (parse_bounded_int32 (U32.v min32) (U32.v max32))
=
  (input: S.slice byte) (poffset: R.ref SZ.t) (#offset: Ghost.erased SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = v_base input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) { true } else { poffset := offset_val; false }
  } else { false }
}

inline_for_extraction
fn validate_bounded_int32_le'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: integer_size { sz == log256' (U32.v max32) })
  (v_base: LPS.validator (parse_bounded_integer_le sz))
  (r: PPB.leaf_reader (parse_bounded_integer_le sz))
: LPS.validator (parse_bounded_int32_le (U32.v min32) (U32.v max32))
=
  (input: S.slice byte) (poffset: R.ref SZ.t) (#offset: Ghost.erased SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_int32_le_eq (U32.v min32) (U32.v max32) sinput;
  let offset_val = !poffset;
  let is_valid = v_base input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    if (not (U32.lt x min32 || U32.lt max32 x)) { true } else { poffset := offset_val; false }
  } else { false }
}

(* Runtime dispatchers *)

inline_for_extraction
fn validate_bounded_int32
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (r1: PPB.leaf_reader (parse_bounded_integer 1))
  (r2: PPB.leaf_reader (parse_bounded_integer 2))
  (r3: PPB.leaf_reader (parse_bounded_integer 3))
  (r4: PPB.leaf_reader (parse_bounded_integer 4))
: LPS.validator (parse_bounded_int32 (U32.v min32) (U32.v max32))
=
  (input: S.slice byte) (poffset: R.ref SZ.t) (#offset: Ghost.erased SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  if (U32.lt max32 256ul) {
    validate_bounded_int32_1 min32 max32 r1 input poffset
  } else if (U32.lt max32 65536ul) {
    validate_bounded_int32_2 min32 max32 r2 input poffset
  } else if (U32.lt max32 16777216ul) {
    validate_bounded_int32_3 min32 max32 r3 input poffset
  } else {
    validate_bounded_int32_4 min32 max32 r4 input poffset
  }
}

inline_for_extraction
fn validate_bounded_int32_le
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (r1: PPB.leaf_reader (parse_bounded_integer_le 1))
  (r2: PPB.leaf_reader (parse_bounded_integer_le 2))
  (r3: PPB.leaf_reader (parse_bounded_integer_le 3))
  (r4: PPB.leaf_reader (parse_bounded_integer_le 4))
: LPS.validator (parse_bounded_int32_le (U32.v min32) (U32.v max32))
=
  (input: S.slice byte) (poffset: R.ref SZ.t) (#offset: Ghost.erased SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  if (U32.lt max32 256ul) {
    validate_bounded_int32_le_1 min32 max32 r1 input poffset
  } else if (U32.lt max32 65536ul) {
    validate_bounded_int32_le_2 min32 max32 r2 input poffset
  } else if (U32.lt max32 16777216ul) {
    validate_bounded_int32_le_3 min32 max32 r3 input poffset
  } else {
    validate_bounded_int32_le_4 min32 max32 r4 input poffset
  }
}

#pop-options

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

(* Simple constant-size jumpers *)

inline_for_extraction noextract
let jump_bounded_integer (i: integer_size)
: Tot (LPS.jumper (parse_bounded_integer i))
= LPS.jump_constant_size (parse_bounded_integer i) (SZ.uint_to_t i)

inline_for_extraction noextract
let jump_bounded_integer_le (i: integer_size)
: Tot (LPS.jumper (parse_bounded_integer_le i))
= LPS.jump_constant_size (parse_bounded_integer_le i) (SZ.uint_to_t i)

inline_for_extraction
let jump_u16_le
: LPS.jumper parse_u16_le
= LPS.jump_constant_size parse_u16_le 2sz

inline_for_extraction
let jump_u32_le
: LPS.jumper parse_u32_le
= LPS.jump_constant_size parse_u32_le 4sz

inline_for_extraction
let jump_bounded_int32_le_fixed_size
  (min32: U32.t)
  (max32: U32.t { U32.v min32 <= U32.v max32 })
: Tot (LPS.jumper (parse_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32)))
= LPS.jump_constant_size (parse_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32)) 4sz

(* Bounded int32 jumpers (BE) — all constant-size, sz = log256' max *)

inline_for_extraction
let jump_bounded_int32_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (LPS.jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= LPS.jump_constant_size (parse_bounded_int32 (U32.v min32) (U32.v max32)) 1sz

inline_for_extraction
let jump_bounded_int32_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (LPS.jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= LPS.jump_constant_size (parse_bounded_int32 (U32.v min32) (U32.v max32)) 2sz

inline_for_extraction
let jump_bounded_int32_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (LPS.jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= LPS.jump_constant_size (parse_bounded_int32 (U32.v min32) (U32.v max32)) 3sz

inline_for_extraction
let jump_bounded_int32_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (LPS.jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= LPS.jump_constant_size (parse_bounded_int32 (U32.v min32) (U32.v max32)) 4sz

(* Bounded int32 jumpers (LE) *)

inline_for_extraction
let jump_bounded_int32_le_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (LPS.jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= LPS.jump_constant_size (parse_bounded_int32_le (U32.v min32) (U32.v max32)) 1sz

inline_for_extraction
let jump_bounded_int32_le_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (LPS.jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= LPS.jump_constant_size (parse_bounded_int32_le (U32.v min32) (U32.v max32)) 2sz

inline_for_extraction
let jump_bounded_int32_le_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (LPS.jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= LPS.jump_constant_size (parse_bounded_int32_le (U32.v min32) (U32.v max32)) 3sz

inline_for_extraction
let jump_bounded_int32_le_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (LPS.jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= LPS.jump_constant_size (parse_bounded_int32_le (U32.v min32) (U32.v max32)) 4sz

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

(* Leaf readers for parse_bounded_integer_le *)

module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module Trade = Pulse.Lib.Trade.Util

#push-options "--z3rlimit 32"

inline_for_extraction
fn leaf_read_bounded_integer_le_1
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (bounded_integer 1))
requires
  PPB.pts_to_parsed (parse_bounded_integer_le 1) input #pm v
returns res: bounded_integer 1
ensures
  PPB.pts_to_parsed (parse_bounded_integer_le 1) input #pm v **
  pure (res == Ghost.reveal v)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parser_kind_prop_equiv (parse_bounded_integer_kind 1) (parse_bounded_integer_le 1);
  S.pts_to_len input;
  parse_bounded_integer_le_eq 1 w;
  Seq.lemma_eq_elim (Seq.slice w 0 1) w;
  LowParse.Spec.Int32le.le_to_n_1_eq w;
  let b0 = input.(0sz);
  let res = Cast.uint8_to_uint32 b0;
  Trade.elim _ _;
  res
}

inline_for_extraction
fn leaf_read_bounded_integer_le_2
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (bounded_integer 2))
requires
  PPB.pts_to_parsed (parse_bounded_integer_le 2) input #pm v
returns res: bounded_integer 2
ensures
  PPB.pts_to_parsed (parse_bounded_integer_le 2) input #pm v **
  pure (res == Ghost.reveal v)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parser_kind_prop_equiv (parse_bounded_integer_kind 2) (parse_bounded_integer_le 2);
  S.pts_to_len input;
  parse_bounded_integer_le_eq 2 w;
  Seq.lemma_eq_elim (Seq.slice w 0 2) w;
  LowParse.Spec.Int32le.le_to_n_2_eq w;
  let b0 = input.(0sz);
  let b1 = input.(1sz);
  let v0 = Cast.uint8_to_uint32 b0;
  let v1 = Cast.uint8_to_uint32 b1;
  let res = U32.add v0 (U32.mul 256ul v1);
  Trade.elim _ _;
  res
}

inline_for_extraction
fn leaf_read_bounded_integer_le_4
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (bounded_integer 4))
requires
  PPB.pts_to_parsed (parse_bounded_integer_le 4) input #pm v
returns res: bounded_integer 4
ensures
  PPB.pts_to_parsed (parse_bounded_integer_le 4) input #pm v **
  pure (res == Ghost.reveal v)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parser_kind_prop_equiv (parse_bounded_integer_kind 4) (parse_bounded_integer_le 4);
  S.pts_to_len input;
  parse_bounded_integer_le_eq 4 w;
  Seq.lemma_eq_elim (Seq.slice w 0 4) w;
  LowParse.Spec.Int32le.le_to_n_4_eq w;
  let b0 = input.(0sz);
  let b1 = input.(1sz);
  let b2 = input.(2sz);
  let b3 = input.(3sz);
  let v0 = Cast.uint8_to_uint32 b0;
  let v1 = Cast.uint8_to_uint32 b1;
  let v2 = Cast.uint8_to_uint32 b2;
  let v3 = Cast.uint8_to_uint32 b3;
  let res = U32.add v0 (U32.mul 256ul (U32.add v1 (U32.mul 256ul (U32.add v2 (U32.mul 256ul v3)))));
  Trade.elim _ _;
  res
}

#pop-options

(* leaf_reader for parse_bounded_integer (big-endian) *)

#push-options "--z3rlimit 32"

inline_for_extraction
fn leaf_read_bounded_integer_1
  (_: squash FStar.SizeT.fits_u64)
: PPB.leaf_reader (parse_bounded_integer 1)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (bounded_integer 1))
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_bounded_integer_spec 1 w;
  S.pts_to_len input;
  let b0 = input.(0sz);
  FStar.Endianness.reveal_be_to_n (Seq.slice w 0 1);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 1) 0 0);
  Seq.lemma_index_slice w 0 1 0;
  let res = Cast.uint8_to_uint32 b0;
  Trade.elim _ _;
  res
}

inline_for_extraction
fn leaf_read_bounded_integer_2
  (_: squash FStar.SizeT.fits_u64)
: PPB.leaf_reader (parse_bounded_integer 2)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (bounded_integer 2))
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_bounded_integer_spec 2 w;
  S.pts_to_len input;
  let b0 = input.(0sz);
  let b1 = input.(1sz);
  FStar.Endianness.reveal_be_to_n (Seq.slice w 0 2);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 2) 0 1);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 2) 0 0);
  Seq.lemma_index_slice w 0 2 1;
  Seq.lemma_index_slice w 0 2 0;
  Seq.lemma_index_slice (Seq.slice w 0 2) 0 1 0;
  let v0 = Cast.uint8_to_uint32 b0;
  let v1 = Cast.uint8_to_uint32 b1;
  let res = U32.add (U32.mul 256ul v0) v1;
  Trade.elim _ _;
  res
}

inline_for_extraction
fn leaf_read_bounded_integer_3
  (_: squash FStar.SizeT.fits_u64)
: PPB.leaf_reader (parse_bounded_integer 3)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (bounded_integer 3))
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_bounded_integer_spec 3 w;
  S.pts_to_len input;
  let b0 = input.(0sz);
  let b1 = input.(1sz);
  let b2 = input.(2sz);
  FStar.Endianness.reveal_be_to_n (Seq.slice w 0 3);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 3) 0 2);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 3) 0 1);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 3) 0 0);
  Seq.lemma_index_slice w 0 3 2;
  Seq.lemma_index_slice w 0 3 1;
  Seq.lemma_index_slice w 0 3 0;
  Seq.lemma_index_slice (Seq.slice w 0 3) 0 2 1;
  Seq.lemma_index_slice (Seq.slice w 0 3) 0 2 0;
  Seq.lemma_index_slice (Seq.slice w 0 3) 0 1 0;
  let v0 = Cast.uint8_to_uint32 b0;
  let v1 = Cast.uint8_to_uint32 b1;
  let v2 = Cast.uint8_to_uint32 b2;
  let res = U32.add (U32.mul 256ul (U32.add (U32.mul 256ul v0) v1)) v2;
  Trade.elim _ _;
  res
}

inline_for_extraction
fn leaf_read_bounded_integer_4
  (_: squash FStar.SizeT.fits_u64)
: PPB.leaf_reader (parse_bounded_integer 4)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (bounded_integer 4))
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_bounded_integer_spec 4 w;
  S.pts_to_len input;
  let b0 = input.(0sz);
  let b1 = input.(1sz);
  let b2 = input.(2sz);
  let b3 = input.(3sz);
  FStar.Endianness.reveal_be_to_n (Seq.slice w 0 4);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 4) 0 3);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 4) 0 2);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 4) 0 1);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 4) 0 0);
  Seq.lemma_index_slice w 0 4 3;
  Seq.lemma_index_slice w 0 4 2;
  Seq.lemma_index_slice w 0 4 1;
  Seq.lemma_index_slice w 0 4 0;
  Seq.lemma_index_slice (Seq.slice w 0 4) 0 3 2;
  Seq.lemma_index_slice (Seq.slice w 0 4) 0 3 1;
  Seq.lemma_index_slice (Seq.slice w 0 4) 0 3 0;
  Seq.lemma_index_slice (Seq.slice w 0 4) 0 2 1;
  Seq.lemma_index_slice (Seq.slice w 0 4) 0 2 0;
  Seq.lemma_index_slice (Seq.slice w 0 4) 0 1 0;
  let v0 = Cast.uint8_to_uint32 b0;
  let v1 = Cast.uint8_to_uint32 b1;
  let v2 = Cast.uint8_to_uint32 b2;
  let v3 = Cast.uint8_to_uint32 b3;
  let res = U32.add (U32.mul 256ul (U32.add (U32.mul 256ul (U32.add (U32.mul 256ul v0) v1)) v2)) v3;
  Trade.elim _ _;
  res
}

#pop-options

inline_for_extraction
let leaf_read_bounded_integer
  (sq: squash FStar.SizeT.fits_u64)
  (i: integer_size)
: Tot (PPB.leaf_reader (parse_bounded_integer i))
= if i = 1 then leaf_read_bounded_integer_1 sq
  else if i = 2 then leaf_read_bounded_integer_2 sq
  else if i = 3 then leaf_read_bounded_integer_3 sq
  else leaf_read_bounded_integer_4 sq

module LowParse.Pulse.DER
#lang-pulse
include LowParse.Spec.DER
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

module LPI = LowParse.Pulse.Int

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 })
  (r_u8: LPS.leaf_reader serialize_u8)
  (r_bi: (i: integer_size) -> LPS.leaf_reader (serialize_bounded_integer i))
: LPS.validator (parse_der_length_payload32 x)
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_der_length_payload32_unfold x sinput;
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  if (U8.lt x 128uy) {
    true
  } else if (x = 128uy || x = 255uy) {
    false
  } else if (x = 129uy) {
    let offset_val = !poffset;
    let is_valid = LPI.validate_u8 input poffset;
    if is_valid {
      let off = !poffset;
      let z = LPS.read_from_validator_success r_u8 input offset_val off;
      if (U8.lt z 128uy) {
        poffset := offset_val;
        false
      } else {
        true
      }
    } else {
      false
    }
  } else {
    let len = U8.sub x 128uy;
    let offset_val = !poffset;
    if (U8.eq len 2uy) {
      let is_valid = LPS.validate_total_constant_size (parse_bounded_integer 2) 2sz input poffset;
      if is_valid {
        let off = !poffset;
        let y = LPS.read_from_validator_success (r_bi 2) input offset_val off;
        if (U32.lt y 256ul) {
          poffset := offset_val;
          false
        } else {
          true
        }
      } else {
        false
      }
    } else if (U8.eq len 3uy) {
      let is_valid = LPS.validate_total_constant_size (parse_bounded_integer 3) 3sz input poffset;
      if is_valid {
        let off = !poffset;
        let y = LPS.read_from_validator_success (r_bi 3) input offset_val off;
        if (U32.lt y 65536ul) {
          poffset := offset_val;
          false
        } else {
          true
        }
      } else {
        false
      }
    } else {
      let is_valid = LPS.validate_total_constant_size (parse_bounded_integer 4) 4sz input poffset;
      if is_valid {
        let off = !poffset;
        let y = LPS.read_from_validator_success (r_bi 4) input offset_val off;
        if (U32.lt y 16777216ul) {
          poffset := offset_val;
          false
        } else {
          true
        }
      } else {
        false
      }
    }
  }
}

inline_for_extraction
fn validate_bounded_der_length32
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max })
  (r_u8: LPS.leaf_reader serialize_u8)
  (r_bi: (i: integer_size) -> LPS.leaf_reader (serialize_bounded_integer i))
: LPS.validator (parse_bounded_der_length32 (U32.v min) (U32.v max))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_der_length32_unfold (U32.v min) (U32.v max) sinput;
  let offset_val = !poffset;
  let is_valid_tag = LPI.validate_u8 input poffset;
  if is_valid_tag {
    let off1 = !poffset;
    let x = LPS.read_from_validator_success r_u8 input offset_val off1;
    let len = der_length_payload_size_of_tag8 x;
    let tg1 = tag_of_der_length32_impl min;
    let l1 = der_length_payload_size_of_tag8 tg1;
    let tg2 = tag_of_der_length32_impl max;
    let l2 = der_length_payload_size_of_tag8 tg2;
    if (U8.lt len l1 || U8.lt l2 len) {
      poffset := offset_val;
      false
    } else {
      let sinput2 = Ghost.hide (Seq.slice v (SZ.v off1) (Seq.length v));
      parse_der_length_payload32_unfold x sinput2;
      assert_norm (pow2 8 == 256);
      assert_norm (pow2 16 == 65536);
      assert_norm (pow2 24 == 16777216);
      assert_norm (pow2 32 == 4294967296);
      if (U8.lt x 128uy) {
        let y = Cast.uint8_to_uint32 x;
        if (U32.lt y min || U32.lt max y) {
          poffset := offset_val;
          false
        } else {
          true
        }
      } else if (x = 128uy || x = 255uy) {
        poffset := offset_val;
        false
      } else if (x = 129uy) {
        let is_valid2 = LPI.validate_u8 input poffset;
        if is_valid2 {
          let off2 = !poffset;
          let z = LPS.read_from_validator_success r_u8 input off1 off2;
          if (U8.lt z 128uy || U32.lt (Cast.uint8_to_uint32 z) min || U32.lt max (Cast.uint8_to_uint32 z)) {
            poffset := offset_val;
            false
          } else {
            true
          }
        } else {
          poffset := offset_val;
          false
        }
      } else {
        if (U8.eq len 2uy) {
          let is_valid2 = LPS.validate_total_constant_size (parse_bounded_integer 2) 2sz input poffset;
          if is_valid2 {
            let off2 = !poffset;
            let y = LPS.read_from_validator_success (r_bi 2) input off1 off2;
            if (U32.lt y 256ul || U32.lt y min || U32.lt max y) {
              poffset := offset_val;
              false
            } else {
              true
            }
          } else {
            poffset := offset_val;
            false
          }
        } else if (U8.eq len 3uy) {
          let is_valid2 = LPS.validate_total_constant_size (parse_bounded_integer 3) 3sz input poffset;
          if is_valid2 {
            let off2 = !poffset;
            let y = LPS.read_from_validator_success (r_bi 3) input off1 off2;
            if (U32.lt y 65536ul || U32.lt y min || U32.lt max y) {
              poffset := offset_val;
              false
            } else {
              true
            }
          } else {
            poffset := offset_val;
            false
          }
        } else {
          let is_valid2 = LPS.validate_total_constant_size (parse_bounded_integer 4) 4sz input poffset;
          if is_valid2 {
            let off2 = !poffset;
            let y = LPS.read_from_validator_success (r_bi 4) input off1 off2;
            if (U32.lt y 16777216ul || U32.lt y min || U32.lt max y) {
              poffset := offset_val;
              false
            } else {
              true
            }
          } else {
            poffset := offset_val;
            false
          }
        }
      }
    }
  } else {
    false
  }
}

#pop-options

#push-options "--z3rlimit 32"

module PPB = LowParse.PulseParse.Base

inline_for_extraction
fn jump_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 })
: LPS.jumper (parse_der_length_payload32 x)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_der_length_payload32_unfold x sinput;
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  pts_to_len input;
  if (U8.lt x 128uy) {
    offset
  } else {
    let len = U8.sub x 128uy;
    parser_kind_prop_equiv parse_u8_kind parse_u8;
    parser_kind_prop_equiv (parse_bounded_integer_kind (U8.v len)) (parse_bounded_integer (U8.v len));
    if (U8.eq len 1uy) { SZ.add offset 1sz }
    else if (U8.eq len 2uy) { SZ.add offset 2sz }
    else if (U8.eq len 3uy) { SZ.add offset 3sz }
    else { SZ.add offset 4sz }
  }
}

inline_for_extraction
fn jump_bounded_der_length32
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (r_u8: PPB.leaf_reader parse_u8)
: LPS.jumper (parse_bounded_der_length32 vmin vmax)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_der_length32_unfold vmin vmax sinput;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  pts_to_len input;
  let off1 = LPI.jump_u8 input offset;
  let x = PPB.read_parsed_from_validator_success r_u8 input offset off1;
  let _len = der_length_payload_size_of_tag8 x;
  Seq.lemma_eq_elim
    (Seq.slice sinput (SZ.v off1 - SZ.v offset) (Seq.length sinput))
    (Seq.slice v (SZ.v off1) (Seq.length v));
  jump_der_length_payload32 x input off1
}

#pop-options

(* leaf_reader for parse_bounded_der_length32 *)

module LPI = LowParse.Pulse.Int
module PPBI = LowParse.PulseParse.BoundedInt

#push-options "--z3rlimit 64"

inline_for_extraction
fn leaf_read_bounded_der_length32
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (r_u8: PPB.leaf_reader parse_u8)
  (r_bi: (i: integer_size) -> Tot (PPB.leaf_reader (parse_bounded_integer i)))
: PPB.leaf_reader (parse_bounded_der_length32 vmin vmax)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (bounded_int32 vmin vmax))
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_bounded_der_length32_unfold vmin vmax w;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  S.pts_to_len input;
  let x = PPB.read_parsed_from_validator_success r_u8 input 0sz 1sz;
  Seq.lemma_eq_elim (Seq.slice w 1 (Seq.length w)) (Seq.slice w 1 (Seq.length w));
  parse_der_length_payload32_unfold x (Seq.slice w 1 (Seq.length w));
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  if (U8.lt x 128uy) {
    Trade.elim _ _;
    Cast.uint8_to_uint32 x
  } else if (U8.eq x 129uy) {
    parser_kind_prop_equiv parse_u8_kind parse_u8;
    let y = PPB.read_parsed_from_validator_success r_u8 input 1sz 2sz;
    Trade.elim _ _;
    Cast.uint8_to_uint32 y
  } else if (U8.eq x 130uy) {
    parser_kind_prop_equiv (parse_bounded_integer_kind 2) (parse_bounded_integer 2);
    let y = PPB.read_parsed_from_validator_success (r_bi 2) input 1sz 3sz;
    Trade.elim _ _;
    y
  } else if (U8.eq x 131uy) {
    parser_kind_prop_equiv (parse_bounded_integer_kind 3) (parse_bounded_integer 3);
    let y = PPB.read_parsed_from_validator_success (r_bi 3) input 1sz 4sz;
    Trade.elim _ _;
    y
  } else {
    parser_kind_prop_equiv (parse_bounded_integer_kind 4) (parse_bounded_integer 4);
    let y = PPB.read_parsed_from_validator_success (r_bi 4) input 1sz 5sz;
    Trade.elim _ _;
    y
  }
}

#pop-options

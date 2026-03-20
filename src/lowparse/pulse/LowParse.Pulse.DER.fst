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

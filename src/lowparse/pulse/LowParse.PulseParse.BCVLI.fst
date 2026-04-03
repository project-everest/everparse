module LowParse.PulseParse.BCVLI
#lang-pulse
include LowParse.Spec.BCVLI
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module U32 = FStar.UInt32

#push-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false --max_fuel 0"

inline_for_extraction
fn validate_bcvli
  (r1: PPB.leaf_reader (parse_bounded_integer_le 1))
  (r2: PPB.leaf_reader (parse_bounded_integer_le 2))
  (r4: PPB.leaf_reader (parse_bounded_integer_le 4))
: LPS.validator parse_bcvli
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bcvli_eq sinput;
  let offset_val = !poffset;
  let is_valid_1 = LPS.validate_total_constant_size (parse_bounded_integer_le 1) 1sz input poffset;
  if is_valid_1 {
    let off1 = !poffset;
    let x = PPB.read_parsed_from_validator_success r1 input offset_val off1;
    Seq.lemma_eq_elim
      (Seq.slice sinput (SZ.v off1 - SZ.v offset_val) (Seq.length sinput))
      (Seq.slice v (SZ.v off1) (Seq.length v));
    if (U32.lt x 253ul) {
      true
    } else if (x = 253ul) {
      let is_valid_2 = LPS.validate_total_constant_size (parse_bounded_integer_le 2) 2sz input poffset;
      if is_valid_2 {
        let off2 = !poffset;
        let y = PPB.read_parsed_from_validator_success r2 input off1 off2;
        if (U32.lt y 253ul) {
          poffset := offset_val;
          false
        } else {
          true
        }
      } else {
        poffset := offset_val;
        false
      }
    } else if (x = 254ul) {
      let is_valid_4 = LPS.validate_total_constant_size (parse_bounded_integer_le 4) 4sz input poffset;
      if is_valid_4 {
        let off2 = !poffset;
        let y = PPB.read_parsed_from_validator_success r4 input off1 off2;
        if (U32.lt y 65536ul) {
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
      poffset := offset_val;
      false
    }
  } else {
    false
  }
}

inline_for_extraction
fn validate_bounded_bcvli
  (min32: U32.t)
  (max32: U32.t { U32.v min32 <= U32.v max32 })
  (r1: PPB.leaf_reader (parse_bounded_integer_le 1))
  (r2: PPB.leaf_reader (parse_bounded_integer_le 2))
  (r4: PPB.leaf_reader (parse_bounded_integer_le 4))
: LPS.validator (parse_bounded_bcvli (U32.v min32) (U32.v max32))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_bcvli_eq (U32.v min32) (U32.v max32) sinput;
  parse_bcvli_eq sinput;
  let offset_val = !poffset;
  let is_valid_1 = LPS.validate_total_constant_size (parse_bounded_integer_le 1) 1sz input poffset;
  if is_valid_1 {
    let off1 = !poffset;
    let x = PPB.read_parsed_from_validator_success r1 input offset_val off1;
    Seq.lemma_eq_elim
      (Seq.slice sinput (SZ.v off1 - SZ.v offset_val) (Seq.length sinput))
      (Seq.slice v (SZ.v off1) (Seq.length v));
    if (U32.lt x 253ul && U32.lte min32 x && U32.lte x max32) {
      true
    } else if (U32.lt max32 253ul) {
      poffset := offset_val;
      false
    } else if (x = 253ul) {
      if (U32.lte 65536ul min32) {
        poffset := offset_val;
        false
      } else {
        let is_valid_2 = LPS.validate_total_constant_size (parse_bounded_integer_le 2) 2sz input poffset;
        if is_valid_2 {
          let off2 = !poffset;
          let y = PPB.read_parsed_from_validator_success r2 input off1 off2;
          if (U32.lt y 253ul || U32.lt y min32 || U32.lt max32 y) {
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
    } else if (U32.lt max32 65536ul) {
      poffset := offset_val;
      false
    } else if (x = 254ul) {
      let is_valid_4 = LPS.validate_total_constant_size (parse_bounded_integer_le 4) 4sz input poffset;
      if is_valid_4 {
        let off2 = !poffset;
        let y = PPB.read_parsed_from_validator_success r4 input off1 off2;
        if (U32.lt y 65536ul || U32.lt y min32 || U32.lt max32 y) {
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
      poffset := offset_val;
      false
    }
  } else {
    false
  }
}

#pop-options

#push-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false --max_fuel 0"

inline_for_extraction
fn jump_bcvli
  (r1: PPB.leaf_reader (parse_bounded_integer_le 1))
: LPS.jumper parse_bcvli
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bcvli_eq sinput;
  parser_kind_prop_equiv (parse_bounded_integer_kind 1) (parse_bounded_integer_le 1);
  pts_to_len input;
  let off1 = SZ.add offset 1sz;
  let x = PPB.read_parsed_from_validator_success r1 input offset off1;
  Seq.lemma_eq_elim
    (Seq.slice sinput (SZ.v off1 - SZ.v offset) (Seq.length sinput))
    (Seq.slice v (SZ.v off1) (Seq.length v));
  if (U32.lt x 253ul) {
    off1
  } else if (x = 253ul) {
    parser_kind_prop_equiv (parse_bounded_integer_kind 2) (parse_bounded_integer_le 2);
    SZ.add off1 2sz
  } else {
    parser_kind_prop_equiv (parse_bounded_integer_kind 4) (parse_bounded_integer_le 4);
    SZ.add off1 4sz
  }
}

inline_for_extraction
fn jump_bounded_bcvli
  (min: Ghost.erased nat)
  (max: Ghost.erased nat { min <= max })
  (r1: PPB.leaf_reader (parse_bounded_integer_le 1))
: LPS.jumper (parse_bounded_bcvli min max)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_bcvli_eq min max sinput;
  parse_bcvli_eq sinput;
  jump_bcvli r1 input offset
}

#pop-options

(* leaf_reader for parse_bcvli *)

#push-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false --max_fuel 0"

inline_for_extraction
fn leaf_read_bcvli
  (r1: PPB.leaf_reader (parse_bounded_integer_le 1))
  (r2: PPB.leaf_reader (parse_bounded_integer_le 2))
  (r4: PPB.leaf_reader (parse_bounded_integer_le 4))
: PPB.leaf_reader parse_bcvli
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased U32.t)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_bcvli_eq w;
  parser_kind_prop_equiv (parse_bounded_integer_kind 1) (parse_bounded_integer_le 1);
  S.pts_to_len input;
  let x = PPB.read_parsed_from_validator_success r1 input 0sz 1sz;
  Seq.lemma_eq_elim
    (Seq.slice w 1 (Seq.length w))
    (Seq.slice w 1 (Seq.length w));
  if (U32.lt x 253ul) {
    Trade.elim _ _;
    x
  } else if (U32.eq x 253ul) {
    parser_kind_prop_equiv (parse_bounded_integer_kind 2) (parse_bounded_integer_le 2);
    let y = PPB.read_parsed_from_validator_success r2 input 1sz 3sz;
    Trade.elim _ _;
    y
  } else {
    parser_kind_prop_equiv (parse_bounded_integer_kind 4) (parse_bounded_integer_le 4);
    let y = PPB.read_parsed_from_validator_success r4 input 1sz 5sz;
    Trade.elim _ _;
    y
  }
}

#pop-options

(* leaf_reader for parse_bounded_bcvli *)

#push-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false --max_fuel 0"

inline_for_extraction
fn leaf_read_bounded_bcvli
  (min: nat)
  (max: nat { min <= max })
  (r1: PPB.leaf_reader (parse_bounded_integer_le 1))
  (r2: PPB.leaf_reader (parse_bounded_integer_le 2))
  (r4: PPB.leaf_reader (parse_bounded_integer_le 4))
: PPB.leaf_reader (parse_bounded_bcvli min max)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (bounded_int32 min max))
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_bounded_bcvli_eq min max w;
  parse_bcvli_eq w;
  parser_kind_prop_equiv (parse_bounded_integer_kind 1) (parse_bounded_integer_le 1);
  S.pts_to_len input;
  let x = PPB.read_parsed_from_validator_success r1 input 0sz 1sz;
  Seq.lemma_eq_elim
    (Seq.slice w 1 (Seq.length w))
    (Seq.slice w 1 (Seq.length w));
  if (U32.lt x 253ul) {
    Trade.elim _ _;
    x
  } else if (U32.eq x 253ul) {
    parser_kind_prop_equiv (parse_bounded_integer_kind 2) (parse_bounded_integer_le 2);
    let y = PPB.read_parsed_from_validator_success r2 input 1sz 3sz;
    Trade.elim _ _;
    y
  } else {
    parser_kind_prop_equiv (parse_bounded_integer_kind 4) (parse_bounded_integer_le 4);
    let y = PPB.read_parsed_from_validator_success r4 input 1sz 5sz;
    Trade.elim _ _;
    y
  }
}

#pop-options

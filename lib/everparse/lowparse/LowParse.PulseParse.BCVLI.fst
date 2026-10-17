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
module LPC = LowParse.Pulse.Combinators
module LPPILE = LowParse.Pulse.BoundedIntLE

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

(* ----- l2r leaf writer and runtime size for BCVLI ----- *)

#push-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false"

let serialize_bcvli_length (x: U32.t) : Lemma
  (Seq.length (serialize serialize_bcvli x) ==
    (if U32.v x <= 252 then 1 else if U32.v x <= 65535 then 3 else 5))
= serialize_bcvli_eq x;
  let c1 : bounded_integer 1 =
    if U32.v x <= 252 then x else if U32.v x <= 65535 then 253ul else 254ul
  in
  let body : bytes =
    if U32.v c1 <= 252 then Seq.empty #byte else
    if U32.v c1 = 253 then serialize (serialize_bounded_integer_le 2) x else
    serialize (serialize_bounded_integer_le 4) x
  in
  LPPILE.serialize_bounded_integer_le_length 1 c1;
  Seq.lemma_len_append (serialize (serialize_bounded_integer_le 1) c1) body;
  if U32.v x <= 252 then ()
  else if U32.v x <= 65535 then LPPILE.serialize_bounded_integer_le_length 2 x
  else LPPILE.serialize_bounded_integer_le_length 4 x

#pop-options

#push-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false --max_fuel 0"

let bcvli_size (x: U32.t)
: (sz: SZ.t { SZ.v sz == Seq.length (serialize serialize_bcvli x) /\ SZ.v sz < pow2 64 })
= serialize_bcvli_length x;
  assert_norm (SZ.v 1sz == 1);
  assert_norm (SZ.v 3sz == 3);
  assert_norm (SZ.v 5sz == 5);
  assert_norm (5 < pow2 64);
  if U32.lte x 252ul then 1sz
  else if U32.lte x 65535ul then 3sz
  else 5sz

inline_for_extraction
let bounded_bcvli_size (min: nat) (max: nat { min <= max }) (x: bounded_int32 min max { max < 4294967296 })
: (sz: SZ.t { SZ.v sz == Seq.length (serialize (serialize_bounded_bcvli min max) x) /\ SZ.v sz < pow2 64 })
= serialize_bounded_bcvli_eq min max x;
  bcvli_size x

#pop-options

#push-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"

inline_for_extraction
fn l2r_leaf_write_bcvli (_: unit) : LPS.l2r_leaf_writer serialize_bcvli
= (x: U32.t)
  (out: S.slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len out;
  serialize_bcvli_length x;
  serialize_bcvli_eq x;
  let c1 : bounded_integer 1 = (if U32.lte x 252ul then x else if U32.lte x 65535ul then 253ul else 254ul);
  LPPILE.serialize_bounded_integer_le_length 1 c1;
  let off1 = LPPILE.l2r_leaf_write_bounded_integer_le 1 1sz c1 out offset;
  with v1. assert (pts_to out v1);
  if (U32.lte x 252ul) {
    Seq.append_empty_r (serialize (serialize_bounded_integer_le 1) c1);
    Seq.lemma_eq_intro (Seq.slice v1 (SZ.v offset) (SZ.v off1)) (serialize serialize_bcvli x);
    off1
  } else if (U32.lte x 65535ul) {
    LPPILE.serialize_bounded_integer_le_length 2 x;
    let off2 = LPPILE.l2r_leaf_write_bounded_integer_le 2 2sz x out off1;
    with v2. assert (pts_to out v2);
    assert (pure (Seq.slice v2 0 (SZ.v off1) == Seq.slice v1 0 (SZ.v off1)));
    assert (pure (Seq.slice v1 (SZ.v offset) (SZ.v off1) == serialize (serialize_bounded_integer_le 1) c1));
    assert (pure (Seq.slice v2 (SZ.v off1) (SZ.v off2) == serialize (serialize_bounded_integer_le 2) x));
    Seq.slice_slice v2 0 (SZ.v off1) (SZ.v offset) (SZ.v off1);
    Seq.lemma_split (Seq.slice v2 (SZ.v offset) (SZ.v off2)) (SZ.v off1 - SZ.v offset);
    Seq.slice_slice v2 (SZ.v offset) (SZ.v off2) 0 (SZ.v off1 - SZ.v offset);
    Seq.slice_slice v2 (SZ.v offset) (SZ.v off2) (SZ.v off1 - SZ.v offset) (SZ.v off2 - SZ.v offset);
    Seq.lemma_eq_intro (Seq.slice v2 (SZ.v offset) (SZ.v off2)) (serialize serialize_bcvli x);
    Seq.slice_slice v2 0 (SZ.v off1) 0 (SZ.v offset);
    Seq.slice_slice v1 0 (SZ.v off1) 0 (SZ.v offset);
    off2
  } else {
    LPPILE.serialize_bounded_integer_le_length 4 x;
    let off2 = LPPILE.l2r_leaf_write_bounded_integer_le 4 4sz x out off1;
    with v2. assert (pts_to out v2);
    assert (pure (Seq.slice v2 0 (SZ.v off1) == Seq.slice v1 0 (SZ.v off1)));
    assert (pure (Seq.slice v1 (SZ.v offset) (SZ.v off1) == serialize (serialize_bounded_integer_le 1) c1));
    assert (pure (Seq.slice v2 (SZ.v off1) (SZ.v off2) == serialize (serialize_bounded_integer_le 4) x));
    Seq.slice_slice v2 0 (SZ.v off1) (SZ.v offset) (SZ.v off1);
    Seq.lemma_split (Seq.slice v2 (SZ.v offset) (SZ.v off2)) (SZ.v off1 - SZ.v offset);
    Seq.slice_slice v2 (SZ.v offset) (SZ.v off2) 0 (SZ.v off1 - SZ.v offset);
    Seq.slice_slice v2 (SZ.v offset) (SZ.v off2) (SZ.v off1 - SZ.v offset) (SZ.v off2 - SZ.v offset);
    Seq.lemma_eq_intro (Seq.slice v2 (SZ.v offset) (SZ.v off2)) (serialize serialize_bcvli x);
    Seq.slice_slice v2 0 (SZ.v off1) 0 (SZ.v offset);
    Seq.slice_slice v1 0 (SZ.v off1) 0 (SZ.v offset);
    off2
  }
}

inline_for_extraction
fn l2r_leaf_write_bounded_bcvli
  (min max: nat)
  (sq: squash (min <= max /\ max < 4294967296))
: LPS.l2r_leaf_writer (serialize_bounded_bcvli min max)
= (x: bounded_int32 min max)
  (out: S.slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  serialize_bounded_bcvli_eq min max x;
  l2r_leaf_write_bcvli () x out offset
}

#pop-options

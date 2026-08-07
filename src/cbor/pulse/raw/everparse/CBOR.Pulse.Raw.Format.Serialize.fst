module CBOR.Pulse.Raw.Format.Serialize
friend CBOR.Spec.Raw.Format
friend CBOR.Pulse.Raw.Format.Match
include CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Format
open Pulse.Lib.Trade
module U8 = FStar.UInt8
module S = Pulse.Lib.Slice
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.Base
open LowParse.Pulse.Base

open CBOR.Pulse.Raw.Match
module LP = LowParse.Pulse.Combinators
module LPI = LowParse.Pulse.Int

inline_for_extraction
let write_initial_byte' : l2r_leaf_writer serialize_initial_byte_t =
  l2r_leaf_writer_ext
    (LP.l2r_leaf_write_synth'
      (LowParse.Pulse.BitSum.l2r_write_bitsum'
        mk_synth_initial_byte
        (LPI.l2r_leaf_write_u8 ())
      )
      synth_initial_byte
      synth_initial_byte_recip
    )
    _

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_initial_byte : l2r_leaf_writer serialize_initial_byte =
  LP.l2r_leaf_write_filter
    write_initial_byte'
    initial_byte_wf

inline_for_extraction
let size_initial_byte : leaf_compute_remaining_size serialize_initial_byte =
  leaf_compute_remaining_size_constant_size _ 1sz

inline_for_extraction
let write_long_argument_8_simple_value
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
  (sq2: squash ((b.major_type = cbor_major_type_simple_value) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
          l2r_leaf_writer_ext
            (LP.l2r_leaf_write_synth'
              (LP.l2r_leaf_write_filter
                (LPI.l2r_leaf_write_u8 ())
                simple_value_long_argument_wf
              )
              (LongArgumentSimpleValue #b ())
              (LongArgumentSimpleValue?.v)
            )
            (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_8_not_simple_value
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
  (sq2: squash ((b.major_type = cbor_major_type_simple_value) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (LP.l2r_leaf_write_synth'
                  (LPI.l2r_leaf_write_u8 ())
                  (LongArgumentU8 #b ())
                  (LongArgumentU8?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_8
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
    (serialize_long_argument b)
    (b.major_type = cbor_major_type_simple_value)
    (write_long_argument_8_simple_value b sq1)
    (write_long_argument_8_not_simple_value b sq1)

#restart-solver

inline_for_extraction
noextract [@@noextract_to "krml"]
let size_long_argument_8
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
: Tot (leaf_compute_remaining_size (serialize_long_argument b))
= leaf_compute_remaining_size_ext
    (leaf_compute_remaining_size_constant_size _ 1sz <: leaf_compute_remaining_size #(long_argument b) #_ #(if b.major_type = cbor_major_type_simple_value then LP.parse_synth (LP.parse_filter LPI.parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b ()) else weaken (LP.parse_filter_kind LPI.parse_u8_kind) (LP.parse_synth LPI.parse_u8 (LongArgumentU8 #b ()))) (if b.major_type = cbor_major_type_simple_value then LP.serialize_synth _ (LongArgumentSimpleValue #b ())  (LP.serialize_filter LPI.serialize_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue?.v) () else LP.serialize_weaken (LP.parse_filter_kind LPI.parse_u8_kind) (LP.serialize_synth _ (LongArgumentU8 #b ()) LPI.serialize_u8 (LongArgumentU8?.v) ())))
    _

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_16
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_16_bits) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (LP.l2r_leaf_write_synth'
                  (LPI.l2r_leaf_write_u16 ())
                  (LongArgumentU16 #b ())
                  (LongArgumentU16?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let size_long_argument_16
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_16_bits) == true))
: Tot (leaf_compute_remaining_size (serialize_long_argument b))
=
              leaf_compute_remaining_size_ext
                (leaf_compute_remaining_size_constant_size (LP.serialize_synth _ (LongArgumentU16 #b ()) LPI.serialize_u16 (LongArgumentU16?.v) ()) 2sz)
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_32
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_32_bits) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (LP.l2r_leaf_write_synth'
                  (LPI.l2r_leaf_write_u32 ())
                  (LongArgumentU32 #b ())
                  (LongArgumentU32?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let size_long_argument_32
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_32_bits) == true))
: Tot (leaf_compute_remaining_size (serialize_long_argument b))
=
              leaf_compute_remaining_size_ext
                (leaf_compute_remaining_size_constant_size (LP.serialize_synth _ (LongArgumentU32 #b ()) LPI.serialize_u32 (LongArgumentU32?.v) ()) 4sz)
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_64
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_64_bits) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (LP.l2r_leaf_write_synth'
                  (LPI.l2r_leaf_write_u64 ())
                  (LongArgumentU64 #b ())
                  (LongArgumentU64?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let size_long_argument_64
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_64_bits) == true))
: Tot (leaf_compute_remaining_size (serialize_long_argument b))
=
              leaf_compute_remaining_size_ext
                (leaf_compute_remaining_size_constant_size (LP.serialize_synth _ (LongArgumentU64 #b ()) LPI.serialize_u64 (LongArgumentU64?.v) ()) 8sz)
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_other
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
  (sq64: squash ((b.additional_info = additional_info_long_argument_64_bits) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (l2r_leaf_writer_zero_size
                  (LP.serialize_synth _ (LongArgumentOther #b ()) LP.serialize_empty LongArgumentOther?.v ())
                  ()
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let size_long_argument_other
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
  (sq64: squash ((b.additional_info = additional_info_long_argument_64_bits) == false))
: Tot (leaf_compute_remaining_size (serialize_long_argument b))
=
              leaf_compute_remaining_size_ext
                (leaf_compute_remaining_size_zero_size
                  (LP.serialize_synth _ (LongArgumentOther #b ()) LP.serialize_empty LongArgumentOther?.v ())
                  ()
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_not_8_16_32
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_64_bits)
    (write_long_argument_64 b)
    (write_long_argument_other b sq8 sq16 sq32)

inline_for_extraction
noextract [@@noextract_to "krml"]
let size_long_argument_not_8_16_32
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
: Tot (leaf_compute_remaining_size (serialize_long_argument b))
= leaf_compute_remaining_size_ifthenelse
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_64_bits)
    (size_long_argument_64 b)
    (size_long_argument_other b sq8 sq16 sq32)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_not_8_16
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_32_bits)
    (write_long_argument_32 b)
    (write_long_argument_not_8_16_32 b sq8 sq16)

inline_for_extraction
noextract [@@noextract_to "krml"]
let size_long_argument_not_8_16
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
: Tot (leaf_compute_remaining_size (serialize_long_argument b))
= leaf_compute_remaining_size_ifthenelse
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_32_bits)
    (size_long_argument_32 b)
    (size_long_argument_not_8_16_32 b sq8 sq16)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_not_8
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_16_bits)
    (write_long_argument_16 b)
    (write_long_argument_not_8_16 b sq8)

inline_for_extraction
noextract [@@noextract_to "krml"]
let size_long_argument_not_8
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
: Tot (leaf_compute_remaining_size (serialize_long_argument b))
= leaf_compute_remaining_size_ifthenelse
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_16_bits)
    (size_long_argument_16 b)
    (size_long_argument_not_8_16 b sq8)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument
  (b: initial_byte)
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
      (serialize_long_argument b)
      (b.additional_info = additional_info_long_argument_8_bits)
      (write_long_argument_8 b)
      (write_long_argument_not_8 b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let size_long_argument
  (b: initial_byte)
: Tot (leaf_compute_remaining_size (serialize_long_argument b))
= leaf_compute_remaining_size_ifthenelse
      (serialize_long_argument b)
      (b.additional_info = additional_info_long_argument_8_bits)
      (size_long_argument_8 b)
      (size_long_argument_not_8 b)

let write_header : l2r_leaf_writer serialize_header =
  l2r_leaf_writer_ext
    (LP.l2r_leaf_write_dtuple2
      write_initial_byte
      ()
      write_long_argument
    )
    _

let size_header : leaf_compute_remaining_size serialize_header =
  leaf_compute_remaining_size_ext
    (LP.leaf_compute_remaining_size_dtuple2
      size_initial_byte
      ()
      size_long_argument
    )
    _

module SZ = FStar.SizeT
module PM = Pulse.Lib.SeqMatch

let cbor_match_with_perm
  (x: with_perm cbor_raw)
  (y: raw_data_item)
: Tot slprop
= cbor_match x.p x.v y

module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
fn cbor_match_with_perm_lens
  (p: perm)
: vmatch_lens #_ #_ #_ (cbor_match p) cbor_match_with_perm
=
  (x: cbor_raw)
  (y: raw_data_item)
{
  let res : with_perm cbor_raw = {
    v = x;
    p = p;
  };
  Trade.rewrite_with_trade
    (cbor_match p x y)
    (cbor_match_with_perm res y);
  res
}

#push-options "--z3rlimit 64"

fn cbor_raw_get_header
  (p: perm)
  (xl: cbor_raw)
  (xh: erased raw_data_item)
requires
      (cbor_match p xl xh)
returns res: header
ensures
          cbor_match p xl xh **
          pure (res == get_raw_data_item_header xh)
{
  cbor_match_cases xl;
  match xl {
    norewrite
    CBOR_Case_Int _ -> {
      let ty = cbor_match_int_elim_type xl;
      let v = cbor_match_int_elim_value xl;
      raw_uint64_as_argument ty v
    }
    norewrite
    CBOR_Case_String _ -> {
      let ty = cbor_match_string_elim_type xl;
      let len = cbor_match_string_elim_length xl;
      raw_uint64_as_argument ty len
    }
    norewrite
    CBOR_Case_Tagged _ -> {
      let tag = cbor_match_tagged_get_tag xl;
      raw_uint64_as_argument cbor_major_type_tagged tag
    }
    norewrite
    CBOR_Case_Serialized_Tagged _ -> {
      let tag = cbor_match_tagged_get_tag xl;
      raw_uint64_as_argument cbor_major_type_tagged tag
    }
    norewrite
    CBOR_Case_Array _ -> {
      let len = cbor_match_array_get_length xl;
      raw_uint64_as_argument cbor_major_type_array len
    }
    norewrite
    CBOR_Case_Serialized_Array _ -> {
      let len = cbor_match_array_get_length xl;
      raw_uint64_as_argument cbor_major_type_array len
    }
    norewrite
    CBOR_Case_Map _ -> {
      let len = cbor_match_map_get_length xl;
      raw_uint64_as_argument cbor_major_type_map len
    }
    norewrite
    CBOR_Case_Serialized_Map _ -> {
      let len = cbor_match_map_get_length xl;
      raw_uint64_as_argument cbor_major_type_map len
    }
    norewrite
    CBOR_Case_Simple _ -> {
      let v = cbor_match_simple_elim xl;
      simple_value_as_argument v
    }
  }
}

#pop-options

fn cbor_raw_with_perm_get_header
  (xl: with_perm cbor_raw)
  (xh: erased raw_data_item)
requires
      (cbor_match_with_perm xl xh)
returns res: header
ensures
          cbor_match_with_perm xl xh **
          pure (res == get_raw_data_item_header xh)
{
  unfold (cbor_match_with_perm xl xh);
  let res = cbor_raw_get_header xl.p xl.v xh;
  fold (cbor_match_with_perm xl xh);
  res
}

let synth_raw_data_item_recip_synth_raw_data_item
  (x: _)
: Lemma
  (synth_raw_data_item_recip (synth_raw_data_item x) == x)
= assert (synth_raw_data_item (synth_raw_data_item_recip (synth_raw_data_item x)) == synth_raw_data_item x)

inline_for_extraction
fn cbor_raw_get_header'
  (xl: with_perm cbor_raw)
  (xh: erased (dtuple2 header content))
requires
      (LP.vmatch_synth (cbor_match_with_perm) synth_raw_data_item xl (reveal xh))
returns res: header
ensures
          LP.vmatch_synth (cbor_match_with_perm) synth_raw_data_item xl (reveal xh) **
          pure (res == dfst (reveal xh))
{
  synth_raw_data_item_recip_synth_raw_data_item xh;
  unfold (LP.vmatch_synth (cbor_match_with_perm) synth_raw_data_item xl (reveal xh));
  let res = cbor_raw_with_perm_get_header xl _;
  fold (LP.vmatch_synth (cbor_match_with_perm) synth_raw_data_item xl (reveal xh));
  res
}

let match_cbor_payload
  (xh1: header)
=
        (LP.vmatch_dep_proj2
            (LP.vmatch_synth
                (cbor_match_with_perm)
                synth_raw_data_item
            )
            xh1
        )

module U64 = FStar.UInt64

ghost
fn match_cbor_payload_elim_trade
  (xh1: header)
  (xl: with_perm cbor_raw)
  (xh: content xh1)
requires
  match_cbor_payload xh1 xl xh
returns xh': Ghost.erased raw_data_item
ensures
  (cbor_match_with_perm xl xh' **
    Trade.trade
      (cbor_match_with_perm xl xh')
      (match_cbor_payload xh1 xl xh) **
      pure (synth_raw_data_item_recip xh' == (| xh1, xh |))
  )
{
  Trade.rewrite_with_trade
    (match_cbor_payload xh1 xl xh)
    (cbor_match_with_perm xl (synth_raw_data_item (| xh1, xh |)));
  synth_raw_data_item_recip_synth_raw_data_item (| xh1, xh |);
  synth_raw_data_item (| xh1, xh |)
}

// ============================================================================
// Depth-indexed serialization (EverParse PR 291 style): the depth `n` bounding
// the inline (non-serialized) structure is threaded through the rel/vmatch
// slprop, so the recursive writer/size-computer decreases on the ghost depth:
//   cbor_match_with_perm_d n x y == cbor_match_with_depth n x.p x.v y
// Foundation: a depth-preserving header reader and a depth-indexed payload
// match, mirroring cbor_raw_get_header / cbor_raw_get_header' / match_cbor_payload.
// The small depth header-reading helpers below are local copies (cf. the
// per-module copies in CBOR.Pulse.Raw.{Read,Copy,Compare}).
// ============================================================================

ghost
fn cbor_match_with_depth_cases (n: nat) (p: perm) (c: cbor_raw) (r: raw_data_item)
  requires cbor_match_with_depth n p c r
  ensures cbor_match_with_depth n p c r ** pure (cbor_match_cases_pred c r)
{
  cbor_match_with_depth_eq0 n p c r;
  rewrite (cbor_match_with_depth n p c r) as (cbor_match0 p c r (depth_cb n r));
  cbor_match0_cases p c r (depth_cb n r);
  rewrite (cbor_match0 p c r (depth_cb n r)) as (cbor_match_with_depth n p c r);
}

ghost
fn cbor_match_with_depth_to_match
  (depth: Ghost.erased nat)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p x v **
  pure (~ (CBOR_Case_Array? x \/ CBOR_Case_Map? x \/ CBOR_Case_Tagged? x))
ensures
  cbor_match p x v **
  Trade.trade (cbor_match p x v) (cbor_match_with_depth depth p x v)
{
  cbor_match_with_depth_cases depth p x v;
  match x {
    norewrite
    CBOR_Case_Int ct -> {
      cbor_match_with_depth_eq_match_int depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Simple ct -> {
      cbor_match_with_depth_eq_match_simple depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_String ct -> {
      cbor_match_with_depth_eq_match_string depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Serialized_Array ct -> {
      cbor_match_with_depth_eq_match_ser_array depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Serialized_Map ct -> {
      cbor_match_with_depth_eq_match_ser_map depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Serialized_Tagged ct -> {
      cbor_match_with_depth_eq_match_ser_tagged depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Array ct -> { unreachable () }
    norewrite
    CBOR_Case_Map ct -> { unreachable () }
    norewrite
    CBOR_Case_Tagged ct -> { unreachable () }
  }
}

#push-options "--z3rlimit 64"

fn cbor_match_array_get_length_with_depth
  (depth: Ghost.erased nat) (c: cbor_raw) (#p: perm) (#v: Ghost.erased raw_data_item)
requires cbor_match_with_depth depth p c v ** pure (Array? v)
returns res: raw_uint64
ensures cbor_match_with_depth depth p c v ** pure (Array? v /\ res == Array?.len v)
{
  cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Array a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
      cbor_match_with_depth_array_elim depth p a v;
      let res : raw_uint64 = { size = a.cbor_array_length_size; value = SZ.sizet_to_uint64 (S.len a.cbor_array_ptr) };
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Array a) v) as (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Array a -> {
      cbor_match_with_depth_to_match depth c;
      let res = cbor_match_array_get_length c;
      Trade.elim (cbor_match p c v) (cbor_match_with_depth depth p c v);
      res
    }
  }
}

fn cbor_match_map_get_length_with_depth
  (depth: Ghost.erased nat) (c: cbor_raw) (#p: perm) (#v: Ghost.erased raw_data_item)
requires cbor_match_with_depth depth p c v ** pure (Map? v)
returns res: raw_uint64
ensures cbor_match_with_depth depth p c v ** pure (Map? v /\ res == Map?.len v)
{
  cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Map a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
      cbor_match_with_depth_map_elim depth p a v;
      let res : raw_uint64 = { size = a.cbor_map_length_size; value = SZ.sizet_to_uint64 (S.len a.cbor_map_ptr) };
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Map a) v) as (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Map a -> {
      cbor_match_with_depth_to_match depth c;
      let res = cbor_match_map_get_length c;
      Trade.elim (cbor_match p c v) (cbor_match_with_depth depth p c v);
      res
    }
  }
}

fn cbor_match_tagged_get_tag_with_depth
  (depth: Ghost.erased nat) (c: cbor_raw) (#p: perm) (#v: Ghost.erased raw_data_item)
requires cbor_match_with_depth depth p c v ** pure (Tagged? v)
returns res: raw_uint64
ensures cbor_match_with_depth depth p c v ** pure (Tagged? v /\ res == Tagged?.tag v)
{
  cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Tagged a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
      cbor_match_with_depth_tagged_elim depth p a v;
      let res = a.cbor_tagged_tag;
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v) as (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Tagged a -> {
      cbor_match_with_depth_to_match depth c;
      let res = cbor_match_tagged_get_tag c;
      Trade.elim (cbor_match p c v) (cbor_match_with_depth depth p c v);
      res
    }
  }
}

#pop-options

#push-options "--z3rlimit 64"

fn cbor_raw_get_header_d
  (n: Ghost.erased nat)
  (p: perm)
  (xl: cbor_raw)
  (xh: erased raw_data_item)
requires
      (cbor_match_with_depth n p xl xh)
returns res: header
ensures
          cbor_match_with_depth n p xl xh **
          pure (res == get_raw_data_item_header xh)
{
  cbor_match_with_depth_cases n p xl xh;
  match xl {
    norewrite
    CBOR_Case_Int _ -> {
      cbor_match_with_depth_to_match n xl;
      let ty = cbor_match_int_elim_type xl;
      let v = cbor_match_int_elim_value xl;
      Trade.elim (cbor_match p xl xh) (cbor_match_with_depth n p xl xh);
      raw_uint64_as_argument ty v
    }
    norewrite
    CBOR_Case_String _ -> {
      cbor_match_with_depth_to_match n xl;
      let ty = cbor_match_string_elim_type xl;
      let len = cbor_match_string_elim_length xl;
      Trade.elim (cbor_match p xl xh) (cbor_match_with_depth n p xl xh);
      raw_uint64_as_argument ty len
    }
    norewrite
    CBOR_Case_Tagged _ -> {
      let tag = cbor_match_tagged_get_tag_with_depth n xl;
      raw_uint64_as_argument cbor_major_type_tagged tag
    }
    norewrite
    CBOR_Case_Serialized_Tagged _ -> {
      let tag = cbor_match_tagged_get_tag_with_depth n xl;
      raw_uint64_as_argument cbor_major_type_tagged tag
    }
    norewrite
    CBOR_Case_Array _ -> {
      let len = cbor_match_array_get_length_with_depth n xl;
      raw_uint64_as_argument cbor_major_type_array len
    }
    norewrite
    CBOR_Case_Serialized_Array _ -> {
      let len = cbor_match_array_get_length_with_depth n xl;
      raw_uint64_as_argument cbor_major_type_array len
    }
    norewrite
    CBOR_Case_Map _ -> {
      let len = cbor_match_map_get_length_with_depth n xl;
      raw_uint64_as_argument cbor_major_type_map len
    }
    norewrite
    CBOR_Case_Serialized_Map _ -> {
      let len = cbor_match_map_get_length_with_depth n xl;
      raw_uint64_as_argument cbor_major_type_map len
    }
    norewrite
    CBOR_Case_Simple _ -> {
      cbor_match_with_depth_to_match n xl;
      let v = cbor_match_simple_elim xl;
      Trade.elim (cbor_match p xl xh) (cbor_match_with_depth n p xl xh);
      simple_value_as_argument v
    }
  }
}

#pop-options

let cbor_match_with_perm_d
  (n: nat)
  (x: with_perm cbor_raw)
  (y: raw_data_item)
: Tot slprop
= cbor_match_with_depth n x.p x.v y

inline_for_extraction
fn cbor_match_with_perm_lens_d
  (n: Ghost.erased nat)
  (p: perm)
: vmatch_lens #_ #_ #_ (cbor_match_with_depth n p) (cbor_match_with_perm_d n)
=
  (x: cbor_raw)
  (y: raw_data_item)
{
  let res : with_perm cbor_raw = {
    v = x;
    p = p;
  };
  Trade.rewrite_with_trade
    (cbor_match_with_depth n p x y)
    (cbor_match_with_perm_d n res y);
  res
}

fn cbor_raw_with_perm_get_header_d
  (n: Ghost.erased nat)
  (xl: with_perm cbor_raw)
  (xh: erased raw_data_item)
requires
      (cbor_match_with_perm_d n xl xh)
returns res: header
ensures
          cbor_match_with_perm_d n xl xh **
          pure (res == get_raw_data_item_header xh)
{
  unfold (cbor_match_with_perm_d n xl xh);
  let res = cbor_raw_get_header_d n xl.p xl.v xh;
  fold (cbor_match_with_perm_d n xl xh);
  res
}

inline_for_extraction
fn cbor_raw_get_header'_d
  (n: Ghost.erased nat)
  (xl: with_perm cbor_raw)
  (xh: erased (dtuple2 header content))
requires
      (LP.vmatch_synth (cbor_match_with_perm_d n) synth_raw_data_item xl (reveal xh))
returns res: header
ensures
          LP.vmatch_synth (cbor_match_with_perm_d n) synth_raw_data_item xl (reveal xh) **
          pure (res == dfst (reveal xh))
{
  synth_raw_data_item_recip_synth_raw_data_item xh;
  unfold (LP.vmatch_synth (cbor_match_with_perm_d n) synth_raw_data_item xl (reveal xh));
  let res = cbor_raw_with_perm_get_header_d n xl _;
  fold (LP.vmatch_synth (cbor_match_with_perm_d n) synth_raw_data_item xl (reveal xh));
  res
}

let match_cbor_payload_d
  (n: nat)
  (xh1: header)
=
        (LP.vmatch_dep_proj2
            (LP.vmatch_synth
                (cbor_match_with_perm_d n)
                synth_raw_data_item
            )
            xh1
        )

ghost
fn match_cbor_payload_elim_trade_d
  (n: Ghost.erased nat)
  (xh1: header)
  (xl: with_perm cbor_raw)
  (xh: content xh1)
requires
  match_cbor_payload_d n xh1 xl xh
returns xh': Ghost.erased raw_data_item
ensures
  (cbor_match_with_perm_d n xl xh' **
    Trade.trade
      (cbor_match_with_perm_d n xl xh')
      (match_cbor_payload_d n xh1 xl xh) **
      pure (synth_raw_data_item_recip xh' == (| xh1, xh |))
  )
{
  Trade.rewrite_with_trade
    (match_cbor_payload_d n xh1 xl xh)
    (cbor_match_with_perm_d n xl (synth_raw_data_item (| xh1, xh |)));
  synth_raw_data_item_recip_synth_raw_data_item (| xh1, xh |);
  synth_raw_data_item (| xh1, xh |)
}

// ============================================================================
// Array element-predicate conversions (copied verbatim from
// CBOR.Pulse.Raw.Read.fst:722-838; Serialize.fst does not `open` Read).
// The depth-array elim yields a seq_list_match whose element predicate is the
// REFINED depth callback [(depth_cb depth r) pl]. The generic slice/iterator
// machinery needs the UNREFINED predicate [cbor_match_with_depth (nat_pred
// depth) pl] (and back, via a trade). These four helpers do that conversion.
// NB: `seq_list_match_cons_elim_trade` lives in Pulse.Lib.SeqMatch.Util (not
// in the base Pulse.Lib.SeqMatch that Serialize.fst aliases as PM), so it is
// referenced here through the PMU alias.
// ============================================================================

module PMU = Pulse.Lib.SeqMatch.Util

// Peek the head (if any) to learn that a non-empty container forces depth >= 1.
ghost
fn array_peek
  (depth: Ghost.erased nat)
  (r: raw_data_item { Array? r })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)
ensures
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl) **
    pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  if (Cons? (Array?.v r)) {
    PMU.seq_list_match_cons_elim_trade s (Array?.v r) ((depth_cb d r) pl);
    depth_cb_pos d r pl (Seq.head s) (List.Tot.hd (Array?.v r));
    Trade.elim _ (PM.seq_list_match s (Array?.v r) ((depth_cb d r) pl));
  } else {
    ()
  }
}

ghost
fn array_to_unref
  (depth: Ghost.erased nat)
  (r: raw_data_item { Array? r })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)
ensures
    PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  array_peek depth r pl s;
  ghost fn prf
    (c': cbor_raw)
    (v': raw_data_item { v' << Array?.v r /\ List.Tot.memP v' (Array?.v r) })
    requires (depth_cb d r) pl c' v'
    ensures cbor_match_with_depth (nat_pred d) pl c' v'
  {
    depth_cb_pos d r pl c' v';
    depth_cb_succ d r pl c' v';
    nat_pred_succ d;
    rewrite ((depth_cb d r) pl c' v')
      as (cbor_match_with_depth (nat_pred d) pl c' v');
  };
  seq_list_match_conv s (Array?.v r)
    ((depth_cb d r) pl)
    (cbor_match_with_depth (nat_pred d) pl)
    prf;
}

ghost
fn array_to_ref
  (depth: Ghost.erased nat)
  (r: raw_data_item { Array? r })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1)
ensures
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)
{
  let d = Ghost.reveal depth;
  if (d = 0) {
    PM.seq_list_match_nil_elim s (Array?.v r) (cbor_match_with_depth (nat_pred d) pl);
    PM.seq_list_match_nil_intro s (Array?.v r) ((depth_cb d r) pl);
  } else {
    ghost fn prf
      (c': cbor_raw)
      (v': raw_data_item { v' << Array?.v r /\ List.Tot.memP v' (Array?.v r) })
      requires cbor_match_with_depth (nat_pred d) pl c' v'
      ensures (depth_cb d r) pl c' v'
    {
      depth_cb_succ d r pl c' v';
      nat_pred_succ d;
      rewrite (cbor_match_with_depth (nat_pred d) pl c' v')
        as ((depth_cb d r) pl c' v');
    };
    seq_list_match_conv s (Array?.v r)
      (cbor_match_with_depth (nat_pred d) pl)
      ((depth_cb d r) pl)
      prf;
  }
}

// forward conversion + reverse trade + the depth>=1 fact.
ghost
fn cbor_seq_list_match_depth_to_succ
  (depth: Ghost.erased nat)
  (r: raw_data_item { Array? r })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)
ensures
    PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    Trade.trade
      (PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl))
      (PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)) **
    pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1)
{
  array_to_unref depth r pl s;
  intro
    (Trade.trade
      (PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl))
      (PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)))
    #(pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1))
    fn _
  {
    array_to_ref depth r pl s;
  };
}

// ===== map element-predicate conversions (entry-level), duplicated from Read.fst =====
ghost
fn map_peek
  (depth: Ghost.erased nat)
  (r: raw_data_item { Map? r })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))
ensures
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl)) **
    pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  if (Cons? (Map?.v r)) {
    PMU.seq_list_match_cons_elim_trade s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb d r) pl));
    unfold (cbor_match_map_entry0 r ((depth_cb d r) pl) (Seq.head s) (List.Tot.hd (Map?.v r)));
    depth_cb_pos d r pl (Seq.head s).cbor_map_entry_key (fst (List.Tot.hd (Map?.v r)));
    fold (cbor_match_map_entry0 r ((depth_cb d r) pl) (Seq.head s) (List.Tot.hd (Map?.v r)));
    Trade.elim _ (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb d r) pl)));
  } else {
    ()
  }
}

ghost
fn map_to_unref
  (depth: Ghost.erased nat)
  (r: raw_data_item { Map? r })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))
ensures
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  map_peek depth r pl s;
  ghost fn prf
    (c': cbor_map_entry)
    (pr: (raw_data_item & raw_data_item) { pr << Map?.v r /\ List.Tot.memP pr (Map?.v r) })
    requires cbor_match_map_entry0 r ((depth_cb d r) pl) c' pr
    ensures cbor_match_map_entry_with_depth (nat_pred d) pl c' pr
  {
    unfold (cbor_match_map_entry0 r ((depth_cb d r) pl) c' pr);
    depth_cb_pos d r pl c'.cbor_map_entry_key (fst pr);
    depth_cb_succ d r pl c'.cbor_map_entry_key (fst pr);
    nat_pred_succ d;
    rewrite ((depth_cb d r) pl c'.cbor_map_entry_key (fst pr))
      as (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_key (fst pr));
    depth_cb_succ d r pl c'.cbor_map_entry_value (snd pr);
    rewrite ((depth_cb d r) pl c'.cbor_map_entry_value (snd pr))
      as (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_value (snd pr));
    fold (cbor_match_map_entry_with_depth (nat_pred d) pl c' pr);
  };
  seq_list_match_conv s (Map?.v r)
    (cbor_match_map_entry0 r ((depth_cb d r) pl))
    (cbor_match_map_entry_with_depth (nat_pred d) pl)
    prf;
}

ghost
fn map_to_ref
  (depth: Ghost.erased nat)
  (r: raw_data_item { Map? r })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1)
ensures
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))
{
  let d = Ghost.reveal depth;
  if (d = 0) {
    PM.seq_list_match_nil_elim s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred d) pl);
    PM.seq_list_match_nil_intro s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb d r) pl));
  } else {
    ghost fn prf
      (c': cbor_map_entry)
      (pr: (raw_data_item & raw_data_item) { pr << Map?.v r /\ List.Tot.memP pr (Map?.v r) })
      requires cbor_match_map_entry_with_depth (nat_pred d) pl c' pr
      ensures cbor_match_map_entry0 r ((depth_cb d r) pl) c' pr
    {
      unfold (cbor_match_map_entry_with_depth (nat_pred d) pl c' pr);
      depth_cb_succ d r pl c'.cbor_map_entry_key (fst pr);
      nat_pred_succ d;
      rewrite (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_key (fst pr))
        as ((depth_cb d r) pl c'.cbor_map_entry_key (fst pr));
      depth_cb_succ d r pl c'.cbor_map_entry_value (snd pr);
      rewrite (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_value (snd pr))
        as ((depth_cb d r) pl c'.cbor_map_entry_value (snd pr));
      fold (cbor_match_map_entry0 r ((depth_cb d r) pl) c' pr);
    };
    seq_list_match_conv s (Map?.v r)
      (cbor_match_map_entry_with_depth (nat_pred d) pl)
      (cbor_match_map_entry0 r ((depth_cb d r) pl))
      prf;
  }
}

// forward conversion + reverse trade + the depth>=1 fact (map version).
ghost
fn cbor_seq_list_match_map_depth_to_succ
  (depth: Ghost.erased nat)
  (r: raw_data_item { Map? r })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))
ensures
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    Trade.trade
      (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl))
      (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))) **
    pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1)
{
  map_to_unref depth r pl s;
  intro
    (Trade.trade
      (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl))
      (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))))
    #(pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1))
    fn _
  {
    map_to_ref depth r pl s;
  };
}

let ser_payload_string_lens_aux_post
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
  (xh:
      (LowParse.Spec.Combinators.parse_filter_refine
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
      )
  )
  (xh' : raw_data_item)
: Tot prop
=
        synth_raw_data_item_recip xh' == (| xh1, xh |)

ghost
fn ser_payload_string_lens_aux
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
  (xl: with_perm cbor_raw)
  (xh:
      (LowParse.Spec.Combinators.parse_filter_refine
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
      )
  )
requires
  (vmatch_ext
      (LowParse.Spec.Combinators.parse_filter_refine
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
      )
      (match_cbor_payload xh1)
      xl xh
  )
returns xh': Ghost.erased raw_data_item
ensures
  (cbor_match_with_perm xl xh' **
    Trade.trade
      (cbor_match_with_perm xl xh')
      (vmatch_ext
        (LowParse.Spec.Combinators.parse_filter_refine
          (lseq_utf8_correct (get_header_initial_byte xh1).major_type
            (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
          )
        )
        (match_cbor_payload xh1) xl xh
      ) **
      pure (
        ser_payload_string_lens_aux_post xh1 sq xh xh'
      )
  )
{
  let _ = vmatch_ext_elim_trade 
        (LowParse.Spec.Combinators.parse_filter_refine
          (lseq_utf8_correct (get_header_initial_byte xh1).major_type
            (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
          )
        )
        (match_cbor_payload xh1) xl xh;
  let xh' = match_cbor_payload_elim_trade xh1 xl _;
  Trade.trans (cbor_match_with_perm xl xh') _ _;
  xh'
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn ser_payload_string_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
: 
vmatch_lens #_ #_ #_
  (vmatch_ext
      (LowParse.Spec.Combinators.parse_filter_refine
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
      )
      (match_cbor_payload xh1))
  (LP.vmatch_filter 
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
    )
    (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
    )
  )
= (x1': _)
  (z: _)
{
  let xh' = ser_payload_string_lens_aux xh1 sq x1' z;
  Trade.rewrite_with_trade
    (cbor_match_with_perm x1' xh')
    (cbor_match x1'.p x1'.v xh');
  Trade.trans
    (cbor_match x1'.p x1'.v xh')
    (cbor_match_with_perm x1' xh') _; // FIXME: WHY WHY WHY do I now have to help Pulse here?
  let s = cbor_match_string_elim_payload x1'.v;
  Trade.trans _ (cbor_match _ x1'.v xh') _;
  S.pts_to_len s;
  with p' . assert (pts_to s #p' (Ghost.reveal z <: Seq.seq U8.t));
  let res : with_perm (S.slice byte) = {
    v = s;
    p = p';
  };
  let x' = LowParse.Pulse.SeqBytes.pts_to_seqbytes_intro
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1)))
    _
    s
    z
    res;
  LowParse.Pulse.VCList.trade_trans_nounify
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      res x')
    _
    _ _;
  Trade.rewrite_with_trade
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      res x')
    (LowParse.Pulse.Combinators.vmatch_filter
      (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      )
      (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
      )
      res (Ghost.reveal z)
    );
  Trade.trans _ 
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      res x')
    _;
  res
}

#pop-options

inline_for_extraction
let ser_payload_string
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_string_lens xh1 sq)
      (LowParse.Pulse.Combinators.l2r_write_filter
        _
        (LowParse.Pulse.SeqBytes.l2r_write_lseq_bytes_copy
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type _)
      )
    )
    (serialize_content xh1)

inline_for_extraction
let size_payload_string
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_string_lens xh1 sq)
      (LowParse.Pulse.Combinators.compute_remaining_size_filter
        _
        (LowParse.Pulse.SeqBytes.compute_remaining_size_lseq_bytes_copy
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type _)
      )
    )
    (serialize_content xh1)

// ============================================================================
// DEPTH-AWARE STRING (leaf) writer twin. String is a leaf (non-inline
// composite): ser_payload_string_lens_aux_d bridges the depth match to plain
// cbor_match via cbor_match_with_depth_to_match, then the rest reuses the exact
// non-depth seqbytes extraction. No recursion / no `f`.
// ============================================================================

#push-options "--z3rlimit 10 --split_queries always"

ghost
fn ser_payload_string_lens_aux_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
  (xl: with_perm cbor_raw)
  (xh:
      (LowParse.Spec.Combinators.parse_filter_refine
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
      )
  )
requires
  (vmatch_ext
      (LowParse.Spec.Combinators.parse_filter_refine
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
      )
      (match_cbor_payload_d n xh1)
      xl xh
  )
returns xh': Ghost.erased raw_data_item
ensures
  (cbor_match_with_perm xl xh' **
    Trade.trade
      (cbor_match_with_perm xl xh')
      (vmatch_ext
        (LowParse.Spec.Combinators.parse_filter_refine
          (lseq_utf8_correct (get_header_initial_byte xh1).major_type
            (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
          )
        )
        (match_cbor_payload_d n xh1) xl xh
      ) **
      pure (
        ser_payload_string_lens_aux_post xh1 sq xh xh'
      )
  )
{
  let _ = vmatch_ext_elim_trade 
        (LowParse.Spec.Combinators.parse_filter_refine
          (lseq_utf8_correct (get_header_initial_byte xh1).major_type
            (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
          )
        )
        (match_cbor_payload_d n xh1) xl xh;
  let xh' = match_cbor_payload_elim_trade_d n xh1 xl _;
  Trade.trans (cbor_match_with_perm_d n xl xh') _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d n xl xh')
    (cbor_match_with_depth n xl.p xl.v xh');
  Trade.trans (cbor_match_with_depth n xl.p xl.v xh') (cbor_match_with_perm_d n xl xh') _;
  cbor_match_with_depth_cases n xl.p xl.v xh';
  assert_norm ((cbor_major_type_byte_string <: FStar.UInt8.t) == 2uy);
  assert_norm ((cbor_major_type_text_string <: FStar.UInt8.t) == 3uy);
  assert_norm ((cbor_major_type_array <: FStar.UInt8.t) == 4uy);
  assert_norm ((cbor_major_type_map <: FStar.UInt8.t) == 5uy);
  assert_norm ((cbor_major_type_tagged <: FStar.UInt8.t) == 6uy);
  get_major_type_synth_raw_data_item_recip (Ghost.reveal xh');
  cbor_match_with_depth_to_match n xl.v;
  Trade.trans (cbor_match xl.p xl.v xh') (cbor_match_with_depth n xl.p xl.v xh') _;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh')
    (cbor_match_with_perm xl xh');
  Trade.trans (cbor_match_with_perm xl xh') (cbor_match xl.p xl.v xh') _;
  xh'
}

#pop-options

#push-options "--z3rlimit 32"

inline_for_extraction
fn ser_payload_string_lens_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
: 
vmatch_lens #_ #_ #_
  (vmatch_ext
      (LowParse.Spec.Combinators.parse_filter_refine
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
      )
      (match_cbor_payload_d n xh1))
  (LP.vmatch_filter 
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
    )
    (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
    )
  )
= (x1': _)
  (z: _)
{
  let xh' = ser_payload_string_lens_aux_d n xh1 sq x1' z;
  Trade.rewrite_with_trade
    (cbor_match_with_perm x1' xh')
    (cbor_match x1'.p x1'.v xh');
  Trade.trans
    (cbor_match x1'.p x1'.v xh')
    (cbor_match_with_perm x1' xh') _;
  let s = cbor_match_string_elim_payload x1'.v;
  Trade.trans _ (cbor_match _ x1'.v xh') _;
  S.pts_to_len s;
  with p' . assert (pts_to s #p' (Ghost.reveal z <: Seq.seq U8.t));
  let res : with_perm (S.slice byte) = {
    v = s;
    p = p';
  };
  let x' = LowParse.Pulse.SeqBytes.pts_to_seqbytes_intro
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1)))
    _
    s
    z
    res;
  LowParse.Pulse.VCList.trade_trans_nounify
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      res x')
    _
    _ _;
  Trade.rewrite_with_trade
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      res x')
    (LowParse.Pulse.Combinators.vmatch_filter
      (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      )
      (lseq_utf8_correct (get_header_initial_byte xh1).major_type
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
      )
      res (Ghost.reveal z)
    );
  Trade.trans _ 
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      res x')
    _;
  res
}

#pop-options

inline_for_extraction
let ser_payload_string_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
: l2r_writer (match_cbor_payload_d n xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_string_lens_d n xh1 sq)
      (LowParse.Pulse.Combinators.l2r_write_filter
        _
        (LowParse.Pulse.SeqBytes.l2r_write_lseq_bytes_copy
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type _)
      )
    )
    (serialize_content xh1)

inline_for_extraction
let size_payload_string_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
: compute_remaining_size (match_cbor_payload_d n xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_string_lens_d n xh1 sq)
      (LowParse.Pulse.Combinators.compute_remaining_size_filter
        _
        (LowParse.Pulse.SeqBytes.compute_remaining_size_lseq_bytes_copy
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type _)
      )
    )
    (serialize_content xh1)

inline_for_extraction
let cbor_with_perm_case_array
  (c: with_perm cbor_raw)
: Tot bool
= match c.v with
  | CBOR_Case_Array _ -> true
  | _ -> false

inline_for_extraction
let cbor_with_perm_case_array_get
  (c: with_perm cbor_raw)
: Tot (option (with_perm (S.slice cbor_raw)))
= match c.v with
  | CBOR_Case_Array a -> Some { v = a.cbor_array_ptr; p = perm_mul c.p a.cbor_array_array_perm }
  | _ -> None

let cbor_with_perm_case_array_match_elem
  (c: with_perm cbor_raw)
: (x: cbor_raw) ->
  (y: raw_data_item) ->
  Tot slprop
= cbor_match
    (perm_mul c.p (match c.v with CBOR_Case_Array a -> a.cbor_array_payload_perm | _ -> 1.0R (* dummy *) ))

let cbor_with_perm_case_array_match_elem_eq
  (c: with_perm cbor_raw)
  (a: cbor_array)
  (sq: squash (c.v == CBOR_Case_Array a))
: Lemma (
    (match c.v with
      | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
      | _ -> 1.0R) == a.cbor_array_payload_perm
  )
= match c.v with
  | CBOR_Case_Array a' -> assert (a' == a)
  | _ -> assert False

inline_for_extraction
let ser_payload_array_array_elem
  (f: l2r_writer cbor_match_with_perm serialize_raw_data_item)
  (a: with_perm cbor_raw)
: l2r_writer (cbor_with_perm_case_array_match_elem a) serialize_raw_data_item
= l2r_writer_lens
    (cbor_match_with_perm_lens _)
    f

inline_for_extraction
let size_payload_array_array_elem
  (f: compute_remaining_size cbor_match_with_perm serialize_raw_data_item)
  (a: with_perm cbor_raw)
: compute_remaining_size (cbor_with_perm_case_array_match_elem a) serialize_raw_data_item
= compute_remaining_size_lens
    (cbor_match_with_perm_lens _)
    f

#push-options "--z3rlimit 32"

ghost
fn ser_payload_array_array_lens_aux
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_array))
  (xl: with_perm cbor_raw)
  (xh: LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))) raw_data_item)
requires
  (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array)
      xl xh
  )
ensures
  LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
    cbor_with_perm_case_array_match_elem
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))
    xl xh **
  Trade.trade
    (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
      xl xh)
      (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1)))
                  raw_data_item)
                  (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array)
                  xl xh
      )
{
  let xh2 = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          raw_data_item) (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array) _ _;
  assert (pure (Ghost.reveal xh2 == xh));
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) _ xl (Ghost.reveal xh2);
  Trade.trans (match_cbor_payload xh1 xl (Ghost.reveal xh2)) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl (Ghost.reveal xh2);
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match _ _ _) (cbor_match_with_perm _ _) _; // FIXME: WHY WHY WHY do I need to help Pulse here?
  cbor_match_cases _;
  let CBOR_Case_Array a = xl.v;
  cbor_with_perm_case_array_match_elem_eq xl a ();
  cbor_match_eq_array xl.p a xh0;
  assert (pure (Array?.v (Ghost.reveal xh0) == xh));
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_array a xl.p xh0 cbor_match);
  Trade.trans (cbor_match_array a xl.p xh0 cbor_match) _ _;
  unfold (cbor_match_array a xl.p xh0 cbor_match);
  with s. assert (PM.seq_list_match s (Array?.v xh0)
    (cbor_match (xl.p `perm_mul` a.cbor_array_payload_perm)));
  rewrite
    (PM.seq_list_match s (Array?.v xh0)
      (cbor_match (xl.p `perm_mul` a.cbor_array_payload_perm)))
    as (PM.seq_list_match s xh
      (cbor_match
        (xl.p `perm_mul`
          (match xl.v with
            | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
            | _ -> 1.0R))));
  rewrite
    (PM.seq_list_match s xh
      (cbor_match
        (xl.p `perm_mul`
          (match xl.v with
            | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
            | _ -> 1.0R))))
    as (PM.seq_list_match s xh (cbor_with_perm_case_array_match_elem xl));
  // let ar = Some?.v (cbor_with_perm_case_array_get xl);
  let Some ar = cbor_with_perm_case_array_get xl;
  rewrite each a.cbor_array_ptr as ar.v;
  LowParse.Pulse.VCList.nlist_match_slice_intro cbor_with_perm_case_array_get
    cbor_with_perm_case_array_match_elem
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))
    xl xh
      ar s
  ;
  intro
    (Trade.trade
      (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
        cbor_with_perm_case_array_match_elem
        (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
        xl xh
      )
      (cbor_match_array a xl.p xh0 cbor_match)
    )
    #emp
    fn _
  {
    unfold (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
      xl xh
    );
    with (s : S.slice cbor_raw) #p v.
      assert S.pts_to s #p v;
    (* ^ There is a single pts_to in the context, rewrite the slice ptr into
       a.cbor_array_ptr and then let maching figure it out. *)
    rewrite S.pts_to s #p v as S.pts_to a.cbor_array_ptr #p v;
    rewrite
      (PM.seq_list_match v xh (cbor_with_perm_case_array_match_elem xl))
      as (PM.seq_list_match v xh
        (cbor_match
          (xl.p `perm_mul`
            (match xl.v with
              | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
              | _ -> 1.0R))));
    rewrite
      (PM.seq_list_match v xh
        (cbor_match
          (xl.p `perm_mul`
            (match xl.v with
              | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
              | _ -> 1.0R))))
      as (PM.seq_list_match v (Array?.v xh0)
        (cbor_match (xl.p `perm_mul` a.cbor_array_payload_perm)));
    fold (cbor_match_array a xl.p xh0 cbor_match);
    ()
  };
  Trade.trans _ (cbor_match_array a xl.p xh0 cbor_match) _;
}

#pop-options

inline_for_extraction
fn ser_payload_array_array_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_array))
:
vmatch_lens #_ #_ #_
  (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array))
  (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                  (get_header_long_argument xh1))))
=
  (x1': _)
  (x: _)
{
  ser_payload_array_array_lens_aux xh1 sq x1' x;
  x1'
}

#push-options "--z3rlimit 32"

inline_for_extraction
let ser_payload_array_array
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_array_array_lens xh1 sq)
      (LowParse.Pulse.VCList.l2r_write_nlist_as_slice
        cbor_with_perm_case_array_get
        cbor_with_perm_case_array_match_elem
        serialize_raw_data_item
        (ser_payload_array_array_elem f)
        (Ghost.hide (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1))))
      )
    )
    (serialize_content xh1)

inline_for_extraction
let size_payload_array_array
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_array_array_lens xh1 sq)
      (LowParse.Pulse.VCList.compute_remaining_size_nlist_as_slice
        cbor_with_perm_case_array_get
        cbor_with_perm_case_array_match_elem
        serialize_raw_data_item
        (size_payload_array_array_elem f)
        (Ghost.hide (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1))))
      )
    )
    (serialize_content xh1)

#pop-options

ghost
fn cbor_serialized_array_pts_to_serialized_with_perm_trade
  (xs: cbor_serialized)
  (p: perm)
  (xh0: raw_data_item { Array? xh0 })
  (n: nat { n == U64.v (Array?.len xh0).value })
  (res: with_perm (S.slice byte))
requires
  cbor_match_serialized_array xs p xh0 ** pure (
    res.v == (to_slice xs.cbor_serialized_payload) /\
    res.p == p `perm_mul` xs.cbor_serialized_perm
  )
ensures
  pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0) **
  Trade.trade
    (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0) )
    (cbor_match_serialized_array xs p xh0)
{
  unfold (cbor_match_serialized_array xs p xh0);
  unfold (cbor_match_serialized_payload_array (to_slice xs.cbor_serialized_payload) (p `perm_mul` xs.cbor_serialized_perm) (Array?.v xh0));
  with n' (r': LowParse.Spec.VCList.nlist n' raw_data_item) . assert
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' serialize_raw_data_item) (to_slice xs.cbor_serialized_payload) #(p `perm_mul` xs.cbor_serialized_perm) r');
  rewrite (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' serialize_raw_data_item) (to_slice xs.cbor_serialized_payload) #(p `perm_mul` xs.cbor_serialized_perm) r')
    as (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0));
  intro
    (Trade.trade
      (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0))
      (cbor_match_serialized_array xs p xh0)
    )
    #emp
    fn _
  { 
    rewrite (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0))
      as (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) (to_slice xs.cbor_serialized_payload) #(p `perm_mul` xs.cbor_serialized_perm) (Array?.v xh0));
    fold (cbor_match_serialized_payload_array (to_slice xs.cbor_serialized_payload) (p `perm_mul` xs.cbor_serialized_perm) (Array?.v xh0));
    fold (cbor_match_serialized_array xs p xh0);
  };
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn ser_payload_array_not_array_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: vmatch_lens #_ #_ #_ (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_array)))
  (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item))
= (xl: _)
  (v: _)
{
  let _ = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_array)) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) (pnot cbor_with_perm_case_array) _ _;
  Trade.trans (match_cbor_payload xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl _;
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match xl.p xl.v xh0) (cbor_match_with_perm xl xh0) _; // FIXME: WHY WHY WHY do I need to help Pulse there?
  cbor_match_cases xl.v;
  let CBOR_Case_Serialized_Array xs = xl.v;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_serialized_array xs xl.p xh0);
  Trade.trans (cbor_match_serialized_array xs xl.p xh0) _ _;
  let res : with_perm (S.slice byte) = {
    v = (to_slice xs.cbor_serialized_payload);
    p = xl.p `perm_mul` xs.cbor_serialized_perm;
  };
  cbor_serialized_array_pts_to_serialized_with_perm_trade xs xl.p xh0
    (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
    res;
  Trade.trans _ (cbor_match_serialized_array xs xl.p xh0) _;
  with w . assert (
    pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item)
      res
      w
  );
  assert (pure (w == Ghost.reveal v));
  Trade.rewrite_with_trade
    (    pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item)
      res
      w
    )
    (
        pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item)
      res
      v
    );
  Trade.trans 
    (
        pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item)
      res
      v
    )
    _ _;
  res
}

inline_for_extraction
let ser_payload_array_not_array
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
:
l2r_writer (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_array))
  (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_array_not_array_lens xh1 sq)
      (l2r_write_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) serialize_raw_data_item
      ))
    )
    _

inline_for_extraction
let size_payload_array_not_array
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
:
compute_remaining_size (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_array))
  (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_array_not_array_lens xh1 sq)
      (compute_remaining_size_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) serialize_raw_data_item
      ))
    )
    _

#pop-options

inline_for_extraction
let ser_payload_array
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_array
    (ser_payload_array_array f xh1 sq)
    (ser_payload_array_not_array xh1 sq)

inline_for_extraction
let size_payload_array
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse_low
    _ _
    cbor_with_perm_case_array
    (size_payload_array_array f xh1 sq)
    (size_payload_array_not_array xh1 sq)

// ============================================================================
// DEPTH-AWARE array-case writers (`_d` twins). The node is at ghost depth `n`;
// its INLINE children are at depth `nat_pred n`. Mirrors the non-depth array
// writers above, threading the depth through the vmatch.
// ============================================================================

// DELIVERABLE 1: depth-aware array element predicate.
let cbor_with_perm_case_array_match_elem_d
  (m: nat)
  (c: with_perm cbor_raw)
: (x: cbor_raw) ->
  (y: raw_data_item) ->
  Tot slprop
= cbor_match_with_depth m
    (perm_mul c.p (match c.v with CBOR_Case_Array a -> a.cbor_array_payload_perm | _ -> 1.0R (* dummy *) ))

let cbor_with_perm_case_array_match_elem_d_eq
  (m: nat)
  (c: with_perm cbor_raw)
  (a: cbor_array)
  (sq: squash (c.v == CBOR_Case_Array a))
: Lemma (
    (match c.v with
      | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
      | _ -> 1.0R) == a.cbor_array_payload_perm
  )
= match c.v with
  | CBOR_Case_Array a' -> assert (a' == a)
  | _ -> assert False

// DELIVERABLE 2: depth-aware element writer / size-computer.
inline_for_extraction
let ser_payload_array_array_elem_d
  (m: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d m) serialize_raw_data_item)
  (a: with_perm cbor_raw)
: l2r_writer (cbor_with_perm_case_array_match_elem_d m a) serialize_raw_data_item
= l2r_writer_lens
    (cbor_match_with_perm_lens_d m _)
    f

inline_for_extraction
let size_payload_array_array_elem_d
  (m: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d m) serialize_raw_data_item)
  (a: with_perm cbor_raw)
: compute_remaining_size (cbor_with_perm_case_array_match_elem_d m a) serialize_raw_data_item
= compute_remaining_size_lens
    (cbor_match_with_perm_lens_d m _)
    f

#push-options "--z3rlimit 32"

// DELIVERABLE 3 (the crux): convert the depth-array node payload match into the
// depth-aware `nlist_match_slice`, with a reverse trade. Mirrors
// `ser_payload_array_array_lens_aux` but goes through the depth machinery:
// `match_cbor_payload_elim_trade_d` -> `cbor_match_with_depth n` -> array elim
// (`cbor_match_with_depth_eq_array`, giving `depth_cb n xh0`), then converts the
// element predicate from `depth_cb n xh0 pl` to `cbor_match_with_depth (nat_pred
// n) pl` via `array_to_unref` (forward) / `array_to_ref` (reverse closure).
ghost
fn ser_payload_array_array_lens_aux_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_array))
  (xl: with_perm cbor_raw)
  (xh: LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))) raw_data_item)
requires
  (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_array)
      xl xh
  )
ensures
  LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
    (cbor_with_perm_case_array_match_elem_d (nat_pred n))
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))
    xl xh **
  Trade.trade
    (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
      (cbor_with_perm_case_array_match_elem_d (nat_pred n))
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
      xl xh)
      (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1)))
                  raw_data_item)
                  (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_array)
                  xl xh
      )
{
  let xh2 = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          raw_data_item) (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_array) _ _;
  assert (pure (Ghost.reveal xh2 == xh));
  vmatch_with_cond_elim_trade (match_cbor_payload_d n xh1) _ xl (Ghost.reveal xh2);
  Trade.trans (match_cbor_payload_d n xh1 xl (Ghost.reveal xh2)) _ _;
  let xh0 = match_cbor_payload_elim_trade_d n xh1 xl (Ghost.reveal xh2);
  Trade.trans (cbor_match_with_perm_d n xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d n xl xh0)
    (cbor_match_with_depth n xl.p xl.v xh0);
  Trade.trans (cbor_match_with_depth n xl.p xl.v xh0) (cbor_match_with_perm_d n xl xh0) _; // FIXME: WHY WHY WHY do I need to help Pulse here?
  cbor_match_with_depth_cases n xl.p xl.v xh0;
  let CBOR_Case_Array a = xl.v;
  cbor_with_perm_case_array_match_elem_d_eq (nat_pred n) xl a ();
  cbor_match_with_depth_eq_array n xl.p a xh0;
  depth_cb_eq n (Ghost.reveal xh0);
  assert (pure (Array?.v (Ghost.reveal xh0) == xh));
  Trade.rewrite_with_trade
    (cbor_match_with_depth n xl.p xl.v xh0)
    (cbor_match_array a xl.p xh0 (depth_cb n xh0));
  Trade.trans (cbor_match_array a xl.p xh0 (depth_cb n xh0)) _ _;
  unfold (cbor_match_array a xl.p xh0 (depth_cb n xh0));
  with s. assert (PM.seq_list_match s (Array?.v xh0)
    ((depth_cb n xh0) (xl.p `perm_mul` a.cbor_array_payload_perm)));
  array_to_unref n xh0 (xl.p `perm_mul` a.cbor_array_payload_perm) s;
  rewrite
    (PM.seq_list_match s (Array?.v xh0)
      (cbor_match_with_depth (nat_pred n)
        (xl.p `perm_mul` a.cbor_array_payload_perm)))
    as (PM.seq_list_match s xh
      (cbor_match_with_depth (nat_pred n)
        (xl.p `perm_mul`
          (match xl.v with
            | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
            | _ -> 1.0R))));
  rewrite
    (PM.seq_list_match s xh
      (cbor_match_with_depth (nat_pred n)
        (xl.p `perm_mul`
          (match xl.v with
            | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
            | _ -> 1.0R))))
    as (PM.seq_list_match s xh
      (cbor_with_perm_case_array_match_elem_d (nat_pred n) xl));
  let Some ar = cbor_with_perm_case_array_get xl;
  rewrite each a.cbor_array_ptr as ar.v;
  LowParse.Pulse.VCList.nlist_match_slice_intro cbor_with_perm_case_array_get
    (cbor_with_perm_case_array_match_elem_d (nat_pred n))
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))
    xl xh
      ar s
  ;
  intro
    (Trade.trade
      (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
        (cbor_with_perm_case_array_match_elem_d (nat_pred n))
        (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
        xl xh
      )
      (cbor_match_array a xl.p xh0 (depth_cb n xh0))
    )
    #(pure (Cons? (Array?.v xh0) ==> Ghost.reveal n >= 1))
    fn _
  {
    unfold (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
      (cbor_with_perm_case_array_match_elem_d (nat_pred n))
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
      xl xh
    );
    with (sl : S.slice cbor_raw) #p v.
      assert (S.pts_to sl #p v);
    (* ^ There is a single pts_to in the context, rewrite the slice ptr into
       a.cbor_array_ptr and then let matching figure it out. *)
    rewrite (S.pts_to sl #p v) as (S.pts_to a.cbor_array_ptr #p v);
    rewrite
      (PM.seq_list_match v xh
        (cbor_with_perm_case_array_match_elem_d (nat_pred n) xl))
      as (PM.seq_list_match v xh
        (cbor_match_with_depth (nat_pred n)
          (xl.p `perm_mul`
            (match xl.v with
              | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
              | _ -> 1.0R))));
    rewrite
      (PM.seq_list_match v xh
        (cbor_match_with_depth (nat_pred n)
          (xl.p `perm_mul`
            (match xl.v with
              | CBOR_Case_Array a' -> a'.cbor_array_payload_perm
              | _ -> 1.0R))))
      as (PM.seq_list_match v (Array?.v xh0)
        (cbor_match_with_depth (nat_pred n)
          (xl.p `perm_mul` a.cbor_array_payload_perm)));
    array_to_ref n xh0 (xl.p `perm_mul` a.cbor_array_payload_perm) v;
    fold (cbor_match_array a xl.p xh0 (depth_cb n xh0));
    ()
  };
  Trade.trans _ (cbor_match_array a xl.p xh0 (depth_cb n xh0)) _;
}

#pop-options

// DELIVERABLE 4: depth-aware array node payload -> nlist_match_slice lens.
inline_for_extraction
fn ser_payload_array_array_lens_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_array))
:
vmatch_lens #_ #_ #_
  (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_array))
  (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
      (cbor_with_perm_case_array_match_elem_d (nat_pred n))
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                  (get_header_long_argument xh1))))
=
  (x1': _)
  (x: _)
{
  ser_payload_array_array_lens_aux_d n xh1 sq x1' x;
  x1'
}

#push-options "--z3rlimit 32"

// DELIVERABLE 5: depth-aware array-case content writer / size-computer.
inline_for_extraction
let ser_payload_array_array_d
  (n: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_array) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_array_array_lens_d n xh1 sq)
      (LowParse.Pulse.VCList.l2r_write_nlist_as_slice
        cbor_with_perm_case_array_get
        (cbor_with_perm_case_array_match_elem_d (nat_pred n))
        serialize_raw_data_item
        (ser_payload_array_array_elem_d (nat_pred n) f)
        (Ghost.hide (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1))))
      )
    )
    (serialize_content xh1)

inline_for_extraction
let size_payload_array_array_d
  (n: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_array) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_array_array_lens_d n xh1 sq)
      (LowParse.Pulse.VCList.compute_remaining_size_nlist_as_slice
        cbor_with_perm_case_array_get
        (cbor_with_perm_case_array_match_elem_d (nat_pred n))
        serialize_raw_data_item
        (size_payload_array_array_elem_d (nat_pred n) f)
        (Ghost.hide (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1))))
      )
    )
    (serialize_content xh1)

#pop-options

#push-options "--z3rlimit 32"

// DELIVERABLE 6: depth-aware serialized-array (not-array) case. Bridges the depth
// match to the plain `cbor_match` via `cbor_match_with_depth_to_match` (valid
// because the node is CBOR_Case_Serialized_Array, a non-inline composite), then
// proceeds exactly as the non-depth serialized case. No recursion / no `f`.
inline_for_extraction
fn ser_payload_array_not_array_lens_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: vmatch_lens #_ #_ #_ (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_array)))
  (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item))
= (xl: _)
  (v: _)
{
  let _ = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_array)) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_array) _ _;
  Trade.trans (match_cbor_payload_d n xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade_d n xh1 xl _;
  Trade.trans (cbor_match_with_perm_d n xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d n xl xh0)
    (cbor_match_with_depth n xl.p xl.v xh0);
  Trade.trans (cbor_match_with_depth n xl.p xl.v xh0) (cbor_match_with_perm_d n xl xh0) _; // FIXME: WHY WHY WHY do I need to help Pulse there?
  cbor_match_with_depth_cases n xl.p xl.v xh0;
  cbor_match_with_depth_to_match n xl.v;
  Trade.trans (cbor_match xl.p xl.v xh0) (cbor_match_with_depth n xl.p xl.v xh0) _;
  cbor_match_cases xl.v;
  let CBOR_Case_Serialized_Array xs = xl.v;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_serialized_array xs xl.p xh0);
  Trade.trans (cbor_match_serialized_array xs xl.p xh0) _ _;
  let res : with_perm (S.slice byte) = {
    v = (to_slice xs.cbor_serialized_payload);
    p = xl.p `perm_mul` xs.cbor_serialized_perm;
  };
  cbor_serialized_array_pts_to_serialized_with_perm_trade xs xl.p xh0
    (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
    res;
  Trade.trans _ (cbor_match_serialized_array xs xl.p xh0) _;
  with w . assert (
    pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item)
      res
      w
  );
  assert (pure (w == Ghost.reveal v));
  Trade.rewrite_with_trade
    (    pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item)
      res
      w
    )
    (
        pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item)
      res
      v
    );
  Trade.trans 
    (
        pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item)
      res
      v
    )
    _ _;
  res
}

inline_for_extraction
let ser_payload_array_not_array_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
:
l2r_writer (vmatch_with_cond (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_array))
  (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_array_not_array_lens_d n xh1 sq)
      (l2r_write_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) serialize_raw_data_item
      ))
    )
    _

inline_for_extraction
let size_payload_array_not_array_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
:
compute_remaining_size (vmatch_with_cond (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_array))
  (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_array_not_array_lens_d n xh1 sq)
      (compute_remaining_size_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) serialize_raw_data_item
      ))
    )
    _

#pop-options

// DELIVERABLE 7: depth-aware array payload dispatcher.
inline_for_extraction
let ser_payload_array_d
  (n: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (match_cbor_payload_d n xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_array
    (ser_payload_array_array_d n f xh1 sq)
    (ser_payload_array_not_array_d n xh1 sq)

inline_for_extraction
let size_payload_array_d
  (n: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (match_cbor_payload_d n xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse_low
    _ _
    cbor_with_perm_case_array
    (size_payload_array_array_d n f xh1 sq)
    (size_payload_array_not_array_d n xh1 sq)

inline_for_extraction
let cbor_with_perm_case_map
  (c: with_perm cbor_raw)
: Tot bool
= match c.v with
  | CBOR_Case_Map _ -> true
  | _ -> false

inline_for_extraction
let cbor_with_perm_case_map_get
  (c: with_perm cbor_raw)
: Tot (option (with_perm (S.slice cbor_map_entry)))
= match c.v with
  | CBOR_Case_Map a -> Some { v = a.cbor_map_ptr; p = perm_mul c.p a.cbor_map_array_perm }
  | _ -> None

let cbor_with_perm_case_map_match_elem_perm
  (c: with_perm cbor_raw)
: Tot perm
= (perm_mul c.p (match c.v with CBOR_Case_Map a -> a.cbor_map_payload_perm | _ -> 1.0R (* dummy *) ))

let cbor_with_perm_case_map_match_elem
  (c: with_perm cbor_raw)
: (x: cbor_map_entry) ->
  (y: (raw_data_item & raw_data_item)) ->
  Tot slprop
= cbor_match_map_entry (cbor_with_perm_case_map_match_elem_perm c)

let cbor_with_perm_case_map_match_elem_eq
  (c: with_perm cbor_raw)
  (a: cbor_map)
  (sq: squash (c.v == CBOR_Case_Map a))
: Lemma (
    cbor_with_perm_case_map_match_elem_perm c ==
      c.p `perm_mul` a.cbor_map_payload_perm
  )
= match c.v with
  | CBOR_Case_Map a' -> assert (a' == a)
  | _ -> assert False

inline_for_extraction
fn ser_payload_map_map_elem_fst
  (a: with_perm cbor_raw)
  (xl: cbor_map_entry)
  (xh: erased (raw_data_item & raw_data_item))
requires
  (cbor_with_perm_case_map_match_elem a xl xh)
returns xl1: (with_perm cbor_raw)
ensures
      (
          cbor_match_with_perm xl1 (fst xh) **
          trade (cbor_match_with_perm xl1 (fst xh)) (cbor_with_perm_case_map_match_elem a xl xh))
{
  let xl1 : with_perm cbor_raw = {
    v = xl.cbor_map_entry_key;
    p = cbor_with_perm_case_map_match_elem_perm a;
  };
  Trade.rewrite_with_trade
    (cbor_with_perm_case_map_match_elem a xl xh)
    (cbor_match_with_perm xl1 (fst xh) **
      cbor_match (cbor_with_perm_case_map_match_elem_perm a) xl.cbor_map_entry_value (snd xh)
    );
  Trade.elim_hyp_r _ _ _;
  xl1
}

inline_for_extraction
fn ser_payload_map_map_elem_snd
  (a: with_perm cbor_raw)
  (xl: cbor_map_entry)
  (xh: erased (raw_data_item & raw_data_item))
requires
  (cbor_with_perm_case_map_match_elem a xl xh)
returns xl1: (with_perm cbor_raw)
ensures
      (
          cbor_match_with_perm xl1 (snd xh) **
          trade (cbor_match_with_perm xl1 (snd xh)) (cbor_with_perm_case_map_match_elem a xl xh))
{
  let xl2 : with_perm cbor_raw = {
    v = xl.cbor_map_entry_value;
    p = cbor_with_perm_case_map_match_elem_perm a;
  };
  Trade.rewrite_with_trade
    (cbor_with_perm_case_map_match_elem a xl xh)
    (cbor_match (cbor_with_perm_case_map_match_elem_perm a) xl.cbor_map_entry_key (fst xh) **
      cbor_match_with_perm xl2 (snd xh)
    );
  Trade.elim_hyp_l _ _ _;
  xl2
}

inline_for_extraction
let ser_payload_map_map_elem
  (f: l2r_writer cbor_match_with_perm serialize_raw_data_item)
  (a: with_perm cbor_raw)
: l2r_writer (cbor_with_perm_case_map_match_elem a) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= LP.l2r_write_nondep_then
    f
    ()
    f
    _
    (ser_payload_map_map_elem_fst a)
    (ser_payload_map_map_elem_snd a)

inline_for_extraction
let size_payload_map_map_elem
  (f: compute_remaining_size cbor_match_with_perm serialize_raw_data_item)
  (a: with_perm cbor_raw)
: compute_remaining_size (cbor_with_perm_case_map_match_elem a) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= LP.compute_remaining_size_nondep_then
    f
    ()
    f
    _
    (ser_payload_map_map_elem_fst a)
    (ser_payload_map_map_elem_snd a)

#push-options "--z3rlimit 32"

#restart-solver
ghost
fn ser_payload_map_map_lens_aux
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_map))
  (xl: with_perm cbor_raw)
  (xh: LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))) (raw_data_item & raw_data_item))
requires
  (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map)
      xl xh
  )
ensures
  LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
    cbor_with_perm_case_map_match_elem
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))
    xl xh **
  Trade.trade
    (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
      xl xh)
      (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1)))
                  (raw_data_item & raw_data_item))
                  (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map)
                  xl xh
      )
{
  let xh2 = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item)) (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map) _ _;
  assert (pure (Ghost.reveal xh2 == xh));
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) _ xl (Ghost.reveal xh2);
  Trade.trans (match_cbor_payload xh1 xl (Ghost.reveal xh2)) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl (Ghost.reveal xh2);
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match _ _ _) (cbor_match_with_perm xl xh0) _; // FIXME: WHY WHY WHY do I need to help Pulse here?
  cbor_match_cases _;
  let CBOR_Case_Map a = xl.v;
  cbor_with_perm_case_map_match_elem_eq xl a ();
  cbor_match_eq_map0 xl.p a xh0;
  assert (pure (Map?.v (Ghost.reveal xh0) == xh));
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_map0 a xl.p xh0 cbor_match);
  Trade.trans (cbor_match_map0 a xl.p xh0 cbor_match) _ _;
  cbor_match_map0_map_trade a xl.p xh0;
  Trade.trans (cbor_match_map xl.p a xh0) _ _;
  unfold (cbor_match_map xl.p a xh0);
  with s. assert (PM.seq_list_match s (Map?.v xh0)
    (cbor_match_map_entry (xl.p `perm_mul` a.cbor_map_payload_perm)));
  rewrite
    (PM.seq_list_match s (Map?.v xh0)
      (cbor_match_map_entry (xl.p `perm_mul` a.cbor_map_payload_perm)))
    as (PM.seq_list_match s xh
      (cbor_match_map_entry (cbor_with_perm_case_map_match_elem_perm xl)));
  rewrite
    (PM.seq_list_match s xh
      (cbor_match_map_entry (cbor_with_perm_case_map_match_elem_perm xl)))
    as (PM.seq_list_match s xh (cbor_with_perm_case_map_match_elem xl));
  let Some ar = cbor_with_perm_case_map_get xl;
  rewrite each a.cbor_map_ptr as (Mkwith_perm?.v ar);
  LowParse.Pulse.VCList.nlist_match_slice_intro cbor_with_perm_case_map_get
    cbor_with_perm_case_map_match_elem
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))
    xl xh
      ar s
  ;
  intro
    (Trade.trade
      (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
        cbor_with_perm_case_map_match_elem
        (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
          (get_header_long_argument xh1)))
        xl xh
      )
      (cbor_match_map xl.p a xh0)
    )
    #emp
    fn _
  {
    unfold (    LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
      xl xh
    );
    with ar _p _v. assert (S.pts_to #cbor_map_entry (Mkwith_perm?.v ar) #_p _v);
    rewrite each (Mkwith_perm?.v ar) as a.cbor_map_ptr;
    rewrite
      (PM.seq_list_match _v xh (cbor_with_perm_case_map_match_elem xl))
      as (PM.seq_list_match _v xh
        (cbor_match_map_entry (cbor_with_perm_case_map_match_elem_perm xl)));
    rewrite
      (PM.seq_list_match _v xh
        (cbor_match_map_entry (cbor_with_perm_case_map_match_elem_perm xl)))
      as (PM.seq_list_match _v (Map?.v xh0)
        (cbor_match_map_entry (xl.p `perm_mul` a.cbor_map_payload_perm)));
    fold (cbor_match_map xl.p a xh0);
    ()
  };
  Trade.trans _ (cbor_match_map xl.p a xh0) _;
}

#pop-options

inline_for_extraction
fn ser_payload_map_map_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_map))
:
vmatch_lens #_ #_ #_
  (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map))
  (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                  (get_header_long_argument xh1))))
=
  (x1': _)
  (x: _)
{
  ser_payload_map_map_lens_aux xh1 sq x1' x;
  x1'
}

#push-options "--z3rlimit 32"

inline_for_extraction
let ser_payload_map_map
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_map_map_lens xh1 sq)
      (LowParse.Pulse.VCList.l2r_write_nlist_as_slice
        cbor_with_perm_case_map_get
        cbor_with_perm_case_map_match_elem
        (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
        (ser_payload_map_map_elem f)
        (Ghost.hide (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1))))
      )
    )
    (serialize_content xh1)

inline_for_extraction
let size_payload_map_map
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_map_map_lens xh1 sq)
      (LowParse.Pulse.VCList.compute_remaining_size_nlist_as_slice
        cbor_with_perm_case_map_get
        cbor_with_perm_case_map_match_elem
        (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
        (size_payload_map_map_elem f)
        (Ghost.hide (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1))))
      )
    )
    (serialize_content xh1)

#pop-options

ghost
fn cbor_serialized_map_pts_to_serialized_with_perm_trade
  (xs: cbor_serialized)
  (p: perm)
  (xh0: raw_data_item { Map? xh0 })
  (n: nat { n == U64.v (Map?.len xh0).value })
  (res: with_perm (S.slice byte))
requires
  cbor_match_serialized_map xs p xh0 ** pure (
    res.v == (to_slice xs.cbor_serialized_payload) /\
    res.p == p `perm_mul` xs.cbor_serialized_perm
  )
ensures
  pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0) **
  Trade.trade
    (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0) )
    (cbor_match_serialized_map xs p xh0)
{
  unfold (cbor_match_serialized_map xs p xh0);
  unfold (cbor_match_serialized_payload_map (to_slice xs.cbor_serialized_payload) (p `perm_mul` xs.cbor_serialized_perm) (Map?.v xh0));
  let _ = assert_norm (
    parse_raw_data_item_kind.parser_kind_subkind == Some ParserStrong /\
    (LowParse.Spec.Combinators.and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind).parser_kind_subkind == Some ParserStrong
  );
  with n' (r': LowParse.Spec.VCList.nlist n' (raw_data_item & raw_data_item)) . assert
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (to_slice xs.cbor_serialized_payload) #(p `perm_mul` xs.cbor_serialized_perm) r');
  rewrite (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (to_slice xs.cbor_serialized_payload) #(p `perm_mul` xs.cbor_serialized_perm) r')
    as (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0));
  intro
    (Trade.trade
      (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0))
      (cbor_match_serialized_map xs p xh0)
    )
    #emp
    fn _
  { 
    rewrite (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0))
      as (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) (to_slice xs.cbor_serialized_payload) #(p `perm_mul` xs.cbor_serialized_perm) (Map?.v xh0));
    fold (cbor_match_serialized_payload_map (to_slice xs.cbor_serialized_payload) (p `perm_mul` xs.cbor_serialized_perm) (Map?.v xh0));
    fold (cbor_match_serialized_map xs p xh0);
  };
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn ser_payload_map_not_map_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: vmatch_lens #_ #_ #_ (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_map)))
  (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)))
= (xl: _)
  (v: _)
{
  let _ = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_map)) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) (pnot cbor_with_perm_case_map) _ _;
  Trade.trans (match_cbor_payload xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl _;
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match xl.p xl.v xh0) (cbor_match_with_perm xl xh0) _; // FIXME: WHY WHY WHY do I need to help Pulse here?
  cbor_match_cases xl.v;
  let CBOR_Case_Serialized_Map xs = xl.v;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_serialized_map xs xl.p xh0);
  Trade.trans (cbor_match_serialized_map xs xl.p xh0) _ _;
  let res : with_perm (S.slice byte) = {
    v = (to_slice xs.cbor_serialized_payload);
    p = xl.p `perm_mul` xs.cbor_serialized_perm;
  };
  cbor_serialized_map_pts_to_serialized_with_perm_trade xs xl.p xh0
    (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
    res;
  Trade.trans _ (cbor_match_serialized_map xs xl.p xh0) _;
  with w . assert (
      pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          (LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item
              serialize_raw_data_item))
      res
      w
  );
  assert (pure (w == Ghost.reveal v));
  Trade.rewrite_with_trade
    (
      pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          (LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item
              serialize_raw_data_item))
      res
      w
    )
    (
      pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          (LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item
              serialize_raw_data_item))
      res
      v
    );
  Trade.trans
    (
      pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          (LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item
              serialize_raw_data_item))
      res
      v
    )
    _ _;
  res
}

inline_for_extraction
let ser_payload_map_not_map
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
:
l2r_writer (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_map))
  (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_map_not_map_lens xh1 sq)
      (l2r_write_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      ))
    )
    _

inline_for_extraction
let size_payload_map_not_map
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
:
compute_remaining_size (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_map))
  (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_map_not_map_lens xh1 sq)
      (compute_remaining_size_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      ))
    )
    _

#pop-options

inline_for_extraction
let ser_payload_map
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_map
    (ser_payload_map_map f xh1 sq)
    (ser_payload_map_not_map xh1 sq)

inline_for_extraction
let size_payload_map
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse_low
    _ _
    cbor_with_perm_case_map
    (size_payload_map_map f xh1 sq)
    (size_payload_map_not_map xh1 sq)

///////////////////////////////////////////////////////////////////////////////
// DEPTH-AWARE MAP writer twins (mirror the array _d template; entries are pairs)
///////////////////////////////////////////////////////////////////////////////

// DELIVERABLE 2 (map): depth-aware per-entry element predicate.
let cbor_with_perm_case_map_match_elem_d
  (m: nat)
  (c: with_perm cbor_raw)
: (x: cbor_map_entry) ->
  (y: (raw_data_item & raw_data_item)) ->
  Tot slprop
= cbor_match_map_entry_with_depth m (cbor_with_perm_case_map_match_elem_perm c)

let cbor_with_perm_case_map_match_elem_d_eq
  (m: nat)
  (c: with_perm cbor_raw)
  (a: cbor_map)
  (sq: squash (c.v == CBOR_Case_Map a))
: Lemma (
    cbor_with_perm_case_map_match_elem_perm c ==
      c.p `perm_mul` a.cbor_map_payload_perm
  )
= match c.v with
  | CBOR_Case_Map a' -> assert (a' == a)
  | _ -> assert False

// DELIVERABLE 3 (map): split the depth entry match into key / value halves.
inline_for_extraction
fn ser_payload_map_map_elem_fst_d
  (m: Ghost.erased nat)
  (a: with_perm cbor_raw)
  (xl: cbor_map_entry)
  (xh: erased (raw_data_item & raw_data_item))
requires
  (cbor_with_perm_case_map_match_elem_d m a xl xh)
returns xl1: (with_perm cbor_raw)
ensures
      (
          cbor_match_with_perm_d m xl1 (fst xh) **
          trade (cbor_match_with_perm_d m xl1 (fst xh)) (cbor_with_perm_case_map_match_elem_d m a xl xh))
{
  let xl1 : with_perm cbor_raw = {
    v = xl.cbor_map_entry_key;
    p = cbor_with_perm_case_map_match_elem_perm a;
  };
  Trade.rewrite_with_trade
    (cbor_with_perm_case_map_match_elem_d m a xl xh)
    (cbor_match_with_perm_d m xl1 (fst xh) **
      cbor_match_with_depth m (cbor_with_perm_case_map_match_elem_perm a) xl.cbor_map_entry_value (snd xh)
    );
  Trade.elim_hyp_r _ _ _;
  xl1
}

inline_for_extraction
fn ser_payload_map_map_elem_snd_d
  (m: Ghost.erased nat)
  (a: with_perm cbor_raw)
  (xl: cbor_map_entry)
  (xh: erased (raw_data_item & raw_data_item))
requires
  (cbor_with_perm_case_map_match_elem_d m a xl xh)
returns xl1: (with_perm cbor_raw)
ensures
      (
          cbor_match_with_perm_d m xl1 (snd xh) **
          trade (cbor_match_with_perm_d m xl1 (snd xh)) (cbor_with_perm_case_map_match_elem_d m a xl xh))
{
  let xl2 : with_perm cbor_raw = {
    v = xl.cbor_map_entry_value;
    p = cbor_with_perm_case_map_match_elem_perm a;
  };
  Trade.rewrite_with_trade
    (cbor_with_perm_case_map_match_elem_d m a xl xh)
    (cbor_match_with_depth m (cbor_with_perm_case_map_match_elem_perm a) xl.cbor_map_entry_key (fst xh) **
      cbor_match_with_perm_d m xl2 (snd xh)
    );
  Trade.elim_hyp_l _ _ _;
  xl2
}

// DELIVERABLE 4 (map): depth-aware entry writer / size-computer.
inline_for_extraction
let ser_payload_map_map_elem_d
  (m: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d m) serialize_raw_data_item)
  (a: with_perm cbor_raw)
: l2r_writer (cbor_with_perm_case_map_match_elem_d m a) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= LP.l2r_write_nondep_then
    f
    ()
    f
    _
    (ser_payload_map_map_elem_fst_d m a)
    (ser_payload_map_map_elem_snd_d m a)

inline_for_extraction
let size_payload_map_map_elem_d
  (m: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d m) serialize_raw_data_item)
  (a: with_perm cbor_raw)
: compute_remaining_size (cbor_with_perm_case_map_match_elem_d m a) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= LP.compute_remaining_size_nondep_then
    f
    ()
    f
    _
    (ser_payload_map_map_elem_fst_d m a)
    (ser_payload_map_map_elem_snd_d m a)

#push-options "--z3rlimit 32"

#restart-solver
// DELIVERABLE 5 (map, the crux): convert the depth-map node payload match into
// the depth-aware nlist_match_slice, with a reverse trade. Mirrors
// ser_payload_array_array_lens_aux_d, staying at cbor_match_map0 (...depth_cb n
// xh0) and converting the entry predicate via map_to_unref / map_to_ref.
ghost
fn ser_payload_map_map_lens_aux_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_map))
  (xl: with_perm cbor_raw)
  (xh: LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))) (raw_data_item & raw_data_item))
requires
  (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_map)
      xl xh
  )
ensures
  LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
    (cbor_with_perm_case_map_match_elem_d (nat_pred n))
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))
    xl xh **
  Trade.trade
    (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
      (cbor_with_perm_case_map_match_elem_d (nat_pred n))
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
      xl xh)
      (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1)))
                  (raw_data_item & raw_data_item))
                  (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_map)
                  xl xh
      )
{
  let xh2 = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item)) (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_map) _ _;
  assert (pure (Ghost.reveal xh2 == xh));
  vmatch_with_cond_elim_trade (match_cbor_payload_d n xh1) _ xl (Ghost.reveal xh2);
  Trade.trans (match_cbor_payload_d n xh1 xl (Ghost.reveal xh2)) _ _;
  let xh0 = match_cbor_payload_elim_trade_d n xh1 xl (Ghost.reveal xh2);
  Trade.trans (cbor_match_with_perm_d n xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d n xl xh0)
    (cbor_match_with_depth n xl.p xl.v xh0);
  Trade.trans (cbor_match_with_depth n xl.p xl.v xh0) (cbor_match_with_perm_d n xl xh0) _;
  cbor_match_with_depth_cases n xl.p xl.v xh0;
  let CBOR_Case_Map a = xl.v;
  cbor_with_perm_case_map_match_elem_d_eq (nat_pred n) xl a ();
  cbor_match_with_depth_eq_map0 n xl.p a xh0;
  depth_cb_eq n (Ghost.reveal xh0);
  assert (pure (Map?.v (Ghost.reveal xh0) == xh));
  Trade.rewrite_with_trade
    (cbor_match_with_depth n xl.p xl.v xh0)
    (cbor_match_map0 a xl.p xh0 (depth_cb n xh0));
  Trade.trans (cbor_match_map0 a xl.p xh0 (depth_cb n xh0)) _ _;
  unfold (cbor_match_map0 a xl.p xh0 (depth_cb n xh0));
  with s. assert (PM.seq_list_match s (Map?.v xh0)
    (cbor_match_map_entry0 xh0 ((depth_cb n xh0) (xl.p `perm_mul` a.cbor_map_payload_perm))));
  map_to_unref n xh0 (xl.p `perm_mul` a.cbor_map_payload_perm) s;
  rewrite
    (PM.seq_list_match s (Map?.v xh0)
      (cbor_match_map_entry_with_depth (nat_pred n)
        (xl.p `perm_mul` a.cbor_map_payload_perm)))
    as (PM.seq_list_match s xh
      (cbor_match_map_entry_with_depth (nat_pred n)
        (cbor_with_perm_case_map_match_elem_perm xl)));
  rewrite
    (PM.seq_list_match s xh
      (cbor_match_map_entry_with_depth (nat_pred n)
        (cbor_with_perm_case_map_match_elem_perm xl)))
    as (PM.seq_list_match s xh
      (cbor_with_perm_case_map_match_elem_d (nat_pred n) xl));
  let Some ar = cbor_with_perm_case_map_get xl;
  rewrite each a.cbor_map_ptr as ar.v;
  LowParse.Pulse.VCList.nlist_match_slice_intro cbor_with_perm_case_map_get
    (cbor_with_perm_case_map_match_elem_d (nat_pred n))
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))
    xl xh
      ar s
  ;
  intro
    (Trade.trade
      (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
        (cbor_with_perm_case_map_match_elem_d (nat_pred n))
        (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
        xl xh
      )
      (cbor_match_map0 a xl.p xh0 (depth_cb n xh0))
    )
    #(pure (Cons? (Map?.v xh0) ==> Ghost.reveal n >= 1))
    fn _
  {
    unfold (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
      (cbor_with_perm_case_map_match_elem_d (nat_pred n))
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))
      xl xh
    );
    with (sl : S.slice cbor_map_entry) #p v.
      assert (S.pts_to sl #p v);
    rewrite (S.pts_to sl #p v) as (S.pts_to a.cbor_map_ptr #p v);
    rewrite
      (PM.seq_list_match v xh
        (cbor_with_perm_case_map_match_elem_d (nat_pred n) xl))
      as (PM.seq_list_match v xh
        (cbor_match_map_entry_with_depth (nat_pred n)
          (cbor_with_perm_case_map_match_elem_perm xl)));
    rewrite
      (PM.seq_list_match v xh
        (cbor_match_map_entry_with_depth (nat_pred n)
          (cbor_with_perm_case_map_match_elem_perm xl)))
      as (PM.seq_list_match v (Map?.v xh0)
        (cbor_match_map_entry_with_depth (nat_pred n)
          (xl.p `perm_mul` a.cbor_map_payload_perm)));
    map_to_ref n xh0 (xl.p `perm_mul` a.cbor_map_payload_perm) v;
    fold (cbor_match_map0 a xl.p xh0 (depth_cb n xh0));
    ()
  };
  Trade.trans _ (cbor_match_map0 a xl.p xh0 (depth_cb n xh0)) _;
}

#pop-options

// DELIVERABLE 6 (map): depth-aware map node payload -> nlist_match_slice lens.
inline_for_extraction
fn ser_payload_map_map_lens_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_map))
:
vmatch_lens #_ #_ #_
  (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_map))
  (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
      (cbor_with_perm_case_map_match_elem_d (nat_pred n))
      (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                  (get_header_long_argument xh1))))
=
  (x1': _)
  (x: _)
{
  ser_payload_map_map_lens_aux_d n xh1 sq x1' x;
  x1'
}

#push-options "--z3rlimit 32"

inline_for_extraction
let ser_payload_map_map_d
  (n: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_map) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_map_map_lens_d n xh1 sq)
      (LowParse.Pulse.VCList.l2r_write_nlist_as_slice
        cbor_with_perm_case_map_get
        (cbor_with_perm_case_map_match_elem_d (nat_pred n))
        (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
        (ser_payload_map_map_elem_d (nat_pred n) f)
        (Ghost.hide (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1))))
      )
    )
    (serialize_content xh1)

inline_for_extraction
let size_payload_map_map_d
  (n: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (vmatch_with_cond (match_cbor_payload_d n xh1) cbor_with_perm_case_map) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_map_map_lens_d n xh1 sq)
      (LowParse.Pulse.VCList.compute_remaining_size_nlist_as_slice
        cbor_with_perm_case_map_get
        (cbor_with_perm_case_map_match_elem_d (nat_pred n))
        (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
        (size_payload_map_map_elem_d (nat_pred n) f)
        (Ghost.hide (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1))))
      )
    )
    (serialize_content xh1)

#pop-options

#push-options "--z3rlimit 32"

// DELIVERABLE 7 (map): depth-aware serialized-map (not-map) case. Bridges the
// depth match to plain cbor_match via cbor_match_with_depth_to_match, then
// proceeds exactly as the non-depth serialized case. No recursion / no `f`.
inline_for_extraction
fn ser_payload_map_not_map_lens_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: vmatch_lens #_ #_ #_ (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_map)))
  (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)))
= (xl: _)
  (v: _)
{
  let _ = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_map)) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_map) _ _;
  Trade.trans (match_cbor_payload_d n xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade_d n xh1 xl _;
  Trade.trans (cbor_match_with_perm_d n xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d n xl xh0)
    (cbor_match_with_depth n xl.p xl.v xh0);
  Trade.trans (cbor_match_with_depth n xl.p xl.v xh0) (cbor_match_with_perm_d n xl xh0) _;
  cbor_match_with_depth_cases n xl.p xl.v xh0;
  cbor_match_with_depth_to_match n xl.v;
  Trade.trans (cbor_match xl.p xl.v xh0) (cbor_match_with_depth n xl.p xl.v xh0) _;
  cbor_match_cases xl.v;
  let CBOR_Case_Serialized_Map xs = xl.v;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_serialized_map xs xl.p xh0);
  Trade.trans (cbor_match_serialized_map xs xl.p xh0) _ _;
  let res : with_perm (S.slice byte) = {
    v = (to_slice xs.cbor_serialized_payload);
    p = xl.p `perm_mul` xs.cbor_serialized_perm;
  };
  cbor_serialized_map_pts_to_serialized_with_perm_trade xs xl.p xh0
    (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
    res;
  Trade.trans _ (cbor_match_serialized_map xs xl.p xh0) _;
  with w . assert (
      pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          (LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item
              serialize_raw_data_item))
      res
      w
  );
  assert (pure (w == Ghost.reveal v));
  Trade.rewrite_with_trade
    (
      pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          (LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item
              serialize_raw_data_item))
      res
      w
    )
    (
      pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          (LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item
              serialize_raw_data_item))
      res
      v
    );
  Trade.trans
    (
      pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64
                  (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))
          (LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item
              serialize_raw_data_item))
      res
      v
    )
    _ _;
  res
}

inline_for_extraction
let ser_payload_map_not_map_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
:
l2r_writer (vmatch_with_cond (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_map))
  (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_map_not_map_lens_d n xh1 sq)
      (l2r_write_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      ))
    )
    _

inline_for_extraction
let size_payload_map_not_map_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
:
compute_remaining_size (vmatch_with_cond (match_cbor_payload_d n xh1) (pnot cbor_with_perm_case_map))
  (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_map_not_map_lens_d n xh1 sq)
      (compute_remaining_size_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      ))
    )
    _

#pop-options

// DELIVERABLE 8 (map): depth-aware map payload dispatcher.
inline_for_extraction
let ser_payload_map_d
  (n: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (match_cbor_payload_d n xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_map
    (ser_payload_map_map_d n f xh1 sq)
    (ser_payload_map_not_map_d n xh1 sq)

inline_for_extraction
let size_payload_map_d
  (n: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (match_cbor_payload_d n xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse_low
    _ _
    cbor_with_perm_case_map
    (size_payload_map_map_d n f xh1 sq)
    (size_payload_map_not_map_d n xh1 sq)

inline_for_extraction
let cbor_with_perm_case_tagged
  (c: with_perm cbor_raw)
: Tot bool
= match c.v with
  | CBOR_Case_Tagged _ -> true
  | _ -> false

inline_for_extraction
fn ser_payload_tagged_tagged_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_tagged))
: vmatch_lens #_ #_ #_ (vmatch_with_cond (vmatch_ext raw_data_item (match_cbor_payload xh1))
      cbor_with_perm_case_tagged)
  cbor_match_with_perm
= (xl: _)
  (v: _)
{
  vmatch_with_cond_elim_trade (vmatch_ext raw_data_item (match_cbor_payload xh1)) cbor_with_perm_case_tagged _ _;
  let xh2 = vmatch_ext_elim_trade raw_data_item (match_cbor_payload xh1) _ _;
  Trade.trans (match_cbor_payload xh1 xl (Ghost.reveal xh2)) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl (Ghost.reveal xh2);
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match xl.p xl.v xh0) (cbor_match_with_perm xl xh0) _; // FIXME: WHY WHY WHY do I need to help Pulse here?
  cbor_match_cases xl.v;
  let CBOR_Case_Tagged tg = xl.v;
  cbor_match_eq_tagged xl.p tg xh0;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_tagged tg xl.p xh0 cbor_match);
  Trade.trans (cbor_match_tagged tg xl.p xh0 cbor_match) _ _;
  cbor_match_tagged_elim tg _ _;
  Trade.trans _ (cbor_match_tagged tg xl.p xh0 cbor_match) _;
  let pl = !(tg.cbor_tagged_ptr);
  let res = {
    v = pl;
    p = xl.p `perm_mul` tg.cbor_tagged_payload_perm;
  };
  Trade.elim_hyp_l _ _ _;
  Trade.rewrite_with_trade
    (cbor_match _ _ _)
    (cbor_match_with_perm res v);
  Trade.trans (cbor_match_with_perm res v) _ _;
  res
}

ghost
fn cbor_serialized_tagged_pts_to_serialized_with_perm_trade
  (xs: cbor_serialized)
  (p: perm)
  (xh0: raw_data_item { Tagged? xh0 })
  (res: with_perm (S.slice byte))
requires
  cbor_match_serialized_tagged xs p xh0 ** pure (
    res.v == (to_slice xs.cbor_serialized_payload) /\
    res.p == p `perm_mul` xs.cbor_serialized_perm
  )
ensures
  pts_to_serialized_with_perm serialize_raw_data_item res (Tagged?.v xh0) **
  Trade.trade
    (pts_to_serialized_with_perm (serialize_raw_data_item) res (Tagged?.v xh0) )
    (cbor_match_serialized_tagged xs p xh0)
{
  unfold (cbor_match_serialized_tagged xs p xh0);
  rewrite (cbor_match_serialized_payload_tagged (to_slice xs.cbor_serialized_payload) (p `perm_mul` xs.cbor_serialized_perm) (Tagged?.v xh0))
    as (pts_to_serialized_with_perm serialize_raw_data_item res (Tagged?.v xh0));
  intro
    (Trade.trade
      (pts_to_serialized_with_perm (serialize_raw_data_item) res (Tagged?.v xh0))
      (cbor_match_serialized_tagged xs p xh0)
    )
    #emp
    fn _
  { 
    rewrite (pts_to_serialized_with_perm (serialize_raw_data_item) res (Tagged?.v xh0))
      as (cbor_match_serialized_payload_tagged (to_slice xs.cbor_serialized_payload) (p `perm_mul` xs.cbor_serialized_perm) (Tagged?.v xh0));
    fold (cbor_match_serialized_tagged xs p xh0);
  };
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn ser_payload_tagged_not_tagged_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_tagged))
: vmatch_lens #_ #_ #_ (vmatch_with_cond (vmatch_ext raw_data_item (match_cbor_payload xh1))
      (pnot cbor_with_perm_case_tagged))
  (pts_to_serialized_with_perm serialize_raw_data_item)
= (xl: _)
  (v: _)
{
  vmatch_with_cond_elim_trade (vmatch_ext raw_data_item (match_cbor_payload xh1)) (pnot cbor_with_perm_case_tagged) _ _;
  let xh2 = vmatch_ext_elim_trade raw_data_item (match_cbor_payload xh1) _ _;
  Trade.trans (match_cbor_payload xh1 xl (Ghost.reveal xh2)) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl (Ghost.reveal xh2);
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match xl.p xl.v xh0) (cbor_match_with_perm xl xh0) _; // FIXME: WHY WHY WHY do I need to help Pulse here?
  cbor_match_cases xl.v;
  let CBOR_Case_Serialized_Tagged ser = xl.v;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_serialized_tagged ser xl.p xh0);
  Trade.trans (cbor_match_serialized_tagged ser xl.p xh0) _ _;
  let res = {
    v = (to_slice ser.cbor_serialized_payload);
    p = xl.p `perm_mul` ser.cbor_serialized_perm;
  };
  cbor_serialized_tagged_pts_to_serialized_with_perm_trade ser _ _ res;
  Trade.trans _ (cbor_match_serialized_tagged ser xl.p xh0) _;
  rewrite each (Tagged?.v xh0) as v;
  res
}

#pop-options

#push-options "--z3rlimit 32"

inline_for_extraction
let ser_payload_tagged
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_ifthenelse_low
      _ _
      cbor_with_perm_case_tagged
      (l2r_writer_lens
        (ser_payload_tagged_tagged_lens xh1 sq)
        f
      )
      (l2r_writer_lens
        (ser_payload_tagged_not_tagged_lens xh1 sq)
        (l2r_write_copy serialize_raw_data_item)
      )
    )
    _

inline_for_extraction
let size_payload_tagged
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_ifthenelse_low
      _ _
      cbor_with_perm_case_tagged
      (compute_remaining_size_lens
        (ser_payload_tagged_tagged_lens xh1 sq)
        f
      )
      (compute_remaining_size_lens
        (ser_payload_tagged_not_tagged_lens xh1 sq)
        (compute_remaining_size_copy serialize_raw_data_item)
      )
    )
    _

#pop-options

// ================= DEPTH-AWARE TAGGED WRITER TWINS (deliverables 9-11) =================
// The tagged case is simpler than array/map: a single child, no seq_list
// conversion. The inline (tagged) child is at depth `nat_pred n`; the writer
// `f` for it is `l2r_writer (cbor_match_with_perm_d (nat_pred n)) ...`.

#push-options "--z3rlimit 32"

// DELIVERABLE 9: depth-aware tagged node payload -> child lens. Mirrors the
// non-depth ser_payload_tagged_tagged_lens, but bridges cbor_match_with_perm_d n
// to cbor_match_with_depth n and uses cbor_match_with_depth_tagged_elim (which
// operates directly on cbor_match_with_depth n (CBOR_Case_Tagged tg) and yields
// the child at cbor_match_with_depth (nat_pred n)).
inline_for_extraction
fn ser_payload_tagged_tagged_lens_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_tagged))
: vmatch_lens #_ #_ #_ (vmatch_with_cond (vmatch_ext raw_data_item (match_cbor_payload_d n xh1))
      cbor_with_perm_case_tagged)
  (cbor_match_with_perm_d (nat_pred n))
= (xl: _)
  (v: _)
{
  vmatch_with_cond_elim_trade (vmatch_ext raw_data_item (match_cbor_payload_d n xh1)) cbor_with_perm_case_tagged _ _;
  let xh2 = vmatch_ext_elim_trade raw_data_item (match_cbor_payload_d n xh1) _ _;
  Trade.trans (match_cbor_payload_d n xh1 xl (Ghost.reveal xh2)) _ _;
  let xh0 = match_cbor_payload_elim_trade_d n xh1 xl (Ghost.reveal xh2);
  Trade.trans (cbor_match_with_perm_d n xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d n xl xh0)
    (cbor_match_with_depth n xl.p xl.v xh0);
  Trade.trans (cbor_match_with_depth n xl.p xl.v xh0) (cbor_match_with_perm_d n xl xh0) _;
  cbor_match_with_depth_cases n xl.p xl.v xh0;
  let CBOR_Case_Tagged tg = xl.v;
  Trade.rewrite_with_trade
    (cbor_match_with_depth n xl.p xl.v xh0)
    (cbor_match_with_depth n xl.p (CBOR_Case_Tagged tg) xh0);
  Trade.trans (cbor_match_with_depth n xl.p (CBOR_Case_Tagged tg) xh0) _ _;
  cbor_match_with_depth_tagged_elim n xl.p tg xh0;
  Trade.trans _ (cbor_match_with_depth n xl.p (CBOR_Case_Tagged tg) xh0) _;
  let pl = !(tg.cbor_tagged_ptr);
  let res = {
    v = pl;
    p = xl.p `perm_mul` tg.cbor_tagged_payload_perm;
  };
  Trade.elim_hyp_l _ _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_depth (nat_pred n) _ _ _)
    (cbor_match_with_perm_d (nat_pred n) res v);
  Trade.trans (cbor_match_with_perm_d (nat_pred n) res v) _ _;
  res
}

#pop-options

#push-options "--z3rlimit 64"

// DELIVERABLE 10: depth-aware serialized-tagged (not-tagged) case. Bridges the
// depth match to plain cbor_match via cbor_match_with_depth_to_match, then
// proceeds exactly as the non-depth serialized case (reusing the non-depth
// cbor_serialized_tagged_pts_to_serialized_with_perm_trade). No recursion / no `f`.
inline_for_extraction
fn ser_payload_tagged_not_tagged_lens_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_tagged))
: vmatch_lens #_ #_ #_ (vmatch_with_cond (vmatch_ext raw_data_item (match_cbor_payload_d n xh1))
      (pnot cbor_with_perm_case_tagged))
  (pts_to_serialized_with_perm serialize_raw_data_item)
= (xl: _)
  (v: _)
{
  vmatch_with_cond_elim_trade (vmatch_ext raw_data_item (match_cbor_payload_d n xh1)) (pnot cbor_with_perm_case_tagged) _ _;
  let xh2 = vmatch_ext_elim_trade raw_data_item (match_cbor_payload_d n xh1) _ _;
  Trade.trans (match_cbor_payload_d n xh1 xl (Ghost.reveal xh2)) _ _;
  let xh0 = match_cbor_payload_elim_trade_d n xh1 xl (Ghost.reveal xh2);
  Trade.trans (cbor_match_with_perm_d n xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d n xl xh0)
    (cbor_match_with_depth n xl.p xl.v xh0);
  Trade.trans (cbor_match_with_depth n xl.p xl.v xh0) (cbor_match_with_perm_d n xl xh0) _;
  cbor_match_with_depth_cases n xl.p xl.v xh0;
  cbor_match_with_depth_to_match n xl.v;
  Trade.trans (cbor_match xl.p xl.v xh0) (cbor_match_with_depth n xl.p xl.v xh0) _;
  cbor_match_cases xl.v;
  let CBOR_Case_Serialized_Tagged ser = xl.v;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_serialized_tagged ser xl.p xh0);
  Trade.trans (cbor_match_serialized_tagged ser xl.p xh0) _ _;
  let res = {
    v = (to_slice ser.cbor_serialized_payload);
    p = xl.p `perm_mul` ser.cbor_serialized_perm;
  };
  cbor_serialized_tagged_pts_to_serialized_with_perm_trade ser _ _ res;
  Trade.trans _ (cbor_match_serialized_tagged ser xl.p xh0) _;
  rewrite each (Tagged?.v xh0) as v;
  res
}

#pop-options

#push-options "--z3rlimit 32"

// DELIVERABLE 11: depth-aware tagged payload dispatcher.
inline_for_extraction
let ser_payload_tagged_d
  (n: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: l2r_writer (match_cbor_payload_d n xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_ifthenelse_low
      _ _
      cbor_with_perm_case_tagged
      (l2r_writer_lens
        (ser_payload_tagged_tagged_lens_d n xh1 sq)
        f
      )
      (l2r_writer_lens
        (ser_payload_tagged_not_tagged_lens_d n xh1 sq)
        (l2r_write_copy serialize_raw_data_item)
      )
    )
    _

inline_for_extraction
let size_payload_tagged_d
  (n: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: compute_remaining_size (match_cbor_payload_d n xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_ifthenelse_low
      _ _
      cbor_with_perm_case_tagged
      (compute_remaining_size_lens
        (ser_payload_tagged_tagged_lens_d n xh1 sq)
        f
      )
      (compute_remaining_size_lens
        (ser_payload_tagged_not_tagged_lens_d n xh1 sq)
        (compute_remaining_size_copy serialize_raw_data_item)
      )
    )
    _

#pop-options

inline_for_extraction
let ser_payload_scalar
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
  (sq_not_tagged: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_tagged == false))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (LP.l2r_write_empty _)
    _

inline_for_extraction
let size_payload_scalar
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
  (sq_not_tagged: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_tagged == false))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (LP.compute_remaining_size_empty _)
    _

inline_for_extraction
let ser_payload_not_string_not_array_not_map
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged)
    (ser_payload_tagged f xh1)
    (ser_payload_scalar xh1 () () ())

inline_for_extraction
let size_payload_not_string_not_array_not_map
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged)
    (size_payload_tagged f xh1)
    (size_payload_scalar xh1 () () ())

inline_for_extraction
let ser_payload_not_string_not_array
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map)
    (ser_payload_map f xh1)
    (ser_payload_not_string_not_array_not_map f xh1 () ())

inline_for_extraction
let size_payload_not_string_not_array
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map)
    (size_payload_map f xh1)
    (size_payload_not_string_not_array_not_map f xh1 () ())

inline_for_extraction
let ser_payload_not_string
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array)
    (ser_payload_array f xh1)
    (ser_payload_not_string_not_array f xh1 sq)

inline_for_extraction
let size_payload_not_string
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array)
    (size_payload_array f xh1)
    (size_payload_not_string_not_array f xh1 sq)

inline_for_extraction
let ser_payload
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (ser_payload_string xh1)
    (ser_payload_not_string f xh1)

inline_for_extraction
let size_payload
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (size_payload_string xh1)
    (size_payload_not_string f xh1)

// ================= DEPTH-AWARE SCALAR + DISPATCH WRITER TWINS (deliverables 13-17) =================
// The scalar case is a leaf (empty content, no recursion). The dispatch
// combinators are pure combinator plumbing threading the ghost depth `n` and
// the recursive writer `f` (at depth `nat_pred n`), typed at match_cbor_payload_d n xh1.

// DELIVERABLE 13: depth-aware scalar (leaf) writer. Empty content; no `f`.
inline_for_extraction
let ser_payload_scalar_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
  (sq_not_tagged: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_tagged == false))
: l2r_writer (match_cbor_payload_d n xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (LP.l2r_write_empty _)
    _

inline_for_extraction
let size_payload_scalar_d
  (n: Ghost.erased nat)
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
  (sq_not_tagged: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_tagged == false))
: compute_remaining_size (match_cbor_payload_d n xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (LP.compute_remaining_size_empty _)
    _

// DELIVERABLE 14: depth-aware dispatch (tagged vs scalar).
inline_for_extraction
let ser_payload_not_string_not_array_not_map_d
  (n: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
: l2r_writer (match_cbor_payload_d n xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged)
    (ser_payload_tagged_d n f xh1)
    (ser_payload_scalar_d n xh1 () () ())

inline_for_extraction
let size_payload_not_string_not_array_not_map_d
  (n: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
: compute_remaining_size (match_cbor_payload_d n xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged)
    (size_payload_tagged_d n f xh1)
    (size_payload_scalar_d n xh1 () () ())

// DELIVERABLE 15: depth-aware dispatch (map vs tagged/scalar).
inline_for_extraction
let ser_payload_not_string_not_array_d
  (n: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: l2r_writer (match_cbor_payload_d n xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map)
    (ser_payload_map_d n f xh1)
    (ser_payload_not_string_not_array_not_map_d n f xh1 () ())

inline_for_extraction
let size_payload_not_string_not_array_d
  (n: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: compute_remaining_size (match_cbor_payload_d n xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map)
    (size_payload_map_d n f xh1)
    (size_payload_not_string_not_array_not_map_d n f xh1 () ())

// DELIVERABLE 16: depth-aware dispatch (array vs map/tagged/scalar).
inline_for_extraction
let ser_payload_not_string_d
  (n: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
: l2r_writer (match_cbor_payload_d n xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array)
    (ser_payload_array_d n f xh1)
    (ser_payload_not_string_not_array_d n f xh1 sq)

inline_for_extraction
let size_payload_not_string_d
  (n: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
: compute_remaining_size (match_cbor_payload_d n xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array)
    (size_payload_array_d n f xh1)
    (size_payload_not_string_not_array_d n f xh1 sq)

// DELIVERABLE 17: depth-aware top-level payload dispatch (string vs everything else).
inline_for_extraction
let ser_payload_d
  (n: Ghost.erased nat)
  (f: l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
: l2r_writer (match_cbor_payload_d n xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (ser_payload_string_d n xh1)
    (ser_payload_not_string_d n f xh1)

inline_for_extraction
let size_payload_d
  (n: Ghost.erased nat)
  (f: compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
  (xh1: header)
: compute_remaining_size (match_cbor_payload_d n xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (size_payload_string_d n xh1)
    (size_payload_not_string_d n f xh1)

// ============================================================================
// DEPTH-TERMINATING RECURSION KNOT (ser'_d / siz'_d).
//
// NOTE ON DESIGN DEVIATION.  The task's literal deliverable-5 shape
//   `ser_body'_d n rec = if Ghost.reveal n = 0 then ser_base_d else ...`
// is impossible in Pulse: since `n : Ghost.erased nat`, `Ghost.reveal n = 0`
// is a GHOST boolean and Pulse rejects branching on it in effectful (stt)
// code ("Expected a Total computation, but got Ghost").  We instead follow the
// working idiom of `cbor_copy0_with_depth`: dispatch on the CONCRETE node
// structure.  A node whose serialization actually recurses (an inline tagged,
// or a NON-EMPTY inline array/map) forces `depth >= 1`, so `rec (nat_pred n)`
// typechecks; every other node (leaf / serialized / string / EMPTY inline
// array/map) is serialized by the non-recursive depth-0 base writer
// `ser_base_d`, reached from depth `n` via `shallow_to_zero` (these nodes'
// matches are depth-irrelevant).
// ============================================================================

// ---- (A) pure lemmas: an EMPTY inline array/map payload serializes to 0 bytes.

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let serialize_content_array_empty_from_nil
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
  (xh: content xh1)
  (xh0: raw_data_item)
: Lemma
    (requires Array? xh0 /\ synth_raw_data_item_recip xh0 == (| xh1, xh |) /\ Nil? (Array?.v xh0))
    (ensures Seq.length (bare_serialize (serialize_content xh1) xh) == 0)
= assert_norm (cbor_major_type_array == 4uy);
  assert_norm (cbor_major_type_simple_value == 7uy);
  assert_norm (cbor_major_type_byte_string == 2uy);
  assert_norm (cbor_major_type_text_string == 3uy);
  assert (~(long_argument_simple_value_prop (get_header_initial_byte xh1)));
  synth_raw_data_item_recip_inverse;
  assert (synth_raw_data_item (| xh1, xh |) == xh0);
  assert (List.Tot.length (Array?.v xh0) == U64.v (Array?.len xh0).value);
  assert (Array?.len xh0 == argument_as_raw_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1));
  assert (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)) == 0);
  let xh' : LowParse.Spec.VCList.nlist 0 raw_data_item = xh in
  LowParse.Spec.VCList.nlist_nil_unique raw_data_item xh';
  LowParse.Spec.VCList.serialize_nlist_nil _ serialize_raw_data_item
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let serialize_content_map_empty_from_nil
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
  (xh: content xh1)
  (xh0: raw_data_item)
: Lemma
    (requires Map? xh0 /\ synth_raw_data_item_recip xh0 == (| xh1, xh |) /\ Nil? (Map?.v xh0))
    (ensures Seq.length (bare_serialize (serialize_content xh1) xh) == 0)
= assert_norm (cbor_major_type_map == 5uy);
  assert_norm (cbor_major_type_array == 4uy);
  assert_norm (cbor_major_type_simple_value == 7uy);
  assert_norm (cbor_major_type_byte_string == 2uy);
  assert_norm (cbor_major_type_text_string == 3uy);
  assert (~(long_argument_simple_value_prop (get_header_initial_byte xh1)));
  synth_raw_data_item_recip_inverse;
  assert (synth_raw_data_item (| xh1, xh |) == xh0);
  assert (List.Tot.length (Map?.v xh0) == U64.v (Map?.len xh0).value);
  assert (Map?.len xh0 == argument_as_raw_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1));
  assert (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)) == 0);
  let xh' : LowParse.Spec.VCList.nlist 0 (raw_data_item & raw_data_item) = xh in
  LowParse.Spec.VCList.nlist_nil_unique (raw_data_item & raw_data_item) xh';
  LowParse.Spec.VCList.serialize_nlist_nil _ (serialize_raw_data_item `LowParse.Spec.Combinators.serialize_nondep_then` serialize_raw_data_item)
#pop-options

// ---- (B) ghost helpers: at depth 0 an inline array/map is necessarily empty,
// so its payload serializes to 0 bytes.  Mirrors ser_payload_array_array_lens_aux_d
// but PEEKs (array_peek at depth 0 forces emptiness) instead of transforming.

#push-options "--z3rlimit 32"
ghost
fn array_empty_at_zero
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
  (xl: with_perm cbor_raw)
  (xh: content xh1)
requires
  vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_array xl xh
ensures
  vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_array xl xh **
  pure (Seq.length (bare_serialize (serialize_content xh1) xh) == 0)
{
  vmatch_with_cond_elim_trade (match_cbor_payload_d 0 xh1) cbor_with_perm_case_array xl xh;
  let xh0 = match_cbor_payload_elim_trade_d 0 xh1 xl xh;
  Trade.trans (cbor_match_with_perm_d 0 xl xh0) (match_cbor_payload_d 0 xh1 xl xh) _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d 0 xl xh0)
    (cbor_match_with_depth 0 xl.p xl.v xh0);
  Trade.trans (cbor_match_with_depth 0 xl.p xl.v xh0) (cbor_match_with_perm_d 0 xl xh0) _;
  cbor_match_with_depth_cases 0 xl.p xl.v xh0;
  let CBOR_Case_Array a = xl.v;
  cbor_match_with_depth_eq_array 0 xl.p a xh0;
  depth_cb_eq 0 (Ghost.reveal xh0);
  Trade.rewrite_with_trade
    (cbor_match_with_depth 0 xl.p xl.v xh0)
    (cbor_match_array a xl.p xh0 (depth_cb 0 xh0));
  Trade.trans (cbor_match_array a xl.p xh0 (depth_cb 0 xh0)) _ _;
  unfold (cbor_match_array a xl.p xh0 (depth_cb 0 xh0));
  with s. assert (PM.seq_list_match s (Array?.v xh0)
    ((depth_cb 0 xh0) (xl.p `perm_mul` a.cbor_array_payload_perm)));
  array_peek 0 xh0 (xl.p `perm_mul` a.cbor_array_payload_perm) s;
  serialize_content_array_empty_from_nil xh1 sq xh xh0;
  fold (cbor_match_array a xl.p xh0 (depth_cb 0 xh0));
  Trade.elim (cbor_match_array a xl.p xh0 (depth_cb 0 xh0))
    (vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_array xl xh);
}
#pop-options

#push-options "--z3rlimit 32"
ghost
fn map_empty_at_zero
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
  (xl: with_perm cbor_raw)
  (xh: content xh1)
requires
  vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_map xl xh
ensures
  vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_map xl xh **
  pure (Seq.length (bare_serialize (serialize_content xh1) xh) == 0)
{
  vmatch_with_cond_elim_trade (match_cbor_payload_d 0 xh1) cbor_with_perm_case_map xl xh;
  let xh0 = match_cbor_payload_elim_trade_d 0 xh1 xl xh;
  Trade.trans (cbor_match_with_perm_d 0 xl xh0) (match_cbor_payload_d 0 xh1 xl xh) _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d 0 xl xh0)
    (cbor_match_with_depth 0 xl.p xl.v xh0);
  Trade.trans (cbor_match_with_depth 0 xl.p xl.v xh0) (cbor_match_with_perm_d 0 xl xh0) _;
  cbor_match_with_depth_cases 0 xl.p xl.v xh0;
  let CBOR_Case_Map a = xl.v;
  cbor_match_with_depth_eq_map0 0 xl.p a xh0;
  depth_cb_eq 0 (Ghost.reveal xh0);
  Trade.rewrite_with_trade
    (cbor_match_with_depth 0 xl.p xl.v xh0)
    (cbor_match_map0 a xl.p xh0 (depth_cb 0 xh0));
  Trade.trans (cbor_match_map0 a xl.p xh0 (depth_cb 0 xh0)) _ _;
  unfold (cbor_match_map0 a xl.p xh0 (depth_cb 0 xh0));
  with s. assert (PM.seq_list_match s (Map?.v xh0)
    (cbor_match_map_entry0 xh0 ((depth_cb 0 xh0) (xl.p `perm_mul` a.cbor_map_payload_perm))));
  map_peek 0 xh0 (xl.p `perm_mul` a.cbor_map_payload_perm) s;
  serialize_content_map_empty_from_nil xh1 sq xh xh0;
  fold (cbor_match_map0 a xl.p xh0 (depth_cb 0 xh0));
  Trade.elim (cbor_match_map0 a xl.p xh0 (depth_cb 0 xh0))
    (vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_map xl xh);
}
#pop-options

// ---- (C) EMPTY / IMPOSSIBLE payload writers at depth 0 (no children-writer).

#push-options "--z3rlimit 32"
inline_for_extraction
fn ser_payload_array_array_empty_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_array) (serialize_content xh1)
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  array_empty_at_zero xh1 sq x' x;
  serialize_length (serialize_content xh1) x;
  offset
}

inline_for_extraction
fn size_payload_array_array_empty_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_array) (serialize_content xh1)
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  array_empty_at_zero xh1 sq x' x;
  serialize_length (serialize_content xh1) x;
  true
}

inline_for_extraction
fn ser_payload_map_map_empty_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_map) (serialize_content xh1)
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  map_empty_at_zero xh1 sq x' x;
  serialize_length (serialize_content xh1) x;
  offset
}

inline_for_extraction
fn size_payload_map_map_empty_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (vmatch_with_cond (match_cbor_payload_d 0 xh1) cbor_with_perm_case_map) (serialize_content xh1)
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  map_empty_at_zero xh1 sq x' x;
  serialize_length (serialize_content xh1) x;
  true
}

// An INLINE tagged node cannot exist at depth 0 (a tagged always has a child,
// forcing depth >= 1).  We derive `pure False` via cbor_match_with_depth_tagged_elim
// and discharge the branch with `unreachable`.  Typed (like the tagged lenses it
// replaces) at `vmatch_ext raw_data_item (match_cbor_payload_d 0 xh1)` / serialize_raw_data_item.
inline_for_extraction
fn ser_payload_tagged_tagged_impossible_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: l2r_writer (vmatch_with_cond (vmatch_ext raw_data_item (match_cbor_payload_d 0 xh1)) cbor_with_perm_case_tagged) serialize_raw_data_item
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  vmatch_with_cond_elim_trade (vmatch_ext raw_data_item (match_cbor_payload_d 0 xh1)) cbor_with_perm_case_tagged x' x;
  let xh2 = vmatch_ext_elim_trade raw_data_item (match_cbor_payload_d 0 xh1) x' x;
  let xh0 = match_cbor_payload_elim_trade_d 0 xh1 x' (Ghost.reveal xh2);
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d 0 x' xh0)
    (cbor_match_with_depth 0 x'.p x'.v xh0);
  cbor_match_with_depth_cases 0 x'.p x'.v xh0;
  let CBOR_Case_Tagged tg = x'.v;
  Trade.rewrite_with_trade
    (cbor_match_with_depth 0 x'.p x'.v xh0)
    (cbor_match_with_depth 0 x'.p (CBOR_Case_Tagged tg) xh0);
  cbor_match_with_depth_tagged_elim 0 x'.p tg xh0;
  unreachable ();
  offset
}

inline_for_extraction
fn size_payload_tagged_tagged_impossible_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: compute_remaining_size (vmatch_with_cond (vmatch_ext raw_data_item (match_cbor_payload_d 0 xh1)) cbor_with_perm_case_tagged) serialize_raw_data_item
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  vmatch_with_cond_elim_trade (vmatch_ext raw_data_item (match_cbor_payload_d 0 xh1)) cbor_with_perm_case_tagged x' x;
  let xh2 = vmatch_ext_elim_trade raw_data_item (match_cbor_payload_d 0 xh1) x' x;
  let xh0 = match_cbor_payload_elim_trade_d 0 xh1 x' (Ghost.reveal xh2);
  Trade.rewrite_with_trade
    (cbor_match_with_perm_d 0 x' xh0)
    (cbor_match_with_depth 0 x'.p x'.v xh0);
  cbor_match_with_depth_cases 0 x'.p x'.v xh0;
  let CBOR_Case_Tagged tg = x'.v;
  Trade.rewrite_with_trade
    (cbor_match_with_depth 0 x'.p x'.v xh0)
    (cbor_match_with_depth 0 x'.p (CBOR_Case_Tagged tg) xh0);
  cbor_match_with_depth_tagged_elim 0 x'.p tg xh0;
  unreachable ();
  false
}
#pop-options

// ---- (D) BASE dispatch tree at depth 0 (mirror of ser_payload_d / size_payload_d
// with the children-consuming inline array/map/tagged branches replaced by the
// empty / impossible depth-0 writers).

inline_for_extraction
let ser_payload_array_base_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_array
    (ser_payload_array_array_empty_d xh1 sq)
    (ser_payload_array_not_array_d 0 xh1 sq)

inline_for_extraction
let size_payload_array_base_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse_low
    _ _
    cbor_with_perm_case_array
    (size_payload_array_array_empty_d xh1 sq)
    (size_payload_array_not_array_d 0 xh1 sq)

inline_for_extraction
let ser_payload_map_base_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_map
    (ser_payload_map_map_empty_d xh1 sq)
    (ser_payload_map_not_map_d 0 xh1 sq)

inline_for_extraction
let size_payload_map_base_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse_low
    _ _
    cbor_with_perm_case_map
    (size_payload_map_map_empty_d xh1 sq)
    (size_payload_map_not_map_d 0 xh1 sq)

#push-options "--z3rlimit 32"
inline_for_extraction
let ser_payload_tagged_base_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: l2r_writer (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_ifthenelse_low
      _ _
      cbor_with_perm_case_tagged
      (ser_payload_tagged_tagged_impossible_d xh1 sq)
      (l2r_writer_lens
        (ser_payload_tagged_not_tagged_lens_d 0 xh1 sq)
        (l2r_write_copy serialize_raw_data_item)
      )
    )
    _

inline_for_extraction
let size_payload_tagged_base_d
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: compute_remaining_size (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_ifthenelse_low
      _ _
      cbor_with_perm_case_tagged
      (size_payload_tagged_tagged_impossible_d xh1 sq)
      (compute_remaining_size_lens
        (ser_payload_tagged_not_tagged_lens_d 0 xh1 sq)
        (compute_remaining_size_copy serialize_raw_data_item)
      )
    )
    _
#pop-options

inline_for_extraction
let ser_payload_not_string_not_array_not_map_base_d
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
: l2r_writer (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged)
    (ser_payload_tagged_base_d xh1)
    (ser_payload_scalar_d 0 xh1 () () ())

inline_for_extraction
let size_payload_not_string_not_array_not_map_base_d
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
: compute_remaining_size (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged)
    (size_payload_tagged_base_d xh1)
    (size_payload_scalar_d 0 xh1 () () ())

inline_for_extraction
let ser_payload_not_string_not_array_base_d
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: l2r_writer (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map)
    (ser_payload_map_base_d xh1)
    (ser_payload_not_string_not_array_not_map_base_d xh1 () ())

inline_for_extraction
let size_payload_not_string_not_array_base_d
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: compute_remaining_size (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map)
    (size_payload_map_base_d xh1)
    (size_payload_not_string_not_array_not_map_base_d xh1 () ())

inline_for_extraction
let ser_payload_not_string_base_d
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
: l2r_writer (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array)
    (ser_payload_array_base_d xh1)
    (ser_payload_not_string_not_array_base_d xh1 sq)

inline_for_extraction
let size_payload_not_string_base_d
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
: compute_remaining_size (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array)
    (size_payload_array_base_d xh1)
    (size_payload_not_string_not_array_base_d xh1 sq)

inline_for_extraction
let ser_payload_base_d
  (xh1: header)
: l2r_writer (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (ser_payload_string_d 0 xh1)
    (ser_payload_not_string_base_d xh1)

inline_for_extraction
let size_payload_base_d
  (xh1: header)
: compute_remaining_size (match_cbor_payload_d 0 xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (size_payload_string_d 0 xh1)
    (size_payload_not_string_base_d xh1)

inline_for_extraction
let ser_body
  (f: LP.l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
: LP.l2r_writer (cbor_match_with_perm) serialize_raw_data_item
= LP.l2r_writer_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (LP.l2r_write_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (LP.l2r_write_dtuple2_recip_explicit_header
        write_header
        (cbor_raw_get_header')
        ()
        (ser_payload f)
      )
    )
    (Classical.forall_intro parse_raw_data_item_eq; serialize_raw_data_item)

inline_for_extraction
let size_body
  (f: LP.compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
: LP.compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item
= LP.compute_remaining_size_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (LP.compute_remaining_size_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (LP.compute_remaining_size_dtuple2_recip_explicit_header
        size_header
        (cbor_raw_get_header')
        ()
        (size_payload f)
      )
    )
    (Classical.forall_intro parse_raw_data_item_eq; serialize_raw_data_item)

let ser_pre
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
: Tot slprop
=
    (pts_to out v ** cbor_match_with_perm x' x ** pure (
      SZ.v offset + Seq.length (bare_serialize serialize_raw_data_item x) <= Seq.length v
    ))

let ser_post
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
  (res: SZ.t)
: Tot slprop
=
  exists* v' .
      pts_to out v' ** cbor_match_with_perm x' x ** pure (
      let bs = bare_serialize serialize_raw_data_item x in
      SZ.v res == SZ.v offset + Seq.length bs /\
      SZ.v res <= Seq.length v /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
      Seq.slice v' (SZ.v offset) (SZ.v res) `Seq.equal` bs
  )

inline_for_extraction
fn ser_fold
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre x' x out offset v) (fun res -> ser_post x' x out offset v res))
: LP.l2r_writer #_ #raw_data_item (cbor_match_with_perm) #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item
=
  (x': with_perm cbor_raw) (#x: raw_data_item) (out: S.slice LP.byte) (offset: SZ.t) (#v: Ghost.erased LP.bytes)
{
  fold (ser_pre x' x out offset v);
  let res = f x' x out offset v;
  unfold (ser_post x' x out offset v res);
  res
}

inline_for_extraction
fn ser_unfold
  (f: LP.l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre x' x out offset v)
returns res: SZ.t
ensures
  (ser_post x' x out offset v res)
{
  unfold (ser_pre x' x out offset v);
  let res = f x' out offset;
  fold (ser_post x' x out offset v res);
  res
}

inline_for_extraction
fn ser_body'
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre x' x out offset v) (fun res -> ser_post x' x out offset v res))
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre x' x out offset v)
returns res: SZ.t
ensures
  ser_post x' x out offset v res
{
  ser_unfold (ser_body (ser_fold f)) x' x out offset v;
}

// ==== DEPTH-INDEXED KNOT (proven-terminating). Mechanical mirrors first. ====

inline_for_extraction
let ser_body_d
  (n: Ghost.erased nat)
  (f: LP.l2r_writer (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
: LP.l2r_writer (cbor_match_with_perm_d n) serialize_raw_data_item
= LP.l2r_writer_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (LP.l2r_write_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (LP.l2r_write_dtuple2_recip_explicit_header
        write_header
        (cbor_raw_get_header'_d n)
        ()
        (ser_payload_d n f)
      )
    )
    (Classical.forall_intro parse_raw_data_item_eq; serialize_raw_data_item)

inline_for_extraction
let ser_body_base_d
: LP.l2r_writer (cbor_match_with_perm_d 0) serialize_raw_data_item
= LP.l2r_writer_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (LP.l2r_write_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (LP.l2r_write_dtuple2_recip_explicit_header
        write_header
        (cbor_raw_get_header'_d 0)
        ()
        ser_payload_base_d
      )
    )
    (Classical.forall_intro parse_raw_data_item_eq; serialize_raw_data_item)

let ser_pre_d
  (n: nat)
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
: Tot slprop
= (pts_to out v ** cbor_match_with_perm_d n x' x ** pure (
      SZ.v offset + Seq.length (bare_serialize serialize_raw_data_item x) <= Seq.length v
    ))

let ser_post_d
  (n: nat)
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
  (res: SZ.t)
: Tot slprop
= exists* v' .
      pts_to out v' ** cbor_match_with_perm_d n x' x ** pure (
      let bs = bare_serialize serialize_raw_data_item x in
      SZ.v res == SZ.v offset + Seq.length bs /\
      SZ.v res <= Seq.length v /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
      Seq.slice v' (SZ.v offset) (SZ.v res) `Seq.equal` bs
  )

inline_for_extraction
fn ser_fold_d
  (n: Ghost.erased nat)
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre_d n x' x out offset v) (fun res -> ser_post_d n x' x out offset v res))
: LP.l2r_writer #_ #raw_data_item (cbor_match_with_perm_d n) #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item
=
  (x': with_perm cbor_raw) (#x: raw_data_item) (out: S.slice LP.byte) (offset: SZ.t) (#v: Ghost.erased LP.bytes)
{
  fold (ser_pre_d n x' x out offset v);
  let res = f x' x out offset v;
  unfold (ser_post_d n x' x out offset v res);
  res
}

inline_for_extraction
fn ser_unfold_d
  (n: Ghost.erased nat)
  (f: LP.l2r_writer (cbor_match_with_perm_d n) serialize_raw_data_item)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre_d n x' x out offset v)
returns res: SZ.t
ensures
  (ser_post_d n x' x out offset v res)
{
  unfold (ser_pre_d n x' x out offset v);
  let res = f x' out offset;
  fold (ser_post_d n x' x out offset v res);
  res
}

inline_for_extraction
fn ser_base_d
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre_d 0 x' x out offset v)
returns res: SZ.t
ensures
  (ser_post_d 0 x' x out offset v res)
{
  ser_unfold_d 0 ser_body_base_d x' x out offset v
}

inline_for_extraction
let size_body_d
  (n: Ghost.erased nat)
  (f: LP.compute_remaining_size (cbor_match_with_perm_d (nat_pred n)) serialize_raw_data_item)
: LP.compute_remaining_size (cbor_match_with_perm_d n) serialize_raw_data_item
= LP.compute_remaining_size_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (LP.compute_remaining_size_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (LP.compute_remaining_size_dtuple2_recip_explicit_header
        size_header
        (cbor_raw_get_header'_d n)
        ()
        (size_payload_d n f)
      )
    )
    (Classical.forall_intro parse_raw_data_item_eq; serialize_raw_data_item)

inline_for_extraction
let size_body_base_d
: LP.compute_remaining_size (cbor_match_with_perm_d 0) serialize_raw_data_item
= LP.compute_remaining_size_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (LP.compute_remaining_size_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (LP.compute_remaining_size_dtuple2_recip_explicit_header
        size_header
        (cbor_raw_get_header'_d 0)
        ()
        size_payload_base_d
      )
    )
    (Classical.forall_intro parse_raw_data_item_eq; serialize_raw_data_item)

let size_pre_d
  (n: nat)
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: ref SZ.t)
  (v: SZ.t)
: Tot slprop
= (pts_to out v ** cbor_match_with_perm_d n x' x)

let size_post_d
  (n: nat)
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: ref SZ.t)
  (v: SZ.t)
  (res: bool)
: Tot slprop
= exists* v' .
      pts_to out v' ** cbor_match_with_perm_d n x' x ** pure (
        let bs = Seq.length (bare_serialize serialize_raw_data_item x) in
        (res == true <==> bs <= SZ.v v) /\
        (res == true ==> bs + SZ.v v' == SZ.v v)
      )

inline_for_extraction
fn size_fold_d
  (n: Ghost.erased nat)
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: ref SZ.t) -> (v: Ghost.erased SZ.t) -> stt bool (size_pre_d n x' x out v) (fun res -> size_post_d n x' x out v res))
: LP.compute_remaining_size #_ #raw_data_item (cbor_match_with_perm_d n) #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item
=
  (x': with_perm cbor_raw) (#x: raw_data_item) (out: _) (#v: _)
{
  fold (size_pre_d n x' x out v);
  let res = f x' x out v;
  unfold (size_post_d n x' x out v res);
  res
}

inline_for_extraction
fn size_unfold_d
  (n: Ghost.erased nat)
  (f: LP.compute_remaining_size (cbor_match_with_perm_d n) serialize_raw_data_item)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: ref SZ.t)
  (v: Ghost.erased SZ.t)
requires
  (size_pre_d n x' x out v)
returns res: bool
ensures
  (size_post_d n x' x out v res)
{
  unfold (size_pre_d n x' x out v);
  let res = f x' out;
  fold (size_post_d n x' x out v res);
  res
}

inline_for_extraction
fn size_base_d
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: ref SZ.t)
  (v: Ghost.erased SZ.t)
requires
  (size_pre_d 0 x' x out v)
returns res: bool
ensures
  (size_post_d 0 x' x out v res)
{
  size_unfold_d 0 size_body_base_d x' x out v
}

// `compute_deep c` is true exactly when serializing `c` recurses into children:
// an inline tagged, or a NON-EMPTY inline array/map.  (Empty inline containers,
// leaves, strings and serialized nodes are NOT deep and are handled by ser_base_d.)
let compute_deep (c: cbor_raw) : Tot bool =
  match c with
  | CBOR_Case_Tagged _ -> true
  | CBOR_Case_Array a -> not (S.len a.cbor_array_ptr = 0sz)
  | CBOR_Case_Map a -> not (S.len a.cbor_map_ptr = 0sz)
  | _ -> false

// ============================================================================
// Depth dispatch helpers for the recursive serializer (see NOTE ON DESIGN
// DEVIATION above).  `estab_deep_pos` proves that a DEEP node (compute_deep
// true) forces depth >= 1, so `rec (nat_pred n)` typechecks.  `shallow_to_zero`
// re-indexes a SHALLOW node's match (compute_deep false) to depth 0, with a
// trade back to depth n, so the depth-0 base writer `ser_base_d` applies.
// Two tiny SizeT lemmas support the emptiness reasoning.
// ============================================================================

let sz_len_nonzero (x: SZ.t) : Lemma (requires SZ.v x == 0) (ensures x == 0sz) =
  FStar.SizeT.size_v_inj x

let sz_pos (x: SZ.t) : Lemma (requires x <> 0sz) (ensures SZ.v x > 0) =
  if SZ.v x = 0 then sz_len_nonzero x else ()

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
ghost
fn estab_deep_pos
  (n: Ghost.erased nat)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
requires
  cbor_match_with_perm_d n x' x ** pure (compute_deep x'.v == true)
ensures
  cbor_match_with_perm_d n x' x ** pure (Ghost.reveal n >= 1)
{
  unfold (cbor_match_with_perm_d n x' x);
  cbor_match_with_depth_cases n x'.p x'.v x;
  match x'.v {
    norewrite
    CBOR_Case_Tagged a -> {
      rewrite (cbor_match_with_depth n x'.p x'.v x) as (cbor_match_with_depth n x'.p (CBOR_Case_Tagged a) x);
      cbor_match_with_depth_tagged_elim n x'.p a x;
      Trade.elim _ (cbor_match_with_depth n x'.p (CBOR_Case_Tagged a) x);
      rewrite (cbor_match_with_depth n x'.p (CBOR_Case_Tagged a) x) as (cbor_match_with_depth n x'.p x'.v x);
      fold (cbor_match_with_perm_d n x' x);
    }
    norewrite
    CBOR_Case_Array a -> {
      rewrite (cbor_match_with_depth n x'.p x'.v x) as (cbor_match_with_depth n x'.p (CBOR_Case_Array a) x);
      cbor_match_with_depth_array_elim n x'.p a x;
      with s. assert (
        pts_to a.cbor_array_ptr #(x'.p `perm_mul` a.cbor_array_array_perm) s **
        PM.seq_list_match s (Array?.v x) ((depth_cb n x) (x'.p `perm_mul` a.cbor_array_payload_perm)));
      sz_pos (S.len a.cbor_array_ptr);
      array_peek n x (x'.p `perm_mul` a.cbor_array_payload_perm) s;
      assert (pure (Ghost.reveal n >= 1));
      Trade.elim _ (cbor_match_with_depth n x'.p (CBOR_Case_Array a) x);
      rewrite (cbor_match_with_depth n x'.p (CBOR_Case_Array a) x) as (cbor_match_with_depth n x'.p x'.v x);
      fold (cbor_match_with_perm_d n x' x);
    }
    norewrite
    CBOR_Case_Map a -> {
      rewrite (cbor_match_with_depth n x'.p x'.v x) as (cbor_match_with_depth n x'.p (CBOR_Case_Map a) x);
      cbor_match_with_depth_map_elim n x'.p a x;
      with s. assert (
        pts_to a.cbor_map_ptr #(x'.p `perm_mul` a.cbor_map_array_perm) s **
        PM.seq_list_match s (Map?.v x) (cbor_match_map_entry0 x ((depth_cb n x) (x'.p `perm_mul` a.cbor_map_payload_perm))));
      sz_pos (S.len a.cbor_map_ptr);
      map_peek n x (x'.p `perm_mul` a.cbor_map_payload_perm) s;
      assert (pure (Ghost.reveal n >= 1));
      Trade.elim _ (cbor_match_with_depth n x'.p (CBOR_Case_Map a) x);
      rewrite (cbor_match_with_depth n x'.p (CBOR_Case_Map a) x) as (cbor_match_with_depth n x'.p x'.v x);
      fold (cbor_match_with_perm_d n x' x);
    }
    norewrite CBOR_Case_Int _ -> { fold (cbor_match_with_perm_d n x' x); }
    norewrite CBOR_Case_Simple _ -> { fold (cbor_match_with_perm_d n x' x); }
    norewrite CBOR_Case_String _ -> { fold (cbor_match_with_perm_d n x' x); }
    norewrite CBOR_Case_Serialized_Tagged _ -> { fold (cbor_match_with_perm_d n x' x); }
    norewrite CBOR_Case_Serialized_Array _ -> { fold (cbor_match_with_perm_d n x' x); }
    norewrite CBOR_Case_Serialized_Map _ -> { fold (cbor_match_with_perm_d n x' x); }
  }
}
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
ghost
fn shallow_to_zero
  (n: Ghost.erased nat)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
requires
  cbor_match_with_perm_d n x' x ** pure (compute_deep x'.v == false)
ensures
  cbor_match_with_perm_d 0 x' x ** Trade.trade (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x)
{
  unfold (cbor_match_with_perm_d n x' x);
  cbor_match_with_depth_cases n x'.p x'.v x;
  match x'.v {
    norewrite
    CBOR_Case_Array a -> {
      rewrite (cbor_match_with_depth n x'.p x'.v x) as (cbor_match_with_depth n x'.p (CBOR_Case_Array a) x);
      cbor_match_with_depth_eq_array n x'.p a x;
      depth_cb_eq n (Ghost.reveal x);
      rewrite (cbor_match_with_depth n x'.p (CBOR_Case_Array a) x) as (cbor_match_array a x'.p x (depth_cb n x));
      unfold (cbor_match_array a x'.p x (depth_cb n x));
      with s. assert (
        pts_to a.cbor_array_ptr #(x'.p `perm_mul` a.cbor_array_array_perm) s **
        PM.seq_list_match s (Array?.v x) ((depth_cb n x) (x'.p `perm_mul` a.cbor_array_payload_perm)));
      assert (pure (S.len a.cbor_array_ptr == 0sz));
      assert (pure (Nil? (Array?.v x)));
      PM.seq_list_match_nil_elim s (Array?.v x) ((depth_cb n x) (x'.p `perm_mul` a.cbor_array_payload_perm));
      PM.seq_list_match_nil_intro s (Array?.v x) ((depth_cb 0 x) (x'.p `perm_mul` a.cbor_array_payload_perm));
      fold (cbor_match_array a x'.p x (depth_cb 0 x));
      cbor_match_with_depth_eq_array 0 x'.p a x;
      depth_cb_eq 0 (Ghost.reveal x);
      rewrite (cbor_match_array a x'.p x (depth_cb 0 x)) as (cbor_match_with_depth 0 x'.p (CBOR_Case_Array a) x);
      rewrite (cbor_match_with_depth 0 x'.p (CBOR_Case_Array a) x) as (cbor_match_with_depth 0 x'.p x'.v x);
      fold (cbor_match_with_perm_d 0 x' x);
      intro
        (Trade.trade (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x))
        #(pure (x'.v == CBOR_Case_Array a))
        fn _
      {
        unfold (cbor_match_with_perm_d 0 x' x);
        rewrite (cbor_match_with_depth 0 x'.p x'.v x) as (cbor_match_with_depth 0 x'.p (CBOR_Case_Array a) x);
        cbor_match_with_depth_eq_array 0 x'.p a x;
        depth_cb_eq 0 (Ghost.reveal x);
        rewrite (cbor_match_with_depth 0 x'.p (CBOR_Case_Array a) x) as (cbor_match_array a x'.p x (depth_cb 0 x));
        unfold (cbor_match_array a x'.p x (depth_cb 0 x));
        with s2. assert (
          pts_to a.cbor_array_ptr #(x'.p `perm_mul` a.cbor_array_array_perm) s2 **
          PM.seq_list_match s2 (Array?.v x) ((depth_cb 0 x) (x'.p `perm_mul` a.cbor_array_payload_perm)));
        array_peek 0 x (x'.p `perm_mul` a.cbor_array_payload_perm) s2;
        assert (pure (Nil? (Array?.v x)));
        PM.seq_list_match_nil_elim s2 (Array?.v x) ((depth_cb 0 x) (x'.p `perm_mul` a.cbor_array_payload_perm));
        PM.seq_list_match_nil_intro s2 (Array?.v x) ((depth_cb n x) (x'.p `perm_mul` a.cbor_array_payload_perm));
        fold (cbor_match_array a x'.p x (depth_cb n x));
        cbor_match_with_depth_eq_array n x'.p a x;
        depth_cb_eq n (Ghost.reveal x);
        rewrite (cbor_match_array a x'.p x (depth_cb n x)) as (cbor_match_with_depth n x'.p (CBOR_Case_Array a) x);
        rewrite (cbor_match_with_depth n x'.p (CBOR_Case_Array a) x) as (cbor_match_with_depth n x'.p x'.v x);
        fold (cbor_match_with_perm_d n x' x);
      };
    }
    norewrite
    CBOR_Case_Map a -> {
      rewrite (cbor_match_with_depth n x'.p x'.v x) as (cbor_match_with_depth n x'.p (CBOR_Case_Map a) x);
      cbor_match_with_depth_eq_map0 n x'.p a x;
      depth_cb_eq n (Ghost.reveal x);
      rewrite (cbor_match_with_depth n x'.p (CBOR_Case_Map a) x) as (cbor_match_map0 a x'.p x (depth_cb n x));
      unfold (cbor_match_map0 a x'.p x (depth_cb n x));
      with s. assert (
        pts_to a.cbor_map_ptr #(x'.p `perm_mul` a.cbor_map_array_perm) s **
        PM.seq_list_match s (Map?.v x) (cbor_match_map_entry0 x ((depth_cb n x) (x'.p `perm_mul` a.cbor_map_payload_perm))));
      assert (pure (S.len a.cbor_map_ptr == 0sz));
      assert (pure (Nil? (Map?.v x)));
      PM.seq_list_match_nil_elim s (Map?.v x) (cbor_match_map_entry0 x ((depth_cb n x) (x'.p `perm_mul` a.cbor_map_payload_perm)));
      PM.seq_list_match_nil_intro s (Map?.v x) (cbor_match_map_entry0 x ((depth_cb 0 x) (x'.p `perm_mul` a.cbor_map_payload_perm)));
      fold (cbor_match_map0 a x'.p x (depth_cb 0 x));
      cbor_match_with_depth_eq_map0 0 x'.p a x;
      depth_cb_eq 0 (Ghost.reveal x);
      rewrite (cbor_match_map0 a x'.p x (depth_cb 0 x)) as (cbor_match_with_depth 0 x'.p (CBOR_Case_Map a) x);
      rewrite (cbor_match_with_depth 0 x'.p (CBOR_Case_Map a) x) as (cbor_match_with_depth 0 x'.p x'.v x);
      fold (cbor_match_with_perm_d 0 x' x);
      intro
        (Trade.trade (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x))
        #(pure (x'.v == CBOR_Case_Map a))
        fn _
      {
        unfold (cbor_match_with_perm_d 0 x' x);
        rewrite (cbor_match_with_depth 0 x'.p x'.v x) as (cbor_match_with_depth 0 x'.p (CBOR_Case_Map a) x);
        cbor_match_with_depth_eq_map0 0 x'.p a x;
        depth_cb_eq 0 (Ghost.reveal x);
        rewrite (cbor_match_with_depth 0 x'.p (CBOR_Case_Map a) x) as (cbor_match_map0 a x'.p x (depth_cb 0 x));
        unfold (cbor_match_map0 a x'.p x (depth_cb 0 x));
        with s2. assert (
          pts_to a.cbor_map_ptr #(x'.p `perm_mul` a.cbor_map_array_perm) s2 **
          PM.seq_list_match s2 (Map?.v x) (cbor_match_map_entry0 x ((depth_cb 0 x) (x'.p `perm_mul` a.cbor_map_payload_perm))));
        map_peek 0 x (x'.p `perm_mul` a.cbor_map_payload_perm) s2;
        assert (pure (Nil? (Map?.v x)));
        PM.seq_list_match_nil_elim s2 (Map?.v x) (cbor_match_map_entry0 x ((depth_cb 0 x) (x'.p `perm_mul` a.cbor_map_payload_perm)));
        PM.seq_list_match_nil_intro s2 (Map?.v x) (cbor_match_map_entry0 x ((depth_cb n x) (x'.p `perm_mul` a.cbor_map_payload_perm)));
        fold (cbor_match_map0 a x'.p x (depth_cb n x));
        cbor_match_with_depth_eq_map0 n x'.p a x;
        depth_cb_eq n (Ghost.reveal x);
        rewrite (cbor_match_map0 a x'.p x (depth_cb n x)) as (cbor_match_with_depth n x'.p (CBOR_Case_Map a) x);
        rewrite (cbor_match_with_depth n x'.p (CBOR_Case_Map a) x) as (cbor_match_with_depth n x'.p x'.v x);
        fold (cbor_match_with_perm_d n x' x);
      };
    }
    norewrite
    CBOR_Case_Tagged a -> {
      unreachable ();
    }
    norewrite CBOR_Case_Int _ -> {
      cbor_match_with_depth_to_match n x'.v;
      cbor_match_with_depth_intro_noninline 0 x'.p x'.v x;
      Trade.trans (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x);
      fold (cbor_match_with_perm_d 0 x' x);
      rewrite (Trade.trade (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x))
        as (Trade.trade (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x));
    }
    norewrite CBOR_Case_Simple _ -> {
      cbor_match_with_depth_to_match n x'.v;
      cbor_match_with_depth_intro_noninline 0 x'.p x'.v x;
      Trade.trans (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x);
      fold (cbor_match_with_perm_d 0 x' x);
      rewrite (Trade.trade (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x))
        as (Trade.trade (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x));
    }
    norewrite CBOR_Case_String _ -> {
      cbor_match_with_depth_to_match n x'.v;
      cbor_match_with_depth_intro_noninline 0 x'.p x'.v x;
      Trade.trans (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x);
      fold (cbor_match_with_perm_d 0 x' x);
      rewrite (Trade.trade (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x))
        as (Trade.trade (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x));
    }
    norewrite CBOR_Case_Serialized_Tagged _ -> {
      cbor_match_with_depth_to_match n x'.v;
      cbor_match_with_depth_intro_noninline 0 x'.p x'.v x;
      Trade.trans (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x);
      fold (cbor_match_with_perm_d 0 x' x);
      rewrite (Trade.trade (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x))
        as (Trade.trade (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x));
    }
    norewrite CBOR_Case_Serialized_Array _ -> {
      cbor_match_with_depth_to_match n x'.v;
      cbor_match_with_depth_intro_noninline 0 x'.p x'.v x;
      Trade.trans (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x);
      fold (cbor_match_with_perm_d 0 x' x);
      rewrite (Trade.trade (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x))
        as (Trade.trade (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x));
    }
    norewrite CBOR_Case_Serialized_Map _ -> {
      cbor_match_with_depth_to_match n x'.v;
      cbor_match_with_depth_intro_noninline 0 x'.p x'.v x;
      Trade.trans (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x);
      fold (cbor_match_with_perm_d 0 x' x);
      rewrite (Trade.trade (cbor_match_with_depth 0 x'.p x'.v x) (cbor_match_with_depth n x'.p x'.v x))
        as (Trade.trade (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x));
    }
  }
}
#pop-options

// ==== DEPTH-INDEXED DRIVERS (proven-terminating). Concrete dispatch on
// `compute_deep x'.v`: DEEP nodes (inline tagged / non-empty inline
// array/map) recurse at strictly-smaller ghost depth `nat_pred n` (justified
// by `estab_deep_pos` establishing `n >= 1`); NOT-deep nodes (leaves, strings,
// serialized, empty inline containers) are serialized by the non-recursive
// `ser_base_d` at depth 0, reached via `shallow_to_zero` (with a trade back). ====

inline_for_extraction
fn ser_body'_d
  (n: Ghost.erased nat)
  (recf: (n': Ghost.erased nat { Ghost.reveal n' < Ghost.reveal n }) -> (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre_d n' x' x out offset v) (fun res -> ser_post_d n' x' x out offset v res))
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre_d n x' x out offset v)
returns res: SZ.t
ensures
  ser_post_d n x' x out offset v res
{
  let deep = compute_deep x'.v;
  if (deep) {
    unfold (ser_pre_d n x' x out offset v);
    estab_deep_pos n x' x;
    nat_pred_succ n;
    fold (ser_pre_d n x' x out offset v);
    ser_unfold_d n (ser_body_d n (ser_fold_d (nat_pred n) (recf (nat_pred n)))) x' x out offset v
  } else {
    unfold (ser_pre_d n x' x out offset v);
    shallow_to_zero n x' x;
    fold (ser_pre_d 0 x' x out offset v);
    let res = ser_base_d x' x out offset v;
    unfold (ser_post_d 0 x' x out offset v res);
    Trade.elim (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x);
    fold (ser_post_d n x' x out offset v res);
    res
  }
}

fn rec ser'_d
  (n: Ghost.erased nat)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre_d n x' x out offset v)
returns res: SZ.t
ensures
  ser_post_d n x' x out offset v res
decreases (Ghost.reveal n)
{
  ser_body'_d n (fun (n': Ghost.erased nat { Ghost.reveal n' < Ghost.reveal n }) -> ser'_d n') x' x out offset v
}

inline_for_extraction
fn size_body'_d
  (n: Ghost.erased nat)
  (recf: (n': Ghost.erased nat { Ghost.reveal n' < Ghost.reveal n }) -> (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: ref SZ.t) -> (v: Ghost.erased SZ.t) -> stt bool (size_pre_d n' x' x out v) (fun res -> size_post_d n' x' x out v res))
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: ref SZ.t)
  (v: Ghost.erased SZ.t)
requires
  (size_pre_d n x' x out v)
returns res: bool
ensures
  size_post_d n x' x out v res
{
  let deep = compute_deep x'.v;
  if (deep) {
    unfold (size_pre_d n x' x out v);
    estab_deep_pos n x' x;
    nat_pred_succ n;
    fold (size_pre_d n x' x out v);
    size_unfold_d n (size_body_d n (size_fold_d (nat_pred n) (recf (nat_pred n)))) x' x out v
  } else {
    unfold (size_pre_d n x' x out v);
    shallow_to_zero n x' x;
    fold (size_pre_d 0 x' x out v);
    let res = size_base_d x' x out v;
    unfold (size_post_d 0 x' x out v res);
    Trade.elim (cbor_match_with_perm_d 0 x' x) (cbor_match_with_perm_d n x' x);
    fold (size_post_d n x' x out v res);
    res
  }
}

fn rec siz'_d
  (n: Ghost.erased nat)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: ref SZ.t)
  (v: Ghost.erased SZ.t)
requires
  (size_pre_d n x' x out v)
returns res: bool
ensures
  size_post_d n x' x out v res
decreases (Ghost.reveal n)
{
  size_body'_d n (fun (n': Ghost.erased nat { Ghost.reveal n' < Ghost.reveal n }) -> siz'_d n') x' x out v
}

fn cbor_serialize
  (x: cbor_raw)
  (output: S.slice U8.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
norewrite
requires
    (exists* v . cbor_match pm x y ** pts_to output v ** pure (Seq.length (serialize_cbor y) <= SZ.v (S.len output)))
returns res: SZ.t
ensures exists* v . cbor_match pm x y ** pts_to output v ** pure (
      let s = serialize_cbor y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))
    )
{
  S.pts_to_len output;
  cbor_match_match_with_depth pm x y;
  with n. assert (cbor_match_with_depth n pm x y);
  let xp : with_perm cbor_raw = { v = x; p = pm };
  rewrite (cbor_match_with_depth n pm x y) as (cbor_match_with_perm_d n xp y);
  let res = (ser_fold_d n (ser'_d n)) xp output 0sz;
  rewrite (cbor_match_with_perm_d n xp y) as (cbor_match_with_depth n pm x y);
  cbor_match_with_depth_forget n pm x y;
  with v . assert (pts_to output v);
  Seq.lemma_split v (SZ.v res);
  res
}

let size_pre
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: ref SZ.t)
  (v: SZ.t)
: Tot slprop
=
    (pts_to out v ** cbor_match_with_perm x' x)

let size_post
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: ref SZ.t)
  (v: SZ.t)
  (res: bool)
: Tot slprop
=
  exists* v' .
      pts_to out v' ** cbor_match_with_perm x' x ** pure (
        let bs = Seq.length (bare_serialize serialize_raw_data_item x) in
        (res == true <==> bs <= SZ.v v) /\
        (res == true ==> bs + SZ.v v' == SZ.v v)
      )

inline_for_extraction
fn size_fold
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: ref SZ.t) -> (v: Ghost.erased SZ.t) -> stt bool (size_pre x' x out v) (fun res -> size_post x' x out v res))
: compute_remaining_size #_ #raw_data_item (cbor_match_with_perm) #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item
=
  (x': with_perm cbor_raw) (#x: raw_data_item) (out: _) (#v: _)
{
  fold (size_pre x' x out v);
  let res = f x' x out v;
  unfold (size_post x' x out v res);
  res
}

inline_for_extraction
fn size_unfold
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: ref SZ.t)
  (v: Ghost.erased SZ.t)
requires
  (size_pre x' x out v)
returns res: bool
ensures
  (size_post x' x out v res)
{
  unfold (size_pre x' x out v);
  let res = f x' out;
  fold (size_post x' x out v res);
  res
}

inline_for_extraction
fn size_body'
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: ref SZ.t) -> (v: Ghost.erased SZ.t) -> stt bool (size_pre x' x out v) (fun res -> size_post x' x out v res))
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: ref SZ.t)
  (v: Ghost.erased SZ.t)
requires
  (size_pre x' x out v)
returns res: bool
ensures
  size_post x' x out v res
{
  size_unfold (size_body (size_fold f)) x' x out v;
}

fn cbor_size
  (x: cbor_raw)
  (bound: SZ.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
requires
    (cbor_match pm x y)
returns res: SZ.t
ensures cbor_match pm x y ** pure (
        cbor_size_post bound y res
    )
{
  serialize_length serialize_raw_data_item y;
  let mut output = bound;
  cbor_match_match_with_depth pm x y;
  with n. assert (cbor_match_with_depth n pm x y);
  let xp : with_perm cbor_raw = { v = x; p = pm };
  rewrite (cbor_match_with_depth n pm x y) as (cbor_match_with_perm_d n xp y);
  let res = (size_fold_d n (siz'_d n)) xp output;
  rewrite (cbor_match_with_perm_d n xp y) as (cbor_match_with_depth n pm x y);
  cbor_match_with_depth_forget n pm x y;
  if (res) {
    let rem = !output;
    SZ.sub bound rem;
  } else {
    0sz
  }
}

#push-options "--z3rlimit 32"
fn cbor_serialize_tag
  (tag: raw_uint64)
  (output: S.slice U8.t)
norewrite
requires
  (exists* v . pts_to output v)
returns res: SZ.t
ensures
  (exists* v . pts_to output v ** pure (cbor_serialize_tag_postcond tag output res v))
{
  serialize_cbor_tag_length tag;
  let h = raw_uint64_as_argument cbor_major_type_tagged tag;
  let mut slen = S.len output;
  let fits = size_header h slen;
  S.pts_to_len output;
  if (fits) {
    let res = write_header h output 0sz;
    S.pts_to_len output;
    res
  } else {
    0sz
  }
}
#pop-options

let seq_length_append_slice_left
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
= assert (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1)

module Swap = Pulse.Lib.Swap.Slice

#push-options "--z3rlimit 128"

inline_for_extraction noextract [@@noextract_to "krml"]
let sz_zero : SZ.t = 0sz

let cbor_serialize_array_postcond_zero
  (len: raw_uint64)
  (l: list raw_data_item)
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Lemma
  (requires (
    cbor_serialize_array_precond len l off v /\
    Seq.length (serialize_header (raw_uint64_as_argument cbor_major_type_array len)) > Seq.length v - SZ.v off
  ))
  (ensures (
    cbor_serialize_array_postcond len l sz_zero v
  ))
= serialize_array_eq len l;
  ()

let cbor_serialize_array_postcond_nonzero
  (len: raw_uint64)
  (l: list raw_data_item)
  (off: SZ.t)
  (v: Seq.seq U8.t)
  (res: SZ.t)
  (v2: Seq.seq U8.t)
  (v': Seq.seq U8.t)
: Lemma
  (requires (
    cbor_serialize_array_precond len l off v /\
    SZ.v res == Seq.length (Seq.append (serialize_header (raw_uint64_as_argument cbor_major_type_array len)) (serialize_cbor_list l)) /\
    Seq.length v == SZ.v res + Seq.length v2 /\
    v' == Seq.append (Seq.append (serialize_header (raw_uint64_as_argument cbor_major_type_array len)) (serialize_cbor_list l)) v2
  ))
  (ensures (
    cbor_serialize_array_postcond len l res v'
  ))
=
  serialize_array_eq len l;
  let h = raw_uint64_as_argument cbor_major_type_array len in
  serialize_length serialize_header h;
  seq_length_append_slice_left (Seq.append (serialize_header h) (serialize_cbor_list l)) v2;
  ()

#restart-solver

let cbor_serialize_array_post
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list raw_data_item))
  (off: SZ.t)
  (res: SZ.t)
: Tot slprop
=
  exists* v .
    pts_to out v **
    pure (cbor_serialize_array_postcond len l res v)

let cbor_serialize_array_t =
  (len: raw_uint64) ->
  (out: S.slice U8.t) ->
  (l: Ghost.erased (list raw_data_item)) ->
  (off: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_serialize_array_precond len l off v)
  )
  (fun res -> cbor_serialize_array_post len out l off res)

#restart-solver

#push-options "--z3rlimit 256"

fn cbor_serialize_array'
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list raw_data_item))
  (off: SZ.t)
norewrite
requires
  exists* v . pts_to out v **
    pure (cbor_serialize_array_precond len l off v)
returns res: SZ.t
ensures
  cbor_serialize_array_post len out l off res
{
  let sq_len : squash (SZ.v off == Seq.length (serialize_cbor_list l)) = ();
  with v . assert (pts_to out v);
  S.pts_to_len out;
  Seq.lemma_split v (SZ.v off);
  serialize_array_eq len l;
  let slen = S.len out;
  let mut rem = (SZ.sub slen off <: SZ.t);
  let h = raw_uint64_as_argument cbor_major_type_array len;
  serialize_length serialize_header h;
  let hfits = size_header h rem;
  if (hfits) {
    let llen = write_header h out off;
    let sp = S.split out llen;
    match sp {
      Mktuple2 sp1 sp2 -> {
        S.pts_to_len sp1;
        with v1 . assert (pts_to sp1 v1);
        with v2 . assert (pts_to sp2 v2);
        Seq.lemma_split v1 (SZ.v off);
        assert (pure (Seq.equal v1 (Seq.append (serialize_cbor_list l) (serialize_header h))));
        rewrite (pts_to sp1 v1) as (pts_to sp1 (Seq.append (serialize_cbor_list l) (serialize_header h)));
        Swap.slice_swap' sp1 off (serialize_cbor_list l) (serialize_header h);
        seq_length_append_slice_left (Seq.append (serialize_header h) (serialize_cbor_list l)) v2;
        S.join sp1 sp2 out;
        with v' . assert (pts_to out v');
        S.pts_to_len out;
        cbor_serialize_array_postcond_nonzero len l off v llen v2 v';
        assert (pure (cbor_serialize_array_postcond len l llen v'));
        fold (cbor_serialize_array_post len out l off llen);
        llen
      }
    }
  } else {
    cbor_serialize_array_postcond_zero len (Ghost.reveal l) off v;
    fold (cbor_serialize_array_post len out l off sz_zero);
    sz_zero
  }
}

#pop-options

fn cbor_serialize_array
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list raw_data_item))
  (off: SZ.t)
norewrite
requires
  exists* v . pts_to out v **
    pure (cbor_serialize_array_precond len l off v)
returns res: SZ.t
ensures
  exists* v .
    pts_to out v **
    pure (cbor_serialize_array_postcond len l res v)
{
  let res = cbor_serialize_array' len out l off;
  unfold (cbor_serialize_array_post len out l off res);
  res
}

#restart-solver

fn cbor_serialize_string
  (_: unit)
: cbor_serialize_string_t
=
  (ty: _)
  (off: _)
  (out: _)
  (#v: _)
{
  with v . assert (pts_to out v);
  S.pts_to_len out;
  Seq.lemma_split v (U64.v off.value);
  let w = Ghost.hide (Seq.slice v 0 (U64.v off.value));
  serialize_string_eq ty off w;
  let soff = SZ.uint64_to_sizet off.value;
  let slen = S.len out;
  let mut rem = (SZ.sub slen soff <: SZ.t);
  let h = raw_uint64_as_argument ty off;
  serialize_length serialize_header h;
  let hfits = size_header h rem;
  if (hfits) {
    let llen = write_header h out soff;
    let sp = S.split out llen;
    match sp {
      Mktuple2 sp1 sp2 -> {
        S.pts_to_len sp1;
        with v1 . assert (pts_to sp1 v1);
        with v2 . assert (pts_to sp2 v2);
        Seq.lemma_split v1 (SZ.v soff);
        assert (pure (Seq.equal v1 (Seq.append w (serialize_header h))));
        rewrite (pts_to sp1 v1) as (pts_to sp1 (Seq.append w (serialize_header h)));
        Swap.slice_swap' sp1 soff w (serialize_header h);
        seq_length_append_slice_left (Seq.append (serialize_header h) w) v2;
        S.join sp1 sp2 out;
        llen
      }
    }
  } else {
    sz_zero
  }
}

let cbor_serialize_map_postcond_zero
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Lemma
  (requires (
    cbor_serialize_map_precond len l off v /\
    Seq.length (serialize_header (raw_uint64_as_argument cbor_major_type_map len)) > Seq.length v - SZ.v off
  ))
  (ensures (
    cbor_serialize_map_postcond len l sz_zero v
  ))
= serialize_map_eq len l;
  ()

let cbor_serialize_map_postcond_nonzero
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (v: Seq.seq U8.t)
  (res: SZ.t)
  (v2: Seq.seq U8.t)
  (v': Seq.seq U8.t)
: Lemma
  (requires (
    cbor_serialize_map_precond len l off v /\
    SZ.v res == Seq.length (Seq.append (serialize_header (raw_uint64_as_argument cbor_major_type_map len)) (serialize_cbor_map l)) /\
    Seq.length v == SZ.v res + Seq.length v2 /\
    v' == Seq.append (Seq.append (serialize_header (raw_uint64_as_argument cbor_major_type_map len)) (serialize_cbor_map l)) v2
  ))
  (ensures (
    cbor_serialize_map_postcond len l res v'
  ))
=
  serialize_map_eq len l;
  let h = raw_uint64_as_argument cbor_major_type_map len in
  serialize_length serialize_header h;
  seq_length_append_slice_left (Seq.append (serialize_header h) (serialize_cbor_map l)) v2;
  ()

#restart-solver

let cbor_serialize_map_post
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off: SZ.t)
  (res: SZ.t)
: Tot slprop
=
  exists* v .
    pts_to out v **
    pure (cbor_serialize_map_postcond len l res v)

let cbor_serialize_map_t =
  (len: raw_uint64) ->
  (out: S.slice U8.t) ->
  (l: Ghost.erased (list (raw_data_item & raw_data_item))) ->
  (off: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_serialize_map_precond len l off v)
  )
  (fun res -> cbor_serialize_map_post len out l off res)

#pop-options

#push-options "--z3rlimit 256"

#restart-solver

fn cbor_serialize_map'
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off: SZ.t)
norewrite
requires
  exists* v . pts_to out v **
    pure (cbor_serialize_map_precond len l off v)
returns res: SZ.t
ensures
  cbor_serialize_map_post len out l off res
{
  let sq_len : squash (SZ.v off == Seq.length (serialize_cbor_map l)) = ();
  with v . assert (pts_to out v);
  S.pts_to_len out;
  Seq.lemma_split v (SZ.v off);
  serialize_map_eq len l;
  let slen = S.len out;
  let mut rem = (SZ.sub slen off <: SZ.t);
  let h = raw_uint64_as_argument cbor_major_type_map len;
  serialize_length serialize_header h;
  let hfits = size_header h rem;
  if (hfits) {
    let llen = write_header h out off;
    let sp = S.split out llen;
    match sp {
      Mktuple2 sp1 sp2 -> {
        S.pts_to_len sp1;
        with v1 . assert (pts_to sp1 v1);
        with v2 . assert (pts_to sp2 v2);
        Seq.lemma_split v1 (SZ.v off);
        assert (pure (Seq.equal v1 (Seq.append (serialize_cbor_map l) (serialize_header h))));
        rewrite (pts_to sp1 v1) as (pts_to sp1 (Seq.append (serialize_cbor_map l) (serialize_header h)));
        Swap.slice_swap' sp1 off (serialize_cbor_map l) (serialize_header h);
        seq_length_append_slice_left (Seq.append (serialize_header h) (serialize_cbor_map l)) v2;
        S.join sp1 sp2 out;
        with v' . assert (pts_to out v');
        S.pts_to_len out;
        cbor_serialize_map_postcond_nonzero len l off v llen v2 v';
        assert (pure (cbor_serialize_map_postcond len l llen v'));
        fold (cbor_serialize_map_post len out l off llen);
        llen
      }
    }
  } else {
    cbor_serialize_map_postcond_zero len (Ghost.reveal l) off v;
    fold (cbor_serialize_map_post len out l off sz_zero);
    sz_zero
  }
}

fn cbor_serialize_map
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off: SZ.t)
norewrite
requires
  exists* v . pts_to out v **
    pure (cbor_serialize_map_precond len l off v)
returns res: SZ.t
ensures
  exists* v .
    pts_to out v **
    pure (cbor_serialize_map_postcond len l res v)
{
  let res = cbor_serialize_map' len out l off;
  unfold (cbor_serialize_map_post len out l off res);
  res
}

#pop-options

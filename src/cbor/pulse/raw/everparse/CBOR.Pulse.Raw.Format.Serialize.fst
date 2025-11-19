module CBOR.Pulse.Raw.Format.Serialize
#lang-pulse
open Pulse.Lib.Pervasives
friend CBOR.Spec.Raw.Format
friend CBOR.Pulse.Raw.Format.Match
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

#push-options "--z3rlimit 32"

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
    CBOR_Case_Int _ -> {
      let ty = cbor_match_int_elim_type xl;
      let v = cbor_match_int_elim_value xl;
      raw_uint64_as_argument ty v
    }
    CBOR_Case_String _ -> {
      let ty = cbor_match_string_elim_type xl;
      let len = cbor_match_string_elim_length xl;
      raw_uint64_as_argument ty len
    }
    CBOR_Case_Tagged _ -> {
      let tag = cbor_match_tagged_get_tag xl;
      raw_uint64_as_argument cbor_major_type_tagged tag
    }
    CBOR_Case_Serialized_Tagged _ -> {
      let tag = cbor_match_tagged_get_tag xl;
      raw_uint64_as_argument cbor_major_type_tagged tag
    }
    CBOR_Case_Array _ -> {
      let len = cbor_match_array_get_length xl;
      raw_uint64_as_argument cbor_major_type_array len
    }
    CBOR_Case_Serialized_Array _ -> {
      let len = cbor_match_array_get_length xl;
      raw_uint64_as_argument cbor_major_type_array len
    }
    CBOR_Case_Map _ -> {
      let len = cbor_match_map_get_length xl;
      raw_uint64_as_argument cbor_major_type_map len
    }
    CBOR_Case_Serialized_Map _ -> {
      let len = cbor_match_map_get_length xl;
      raw_uint64_as_argument cbor_major_type_map len
    }
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
    _ _;
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
  Trade.trans
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      res x')
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
      res z
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
  (f64: squash SZ.fits_u64)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_array))
  (xl: with_perm cbor_raw)
  (xh: LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))) raw_data_item)
requires
  (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array)
      xl xh
  )
ensures
  LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
    cbor_with_perm_case_array_match_elem
    (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1))))
    xl xh **
  Trade.trade
    (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh)
      (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1))))
                  raw_data_item)
                  (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array)
                  xl xh
      )
{
  let xh2 = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          raw_data_item) (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) _ _ _;
  Trade.trans (match_cbor_payload xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 _ _;
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match _ _ _) (cbor_match_with_perm _ _) _; // FIXME: WHY WHY WHY do I need to help Pulse here?
  cbor_match_cases _;
  let CBOR_Case_Array a = xl.v;
  cbor_match_eq_array xl.p a xh0;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_array a xl.p xh0 cbor_match);
  Trade.trans (cbor_match_array a xl.p xh0 cbor_match) _ _;
  unfold (cbor_match_array a xl.p xh0 cbor_match);
  // let ar = Some?.v (cbor_with_perm_case_array_get xl);
  let Some ar = cbor_with_perm_case_array_get xl;
  rewrite each a.cbor_array_ptr as ar.v;
  LowParse.Pulse.VCList.nlist_match_slice_intro cbor_with_perm_case_array_get
    cbor_with_perm_case_array_match_elem
    (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1))))
    xl xh
    ar _
  ;
  intro
    (Trade.trade
      (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
        cbor_with_perm_case_array_match_elem
        (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
        xl xh
      )
      (cbor_match_array a xl.p xh0 cbor_match)
    )
    #emp
    fn _
  {
    unfold (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh
    );
    with (s : S.slice cbor_raw) #p v.
      assert S.pts_to s #p v;
    (* ^ There is a single pts_to in the context, rewrite the slice ptr into
       a.cbor_array_ptr and then let maching figure it out. *)
    rewrite S.pts_to s #p v as S.pts_to a.cbor_array_ptr #p v;
    fold (cbor_match_array a xl.p xh0 cbor_match);
    ()
  };
  Trade.trans _ (cbor_match_array a xl.p xh0 cbor_match) _;
}

#pop-options

inline_for_extraction
fn ser_payload_array_array_lens
  (f64: squash SZ.fits_u64)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_array))
:
vmatch_lens #_ #_ #_
  (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array))
  (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))))
=
  (x1': _)
  (x: _)
{
  ser_payload_array_array_lens_aux f64 xh1 sq x1' x;
  x1'
}

inline_for_extraction
let ser_payload_array_array
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_array_array_lens f64 xh1 sq)
      (LowParse.Pulse.VCList.l2r_write_nlist_as_slice
        cbor_with_perm_case_array_get
        cbor_with_perm_case_array_match_elem
        serialize_raw_data_item
        (ser_payload_array_array_elem f)
        (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
      )
    )
    (serialize_content xh1)

inline_for_extraction
let size_payload_array_array
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_array_array_lens f64 xh1 sq)
      (LowParse.Pulse.VCList.compute_remaining_size_nlist_as_slice
        cbor_with_perm_case_array_get
        cbor_with_perm_case_array_match_elem
        serialize_raw_data_item
        (size_payload_array_array_elem f)
        (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
      )
    )
    (serialize_content xh1)

ghost
fn cbor_serialized_array_pts_to_serialized_with_perm_trade
  (xs: cbor_serialized)
  (p: perm)
  (xh0: raw_data_item { Array? xh0 })
  (n: nat { n == U64.v (Array?.len xh0).value })
  (res: with_perm (S.slice byte))
requires
  cbor_match_serialized_array xs p xh0 ** pure (
    res.v == xs.cbor_serialized_payload /\
    res.p == p `perm_mul` xs.cbor_serialized_perm
  )
ensures
  pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0) **
  Trade.trade
    (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0) )
    (cbor_match_serialized_array xs p xh0)
{
  unfold (cbor_match_serialized_array xs p xh0);
  unfold (cbor_match_serialized_payload_array xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Array?.v xh0));
  with n' (r': LowParse.Spec.VCList.nlist n' raw_data_item) . assert
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' serialize_raw_data_item) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) r');
  rewrite (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' serialize_raw_data_item) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) r')
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
      as (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) (Array?.v xh0));
    fold (cbor_match_serialized_payload_array xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Array?.v xh0));
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
    v = xs.cbor_serialized_payload;
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

#pop-options

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

inline_for_extraction
let ser_payload_array
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_array
    (ser_payload_array_array f64 f xh1 sq)
    (ser_payload_array_not_array xh1 sq)

inline_for_extraction
let size_payload_array
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse_low
    _ _
    cbor_with_perm_case_array
    (size_payload_array_array f64 f xh1 sq)
    (size_payload_array_not_array xh1 sq)

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
  (f64: squash SZ.fits_u64)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_map))
  (xl: with_perm cbor_raw)
  (xh: LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
requires
  (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map)
      xl xh
  )
ensures
  LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
    cbor_with_perm_case_map_match_elem
    (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1))))
    xl xh **
  Trade.trade
    (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh)
      (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1))))
                  (raw_data_item & raw_data_item))
                  (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map)
                  xl xh
      )
{
  let xh2 = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          (raw_data_item & raw_data_item)) (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) _ _ _;
  Trade.trans (match_cbor_payload xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 _ _;
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match _ _ _) (cbor_match_with_perm xl xh0) _; // FIXME: WHY WHY WHY do I need to help Pulse here?
  cbor_match_cases _;
  let CBOR_Case_Map a = xl.v;
  cbor_match_eq_map0 xl.p a xh0;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_map0 a xl.p xh0 cbor_match);
  Trade.trans (cbor_match_map0 a xl.p xh0 cbor_match) _ _;
  cbor_match_map0_map_trade a xl.p xh0;
  Trade.trans (cbor_match_map xl.p a xh0) _ _;
  unfold (cbor_match_map xl.p a xh0);
  let Some ar = cbor_with_perm_case_map_get xl;
  rewrite each a.cbor_map_ptr as (Mkwith_perm?.v ar);
  LowParse.Pulse.VCList.nlist_match_slice_intro cbor_with_perm_case_map_get
    cbor_with_perm_case_map_match_elem
    (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1))))
    xl xh
    ar _
  ;
  intro
    (Trade.trade
      (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
        cbor_with_perm_case_map_match_elem
        (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
          (get_header_long_argument xh1))))
        xl xh
      )
      (cbor_match_map xl.p a xh0)
    )
    #emp
    fn _
  {
    unfold (    LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh
    );
    with ar _p _v. assert (S.pts_to #cbor_map_entry (Mkwith_perm?.v ar) #_p _v);
    rewrite each (Mkwith_perm?.v ar) as a.cbor_map_ptr;
    fold (cbor_match_map xl.p a xh0);
    ()
  };
  Trade.trans _ (cbor_match_map xl.p a xh0) _;
}

#pop-options

inline_for_extraction
fn ser_payload_map_map_lens
  (f64: squash SZ.fits_u64)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_map))
:
vmatch_lens #_ #_ #_
  (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map))
  (LowParse.Pulse.VCList.nlist_match_slice cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))))
=
  (x1': _)
  (x: _)
{
  ser_payload_map_map_lens_aux f64 xh1 sq x1' x;
  x1'
}

inline_for_extraction
let ser_payload_map_map
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_map_map_lens f64 xh1 sq)
      (LowParse.Pulse.VCList.l2r_write_nlist_as_slice
        cbor_with_perm_case_map_get
        cbor_with_perm_case_map_match_elem
        (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
        (ser_payload_map_map_elem f)
        (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
      )
    )
    (serialize_content xh1)

inline_for_extraction
let size_payload_map_map
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_map_map_lens f64 xh1 sq)
      (LowParse.Pulse.VCList.compute_remaining_size_nlist_as_slice
        cbor_with_perm_case_map_get
        cbor_with_perm_case_map_match_elem
        (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
        (size_payload_map_map_elem f)
        (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
      )
    )
    (serialize_content xh1)

ghost
fn cbor_serialized_map_pts_to_serialized_with_perm_trade
  (xs: cbor_serialized)
  (p: perm)
  (xh0: raw_data_item { Map? xh0 })
  (n: nat { n == U64.v (Map?.len xh0).value })
  (res: with_perm (S.slice byte))
requires
  cbor_match_serialized_map xs p xh0 ** pure (
    res.v == xs.cbor_serialized_payload /\
    res.p == p `perm_mul` xs.cbor_serialized_perm
  )
ensures
  pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0) **
  Trade.trade
    (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0) )
    (cbor_match_serialized_map xs p xh0)
{
  unfold (cbor_match_serialized_map xs p xh0);
  unfold (cbor_match_serialized_payload_map xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Map?.v xh0));
  with n' (r': LowParse.Spec.VCList.nlist n' (raw_data_item & raw_data_item)) . assert
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) r');
  rewrite (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) r')
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
      as (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) (Map?.v xh0));
    fold (cbor_match_serialized_payload_map xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Map?.v xh0));
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
    v = xs.cbor_serialized_payload;
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

#pop-options

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

inline_for_extraction
let ser_payload_map
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_map
    (ser_payload_map_map f64 f xh1 sq)
    (ser_payload_map_not_map xh1 sq)

inline_for_extraction
let size_payload_map
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse_low
    _ _
    cbor_with_perm_case_map
    (size_payload_map_map f64 f xh1 sq)
    (size_payload_map_not_map xh1 sq)

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
  Trade.trans (match_cbor_payload xh1 xl xh2) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl xh2;
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
    res.v == xs.cbor_serialized_payload /\
    res.p == p `perm_mul` xs.cbor_serialized_perm
  )
ensures
  pts_to_serialized_with_perm serialize_raw_data_item res (Tagged?.v xh0) **
  Trade.trade
    (pts_to_serialized_with_perm (serialize_raw_data_item) res (Tagged?.v xh0) )
    (cbor_match_serialized_tagged xs p xh0)
{
  unfold (cbor_match_serialized_tagged xs p xh0);
  rewrite (cbor_match_serialized_payload_tagged xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Tagged?.v xh0))
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
      as (cbor_match_serialized_payload_tagged xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Tagged?.v xh0));
    fold (cbor_match_serialized_tagged xs p xh0);
  };
}

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
  Trade.trans (match_cbor_payload xh1 xl xh2) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl xh2;
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
    v = ser.cbor_serialized_payload;
    p = xl.p `perm_mul` ser.cbor_serialized_perm;
  };
  cbor_serialized_tagged_pts_to_serialized_with_perm_trade ser _ _ res;
  Trade.trans _ (cbor_match_serialized_tagged ser xl.p xh0) _;
  res
}

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
  (f64: squash SZ.fits_u64)
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
  (f64: squash SZ.fits_u64)
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
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map)
    (ser_payload_map f64 f xh1)
    (ser_payload_not_string_not_array_not_map f64 f xh1 () ())

inline_for_extraction
let size_payload_not_string_not_array
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map)
    (size_payload_map f64 f xh1)
    (size_payload_not_string_not_array_not_map f64 f xh1 () ())

inline_for_extraction
let ser_payload_not_string
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array)
    (ser_payload_array f64 f xh1)
    (ser_payload_not_string_not_array f64 f xh1 sq)

inline_for_extraction
let size_payload_not_string
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array)
    (size_payload_array f64 f xh1)
    (size_payload_not_string_not_array f64 f xh1 sq)

inline_for_extraction
let ser_payload
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (ser_payload_string xh1)
    (ser_payload_not_string f64 f xh1)

inline_for_extraction
let size_payload
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (size_payload_string xh1)
    (size_payload_not_string f64 f xh1)

inline_for_extraction
let ser_body
  (f64: squash SZ.fits_u64)
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
        (ser_payload f64 f)
      )
    )
    (Classical.forall_intro parse_raw_data_item_eq; serialize_raw_data_item)

inline_for_extraction
let size_body
  (f64: squash SZ.fits_u64)
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
        (size_payload f64 f)
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
  (f64: squash SZ.fits_u64)
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
  ser_unfold (ser_body f64 (ser_fold f)) x' x out offset v;
}

fn rec ser'
  (f64: squash SZ.fits_u64)
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
  ser_body' f64 (ser' f64) x' x out offset v
}

let ser (f64: squash SZ.fits_u64) (p: perm) : l2r_writer (cbor_match p) serialize_raw_data_item =
  l2r_writer_lens
    (cbor_match_with_perm_lens p)
    (ser_fold (ser' f64))

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
  let sq : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len output;
  let res = ser sq _ x output 0sz;
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
  (f64: squash SZ.fits_u64)
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
  size_unfold (size_body f64 (size_fold f)) x' x out v;
}

fn rec siz'
  (f64: squash SZ.fits_u64)
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
  size_body' f64 (siz' f64) x' x out v
}

let siz (f64: squash SZ.fits_u64) (p: perm) : compute_remaining_size (cbor_match p) serialize_raw_data_item =
  compute_remaining_size_lens
    (cbor_match_with_perm_lens p)
    (size_fold (siz' f64))

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
  let sq : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let mut output = bound;
  let res = siz sq pm x output;
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

#push-options "--z3rlimit 64"

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
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
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

module CBOR.Pulse.Raw.EverParse.Serialize
#lang-pulse
open Pulse.Lib.Pervasives
friend CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.Format
open LowParse.Spec.Base
open LowParse.Pulse.Base
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Type
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Base
module LP = LowParse.Pulse.Combinators
open LowParse.Pulse.Combinators
module LPI = LowParse.Pulse.Int
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module I = LowParse.PulseParse.Iterator
module LPIter = LowParse.Pulse.Iterator
module PPB = LowParse.PulseParse.Base
module Trade = Pulse.Lib.Trade.Util

(* ================================================================ *)
(* Part 1: Header writers — pure LowParse combinators, no match dep *)
(* ================================================================ *)

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

(* ================================================================ *)
(* Part 2: Bridge between cbor_raw_match and LowParse combinators   *)
(* ================================================================ *)

let cbor_raw_match_with_perm
  (x: with_perm cbor_raw)
  (y: raw_data_item)
: Tot slprop
= cbor_raw_match x.p x.v y

inline_for_extraction
fn cbor_raw_match_with_perm_lens
  (p: perm)
: vmatch_lens #_ #_ #_ (cbor_raw_match p) cbor_raw_match_with_perm
=
  (x: cbor_raw)
  (y: raw_data_item)
{
  let res : with_perm cbor_raw = {
    v = x;
    p = p;
  };
  Trade.rewrite_with_trade
    (cbor_raw_match p x y)
    (cbor_raw_match_with_perm res y);
  res
}

let synth_raw_data_item_recip_synth_raw_data_item
  (x: _)
: Lemma
  (synth_raw_data_item_recip (synth_raw_data_item x) == x)
= assert (synth_raw_data_item (synth_raw_data_item_recip (synth_raw_data_item x)) == synth_raw_data_item x)

(* Extract header from the concrete cbor_raw value *)
#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
let cbor_raw_get_header_pure (xl: cbor_raw) : Tot (option header) =
  match xl with
  | CBOR_Case_Int v ->
    Some (raw_uint64_as_argument v.cbor_int_type
      ({ size = v.cbor_int_size; value = v.cbor_int_value }))
  | CBOR_Case_Simple v ->
    Some (simple_value_as_argument v)
  | CBOR_Case_String v ->
    Some (raw_uint64_as_argument v.cbor_string_type
      ({ size = v.cbor_string_size;
         value = U64.uint_to_t (SZ.v (S.len v.cbor_string_ptr)) }))
  | CBOR_Case_Array v ->
    Some (raw_uint64_as_argument cbor_major_type_array
      ({ size = v.cbor_array_length_size;
         value = U64.uint_to_t (SZ.v (I.mixed_list_length v.cbor_array_ptr)) }))
  | CBOR_Case_Map v ->
    Some (raw_uint64_as_argument cbor_major_type_map
      ({ size = v.cbor_map_length_size;
         value = U64.uint_to_t (SZ.v (I.mixed_list_length v.cbor_map_ptr)) }))
  | CBOR_Case_Tagged v ->
    Some (raw_uint64_as_argument cbor_major_type_tagged v.cbor_tagged_tag)
  | CBOR_Case_Tagged_Serialized v ->
    Some (raw_uint64_as_argument cbor_major_type_tagged v.cbor_tagged_serialized_tag)
  | CBOR_Case_Invalid -> None

fn cbor_raw_get_header_impl
  (pm: perm)
  (xl: cbor_raw)
  (xh: erased raw_data_item)
requires
      (cbor_raw_match pm xl xh)
returns res: header
ensures
          cbor_raw_match pm xl xh **
          pure (res == get_raw_data_item_header xh)
{
  cbor_raw_match_unfold_aux xl;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm xl xh);
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
    as
    (pure (cbor_raw_get_header xl ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  let the_prop = cbor_raw_get_header xl ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)));
  let sq = elim_pure_explicit the_prop;
  let Some res = cbor_raw_get_header_pure xl;
  intro_pure the_prop sq;
  rewrite (pure the_prop)
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm xl (Ghost.reveal xh));
  cbor_raw_match_fold_aux xl;
  res
}

#pop-options

fn cbor_raw_with_perm_get_header
  (xl: with_perm cbor_raw)
  (xh: erased raw_data_item)
requires
      (cbor_raw_match_with_perm xl xh)
returns res: header
ensures
          cbor_raw_match_with_perm xl xh **
          pure (res == get_raw_data_item_header xh)
{
  unfold (cbor_raw_match_with_perm xl xh);
  let res = cbor_raw_get_header_impl xl.p xl.v xh;
  fold (cbor_raw_match_with_perm xl xh);
  res
}

inline_for_extraction
fn cbor_raw_get_header'
  (xl: with_perm cbor_raw)
  (xh: erased (dtuple2 header content))
requires
      (LP.vmatch_synth (cbor_raw_match_with_perm) synth_raw_data_item xl (reveal xh))
returns res: header
ensures
          LP.vmatch_synth (cbor_raw_match_with_perm) synth_raw_data_item xl (reveal xh) **
          pure (res == dfst (reveal xh))
{
  synth_raw_data_item_recip_synth_raw_data_item xh;
  unfold (LP.vmatch_synth (cbor_raw_match_with_perm) synth_raw_data_item xl (reveal xh));
  let res = cbor_raw_with_perm_get_header xl _;
  fold (LP.vmatch_synth (cbor_raw_match_with_perm) synth_raw_data_item xl (reveal xh));
  res
}

let match_cbor_payload
  (xh1: header)
=
        (LP.vmatch_dep_proj2
            (LP.vmatch_synth
                (cbor_raw_match_with_perm)
                synth_raw_data_item
            )
            xh1
        )

ghost
fn match_cbor_payload_elim_trade
  (xh1: header)
  (xl: with_perm cbor_raw)
  (xh: content xh1)
requires
  match_cbor_payload xh1 xl xh
returns xh': Ghost.erased raw_data_item
ensures
  (cbor_raw_match_with_perm xl xh' **
    Trade.trade
      (cbor_raw_match_with_perm xl xh')
      (match_cbor_payload xh1 xl xh) **
    pure (synth_raw_data_item_recip xh' == (| xh1, xh |))
  )
{
  Trade.rewrite_with_trade
    (match_cbor_payload xh1 xl xh)
    (cbor_raw_match_with_perm xl (synth_raw_data_item (| xh1, xh |)));
  synth_raw_data_item_recip_synth_raw_data_item (| xh1, xh |);
  synth_raw_data_item (| xh1, xh |)
}

(* ================================================================ *)
(* Part 3: Payload writers for each content type                    *)
(* ================================================================ *)

(* --- Scalar payload (Int, Simple) --- *)

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

(* --- String payload --- *)

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
  (cbor_raw_match_with_perm xl xh' **
    Trade.trade
      (cbor_raw_match_with_perm xl xh')
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
  Trade.trans (cbor_raw_match_with_perm xl xh') _ _;
  xh'
}

open CBOR.Pulse.Raw.EverParse.Access

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
    (cbor_raw_match_with_perm x1' xh')
    (cbor_raw_match x1'.p x1'.v xh');
  Trade.trans
    (cbor_raw_match x1'.p x1'.v xh')
    (cbor_raw_match_with_perm x1' xh') _;
  let s = cbor_raw_get_string x1'.p x1'.v ();
  Trade.trans _ (cbor_raw_match _ x1'.v xh') _;
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
    (LP.vmatch_filter
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
      (LP.l2r_write_filter
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
      (LP.compute_remaining_size_filter
        _
        (LowParse.Pulse.SeqBytes.compute_remaining_size_lseq_bytes_copy
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
        )
        (lseq_utf8_correct (get_header_initial_byte xh1).major_type _)
      )
    )
    (serialize_content xh1)

(* --- Array payload --- *)

(* For the array case, the new match uses mixed_list_match directly.
   We need a lens from match_cbor_payload to mixed_list_match_for_l2r,
   then use l2r_write_mixed_list. *)

let cbor_raw_match_elem
  (xl: with_perm cbor_raw)
: (x: cbor_raw) ->
  (y: raw_data_item) ->
  Tot slprop
= cbor_raw_match
    (xl.p *. (match xl.v with CBOR_Case_Array a -> a.cbor_array_slice_perm | _ -> 1.0R))

inline_for_extraction
let ser_payload_array_elem
  (f: l2r_writer cbor_raw_match_with_perm serialize_raw_data_item)
  (a: with_perm cbor_raw)
: l2r_writer (cbor_raw_match_elem a) serialize_raw_data_item
= l2r_writer_lens
    (cbor_raw_match_with_perm_lens _)
    f

inline_for_extraction
let size_payload_array_elem
  (f: compute_remaining_size cbor_raw_match_with_perm serialize_raw_data_item)
  (a: with_perm cbor_raw)
: compute_remaining_size (cbor_raw_match_elem a) serialize_raw_data_item
= compute_remaining_size_lens
    (cbor_raw_match_with_perm_lens _)
    f

(* --- Tagged payload --- *)

(* The tagged case has two variants:
   CBOR_Case_Tagged → recursive write using f
   CBOR_Case_Tagged_Serialized → copy from pts_to_parsed_strong_prefix *)

inline_for_extraction
let cbor_with_perm_case_tagged
  (c: with_perm cbor_raw)
: Tot bool
= match c.v with
  | CBOR_Case_Tagged _ -> true
  | _ -> false

(* Tagged-variant lens: from match_cbor_payload to cbor_raw_match_with_perm (for recursive write) *)

#push-options "--z3rlimit 64"

inline_for_extraction
fn ser_payload_tagged_tagged_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: vmatch_lens #_ #_ #_
  (vmatch_with_cond (vmatch_ext raw_data_item (match_cbor_payload xh1)) cbor_with_perm_case_tagged)
  cbor_raw_match_with_perm
= (xl: _) (z: _) {
  vmatch_with_cond_elim_trade (vmatch_ext raw_data_item (match_cbor_payload xh1)) cbor_with_perm_case_tagged xl z;
  let xh2 = vmatch_ext_elim_trade raw_data_item (match_cbor_payload xh1) xl z;
  Trade.trans (match_cbor_payload xh1 xl xh2) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl xh2;
  Trade.trans (cbor_raw_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_raw_match_with_perm xl xh0)
    (cbor_raw_match xl.p xl.v xh0);
  Trade.trans (cbor_raw_match xl.p xl.v xh0) (cbor_raw_match_with_perm xl xh0) _;
  let sq64 : squash SZ.fits_u64 = assume (SZ.fits_u64);
  let payload = cbor_raw_get_tagged_payload xl.p xl.v sq64 ();
  with pm' payload_xh . assert (cbor_raw_match pm' payload payload_xh);
  Trade.trans (cbor_raw_match pm' payload payload_xh) (cbor_raw_match xl.p xl.v xh0) _;
  let res = { v = payload; p = pm' };
  Trade.rewrite_with_trade
    (cbor_raw_match pm' payload payload_xh)
    (cbor_raw_match_with_perm res z);
  Trade.trans (cbor_raw_match_with_perm res z)
    (cbor_raw_match pm' payload payload_xh) _;
  res
}

#pop-options

(* Tagged_Serialized-variant lens: from match_cbor_payload to pts_to_serialized_with_perm (for copy) *)

#push-options "--z3rlimit 64"

inline_for_extraction
fn ser_payload_tagged_not_tagged_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: vmatch_lens #_ #_ #_
  (vmatch_with_cond (vmatch_ext raw_data_item (match_cbor_payload xh1)) (pnot cbor_with_perm_case_tagged))
  (pts_to_serialized_with_perm serialize_raw_data_item)
= (xl: _) (z: _) {
  vmatch_with_cond_elim_trade (vmatch_ext raw_data_item (match_cbor_payload xh1)) (pnot cbor_with_perm_case_tagged) xl z;
  let xh2 = vmatch_ext_elim_trade raw_data_item (match_cbor_payload xh1) xl z;
  Trade.trans (match_cbor_payload xh1 xl xh2) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl xh2;
  Trade.trans (cbor_raw_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_raw_match_with_perm xl xh0)
    (cbor_raw_match xl.p xl.v xh0);
  Trade.trans (cbor_raw_match xl.p xl.v xh0) (cbor_raw_match_with_perm xl xh0) _;
  admit ()
}

#pop-options

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

inline_for_extraction
let ser_payload_tagged
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
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
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
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

(* --- Array payload --- *)

(* For arrays, we use a lens to extract the mixed_list, then l2r_write_mixed_list.
   However, since mixed_list_match carries a variable permission, we write
   ser_payload_array as a direct fn. *)

inline_for_extraction
let ser_payload_array
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= admit ()

inline_for_extraction
let size_payload_array
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= admit ()

(* --- Map payload --- *)

inline_for_extraction
let ser_payload_map
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= admit ()

inline_for_extraction
let size_payload_map
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= admit ()

(* --- Payload dispatch --- *)

inline_for_extraction
let ser_payload_not_string_not_array_not_map
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
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
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
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
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
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
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
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
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
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
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
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
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (ser_payload_string xh1)
    (ser_payload_not_string f64 f xh1)

inline_for_extraction
let size_payload
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (size_payload_string xh1)
    (size_payload_not_string f64 f xh1)

(* ================================================================ *)
(* Part 4: Composition and recursion                                *)
(* ================================================================ *)

inline_for_extraction
let ser_body
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item
= l2r_writer_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (l2r_write_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (l2r_write_dtuple2_recip_explicit_header
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
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item
= compute_remaining_size_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (compute_remaining_size_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (compute_remaining_size_dtuple2_recip_explicit_header
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
  (out: S.slice byte)
  (offset: SZ.t)
  (v: Ghost.erased bytes)
: Tot slprop
=
    (pts_to out v ** cbor_raw_match_with_perm x' x ** pure (
      SZ.v offset + Seq.length (bare_serialize serialize_raw_data_item x) <= Seq.length v
    ))

let ser_post
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: S.slice byte)
  (offset: SZ.t)
  (v: Ghost.erased bytes)
  (res: SZ.t)
: Tot slprop
=
  exists* v' .
      pts_to out v' ** cbor_raw_match_with_perm x' x ** pure (
      let bs = bare_serialize serialize_raw_data_item x in
      SZ.v res == SZ.v offset + Seq.length bs /\
      SZ.v res <= Seq.length v /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
      Seq.slice v' (SZ.v offset) (SZ.v res) `Seq.equal` bs
  )

inline_for_extraction
fn ser_fold
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice byte) -> (offset: SZ.t) -> (v: Ghost.erased bytes) -> stt SZ.t (ser_pre x' x out offset v) (fun res -> ser_post x' x out offset v res))
: l2r_writer #_ #raw_data_item (cbor_raw_match_with_perm) #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item
=
  (x': with_perm cbor_raw) (#x: raw_data_item) (out: S.slice byte) (offset: SZ.t) (#v: Ghost.erased bytes)
{
  fold (ser_pre x' x out offset v);
  let res = f x' x out offset v;
  unfold (ser_post x' x out offset v res);
  res
}

inline_for_extraction
fn ser_unfold
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice byte)
  (offset: SZ.t)
  (v: Ghost.erased bytes)
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
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice byte) -> (offset: SZ.t) -> (v: Ghost.erased bytes) -> stt SZ.t (ser_pre x' x out offset v) (fun res -> ser_post x' x out offset v res))
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice byte)
  (offset: SZ.t)
  (v: Ghost.erased bytes)
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
  (out: S.slice byte)
  (offset: SZ.t)
  (v: Ghost.erased bytes)
requires
  (ser_pre x' x out offset v)
returns res: SZ.t
ensures
  ser_post x' x out offset v res
{
  ser_body' f64 (ser' f64) x' x out offset v
}

let ser (f64: squash SZ.fits_u64) (p: perm) : l2r_writer (cbor_raw_match p) serialize_raw_data_item =
  l2r_writer_lens
    (cbor_raw_match_with_perm_lens p)
    (ser_fold (ser' f64))

fn cbor_serialize
  (x: cbor_raw)
  (output: S.slice U8.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
norewrite
requires
    (exists* v . cbor_raw_match pm x y ** pts_to output v ** pure (Seq.length (serialize_cbor y) <= SZ.v (S.len output)))
returns res: SZ.t
ensures exists* v . cbor_raw_match pm x y ** pts_to output v ** pure (
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

(* ================================================================ *)
(* Size computation                                                 *)
(* ================================================================ *)

let size_pre
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: ref SZ.t)
  (v: SZ.t)
: Tot slprop
=
    (pts_to out v ** cbor_raw_match_with_perm x' x)

let size_post
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: ref SZ.t)
  (v: SZ.t)
  (res: bool)
: Tot slprop
=
  exists* v' .
      pts_to out v' ** cbor_raw_match_with_perm x' x ** pure (
        let bs = Seq.length (bare_serialize serialize_raw_data_item x) in
        (res == true <==> bs <= SZ.v v) /\
        (res == true ==> bs + SZ.v v' == SZ.v v)
      )

inline_for_extraction
fn size_fold
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: ref SZ.t) -> (v: Ghost.erased SZ.t) -> stt bool (size_pre x' x out v) (fun res -> size_post x' x out v res))
: compute_remaining_size #_ #raw_data_item (cbor_raw_match_with_perm) #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item
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
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
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

let siz (f64: squash SZ.fits_u64) (p: perm) : compute_remaining_size (cbor_raw_match p) serialize_raw_data_item =
  compute_remaining_size_lens
    (cbor_raw_match_with_perm_lens p)
    (size_fold (siz' f64))

let cbor_size_post
  (bound: SZ.t)
  (y: raw_data_item)
  (res: SZ.t)
: Tot prop
= let s = Seq.length (serialize_cbor y) in
  (SZ.v res == 0 <==> s > SZ.v bound) /\
  (SZ.v res > 0 ==> SZ.v res == s)

fn cbor_size
  (x: cbor_raw)
  (bound: SZ.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
requires
    (cbor_raw_match pm x y)
returns res: SZ.t
ensures cbor_raw_match pm x y ** pure (
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

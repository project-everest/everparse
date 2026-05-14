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
open LowParse.Spec.VCList
open CBOR.Pulse.Raw.EverParse.Validate

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

(* Since cbor_raw_get_tagged_payload handles both CBOR_Case_Tagged and
   CBOR_Case_Tagged_Serialized, we use a single lens for all tagged cases
   that extracts the payload as cbor_raw_match_with_perm, then recurse. *)

(* Tagged payload lens: from match_cbor_payload to cbor_raw_match_with_perm *)

#push-options "--z3rlimit 64"

inline_for_extraction
fn ser_payload_tagged_lens
  (f64: squash SZ.fits_u64)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: vmatch_lens #_ #_ #_
  (vmatch_ext raw_data_item (match_cbor_payload xh1))
  cbor_raw_match_with_perm
= (xl: _) (z: _) {
  let xh2 = vmatch_ext_elim_trade raw_data_item (match_cbor_payload xh1) xl z;
  let xh0 = match_cbor_payload_elim_trade xh1 xl xh2;
  Trade.trans (cbor_raw_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_raw_match_with_perm xl xh0)
    (cbor_raw_match xl.p xl.v xh0);
  Trade.trans (cbor_raw_match xl.p xl.v xh0) (cbor_raw_match_with_perm xl xh0) _;
  let sq64 : squash SZ.fits_u64 = f64;
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

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

inline_for_extraction
let ser_payload_tagged
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_tagged_lens f64 xh1 sq)
      f
    )
    _

inline_for_extraction
let size_payload_tagged
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (compute_remaining_size_lens
      (ser_payload_tagged_lens f64 xh1 sq)
      f
    )
    _

#pop-options

(* --- Array payload --- *)

(* share/gather wrappers for cbor_raw_match, needed for l2r_write_mixed_list *)
ghost
fn cbor_raw_match_share_wrapper
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
requires cbor_raw_match p x1 x2
ensures cbor_raw_match (p /. 2.0R) x1 x2 ** cbor_raw_match (p /. 2.0R) x1 x2
{
  cbor_raw_match_share x1
}

ghost
fn cbor_raw_match_gather_wrapper
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
requires cbor_raw_match p x1 x2 ** cbor_raw_match p' x1 x2'
ensures cbor_raw_match (p +. p') x1 x2 ** pure (x2 == x2')
{
  cbor_raw_match_gather x1 #p #x2 #p' #x2'
}

let cbor_raw_match_share_t : I.share_t cbor_raw_match = cbor_raw_match_share_wrapper
let cbor_raw_match_gather_t : I.gather_t cbor_raw_match = cbor_raw_match_gather_wrapper

(* Array: bridge from match_cbor_payload to mixed_list_match_for_l2r,
   then use l2r_write_mixed_list. Written as a direct fn because
   the permission in mixed_list_match depends on the runtime value xl. *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn ser_payload_array_impl
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
  (xl: with_perm cbor_raw)
  (#xh: Ghost.erased (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
    (get_header_long_argument xh1)))) raw_data_item))
  (out: S.slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
requires
  pts_to out v **
  vmatch_ext
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) raw_data_item)
    (match_cbor_payload xh1) xl xh **
  pure (l2r_writer_for_pre
    (serialize_nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) serialize_raw_data_item) xh offset v)
returns res: SZ.t
ensures
  exists* v'.
  pts_to out v' **
  vmatch_ext
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) raw_data_item)
    (match_cbor_payload xh1) xl xh **
  pure (l2r_writer_for_post
    (serialize_nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) serialize_raw_data_item) xh offset v res v')
{
  // Step 1: Unfold vmatch_ext
  let xh2 = vmatch_ext_elim_trade
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
    (match_cbor_payload xh1) xl xh;
  // Now: match_cbor_payload xh1 xl xh2 ** trade (match_cbor_payload xh1 xl xh2) (vmatch_ext ...)
  // Step 2: Unfold match_cbor_payload to cbor_raw_match_with_perm
  let xh0 = match_cbor_payload_elim_trade xh1 xl xh2;
  // cbor_raw_match_with_perm xl xh0 ** trade ... (match_cbor_payload xh1 xl xh2)
  Trade.trans
    (cbor_raw_match_with_perm xl xh0)
    (match_cbor_payload xh1 xl xh2)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
      (match_cbor_payload xh1) xl xh);
  // Rewrite to cbor_raw_match xl.p xl.v xh0
  Trade.rewrite_with_trade
    (cbor_raw_match_with_perm xl xh0)
    (cbor_raw_match xl.p xl.v xh0);
  Trade.trans
    (cbor_raw_match xl.p xl.v xh0)
    (cbor_raw_match_with_perm xl xh0)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
      (match_cbor_payload xh1) xl xh);
  // Step 3: Call cbor_raw_get_array
  let arr = cbor_raw_get_array xl.p xl.v #xh0 () ;
  with pm' l . assert (
    I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l
  );
  Trade.trans
    (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l)
    (cbor_raw_match xl.p xl.v xh0)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
      (match_cbor_payload xh1) xl xh);
  // Rewrite mixed_list_match to mixed_list_match_for_l2r for l2r_write_mixed_list
  let n = SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1));
  rewrite (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l)
       as (LPIter.mixed_list_match_for_l2r cbor_raw_match parse_raw_data_item pm' (SZ.v n) arr l);
  // Build trade from mixed_list_match_for_l2r to vmatch_ext
  intro
    (Trade.trade
      (LPIter.mixed_list_match_for_l2r cbor_raw_match parse_raw_data_item pm' (SZ.v n) arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
        (match_cbor_payload xh1) xl xh))
  #(Trade.trade
      (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
        (match_cbor_payload xh1) xl xh))
  fn _ {
    rewrite (LPIter.mixed_list_match_for_l2r cbor_raw_match parse_raw_data_item pm' (SZ.v n) arr l)
         as (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l);
    Trade.elim
      (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
        (match_cbor_payload xh1) xl xh);
  };
  // Step 4: Write using l2r_write_mixed_list
  let w = LPIter.l2r_write_mixed_list
    cbor_raw_match
    serialize_raw_data_item
    (fun pm'' -> l2r_writer_lens (cbor_raw_match_with_perm_lens pm'') f)
    (jump_raw_data_item f64)
    cbor_raw_match_share_t cbor_raw_match_gather_t
    pm' n;
  let res = w arr out offset;
  // Step 5: Fold back
  Trade.elim
    (LPIter.mixed_list_match_for_l2r cbor_raw_match parse_raw_data_item pm' (SZ.v n) arr l)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
      (match_cbor_payload xh1) xl xh);
  res
}

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
let ser_payload_array
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (ser_payload_array_impl f64 f xh1 sq)
    (serialize_content xh1)

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn size_payload_array_impl
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
  (xl: with_perm cbor_raw)
  (#xh: Ghost.erased (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
    (get_header_long_argument xh1)))) raw_data_item))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
requires
  R.pts_to out v **
  vmatch_ext
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) raw_data_item)
    (match_cbor_payload xh1) xl xh
returns res: bool
ensures
  exists* v'.
  R.pts_to out v' **
  vmatch_ext
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) raw_data_item)
    (match_cbor_payload xh1) xl xh **
  pure (
    let bs = Seq.length (bare_serialize
      (serialize_nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))) serialize_raw_data_item) xh) in
    (res == true <==> bs <= SZ.v v) /\
    (res == true ==> bs + SZ.v v' == SZ.v v)
  )
{
  // Same pattern as ser_payload_array_impl
  let xh2 = vmatch_ext_elim_trade
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
    (match_cbor_payload xh1) xl xh;
  let xh0 = match_cbor_payload_elim_trade xh1 xl xh2;
  Trade.trans
    (cbor_raw_match_with_perm xl xh0)
    (match_cbor_payload xh1 xl xh2)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
      (match_cbor_payload xh1) xl xh);
  Trade.rewrite_with_trade
    (cbor_raw_match_with_perm xl xh0)
    (cbor_raw_match xl.p xl.v xh0);
  Trade.trans
    (cbor_raw_match xl.p xl.v xh0)
    (cbor_raw_match_with_perm xl xh0)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
      (match_cbor_payload xh1) xl xh);
  let arr = cbor_raw_get_array xl.p xl.v #xh0 () ;
  with pm' l . assert (
    I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l
  );
  Trade.trans
    (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l)
    (cbor_raw_match xl.p xl.v xh0)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
      (match_cbor_payload xh1) xl xh);
  let n = SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1));
  rewrite (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l)
       as (LPIter.mixed_list_match_for_l2r cbor_raw_match parse_raw_data_item pm' (SZ.v n) arr l);
  intro
    (Trade.trade
      (LPIter.mixed_list_match_for_l2r cbor_raw_match parse_raw_data_item pm' (SZ.v n) arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
        (match_cbor_payload xh1) xl xh))
  #(Trade.trade
      (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
        (match_cbor_payload xh1) xl xh))
  fn _ {
    rewrite (LPIter.mixed_list_match_for_l2r cbor_raw_match parse_raw_data_item pm' (SZ.v n) arr l)
         as (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l);
    Trade.elim
      (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
        (match_cbor_payload xh1) xl xh);
  };
  let cr = LPIter.compute_remaining_size_mixed_list
    cbor_raw_match
    serialize_raw_data_item
    (fun pm'' -> compute_remaining_size_lens (cbor_raw_match_with_perm_lens pm'') f)
    (jump_raw_data_item f64)
    cbor_raw_match_share_t cbor_raw_match_gather_t
    pm' n;
  let res = cr arr out;
  Trade.elim
    (LPIter.mixed_list_match_for_l2r cbor_raw_match parse_raw_data_item pm' (SZ.v n) arr l)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) raw_data_item)
      (match_cbor_payload xh1) xl xh);
  res
}

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
let size_payload_array
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (size_payload_array_impl f64 f xh1 sq)
    (serialize_content xh1)

#pop-options

(* --- Map payload --- *)

(* Map entry vmatch: cbor_map_entry_match cbor_raw_match *)
let cbor_map_entry_vmatch
  (pm: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item))
: Tot slprop
= cbor_map_entry_match cbor_raw_match pm elem v

(* Share/gather wrappers for cbor_map_entry_vmatch *)
ghost
fn cbor_map_entry_vmatch_share_wrapper
  (entry: cbor_map_entry cbor_raw) (#pm: perm) (#pair: (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm entry pair
ensures cbor_map_entry_vmatch (pm /. 2.0R) entry pair ** cbor_map_entry_vmatch (pm /. 2.0R) entry pair
{
  unfold (cbor_map_entry_vmatch pm entry pair);
  cbor_map_entry_match_share cbor_raw_match cbor_raw_match_share_wrapper entry;
  fold (cbor_map_entry_vmatch (pm /. 2.0R) entry pair);
  fold (cbor_map_entry_vmatch (pm /. 2.0R) entry pair);
}

ghost
fn cbor_map_entry_vmatch_gather_wrapper
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm) (#pair: (raw_data_item & raw_data_item))
  (#pm': perm) (#pair': (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm entry pair ** cbor_map_entry_vmatch pm' entry pair'
ensures cbor_map_entry_vmatch (pm +. pm') entry pair ** pure (pair == pair')
{
  unfold (cbor_map_entry_vmatch pm entry pair);
  unfold (cbor_map_entry_vmatch pm' entry pair');
  unfold (cbor_map_entry_match cbor_raw_match pm entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd pair));
  unfold (cbor_map_entry_match cbor_raw_match pm' entry pair');
  unfold (vmatch_pair_with_proj (cbor_raw_match pm') cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj) entry pair');
  unfold (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj entry (snd pair'));
  rewrite (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match pm entry.cbor_map_entry_key (fst pair));
  rewrite (cbor_raw_match pm' (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair'))
       as (cbor_raw_match pm' entry.cbor_map_entry_key (fst pair'));
  rewrite (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match pm entry.cbor_map_entry_value (snd pair));
  rewrite (cbor_raw_match pm' (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair'))
       as (cbor_raw_match pm' entry.cbor_map_entry_value (snd pair'));
  cbor_raw_match_gather entry.cbor_map_entry_key #pm #(fst pair) #pm' #(fst pair');
  cbor_raw_match_gather entry.cbor_map_entry_value #pm #(snd pair) #pm' #(snd pair');
  rewrite (cbor_raw_match (pm +. pm') entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match (pm +. pm') (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (cbor_raw_match (pm +. pm') entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match (pm +. pm') (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (cbor_raw_match (pm +. pm')) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (cbor_raw_match (pm +. pm')) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match (pm +. pm')) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match cbor_raw_match (pm +. pm') entry pair);
  fold (cbor_map_entry_vmatch (pm +. pm') entry pair);
}

let cbor_map_entry_vmatch_share_t : I.share_t cbor_map_entry_vmatch = cbor_map_entry_vmatch_share_wrapper
let cbor_map_entry_vmatch_gather_t : I.gather_t cbor_map_entry_vmatch = cbor_map_entry_vmatch_gather_wrapper

(* Map entry lens: extract key/value as with_perm cbor_raw from map entry *)
inline_for_extraction
fn cbor_map_entry_key_lens
  (pm': perm)
  (entry: cbor_map_entry cbor_raw)
  (pair: Ghost.erased (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm' entry pair
returns res: with_perm cbor_raw
ensures cbor_raw_match_with_perm res (fst pair) **
        Trade.trade (cbor_raw_match_with_perm res (fst pair)) (cbor_map_entry_vmatch pm' entry pair)
{
  unfold (cbor_map_entry_vmatch pm' entry pair);
  unfold (cbor_map_entry_match cbor_raw_match pm' entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match pm') cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj) entry pair);
  rewrite (cbor_raw_match pm' (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match pm' entry.cbor_map_entry_key (fst pair));
  let res : with_perm cbor_raw = { v = entry.cbor_map_entry_key; p = pm' };
  rewrite (cbor_raw_match pm' entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match_with_perm res (fst pair));
  intro
    (Trade.trade (cbor_raw_match_with_perm res (fst pair)) (cbor_map_entry_vmatch pm' entry pair))
  #(vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj entry (snd pair))
  fn _ {
    rewrite (cbor_raw_match_with_perm res (fst pair))
         as (cbor_raw_match pm' entry.cbor_map_entry_key (fst pair));
    rewrite (cbor_raw_match pm' entry.cbor_map_entry_key (fst pair))
         as (cbor_raw_match pm' (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
    fold (vmatch_pair_with_proj (cbor_raw_match pm') cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj) entry pair);
    fold (cbor_map_entry_match cbor_raw_match pm' entry pair);
    fold (cbor_map_entry_vmatch pm' entry pair);
  };
  res
}

inline_for_extraction
fn cbor_map_entry_value_lens
  (pm': perm)
  (entry: cbor_map_entry cbor_raw)
  (pair: Ghost.erased (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm' entry pair
returns res: with_perm cbor_raw
ensures cbor_raw_match_with_perm res (snd pair) **
        Trade.trade (cbor_raw_match_with_perm res (snd pair)) (cbor_map_entry_vmatch pm' entry pair)
{
  unfold (cbor_map_entry_vmatch pm' entry pair);
  unfold (cbor_map_entry_match cbor_raw_match pm' entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match pm') cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj entry (snd pair));
  rewrite (cbor_raw_match pm' (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match pm' entry.cbor_map_entry_value (snd pair));
  let res : with_perm cbor_raw = { v = entry.cbor_map_entry_value; p = pm' };
  rewrite (cbor_raw_match pm' entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match_with_perm res (snd pair));
  intro
    (Trade.trade (cbor_raw_match_with_perm res (snd pair)) (cbor_map_entry_vmatch pm' entry pair))
  #(cbor_raw_match pm' (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
  fn _ {
    rewrite (cbor_raw_match_with_perm res (snd pair))
         as (cbor_raw_match pm' entry.cbor_map_entry_value (snd pair));
    rewrite (cbor_raw_match pm' entry.cbor_map_entry_value (snd pair))
         as (cbor_raw_match pm' (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
    fold (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj entry (snd pair));
    fold (vmatch_pair_with_proj (cbor_raw_match pm') cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj) entry pair);
    fold (cbor_map_entry_match cbor_raw_match pm' entry pair);
    fold (cbor_map_entry_vmatch pm' entry pair);
  };
  res
}

(* Map entry writer: write key and value using l2r_write_nondep_then *)
inline_for_extraction
let ser_map_entry
  (f: l2r_writer cbor_raw_match_with_perm serialize_raw_data_item)
  (pm': perm)
: l2r_writer (cbor_map_entry_vmatch pm') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= l2r_write_nondep_then
    f () f
    (cbor_map_entry_vmatch pm')
    (cbor_map_entry_key_lens pm')
    (cbor_map_entry_value_lens pm')

inline_for_extraction
let size_map_entry
  (f: compute_remaining_size cbor_raw_match_with_perm serialize_raw_data_item)
  (pm': perm)
: compute_remaining_size (cbor_map_entry_vmatch pm') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= compute_remaining_size_nondep_then
    f () f
    (cbor_map_entry_vmatch pm')
    (cbor_map_entry_key_lens pm')
    (cbor_map_entry_value_lens pm')

(* Map payload impl: same pattern as array but with map entry vmatch *)
#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn ser_payload_map_impl
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
  (xl: with_perm cbor_raw)
  (#xh: Ghost.erased (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
    (get_header_long_argument xh1)))) (raw_data_item & raw_data_item)))
  (out: S.slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
requires
  pts_to out v **
  vmatch_ext
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
    (match_cbor_payload xh1) xl xh **
  pure (l2r_writer_for_pre
    (serialize_nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) xh offset v)
returns res: SZ.t
ensures
  exists* v'.
  pts_to out v' **
  vmatch_ext
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
    (match_cbor_payload xh1) xl xh **
  pure (l2r_writer_for_post
    (serialize_nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) xh offset v res v')
{
  let xh2 = vmatch_ext_elim_trade
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
    (match_cbor_payload xh1) xl xh;
  let xh0 = match_cbor_payload_elim_trade xh1 xl xh2;
  Trade.trans
    (cbor_raw_match_with_perm xl xh0)
    (match_cbor_payload xh1 xl xh2)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
      (match_cbor_payload xh1) xl xh);
  Trade.rewrite_with_trade
    (cbor_raw_match_with_perm xl xh0)
    (cbor_raw_match xl.p xl.v xh0);
  Trade.trans
    (cbor_raw_match xl.p xl.v xh0)
    (cbor_raw_match_with_perm xl xh0)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
      (match_cbor_payload xh1) xl xh);
  let arr = cbor_raw_get_map xl.p xl.v #xh0 () ;
  with pm' l . assert (
    I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l
  );
  // Rewrite eta-expanded lambda to cbor_map_entry_vmatch
  rewrite (I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l)
    as (I.mixed_list_match
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l);
  // Build a new trade from cbor_map_entry_vmatch form to cbor_raw_match
  // by intro'ing a trade that rewrites back to eta-expanded form and elims the old trade
  intro
    (Trade.trade
      (I.mixed_list_match
        cbor_map_entry_vmatch
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm' arr l)
      (cbor_raw_match xl.p xl.v xh0))
  #(Trade.trade
      (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match cbor_raw_match pm0 elem v)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm' arr l)
      (cbor_raw_match xl.p xl.v xh0))
  fn _ {
    rewrite (I.mixed_list_match
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l)
    as (I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l);
    Trade.elim
      (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match cbor_raw_match pm0 elem v)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm' arr l)
      (cbor_raw_match xl.p xl.v xh0);
  };
  Trade.trans
    (I.mixed_list_match
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l)
    (cbor_raw_match xl.p xl.v xh0)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
      (match_cbor_payload xh1) xl xh);
  let n = SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1));
  rewrite (I.mixed_list_match
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l)
    as (LPIter.mixed_list_match_for_l2r
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' (SZ.v n) arr l);
  intro
    (Trade.trade
      (LPIter.mixed_list_match_for_l2r cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' (SZ.v n) arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
        (match_cbor_payload xh1) xl xh))
  #(Trade.trade
      (I.mixed_list_match cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
        (match_cbor_payload xh1) xl xh))
  fn _ {
    rewrite (LPIter.mixed_list_match_for_l2r cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' (SZ.v n) arr l)
         as (I.mixed_list_match cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' arr l);
    Trade.elim
      (I.mixed_list_match cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
        (match_cbor_payload xh1) xl xh);
  };
  let w = LPIter.l2r_write_mixed_list
    cbor_map_entry_vmatch
    (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
    (fun pm'' -> ser_map_entry f pm'')
    (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64))
    cbor_map_entry_vmatch_share_t cbor_map_entry_vmatch_gather_t
    pm' n;
  let res = w arr out offset;
  Trade.elim
    (LPIter.mixed_list_match_for_l2r cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' (SZ.v n) arr l)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
      (match_cbor_payload xh1) xl xh);
  res
}

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
let ser_payload_map
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (ser_payload_map_impl f64 f xh1 sq)
    (serialize_content xh1)

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn size_payload_map_impl
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
  (xl: with_perm cbor_raw)
  (#xh: Ghost.erased (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
    (get_header_long_argument xh1)))) (raw_data_item & raw_data_item)))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
requires
  R.pts_to out v **
  vmatch_ext
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
    (match_cbor_payload xh1) xl xh
returns res: bool
ensures
  exists* v'.
  R.pts_to out v' **
  vmatch_ext
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
    (match_cbor_payload xh1) xl xh **
  pure (
    let bs = Seq.length (bare_serialize
      (serialize_nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1)))) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) xh) in
    (res == true <==> bs <= SZ.v v) /\
    (res == true ==> bs + SZ.v v' == SZ.v v)
  )
{
  let xh2 = vmatch_ext_elim_trade
    (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
    (match_cbor_payload xh1) xl xh;
  let xh0 = match_cbor_payload_elim_trade xh1 xl xh2;
  Trade.trans
    (cbor_raw_match_with_perm xl xh0)
    (match_cbor_payload xh1 xl xh2)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
      (match_cbor_payload xh1) xl xh);
  Trade.rewrite_with_trade
    (cbor_raw_match_with_perm xl xh0)
    (cbor_raw_match xl.p xl.v xh0);
  Trade.trans
    (cbor_raw_match xl.p xl.v xh0)
    (cbor_raw_match_with_perm xl xh0)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
      (match_cbor_payload xh1) xl xh);
  let arr = cbor_raw_get_map xl.p xl.v #xh0 () ;
  with pm' l . assert (
    I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l
  );
  rewrite (I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l)
    as (I.mixed_list_match
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l);
  intro
    (Trade.trade
      (I.mixed_list_match
        cbor_map_entry_vmatch
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm' arr l)
      (cbor_raw_match xl.p xl.v xh0))
  #(Trade.trade
      (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match cbor_raw_match pm0 elem v)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm' arr l)
      (cbor_raw_match xl.p xl.v xh0))
  fn _ {
    rewrite (I.mixed_list_match
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l)
    as (I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l);
    Trade.elim
      (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match cbor_raw_match pm0 elem v)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm' arr l)
      (cbor_raw_match xl.p xl.v xh0);
  };
  Trade.trans
    (I.mixed_list_match
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l)
    (cbor_raw_match xl.p xl.v xh0)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
      (match_cbor_payload xh1) xl xh);
  let n = SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1));
  rewrite (I.mixed_list_match
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' arr l)
    as (LPIter.mixed_list_match_for_l2r
      cbor_map_entry_vmatch
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' (SZ.v n) arr l);
  intro
    (Trade.trade
      (LPIter.mixed_list_match_for_l2r cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' (SZ.v n) arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
        (match_cbor_payload xh1) xl xh))
  #(Trade.trade
      (I.mixed_list_match cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
        (match_cbor_payload xh1) xl xh))
  fn _ {
    rewrite (LPIter.mixed_list_match_for_l2r cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' (SZ.v n) arr l)
         as (I.mixed_list_match cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' arr l);
    Trade.elim
      (I.mixed_list_match cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' arr l)
      (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
        (match_cbor_payload xh1) xl xh);
  };
  let cr = LPIter.compute_remaining_size_mixed_list
    cbor_map_entry_vmatch
    (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
    (fun pm'' -> size_map_entry f pm'')
    (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64))
    cbor_map_entry_vmatch_share_t cbor_map_entry_vmatch_gather_t
    pm' n;
  let res = cr arr out;
  Trade.elim
    (LPIter.mixed_list_match_for_l2r cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm' (SZ.v n) arr l)
    (vmatch_ext (nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
      (match_cbor_payload xh1) xl xh);
  res
}

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
let size_payload_map
  (f64: squash SZ.fits_u64)
  (f: compute_remaining_size (cbor_raw_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: compute_remaining_size (match_cbor_payload xh1) (serialize_content xh1)
= compute_remaining_size_ext_gen
    (size_payload_map_impl f64 f xh1 sq)
    (serialize_content xh1)

#pop-options

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
    (ser_payload_tagged f64 f xh1)
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
    (size_payload_tagged f64 f xh1)
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
  (f64: squash SZ.fits_u64)
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
  S.pts_to_len output;
  let res = ser f64 _ x output 0sz;
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

fn cbor_size
  (f64: squash SZ.fits_u64)
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
  let mut output = bound;
  let res = siz f64 pm x output;
  if (res) {
    let rem = !output;
    SZ.sub bound rem;
  } else {
    0sz
  }
}

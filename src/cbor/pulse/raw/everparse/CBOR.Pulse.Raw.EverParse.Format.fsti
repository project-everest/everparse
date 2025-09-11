module CBOR.Pulse.Raw.EverParse.Format
open CBOR.Spec.Raw.EverParse
open Pulse.Lib.Slice open Pulse.Lib.Pervasives open Pulse.Lib.Trade
open LowParse.Pulse.Combinators
open LowParse.Pulse.Recursive

module Trade = Pulse.Lib.Trade.Util
module U64 = FStar.UInt64
module L = LowParse.Spec.VCList
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice

val read_header (_: unit) : leaf_reader #header #parse_header_kind #parse_header serialize_header

val jump_header (_: unit) : jumper #header #parse_header_kind parse_header

inline_for_extraction
noextract [@@noextract_to "krml"]
val jump_leaf_content
  (sq: squash (SZ.fits_u64))
  (h: header)
: Tot (jumper (parse_leaf_content h))

inline_for_extraction
noextract [@@noextract_to "krml"]
val jump_leaf
  (sq: squash (SZ.fits_u64))
: Tot (jumper parse_leaf)

val jump_recursive_step_count_leaf (_: squash SZ.fits_u64) :
  jump_recursive_step_count #parse_raw_data_item_param serialize_raw_data_item_param

val validate_raw_data_item (_: squash SZ.fits_u64) : validator #raw_data_item #parse_raw_data_item_kind parse_raw_data_item

val jump_raw_data_item (_: squash SZ.fits_u64) : jumper #raw_data_item #parse_raw_data_item_kind parse_raw_data_item

inline_for_extraction
noextract [@@noextract_to "krml"]
val get_header_and_contents
  (input: S.slice byte)
  (outh: R.ref header)
  (#pm: perm)
  (#v: Ghost.erased raw_data_item)
: stt (S.slice byte)
  (requires exists* h . pts_to_serialized serialize_raw_data_item input #pm v ** pts_to outh h)
  (ensures fun outc -> exists* h c .
    pts_to outh h **
    pts_to_serialized (serialize_content h) outc #pm c **
    trade (pts_to_serialized (serialize_content h) outc #pm c) (pts_to_serialized serialize_raw_data_item input #pm v) **
    pure (synth_raw_data_item_recip v == (| h, c |))
  )

val get_string_payload
  (input: S.slice byte)
  (v: Ghost.erased raw_data_item)
  (#pm: perm)
  (#h: Ghost.erased header)
  (#c: Ghost.erased (content h)) 
: stt_ghost unit emp_inames
  (requires pts_to_serialized (serialize_content h) input #pm c ** pure (synth_raw_data_item_recip v == (| Ghost.reveal h, Ghost.reveal c |) /\ String? v))
  (ensures fun _ -> exists* (v' : Seq.seq byte) .
    pts_to input #pm v' **
    trade (pts_to input #pm v') (pts_to_serialized (serialize_content h) input #pm c) **
    pure (String? v /\ v' == String?.v v)
  )

val get_tagged_payload
  (input: S.slice byte)
  (v: Ghost.erased raw_data_item)
  (#pm: perm)
  (#h: Ghost.erased header)
  (#c: Ghost.erased (content h)) 
: stt_ghost unit emp_inames
  (requires pts_to_serialized (serialize_content h) input #pm c ** pure (synth_raw_data_item_recip v == (| Ghost.reveal h, Ghost.reveal c |) /\ Tagged? v))
  (ensures fun _ -> exists* v' .
    pts_to_serialized serialize_raw_data_item input #pm v' **
    trade (pts_to_serialized serialize_raw_data_item input #pm v') (pts_to_serialized (serialize_content h) input #pm c) **
    pure (Tagged? v /\ v' == Tagged?.v v)
  )

inline_for_extraction
let get_array_payload_t
  (input: S.slice byte)
=
  (v: Ghost.erased raw_data_item {Array? v }) ->
  (#pm: perm) ->
  (#h: Ghost.erased header) ->
  (#c: Ghost.erased (content h)) ->
  stt_ghost unit emp_inames
  (requires pts_to_serialized (serialize_content h) input #pm c ** pure (synth_raw_data_item_recip v == (| Ghost.reveal h, Ghost.reveal c |)))
  (ensures fun _ -> exists* v' .
    pts_to_serialized (L.serialize_nlist (U64.v (Array?.len v).value) serialize_raw_data_item) input #pm v' **
    trade (pts_to_serialized (L.serialize_nlist (U64.v (Array?.len v).value) serialize_raw_data_item) input #pm v') (pts_to_serialized (serialize_content h) input #pm c) **
    pure (v' == Array?.v v)
  )

val get_array_payload (input: S.slice byte) : get_array_payload_t input

inline_for_extraction
let get_map_payload_t
  (input: S.slice byte)
=
  (v: Ghost.erased raw_data_item {Map? v }) ->
  (#pm: perm) ->
  (#h: Ghost.erased header) ->
  (#c: Ghost.erased (content h)) ->
  stt_ghost unit emp_inames
  (requires pts_to_serialized (serialize_content h) input #pm c ** pure (synth_raw_data_item_recip v == (| Ghost.reveal h, Ghost.reveal c |)))
  (ensures fun _ -> exists* v' .
    pts_to_serialized (L.serialize_nlist (U64.v (Map?.len v).value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) input #pm v' **
    trade (pts_to_serialized (L.serialize_nlist (U64.v (Map?.len v).value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) input #pm v') (pts_to_serialized (serialize_content h) input #pm c) **
    pure (v' == Map?.v v)
  )

val get_map_payload (input: S.slice byte) : get_map_payload_t input

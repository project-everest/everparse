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

val impl_remaining_data_items_header
  (bound: Ghost.erased SZ.t)
  (h: header)
: Pure SZ.t
  (requires
    SZ.fits_u64 /\
    remaining_data_items_header h <= SZ.v bound
  )
  (ensures fun res ->
    SZ.v res == remaining_data_items_header h
  )

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

let pts_to_serialized_nlist_raw_data_item_head_header_t =
  (a: slice byte) ->
  (n: pos) ->
  (#pm: perm) ->
  (#va: LowParse.Spec.VCList.nlist n raw_data_item) ->
  stt_ghost unit emp_inames
(requires
  pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va
)
(ensures fun _ -> exists* (l: leaf) (h: header) v' .
  pts_to_serialized
    (LowParse.Spec.Combinators.serialize_nondep_then
      serialize_header
      (LowParse.Spec.Combinators.serialize_nondep_then
        (serialize_leaf_content h)
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n l)
      )
    )
    a #pm v' **
  Trade.trade
    (pts_to_serialized
      (LowParse.Spec.Combinators.serialize_nondep_then
        serialize_header
        (LowParse.Spec.Combinators.serialize_nondep_then
          (serialize_leaf_content h)
          (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n l)
        )
      )
      a #pm v'
    )
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va) **
  pure (
    h == get_raw_data_item_header (List.Tot.hd va) /\
    l == dfst (synth_raw_data_item_from_alt_recip (List.Tot.hd va)) /\
    fst v' == h /\
    dfst l == h /\
    fst (snd v') == dsnd l /\
    (fst (snd (snd v')) <: list raw_data_item) == (dsnd (synth_raw_data_item_from_alt_recip (List.Tot.hd va)) <: list raw_data_item) /\
    (snd (snd (snd v')) <: list raw_data_item) == List.Tot.tl va
  )
)

val pts_to_serialized_nlist_raw_data_item_head_header : pts_to_serialized_nlist_raw_data_item_head_header_t

let pts_to_serialized_nlist_raw_data_item_head_header'_post
  (n: pos)
  (va: LowParse.Spec.VCList.nlist n raw_data_item)
  (h: header) (v': (header & (leaf_content h & (nlist raw_data_item (remaining_data_items_header h) & nlist raw_data_item  (n - 1)))))
: Tot prop
=
    let l = dfst (synth_raw_data_item_from_alt_recip (List.Tot.hd va)) in
    h == get_raw_data_item_header (List.Tot.hd va) /\
    fst v' == h /\
    fst (snd v') == (dsnd l) /\
    (fst (snd (snd v')) <: list raw_data_item) == (dsnd (synth_raw_data_item_from_alt_recip (List.Tot.hd va)) <: list raw_data_item) /\
    (snd (snd (snd v')) <: list raw_data_item) == List.Tot.tl va

val pts_to_serialized_nlist_raw_data_item_head_header'
  (a: slice byte)
  (n: pos)
  (#pm: perm)
  (#va: LowParse.Spec.VCList.nlist n raw_data_item)
: stt_ghost (Ghost.erased header) emp_inames
(requires
  pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) a #pm va
)
(ensures fun h -> exists* v' .
  pts_to_serialized
    (LowParse.Spec.Combinators.serialize_nondep_then
      serialize_header
      (LowParse.Spec.Combinators.serialize_nondep_then
        (serialize_leaf_content h)
        (LowParse.Spec.Combinators.serialize_nondep_then
          (L.serialize_nlist (remaining_data_items_header h) serialize_raw_data_item)
          (L.serialize_nlist (n - 1) serialize_raw_data_item)
        )
      )
    )
    a #pm v' **
  Trade.trade
    (pts_to_serialized
      (LowParse.Spec.Combinators.serialize_nondep_then
        serialize_header
        (LowParse.Spec.Combinators.serialize_nondep_then
          (serialize_leaf_content h)
          (LowParse.Spec.Combinators.serialize_nondep_then
            (L.serialize_nlist (remaining_data_items_header h) serialize_raw_data_item)
            (L.serialize_nlist (n - 1) serialize_raw_data_item)
          )
        )
      )
      a #pm v'
    )
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) a #pm va) **
  pure (
    pts_to_serialized_nlist_raw_data_item_head_header'_post n va h v'
  )
)

inline_for_extraction
val impl_holds_on_raw_data_item
  (f64: squash SZ.fits_u64)
  (p: Ghost.erased (raw_data_item -> bool))
  (impl_p: LowParse.Pulse.Recursive.impl_pred_t serialize_raw_data_item_param p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased raw_data_item)
: stt bool
  (requires pts_to_serialized serialize_raw_data_item input #pm v)
  (ensures fun res -> pts_to_serialized serialize_raw_data_item input #pm v ** pure (res == holds_on_raw_data_item p v))

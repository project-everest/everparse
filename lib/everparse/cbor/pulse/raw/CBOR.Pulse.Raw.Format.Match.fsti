module CBOR.Pulse.Raw.Format.Match
include CBOR.Pulse.Raw.Type
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade

val cbor_match_serialized_payload_array
  (c: slice U8.t)
  (p: perm)
  (r: list raw_data_item)
: Tot slprop

val cbor_match_serialized_payload_map
  (c: slice U8.t)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
: Tot slprop

val cbor_match_serialized_payload_tagged
  (c: slice U8.t)
  (p: perm)
  (r: raw_data_item)
: Tot slprop

val cbor_match_serialized_payload_array_share
  (c: slice U8.t)
  (p: perm)
  (r: list raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_array c p r)
    (fun _ ->
      cbor_match_serialized_payload_array c (p /. 2.0R) r **
      cbor_match_serialized_payload_array c (p /. 2.0R) r
    )

val cbor_match_serialized_payload_array_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: list raw_data_item)
  (p2: perm)
  (r2: list raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_array c p1 r1 **
      cbor_match_serialized_payload_array c p2 r2
    )
    (fun _ ->
      cbor_match_serialized_payload_array c (p1 +. p2) r1 **
      pure (r1 == r2)
    )

val cbor_match_serialized_payload_map_share
  (c: slice U8.t)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_map c p r)
    (fun _ ->
      cbor_match_serialized_payload_map c (p /. 2.0R) r **
      cbor_match_serialized_payload_map c (p /. 2.0R) r
    )

val cbor_match_serialized_payload_map_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: list (raw_data_item & raw_data_item))
  (p2: perm)
  (r2: list (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_map c p1 r1 **
      cbor_match_serialized_payload_map c p2 r2
    )
    (fun _ ->
      cbor_match_serialized_payload_map c (p1 +. p2) r1 **
      pure (r1 == r2)
    )

val cbor_match_serialized_payload_tagged_share
  (c: slice U8.t)
  (p: perm)
  (r: raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_tagged c p r)
    (fun _ ->
      cbor_match_serialized_payload_tagged c (p /. 2.0R) r **
      cbor_match_serialized_payload_tagged c (p /. 2.0R) r
    )

val cbor_match_serialized_payload_tagged_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: raw_data_item)
  (p2: perm)
  (r2: raw_data_item)
: stt_ghost unit emp_inames
    (cbor_match_serialized_payload_tagged c p1 r1 **
      cbor_match_serialized_payload_tagged c p2 r2
    )
    (fun _ ->
      cbor_match_serialized_payload_tagged c (p1 +. p2) r1 **
      pure (r1 == r2)
    )

val cbor_match_serialized_payload_array_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list raw_data_item))
  (c': slice U8.t)
: stt unit
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_array c p r **
      pure (len c == len c')
    )
    (fun _ ->
      cbor_match_serialized_payload_array c p r **
      cbor_match_serialized_payload_array c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_array c' 1.0R r)
        (exists* v' . pts_to c' v')
    )

val cbor_match_serialized_payload_map_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list (raw_data_item & raw_data_item)))
  (c': slice U8.t)
: stt unit
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_map c p r **
      pure (len c == len c')
    )
    (fun _ ->
      cbor_match_serialized_payload_map c p r **
      cbor_match_serialized_payload_map c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_map c' 1.0R r)
        (exists* v' . pts_to c' v')
    )

val cbor_match_serialized_payload_tagged_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased raw_data_item)
  (c': slice U8.t)
: stt unit
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_tagged c p r **
      pure (len c == len c')
    )
    (fun _ ->
      cbor_match_serialized_payload_tagged c p r **
      cbor_match_serialized_payload_tagged c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_tagged c' 1.0R r)
        (exists* v' . pts_to c' v')
    )

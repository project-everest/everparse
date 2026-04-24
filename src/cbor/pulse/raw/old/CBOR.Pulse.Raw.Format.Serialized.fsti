module CBOR.Pulse.Raw.Format.Serialized
open CBOR.Pulse.Raw.Iterator.Base
include CBOR.Pulse.Raw.Match
open CBOR.Pulse.Raw.Iterator
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64

val cbor_match_serialized_tagged_get_payload
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Tagged? r })
: stt cbor_raw
  (cbor_match_serialized_tagged c pm r)
  (fun res ->
    cbor_match 1.0R res (Tagged?.v r) **
    trade
      (cbor_match 1.0R res (Tagged?.v r))
      (cbor_match_serialized_tagged c pm r)
  )

val cbor_serialized_array_item
  (c: cbor_serialized)
  (i: U64.t)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
: stt cbor_raw
    (cbor_match_serialized_array c pm r **
      pure (U64.v i < List.Tot.length (Array?.v r))
    )
    (fun res -> exists* y .
      cbor_match 1.0R res y **
      trade
        (cbor_match 1.0R res y)
        (cbor_match_serialized_array c pm r) **
      pure (
        U64.v i < List.Tot.length (Array?.v r) /\
        List.Tot.index (Array?.v r) (U64.v i) == y
      )
    )

val cbor_serialized_array_iterator_match
  (p: perm)
  (i: cbor_raw_serialized_iterator)
  (a: list raw_data_item)
: slprop

val cbor_serialized_array_iterator_init
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
: stt cbor_raw_serialized_iterator
    (cbor_match_serialized_array c pm r)
    (fun res -> exists* p .
      cbor_serialized_array_iterator_match p res (Array?.v r) **
      trade
        (cbor_serialized_array_iterator_match p res (Array?.v r))
        (cbor_match_serialized_array c pm r)
    )

val cbor_serialized_array_iterator_is_empty : cbor_raw_serialized_iterator_is_empty_t cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_length : cbor_raw_serialized_iterator_length_t cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_next (_: squash SZ.fits_u64) : cbor_raw_serialized_iterator_next_t cbor_match cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_truncate : cbor_raw_serialized_iterator_truncate_t cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_share : cbor_raw_serialized_iterator_share_t cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_gather : cbor_raw_serialized_iterator_gather_t cbor_serialized_array_iterator_match

val cbor_serialized_map_iterator_match
  (p: perm)
  (i: cbor_raw_serialized_iterator)
  (a: list (raw_data_item & raw_data_item))
: slprop

val cbor_serialized_map_iterator_init
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
: stt cbor_raw_serialized_iterator
    (cbor_match_serialized_map c pm r)
    (fun res -> exists* p .
      cbor_serialized_map_iterator_match p res (Map?.v r) **
      trade
        (cbor_serialized_map_iterator_match p res (Map?.v r))
        (cbor_match_serialized_map c pm r)
    )

val cbor_serialized_map_iterator_is_empty : cbor_raw_serialized_iterator_is_empty_t cbor_serialized_map_iterator_match

val cbor_serialized_map_iterator_next (_: squash SZ.fits_u64) : cbor_raw_serialized_iterator_next_t cbor_match_map_entry cbor_serialized_map_iterator_match

val cbor_serialized_map_iterator_share : cbor_raw_serialized_iterator_share_t cbor_serialized_map_iterator_match

val cbor_serialized_map_iterator_gather : cbor_raw_serialized_iterator_gather_t cbor_serialized_map_iterator_match

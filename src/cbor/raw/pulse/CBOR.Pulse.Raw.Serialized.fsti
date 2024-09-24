module CBOR.Pulse.Raw.Serialized
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

[@@CAbstractStruct]
val cbor_serialized_array_iterator: Type0

val cbor_serialized_array_iterator_match
  (p: perm)
  (i: cbor_serialized_array_iterator)
  (a: list raw_data_item)
: slprop

val cbor_serialized_array_iterator_init
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
: stt cbor_serialized_array_iterator
    (cbor_match_serialized_array c pm r)
    (fun res ->
      cbor_serialized_array_iterator_match 1.0R res (Array?.v r) **
      trade
        (cbor_serialized_array_iterator_match 1.0R res (Array?.v r))
        (cbor_match_serialized_array c pm r)
    )

val cbor_serialized_array_iterator_is_empty : cbor_raw_serialized_iterator_is_empty_t cbor_serialized_array_iterator_match

val cbor_serialized_array_iterator_next : cbor_raw_serialized_iterator_next_t cbor_match cbor_serialized_array_iterator_match

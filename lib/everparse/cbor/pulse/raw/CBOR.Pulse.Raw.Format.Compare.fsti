module CBOR.Pulse.Raw.Format.Compare
include CBOR.Spec.Raw.Format
include CBOR.Pulse.Raw.Compare.Base
include CBOR.Pulse.Raw.Match
open Pulse.Lib.Pervasives

module I16 = FStar.Int16

val cbor_match_compare_serialized_tagged
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Tagged? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Tagged? r2 })
: stt I16.t
  (cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (Tagged?.tag r1 == Tagged?.tag r2)
  )
  (fun res ->
    cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (
      same_sign (I16.v res) (cbor_compare r1 r2)
    )
  )

val cbor_match_compare_serialized_array
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Array? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Array? r2 })
: stt I16.t
  (cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (Array?.len r1 == Array?.len r2)
  )
  (fun res ->
    cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (
      same_sign (I16.v res) (cbor_compare r1 r2)
    )
  )

val cbor_match_compare_serialized_map
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Map? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Map? r2 })
: stt I16.t
  (cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (Map?.len r1 == Map?.len r2)
  )
  (fun res ->
    cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (
      same_sign (I16.v res) (cbor_compare r1 r2)
    )
  )

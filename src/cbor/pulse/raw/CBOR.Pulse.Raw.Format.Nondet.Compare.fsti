module CBOR.Pulse.Raw.Format.Nondet.Compare
include CBOR.Spec.Raw.Format
include CBOR.Spec.Raw.Valid
include CBOR.Pulse.Raw.Match
open Pulse.Lib.Pervasives

val cbor_match_equal_serialized_tagged
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Tagged? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Tagged? r2 })
: stt bool
  (cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (Tagged?.tag r1 == Tagged?.tag r2 /\
      valid_raw_data_item r1 /\
      valid_raw_data_item r2
    ) 
  )
  (fun res ->
    cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (
      res == raw_equiv r1 r2
    )
  )

val cbor_match_compare_serialized_array
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Array? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Array? r2 })
: stt bool
  (cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (
      valid_raw_data_item r1 /\
      valid_raw_data_item r2
    )
  )
  (fun res ->
    cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (
      res == raw_equiv r1 r2
    )
  )

val cbor_match_compare_serialized_map
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Map? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Map? r2 })
: stt bool
  (cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (
      valid_raw_data_item r1 /\
      valid_raw_data_item r2
    )
  )
  (fun res ->
    cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (
      res == raw_equiv r1 r2
    )
  )

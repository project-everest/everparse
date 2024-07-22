module CBOR.Pulse.Raw.Read
include CBOR.Pulse.Raw.Match
open CBOR.Pulse.Raw.Serialized
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Trade = Pulse.Lib.Trade.Util

(*
```pulse
ghost
fn cbor_match_tagged_elim
  (c: cbor_tagged)
  (pm: perm)
  (r: raw_data_item { Tagged? r })
  requires
    cbor_match_tagged c pm r
  ensures exists* pm' .
    cbor_match 1.0R 
    pts_to_serialized serialize_raw_data_item c.cbor_serialized_payload #pm' (Tagged?.v r) **
    trade
      (pts_to_serialized serialize_raw_data_item c.cbor_serialized_payload #pm' (Tagged?.v r))
      (cbor_match_serialized_tagged c pm r)
{
  unfold (cbor_match_serialized_tagged c pm r);
  unfold (cbor_match_serialized_payload_tagged c pm (Tagged?.v r));
  with pm' . assert (pts_to_serialized serialize_raw_data_item c.cbor_serialized_payload #pm' (Tagged?.v r));
  ghost fn aux (_: unit)
    requires emp ** (pts_to_serialized serialize_raw_data_item c.cbor_serialized_payload #pm' (Tagged?.v r))
    ensures (cbor_match_serialized_tagged c pm r)
  {
    fold (cbor_match_serialized_payload_tagged c pm (Tagged?.v r));
    fold (cbor_match_serialized_tagged c pm r);
  };
  intro_trade _ _ _ aux
}
```


```pulse
fn cbor_match_tagged_get_payload
  (c: cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Tagged? r })
  requires cbor_match pm c r
  returns res: cbor_raw
  ensures
    cbor_match 1.0R res (Tagged?.v r) **
    trade
      (cbor_match 1.0R res (Tagged?.v r))
      (cbor_match pm c r)
{
  cbor_match_cases c;
  if (CBOR_Case_Serialized_Tagged? c) {
    let cs = CBOR_Case_Serialized_Tagged?.v c;
    Trade.rewrite_with_trade
      (cbor_match pm c r)
      (cbor_match_serialized_tagged cs pm r);
    let res = cbor_match_serialized_tagged_get_payload cs;
    Trade.trans _ _ (cbor_match pm c r);
    res
  } else {
    admit ()
  }
}
```

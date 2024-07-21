module CBOR.Pulse.Raw.Serialized
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives

open LowParse.Pulse.Util
open CBOR.Spec.Raw.Format
open CBOR.Pulse.Raw.Format
open LowParse.Pulse.Combinators
open CBOR.Pulse.Raw.Serialized.Base
friend CBOR.Pulse.Raw.Match.Serialized

module Trade = Pulse.Lib.Trade.Util

```pulse
ghost
fn cbor_match_serialized_tagged_elim
  (c: cbor_serialized)
  (pm: perm)
  (r: raw_data_item { Tagged? r })
  requires
    cbor_match_serialized_tagged c pm r
  ensures exists* pm' .
    pts_to_serialized serialize_raw_data_item c.cbor_serialized_payload #pm' (Tagged?.v r) **
    trade
      (pts_to_serialized serialize_raw_data_item c.cbor_serialized_payload #pm' (Tagged?.v r))
      (cbor_match_serialized_tagged c pm r)
{
  unfold (cbor_match_serialized_tagged c pm r);
  unfold (cbor_match_serialized_payload_tagged c.cbor_serialized_payload (pm `perm_mul` c.cbor_serialized_perm) (Tagged?.v r));
  with pm' . assert (pts_to_serialized serialize_raw_data_item c.cbor_serialized_payload #pm' (Tagged?.v r));
  ghost fn aux (_: unit)
    requires emp ** (pts_to_serialized serialize_raw_data_item c.cbor_serialized_payload #pm' (Tagged?.v r))
    ensures (cbor_match_serialized_tagged c pm r)
  {
    fold (cbor_match_serialized_payload_tagged c.cbor_serialized_payload (pm `perm_mul` c.cbor_serialized_perm) (Tagged?.v r));
    fold (cbor_match_serialized_tagged c pm r);
  };
  intro_trade _ _ _ aux
}
```

```pulse
fn cbor_match_serialized_tagged_get_payload
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Tagged? r })
  requires cbor_match_serialized_tagged c pm r
  returns res: cbor_raw
  ensures
    cbor_match 1.0R res (Tagged?.v r) **
    trade
      (cbor_match 1.0R res (Tagged?.v r))
      (cbor_match_serialized_tagged c pm r)
{
  cbor_match_serialized_tagged_elim c pm r;
  let res = cbor_read c.cbor_serialized_payload;
  Trade.trans _ _ (cbor_match_serialized_tagged c pm r);
  res
}
```

module CBOR.Pulse.Raw.Format.Match
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.VCList
open LowParse.Pulse.Base

module U64 = FStar.UInt64

let cbor_match_serialized_payload_array
  c p r
= exists* n (r': nlist n raw_data_item) .
    pts_to_serialized (serialize_nlist n serialize_raw_data_item) c #p r' **
    pure (r == r')

let cbor_match_serialized_payload_map
  c p r
= exists* n (r' : nlist n (raw_data_item & raw_data_item)) .
    pts_to_serialized (serialize_nlist n (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item)) c #p r' **
    pure (r == r')

let cbor_match_serialized_payload_tagged
  c p r
= pts_to_serialized serialize_raw_data_item c #p r

#set-options "--print_implicits"

```pulse
fn cbor_match_serialized_payload_array_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list raw_data_item))
  (c': slice U8.t)
requires
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_array c p r **
      pure (len c == len c')
    )
ensures
    (
      cbor_match_serialized_payload_array c p r **
      cbor_match_serialized_payload_array c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_array c' 1.0R r)
        (exists* v' . pts_to c' v')
    )
{
  unfold (cbor_match_serialized_payload_array c p r);
  with n r' . assert (
    pts_to_serialized (serialize_nlist n serialize_raw_data_item) c #p r'
  );
  pts_to_serialized_copy #(nlist n raw_data_item) #(parse_nlist_kind n parse_raw_data_item_kind) #(coerce_eq () (parse_nlist n parse_raw_data_item)) (coerce_eq () (serialize_nlist n serialize_raw_data_item <: serializer (parse_nlist n parse_raw_data_item))) c c';
  fold (cbor_match_serialized_payload_array c p r);
  fold (cbor_match_serialized_payload_array c' 1.0R r);
  ghost fn aux (_: unit)
  requires emp ** cbor_match_serialized_payload_array c' 1.0R r
  ensures exists* v' . pts_to c' v'
  {
    unfold (cbor_match_serialized_payload_array c' 1.0R r);
    with n r' . assert (
      pts_to_serialized (serialize_nlist n serialize_raw_data_item) c' r'
    );
    unfold (pts_to_serialized (serialize_nlist n serialize_raw_data_item) c' r')
  };
  Trade.intro_trade _ _ _ aux
}
```

```pulse
fn cbor_match_serialized_payload_map_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list (raw_data_item & raw_data_item)))
  (c': slice U8.t)
requires
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_map c p r **
      pure (len c == len c')
    )
ensures
    (
      cbor_match_serialized_payload_map c p r **
      cbor_match_serialized_payload_map c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_map c' 1.0R r)
        (exists* v' . pts_to c' v')
    )
{
  unfold (cbor_match_serialized_payload_map c p r);
  with n r' . assert (
    pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p r'
  );
  pts_to_serialized_copy #(nlist n (raw_data_item & raw_data_item)) #(parse_nlist_kind n (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)) #(coerce_eq () (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item))) (coerce_eq () (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) <: serializer (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item)))) c c';
  fold (cbor_match_serialized_payload_map c p r);
  fold (cbor_match_serialized_payload_map c' 1.0R r);
  ghost fn aux (_: unit)
  requires emp ** cbor_match_serialized_payload_map c' 1.0R r
  ensures exists* v' . pts_to c' v'
  {
    unfold (cbor_match_serialized_payload_map c' 1.0R r);
    with n r' . assert (
      pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c' r'
    );
    unfold (pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c' r')
  };
  Trade.intro_trade _ _ _ aux
}
```

```pulse
fn cbor_match_serialized_payload_tagged_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (raw_data_item))
  (c': slice U8.t)
requires
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_tagged c p r **
      pure (len c == len c')
    )
ensures
    (
      cbor_match_serialized_payload_tagged c p r **
      cbor_match_serialized_payload_tagged c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_tagged c' 1.0R r)
        (exists* v' . pts_to c' v')
    )
{
  unfold (cbor_match_serialized_payload_tagged c p r);
  with r' . assert (
    pts_to_serialized (serialize_raw_data_item) c #p r'
  );
  pts_to_serialized_copy serialize_raw_data_item c c';
  fold (cbor_match_serialized_payload_tagged c p r);
  fold (cbor_match_serialized_payload_tagged c' 1.0R r);
  ghost fn aux (_: unit)
  requires emp ** cbor_match_serialized_payload_tagged c' 1.0R r
  ensures exists* v' . pts_to c' v'
  {
    unfold (cbor_match_serialized_payload_tagged c' 1.0R r);
    with r' . assert (
      pts_to_serialized (serialize_raw_data_item) c' r'
    );
    unfold (pts_to_serialized (serialize_raw_data_item) c' r')
  };
  Trade.intro_trade _ _ _ aux
}
```

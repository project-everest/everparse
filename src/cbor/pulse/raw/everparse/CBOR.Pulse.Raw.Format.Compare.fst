module CBOR.Pulse.Raw.Format.Compare
friend CBOR.Pulse.Raw.Format.Match
friend CBOR.Spec.Raw.Format
module Bytes = CBOR.Pulse.Raw.Compare.Bytes

```pulse
fn cbor_match_compare_serialized_tagged
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Tagged? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Tagged? r2 })
requires
  (cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (Tagged?.tag r1 == Tagged?.tag r2)
  )
returns res: I16.t
ensures
  (
    cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (
      same_sign (I16.v res) (cbor_compare r1 r2)
    )
  )
{
  unfold (cbor_match_serialized_tagged c1 pm1 r1);
  unfold (cbor_match_serialized_tagged c2 pm2 r2);
  unfold (cbor_match_serialized_payload_tagged c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Tagged?.v r1));
  unfold (cbor_match_serialized_payload_tagged c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Tagged?.v r2));
  assert (pure (cbor_compare r1 r2 == cbor_compare (Tagged?.v r1) (Tagged?.v r2)));
  cbor_compare_correct (Tagged?.v r1) (Tagged?.v r2);
  // hmm... pts_to_serialized is automatically unfolded here
  let res = Bytes.lex_compare_bytes c1.cbor_serialized_payload c2.cbor_serialized_payload;
  fold (cbor_match_serialized_payload_tagged c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Tagged?.v r2));
  fold (cbor_match_serialized_payload_tagged c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Tagged?.v r1));
  fold (cbor_match_serialized_tagged c1 pm1 r1);
  fold (cbor_match_serialized_tagged c2 pm2 r2);
  res
}
```

module F = CBOR.Spec.Raw.EverParse

```pulse
fn cbor_match_compare_serialized_array
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Array? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Array? r2 })
requires
  (cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (Array?.len r1 == Array?.len r2)
  )
returns res: I16.t
ensures
  (
    cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (
      same_sign (I16.v res) (cbor_compare r1 r2)
    )
  )
{
  unfold (cbor_match_serialized_array c1 pm1 r1);
  unfold (cbor_match_serialized_array c2 pm2 r2);
  unfold (cbor_match_serialized_payload_array c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Array?.v r1));
  unfold (cbor_match_serialized_payload_array c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Array?.v r2));
  cbor_compare_correct r1 r2;
  F.serialized_lex_compare_array_aux (Array?.len r1) (Array?.v r1) (Array?.len r2) (Array?.v r2);
  // hmm... pts_to_serialized is automatically unfolded here
  let res = Bytes.lex_compare_bytes c1.cbor_serialized_payload c2.cbor_serialized_payload;
  fold (cbor_match_serialized_payload_array c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Array?.v r2));
  fold (cbor_match_serialized_payload_array c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Array?.v r1));
  fold (cbor_match_serialized_array c1 pm1 r1);
  fold (cbor_match_serialized_array c2 pm2 r2);
  res
}
```

```pulse
fn cbor_match_compare_serialized_map
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Map? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Map? r2 })
requires
  (cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (Map?.len r1 == Map?.len r2)
  )
returns res: I16.t
ensures
  (
    cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (
      same_sign (I16.v res) (cbor_compare r1 r2)
    )
  )
{
  unfold (cbor_match_serialized_map c1 pm1 r1);
  unfold (cbor_match_serialized_map c2 pm2 r2);
  unfold (cbor_match_serialized_payload_map c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Map?.v r1));
  unfold (cbor_match_serialized_payload_map c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Map?.v r2));
  cbor_compare_correct r1 r2;
  F.serialized_lex_compare_map_aux (Map?.len r1) (Map?.v r1) (Map?.len r2) (Map?.v r2);
  // hmm... pts_to_serialized is automatically unfolded here
  let res = Bytes.lex_compare_bytes c1.cbor_serialized_payload c2.cbor_serialized_payload;
  fold (cbor_match_serialized_payload_map c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Map?.v r2));
  fold (cbor_match_serialized_payload_map c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Map?.v r1));
  fold (cbor_match_serialized_map c1 pm1 r1);
  fold (cbor_match_serialized_map c2 pm2 r2);
  res
}
```

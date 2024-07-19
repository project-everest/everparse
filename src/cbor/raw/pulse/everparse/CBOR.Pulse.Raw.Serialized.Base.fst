module CBOR.Pulse.Raw.Serialized.Base
friend CBOR.Pulse.Raw.Match.Serialized

let dummy_initial_byte : initial_byte = { major_type = cbor_major_type_simple_value; additional_info = 0uy }

let dummy_long_argument : long_argument dummy_initial_byte = LongArgumentOther dummy_initial_byte.additional_info () ()

let dummy_header : header = (| dummy_initial_byte, dummy_long_argument |)

```pulse
ghost
fn cbor_match_int_intro
  (input: S.slice byte)
  (pm: perm)
  (v: raw_data_item)
  (res: cbor_raw)
  requires
    pts_to_serialized serialize_raw_data_item input #pm v ** pure (CBOR_Case_Int? res)
  ensures
    trade (cbor_match 1.0R res v) (pts_to_serialized serialize_raw_data_item input #pm v)  
{ 
  ghost
  fn aux (_: unit)
     requires (pts_to_serialized serialize_raw_data_item input #pm v) ** cbor_match 1.0R res v
     ensures pts_to_serialized serialize_raw_data_item input #pm v
  {
    unfold (cbor_match 1.0R (CBOR_Case_Int (CBOR_Case_Int?.v res)) v);
    unfold (cbor_match_int (CBOR_Case_Int?.v res) v)
  };
  intro_trade _ _ _ aux
}
```

```pulse
fn cbor_match_string_intro
  (input: S.slice byte)
  (#pm: perm)
  (#v: Seq.seq byte)
  (c: cbor_string)
  (r: raw_data_item)
  requires
    S.pts_to input #pm v ** pure (
      input == c.cbor_string_ptr /\
      pm == c.cbor_string_perm /\
      Seq.length v == SZ.v (S.len c.cbor_string_ptr) /\
      r == String c.cbor_string_type ({ size = c.cbor_string_size; value = U64.uint_to_t (SZ.v (S.len c.cbor_string_ptr)) }) v
    )
  ensures
    cbor_match_string c 1.0R r **
    trade (cbor_match_string c 1.0R r) (S.pts_to input #pm v)
{
  fold (cbor_match_string c 1.0R r);
  ghost fn aux (_: unit)
    requires emp ** cbor_match_string c 1.0R r
    ensures S.pts_to input #pm v
  {
    unfold (cbor_match_string c 1.0R r)
  };
  intro_trade _ _ _ aux
}
```

```pulse
fn cbor_read
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased raw_data_item)
  requires
    pts_to_serialized serialize_raw_data_item input #pm v
  returns res: cbor_raw
  ensures
      cbor_match 1.0R res v **
      trade (cbor_match 1.0R res v) (pts_to_serialized serialize_raw_data_item input #pm v)
{
  let mut ph = dummy_header;
  let pc = get_header_and_contents input ph;
  let h = !ph;
  let typ = ((get_header_initial_byte h).major_type);
  if (typ = cbor_major_type_uint64) {
    elim_trade _ _;
    let i = get_int64_value v h;
    let resi = { cbor_int_type = typ; cbor_int_size = i.size; cbor_int_value = i.value };
    fold (cbor_match_int resi v);
    let res = CBOR_Case_Int resi;
    fold (cbor_match 1.0R res v);
    cbor_match_int_intro input pm v res;
    res
  }
(*
  else if (typ = cbor_major_type_text_string || typ = cbor_major_type_byte_string) {
    let i = get_string_length v h;
    get_string_payload pc v;
    trade_trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    S.pts_to_len pc;
    with v' . assert (S.pts_to pc #pm v');
    let res = CBOR_Case_String { cbor_string_type = typ; cbor_string_size = i.size; cbor_string_ptr = pc; cbor_string_perm = pm };
    rewrite_with_trade
      (S.pts_to pc #pm v')
      (cbor_match 1.0R res v);
    trade_trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
  }
*)
  else {
    admit ()
  }
}
```

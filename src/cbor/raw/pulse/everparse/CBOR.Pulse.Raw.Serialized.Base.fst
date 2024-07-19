module CBOR.Pulse.Raw.Serialized.Base
friend CBOR.Pulse.Raw.Match.Serialized

module Trade = Pulse.Lib.Trade.Util

let dummy_initial_byte : initial_byte = { major_type = cbor_major_type_simple_value; additional_info = 0uy }

let dummy_long_argument : long_argument dummy_initial_byte = LongArgumentOther dummy_initial_byte.additional_info () ()

let dummy_header : header = (| dummy_initial_byte, dummy_long_argument |)

```pulse
ghost
fn cbor_match_serialized_tagged_intro_aux
  (tag: raw_uint64)
  (pc: S.slice byte)
  (#v: raw_data_item)
  (#pm: perm)
  (res: cbor_serialized)
  (r: raw_data_item { Tagged? r })
  requires
    pts_to_serialized serialize_raw_data_item pc #pm v ** pure (
      res.cbor_serialized_header == tag /\
      res.cbor_serialized_payload == pc /\
      res.cbor_serialized_perm == pm /\
      r == Tagged tag v
    )
  ensures
    cbor_match_serialized_tagged res 1.0R r **
    trade
      (cbor_match_serialized_tagged res 1.0R r)
      (pts_to_serialized serialize_raw_data_item pc #pm v)
{
  fold (cbor_match_serialized_payload_tagged res 1.0R v);
  fold (cbor_match_serialized_tagged res 1.0R r);
  ghost fn aux (_: unit)
    requires emp ** cbor_match_serialized_tagged res 1.0R r
    ensures pts_to_serialized serialize_raw_data_item pc #pm v
  {
    unfold (cbor_match_serialized_tagged res 1.0R r);
    unfold (cbor_match_serialized_payload_tagged res 1.0R v)
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
  if (typ = cbor_major_type_uint64 || typ = cbor_major_type_neg_int64) {
    elim_trade _ _;
    let i = get_int64_value v h;
    cbor_match_int_intro_trade (pts_to_serialized serialize_raw_data_item input #pm v) typ i
  }
  else if (typ = cbor_major_type_text_string || typ = cbor_major_type_byte_string) {
    let i = get_string_length v h;
    get_string_payload pc v;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let res = cbor_match_string_intro typ i pc;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    res
  }
  else if (typ = cbor_major_type_tagged) {
    let tag = get_tagged_tag v h;
    get_tagged_payload pc v;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let rest = {
      cbor_serialized_header = tag;
      cbor_serialized_payload = pc;
      cbor_serialized_perm = pm;
    };
    cbor_match_serialized_tagged_intro_aux tag pc rest v;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let res = CBOR_Case_Serialized_Tagged rest;
    Trade.rewrite_with_trade
      (cbor_match_serialized_tagged rest 1.0R v)
      (cbor_match 1.0R res v);
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    res
  }
  else if (typ = cbor_major_type_array) {
    admit ()
  }
  else if (typ = cbor_major_type_map) {
    admit ()
  }
  else {
    assert (pure (typ == cbor_major_type_simple_value));
    elim_trade _ _;
    let i = get_simple_value v h;
    cbor_match_simple_intro_trade (pts_to_serialized serialize_raw_data_item input #pm v) i
  }
}
```

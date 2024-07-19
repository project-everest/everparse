module CBOR.Pulse.Raw.Serialized.Base
friend CBOR.Pulse.Raw.Match.Serialized

module Trade = Pulse.Lib.Trade.Util

let dummy_initial_byte : initial_byte = { major_type = cbor_major_type_simple_value; additional_info = 0uy }

let dummy_long_argument : long_argument dummy_initial_byte = LongArgumentOther dummy_initial_byte.additional_info () ()

let dummy_header : header = (| dummy_initial_byte, dummy_long_argument |)

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
    cbor_match_trade_int_intro (pts_to_serialized serialize_raw_data_item input #pm v) v res;
    res
  }
  else if (typ = cbor_major_type_text_string || typ = cbor_major_type_byte_string) {
    let i = get_string_length v h;
    get_string_payload pc v;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let res = cbor_match_string_intro typ i pc;
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    res
  }
  else {
    admit ()
  }
}
```

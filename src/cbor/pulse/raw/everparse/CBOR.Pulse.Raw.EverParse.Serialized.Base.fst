module CBOR.Pulse.Raw.EverParse.Serialized.Base
#lang-pulse
friend CBOR.Pulse.Raw.Format.Match

open CBOR.Pulse.Raw.EverParse.Format
open LowParse.Pulse.Combinators

module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
let dummy_initial_byte : initial_byte = { major_type = cbor_major_type_simple_value; additional_info = 0uy }

inline_for_extraction
let dummy_long_argument : long_argument dummy_initial_byte = LongArgumentOther () ()

inline_for_extraction
let dummy_header : header = (| dummy_initial_byte, dummy_long_argument |)

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
  fold (cbor_match_serialized_payload_tagged pc (1.0R `perm_mul` res.cbor_serialized_perm) v);
  fold (cbor_match_serialized_tagged res 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_tagged res 1.0R r)
      (pts_to_serialized serialize_raw_data_item pc #pm v)
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_tagged res 1.0R r);
    unfold (cbor_match_serialized_payload_tagged pc pm v)
  };
}

ghost
fn cbor_match_serialized_array_intro_aux
  (len: raw_uint64)
  (pc: S.slice byte)
  (#n: nat)
  (#v: LowParse.Spec.VCList.nlist n raw_data_item)
  (#pm: perm)
  (res: cbor_serialized)
  (r: raw_data_item)
  (sq: squash (Array? r))
  requires
    pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) pc #pm v ** pure (
      res.cbor_serialized_header == len /\
      res.cbor_serialized_payload == pc /\
      res.cbor_serialized_perm == pm /\
      n == U64.v len.value /\
      r == Array len v
    )
  ensures
    cbor_match_serialized_array res 1.0R r **
    trade
      (cbor_match_serialized_array res 1.0R r)
      (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) pc #pm v)
{
  fold (cbor_match_serialized_payload_array pc (1.0R `perm_mul` pm) v);
  fold (cbor_match_serialized_array res 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_array res 1.0R r)
      (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) pc #pm v)
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_array res 1.0R r);
    unfold (cbor_match_serialized_payload_array pc pm (Array?.v r))
  };
}

ghost
fn cbor_match_serialized_map_intro_aux
  (len: raw_uint64)
  (pc: S.slice byte)
  (#n: nat)
  (#v: LowParse.Spec.VCList.nlist n (raw_data_item & raw_data_item))
  (#pm: perm)
  (res: cbor_serialized)
  (r: raw_data_item)
  (sq: squash (Map? r))
  requires
    pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) pc #pm v ** pure (
      res.cbor_serialized_header == len /\
      res.cbor_serialized_payload == pc /\
      res.cbor_serialized_perm == pm /\
      n == U64.v len.value /\
      r == Map len v
    )
  ensures
    cbor_match_serialized_map res 1.0R r **
    trade
      (cbor_match_serialized_map res 1.0R r)
      (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) pc #pm v)
{
  fold (cbor_match_serialized_payload_map pc (1.0R `perm_mul` pm) v);
  fold (cbor_match_serialized_map res 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_map res 1.0R r)
      (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) pc #pm v)
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_map res 1.0R r);
    unfold (cbor_match_serialized_payload_map pc pm (Map?.v r))
  };
}

#push-options "--z3rlimit 20"
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
    let len = get_array_length v h;
    get_array_payload pc v;
    with n (v': LowParse.Spec.VCList.nlist n raw_data_item) . assert (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) pc #pm v');
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let resa = {
      cbor_serialized_header = len;
      cbor_serialized_payload = pc;
      cbor_serialized_perm = pm;
    };
    cbor_match_serialized_array_intro_aux len pc #n #v' #pm resa (Ghost.reveal v) ();
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let res = CBOR_Case_Serialized_Array resa;
    Trade.rewrite_with_trade
      (cbor_match_serialized_array resa 1.0R v)
      (cbor_match 1.0R res v);
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    res
  }
  else if (typ = cbor_major_type_map) {
    let len = get_map_length v h;
    get_map_payload pc v;
    with n (v': LowParse.Spec.VCList.nlist n (raw_data_item & raw_data_item)) . assert (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) pc #pm v');
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let resa = {
      cbor_serialized_header = len;
      cbor_serialized_payload = pc;
      cbor_serialized_perm = pm;
    };
    cbor_match_serialized_map_intro_aux len pc #n #v' #pm resa (Ghost.reveal v) ();
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    let res = CBOR_Case_Serialized_Map resa;
    Trade.rewrite_with_trade
      (cbor_match_serialized_map resa 1.0R v)
      (cbor_match 1.0R res v);
    Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
    res
  }
  else {
    assert (pure (typ == cbor_major_type_simple_value));
    elim_trade _ _;
    let i = get_simple_value v h;
    cbor_match_simple_intro_trade (pts_to_serialized serialize_raw_data_item input #pm v) i
  }
}
#pop-options

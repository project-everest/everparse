module CBOR.Pulse.Raw.Match
include CBOR.Pulse.Raw.Match.Serialized
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Trade = Pulse.Lib.Trade.Util

let cbor_match_int
  (c: cbor_int)
  (r: raw_data_item)
: Tot slprop
= pure (
    r == Int64 c.cbor_int_type ({ size = c.cbor_int_size; value = c.cbor_int_value })
  )

let cbor_match_simple
  (c: simple_value)
  (r: raw_data_item)
: Tot slprop
= pure (
    r == Simple c
  )

let cbor_match_string
  (c: cbor_string)
  (p: perm)
  (r: raw_data_item)
: Tot slprop
= exists* v . S.pts_to c.cbor_string_ptr #(p `perm_mul` c.cbor_string_perm) v ** pure
    (r == String c.cbor_string_type ({ size = c.cbor_string_size; value = U64.uint_to_t (SZ.v (S.len c.cbor_string_ptr)) }) v)

let cbor_match_tagged
  (c: cbor_tagged)
  (p: perm)
  (r: raw_data_item { Tagged? r })
  (cbor_match: (cbor_raw -> (v': raw_data_item { v' << r }) -> slprop))
: Tot slprop
= exists* c' . R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_perm) c' **
    cbor_match c' (Tagged?.v r) **
    pure (c.cbor_tagged_tag == Tagged?.tag r)

let cbor_match_array
  (c: cbor_array)
  (p: perm)
  (r: raw_data_item {Array? r})
  (cbor_match: (cbor_raw -> (v': raw_data_item { v' << r }) -> slprop))
: Tot slprop
= exists* v .
    A.pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_perm) v **
    PM.seq_list_match v (Array?.v r) cbor_match **
    pure (c.cbor_array_length == Array?.len r)

let cbor_match_map_entry
  (r0: raw_data_item)
  (cbor_match: (cbor_raw -> (v': raw_data_item { v' << r0 }) -> slprop))
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item) { r << r0 })
: Tot slprop
= cbor_match c.cbor_map_entry_key (fst r) **
  cbor_match c.cbor_map_entry_value (snd r)

let cbor_match_map
  (c: cbor_map)
  (p: perm)
  (r: raw_data_item {Map? r})
  (cbor_match: (cbor_raw -> (v': raw_data_item { v' << r }) -> slprop))
: Tot slprop
= exists* v .
    A.pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_perm) v **
    PM.seq_list_match v (Map?.v r) (cbor_match_map_entry r cbor_match) **
    pure (c.cbor_map_length == Map?.len r)

let cbor_match_serialized_array
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item { Array? r })
: Tot slprop
= cbor_match_serialized_payload_array c p (Array?.v r) **
  pure (c.cbor_serialized_header == Array?.len r)

let cbor_match_serialized_map
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item { Map? r })
: Tot slprop
= cbor_match_serialized_payload_map c p (Map?.v r) **
  pure (c.cbor_serialized_header == Map?.len r)

let cbor_match_serialized_tagged
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item { Tagged? r })
: Tot slprop
= cbor_match_serialized_payload_tagged c p (Tagged?.v r) **
  pure (c.cbor_serialized_header == Tagged?.tag r)

let rec cbor_match
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
: Tot slprop
  (decreases r)
= match c, r with
  | CBOR_Case_Array v, Array _ _ -> cbor_match_array v p r (cbor_match p)
  | CBOR_Case_Map v, Map _ _ -> cbor_match_map v p r (cbor_match p)
  | CBOR_Case_Simple v, _ -> cbor_match_simple v r
  | CBOR_Case_Int v, _ -> cbor_match_int v r
  | CBOR_Case_String v, _ -> cbor_match_string v p r
  | CBOR_Case_Tagged v, Tagged _ _ -> cbor_match_tagged v p r (cbor_match p)
  | CBOR_Case_Serialized_Array v, Array _ _ -> cbor_match_serialized_array v p r
  | CBOR_Case_Serialized_Map v, Map _ _ -> cbor_match_serialized_map v p r
  | CBOR_Case_Serialized_Tagged v, Tagged _ _ -> cbor_match_serialized_tagged v p r
  | _ -> pure False

```pulse
ghost
fn cbor_match_int_intro_trade_aux
  (q: slprop)
  (res: cbor_int)
  (v: raw_data_item)
  requires
    q
  ensures
    trade (cbor_match_int res v) q
{ 
  ghost
  fn aux (_: unit)
     requires q ** cbor_match_int res v
     ensures q
  {
    unfold (cbor_match_int res v)
  };
  intro_trade _ _ _ aux
}
```

inline_for_extraction
```pulse
fn cbor_match_int_intro_aux
  (typ: major_type_uint64_or_neg_int64)
  (i: raw_uint64)
  requires emp
  returns res: cbor_int
  ensures cbor_match_int res (Int64 typ i)
{
  let res = { cbor_int_type = typ; cbor_int_size = i.size; cbor_int_value = i.value };
  fold (cbor_match_int res (Int64 typ i));
  res
}
```

inline_for_extraction
```pulse
fn cbor_match_int_intro
  (typ: major_type_uint64_or_neg_int64)
  (i: raw_uint64)
  requires emp
  returns res: cbor_raw
  ensures cbor_match 1.0R res (Int64 typ i)
{
  let resi = cbor_match_int_intro_aux typ i;
  let res = CBOR_Case_Int resi;
  fold (cbor_match 1.0R res (Int64 typ i));
  res
}
```

inline_for_extraction
```pulse
fn cbor_match_int_intro_trade
  (q: slprop)
  (typ: major_type_uint64_or_neg_int64)
  (i: raw_uint64)
  requires q
  returns res: cbor_raw
  ensures cbor_match 1.0R res (Int64 typ i) ** trade (cbor_match 1.0R res (Int64 typ i)) q
{
  let resi = cbor_match_int_intro_aux typ i;
  cbor_match_int_intro_trade_aux q resi (Int64 typ i);
  let res = CBOR_Case_Int resi;
  Trade.rewrite_with_trade (cbor_match_int resi (Int64 typ i)) (cbor_match 1.0R res (Int64 typ i));
  Trade.trans _ _ q;
  res
}
```

```pulse
ghost
fn cbor_match_simple_intro_trade_aux
  (q: slprop)
  (res: simple_value)
  (v: raw_data_item)
  requires
    q
  ensures
    trade (cbor_match_simple res v) q
{ 
  ghost
  fn aux (_: unit)
     requires q ** cbor_match_simple res v
     ensures q
  {
    unfold (cbor_match_simple res v)
  };
  intro_trade _ _ _ aux
}
```

inline_for_extraction
```pulse
fn cbor_match_simple_intro
  (i: simple_value)
  requires emp
  returns res: cbor_raw
  ensures cbor_match 1.0R res (Simple i)
{
  fold (cbor_match_simple i (Simple i));
  let res = CBOR_Case_Simple i;
  fold (cbor_match 1.0R res (Simple i));
  res
}
```

inline_for_extraction
```pulse
fn cbor_match_simple_intro_trade
  (q: slprop)
  (i: simple_value)
  requires q
  returns res: cbor_raw
  ensures cbor_match 1.0R res (Simple i) ** trade (cbor_match 1.0R res (Simple i)) q
{
  cbor_match_simple_intro_trade_aux q i (Simple i);
  fold (cbor_match_simple i (Simple i));
  let res = CBOR_Case_Simple i;
  Trade.rewrite_with_trade (cbor_match_simple i (Simple i)) (cbor_match 1.0R res (Simple i));
  Trade.trans _ _ q;
  res
}
```

```pulse
ghost
fn cbor_match_string_intro_aux
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Seq.seq U8.t)
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

inline_for_extraction
```pulse
fn cbor_match_string_intro
  (typ: major_type_byte_string_or_text_string)
  (len: raw_uint64)
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  requires
    S.pts_to input #pm v ** pure (
      Seq.length v == U64.v len.value
    )
  returns c: cbor_raw
  ensures exists* r .
    cbor_match 1.0R c r **
    trade (cbor_match 1.0R c r) (S.pts_to input #pm v) **
    pure (
      Seq.length v == U64.v len.value /\
      r == String typ len (Ghost.reveal v)
    )
{
  S.pts_to_len input;
  let ress = { cbor_string_type = typ; cbor_string_size = len.size; cbor_string_ptr = input; cbor_string_perm = pm };
  let r : Ghost.erased raw_data_item = Ghost.hide (String typ len (Ghost.reveal v));
  cbor_match_string_intro_aux input ress r;
  let res = CBOR_Case_String ress;
  Trade.rewrite_with_trade
    (cbor_match_string ress 1.0R r)
    (cbor_match 1.0R res r);
  Trade.trans _ _ (S.pts_to input #pm v);
  res
}
```

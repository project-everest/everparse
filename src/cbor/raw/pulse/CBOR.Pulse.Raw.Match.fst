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
  (cbor_match: (perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop))
: Tot slprop
= exists* c' . R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
    cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r) **
    pure (c.cbor_tagged_tag == Tagged?.tag r)

let cbor_match_array
  (c: cbor_array)
  (p: perm)
  (r: raw_data_item {Array? r})
  (cbor_match: (perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop))
: Tot slprop
= exists* v .
    A.pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) v **
    PM.seq_list_match v (Array?.v r) (cbor_match (p `perm_mul` c.cbor_array_payload_perm)) **
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
  (cbor_match: (perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop))
: Tot slprop
= exists* v .
    A.pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) v **
    PM.seq_list_match v (Map?.v r) (cbor_match_map_entry r (cbor_match (p `perm_mul` c.cbor_map_payload_perm))) **
    pure (c.cbor_map_length == Map?.len r)

let cbor_match_serialized_array
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item { Array? r })
: Tot slprop
= cbor_match_serialized_payload_array c.cbor_serialized_payload (p `perm_mul` c.cbor_serialized_perm)  (Array?.v r) **
  pure (c.cbor_serialized_header == Array?.len r)

let cbor_match_serialized_map
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item { Map? r })
: Tot slprop
= cbor_match_serialized_payload_map c.cbor_serialized_payload (p `perm_mul` c.cbor_serialized_perm) (Map?.v r) **
  pure (c.cbor_serialized_header == Map?.len r)

let cbor_match_serialized_tagged
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item { Tagged? r })
: Tot slprop
= cbor_match_serialized_payload_tagged c.cbor_serialized_payload (p `perm_mul` c.cbor_serialized_perm) (Tagged?.v r) **
  pure (c.cbor_serialized_header == Tagged?.tag r)

let rec cbor_match
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
: Tot slprop
  (decreases r)
= match c, r with
  | CBOR_Case_Array v, Array _ _ -> cbor_match_array v p r cbor_match
  | CBOR_Case_Map v, Map _ _ -> cbor_match_map v p r cbor_match
  | CBOR_Case_Simple v, Simple _ -> cbor_match_simple v r
  | CBOR_Case_Int v, Int64 _ _ -> cbor_match_int v r
  | CBOR_Case_String v, String _ _ _ -> cbor_match_string v p r
  | CBOR_Case_Tagged v, Tagged _ _ -> cbor_match_tagged v p r cbor_match
  | CBOR_Case_Serialized_Array v, Array _ _ -> cbor_match_serialized_array v p r
  | CBOR_Case_Serialized_Map v, Map _ _ -> cbor_match_serialized_map v p r
  | CBOR_Case_Serialized_Tagged v, Tagged _ _ -> cbor_match_serialized_tagged v p r
  | _ -> pure False

let cbor_match_cases_pred
  (c: cbor_raw)
  (r: raw_data_item)
: Tot bool
= 
    match c, r with
    | CBOR_Case_Array _, Array _ _
    | CBOR_Case_Map _, Map _ _
    | CBOR_Case_Simple _, Simple _
    | CBOR_Case_Int _, Int64 _ _
    | CBOR_Case_String _, String _ _ _
    | CBOR_Case_Tagged _, Tagged _ _
    | CBOR_Case_Serialized_Array _, Array _ _
    | CBOR_Case_Serialized_Map _, Map _ _
    | CBOR_Case_Serialized_Tagged _, Tagged _ _ ->
      true
    | _ -> false

```pulse
ghost
fn cbor_match_cases
  (c: cbor_raw)
  (#pm: perm)
  (#r: raw_data_item)
  requires cbor_match pm c r
  ensures cbor_match pm c r ** pure (cbor_match_cases_pred c r)
{
  if cbor_match_cases_pred c r {
    ()
  } else {
    rewrite (cbor_match pm c r) as (pure False);
    rewrite emp as (cbor_match pm c r)
  }
}
```

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

let cbor_string_reset_perm (p: perm) (c: cbor_string) : cbor_string = {
  c with cbor_string_perm = p `perm_mul` c.cbor_string_perm
}

let cbor_serialized_reset_perm (p: perm) (c: cbor_serialized) : cbor_serialized = {
  c with cbor_serialized_perm = p `perm_mul` c.cbor_serialized_perm
}

let cbor_tagged_reset_perm (p: perm) (c: cbor_tagged) : cbor_tagged = {
  c with
    cbor_tagged_ref_perm = p `perm_mul` c.cbor_tagged_ref_perm;
    cbor_tagged_payload_perm = p `perm_mul` c.cbor_tagged_payload_perm
}

let cbor_array_reset_perm (p: perm) (c: cbor_array) : cbor_array = {
  c with
    cbor_array_array_perm = p `perm_mul` c.cbor_array_array_perm;
    cbor_array_payload_perm = p `perm_mul` c.cbor_array_payload_perm;
}

let cbor_map_reset_perm (p: perm) (c: cbor_map) : cbor_map = {
  c with
    cbor_map_array_perm = p `perm_mul` c.cbor_map_array_perm;
    cbor_map_payload_perm = p `perm_mul` c.cbor_map_payload_perm;
}

let cbor_raw_reset_perm (p: perm) (c: cbor_raw) : cbor_raw = match c with
| CBOR_Case_String v -> CBOR_Case_String (cbor_string_reset_perm p v)
| CBOR_Case_Tagged v -> CBOR_Case_Tagged (cbor_tagged_reset_perm p v)
| CBOR_Case_Array v -> CBOR_Case_Array (cbor_array_reset_perm p v)
| CBOR_Case_Map v -> CBOR_Case_Map (cbor_map_reset_perm p v)
| CBOR_Case_Serialized_Tagged v -> CBOR_Case_Serialized_Tagged (cbor_serialized_reset_perm p v)
| CBOR_Case_Serialized_Array v -> CBOR_Case_Serialized_Array (cbor_serialized_reset_perm p v)
| CBOR_Case_Serialized_Map v -> CBOR_Case_Serialized_Map (cbor_serialized_reset_perm p v)
| _ -> c

```pulse
ghost
fn cbor_string_reset_perm_correct
  (p: perm)
  (c: cbor_string)
  (r: raw_data_item)
  requires
    cbor_match_string c p r
  ensures
    cbor_match_string (cbor_string_reset_perm p c) 1.0R r **
    trade
      (cbor_match_string (cbor_string_reset_perm p c) 1.0R r)
      (cbor_match_string c p r)
{
  perm_1_l (p `perm_mul` c.cbor_string_perm);
  let c' = cbor_string_reset_perm p c;
  unfold (cbor_match_string c p r);
  fold (cbor_match_string c' 1.0R r);
  ghost fn aux (_: unit)
    requires (emp ** cbor_match_string c' 1.0R r)
    ensures (cbor_match_string c p r)
  {
    unfold (cbor_match_string c' 1.0R r);
    fold (cbor_match_string c p r)
  };
  intro_trade _ _ _ aux
}
```

```pulse
ghost
fn cbor_raw_reset_perm_correct
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
  requires
    cbor_match p c r
  ensures
    cbor_match 1.0R (cbor_raw_reset_perm p c) r **
    trade
      (cbor_match 1.0R (cbor_raw_reset_perm p c) r)
      (cbor_match p c r)
{
  cbor_match_cases c;
  let c' = cbor_raw_reset_perm p c;
  match c {
    CBOR_Case_String v -> {
      Trade.rewrite_with_trade
        (cbor_match p c r)
        (cbor_match_string v p r);
        cbor_string_reset_perm_correct p v r;
        Trade.trans _ _ (cbor_match p c r);
        Trade.rewrite_with_trade
          (cbor_match_string (cbor_string_reset_perm p v) 1.0R r)
          (cbor_match 1.0R c' r);
        Trade.trans _ _ (cbor_match p c r)
    }
    _ -> { admit () }
  }
}
```

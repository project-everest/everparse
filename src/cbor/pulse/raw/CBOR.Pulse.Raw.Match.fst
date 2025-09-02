module CBOR.Pulse.Raw.Match
#lang-pulse
include CBOR.Pulse.Raw.Format.Match
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
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
= exists* (v: Seq.seq U8.t) . pts_to c.cbor_string_ptr #(p `perm_mul` c.cbor_string_perm) v ** pure
    (Seq.length v == SZ.v (S.len c.cbor_string_ptr) /\
      (c.cbor_string_type == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) /\
      r == String c.cbor_string_type ({ size = c.cbor_string_size; value = U64.uint_to_t (SZ.v (S.len c.cbor_string_ptr)) }) v
    )

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
= exists* (v : Seq.seq cbor_raw) .
    pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) v **
    PM.seq_list_match v (Array?.v r) (cbor_match (p `perm_mul` c.cbor_array_payload_perm)) **
    pure (
      c.cbor_array_length_size == (Array?.len r).size /\
      SZ.v (S.len c.cbor_array_ptr) == U64.v (Array?.len r).value
    )

let cbor_match_map_entry0
  (r0: raw_data_item)
  (cbor_match: (cbor_raw -> (v': raw_data_item { v' << r0 }) -> slprop))
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item) { r << r0 })
: Tot slprop
= cbor_match c.cbor_map_entry_key (fst r) **
  cbor_match c.cbor_map_entry_value (snd r)

let cbor_match_map0
  (c: cbor_map)
  (p: perm)
  (r: raw_data_item {Map? r})
  (cbor_match: (perm -> cbor_raw -> (v': raw_data_item { v' << r }) -> slprop))
: Tot slprop
= exists* v .
    pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) v **
    PM.seq_list_match v (Map?.v r) (cbor_match_map_entry0 r (cbor_match (p `perm_mul` c.cbor_map_payload_perm))) **
    pure (
      c.cbor_map_length_size == (Map?.len r).size /\
      SZ.v (S.len c.cbor_map_ptr) == U64.v (Map?.len r).value
    )

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
  | CBOR_Case_Map v, Map _ _ -> cbor_match_map0 v p r cbor_match
  | CBOR_Case_Simple v, Simple _ -> cbor_match_simple v r
  | CBOR_Case_Int v, Int64 _ _ -> cbor_match_int v r
  | CBOR_Case_String v, String _ _ _ -> cbor_match_string v p r
  | CBOR_Case_Tagged v, Tagged _ _ -> cbor_match_tagged v p r cbor_match
  | CBOR_Case_Serialized_Array v, Array _ _ -> cbor_match_serialized_array v p r
  | CBOR_Case_Serialized_Map v, Map _ _ -> cbor_match_serialized_map v p r
  | CBOR_Case_Serialized_Tagged v, Tagged _ _ -> cbor_match_serialized_tagged v p r
  | _ -> pure False

let cbor_match_map_entry
  (p: perm)
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item))
: Tot slprop
= cbor_match p c.cbor_map_entry_key (fst r) **
  cbor_match p c.cbor_map_entry_value (snd r)

let cbor_match_map
  (p: perm)
  (c: cbor_map)
  (r: raw_data_item {Map? r})
: Tot slprop
= exists* v .
    pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) v **
    PM.seq_list_match v (Map?.v r) (cbor_match_map_entry (p `perm_mul` c.cbor_map_payload_perm)) **
    pure (
      c.cbor_map_length_size == (Map?.len r).size /\
      SZ.v (S.len c.cbor_map_ptr) == U64.v (Map?.len r).value
    )

let slprop_implies (s1 s2: slprop) =
  unit -> stt_ghost unit emp_inames s1 (fun _ -> s2)

let slprop_implies_elim (#s1 #s2: slprop) (f: slprop_implies s1 s2) : stt_ghost unit emp_inames s1 (fun _ -> s2) =
  f ()

let seq_list_match_implies
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match1: (t -> (v': t' { v' << v }) -> slprop))
  (item_match2: (t -> (v': t' { v' << v }) -> slprop))
  (imp: ((v0: t) -> (v': t' { v' << v }) -> slprop_implies (item_match1 v0 v') (item_match2 v0 v')))
: Tot (slprop_implies (PM.seq_list_match c v item_match1) (PM.seq_list_match c v item_match2))
  (decreases v)
= fun _ -> PM.seq_list_match_weaken c v item_match1 item_match2 (fun v0 v' -> imp v0 v' ())

fn cbor_match_map_entry0_entry
  (r0: raw_data_item)
  (p: perm)
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item) { r << r0 })
: slprop_implies (cbor_match_map_entry0 r0 (cbor_match p) c r) (cbor_match_map_entry p c r)
= (_: _) {
  rewrite (cbor_match_map_entry0 r0 (cbor_match p) c r)
    as (cbor_match_map_entry p c r)
}

ghost
fn cbor_match_map0_map
  (c: cbor_map)
  (p: perm)
  (r: raw_data_item {Map? r})
requires
  (cbor_match_map0 c p r cbor_match)
ensures
  (cbor_match_map p c r)
{
  unfold (cbor_match_map0 c p r cbor_match);
  with v . assert (PM.seq_list_match v (Map?.v r) (cbor_match_map_entry0 r (cbor_match (p `perm_mul` c.cbor_map_payload_perm))));
  slprop_implies_elim (seq_list_match_implies v (Map?.v r) (cbor_match_map_entry0 r (cbor_match (p `perm_mul` c.cbor_map_payload_perm))) (cbor_match_map_entry (p `perm_mul` c.cbor_map_payload_perm)) (cbor_match_map_entry0_entry r (p `perm_mul` c.cbor_map_payload_perm)));
  fold (cbor_match_map p c r)
}

fn cbor_match_map_entry_entry0
  (r0: raw_data_item)
  (p: perm)
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item) { r << r0 })
: slprop_implies (cbor_match_map_entry p c r) (cbor_match_map_entry0 r0 (cbor_match p) c r)
= (_: _) {
  rewrite (cbor_match_map_entry p c r)
    as (cbor_match_map_entry0 r0 (cbor_match p) c r)
}

ghost
fn cbor_match_map_map0
  (c: cbor_map)
  (p: perm)
  (r: raw_data_item {Map? r})
requires
  (cbor_match_map p c r)
ensures
  (cbor_match_map0 c p r cbor_match)
{
  unfold (cbor_match_map p c r);
  with v . assert (PM.seq_list_match v (Map?.v r) (cbor_match_map_entry (p `perm_mul` c.cbor_map_payload_perm)));
  slprop_implies_elim (seq_list_match_implies v (Map?.v r)
    (cbor_match_map_entry (p `perm_mul` c.cbor_map_payload_perm))
    (cbor_match_map_entry0 r (cbor_match (p `perm_mul` c.cbor_map_payload_perm)))
    (cbor_match_map_entry_entry0 r (p `perm_mul` c.cbor_map_payload_perm))
  );
  fold (cbor_match_map0 c p r cbor_match)
}

ghost
fn cbor_match_map0_map_trade
  (c: cbor_map)
  (p: perm)
  (r: raw_data_item {Map? r})
requires
  (cbor_match_map0 c p r cbor_match)
ensures
  (cbor_match_map p c r ** trade (cbor_match_map p c r) (cbor_match_map0 c p r cbor_match))
{
  cbor_match_map0_map c p r;
  intro
    (Trade.trade
      (cbor_match_map p c r)
      (cbor_match_map0 c p r cbor_match)
    )
    #emp
    fn _
  {
    cbor_match_map_map0 c p r;
  };
}

ghost
fn cbor_match_map_map0_trade
  (c: cbor_map)
  (p: perm)
  (r: raw_data_item {Map? r})
requires
  (cbor_match_map p c r)
ensures
  (cbor_match_map0 c p r cbor_match ** trade (cbor_match_map0 c p r cbor_match) (cbor_match_map p c r))
{
  cbor_match_map_map0 c p r;
  intro
    (Trade.trade
      (cbor_match_map0 c p r cbor_match)
      (cbor_match_map p c r)
    )
    #emp
    fn _
  {
    cbor_match_map0_map c p r;
  };
}

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
  intro
    (Trade.trade
      (cbor_match_int res v)
      q
    )
    #q
    fn _
  {
    unfold (cbor_match_int res v)
  };
}

inline_for_extraction
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

inline_for_extraction
fn cbor_match_int_intro
  (typ: major_type_uint64_or_neg_int64)
  (i: raw_uint64)
  requires emp
  returns res: cbor_raw
  ensures cbor_match 1.0R res (Int64 typ i)
{
  let resi = cbor_match_int_intro_aux typ i;
  let res = CBOR_Case_Int resi;
  fold (cbor_match 1.0R (CBOR_Case_Int resi) (Int64 typ i));
  res
}

inline_for_extraction
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

inline_for_extraction
fn cbor_match_int_elim_type
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (Int64? v)
returns res: major_type_uint64_or_neg_int64
ensures
  cbor_match p c v ** pure (Int64? v /\ res == Int64?.typ v)
{
  cbor_match_cases c;
  let CBOR_Case_Int c' = c;
  Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_int c' v);
  unfold (cbor_match_int c' v);
  fold (cbor_match_int c' v);
  Trade.elim _ _;
  c'.cbor_int_type
}

inline_for_extraction
fn cbor_match_int_elim_value
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (Int64? v)
returns res: raw_uint64
ensures
  cbor_match p c v ** pure (Int64? v /\ res == Int64?.v v)
{
  cbor_match_cases c;
  let CBOR_Case_Int c' = c;
  Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_int c' v);
  unfold (cbor_match_int c' v);
  fold (cbor_match_int c' v);
  Trade.elim _ _;
  let res = {
    size = c'.cbor_int_size;
    value = c'.cbor_int_value;
  };
  res
}

ghost
fn cbor_match_int_free
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (Int64? v)
ensures
  emp
{
  cbor_match_cases c;
  let CBOR_Case_Int c' = c;
  rewrite (cbor_match p c v) as (cbor_match_int c' v);
  unfold (cbor_match_int c' v)
}

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
  intro
    (Trade.trade
      (cbor_match_simple res v)
      q
    )
    #q
    fn _
  {
    unfold (cbor_match_simple res v)
  };
}

inline_for_extraction
fn cbor_match_simple_intro
  (i: simple_value)
  requires emp
  returns res: cbor_raw
  ensures cbor_match 1.0R res (Simple i)
{
  fold (cbor_match_simple i (Simple i));
  let res = CBOR_Case_Simple i;
  fold (cbor_match 1.0R (CBOR_Case_Simple i) (Simple i));
  res
}

inline_for_extraction
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

inline_for_extraction
fn cbor_match_simple_elim
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (Simple? v)
returns res: simple_value
ensures
  cbor_match p c v ** pure (v == Simple res)
{
  cbor_match_cases c;
  let CBOR_Case_Simple res = c;
  Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_simple res v);
  unfold (cbor_match_simple res v);
  fold (cbor_match_simple res v);
  Trade.elim _ _;
  res
}

ghost
fn cbor_match_simple_free
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (Simple? v)
ensures
  emp
{
  cbor_match_cases c;
  let CBOR_Case_Simple res = c;
  rewrite (cbor_match p c v) as (cbor_match_simple res v);
  unfold (cbor_match_simple res v)
}

ghost
fn cbor_match_string_intro_aux
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Seq.seq U8.t)
  (c: cbor_string)
  (r: raw_data_item)
  requires
    pts_to input #pm v ** pure (
      input == c.cbor_string_ptr /\
      pm == c.cbor_string_perm /\
      Seq.length v == SZ.v (S.len c.cbor_string_ptr) /\
      (c.cbor_string_type == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) /\
      r == String c.cbor_string_type ({ size = c.cbor_string_size; value = U64.uint_to_t (SZ.v (S.len c.cbor_string_ptr)) }) v
    )
  ensures
    cbor_match_string c 1.0R r **
    trade (cbor_match_string c 1.0R r) (pts_to input #pm v)
{
  rewrite each input as c.cbor_string_ptr;
  fold (cbor_match_string c 1.0R r);
  intro
    (Trade.trade
      (cbor_match_string c 1.0R r)
      (pts_to input #pm v)
    )
    #emp
    fn _
  {
    unfold (cbor_match_string c 1.0R r);
    rewrite each c.cbor_string_ptr as input;
    ();
  };
}

inline_for_extraction
fn cbor_match_string_intro
  (typ: major_type_byte_string_or_text_string)
  (len: raw_uint64)
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  requires
    pts_to input #pm v ** pure (
      (typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) /\
      Seq.length v == U64.v len.value
    )
  returns c: cbor_raw
  ensures exists* r .
    cbor_match 1.0R c r **
    trade (cbor_match 1.0R c r) (pts_to input #pm v) **
    pure (
      Seq.length v == U64.v len.value /\
      (typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) /\
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
  Trade.trans _ _ (pts_to input #pm v);
  res
}

inline_for_extraction
fn cbor_match_string_elim_type
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (String? v)
returns res: major_type_byte_string_or_text_string
ensures
  cbor_match p c v ** pure (String? v /\ res == String?.typ v)
{
  cbor_match_cases c;
  let CBOR_Case_String c' = c;
  Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_string c' p v);
  unfold (cbor_match_string c' p v);
  fold (cbor_match_string c' p v);
  Trade.elim _ _;
  c'.cbor_string_type
}

inline_for_extraction
fn cbor_match_string_elim_length
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (String? v)
returns res: raw_uint64
ensures
  cbor_match p c v ** pure (String? v /\ res == String?.len v)
{
  cbor_match_cases c;
  let CBOR_Case_String c' = c;
  Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_string c' p v);
  unfold (cbor_match_string c' p v);
  fold (cbor_match_string c' p v);
  Trade.elim _ _;
  let res = {
    size = c'.cbor_string_size;
    value = SZ.sizet_to_uint64 (S.len c'.cbor_string_ptr);
  };
  res
}

ghost fn cbor_match_string_elim_payload_aux
  (c: cbor_string)
  (p: perm)
  (r: Ghost.erased raw_data_item { String? r })
  (v: Seq.seq U8.t)
  (_: unit)
requires
  pure (
    String?.typ r == c.cbor_string_type /\
    String?.len r == ({ size = c.cbor_string_size; value = U64.uint_to_t (SZ.v (S.len c.cbor_string_ptr)) }) /\
    v == (String?.v r <: Seq.seq U8.t)
  ) **
  pts_to c.cbor_string_ptr #(p `perm_mul` c.cbor_string_perm) v
ensures
  cbor_match_string c p r
{
  fold (cbor_match_string c p r)
}

inline_for_extraction
fn cbor_match_string_elim_payload
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (String? v)
returns res: S.slice U8.t
ensures exists* p' (v': Seq.seq U8.t) .
  pts_to res #p' v' **
  trade (pts_to res #p' v') (cbor_match p c v) **
  pure (String? v /\ v' == String?.v v)
{
  cbor_match_cases c;
  let CBOR_Case_String c' = c;
  Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_string c' p v);
  unfold (cbor_match_string c' p v);
  with v' . assert (pts_to c'.cbor_string_ptr #(p `perm_mul` c'.cbor_string_perm) v');
  intro
    (Trade.trade
      (pts_to c'.cbor_string_ptr #(p `perm_mul` c'.cbor_string_perm) v')
      (cbor_match_string c' p v)
    )
    #emp
    fn _
  {
    fold (cbor_match_string c' p v)
  };
  Trade.trans _ _ (cbor_match p c v);
  c'.cbor_string_ptr
}

let cbor_match_eq_tagged
  (pm: perm)
  (ct: cbor_tagged)
  (r: raw_data_item)
: Lemma
  (requires (Tagged? r))
  (ensures 
    (cbor_match pm (CBOR_Case_Tagged ct) r ==
    cbor_match_tagged ct pm r cbor_match
  ))
=
  let Tagged tag v = r in
  assert_norm (
    cbor_match pm (CBOR_Case_Tagged ct) (Tagged tag v) ==
      cbor_match_tagged ct pm (Tagged tag v) cbor_match
  )

inline_for_extraction
fn cbor_match_tagged_get_tag
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (Tagged? v)
returns res: raw_uint64
ensures
  cbor_match p c v ** pure (Tagged? v /\ res == Tagged?.tag v)
{
  cbor_match_cases c;
  match c {
    CBOR_Case_Tagged c' -> {
      cbor_match_eq_tagged p c' v;
      Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_tagged c' p v cbor_match);
      unfold (cbor_match_tagged c' p v cbor_match);
      fold (cbor_match_tagged c' p v cbor_match);
      Trade.elim _ _;
      c'.cbor_tagged_tag
    }
    CBOR_Case_Serialized_Tagged c' -> {
      Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_serialized_tagged c' p v);
      unfold (cbor_match_serialized_tagged c' p v);
      fold (cbor_match_serialized_tagged c' p v);
      Trade.elim _ _;
      c'.cbor_serialized_header
    }
  }
}

ghost
fn cbor_match_tagged_elim
  (c: cbor_tagged)
  (p: perm)
  (r: raw_data_item { Tagged? r })
  requires
    cbor_match_tagged c p r cbor_match
  ensures exists* c' . R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
    cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r) **
    trade
      (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
        cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r))
      (cbor_match_tagged c p r cbor_match)
{
  unfold (cbor_match_tagged c p r cbor_match);
  with c' . assert (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
    cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r));
  intro
    (Trade.trade
      (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
        cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r)
      )
      (cbor_match_tagged c p r cbor_match)
    )
    #emp
    fn _
  {
    fold (cbor_match_tagged c p r cbor_match)
  };
}

inline_for_extraction
fn cbor_match_tagged_intro
  (tag: raw_uint64)
  (pc: R.ref cbor_raw)
  (#pr: perm)
  (#c: Ghost.erased cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item)
  requires R.pts_to pc #pr c ** cbor_match pm c r
  returns res: cbor_raw
  ensures
    cbor_match 1.0R res (Tagged tag r) **
    trade
      (cbor_match 1.0R res (Tagged tag r))
      (R.pts_to pc #pr c ** cbor_match pm c r)
{
  let res' = {
    cbor_tagged_tag = tag;
    cbor_tagged_ptr = pc;
    cbor_tagged_ref_perm = pr /. 2.0R;
    cbor_tagged_payload_perm = pm;
  };
  R.share pc;
  rewrite (R.pts_to pc #(pr /. 2.0R) c)
    as (R.pts_to res'.cbor_tagged_ptr #res'.cbor_tagged_ref_perm c);
  fold (cbor_match_tagged res' 1.0R (Tagged tag r) cbor_match);
  intro
    (Trade.trade
      (cbor_match_tagged res' 1.0R (Tagged tag r) cbor_match)
      (R.pts_to pc #pr c ** cbor_match pm c r)
    )
    #(R.pts_to pc #(pr /. 2.0R) c)
    fn _
  {
    unfold (cbor_match_tagged res' 1.0R (Tagged tag r) cbor_match);
    with c' . assert (R.pts_to res'.cbor_tagged_ptr #res'.cbor_tagged_ref_perm c');
    rewrite (R.pts_to res'.cbor_tagged_ptr #res'.cbor_tagged_ref_perm c')
      as (R.pts_to pc #(pr /. 2.0R) c');
    R.gather pc
  };
  cbor_match_eq_tagged 1.0R res' (Tagged tag r);
  let res = CBOR_Case_Tagged res';
  Trade.rewrite_with_trade
    (cbor_match_tagged res' 1.0R (Tagged tag r) cbor_match)
    (cbor_match 1.0R res (Tagged tag r));
  Trade.trans (cbor_match 1.0R res (Tagged tag r)) _ _;
  res
}

let cbor_match_eq_array
  (pm: perm)
  (ct: cbor_array)
  (r: raw_data_item)
: Lemma
  (requires (Array? r))
  (ensures 
    cbor_match pm (CBOR_Case_Array ct) r ==
    cbor_match_array ct pm r cbor_match
  )
=
  assert_norm (cbor_match pm (CBOR_Case_Array ct) (Array (Array?.len r) (Array?.v r)) ==
    cbor_match_array ct pm (Array (Array?.len r) (Array?.v r)) cbor_match
  )

inline_for_extraction
fn cbor_match_array_get_length
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (Array? v)
returns res: raw_uint64
ensures
  cbor_match p c v ** pure (Array? v /\ res == Array?.len v)
{
  cbor_match_cases c;
  match c {
    CBOR_Case_Array c' -> {
      cbor_match_eq_array p c' v;
      Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_array c' p v cbor_match);
      unfold (cbor_match_array c' p v cbor_match);
      fold (cbor_match_array c' p v cbor_match);
      Trade.elim _ _;
      ({ size = c'.cbor_array_length_size; value = SZ.sizet_to_uint64 (S.len c'.cbor_array_ptr) })
    }
    CBOR_Case_Serialized_Array c' -> {
      Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_serialized_array c' p v);
      unfold (cbor_match_serialized_array c' p v);
      fold (cbor_match_serialized_array c' p v);
      Trade.elim _ _;
      c'.cbor_serialized_header
    }
  }
}

inline_for_extraction
fn cbor_match_array_intro
  (len: raw_uint64)
  (pc: S.slice cbor_raw)
  (#pr: perm)
  (#c: Ghost.erased (Seq.seq cbor_raw))
  (#pm: perm)
  (#r: Ghost.erased (list raw_data_item))
  requires pts_to pc #pr c ** PM.seq_list_match c r (cbor_match pm) ** pure (Seq.length c == U64.v len.value)
  returns res: cbor_raw
  ensures exists* r' .
    cbor_match 1.0R res (Array len r') **
    trade
      (cbor_match 1.0R res (Array len r'))
      (pts_to pc #pr c ** PM.seq_list_match c r (cbor_match pm)) **
    pure (Ghost.reveal r == r')
{
  S.pts_to_len pc;
  PM.seq_list_match_length (cbor_match pm) c r;
  let res' = {
    cbor_array_length_size = len.size;
    cbor_array_ptr = pc;
    cbor_array_array_perm = pr /. 2.0R;
    cbor_array_payload_perm = pm;
  };
  S.share pc;
  rewrite (pts_to pc #(pr /. 2.0R) c)
    as (pts_to res'.cbor_array_ptr #(1.0R `perm_mul` res'.cbor_array_array_perm) c);
  fold (cbor_match_array res' 1.0R (Array len r) cbor_match);
  intro
    (Trade.trade
      (cbor_match_array res' 1.0R (Array len r) cbor_match)
      (pts_to pc #pr c **
        PM.seq_list_match c r (cbor_match pm)
      )
    )
    #(pts_to pc #(pr /. 2.0R) c)
    fn _
  {
    unfold (cbor_match_array res' 1.0R (Array len r) cbor_match);
    with c' . assert (pts_to res'.cbor_array_ptr #(1.0R `perm_mul` res'.cbor_array_array_perm) c');
    rewrite (pts_to res'.cbor_array_ptr #res'.cbor_array_array_perm c')
            as (pts_to pc #(pr /. 2.0R) c');
    S.gather pc;
    with v _x _y.
      assert PM.seq_list_match #cbor_raw #raw_data_item v _x _y;
    rewrite each v as c;
    ()
  };
  cbor_match_eq_array 1.0R res' (Array len r);
  let res = CBOR_Case_Array res';
  Trade.rewrite_with_trade
    (cbor_match_array res' 1.0R (Array len r) cbor_match)
    (cbor_match 1.0R res (Array len r));
  Trade.trans (cbor_match 1.0R res (Array len r)) _ _;
  res
}

let cbor_match_eq_map0
  (pm: perm)
  (ct: cbor_map)
  (r: raw_data_item)
: Lemma
  (requires (Map? r))
  (ensures 
    cbor_match pm (CBOR_Case_Map ct) r ==
    cbor_match_map0 ct pm r cbor_match
  )
=
  assert_norm (cbor_match pm (CBOR_Case_Map ct) (Map (Map?.len r) (Map?.v r)) ==
    cbor_match_map0 ct pm (Map (Map?.len r) (Map?.v r)) cbor_match
  )

inline_for_extraction
fn cbor_match_map_get_length
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p c v ** pure (Map? v)
returns res: raw_uint64
ensures
  cbor_match p c v ** pure (Map? v /\ res == Map?.len v)
{
  cbor_match_cases c;
  match c {
    CBOR_Case_Map c' -> {
      cbor_match_eq_map0 p c' v;
      Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_map0 c' p v cbor_match);
      unfold (cbor_match_map0 c' p v cbor_match);
      fold (cbor_match_map0 c' p v cbor_match);
      Trade.elim _ _;
      ({ size = c'.cbor_map_length_size; value = SZ.sizet_to_uint64 (S.len c'.cbor_map_ptr) })
    }
    CBOR_Case_Serialized_Map c' -> {
      Trade.rewrite_with_trade (cbor_match p c v) (cbor_match_serialized_map c' p v);
      unfold (cbor_match_serialized_map c' p v);
      fold (cbor_match_serialized_map c' p v);
      Trade.elim _ _;
      c'.cbor_serialized_header
    }
  }
}

inline_for_extraction
fn cbor_match_map_intro
  (len: raw_uint64)
  (pc: S.slice cbor_map_entry)
  (#pr: perm)
  (#c: Ghost.erased (Seq.seq cbor_map_entry))
  (#pm: perm)
  (#r: Ghost.erased (list (raw_data_item & raw_data_item)))
  requires pts_to pc #pr c ** PM.seq_list_match c r (cbor_match_map_entry pm) ** pure (Seq.length c == U64.v len.value)
  returns res: cbor_raw
  ensures exists* r' .
    cbor_match 1.0R res (Map len r') **
    trade
      (cbor_match 1.0R res (Map len r'))
      (pts_to pc #pr c ** PM.seq_list_match c r (cbor_match_map_entry pm)) **
    pure (Ghost.reveal r == r')
{
  S.pts_to_len pc;
  PM.seq_list_match_length (cbor_match_map_entry pm) c r;
  let res' = {
    cbor_map_length_size = len.size;
    cbor_map_ptr = pc;
    cbor_map_array_perm = pr /. 2.0R;
    cbor_map_payload_perm = pm;
  };
  S.share pc;
  rewrite (pts_to pc #(pr /. 2.0R) c)
    as (pts_to res'.cbor_map_ptr #(1.0R `perm_mul` res'.cbor_map_array_perm) c);
  fold (cbor_match_map 1.0R res' (Map len r));
  intro
    (Trade.trade
      (cbor_match_map 1.0R res' (Map len r))
      (pts_to pc #pr c **
        PM.seq_list_match c r (cbor_match_map_entry pm)
      )
    )
    #(pts_to pc #(pr /. 2.0R) c)
    fn _
  {
    unfold (cbor_match_map 1.0R res' (Map len r));
    with c' . assert (pts_to res'.cbor_map_ptr #(1.0R `perm_mul` res'.cbor_map_array_perm) c');
    rewrite (pts_to res'.cbor_map_ptr #res'.cbor_map_array_perm c')
      as (pts_to pc #(pr /. 2.0R) c');
    S.gather pc;
    with v _x _y.
      assert PM.seq_list_match #cbor_map_entry #(raw_data_item & raw_data_item) v _x _y;
    rewrite each v as c;
    ()
  };
  cbor_match_map_map0_trade res' 1.0R (Map len r);
  Trade.trans _ (cbor_match_map 1.0R res' (Map len r)) _;
  cbor_match_eq_map0 1.0R res' (Map len r);
  let res = CBOR_Case_Map res';
  Trade.rewrite_with_trade
    (cbor_match_map0 res' 1.0R (Map len r) cbor_match)
    (cbor_match 1.0R res (Map len r));
  Trade.trans (cbor_match 1.0R res (Map len r)) _ _;
  res
}

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

let cbor_raw_reset_perm_tot (p: perm) (c: cbor_raw) : cbor_raw = match c with
| CBOR_Case_String v -> CBOR_Case_String (cbor_string_reset_perm p v)
| CBOR_Case_Tagged v -> CBOR_Case_Tagged (cbor_tagged_reset_perm p v)
| CBOR_Case_Array v -> CBOR_Case_Array (cbor_array_reset_perm p v)
| CBOR_Case_Map v -> CBOR_Case_Map (cbor_map_reset_perm p v)
| CBOR_Case_Serialized_Tagged v -> CBOR_Case_Serialized_Tagged (cbor_serialized_reset_perm p v)
| CBOR_Case_Serialized_Array v -> CBOR_Case_Serialized_Array (cbor_serialized_reset_perm p v)
| CBOR_Case_Serialized_Map v -> CBOR_Case_Serialized_Map (cbor_serialized_reset_perm p v)
| _ -> c

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
  rewrite each c.cbor_string_ptr as c'.cbor_string_ptr;
  fold (cbor_match_string c' 1.0R r);
  intro
    (Trade.trade
      (cbor_match_string c' 1.0R r)
      (cbor_match_string c p r)
    )
    #emp
    fn _
  {
    unfold (cbor_match_string c' 1.0R r);
    rewrite each c'.cbor_string_ptr as c.cbor_string_ptr;
    fold (cbor_match_string c p r)
  };
}

ghost
fn cbor_tagged_reset_perm_correct
  (p: perm)
  (c: cbor_tagged)
  (r: raw_data_item { Tagged? r })
  requires
    cbor_match_tagged c p r cbor_match
  ensures
    cbor_match_tagged (cbor_tagged_reset_perm p c) 1.0R r cbor_match **
    trade
      (cbor_match_tagged (cbor_tagged_reset_perm p c) 1.0R r cbor_match)
      (cbor_match_tagged c p r cbor_match)
{
  perm_1_l (p `perm_mul` c.cbor_tagged_ref_perm);
  perm_1_l (p `perm_mul` c.cbor_tagged_payload_perm);
  let c' = cbor_tagged_reset_perm p c;
  unfold (cbor_match_tagged c p r cbor_match);
  with s . assert (pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) s);
  rewrite (pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) s)
    as (pts_to c'.cbor_tagged_ptr #(1.0R `perm_mul` c'.cbor_tagged_ref_perm) s);
  fold (cbor_match_tagged c' 1.0R r cbor_match);
  intro
    (Trade.trade
      (cbor_match_tagged c' 1.0R r cbor_match)
      (cbor_match_tagged c p r cbor_match)
    )
    #emp
    fn _
  {
    unfold (cbor_match_tagged c' 1.0R r);
    with s . assert (pts_to c'.cbor_tagged_ptr #(1.0R `perm_mul` c'.cbor_tagged_ref_perm) s);
    rewrite (pts_to c'.cbor_tagged_ptr #(1.0R `perm_mul` c'.cbor_tagged_ref_perm) s)
      as (pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) s);
    fold (cbor_match_tagged c p r cbor_match)
  };
}

ghost
fn cbor_array_reset_perm_correct
  (p: perm)
  (c: cbor_array)
  (r: raw_data_item { Array? r })
  requires
    cbor_match_array c p r cbor_match
  ensures
    cbor_match_array (cbor_array_reset_perm p c) 1.0R r cbor_match **
    trade
      (cbor_match_array (cbor_array_reset_perm p c) 1.0R r cbor_match)
      (cbor_match_array c p r cbor_match)
{
  perm_1_l (p `perm_mul` c.cbor_array_array_perm);
  perm_1_l (p `perm_mul` c.cbor_array_payload_perm);
  let c' = cbor_array_reset_perm p c;
  unfold (cbor_match_array c p r cbor_match);
  with s . assert (pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s);
  rewrite (pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s)
    as (pts_to c'.cbor_array_ptr #(1.0R `perm_mul` c'.cbor_array_array_perm) s);
  fold (cbor_match_array c' 1.0R r cbor_match);
  intro
    (Trade.trade
      (cbor_match_array c' 1.0R r cbor_match)
      (cbor_match_array c p r cbor_match)
    )
    #emp
    fn _
  {
    unfold (cbor_match_array c' 1.0R r);
    with s . assert (pts_to c'.cbor_array_ptr #(1.0R `perm_mul` c'.cbor_array_array_perm) s);
    rewrite (pts_to c'.cbor_array_ptr #(1.0R `perm_mul` c'.cbor_array_array_perm) s)
      as (pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s);
    fold (cbor_match_array c p r cbor_match)
  };
}

ghost
fn cbor_map_reset_perm_correct
  (p: perm)
  (c: cbor_map)
  (r: raw_data_item { Map? r })
  requires
    cbor_match_map0 c p r cbor_match
  ensures
    cbor_match_map0 (cbor_map_reset_perm p c) 1.0R r cbor_match **
    trade
      (cbor_match_map0 (cbor_map_reset_perm p c) 1.0R r cbor_match)
      (cbor_match_map0 c p r cbor_match)
{
  perm_1_l (p `perm_mul` c.cbor_map_array_perm);
  perm_1_l (p `perm_mul` c.cbor_map_payload_perm);
  let c' = cbor_map_reset_perm p c;
  unfold (cbor_match_map0 c p r cbor_match);
  with s . assert (pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) s);
  rewrite (pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) s)
    as (pts_to c'.cbor_map_ptr #(1.0R `perm_mul` c'.cbor_map_array_perm) s);
  fold (cbor_match_map0 c' 1.0R r cbor_match);
  intro
    (Trade.trade
      (cbor_match_map0 c' 1.0R r cbor_match)
      (cbor_match_map0 c p r cbor_match)
    )
    #emp
    fn _
  {
    unfold (cbor_match_map0 c' 1.0R r);
    with s . assert (pts_to c'.cbor_map_ptr #(1.0R `perm_mul` c'.cbor_map_array_perm) s);
    rewrite (pts_to c'.cbor_map_ptr #(1.0R `perm_mul` c'.cbor_map_array_perm) s)
      as (pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) s);
    fold (cbor_match_map0 c p r cbor_match)
  };
}

ghost
fn cbor_raw_reset_perm_correct
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
  requires
    cbor_match p c r
  ensures
    cbor_match 1.0R (cbor_raw_reset_perm_tot p c) r **
    trade
      (cbor_match 1.0R (cbor_raw_reset_perm_tot p c) r)
      (cbor_match p c r)
{
  cbor_match_cases c;
  let c' = cbor_raw_reset_perm_tot p c;
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
    CBOR_Case_Int v -> {
      Trade.rewrite_with_trade
        (cbor_match p c r)
        (cbor_match_int v r);
      Trade.rewrite_with_trade
        (cbor_match_int v r)
        (cbor_match 1.0R c r);
      Trade.trans _ _ (cbor_match p c r)
    }
    CBOR_Case_Simple v -> {
      Trade.rewrite_with_trade
        (cbor_match p c r)
        (cbor_match_simple v r);
      Trade.rewrite_with_trade
        (cbor_match_simple v r)
        (cbor_match 1.0R c r);
      Trade.trans _ _ (cbor_match p c r)
    }
    CBOR_Case_Tagged v -> {
      cbor_match_eq_tagged p v r;
      cbor_match_eq_tagged 1.0R (cbor_tagged_reset_perm p v) r;
      Trade.rewrite_with_trade
        (cbor_match p c r)
        (cbor_match_tagged v p r cbor_match);
      cbor_tagged_reset_perm_correct p v r;
      Trade.trans _ _ (cbor_match p c r);
      Trade.rewrite_with_trade
        (cbor_match_tagged (cbor_tagged_reset_perm p v) 1.0R r cbor_match)
        (cbor_match 1.0R c' r);
      Trade.trans _ _ (cbor_match p c r)
    }
    CBOR_Case_Array v -> {
      cbor_match_eq_array p v r;
      cbor_match_eq_array 1.0R (cbor_array_reset_perm p v) r;
      Trade.rewrite_with_trade
        (cbor_match p c r)
        (cbor_match_array v p r cbor_match);
      cbor_array_reset_perm_correct p v r;
      Trade.trans _ _ (cbor_match p c r);
      Trade.rewrite_with_trade
        (cbor_match_array (cbor_array_reset_perm p v) 1.0R r cbor_match)
        (cbor_match 1.0R c' r);
      Trade.trans _ _ (cbor_match p c r)
    }
    CBOR_Case_Map v -> {
      cbor_match_eq_map0 p v r;
      cbor_match_eq_map0 1.0R (cbor_map_reset_perm p v) r;
      Trade.rewrite_with_trade
        (cbor_match p c r)
        (cbor_match_map0 v p r cbor_match);
      cbor_map_reset_perm_correct p v r;
      Trade.trans _ _ (cbor_match p c r);
      Trade.rewrite_with_trade
        (cbor_match_map0 (cbor_map_reset_perm p v) 1.0R r cbor_match)
        (cbor_match 1.0R c' r);
      Trade.trans _ _ (cbor_match p c r)
    }
    CBOR_Case_Serialized_Tagged _ -> {
      Trade.rewrite_with_trade
        (cbor_match p c r)
        (cbor_match 1.0R c' r)
    }
    CBOR_Case_Serialized_Array _ -> {
      Trade.rewrite_with_trade
        (cbor_match p c r)
        (cbor_match 1.0R c' r)
    }
    CBOR_Case_Serialized_Map _ -> {
      Trade.rewrite_with_trade
        (cbor_match p c r)
        (cbor_match 1.0R c' r)
    }
  }
}

inline_for_extraction
fn cbor_raw_reset_perm
  (p: perm)
  (c: cbor_raw)
  (r: Ghost.erased raw_data_item)
  requires
    cbor_match p c r
  returns c' : cbor_raw
  ensures
    cbor_match 1.0R c' r **
    trade
      (cbor_match 1.0R c' r)
      (cbor_match p c r)
{
  cbor_raw_reset_perm_correct p c r;
  cbor_raw_reset_perm_tot p c
}

fn cbor_mk_map_entry
  (xk: cbor_raw)
  (xv: cbor_raw)
  (#pk: perm)
  (#vk: Ghost.erased raw_data_item)
  (#pv: perm)
  (#vv: Ghost.erased raw_data_item)
requires
    (cbor_match pk xk vk ** cbor_match pv xv vv)
returns res: cbor_map_entry
ensures
    (
      cbor_match_map_entry 1.0R res (Ghost.reveal vk, Ghost.reveal vv) **
      Trade.trade
        (cbor_match_map_entry 1.0R res (Ghost.reveal vk, Ghost.reveal vv))
        (cbor_match pk xk vk ** cbor_match pv xv vv)
    )
{
  let res : cbor_map_entry = {
    cbor_map_entry_key = cbor_raw_reset_perm_tot pk xk;
    cbor_map_entry_value = cbor_raw_reset_perm_tot pv xv;
  };
  cbor_raw_reset_perm_correct pk xk vk;
  cbor_raw_reset_perm_correct pv xv vv;
  Trade.rewrite_with_trade
    (cbor_match 1.0R (cbor_raw_reset_perm_tot pk xk) vk ** cbor_match 1.0R (cbor_raw_reset_perm_tot pv xv) vv)
    (cbor_match_map_entry 1.0R res (Ghost.reveal vk, Ghost.reveal vv));
  Trade.trans_concl_l (cbor_match_map_entry 1.0R res (Ghost.reveal vk, Ghost.reveal vv)) _ _ _; 
  Trade.trans_concl_r (cbor_match_map_entry 1.0R res (Ghost.reveal vk, Ghost.reveal vv)) _ _ _; 
  res
}

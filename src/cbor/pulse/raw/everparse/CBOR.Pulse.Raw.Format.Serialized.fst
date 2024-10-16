module CBOR.Pulse.Raw.Format.Serialized
open CBOR.Spec.Raw.Base
open CBOR.Pulse.Raw.Iterator
open CBOR.Pulse.Raw.EverParse.Iterator
open Pulse.Lib.Slice open Pulse.Lib.Pervasives open Pulse.Lib.Trade
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Format
open LowParse.Pulse.Combinators
open CBOR.Pulse.Raw.EverParse.Serialized.Base
friend CBOR.Pulse.Raw.Format.Match

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

let cbor_serialized_array_iterator_match = cbor_raw_serialized_iterator_match serialize_raw_data_item

module LP = LowParse.Pulse.VCList

```pulse
ghost
fn cbor_match_serialized_array_elim
  (c: cbor_serialized)
  (pm: perm)
  (r: raw_data_item { Array? r })
  requires
    cbor_match_serialized_array c pm r
  ensures exists* pm' .
    pts_to_serialized (LP.serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item) c.cbor_serialized_payload #pm' (Array?.v r) **
    trade
      (pts_to_serialized (LP.serialize_nlist (U64.v (Array?.len r).value) serialize_raw_data_item) c.cbor_serialized_payload #pm' (Array?.v r))
      (cbor_match_serialized_array c pm r)
{
  unfold (cbor_match_serialized_array c pm r);
  unfold (cbor_match_serialized_payload_array c.cbor_serialized_payload (pm `perm_mul` c.cbor_serialized_perm) (Array?.v r));
  with pm' . assert (pts_to_serialized (LP.serialize_nlist (U64.v (Array?.len r).value)  serialize_raw_data_item) c.cbor_serialized_payload #pm' (Array?.v r));
  ghost fn aux (_: unit)
    requires emp ** (pts_to_serialized (LP.serialize_nlist (U64.v (Array?.len r).value)  serialize_raw_data_item) c.cbor_serialized_payload #pm' (Array?.v r))
    ensures (cbor_match_serialized_array c pm r)
  {
    fold (cbor_match_serialized_payload_array c.cbor_serialized_payload (pm `perm_mul` c.cbor_serialized_perm) (Array?.v r));
    fold (cbor_match_serialized_array c pm r);
  };
  intro_trade _ _ _ aux
}
```

#set-options "--print_implicits"

```pulse
fn cbor_serialized_array_iterator_init
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
    (cbor_match_serialized_array c pm r)
returns res: cbor_raw_serialized_iterator
ensures
    (exists* p .
      cbor_serialized_array_iterator_match p res (Array?.v r) **
      trade
        (cbor_serialized_array_iterator_match p res (Array?.v r))
        (cbor_match_serialized_array c pm r)
    )
{
  cbor_match_serialized_array_elim c pm r;
  with p . assert (
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (U64.v (Array?.len (Ghost.reveal r)).value)
          serialize_raw_data_item)
      c.cbor_serialized_payload
      #p
      (Array?.v (Ghost.reveal r)))
  );
  let res : cbor_raw_serialized_iterator = {
    s = c.cbor_serialized_payload;
    len = U64.v (Array?.len r).value;
  };
  Trade.rewrite_with_trade
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (U64.v (Array?.len (Ghost.reveal r)).value)
          serialize_raw_data_item)
      c.cbor_serialized_payload
      #p
      (Array?.v (Ghost.reveal r)))
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (Ghost.reveal res.len)
          serialize_raw_data_item)
      res.s
      #p
      (Array?.v (Ghost.reveal r))      
  )
  ;
  Trade.trans _ _ (cbor_match_serialized_array c pm r);
  cbor_raw_serialized_iterator_fold serialize_raw_data_item p res (Array?.v r);
  Trade.trans _ _ (cbor_match_serialized_array c pm r);
  fold (cbor_serialized_array_iterator_match p res (Array?.v r));
  res
}
```

let cbor_serialized_array_iterator_is_empty = cbor_raw_serialized_iterator_is_empty _

inline_for_extraction
```pulse
fn cbor_serialized_array_iterator_next_cont (_: unit)
: cbor_raw_serialized_iterator_next_cont #cbor_raw #raw_data_item #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item cbor_match
= (x: _) (#pm: _) (#v: _) {
  cbor_read x
}
```

let cbor_serialized_array_iterator_next sq = cbor_raw_serialized_iterator_next _ (jump_raw_data_item sq) cbor_match (cbor_serialized_array_iterator_next_cont ())

let cbor_serialized_map_iterator_match = cbor_raw_serialized_iterator_match (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)

module LP = LowParse.Pulse.VCList

```pulse
ghost
fn cbor_match_serialized_map_elim
  (c: cbor_serialized)
  (pm: perm)
  (r: raw_data_item { Map? r })
  requires
    cbor_match_serialized_map c pm r
  ensures exists* pm' .
    pts_to_serialized (LP.serialize_nlist (U64.v (Map?.len r).value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c.cbor_serialized_payload #pm' (Map?.v r) **
    trade
      (pts_to_serialized (LP.serialize_nlist (U64.v (Map?.len r).value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c.cbor_serialized_payload #pm' (Map?.v r))
      (cbor_match_serialized_map c pm r)
{
  unfold (cbor_match_serialized_map c pm r);
  unfold (cbor_match_serialized_payload_map c.cbor_serialized_payload (pm `perm_mul` c.cbor_serialized_perm) (Map?.v r));
  with pm' . assert (pts_to_serialized (LP.serialize_nlist (U64.v (Map?.len r).value)  (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c.cbor_serialized_payload #pm' (Map?.v r));
  ghost fn aux (_: unit)
    requires emp ** (pts_to_serialized (LP.serialize_nlist (U64.v (Map?.len r).value)  (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c.cbor_serialized_payload #pm' (Map?.v r))
    ensures (cbor_match_serialized_map c pm r)
  {
    fold (cbor_match_serialized_payload_map c.cbor_serialized_payload (pm `perm_mul` c.cbor_serialized_perm) (Map?.v r));
    fold (cbor_match_serialized_map c pm r);
  };
  intro_trade _ _ _ aux
}
```

```pulse
fn cbor_serialized_map_iterator_init
  (c: cbor_serialized)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
requires
    (cbor_match_serialized_map c pm r)
returns res: cbor_raw_serialized_iterator
ensures
    (exists* p .
      cbor_serialized_map_iterator_match p res (Map?.v r) **
      trade
        (cbor_serialized_map_iterator_match p res (Map?.v r))
        (cbor_match_serialized_map c pm r)
    )
{
  cbor_match_serialized_map_elim c pm r;
  with p . assert (
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (U64.v (Map?.len (Ghost.reveal r)).value)
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      c.cbor_serialized_payload
      #p
      (Map?.v (Ghost.reveal r)))
  );
  let res : cbor_raw_serialized_iterator = {
    s = c.cbor_serialized_payload;
    len = U64.v (Map?.len r).value;
  };
  Trade.rewrite_with_trade
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (U64.v (Map?.len (Ghost.reveal r)).value)
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      c.cbor_serialized_payload
      #p
      (Map?.v (Ghost.reveal r)))
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (Ghost.reveal res.len)
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      res.s
      #p
      (Map?.v (Ghost.reveal r))      
  )
  ;
  Trade.trans _ _ (cbor_match_serialized_map c pm r);
  cbor_raw_serialized_iterator_fold (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) p res (Map?.v r);
  Trade.trans _ _ (cbor_match_serialized_map c pm r);
  fold (cbor_serialized_map_iterator_match p res (Map?.v r));
  res
}
```

let cbor_serialized_map_iterator_is_empty = cbor_raw_serialized_iterator_is_empty _

module LPC = LowParse.Pulse.Combinators

inline_for_extraction
```pulse
fn cbor_serialized_map_iterator_next_cont (sq: squash SZ.fits_u64)
: cbor_raw_serialized_iterator_next_cont #cbor_map_entry #(raw_data_item & raw_data_item) #(and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind) #(nondep_then parse_raw_data_item parse_raw_data_item) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) cbor_match_map_entry
= (x: _) (#pm: _) (#v: _) {
  let sp = LPC.split_nondep_then
    serialize_raw_data_item
    (jump_raw_data_item sq)
    serialize_raw_data_item
    x;
  match sp {
    SlicePair s1 s2 -> {
      unfold (LPC.split_nondep_then_post serialize_raw_data_item serialize_raw_data_item x pm v sp);
      unfold (LPC.split_nondep_then_post' serialize_raw_data_item serialize_raw_data_item x pm v s1 s2);
      with v1 . assert (pts_to_serialized serialize_raw_data_item s1 #pm v1);
      with v2 . assert (pts_to_serialized serialize_raw_data_item s2 #pm v2);
      let res1 = cbor_read s1;
      let res2 = cbor_read s2;
      Trade.prod _ (pts_to_serialized serialize_raw_data_item s1 #pm v1) _ (pts_to_serialized serialize_raw_data_item s2 #pm v2);
      Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) x #pm v);
      let res : cbor_map_entry = {
        cbor_map_entry_key = res1;
        cbor_map_entry_value = res2;
      };
      Trade.rewrite_with_trade
        (cbor_match 1.0R res1 v1 ** cbor_match 1.0R res2 v2)
        (cbor_match_map_entry 1.0R res v);
      Trade.trans _ _ (pts_to_serialized (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) x #pm v);
      res
    }
  }
}
```

let cbor_serialized_map_iterator_next sq = cbor_raw_serialized_iterator_next _ (jump_nondep_then (jump_raw_data_item sq) (jump_raw_data_item sq)) cbor_match_map_entry (cbor_serialized_map_iterator_next_cont sq)

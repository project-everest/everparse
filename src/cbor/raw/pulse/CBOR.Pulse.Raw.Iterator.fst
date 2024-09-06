module CBOR.Pulse.Raw.Iterator
open CBOR.Pulse.Raw.Util
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

noeq
type cbor_raw_slice_iterator (elt: Type0) = {
  s: Pulse.Lib.Slice.slice elt;
  slice_perm: perm;
  payload_perm: perm;
}

let cbor_raw_slice_iterator_match
  (#elt_low #elt_high: _)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pm: perm)
  (c: cbor_raw_slice_iterator elt_low)
  (l: list elt_high)
: Tot slprop
= exists* sq .
     Pulse.Lib.Slice.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
     PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))

```pulse
ghost
fn cbor_raw_slice_iterator_match_unfold
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pm: perm)
  (c: cbor_raw_slice_iterator elt_low)
  (l: list elt_high)
requires
  cbor_raw_slice_iterator_match elt_match pm c l
ensures
  exists* sq .
     Pulse.Lib.Slice.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
     PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm)) **
     trade
       (Pulse.Lib.Slice.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
         PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
       )
       (cbor_raw_slice_iterator_match elt_match pm c l)
{
  admit ()
}
```

inline_for_extraction
```pulse
fn cbor_raw_slice_iterator_is_empty
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (c: cbor_raw_slice_iterator elt_low)
  (#pm: perm)
  (#r: Ghost.erased (list elt_high))
requires
    cbor_raw_slice_iterator_match elt_match pm c r
returns res: bool
ensures
    cbor_raw_slice_iterator_match elt_match pm c r **
    pure (res == Nil? r)
{
  unfold (cbor_raw_slice_iterator_match elt_match pm c r);
  PM.seq_list_match_length (elt_match (pm `perm_mul` c.payload_perm)) _ _;
  Pulse.Lib.Slice.pts_to_len c.s;
  let res = (Pulse.Lib.Slice.len c.s = 0sz);
  fold (cbor_raw_slice_iterator_match elt_match pm c r);
  res
}
```

inline_for_extraction
noeq
type is_alternative (#large: Type u#a) (is: (large -> bool)) (side: bool) (small: Type u#b) = {
  get: ((x: large { is x == side }) -> small);
  set: ((x: small) -> (y: large { is y == side /\ get y == x }));
  prf: squash (forall (x: large) . is x == side ==> x == set (get x));
}

inline_for_extraction
let is_alternative_either_left
  (t1: Type u#a) (t2: Type u#b)
: Tot (is_alternative #(either t1 t2) Inl? true t1)
= {
  get = (fun x -> match x with Inl y -> y);
  set = (fun x -> Inl x);
  prf = ();
}

inline_for_extraction
let is_alternative_either_right
  (t1: Type u#a) (t2: Type u#b)
: Tot (is_alternative #(either t1 t2) Inl? false t2)
= {
  get = (fun x -> match x with Inr y -> y);
  set = (fun x -> Inr x);
  prf = ();
}

inline_for_extraction
```pulse
fn cbor_raw_slice_iterator_next'
  (#iterator #elt_low #elt_high: Type0)
  (is: (iterator -> bool))
  (side: bool)
  (alt: is_alternative is side (cbor_raw_slice_iterator elt_low))
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pi: R.ref iterator)
  (#pm: perm)
  (i:cbor_raw_slice_iterator elt_low)
  (#l: Ghost.erased (list elt_high))
requires
  exists* i0 .
    R.pts_to pi i0 **
    cbor_raw_slice_iterator_match elt_match pm i l **
    pure (Cons? l)
returns res: elt_low
ensures
  exists* a p i' q .
    elt_match p res a **
    R.pts_to pi (alt.set i') **
    cbor_raw_slice_iterator_match elt_match pm i' q **
    trade
      (elt_match p res a ** cbor_raw_slice_iterator_match elt_match pm i' q)
      (cbor_raw_slice_iterator_match elt_match pm i l) **
    pure (Ghost.reveal l == a :: q)
{
  cbor_raw_slice_iterator_match_unfold elt_match pm i l;
  PM.seq_list_match_length (elt_match (pm `perm_mul` i.payload_perm)) _ _;
  admit ()
}
```

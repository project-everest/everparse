module CBOR.Pulse.Raw.Read
include CBOR.Pulse.Raw.Match
open CBOR.Pulse.Raw.Serialized
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Trade = Pulse.Lib.Trade.Util

```pulse
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
  ghost fn aux (_: unit)
    requires emp ** (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
      cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r))
    ensures cbor_match_tagged c p r cbor_match
  {
    fold (cbor_match_tagged c p r cbor_match)
  };
  intro_trade _ _ _ aux
}
```

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

```pulse
fn cbor_match_tagged_get_payload
  (c: cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Tagged? r })
  requires cbor_match pm c r
  returns res: cbor_raw
  ensures exists* pm' .
    cbor_match pm' res (Tagged?.v r) **
    trade
      (cbor_match pm' res (Tagged?.v r))
      (cbor_match pm c r)
{
  cbor_match_cases c;
  if (CBOR_Case_Serialized_Tagged? c) {
    let cs = CBOR_Case_Serialized_Tagged?.v c;
    Trade.rewrite_with_trade
      (cbor_match pm c r)
      (cbor_match_serialized_tagged cs pm r);
    let res = cbor_match_serialized_tagged_get_payload cs;
    Trade.trans _ _ (cbor_match pm c r);
    res
  } else {
    let ct = CBOR_Case_Tagged?.v c;
    cbor_match_eq_tagged pm ct r;
    Trade.rewrite_with_trade
      (cbor_match pm c r)
      (cbor_match_tagged ct pm r cbor_match);
    cbor_match_tagged_elim ct pm r;
    Trade.trans _ _ (cbor_match pm c r);
    let res = !ct.cbor_tagged_ptr;
    Trade.elim_hyp_l _ _ (cbor_match pm c r);
    res
  }
}
```

noeq
type cbor_array_iterator =
| CBOR_Array_Iterator_Slice:
  s: Pulse.Lib.Slice.slice cbor_raw ->
  slice_perm: perm ->
  payload_perm: perm ->
  cbor_array_iterator
| CBOR_Array_Iterator_Serialized of cbor_serialized_array_iterator

let cbor_array_iterator_slice_match
  (pm: perm)
  (slice_perm: perm)
  (payload_perm: perm)
  (s: Pulse.Lib.Slice.slice cbor_raw)
  (l: list raw_data_item)
: Tot slprop
= exists* sq .
     Pulse.Lib.Slice.pts_to s #(pm `perm_mul` slice_perm) sq **
     PM.seq_list_match sq l (cbor_match (pm `perm_mul` payload_perm))

let cbor_array_iterator_match
  (pm: perm)
  (i: cbor_array_iterator)
  (l: list raw_data_item)
: Tot slprop
= match i with
  | CBOR_Array_Iterator_Slice s slice_perm payload_perm ->
    cbor_array_iterator_slice_match pm slice_perm payload_perm s l
  | CBOR_Array_Iterator_Serialized s ->
    cbor_serialized_array_iterator_match pm s l

```pulse
ghost
fn cbor_match_array_elim
  (c: cbor_array)
  (p: perm)
  (r: raw_data_item { Array? r })
  requires
    cbor_match_array c p r cbor_match
  ensures exists* s . 
    A.pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s **
    PM.seq_list_match s (Array?.v r) (cbor_match (p `perm_mul` c.cbor_array_payload_perm)) **
    trade
      (A.pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s **
        PM.seq_list_match s (Array?.v r) (cbor_match (p `perm_mul` c.cbor_array_payload_perm)))
      (cbor_match_array c p r cbor_match) **
    pure (c.cbor_array_length == Array?.len r)
{
  unfold (cbor_match_array c p r cbor_match);
  with s . assert (A.pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s);
  ghost
  fn aux (_: unit)
    requires emp ** (A.pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s **
        PM.seq_list_match s (Array?.v r) (cbor_match (p `perm_mul` c.cbor_array_payload_perm)))
    ensures cbor_match_array c p r cbor_match
  {
    fold (cbor_match_array c p r cbor_match)
  };
  Trade.intro _ _ _ aux
}
```

#set-options "--print_implicits"

```pulse
ghost
fn cbor_array_iterator_slice_match_intro
  (c': cbor_array)
  (pm: perm)
  (s: Seq.seq cbor_raw)
  (l: list raw_data_item)
  (s': Pulse.Lib.Slice.slice cbor_raw)
requires
  A.pts_to c'.cbor_array_ptr #((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) s **
  Pulse.Lib.Slice.pts_to s' #((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) s **
  PM.seq_list_match s l (cbor_match (pm `perm_mul` c'.cbor_array_payload_perm)) **
  Pulse.Lib.Slice.is_from_array c'.cbor_array_ptr ((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) s'
ensures
  cbor_array_iterator_slice_match 1.0R ((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) (pm `perm_mul` c'.cbor_array_payload_perm) s' l **
  trade
    (cbor_array_iterator_slice_match 1.0R ((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) (pm `perm_mul` c'.cbor_array_payload_perm) s' l)
    (A.pts_to c'.cbor_array_ptr #(pm `perm_mul` c'.cbor_array_array_perm) s **
      PM.seq_list_match s l (cbor_match (pm `perm_mul` c'.cbor_array_payload_perm)))
{
  fold (cbor_array_iterator_slice_match 1.0R ((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) (pm `perm_mul` c'.cbor_array_payload_perm) s' l);
  ghost
  fn aux (_: unit)
    requires
      (A.pts_to c'.cbor_array_ptr #((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) s **
        Pulse.Lib.Slice.is_from_array c'.cbor_array_ptr ((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) s') **
      cbor_array_iterator_slice_match 1.0R ((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) (pm `perm_mul` c'.cbor_array_payload_perm) s' l
    ensures
      A.pts_to c'.cbor_array_ptr #(pm `perm_mul` c'.cbor_array_array_perm) s **
      PM.seq_list_match s l (cbor_match (pm `perm_mul` c'.cbor_array_payload_perm))
  {
    unfold (cbor_array_iterator_slice_match 1.0R ((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) (pm `perm_mul` c'.cbor_array_payload_perm) s' l);
    Pulse.Lib.Slice.to_array s';
    A.gather c'.cbor_array_ptr
  };
  Trade.intro _ _ _ aux
}
```
  
```pulse
fn cbor_array_iterator_init
  (c: cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
    (cbor_match pm c r ** pure SZ.fits_u64)
returns res: cbor_array_iterator
ensures
      cbor_array_iterator_match 1.0R res (Array?.v r) **
      trade
        (cbor_array_iterator_match 1.0R res (Array?.v r))
        (cbor_match pm c r)
{
  cbor_match_cases c;
  match c {
    CBOR_Case_Serialized_Array c' -> {
      Trade.rewrite_with_trade
        (cbor_match pm c r)
        (cbor_match_serialized_array c' pm r);
      let i' = cbor_serialized_array_iterator_init c';
      Trade.trans
        (cbor_serialized_array_iterator_match 1.0R i' (Array?.v r))
        (cbor_match_serialized_array c' pm r)
        (cbor_match pm c r);
      let i = CBOR_Array_Iterator_Serialized i';
      Trade.rewrite_with_trade
        (cbor_serialized_array_iterator_match 1.0R i' (Array?.v r))
        (cbor_array_iterator_match 1.0R i (Array?.v r));
      Trade.trans
        (cbor_array_iterator_match 1.0R i (Array?.v r))
        (cbor_serialized_array_iterator_match 1.0R i' (Array?.v r))
        (cbor_match pm c r);
      i
    }
    CBOR_Case_Array c' -> {
      assert_norm (cbor_match pm (CBOR_Case_Array c') (Array (Array?.len r) (Array?.v r)) ==
        cbor_match_array c' pm (Array (Array?.len r) (Array?.v r)) cbor_match
      );
      Trade.rewrite_with_trade
        (cbor_match pm c r)
        (cbor_match_array c' pm r cbor_match);
      cbor_match_array_elim c' pm r;
      with s . assert (A.pts_to c'.cbor_array_ptr #(pm `perm_mul` c'.cbor_array_array_perm) s);
      Trade.trans
        (A.pts_to c'.cbor_array_ptr #(pm `perm_mul` c'.cbor_array_array_perm) s **
          PM.seq_list_match s (Array?.v r) (cbor_match (pm `perm_mul` c'.cbor_array_payload_perm)))
        (cbor_match_array c' pm r cbor_match)
        (cbor_match pm c r);
      A.share c'.cbor_array_ptr;
      let s' = Pulse.Lib.Slice.from_array false c'.cbor_array_ptr (SZ.uint64_to_sizet c'.cbor_array_length.value);
      cbor_array_iterator_slice_match_intro _ _ _ _ _;
      Trade.trans
        (cbor_array_iterator_slice_match _ _ _ _ _)
        _
        (cbor_match pm c r);
      let i = CBOR_Array_Iterator_Slice s' ((pm `perm_mul` c'.cbor_array_array_perm) /. 2.0R) (pm `perm_mul` c'.cbor_array_payload_perm);
      Trade.rewrite_with_trade
        (cbor_array_iterator_slice_match _ _ _ _ _)
        (cbor_array_iterator_match 1.0R i (Array?.v r));
      Trade.trans
        (cbor_array_iterator_match 1.0R i (Array?.v r))
        _
        (cbor_match pm c r);
      i
    }
  }
}
```

```pulse
fn cbor_array_iterator_is_empty
  (c: cbor_array_iterator)
  (#pm: perm)
  (#r: Ghost.erased (list raw_data_item))
requires
    cbor_array_iterator_match pm c r
returns res: bool
ensures
    cbor_array_iterator_match pm c r **
    pure (res == Nil? r)
{
  match c {
    CBOR_Array_Iterator_Serialized c' -> {
      rewrite (cbor_array_iterator_match pm c r)
        as (cbor_serialized_array_iterator_match pm c' r);
      let res = cbor_serialized_array_iterator_is_empty c';
      rewrite (cbor_serialized_array_iterator_match pm c' r)
        as (cbor_array_iterator_match pm c r);
      res
    }
    CBOR_Array_Iterator_Slice s ps pp -> {
      rewrite (cbor_array_iterator_match pm c r)
        as (cbor_array_iterator_slice_match pm ps pp s r);
      unfold (cbor_array_iterator_slice_match pm ps pp s r);
      PM.seq_list_match_length (cbor_match (pm `perm_mul` pp)) _ _;
      Pulse.Lib.Slice.pts_to_len s;
      let res = (Pulse.Lib.Slice.len s = 0sz);
      fold (cbor_array_iterator_slice_match pm ps pp s r);
      rewrite (cbor_array_iterator_slice_match pm ps pp s r)
        as (cbor_array_iterator_match pm c r);
      res
    }
  }
}
```

```pulse
fn cbor_array_iterator_next
  (pi: R.ref cbor_array_iterator)
  (#pm: perm)
  (#i: Ghost.erased cbor_array_iterator)
  (#l: Ghost.erased (list raw_data_item))
requires
    R.pts_to pi i **
    cbor_array_iterator_match pm i l **
    pure (Cons? l)
returns res: cbor_raw
ensures exists* a p i' q .
    cbor_match p res a **
    R.pts_to pi i' **
    cbor_array_iterator_match pm i' q **
    trade
      (cbor_match p res a ** cbor_array_iterator_match pm i' q)
      (cbor_array_iterator_match pm i l) **
    pure (Ghost.reveal l == a :: q)
{
  let i = !pi;
  match i {
    CBOR_Array_Iterator_Serialized i_ -> {
      let mut pi_ = i_;
      Trade.rewrite_with_trade (cbor_array_iterator_match pm i l)
        (cbor_serialized_array_iterator_match pm i_ l);
      let res = cbor_serialized_array_iterator_next pi_;
      let i'_ = !pi_;
      with q . assert (cbor_serialized_array_iterator_match pm i'_ q);
      let i' = CBOR_Array_Iterator_Serialized i'_;
      Trade.rewrite_with_trade
        (cbor_serialized_array_iterator_match pm i'_ q)
        (cbor_array_iterator_match pm i' q);
      with p a . assert (cbor_match p res a);
      Trade.reg_l
        (cbor_match p res a)
        (cbor_array_iterator_match pm i' q)
        (cbor_serialized_array_iterator_match pm i'_ q);
      Trade.trans
        (cbor_match p res a ** cbor_array_iterator_match pm i' q)
        (cbor_match p res a ** cbor_serialized_array_iterator_match pm i'_ q)
        (cbor_serialized_array_iterator_match pm i_ l);
      Trade.trans
        (cbor_match p res a ** cbor_array_iterator_match pm i' q)
        (cbor_serialized_array_iterator_match pm i_ l)
        (cbor_array_iterator_match pm i l);
      pi := i';
      res
    }
    CBOR_Array_Iterator_Slice s ps pp -> {
      admit ()
    }
  }
}
```


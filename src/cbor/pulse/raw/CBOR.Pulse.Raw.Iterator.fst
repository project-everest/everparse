module CBOR.Pulse.Raw.Iterator
include CBOR.Pulse.Raw.Iterator.Base
open CBOR.Pulse.Raw.Util
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch.Util
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.SizeT

noeq
type cbor_raw_slice_iterator (elt: Type0) = {
  s: Pulse.Lib.Slice.slice elt;
  slice_perm: perm;
  payload_perm: perm;
}

let cbor_raw_slice_iterator_match
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pm: perm)
  (c: cbor_raw_slice_iterator elt_low)
  (l: list elt_high)
: Tot slprop
= exists* sq .
     pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
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
     pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
     PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm)) **
     trade
       (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
         PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
       )
       (cbor_raw_slice_iterator_match elt_match pm c l)
{
  unfold (cbor_raw_slice_iterator_match elt_match pm c l);
  with sq . assert (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
     PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
  );
  ghost
  fn aux ()
  requires emp ** (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
         PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
       )
  ensures cbor_raw_slice_iterator_match elt_match pm c l
  {
    fold (cbor_raw_slice_iterator_match elt_match pm c l);
  };
  Trade.intro _ _ _ aux
}
```

```pulse
ghost
fn cbor_raw_slice_iterator_match_fold
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pm: perm)
  (c: cbor_raw_slice_iterator elt_low)
  (c': cbor_raw_slice_iterator elt_low { c' == { c with slice_perm = c.slice_perm /. 2.0R } })
  (l: list elt_high)
  (sq: Seq.seq elt_low)
requires
  pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
  PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
ensures
  cbor_raw_slice_iterator_match elt_match pm c' l **
     trade
       (cbor_raw_slice_iterator_match elt_match pm c' l)
       (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
         PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
       )
{
  S.share c.s;
  half_mul pm c.slice_perm;
  fold (cbor_raw_slice_iterator_match elt_match pm c' l);
  ghost
  fn aux ()
  requires (pts_to c.s #((pm `perm_mul` c.slice_perm) /. 2.0R) sq ** cbor_raw_slice_iterator_match elt_match pm c' l)
  ensures
       (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
         PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
       )
  {
    unfold (cbor_raw_slice_iterator_match elt_match pm c' l);
    S.gather c.s
  };
  Trade.intro _ _ _ aux
}
```

```pulse
ghost
fn slice_from_array_trade_aux (#t: Type0) (a: array t) (p: perm) (v: Ghost.erased (Seq.seq t)) (s: S.slice t) (_: unit)
requires
    (S.is_from_array a s ** pts_to s #p v)
ensures
    (A.pts_to a #p v)
{
  S.to_array s
}
```

inline_for_extraction
```pulse
fn slice_from_array_trade (#t: Type0) (a: array t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (alen: SZ.t {
    SZ.v alen == A.length a
})
requires
    (A.pts_to a #p v)
returns s: S.slice t
ensures
    (
        pts_to s #p v **
        trade
          (pts_to s #p v)
          (A.pts_to a #p v)
    )
{
  let s = S.from_array a alen;
  Trade.intro _ _ _ (slice_from_array_trade_aux a p v s);
  s
}
```

inline_for_extraction
```pulse
fn cbor_raw_slice_iterator_init
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (a: A.array elt_low)
  (alen: SZ.t { SZ.v alen == A.length a })
  (#pm: perm)
  (#pm': perm)
  (#l: Ghost.erased (list elt_high))
  (#sq: Ghost.erased (Seq.seq elt_low))
requires
  A.pts_to a #pm sq **
  PM.seq_list_match sq l (elt_match pm')
returns res: cbor_raw_slice_iterator elt_low
ensures exists* p .
  cbor_raw_slice_iterator_match elt_match p res l **
     trade
       (cbor_raw_slice_iterator_match elt_match p res l)
       (A.pts_to a #pm sq **
         PM.seq_list_match sq l (elt_match pm')
       )
{
  let s = slice_from_array_trade a alen;
  let c : cbor_raw_slice_iterator elt_low = {
    s = s;
    slice_perm = 1.0R;
    payload_perm = pm' `perm_div` pm;
  };
  let c' = { c with slice_perm = 0.5R };
  perm_mul_div pm pm';
  Trade.rewrite_with_trade
    (PM.seq_list_match sq l (elt_match pm'))
    (PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm)));
  Trade.prod
    (pts_to s #pm sq)
    (A.pts_to a #pm sq)
    (PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm)))
    (PM.seq_list_match sq l (elt_match pm'))
    ;
  cbor_raw_slice_iterator_match_fold elt_match pm c c' l sq;
  Trade.trans (cbor_raw_slice_iterator_match elt_match pm c' l) _ _;
  c'
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

noeq
type cbor_raw_iterator (elt: Type0) =
| CBOR_Raw_Iterator_Slice of cbor_raw_slice_iterator elt
| CBOR_Raw_Iterator_Serialized of cbor_raw_serialized_iterator

let slice_split_right_postcond
  (#t: Type) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t) (v': Seq.seq t)
: Tot prop
= SZ.v i <= Seq.length v /\
  v' == Seq.slice v (SZ.v i) (Seq.length v)


```pulse
ghost
fn slice_split_right_aux (#t: Type0) (s1: S.slice t) (p: perm) (v1: Seq.seq t) (s2: S.slice t) (v2: Seq.seq t) (i: SZ.t) (s: S.slice t) (v: Seq.seq t) (sq: squash (v == v1 `Seq.append` v2)) (_: unit)
requires
    ((S.is_split s s1 s2 ** pts_to s1 #p v1) ** pts_to s2 #p v2)
ensures
    (pts_to s #p v)
{
  S.join s1 s2 s
}
```

inline_for_extraction
```pulse
fn slice_split_right (#t: Type0) (s: S.slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires pts_to s #p v ** pure (SZ.v i <= Seq.length v)
    returns res: S.slice t
    ensures exists* v' . pts_to res #p v' **
      trade (pts_to res #p v') (pts_to s #p v) **
      pure (slice_split_right_postcond p v i v')
{
  let sp = S.split s i;
  match sp {
    Mktuple2 s1 s2 -> {
      with v1 . assert (pts_to s1 #p v1);
      with v2 . assert (pts_to s2 #p v2);
      let sq : squash (Ghost.reveal v == v1 `Seq.append` v2) = Seq.lemma_split v (SZ.v i);
      Trade.intro _ _ _ (slice_split_right_aux s1 p v1 s2 v2 i s v sq);
      s2
    }
  }
}
```

```pulse
ghost
fn trade_partial_trans
  (a b c d e: slprop)
requires
  (trade a (b ** c) ** trade (d ** c) e)
ensures
  (trade (d ** a) (e ** b))
{
  Trade.reg_l d a (b ** c);
  slprop_equivs ();
  rewrite (trade (d ** a) (d ** (b ** c))) as (trade (d ** a) ((d ** c) ** b));
  Trade.reg_r (d ** c) e b;
  Trade.trans (d ** a) ((d ** c) ** b) (e ** b)
}
```

```pulse
ghost
fn trade_partial_trans_2
  (a b c d: slprop)
requires
  (trade a (b ** c) ** trade c d)
ensures
  (trade a (b ** d))
{
  Trade.reg_l b c d;
  Trade.trans a (b ** c) (b ** d)
}
```

inline_for_extraction
```pulse
fn cbor_raw_slice_iterator_next
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pi: R.ref (cbor_raw_iterator elt_low))
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
    R.pts_to pi (CBOR_Raw_Iterator_Slice i') **
    cbor_raw_slice_iterator_match elt_match pm i' q **
    trade
      (elt_match p res a ** cbor_raw_slice_iterator_match elt_match pm i' q)
      (cbor_raw_slice_iterator_match elt_match pm i l) **
    pure (Ghost.reveal l == a :: q)
{
  cbor_raw_slice_iterator_match_unfold elt_match pm i l; // 1: (pts_to i.s _ ** PM.seq_list_match _ l _) @==> cbor_raw_slice_iterator_match elt_match pm i l
  with sq . assert (pts_to i.s #(pm `perm_mul` i.slice_perm) sq);
  PM.seq_list_match_length (elt_match (pm `perm_mul` i.payload_perm)) _ _;
  let res = Pulse.Lib.Slice.op_Array_Access i.s 0sz;
  PM.seq_list_match_cons_elim_trade _ l (elt_match (pm `perm_mul` i.payload_perm)); // 2: (elt_match _ (List.Tot.hd l) ** PM.seq_list_match _ (List.Tot.tl l) _) @==> PM.seq_list_match _ l _
//  assert (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l)); // FIXME: make this work, without the need for `rewrite ... sq`, see below
  let s' = slice_split_right i.s 1sz; // 3: pts_to s' _ @==> pts_to i.s _
  let i1 = { i with s = s' };
  let i' = { i1 with slice_perm = i.slice_perm /. 2.0R };
  pi := CBOR_Raw_Iterator_Slice i';
  cbor_raw_slice_iterator_match_fold elt_match pm i1 i' (List.Tot.tl l) _; // 4: cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l) @==> (pts_to s' _ ** PM.seq_list_match _ (List.Tot.tl l) _)
  // BEGIN FIXME: PLEASE PLEASE PLEASE automate the following steps away!
  trade_partial_trans // uses 2, 4
    (cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l))
    (pts_to s' #(pm `perm_mul` i.slice_perm) _)
    (PM.seq_list_match _ (List.Tot.tl l) (elt_match (pm `perm_mul` i.payload_perm)))
    (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l))
    (PM.seq_list_match _ l (elt_match (pm `perm_mul` i.payload_perm))); // 5: elt_match _ _ (List.Tot.hd l) ** cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l) @==> PM.seq_list_match _ l _ ** pts_to s' _
  trade_partial_trans_2 // uses 3, 5
    (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l) ** cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l))
    (PM.seq_list_match _ l (elt_match (pm `perm_mul` i.payload_perm)))
    (pts_to s' #(pm `perm_mul` i.slice_perm) _)
    (pts_to i.s #(pm `perm_mul` i.slice_perm) _); // 6: elt_match _ _ (List.Tot.hd l) ** cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l) @==> PM.seq_list_match _ l _ ** pts_to i.s _
  slprop_equivs ();
  Trade.trans
    (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l) ** cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l))
    (PM.seq_list_match _ l (elt_match (pm `perm_mul` i.payload_perm)) ** pts_to i.s #(pm `perm_mul` i.slice_perm) _)
    (cbor_raw_slice_iterator_match elt_match pm i l);
  // END FIXME
  rewrite (elt_match (pm `perm_mul` i.payload_perm) (Seq.head sq) (List.Tot.hd l)) as (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l)); // FIXME: automate this step away; it is the only occurrence of `sq`, see the `assert` above
  res
}
```

let cbor_raw_iterator_match
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (pm: perm)
  (c: cbor_raw_iterator elt_low)
  (l: list elt_high)
: Tot slprop
= match c with
  | CBOR_Raw_Iterator_Slice c' -> cbor_raw_slice_iterator_match elt_match pm c' l
  | CBOR_Raw_Iterator_Serialized c' -> ser_match pm c' l

inline_for_extraction
```pulse
fn cbor_raw_iterator_init_from_array
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (a: A.array elt_low)
  (alen: SZ.t { SZ.v alen == A.length a })
  (#pm: perm)
  (#pm': perm)
  (#l: Ghost.erased (list elt_high))
  (#sq: Ghost.erased (Seq.seq elt_low))
requires
  A.pts_to a #pm sq **
  PM.seq_list_match sq l (elt_match pm')
returns res: cbor_raw_iterator elt_low
ensures exists* p .
  cbor_raw_iterator_match elt_match ser_match p res l **
     trade
       (cbor_raw_iterator_match elt_match ser_match p res l)
       (A.pts_to a #pm sq **
         PM.seq_list_match sq l (elt_match pm')
       )
{
  let i = cbor_raw_slice_iterator_init elt_match a alen;
  with p . assert (cbor_raw_slice_iterator_match elt_match p i l);
  let res : cbor_raw_iterator elt_low = CBOR_Raw_Iterator_Slice i;
  Trade.rewrite_with_trade
    (cbor_raw_slice_iterator_match elt_match p i l)
    (cbor_raw_iterator_match elt_match ser_match p res l);
  Trade.trans (cbor_raw_iterator_match elt_match ser_match p res l) _ _;
  res
}
```

inline_for_extraction
let cbor_raw_serialized_iterator_is_empty_t
  (#elt_high: Type0)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
=
  (c: cbor_raw_serialized_iterator) ->
  (#pm: perm) ->
  (#r: Ghost.erased (list elt_high)) ->
  stt bool
    (ser_match pm c r)
    (fun res -> ser_match pm c r **
      pure (res == Nil? r)
    )

inline_for_extraction
```pulse
fn cbor_raw_iterator_is_empty
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (phi: cbor_raw_serialized_iterator_is_empty_t ser_match)
  (c: cbor_raw_iterator elt_low)
  (#pm: perm)
  (#r: Ghost.erased (list elt_high))
requires
    cbor_raw_iterator_match elt_match ser_match pm c r
returns res: bool
ensures
    cbor_raw_iterator_match elt_match ser_match pm c r **
    pure (res == Nil? r)
{
  match c {
    CBOR_Raw_Iterator_Slice c' -> {
      rewrite (cbor_raw_iterator_match elt_match ser_match pm c r)
        as (cbor_raw_slice_iterator_match elt_match pm c' r);
      let res = cbor_raw_slice_iterator_is_empty elt_match c';
      rewrite (cbor_raw_slice_iterator_match elt_match pm c' r)
        as (cbor_raw_iterator_match elt_match ser_match pm c r);
      res
    }
    CBOR_Raw_Iterator_Serialized c' -> {
      rewrite (cbor_raw_iterator_match elt_match ser_match pm c r)
        as (ser_match pm c' r);
      let res = phi c';
      rewrite (ser_match pm c' r)
        as (cbor_raw_iterator_match elt_match ser_match pm c r);
      res
    }
  }
}
```

inline_for_extraction
let cbor_raw_serialized_iterator_next_t
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
=
  (pi: R.ref (cbor_raw_iterator elt_low)) ->
  (#pm: perm) ->
  (i: cbor_raw_serialized_iterator) ->
  (#l: Ghost.erased (list elt_high)) ->
  stt elt_low
  (exists* i0 .
    R.pts_to pi i0 **
    ser_match pm i l **
    pure (Cons? l)
  )
  (fun res -> exists* a p i' q .
    elt_match p res a **
    R.pts_to pi (CBOR_Raw_Iterator_Serialized i') **
    ser_match pm i' q **
    trade
      (elt_match p res a ** ser_match pm i' q)
      (ser_match pm i l) **
    pure (Ghost.reveal l == a :: q)
  )

```pulse
ghost
fn trade_partial_trans_3
  (a b c d: slprop)
requires
  (trade (a ** b) c ** trade d b)
ensures
  (trade (a ** d) c)
{
  Trade.reg_l a d b;
  Trade.trans (a ** d) (a ** b) c
}
```

inline_for_extraction
```pulse
fn cbor_raw_iterator_next
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (phi: cbor_raw_serialized_iterator_next_t elt_match ser_match)
  (pi: R.ref (cbor_raw_iterator elt_low))
  (#pm: perm)
  (#i0: Ghost.erased (cbor_raw_iterator elt_low))
  (#l: Ghost.erased (list elt_high))
requires
    R.pts_to pi i0 **
    cbor_raw_iterator_match elt_match ser_match pm i0 l **
    pure (Cons? l)
returns res: elt_low
ensures
  exists* a p i' q .
    elt_match p res a **
    R.pts_to pi i' **
    cbor_raw_iterator_match elt_match ser_match pm i' q **
    trade
      (elt_match p res a ** cbor_raw_iterator_match elt_match ser_match pm i' q)
      (cbor_raw_iterator_match elt_match ser_match pm i0 l) **
    pure (Ghost.reveal l == a :: q)
{
  let i0 = !pi;
  match i0 {
    CBOR_Raw_Iterator_Slice i -> {
      Trade.rewrite_with_trade // FIXME: PLEASE automate this step away!
        (cbor_raw_iterator_match elt_match ser_match pm i0 l)
        (cbor_raw_slice_iterator_match elt_match pm i l);
      let res = cbor_raw_slice_iterator_next elt_match pi i;
      // BEGIN FIXME: PLEASE PLEASE PLEASE automate the following steps away!
      Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match pm i0 l);
      with p a . assert (elt_match p res a);
      with i' q . assert (cbor_raw_slice_iterator_match elt_match pm i' q);
      Trade.rewrite_with_trade
        (cbor_raw_slice_iterator_match elt_match pm i' q)
        (cbor_raw_iterator_match elt_match ser_match pm (CBOR_Raw_Iterator_Slice i') q);
      trade_partial_trans_3
        (elt_match p res a)
        (cbor_raw_slice_iterator_match elt_match pm i' q)
        (cbor_raw_iterator_match elt_match ser_match pm i0 l)
        (cbor_raw_iterator_match elt_match ser_match pm (CBOR_Raw_Iterator_Slice i') q);
      // END FIXME
      res
    }
    CBOR_Raw_Iterator_Serialized i -> {
      Trade.rewrite_with_trade // FIXME: PLEASE automate this step away!
        (cbor_raw_iterator_match elt_match ser_match pm i0 l)
        (ser_match pm i l);
      let res = phi pi i;
      // BEGIN FIXME: PLEASE PLEASE PLEASE automate the following steps away!
      Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match pm i0 l);
      with p a . assert (elt_match p res a);
      with i' q . assert (ser_match pm i' q);
      Trade.rewrite_with_trade
        (ser_match pm i' q)
        (cbor_raw_iterator_match elt_match ser_match pm (CBOR_Raw_Iterator_Serialized i') q);
      trade_partial_trans_3
        (elt_match p res a)
        (ser_match pm i' q)
        (cbor_raw_iterator_match elt_match ser_match pm i0 l)
        (cbor_raw_iterator_match elt_match ser_match pm (CBOR_Raw_Iterator_Serialized i') q);
      // END FIXME
      res
    }
  }
}
```

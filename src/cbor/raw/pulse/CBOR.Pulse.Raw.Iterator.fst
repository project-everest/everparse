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
  (#elt_low #elt_high: Type0)
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
  unfold (cbor_raw_slice_iterator_match elt_match pm c l);
  with sq . assert (Pulse.Lib.Slice.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
     PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
  );
  ghost
  fn aux ()
  requires emp ** (Pulse.Lib.Slice.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
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
  Pulse.Lib.Slice.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
  PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
ensures
  cbor_raw_slice_iterator_match elt_match pm c' l **
     trade
       (cbor_raw_slice_iterator_match elt_match pm c' l)
       (Pulse.Lib.Slice.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
         PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
       )
{
  S.share c.s;
  half_mul pm c.slice_perm;
  fold (cbor_raw_slice_iterator_match elt_match pm c' l);
  ghost
  fn aux ()
  requires (S.pts_to c.s #((pm `perm_mul` c.slice_perm) /. 2.0R) sq ** cbor_raw_slice_iterator_match elt_match pm c' l)
  ensures
       (Pulse.Lib.Slice.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
         PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
       )
  {
    unfold (cbor_raw_slice_iterator_match elt_match pm c' l);
    S.gather c.s
  };
  Trade.intro _ _ _ aux
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
type cbor_raw_iterator (elt: Type0) (ser: Type0) =
| CBOR_Raw_Iterator_Slice of cbor_raw_slice_iterator elt
| CBOR_Raw_Iterator_Serialized of ser

```pulse
ghost
fn seq_list_match_cons_elim_trade
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t' { Cons? v \/ Seq.length c > 0 })
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
requires
    (PM.seq_list_match c v item_match)
returns res: (squash (Cons? v /\ Seq.length c > 0))
ensures
    (item_match (Seq.head c) (List.Tot.hd v) **
      PM.seq_list_match (Seq.tail c) (List.Tot.tl v) item_match **
      trade
        (item_match (Seq.head c) (List.Tot.hd v) **
          PM.seq_list_match (Seq.tail c) (List.Tot.tl v) item_match
        )
        (PM.seq_list_match c v item_match)
    )
{
  PM.seq_list_match_cons_elim c v item_match;
  ghost
  fn aux ()
    requires emp **
      (item_match (Seq.head c) (List.Tot.hd v) **
          PM.seq_list_match (Seq.tail c) (List.Tot.tl v) item_match
      )
    ensures
      (PM.seq_list_match c v item_match)
  {
    Seq.cons_head_tail c;
    PM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd v) (Seq.tail c) (List.Tot.tl v) item_match
  };
  Trade.intro _ _ _ aux;
  ()
}
```

let slice_split_right_postcond
  (#t: Type) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t) (v': Seq.seq t)
: Tot prop
= SZ.v i <= Seq.length v /\
  v' == Seq.slice v (SZ.v i) (Seq.length v)

assume val slice_split_right (#t: Type) (s: S.slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t) : stt (S.slice t)
    (requires S.pts_to s #p v ** pure (S.split_precond false p v i))
    (ensures fun res -> exists* v' . S.pts_to res #p v' **
      trade (S.pts_to res #p v') (S.pts_to s #p v) **
      pure (slice_split_right_postcond p v i v')
    )

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
  (#elt_low #elt_high #ser: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (pi: R.ref (cbor_raw_iterator elt_low ser))
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
  cbor_raw_slice_iterator_match_unfold elt_match pm i l; // 1: (S.pts_to i.s _ ** PM.seq_list_match _ l _) @==> cbor_raw_slice_iterator_match elt_match pm i l
  with sq . assert (S.pts_to i.s #(pm `perm_mul` i.slice_perm) sq);
  PM.seq_list_match_length (elt_match (pm `perm_mul` i.payload_perm)) _ _;
  let res = Pulse.Lib.Slice.op_Array_Access i.s 0sz;
  seq_list_match_cons_elim_trade _ l (elt_match (pm `perm_mul` i.payload_perm)); // 2: (elt_match _ (List.Tot.hd l) ** PM.seq_list_match _ (List.Tot.tl l) _) @==> PM.seq_list_match _ l _
//  assert (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l)); // FIXME: make this work, without the need for `rewrite ... sq`, see below
  let s' = slice_split_right i.s 1sz; // 3: S.pts_to s' _ @==> S.pts_to i.s _
  let i1 = { i with s = s' };
  let i' = { i1 with slice_perm = i.slice_perm /. 2.0R };
  pi := CBOR_Raw_Iterator_Slice i';
  cbor_raw_slice_iterator_match_fold elt_match pm i1 i' (List.Tot.tl l) _; // 4: cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l) @==> (S.pts_to s' _ ** PM.seq_list_match _ (List.Tot.tl l) _)
  // BEGIN FIXME: PLEASE PLEASE PLEASE automate the following steps away!
  trade_partial_trans // uses 2, 4
    (cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l))
    (S.pts_to s' #(pm `perm_mul` i.slice_perm) _)
    (PM.seq_list_match _ (List.Tot.tl l) (elt_match (pm `perm_mul` i.payload_perm)))
    (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l))
    (PM.seq_list_match _ l (elt_match (pm `perm_mul` i.payload_perm))); // 5: elt_match _ _ (List.Tot.hd l) ** cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l) @==> PM.seq_list_match _ l _ ** S.pts_to s' _
  trade_partial_trans_2 // uses 3, 5
    (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l) ** cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l))
    (PM.seq_list_match _ l (elt_match (pm `perm_mul` i.payload_perm)))
    (S.pts_to s' #(pm `perm_mul` i.slice_perm) _)
    (S.pts_to i.s #(pm `perm_mul` i.slice_perm) _); // 6: elt_match _ _ (List.Tot.hd l) ** cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l) @==> PM.seq_list_match _ l _ ** S.pts_to i.s _
  slprop_equivs ();
  Trade.trans
    (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l) ** cbor_raw_slice_iterator_match elt_match pm i' (List.Tot.tl l))
    (PM.seq_list_match _ l (elt_match (pm `perm_mul` i.payload_perm)) ** S.pts_to i.s #(pm `perm_mul` i.slice_perm) _)
    (cbor_raw_slice_iterator_match elt_match pm i l);
  // END FIXME
  rewrite (elt_match (pm `perm_mul` i.payload_perm) (Seq.head sq) (List.Tot.hd l)) as (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l)); // FIXME: automate this step away; it is the only occurrence of `sq`, see the `assert` above
  res
}
```

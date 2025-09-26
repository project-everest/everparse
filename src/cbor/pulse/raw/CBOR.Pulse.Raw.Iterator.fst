module CBOR.Pulse.Raw.Iterator
#lang-pulse
include CBOR.Pulse.Raw.Iterator.Base
open CBOR.Pulse.Raw.Util
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch.Util
module S = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util

noeq
type cbor_raw_slice_iterator (elt: Type0) = {
  s: Pulse.Lib.Slice.slice elt;
  sq: squash (SZ.v (S.len s) < pow2 64);
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
     S.pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
     PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))

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
  intro
    (Trade.trade
      (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
        PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
      )
      (cbor_raw_slice_iterator_match elt_match pm c l)
    )
    #emp
    fn _
  {
    fold (cbor_raw_slice_iterator_match elt_match pm c l);
  };
}

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
  with _pm _sq .
    rewrite pts_to c.s #_pm _sq as pts_to c'.s #_pm sq;
  fold (cbor_raw_slice_iterator_match elt_match pm c' l);
  intro
    (Trade.trade
      (cbor_raw_slice_iterator_match elt_match pm c' l)
      (pts_to c.s #(pm `perm_mul` c.slice_perm) sq **
         PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm))
      )
    )
    #(pts_to c.s #((pm `perm_mul` c.slice_perm) /. 2.0R) sq)
    fn _
  {
    unfold (cbor_raw_slice_iterator_match elt_match pm c' l);
    with _pm _sq.
      rewrite S.pts_to c'.s #_pm (reveal _sq) as S.pts_to c.s #_pm _sq;
    S.gather c.s;
    with c v m.
      assert PM.seq_list_match #elt_low #elt_high c v m;
    rewrite each c as sq;
    ();
  };
}

inline_for_extraction
fn cbor_raw_slice_iterator_init
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (a: S.slice elt_low)
  (#pm: perm)
  (#pm': perm)
  (#l: Ghost.erased (list elt_high))
  (#sq: Ghost.erased (Seq.seq elt_low))
requires
  pts_to a #pm sq **
  PM.seq_list_match sq l (elt_match pm') **
  pure (FStar.UInt.fits (SZ.v (S.len a)) U64.n)
returns res: cbor_raw_slice_iterator elt_low
ensures exists* p .
  cbor_raw_slice_iterator_match elt_match p res l **
     trade
       (cbor_raw_slice_iterator_match elt_match p res l)
       (pts_to a #pm sq **
         PM.seq_list_match sq l (elt_match pm')
       )
{
  let c : cbor_raw_slice_iterator elt_low = {
    s = a;
    sq = ();
    slice_perm = 1.0R;
    payload_perm = pm' `perm_div` pm;
  };
  rewrite each a as c.s;
  let c' = { c with slice_perm = 0.5R };
  perm_mul_div pm pm';
  Trade.rewrite_with_trade
    (PM.seq_list_match sq l (elt_match pm'))
    (PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm)));
  Trade.reg_l
    (pts_to a #pm sq)
    (PM.seq_list_match sq l (elt_match (pm `perm_mul` c.payload_perm)))
    (PM.seq_list_match sq l (elt_match pm'))
    ;
  cbor_raw_slice_iterator_match_fold elt_match pm c c' l sq;
  Trade.trans (cbor_raw_slice_iterator_match elt_match pm c' l) _ _;
  c'
}

inline_for_extraction
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

inline_for_extraction
fn cbor_raw_slice_iterator_length
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (c: cbor_raw_slice_iterator elt_low)
  (#pm: perm)
  (#r: Ghost.erased (list elt_high))
requires
    cbor_raw_slice_iterator_match elt_match pm c r
returns res: U64.t
ensures
    cbor_raw_slice_iterator_match elt_match pm c r **
    pure (List.Tot.length r == U64.v res)
{
  unfold (cbor_raw_slice_iterator_match elt_match pm c r);
  PM.seq_list_match_length (elt_match (pm `perm_mul` c.payload_perm)) _ _;
  Pulse.Lib.Slice.pts_to_len c.s;
  let res = (SZ.sizet_to_uint64 (S.len c.s));
  fold (cbor_raw_slice_iterator_match elt_match pm c r);
  res
}

noeq
type cbor_raw_iterator (elt: Type0) =
| CBOR_Raw_Iterator_Slice of cbor_raw_slice_iterator elt
| CBOR_Raw_Iterator_Serialized of cbor_raw_serialized_iterator

let slice_split_right_postcond
  (#t: Type) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t) (v': Seq.seq t)
: Tot prop
= SZ.v i <= Seq.length v /\
  v' == Seq.slice v (SZ.v i) (Seq.length v)


inline_for_extraction
fn slice_split_right (#t: Type0) (s: S.slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires pts_to s #p v ** pure (SZ.v i <= Seq.length v)
    returns res: S.slice t
    ensures exists* v' . pts_to res #p v' **
      trade (pts_to res #p v') (pts_to s #p v) **
      pure (slice_split_right_postcond p v i v')
{
  let s1, s2 = S.split s i;
  with v1 . assert (pts_to s1 #p v1);
  with v2 . assert (pts_to s2 #p v2);
  let sq : squash (Ghost.reveal v == v1 `Seq.append` v2) = Seq.lemma_split v (SZ.v i);
  intro
    (Trade.trade
      (pts_to s2 #p v2)
      (pts_to s #p v)
    )
    #(S.is_split s s1 s2 ** pts_to s1 #p v1)
    fn _
  {
    S.join s1 s2 s
  };
  s2
}

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

inline_for_extraction
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
  S.pts_to_len i.s;
  PM.seq_list_match_length (elt_match (pm `perm_mul` i.payload_perm)) _ _;
  let res = Pulse.Lib.Slice.op_Array_Access i.s 0sz;
  PM.seq_list_match_cons_elim_trade _ l (elt_match (pm `perm_mul` i.payload_perm)); // 2: (elt_match _ (List.Tot.hd l) ** PM.seq_list_match _ (List.Tot.tl l) _) @==> PM.seq_list_match _ l _
//  assert (elt_match (pm `perm_mul` i.payload_perm) res (List.Tot.hd l)); // FIXME: make this work, without the need for `rewrite ... sq`, see below
  let s' = slice_split_right i.s 1sz; // 3: pts_to s' _ @==> pts_to i.s _
  S.pts_to_len s';
  let i1 = { i with s = s' };
  rewrite each s' as i1.s;
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
    (pts_to i1.s #(pm `perm_mul` i.slice_perm) _)
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
fn cbor_raw_iterator_init_from_slice
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (a: S.slice elt_low)
  (#pm: perm)
  (#pm': perm)
  (#l: Ghost.erased (list elt_high))
  (#sq: Ghost.erased (Seq.seq elt_low))
requires
  pts_to a #pm sq **
  PM.seq_list_match sq l (elt_match pm') **
  pure (FStar.UInt.fits (SZ.v (S.len a)) U64.n)
returns res: cbor_raw_iterator elt_low
ensures exists* p .
  cbor_raw_iterator_match elt_match ser_match p res l **
     trade
       (cbor_raw_iterator_match elt_match ser_match p res l)
       (pts_to a #pm sq **
         PM.seq_list_match sq l (elt_match pm')
       )
{
  let i = cbor_raw_slice_iterator_init elt_match a;
  with p . assert (cbor_raw_slice_iterator_match elt_match p i l);
  let res : cbor_raw_iterator elt_low = CBOR_Raw_Iterator_Slice i;
  Trade.rewrite_with_trade
    (cbor_raw_slice_iterator_match elt_match p i l)
    (cbor_raw_iterator_match elt_match ser_match p res l);
  Trade.trans (cbor_raw_iterator_match elt_match ser_match p res l) _ _;
  res
}

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

inline_for_extraction
let cbor_raw_serialized_iterator_length_t
  (#elt_high: Type0)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
=
  (c: cbor_raw_serialized_iterator) ->
  (#pm: perm) ->
  (#r: Ghost.erased (list elt_high)) ->
  stt U64.t
    (ser_match pm c r)
    (fun res -> ser_match pm c r **
      pure ((U64.v res <: nat) == List.Tot.length r)
    )

inline_for_extraction
fn cbor_raw_iterator_length
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (phi: cbor_raw_serialized_iterator_length_t ser_match)
  (c: cbor_raw_iterator elt_low)
  (#pm: perm)
  (#r: Ghost.erased (list elt_high))
requires
    cbor_raw_iterator_match elt_match ser_match pm c r
returns res: U64.t
ensures
    cbor_raw_iterator_match elt_match ser_match pm c r **
    pure ((U64.v res <: nat) == List.Tot.length r)
{
  match c {
    CBOR_Raw_Iterator_Slice c' -> {
      rewrite (cbor_raw_iterator_match elt_match ser_match pm c r)
        as (cbor_raw_slice_iterator_match elt_match pm c' r);
      let res = cbor_raw_slice_iterator_length elt_match c';
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

inline_for_extraction
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

inline_for_extraction
let cbor_raw_serialized_iterator_truncate_t
  (#elt_high: Type0)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
=
  (c: cbor_raw_serialized_iterator) ->
  (len: U64.t) ->
  (#pm: perm) ->
  (#r: Ghost.erased (list elt_high)) ->
  stt cbor_raw_serialized_iterator
    (ser_match pm c r **
      pure (U64.v len <= List.Tot.length r)
    )
    (fun res ->
      ser_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)) **
      Trade.trade
        (ser_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)))
        (ser_match pm c r)
    )

inline_for_extraction
fn cbor_raw_iterator_truncate
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (phi: cbor_raw_serialized_iterator_truncate_t ser_match)
  (c: cbor_raw_iterator elt_low)
  (len: U64.t)
  (#pm: perm)
  (#r: Ghost.erased (list elt_high))
requires
    cbor_raw_iterator_match elt_match ser_match pm c r **
    pure (U64.v len <= List.Tot.length r)
returns res: cbor_raw_iterator elt_low
ensures
    cbor_raw_iterator_match elt_match ser_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)) **
    Trade.trade
      (cbor_raw_iterator_match elt_match ser_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)))
      (cbor_raw_iterator_match elt_match ser_match pm c r)
{
  match c {
    CBOR_Raw_Iterator_Slice c' -> {
      Trade.rewrite_with_trade (cbor_raw_iterator_match elt_match ser_match pm c r)
        (cbor_raw_slice_iterator_match elt_match pm c' r);
      cbor_raw_slice_iterator_match_unfold elt_match pm c' r;
      Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match pm c r);
      with s l . assert (pts_to c'.s #(pm `perm_mul` c'.slice_perm) s ** PM.seq_list_match s l (elt_match (pm `perm_mul` c'.payload_perm)));
      S.pts_to_len c'.s;
      PM.seq_list_match_length (elt_match (pm `perm_mul` c'.payload_perm)) s l;
      Util.list_splitAt_append (U64.v len) l;
      Seq.lemma_split s (U64.v len);
      let l1l2 = Ghost.hide (List.Tot.splitAt (U64.v len) l);
      let l1 = Ghost.hide (fst l1l2);
      let l2 = Ghost.hide (snd l1l2);
      let s1 = Ghost.hide (Seq.slice s 0 (U64.v len));
      let s2 = Ghost.hide (Seq.slice s (U64.v len) (Seq.length s));
      rewrite each s as (s1 `Seq.append` s2);
      PM.seq_list_match_append_elim_trade (elt_match (pm `perm_mul` c'.payload_perm)) s1 l1 s2 l2;
      Trade.elim_hyp_r _ _ (PM.seq_list_match (s1 `Seq.append` s2) l (elt_match (pm `perm_mul` c'.payload_perm)));
      Trade.trans_hyp_r _ _ _ (cbor_raw_iterator_match elt_match ser_match pm c r);
      assume (pure (SZ.fits_u64));
      let sl1, sl2 = S.split_trade c'.s (SZ.uint64_to_sizet len);
      S.pts_to_len sl1;
      Trade.elim_hyp_r _ _ (pts_to c'.s #(pm `perm_mul` c'.slice_perm) s);
      Trade.trans_hyp_l _ _ _ (cbor_raw_iterator_match elt_match ser_match pm c r);
      let c1 = {
        s = sl1;
        sq = ();
        slice_perm = pm `perm_mul` c'.slice_perm;
        payload_perm = pm `perm_mul` c'.payload_perm;
      };
      rewrite each sl1 as c1.s;
      let c' = {
        c1 with slice_perm = c1.slice_perm /. 2.0R;
      };
      cbor_raw_slice_iterator_match_fold elt_match 1.0R c1 c' _ _;
      Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match pm c r);
      let res = CBOR_Raw_Iterator_Slice c';
      Trade.rewrite_with_trade
        (cbor_raw_slice_iterator_match elt_match 1.0R c' l1)
        (cbor_raw_iterator_match elt_match ser_match 1.0R res l1);
      Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match pm c r);
      res
    }
    CBOR_Raw_Iterator_Serialized c' -> {
      Trade.rewrite_with_trade (cbor_raw_iterator_match elt_match ser_match pm c r)
        (ser_match pm c' r);
      let sres = phi c' len;
      Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match pm c r);
      let res : cbor_raw_iterator elt_low = CBOR_Raw_Iterator_Serialized sres;
      Trade.rewrite_with_trade
        (ser_match 1.0R sres (fst (List.Tot.splitAt (U64.v len) r)))
        (cbor_raw_iterator_match elt_match ser_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)));
      Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match pm c r);
      res
    }
  }
}

ghost
fn rec cbor_raw_share_slice // TODO: reuse this proof in CBOR.Pulse.Raw.Match.Perm
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (p: perm)
  (c: Seq.seq elt_low)
  (r: list elt_high)
  (elt_share: (
    (p': perm) ->
    (c': elt_low) ->
    (r': elt_high { r' << r }) ->
    stt_ghost unit emp_inames
      (elt_match p' c' r')
      (fun _ -> elt_match (p' /. 2.0R) c' r' **
        elt_match (p' /. 2.0R) c' r'
      )
  ))
  (_: unit)
requires
  PM.seq_list_match c r (elt_match p)
ensures
  PM.seq_list_match c r (elt_match (p /. 2.0R)) **
  PM.seq_list_match c r (elt_match (p /. 2.0R))
decreases r
{
  match r {
    Nil -> {
      PM.seq_list_match_nil_elim c r (elt_match p);
      PM.seq_list_match_nil_intro c r (elt_match (p /. 2.0R));      
      PM.seq_list_match_nil_intro c r (elt_match (p /. 2.0R))
    }
    a :: q -> {
//      rewrite each r as (a :: q);
      PM.seq_list_match_cons_elim c (a :: q) (elt_match p);
//      rewrite each List.Tot.hd (a :: q) as a; // does not work
      (* ^ Why!? *)

      elt_share p (Seq.head c) _;
      cbor_raw_share_slice elt_match p (Seq.tail c) q elt_share ();
      PM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd (a :: q)) (Seq.tail c) q (elt_match (p /. 2.0R));
      PM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd (a :: q)) (Seq.tail c) q (elt_match (p /. 2.0R));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ();
    }
  }
}

inline_for_extraction
let cbor_raw_serialized_iterator_share_t
  (#elt_high: Type0)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
=
  (c: cbor_raw_serialized_iterator) ->
  (#pm: perm) ->
  (#r: (list elt_high)) ->
  stt_ghost unit emp_inames
    (ser_match pm c r)
    (fun _ ->
      ser_match (pm /. 2.0R) c r **
      ser_match (pm /. 2.0R) c r
    )

ghost
fn cbor_raw_iterator_share
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (elt_share: (
    (p': perm) ->
    (c': elt_low) ->
    (r': elt_high) ->
    stt_ghost unit emp_inames
      (elt_match p' c' r')
      (fun _ -> elt_match (p' /. 2.0R) c' r' **
        elt_match (p' /. 2.0R) c' r'
      )
  ))
  (#ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (phi: cbor_raw_serialized_iterator_share_t ser_match)
  (c: cbor_raw_iterator elt_low)
  (#pm: perm)
  (#r: (list elt_high))
requires
    cbor_raw_iterator_match elt_match ser_match pm c r
ensures
    cbor_raw_iterator_match elt_match ser_match (pm /. 2.0R) c r **
    cbor_raw_iterator_match elt_match ser_match (pm /. 2.0R) c r
{
  match c {
    CBOR_Raw_Iterator_Slice c' -> {
      rewrite (cbor_raw_iterator_match elt_match ser_match pm c r)
        as (cbor_raw_slice_iterator_match elt_match pm c' r);
      unfold (cbor_raw_slice_iterator_match elt_match pm c' r);
      with cs . assert (pts_to c'.s #(pm *. c'.slice_perm) cs);
      S.share c'.s;
      cbor_raw_share_slice elt_match (pm *. c'.payload_perm) cs r elt_share ();
      half_mul_l pm c'.slice_perm;
      half_mul_l pm c'.payload_perm;
      fold (cbor_raw_slice_iterator_match elt_match (pm /. 2.0R) c' r);
      rewrite (cbor_raw_slice_iterator_match elt_match (pm /. 2.0R) c' r)
        as (cbor_raw_iterator_match elt_match ser_match (pm /. 2.0R) c r);
      fold (cbor_raw_slice_iterator_match elt_match (pm /. 2.0R) c' r);
      rewrite (cbor_raw_slice_iterator_match elt_match (pm /. 2.0R) c' r)
        as (cbor_raw_iterator_match elt_match ser_match (pm /. 2.0R) c r);
    }
    CBOR_Raw_Iterator_Serialized c' -> {
      rewrite (cbor_raw_iterator_match elt_match ser_match pm c r)
        as (ser_match pm c' r);
      phi c';
      rewrite (ser_match (pm /. 2.0R) c' r)
        as (cbor_raw_iterator_match elt_match ser_match (pm /. 2.0R) c r);
      rewrite (ser_match (pm /. 2.0R) c' r)
        as (cbor_raw_iterator_match elt_match ser_match (pm /. 2.0R) c r);
    }
  }
}

ghost
fn rec cbor_raw_gather_slice
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (p1: perm)
  (c: Seq.seq elt_low)
  (r1: list elt_high)
  (p2: perm)
  (r2: list elt_high)
  (elt_gather: (
    (p1': perm) ->
    (c': elt_low) ->
    (r1': elt_high) ->
    (p2': perm) ->
    (r2': elt_high { r1' << r1 }) ->
    stt_ghost unit emp_inames
      (elt_match p1' c' r1' ** elt_match p2' c' r2')
      (fun _ -> elt_match (p1' +. p2') c' r1' **
        pure (r1' == r2')
      )
  ))
  (_: unit)
requires
  PM.seq_list_match c r1 (elt_match p1) **
  PM.seq_list_match c r2 (elt_match p2)
ensures
  PM.seq_list_match c r1 (elt_match (p1 +. p2)) **
  pure (r1 == r2)
decreases r1
{
  PM.seq_list_match_length (elt_match p1) c r1;
  PM.seq_list_match_length (elt_match p2) c r2;
  match r1 {
    [] -> {
      PM.seq_list_match_nil_elim c Nil (elt_match p1);
      PM.seq_list_match_nil_elim c r2 (elt_match p2);
      PM.seq_list_match_nil_intro c r1 (elt_match (p1 +. p2));
    }
    a :: q -> {
      PM.seq_list_match_cons_elim c (a :: q) (elt_match p1);
//      rewrite each List.Tot.hd (a :: q) as a; // does not work
      PM.seq_list_match_cons_elim c r2 (elt_match p2);
      elt_gather p1 (Seq.head c) (List.Tot.hd (a :: q)) p2 (List.Tot.hd r2);
      cbor_raw_gather_slice elt_match p1 (Seq.tail c) q p2 (List.Tot.tl r2) elt_gather ();
      PM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd (a :: q)) (Seq.tail c) q (elt_match (p1 +. p2));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ()
    }
  }
}

(* This is a hack to deal with ambiguity. *)

let tag (s: slprop) = s

ghost
fn cbor_raw_gather_slice_TAGGED
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (p1: perm)
  (c: Seq.seq elt_low)
  (r1: list elt_high)
  (p2: perm)
  (r2: list elt_high)
  (elt_gather: (
    (p1': perm) ->
    (c': elt_low) ->
    (r1': elt_high) ->
    (p2': perm) ->
    (r2': elt_high { r1' << r1 }) ->
    stt_ghost unit emp_inames
      (elt_match p1' c' r1' ** elt_match p2' c' r2')
      (fun _ -> elt_match (p1' +. p2') c' r1' **
        pure (r1' == r2')
      )
  ))
  (_: unit)
requires
  tag (PM.seq_list_match c r1 (elt_match p1)) **
  PM.seq_list_match c r2 (elt_match p2)
ensures
  PM.seq_list_match c r1 (elt_match (p1 +. p2)) **
  pure (r1 == r2)
{
  unfold tag;
  cbor_raw_gather_slice elt_match p1 c r1 p2 r2 elt_gather ();
}


inline_for_extraction
let cbor_raw_serialized_iterator_gather_t
  (#elt_high: Type0)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
=
  (c: cbor_raw_serialized_iterator) ->
  (#pm1: perm) ->
  (#r1: (list elt_high)) ->
  (#pm2: perm) ->
  (#r2: (list elt_high)) ->
  stt_ghost unit emp_inames
    (ser_match pm1 c r1 ** ser_match pm2 c r2)
    (fun _ ->
      ser_match (pm1 +. pm2) c r1 **
      pure (r1 == r2)
    )

ghost
fn cbor_raw_iterator_gather
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (elt_gather: (
    (p1': perm) ->
    (c': elt_low) ->
    (r1': elt_high) ->
    (p2': perm) ->
    (r2': elt_high) ->
    stt_ghost unit emp_inames
      (elt_match p1' c' r1' ** elt_match p2' c' r2')
      (fun _ -> elt_match (p1' +. p2') c' r1' **
        pure (r1' == r2')
      )
  ))
  (#ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (phi: cbor_raw_serialized_iterator_gather_t ser_match)
  (c: cbor_raw_iterator elt_low)
  (#pm1: perm)
  (#r1: (list elt_high))
  (#pm2: perm)
  (#r2: (list elt_high))
requires
    cbor_raw_iterator_match elt_match ser_match pm1 c r1 **
    cbor_raw_iterator_match elt_match ser_match pm2 c r2
ensures
    cbor_raw_iterator_match elt_match ser_match (pm1 +. pm2) c r1 **
    pure (r1 == r2)
{
  unfold (cbor_raw_iterator_match elt_match ser_match pm1 c r1);
  unfold (cbor_raw_iterator_match elt_match ser_match pm2 c r2);
  match c {
    CBOR_Raw_Iterator_Slice c' -> {
      unfold cbor_raw_slice_iterator_match elt_match pm1 c' r1;
      with gs1. assert PM.seq_list_match gs1 r1 (elt_match (perm_mul pm1 c'.payload_perm));
      rewrite PM.seq_list_match gs1 r1 (elt_match (perm_mul pm1 c'.payload_perm))
           as tag (PM.seq_list_match gs1 r1 (elt_match (perm_mul pm1 c'.payload_perm)));

      unfold cbor_raw_slice_iterator_match elt_match pm2 c' r2;
      S.gather c'.s;
      perm_mul_add_l pm1 pm2 c'.slice_perm;

      cbor_raw_gather_slice_TAGGED
        elt_match (pm1 *. c'.payload_perm) _ r1 (pm2 *. c'.payload_perm) r2 elt_gather ();
      perm_mul_add_l pm1 pm2 c'.payload_perm;
      fold (cbor_raw_slice_iterator_match elt_match (pm1 +. pm2) c' r1);
      fold (cbor_raw_iterator_match elt_match ser_match (pm1 +. pm2) (CBOR_Raw_Iterator_Slice c') r1);
    }
    CBOR_Raw_Iterator_Serialized c' -> {
      phi c' #pm1 #r1 #pm2 #r2;
      fold (cbor_raw_iterator_match elt_match ser_match (pm1 +. pm2) (CBOR_Raw_Iterator_Serialized c') r1);
    }
  }
}

let rec seq_of_list_splitAt
  (#t: Type)
  (l: list t)
  (i: nat)
: Lemma
  (requires (i <= List.Tot.length l))
  (ensures (
    i <= List.Tot.length l /\
    Seq.seq_of_list (fst (List.Tot.splitAt i l)) `Seq.equal` Seq.slice (Seq.seq_of_list l) 0 i
  ))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> if i = 0 then () else seq_of_list_splitAt q (i - 1)

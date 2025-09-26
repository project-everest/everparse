module CBOR.Pulse.Raw.Compare.Iterator
#lang-pulse
include CBOR.Pulse.Raw.Iterator
include CBOR.Pulse.Raw.Compare.Base
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Sort.Base
module SM = Pulse.Lib.SeqMatch.Util
module SZ = FStar.SizeT
module I16 = FStar.Int16
module Trade = Pulse.Lib.Trade.Util

let vmatch_with_perm
  (#high #low: Type0)
  (vmatch: perm -> low -> high -> slprop)
  (xl: with_perm low)
  (xh: high)
: Tot slprop
= vmatch xl.p xl.v xh

inline_for_extraction
fn lex_compare_iterator
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (ser_is_empty: cbor_raw_serialized_iterator_is_empty_t ser_match)
  (ser_next: cbor_raw_serialized_iterator_next_t elt_match ser_match)
  (compare: Ghost.erased (elt_high -> elt_high -> int))
  (impl_compare: A.impl_compare_t (vmatch_with_perm elt_match) compare)
: A.impl_compare_t u#0 u#0 #_ #_
    (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match))
    (lex_compare compare)
= (x1: _)
  (x2: _)
  (#v1: _)
  (#v2: _)
{
  unfold (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) x1 v1);
  unfold (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) x2 v2);
  let fin1 = cbor_raw_iterator_is_empty elt_match ser_match ser_is_empty x1.v;
  let fin2 = cbor_raw_iterator_is_empty elt_match ser_match ser_is_empty x2.v;
  if (fin1) {
    fold (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) x1 v1);
    fold (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) x2 v2);
    if (fin2) {
      0s
    } else {
      (-1s)
    }
  } else if (fin2) {
    fold (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) x1 v1);
    fold (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) x2 v2);
    1s
  } else {
    let mut pi1 = x1.v;
    let mut pi2 = x2.v;
    let mut pres = 0s;
    let mut pfin1 = false;
    Trade.refl (cbor_raw_iterator_match elt_match ser_match x1.p x1.v v1);
    Trade.refl (cbor_raw_iterator_match elt_match ser_match x2.p x2.v v2);
    while (
      let res = !pres;
      let fin1 = !pfin1;
      (res = 0s && not fin1)
    ) invariant cont . exists* i1 i2 l1 l2 fin1 res . (
      pts_to pi1 i1 ** cbor_raw_iterator_match elt_match ser_match x1.p i1 l1 **
      Trade.trade
        (cbor_raw_iterator_match elt_match ser_match x1.p i1 l1) 
        (cbor_raw_iterator_match elt_match ser_match x1.p x1.v v1) **
      pts_to pi2 i2 ** cbor_raw_iterator_match elt_match ser_match x2.p i2 l2 **
      Trade.trade
        (cbor_raw_iterator_match elt_match ser_match x2.p i2 l2) 
        (cbor_raw_iterator_match elt_match ser_match x2.p x2.v v2) **
      pts_to pres res **
      pts_to pfin1 fin1 **
      pure (
        same_sign (lex_compare compare v1 v2) (if res = 0s then lex_compare compare l1 l2 else I16.v res) /\
        (res == 0s ==> (Nil? l1 == Nil? l2 /\ fin1 == Nil? l1)) /\
        cont == (res = 0s && Cons? l1)
      )
    ) {
      let elt1 = cbor_raw_iterator_next elt_match ser_match ser_next pi1;
      Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match x1.p x1.v v1);
      let elt2 = cbor_raw_iterator_next elt_match ser_match ser_next pi2;
      Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match x2.p x2.v v2);
      with p1 hd1 . assert (elt_match p1 elt1 hd1);
      let pelt1 = Mkwith_perm elt1 p1;
      Trade.rewrite_with_trade
        (elt_match p1 elt1 hd1)
        (vmatch_with_perm elt_match pelt1 hd1);
      Trade.trans_hyp_l (vmatch_with_perm elt_match pelt1 hd1) _ _ (cbor_raw_iterator_match elt_match ser_match x1.p x1.v v1);
      with p2 hd2 . assert (elt_match p2 elt2 hd2);
      let pelt2 = Mkwith_perm elt2 p2;
      Trade.rewrite_with_trade
        (elt_match p2 elt2 hd2)
        (vmatch_with_perm elt_match pelt2 hd2);
      Trade.trans_hyp_l (vmatch_with_perm elt_match pelt2 hd2) _ _ (cbor_raw_iterator_match elt_match ser_match x2.p x2.v v2);
      let c = impl_compare pelt1 pelt2;
      Trade.elim_hyp_l _ _ (cbor_raw_iterator_match elt_match ser_match x1.p x1.v v1);
      Trade.elim_hyp_l _ _ (cbor_raw_iterator_match elt_match ser_match x2.p x2.v v2);
      if (c = 0s) {
        with gi1 l1 . assert (pts_to pi1 gi1 ** cbor_raw_iterator_match elt_match ser_match x1.p gi1 l1);
        let i1 = !pi1;
        Trade.rewrite_with_trade
          (cbor_raw_iterator_match elt_match ser_match x1.p gi1 l1)
          (cbor_raw_iterator_match elt_match ser_match x1.p i1 l1);
        Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match x1.p x1.v v1);
        let fin1 = cbor_raw_iterator_is_empty elt_match ser_match ser_is_empty i1;
        with gi2 l2 . assert (pts_to pi2 gi2 ** cbor_raw_iterator_match elt_match ser_match x2.p gi2 l2);
        let i2 = !pi2;
        Trade.rewrite_with_trade
          (cbor_raw_iterator_match elt_match ser_match x2.p gi2 l2)
          (cbor_raw_iterator_match elt_match ser_match x2.p i2 l2);
        Trade.trans _ _ (cbor_raw_iterator_match elt_match ser_match x2.p x2.v v2);
        let fin2 = cbor_raw_iterator_is_empty elt_match ser_match ser_is_empty i2;
        if (fin1 = fin2) {
          pfin1 := fin1;
        } else if (fin1) {
          pres := (-1s);
        } else {
          pres := 1s;
        }
      } else {
        pres := c
      }
    };
    Trade.elim _ (cbor_raw_iterator_match elt_match ser_match x1.p x1.v v1);
    Trade.elim _ (cbor_raw_iterator_match elt_match ser_match x2.p x2.v v2);
    fold (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) x1 v1);
    fold (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) x2 v2);
    !pres
  }
}

#push-options "--print_implicits"

inline_for_extraction
fn lex_compare_iterator_peel_perm
  (#elt_low #elt_high: Type0)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (ser_match: perm -> cbor_raw_serialized_iterator -> list elt_high -> slprop)
  (ser_is_empty: cbor_raw_serialized_iterator_is_empty_t ser_match)
  (ser_next: cbor_raw_serialized_iterator_next_t elt_match ser_match)
  (compare: Ghost.erased (elt_high -> elt_high -> int))
  (impl_compare: A.impl_compare_t (vmatch_with_perm elt_match) compare)
  (x1: cbor_raw_iterator elt_low)
  (x2: cbor_raw_iterator elt_low)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased (list elt_high))
  (#v2: Ghost.erased (list elt_high))
requires
  cbor_raw_iterator_match elt_match ser_match p1 x1 v1 **
  cbor_raw_iterator_match elt_match ser_match p2 x2 v2
returns res: I16.t
ensures
  cbor_raw_iterator_match elt_match ser_match p1 x1 v1 **
  cbor_raw_iterator_match elt_match ser_match p2 x2 v2 **
  pure (same_sign (I16.v res) (lex_compare compare v1 v2))
{
  let pl1 = Mkwith_perm x1 p1;
  Trade.rewrite_with_trade
    (cbor_raw_iterator_match elt_match ser_match p1 x1 v1)
    (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) pl1 v1);
  let pl2 = Mkwith_perm x2 p2;
  Trade.rewrite_with_trade
    (cbor_raw_iterator_match elt_match ser_match p2 x2 v2)
    (vmatch_with_perm (cbor_raw_iterator_match elt_match ser_match) pl2 v2);
  let res = lex_compare_iterator elt_match ser_match ser_is_empty ser_next compare impl_compare pl1 pl2;
  Trade.elim _ (cbor_raw_iterator_match elt_match ser_match p1 x1 v1);
  Trade.elim _ (cbor_raw_iterator_match elt_match ser_match p2 x2 v2);
  res
}

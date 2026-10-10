module CBOR.Pulse.Raw.Read
#lang-pulse
include CBOR.Pulse.Raw.Match
open CBOR.Pulse.Raw.Iterator
open CBOR.Pulse.Raw.Format.Serialized
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch.Util
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Trade = Pulse.Lib.Trade.Util
module Perm = CBOR.Pulse.Raw.Match.Perm

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
  match c {
    norewrite
    CBOR_Case_Serialized_Tagged cs -> {
      Trade.rewrite_with_trade
        (cbor_match pm c r)
        (cbor_match_serialized_tagged cs pm r);
      let res = cbor_match_serialized_tagged_get_payload cs;
      Trade.trans _ _ (cbor_match pm c r);
      res
    }
    norewrite
    CBOR_Case_Tagged ct -> {
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
}

ghost
fn cbor_match_array_elim
  (c: cbor_array)
  (p: perm)
  (r: raw_data_item { Array? r })
  requires
    cbor_match_array c p r cbor_match
  ensures exists* s . 
    pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s **
    PM.seq_list_match s (Array?.v r) (cbor_match (p `perm_mul` c.cbor_array_payload_perm)) **
    trade
      (pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s **
        PM.seq_list_match s (Array?.v r) (cbor_match (p `perm_mul` c.cbor_array_payload_perm)))
      (cbor_match_array c p r cbor_match) **
    pure (c.cbor_array_length_size == (Array?.len r).size /\
      SZ.v (S.len c.cbor_array_ptr) == U64.v (Array?.len r).value
    )
{
  unfold (cbor_match_array c p r cbor_match);
  with s . assert (pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s);
  intro
    (Trade.trade
      (pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_array_perm) s **
        PM.seq_list_match s (Array?.v r) (cbor_match (p `perm_mul` c.cbor_array_payload_perm))
      )
      (cbor_match_array c p r cbor_match)
    )
    #emp
    fn _
  {
    fold (cbor_match_array c p r cbor_match)
  };
}

fn cbor_array_item
  (c: cbor_raw)
  (i: U64.t)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
    (cbor_match pm c r **
      pure (U64.v i < List.Tot.length (Array?.v r))
    )
returns res: cbor_raw
ensures exists* p' y .
      cbor_match p' res y **
      trade
        (cbor_match p' res y)
        (cbor_match pm c r) **
      pure (
        U64.v i < List.Tot.length (Array?.v r) /\
        List.Tot.index (Array?.v r) (U64.v i) == y
      )
{
  cbor_match_cases c;
  match c {
    norewrite
    CBOR_Case_Serialized_Array c' -> {
      Trade.rewrite_with_trade
        (cbor_match pm c r)
        (cbor_match_serialized_array c' pm r);
      let res = cbor_serialized_array_item c' i;
      Trade.trans _ _ (cbor_match pm c r);
      res
    }
    norewrite
    CBOR_Case_Array c' -> { 
      assert_norm (cbor_match pm (CBOR_Case_Array c') (Array (Array?.len r) (Array?.v r)) ==
        cbor_match_array c' pm (Array (Array?.len r) (Array?.v r)) cbor_match
      );
      Trade.rewrite_with_trade
        (cbor_match pm c r)
        (cbor_match_array c' pm r cbor_match);
      cbor_match_array_elim c' pm r;
      Trade.trans _ _ (cbor_match pm c r);
      S.pts_to_len c'.cbor_array_ptr;
      PM.seq_list_match_length (cbor_match (pm `perm_mul` c'.cbor_array_payload_perm)) _ _;
      let res = S.op_Dot_Lparen_Rparen c'.cbor_array_ptr (SZ.uint64_to_sizet i);
      Trade.elim_hyp_l _ _ (cbor_match pm c r);
      PM.seq_list_match_index_trade (cbor_match (pm `perm_mul` c'.cbor_array_payload_perm)) _ _ (U64.v i);
      Trade.trans _ _ (cbor_match pm c r);
      rewrite each (U64.v i) as (SZ.v (SZ.uint64_to_sizet i));
      res
    }
  }
}

// type annotation necessary, because without it, in CBOR.Pulse.Raw.Nondet.Compare.cbor_nondet_equiv_body, Pulse
// will infer (Ghost.reveal #(CBOR.Pulse.Raw.Iterator.cbor_raw_iterator cbor_raw) ...) in the hypotheses and (Ghost.reveal #cbor_array_iterator _)
// in the conclusion, and then will not be able to match properly and will complain about ambiguity
let cbor_array_iterator_match : perm -> cbor_array_iterator -> list raw_data_item -> slprop
= cbor_raw_iterator_match
    cbor_match
    cbor_serialized_array_iterator_match

fn cbor_array_iterator_init
  (c: cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
    (cbor_match pm c r)
returns res: cbor_array_iterator
ensures exists* p .
      cbor_array_iterator_match p res (Array?.v r) **
      trade
        (cbor_array_iterator_match p res (Array?.v r))
        (cbor_match pm c r)
{
  cbor_match_cases c;
  match c {
    norewrite
    CBOR_Case_Serialized_Array c' -> {
      Trade.rewrite_with_trade
        (cbor_match pm c r)
        (cbor_match_serialized_array c' pm r);
      let i' = cbor_serialized_array_iterator_init c';
      with p . assert (cbor_serialized_array_iterator_match p i' (Array?.v r));
      Trade.trans
        (cbor_serialized_array_iterator_match p i' (Array?.v r))
        (cbor_match_serialized_array c' pm r)
        (cbor_match pm c r);
      let i : cbor_array_iterator = CBOR_Raw_Iterator_Serialized i';
      Trade.rewrite_with_trade
        (cbor_serialized_array_iterator_match p i' (Array?.v r))
        (cbor_array_iterator_match p i (Array?.v r));
      Trade.trans
        (cbor_array_iterator_match p i (Array?.v r))
        (cbor_serialized_array_iterator_match p i' (Array?.v r))
        (cbor_match pm c r);
      i
    }
    norewrite
    CBOR_Case_Array c' -> {
      assert_norm (cbor_match pm (CBOR_Case_Array c') (Array (Array?.len r) (Array?.v r)) ==
        cbor_match_array c' pm (Array (Array?.len r) (Array?.v r)) cbor_match
      );
      Trade.rewrite_with_trade
        (cbor_match pm c r)
        (cbor_match_array c' pm r cbor_match);
      cbor_match_array_elim c' pm r;
      Trade.trans _ _ (cbor_match pm c r);
      let res = cbor_raw_iterator_init_from_slice cbor_match cbor_serialized_array_iterator_match c'.cbor_array_ptr;
      with p _post.
        rewrite trade (cbor_raw_iterator_match cbor_match cbor_serialized_array_iterator_match p res (Array?.v r)) _post
             as trade (cbor_array_iterator_match p res (Array?.v r)) _post;
      Trade.trans _ _ (cbor_match pm c r);
      with p . assert (cbor_raw_iterator_match cbor_match cbor_serialized_array_iterator_match p res (Array?.v r));
      fold (cbor_array_iterator_match p res (Array?.v r));
      res
    }
  }
}

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
  unfold (cbor_array_iterator_match pm c r);
  let res = cbor_raw_iterator_is_empty
    cbor_match
    cbor_serialized_array_iterator_match
    cbor_serialized_array_iterator_is_empty
    c;
  fold (cbor_array_iterator_match pm c r);
  res
}

fn cbor_array_iterator_length
  (c: cbor_array_iterator)
  (#pm: perm)
  (#r: Ghost.erased (list raw_data_item))
requires
    cbor_array_iterator_match pm c r
returns res: U64.t
ensures
    cbor_array_iterator_match pm c r **
    pure ((U64.v res <: nat) == List.Tot.length r)
{
  unfold (cbor_array_iterator_match pm c r);
  let res = cbor_raw_iterator_length
    cbor_match
    cbor_serialized_array_iterator_match
    cbor_serialized_array_iterator_length
    c;
  fold (cbor_array_iterator_match pm c r);
  res
}

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
  unfold (cbor_array_iterator_match pm i l);
  let res = cbor_raw_iterator_next
    cbor_match
    cbor_serialized_array_iterator_match
    (cbor_serialized_array_iterator_next ())
    pi;
  with i'. assert (R.pts_to pi i');
  with l' . rewrite cbor_raw_iterator_match #cbor_raw
      #raw_data_item
      cbor_match
      cbor_serialized_array_iterator_match
      pm
      i'
      l'
    as
    cbor_raw_iterator_match #cbor_raw
      #raw_data_item
      cbor_match
      cbor_serialized_array_iterator_match
      pm
      i'
      (List.Tot.Base.tl l)
  ;
  fold (cbor_array_iterator_match pm i' (List.Tot.tl l));
  with _pre1 _pre2 _post.
    rewrite trade (_pre1 ** _pre2) _post
         as trade (_pre1 ** cbor_array_iterator_match pm
          (reveal u#0 #(cbor_raw_iterator cbor_raw) i')
          (List.Tot.Base.tl u#0
              #raw_data_item
              (reveal u#0 #(list u#0 raw_data_item) l))) (cbor_array_iterator_match pm i l);
  res
}

fn cbor_array_iterator_truncate
  (c: cbor_array_iterator)
  (len: U64.t)
  (#pm: perm)
  (#r: Ghost.erased (list raw_data_item))
requires
    cbor_array_iterator_match pm c r **
    pure (U64.v len <= List.Tot.length r)
returns res: cbor_array_iterator
ensures
    cbor_array_iterator_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)) **
    Trade.trade
      (cbor_array_iterator_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)))
      (cbor_array_iterator_match pm c r)
{
  unfold (cbor_array_iterator_match pm c r);
  let res = cbor_raw_iterator_truncate
    cbor_match
    cbor_serialized_array_iterator_match
    cbor_serialized_array_iterator_truncate
    c
    len;
  fold (cbor_array_iterator_match 1.0R res (fst (List.Tot.splitAt (U64.v len) r)));
  rewrite
    trade (cbor_raw_iterator_match cbor_match
          cbor_serialized_array_iterator_match
          1.0R
          res
          (fst (List.Tot.Base.splitAt (U64.v len) r)))
      (cbor_raw_iterator_match cbor_match
          cbor_serialized_array_iterator_match
          pm
          c
          r)
  as trade (cbor_array_iterator_match 1.0R
          res
          (fst (List.Tot.Base.splitAt (U64.v len) r)))
      (cbor_array_iterator_match pm c r)
    ;
  res
}

ghost
fn cbor_array_iterator_share
  (c: cbor_array_iterator)
  (#pm: perm)
  (#r: (list raw_data_item))
requires
    cbor_array_iterator_match pm c r
ensures
    cbor_array_iterator_match (pm /. 2.0R) c r **
    cbor_array_iterator_match (pm /. 2.0R) c r
{
  unfold (cbor_array_iterator_match pm c r);
  cbor_raw_iterator_share
    cbor_match
    Perm.cbor_raw_share
    cbor_serialized_array_iterator_share
    c;
  fold (cbor_array_iterator_match (pm /. 2.0R) c r);
  fold (cbor_array_iterator_match (pm /. 2.0R) c r);
}

ghost
fn cbor_array_iterator_gather
  (c: cbor_array_iterator)
  (#pm1: perm)
  (#r1: (list raw_data_item))
  (#pm2: perm)
  (#r2: (list raw_data_item))
requires
    cbor_array_iterator_match pm1 c r1 **
    cbor_array_iterator_match pm2 c r2
ensures
    cbor_array_iterator_match (pm1 +. pm2) c r1 **
    pure (r1 == r2)
{
  unfold (cbor_array_iterator_match pm1 c r1);
  unfold (cbor_array_iterator_match pm2 c r2);
  cbor_raw_iterator_gather
    cbor_match
    Perm.cbor_raw_gather
    cbor_serialized_array_iterator_gather
    c
    #pm1 #r1 #pm2 #r2;
  fold (cbor_array_iterator_match (pm1 +. pm2) c r1);
}

ghost
fn cbor_match_map_elim
  (c: cbor_map)
  (p: perm)
  (r: raw_data_item { Map? r })
  requires
    cbor_match_map p c r
  ensures exists* s . 
    pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) s **
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry (p `perm_mul` c.cbor_map_payload_perm)) **
    trade
      (pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) s **
        PM.seq_list_match s (Map?.v r) (cbor_match_map_entry (p `perm_mul` c.cbor_map_payload_perm)))
      (cbor_match_map p c r) **
    pure (c.cbor_map_length_size == (Map?.len r).size /\
      SZ.v (S.len c.cbor_map_ptr) == U64.v (Map?.len r).value
    )
{
  unfold (cbor_match_map p c r);
  with s . assert (pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) s);
  intro
    (Trade.trade
      (pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_array_perm) s **
        PM.seq_list_match s (Map?.v r) (cbor_match_map_entry (p `perm_mul` c.cbor_map_payload_perm))
      )
      (cbor_match_map p c r)
    )
    #emp
    fn _
  {
    fold (cbor_match_map p c r)
  };
}

// see cbor_array_iterator_match for why the annotation is necessary
let cbor_map_iterator_match : perm -> cbor_map_iterator -> list (raw_data_item & raw_data_item) -> slprop
= cbor_raw_iterator_match
    cbor_match_map_entry
    cbor_serialized_map_iterator_match

fn cbor_map_iterator_init
  (c: cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
requires
    (cbor_match pm c r)
returns res: cbor_map_iterator
ensures exists* p .
      cbor_map_iterator_match p res (Map?.v r) **
      trade
        (cbor_map_iterator_match p res (Map?.v r))
        (cbor_match pm c r)
{
  cbor_match_cases c;
  match c {
    norewrite
    CBOR_Case_Serialized_Map c' -> {
      Trade.rewrite_with_trade
        (cbor_match pm c r)
        (cbor_match_serialized_map c' pm r);
      let i' = cbor_serialized_map_iterator_init c';
      with p . assert (cbor_serialized_map_iterator_match p i' (Map?.v r));
      Trade.trans
        (cbor_serialized_map_iterator_match p i' (Map?.v r))
        (cbor_match_serialized_map c' pm r)
        (cbor_match pm c r);
      let i : cbor_map_iterator = CBOR_Raw_Iterator_Serialized i';
      Trade.rewrite_with_trade
        (cbor_serialized_map_iterator_match p i' (Map?.v r))
        (cbor_map_iterator_match p i (Map?.v r));
      Trade.trans
        (cbor_map_iterator_match p i (Map?.v r))
        (cbor_serialized_map_iterator_match p i' (Map?.v r))
        (cbor_match pm c r);
      i
    }
    norewrite
    CBOR_Case_Map c' -> {
      assert_norm (cbor_match pm (CBOR_Case_Map c') (Map (Map?.len r) (Map?.v r)) ==
        cbor_match_map0 c' pm (Map (Map?.len r) (Map?.v r)) cbor_match
      );
      Trade.rewrite_with_trade
        (cbor_match pm c r)
        (cbor_match_map0 c' pm r cbor_match);
      cbor_match_map0_map_trade c' pm r;
      Trade.trans _ _ (cbor_match pm c r);
      cbor_match_map_elim c' pm r;
      with s . assert (pts_to c'.cbor_map_ptr #(pm `perm_mul` c'.cbor_map_array_perm) s);
      Trade.trans
        (pts_to c'.cbor_map_ptr #(pm `perm_mul` c'.cbor_map_array_perm) s **
          PM.seq_list_match s (Map?.v r) (cbor_match_map_entry (pm `perm_mul` c'.cbor_map_payload_perm)))
        (cbor_match_map pm c' r)
        (cbor_match pm c r);
      let res = cbor_raw_iterator_init_from_slice cbor_match_map_entry cbor_serialized_map_iterator_match c'.cbor_map_ptr;
      Trade.trans _ _ (cbor_match pm c r);
      with p . assert (cbor_raw_iterator_match cbor_match_map_entry cbor_serialized_map_iterator_match p res (Map?.v r));
      fold (cbor_map_iterator_match p res (Map?.v r));
      with _p . rewrite
        trade (cbor_raw_iterator_match cbor_match_map_entry
              cbor_serialized_map_iterator_match
              _p
              res
              (Map?.v r))
          (cbor_match pm c r)
        as trade (cbor_map_iterator_match _p res (Map?.v r)) (cbor_match pm c r)
        ;
      res
    }
  }
}

fn cbor_map_iterator_is_empty
  (c: cbor_map_iterator)
  (#pm: perm)
  (#r: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
    cbor_map_iterator_match pm c r
returns res: bool
ensures
    cbor_map_iterator_match pm c r **
    pure (res == Nil? r)
{
  unfold (cbor_map_iterator_match pm c r);
  let res = cbor_raw_iterator_is_empty
    cbor_match_map_entry
    cbor_serialized_map_iterator_match
    cbor_serialized_map_iterator_is_empty
    c;
  fold (cbor_map_iterator_match pm c r);
  res
}

fn cbor_map_iterator_next
  (pi: R.ref cbor_map_iterator)
  (#pm: perm)
  (#i: Ghost.erased cbor_map_iterator)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
    R.pts_to pi i **
    cbor_map_iterator_match pm i l **
    pure (Cons? l)
returns res: cbor_map_entry
ensures exists* a p i' q .
    cbor_match_map_entry p res a **
    R.pts_to pi i' **
    cbor_map_iterator_match pm i' q **
    trade
      (cbor_match_map_entry p res a ** cbor_map_iterator_match pm i' q)
      (cbor_map_iterator_match pm i l) **
    pure (Ghost.reveal l == a :: q)
{
  unfold (cbor_map_iterator_match pm i l);
  let res = cbor_raw_iterator_next
    cbor_match_map_entry
    cbor_serialized_map_iterator_match
    (cbor_serialized_map_iterator_next ())
    pi;
  with i' . assert (R.pts_to pi i');
  with l' . rewrite cbor_raw_iterator_match #cbor_map_entry
      #(raw_data_item & raw_data_item)
      cbor_match_map_entry
      cbor_serialized_map_iterator_match
      pm
      (reveal u#0 #(cbor_raw_iterator cbor_map_entry) i')
      l' as cbor_raw_iterator_match #cbor_map_entry
      #(raw_data_item & raw_data_item)
      cbor_match_map_entry
      cbor_serialized_map_iterator_match
      pm
      (reveal u#0 #(cbor_raw_iterator cbor_map_entry) i')
      (List.Tot.Base.tl u#0
          #(raw_data_item & raw_data_item)
          (reveal u#0 #(list u#0 (raw_data_item & raw_data_item)) l));
  fold (cbor_map_iterator_match pm i' (List.Tot.tl l));
  with p a q . rewrite
    trade #emp_inames
      (cbor_match_map_entry p
          res
          a **
        cbor_raw_iterator_match #cbor_map_entry
          #(raw_data_item & raw_data_item)
          cbor_match_map_entry
          cbor_serialized_map_iterator_match
          pm
          (reveal u#0 #(cbor_raw_iterator cbor_map_entry) i')
          q)
      (cbor_raw_iterator_match #cbor_map_entry
          #(raw_data_item & raw_data_item)
          cbor_match_map_entry
          cbor_serialized_map_iterator_match
          pm
          (reveal u#0 #(cbor_raw_iterator cbor_map_entry) i)
          (reveal u#0 #(list u#0 (raw_data_item & raw_data_item)) l))
    as  trade #emp_inames
      (cbor_match_map_entry p
          res
          a **
        cbor_map_iterator_match pm
          (reveal u#0 #(cbor_raw_iterator cbor_map_entry) i')
          (List.Tot.Base.tl u#0
              #(raw_data_item & raw_data_item)
              (reveal u#0 #(list u#0 (raw_data_item & raw_data_item)) l)))
      (cbor_map_iterator_match pm
          (reveal u#0 #cbor_map_iterator i)
          (reveal u#0 #(list u#0 (raw_data_item & raw_data_item)) l));
  res
}

ghost
fn cbor_map_entry_share
  (p: perm)
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item))
requires
  (
    cbor_match_map_entry p c r
  )
ensures
  (
    cbor_match_map_entry (p /. 2.0R) c r **
    cbor_match_map_entry (p /. 2.0R) c r
  )
{
  unfold (cbor_match_map_entry p c r);
  Perm.cbor_raw_share _ c.cbor_map_entry_key _;
  Perm.cbor_raw_share _ c.cbor_map_entry_value _;
  fold (cbor_match_map_entry (p /. 2.0R) c r);
  fold (cbor_match_map_entry (p /. 2.0R) c r);
}

ghost
fn cbor_map_entry_gather
  (p1: perm)
  (c: cbor_map_entry)
  (r1: (raw_data_item & raw_data_item))
  (p2: perm)
  (r2: (raw_data_item & raw_data_item))
requires
  (
    cbor_match_map_entry p1 c r1 **
    cbor_match_map_entry p2 c r2
  )
ensures
  (
    cbor_match_map_entry (p1 +. p2) c r1 **
    pure (r1 == r2)
  )
{
  unfold (cbor_match_map_entry p1 c r1);
  unfold (cbor_match_map_entry p2 c r2);
  Perm.cbor_raw_gather p1 c.cbor_map_entry_key _ p2 _;
  Perm.cbor_raw_gather p1 c.cbor_map_entry_value _ p2 _;
  fold (cbor_match_map_entry (p1 +. p2) c r1);
}

ghost
fn cbor_map_iterator_share
  (c: cbor_map_iterator)
  (#pm: perm)
  (#r: (list (raw_data_item & raw_data_item)))
requires
    cbor_map_iterator_match pm c r
ensures
    cbor_map_iterator_match (pm /. 2.0R) c r **
    cbor_map_iterator_match (pm /. 2.0R) c r
{
  unfold (cbor_map_iterator_match pm c r);
  cbor_raw_iterator_share
    cbor_match_map_entry
    cbor_map_entry_share
    cbor_serialized_map_iterator_share
    c;
  fold (cbor_map_iterator_match (pm /. 2.0R) c r);
  fold (cbor_map_iterator_match (pm /. 2.0R) c r);
}

ghost
fn cbor_map_iterator_gather
  (c: cbor_map_iterator)
  (#pm1: perm)
  (#r1: (list (raw_data_item & raw_data_item)))
  (#pm2: perm)
  (#r2: (list (raw_data_item & raw_data_item)))
requires
    cbor_map_iterator_match pm1 c r1 **
    cbor_map_iterator_match pm2 c r2
ensures
    cbor_map_iterator_match (pm1 +. pm2) c r1 **
    pure (r1 == r2)
{
  unfold (cbor_map_iterator_match pm1 c r1);
  unfold (cbor_map_iterator_match pm2 c r2);
  cbor_raw_iterator_gather
    cbor_match_map_entry
    cbor_map_entry_gather
    cbor_serialized_map_iterator_gather
    c
    #pm1 #r1 #pm2 #r2;
  fold (cbor_map_iterator_match (pm1 +. pm2) c r1);
}

///////////////////////////////////////////////////////////////////////////////
// DEPTH-AWARE ITERATORS (Stage A)
//
// Below we build depth-indexed analogues of the array/map iterators above,
// using the depth toolkit from CBOR.Pulse.Raw.Match. The seq_list_match
// element-predicate converters mirror those proven in CBOR.Pulse.Raw.Copy
// (which is downstream of this module, so they are replicated here).
///////////////////////////////////////////////////////////////////////////////

// Expose the constructor/case relationship while preserving the depth predicate.
ghost
fn cbor_match_with_depth_cases (n: nat) (p: perm) (c: cbor_raw) (r: raw_data_item)
  requires cbor_match_with_depth n p c r
  ensures cbor_match_with_depth n p c r ** pure (cbor_match_cases_pred c r)
{
  cbor_match_with_depth_eq0 n p c r;
  rewrite (cbor_match_with_depth n p c r) as (cbor_match0 p c r (depth_cb n r));
  cbor_match0_cases p c r (depth_cb n r);
  rewrite (cbor_match0 p c r (depth_cb n r)) as (cbor_match_with_depth n p c r);
}

// ===== array element-predicate conversions =====
// The depth-array elim yields a seq_list_match whose element predicate is the
// REFINED depth callback [(depth_cb depth r) pl : cbor_raw -> (v'{v'<<r}) -> slprop].
// The generic iterator machinery needs an UNREFINED predicate, so we convert it
// to [cbor_match_with_depth (nat_pred depth) pl] (and back, via a trade).

// Peek the head (if any) to learn that a non-empty container forces depth >= 1.
ghost
fn array_peek
  (depth: Ghost.erased nat)
  (r: raw_data_item { Array? r })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)
ensures
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl) **
    pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  if (Cons? (Array?.v r)) {
    PM.seq_list_match_cons_elim_trade s (Array?.v r) ((depth_cb d r) pl);
    depth_cb_pos d r pl (Seq.head s) (List.Tot.hd (Array?.v r));
    Trade.elim _ (PM.seq_list_match s (Array?.v r) ((depth_cb d r) pl));
  } else {
    ()
  }
}

ghost
fn array_to_unref
  (depth: Ghost.erased nat)
  (r: raw_data_item { Array? r })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)
ensures
    PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  array_peek depth r pl s;
  ghost fn prf
    (c': cbor_raw)
    (v': raw_data_item { v' << Array?.v r /\ List.Tot.memP v' (Array?.v r) })
    requires (depth_cb d r) pl c' v'
    ensures cbor_match_with_depth (nat_pred d) pl c' v'
  {
    depth_cb_pos d r pl c' v';
    depth_cb_succ d r pl c' v';
    nat_pred_succ d;
    rewrite ((depth_cb d r) pl c' v')
      as (cbor_match_with_depth (nat_pred d) pl c' v');
  };
  seq_list_match_conv s (Array?.v r)
    ((depth_cb d r) pl)
    (cbor_match_with_depth (nat_pred d) pl)
    prf;
}

ghost
fn array_to_ref
  (depth: Ghost.erased nat)
  (r: raw_data_item { Array? r })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1)
ensures
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)
{
  let d = Ghost.reveal depth;
  if (d = 0) {
    PM.seq_list_match_nil_elim s (Array?.v r) (cbor_match_with_depth (nat_pred d) pl);
    PM.seq_list_match_nil_intro s (Array?.v r) ((depth_cb d r) pl);
  } else {
    ghost fn prf
      (c': cbor_raw)
      (v': raw_data_item { v' << Array?.v r /\ List.Tot.memP v' (Array?.v r) })
      requires cbor_match_with_depth (nat_pred d) pl c' v'
      ensures (depth_cb d r) pl c' v'
    {
      depth_cb_succ d r pl c' v';
      nat_pred_succ d;
      rewrite (cbor_match_with_depth (nat_pred d) pl c' v')
        as ((depth_cb d r) pl c' v');
    };
    seq_list_match_conv s (Array?.v r)
      (cbor_match_with_depth (nat_pred d) pl)
      ((depth_cb d r) pl)
      prf;
  }
}

// DELIVERABLE 2 (array): forward conversion + reverse trade + the depth>=1 fact.
ghost
fn cbor_seq_list_match_depth_to_succ
  (depth: Ghost.erased nat)
  (r: raw_data_item { Array? r })
  (pl: perm)
  (s: Seq.seq cbor_raw)
requires
    PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)
ensures
    PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    Trade.trade
      (PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl))
      (PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)) **
    pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1)
{
  array_to_unref depth r pl s;
  intro
    (Trade.trade
      (PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) pl))
      (PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) pl)))
    #(pure (Cons? (Array?.v r) ==> Ghost.reveal depth >= 1))
    fn _
  {
    array_to_ref depth r pl s;
  };
}

// ===== map element-predicate conversions (entry-level) =====
ghost
fn map_peek
  (depth: Ghost.erased nat)
  (r: raw_data_item { Map? r })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))
ensures
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl)) **
    pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  if (Cons? (Map?.v r)) {
    PM.seq_list_match_cons_elim_trade s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb d r) pl));
    unfold (cbor_match_map_entry0 r ((depth_cb d r) pl) (Seq.head s) (List.Tot.hd (Map?.v r)));
    depth_cb_pos d r pl (Seq.head s).cbor_map_entry_key (fst (List.Tot.hd (Map?.v r)));
    fold (cbor_match_map_entry0 r ((depth_cb d r) pl) (Seq.head s) (List.Tot.hd (Map?.v r)));
    Trade.elim _ (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb d r) pl)));
  } else {
    ()
  }
}

ghost
fn map_to_unref
  (depth: Ghost.erased nat)
  (r: raw_data_item { Map? r })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))
ensures
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1)
{
  let d = Ghost.reveal depth;
  map_peek depth r pl s;
  ghost fn prf
    (c': cbor_map_entry)
    (pr: (raw_data_item & raw_data_item) { pr << Map?.v r /\ List.Tot.memP pr (Map?.v r) })
    requires cbor_match_map_entry0 r ((depth_cb d r) pl) c' pr
    ensures cbor_match_map_entry_with_depth (nat_pred d) pl c' pr
  {
    unfold (cbor_match_map_entry0 r ((depth_cb d r) pl) c' pr);
    depth_cb_pos d r pl c'.cbor_map_entry_key (fst pr);
    depth_cb_succ d r pl c'.cbor_map_entry_key (fst pr);
    nat_pred_succ d;
    rewrite ((depth_cb d r) pl c'.cbor_map_entry_key (fst pr))
      as (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_key (fst pr));
    depth_cb_succ d r pl c'.cbor_map_entry_value (snd pr);
    rewrite ((depth_cb d r) pl c'.cbor_map_entry_value (snd pr))
      as (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_value (snd pr));
    fold (cbor_match_map_entry_with_depth (nat_pred d) pl c' pr);
  };
  seq_list_match_conv s (Map?.v r)
    (cbor_match_map_entry0 r ((depth_cb d r) pl))
    (cbor_match_map_entry_with_depth (nat_pred d) pl)
    prf;
}

ghost
fn map_to_ref
  (depth: Ghost.erased nat)
  (r: raw_data_item { Map? r })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1)
ensures
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))
{
  let d = Ghost.reveal depth;
  if (d = 0) {
    PM.seq_list_match_nil_elim s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred d) pl);
    PM.seq_list_match_nil_intro s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb d r) pl));
  } else {
    ghost fn prf
      (c': cbor_map_entry)
      (pr: (raw_data_item & raw_data_item) { pr << Map?.v r /\ List.Tot.memP pr (Map?.v r) })
      requires cbor_match_map_entry_with_depth (nat_pred d) pl c' pr
      ensures cbor_match_map_entry0 r ((depth_cb d r) pl) c' pr
    {
      unfold (cbor_match_map_entry_with_depth (nat_pred d) pl c' pr);
      depth_cb_succ d r pl c'.cbor_map_entry_key (fst pr);
      nat_pred_succ d;
      rewrite (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_key (fst pr))
        as ((depth_cb d r) pl c'.cbor_map_entry_key (fst pr));
      depth_cb_succ d r pl c'.cbor_map_entry_value (snd pr);
      rewrite (cbor_match_with_depth (nat_pred d) pl c'.cbor_map_entry_value (snd pr))
        as ((depth_cb d r) pl c'.cbor_map_entry_value (snd pr));
      fold (cbor_match_map_entry0 r ((depth_cb d r) pl) c' pr);
    };
    seq_list_match_conv s (Map?.v r)
      (cbor_match_map_entry_with_depth (nat_pred d) pl)
      (cbor_match_map_entry0 r ((depth_cb d r) pl))
      prf;
  }
}

// DELIVERABLE 2 (map): forward conversion + reverse trade + the depth>=1 fact.
ghost
fn cbor_seq_list_match_map_depth_to_succ
  (depth: Ghost.erased nat)
  (r: raw_data_item { Map? r })
  (pl: perm)
  (s: Seq.seq cbor_map_entry)
requires
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))
ensures
    PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl) **
    Trade.trade
      (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl))
      (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))) **
    pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1)
{
  map_to_unref depth r pl s;
  intro
    (Trade.trade
      (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) pl))
      (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) pl))))
    #(pure (Cons? (Map?.v r) ==> Ghost.reveal depth >= 1))
    fn _
  {
    map_to_ref depth r pl s;
  };
}

///////////////////////////////////////////////////////////////////////////////
// DELIVERABLE 3 — depth-aware ARRAY iterators
///////////////////////////////////////////////////////////////////////////////

// see cbor_array_iterator_match for why the annotation is necessary
let cbor_array_iterator_match_with_depth (d: Ghost.erased nat)
  : perm -> cbor_array_iterator -> list raw_data_item -> slprop
= cbor_raw_iterator_match
    (cbor_match_with_depth d)
    cbor_serialized_array_iterator_match

fn cbor_array_iterator_init_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Array? r })
requires
    cbor_match_with_depth depth pm c r
returns res: cbor_array_iterator
ensures exists* p .
      cbor_array_iterator_match_with_depth (nat_pred depth) p res (Array?.v r) **
      trade
        (cbor_array_iterator_match_with_depth (nat_pred depth) p res (Array?.v r))
        (cbor_match_with_depth depth pm c r)
{
  cbor_match_with_depth_cases depth pm c r;
  match c {
    norewrite
    CBOR_Case_Serialized_Array c' -> {
      cbor_match_with_depth_eq_match_ser_array depth pm c' r;
      Trade.rewrite_with_trade
        (cbor_match_with_depth depth pm c r)
        (cbor_match_serialized_array c' pm r);
      let i' = cbor_serialized_array_iterator_init c';
      with p . assert (cbor_serialized_array_iterator_match p i' (Array?.v r));
      Trade.trans
        (cbor_serialized_array_iterator_match p i' (Array?.v r))
        (cbor_match_serialized_array c' pm r)
        (cbor_match_with_depth depth pm c r);
      let i : cbor_array_iterator = CBOR_Raw_Iterator_Serialized i';
      Trade.rewrite_with_trade
        (cbor_serialized_array_iterator_match p i' (Array?.v r))
        (cbor_array_iterator_match_with_depth (nat_pred depth) p i (Array?.v r));
      Trade.trans
        (cbor_array_iterator_match_with_depth (nat_pred depth) p i (Array?.v r))
        (cbor_serialized_array_iterator_match p i' (Array?.v r))
        (cbor_match_with_depth depth pm c r);
      i
    }
    norewrite
    CBOR_Case_Array c' -> {
      Trade.rewrite_with_trade
        (cbor_match_with_depth depth pm c r)
        (cbor_match_with_depth depth pm (CBOR_Case_Array c') r);
      cbor_match_with_depth_array_elim depth pm c' r;
      Trade.trans _ _ (cbor_match_with_depth depth pm c r);
      with s . assert (pts_to c'.cbor_array_ptr #(pm `perm_mul` c'.cbor_array_array_perm) s);
      cbor_seq_list_match_depth_to_succ depth r (pm `perm_mul` c'.cbor_array_payload_perm) s;
      Trade.reg_l
        (pts_to c'.cbor_array_ptr #(pm `perm_mul` c'.cbor_array_array_perm) s)
        (PM.seq_list_match s (Array?.v r) (cbor_match_with_depth (nat_pred (Ghost.reveal depth)) (pm `perm_mul` c'.cbor_array_payload_perm)))
        (PM.seq_list_match s (Array?.v r) ((depth_cb (Ghost.reveal depth) r) (pm `perm_mul` c'.cbor_array_payload_perm)));
      Trade.trans _ _ (cbor_match_with_depth depth pm c r);
      let res = cbor_raw_iterator_init_from_slice (cbor_match_with_depth (nat_pred depth)) cbor_serialized_array_iterator_match c'.cbor_array_ptr;
      with p _post.
        rewrite trade (cbor_raw_iterator_match (cbor_match_with_depth (nat_pred depth)) cbor_serialized_array_iterator_match p res (Array?.v r)) _post
             as trade (cbor_array_iterator_match_with_depth (nat_pred depth) p res (Array?.v r)) _post;
      Trade.trans _ _ (cbor_match_with_depth depth pm c r);
      with p . assert (cbor_raw_iterator_match (cbor_match_with_depth (nat_pred depth)) cbor_serialized_array_iterator_match p res (Array?.v r));
      fold (cbor_array_iterator_match_with_depth (nat_pred depth) p res (Array?.v r));
      res
    }
  }
}

fn cbor_array_iterator_is_empty_with_depth
  (d: Ghost.erased nat)
  (c: cbor_array_iterator)
  (#pm: perm)
  (#r: Ghost.erased (list raw_data_item))
requires
    cbor_array_iterator_match_with_depth d pm c r
returns res: bool
ensures
    cbor_array_iterator_match_with_depth d pm c r **
    pure (res == Nil? r)
{
  unfold (cbor_array_iterator_match_with_depth d pm c r);
  let res = cbor_raw_iterator_is_empty
    (cbor_match_with_depth d)
    cbor_serialized_array_iterator_match
    cbor_serialized_array_iterator_is_empty
    c;
  fold (cbor_array_iterator_match_with_depth d pm c r);
  res
}

fn cbor_array_iterator_next_with_depth
  (d: Ghost.erased nat)
  (pi: R.ref cbor_array_iterator)
  (#pm: perm)
  (#i: Ghost.erased cbor_array_iterator)
  (#l: Ghost.erased (list raw_data_item))
requires
    R.pts_to pi i **
    cbor_array_iterator_match_with_depth d pm i l **
    pure (Cons? l)
returns res: cbor_raw
ensures exists* a p i' q .
    cbor_match_with_depth d p res a **
    R.pts_to pi i' **
    cbor_array_iterator_match_with_depth d pm i' q **
    trade
      (cbor_match_with_depth d p res a ** cbor_array_iterator_match_with_depth d pm i' q)
      (cbor_array_iterator_match_with_depth d pm i l) **
    pure (Ghost.reveal l == a :: q)
{
  unfold (cbor_array_iterator_match_with_depth d pm i l);
  let res = cbor_raw_iterator_next
    (cbor_match_with_depth d)
    cbor_serialized_array_iterator_match
    (cbor_serialized_array_iterator_next_with_depth d)
    pi;
  with i'. assert (R.pts_to pi i');
  with l' . rewrite cbor_raw_iterator_match #cbor_raw
      #raw_data_item
      (cbor_match_with_depth d)
      cbor_serialized_array_iterator_match
      pm
      i'
      l'
    as
    cbor_raw_iterator_match #cbor_raw
      #raw_data_item
      (cbor_match_with_depth d)
      cbor_serialized_array_iterator_match
      pm
      i'
      (List.Tot.Base.tl l)
  ;
  fold (cbor_array_iterator_match_with_depth d pm i' (List.Tot.tl l));
  with _pre1 _pre2 _post.
    rewrite trade (_pre1 ** _pre2) _post
         as trade (_pre1 ** cbor_array_iterator_match_with_depth d pm
          (reveal u#0 #(cbor_raw_iterator cbor_raw) i')
          (List.Tot.Base.tl u#0
              #raw_data_item
              (reveal u#0 #(list u#0 raw_data_item) l))) (cbor_array_iterator_match_with_depth d pm i l);
  res
}

///////////////////////////////////////////////////////////////////////////////
// DELIVERABLE 3 — depth-aware MAP iterators
///////////////////////////////////////////////////////////////////////////////

let cbor_map_iterator_match_with_depth (d: Ghost.erased nat)
  : perm -> cbor_map_iterator -> list (raw_data_item & raw_data_item) -> slprop
= cbor_raw_iterator_match
    (cbor_match_map_entry_with_depth d)
    cbor_serialized_map_iterator_match

fn cbor_map_iterator_init_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Map? r })
requires
    cbor_match_with_depth depth pm c r
returns res: cbor_map_iterator
ensures exists* p .
      cbor_map_iterator_match_with_depth (nat_pred depth) p res (Map?.v r) **
      trade
        (cbor_map_iterator_match_with_depth (nat_pred depth) p res (Map?.v r))
        (cbor_match_with_depth depth pm c r)
{
  cbor_match_with_depth_cases depth pm c r;
  match c {
    norewrite
    CBOR_Case_Serialized_Map c' -> {
      cbor_match_with_depth_eq_match_ser_map depth pm c' r;
      Trade.rewrite_with_trade
        (cbor_match_with_depth depth pm c r)
        (cbor_match_serialized_map c' pm r);
      let i' = cbor_serialized_map_iterator_init c';
      with p . assert (cbor_serialized_map_iterator_match p i' (Map?.v r));
      Trade.trans
        (cbor_serialized_map_iterator_match p i' (Map?.v r))
        (cbor_match_serialized_map c' pm r)
        (cbor_match_with_depth depth pm c r);
      let i : cbor_map_iterator = CBOR_Raw_Iterator_Serialized i';
      Trade.rewrite_with_trade
        (cbor_serialized_map_iterator_match p i' (Map?.v r))
        (cbor_map_iterator_match_with_depth (nat_pred depth) p i (Map?.v r));
      Trade.trans
        (cbor_map_iterator_match_with_depth (nat_pred depth) p i (Map?.v r))
        (cbor_serialized_map_iterator_match p i' (Map?.v r))
        (cbor_match_with_depth depth pm c r);
      i
    }
    norewrite
    CBOR_Case_Map c' -> {
      Trade.rewrite_with_trade
        (cbor_match_with_depth depth pm c r)
        (cbor_match_with_depth depth pm (CBOR_Case_Map c') r);
      cbor_match_with_depth_map_elim depth pm c' r;
      Trade.trans _ _ (cbor_match_with_depth depth pm c r);
      with s . assert (pts_to c'.cbor_map_ptr #(pm `perm_mul` c'.cbor_map_array_perm) s);
      cbor_seq_list_match_map_depth_to_succ depth r (pm `perm_mul` c'.cbor_map_payload_perm) s;
      Trade.reg_l
        (pts_to c'.cbor_map_ptr #(pm `perm_mul` c'.cbor_map_array_perm) s)
        (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry_with_depth (nat_pred (Ghost.reveal depth)) (pm `perm_mul` c'.cbor_map_payload_perm)))
        (PM.seq_list_match s (Map?.v r) (cbor_match_map_entry0 r ((depth_cb (Ghost.reveal depth) r) (pm `perm_mul` c'.cbor_map_payload_perm))));
      Trade.trans _ _ (cbor_match_with_depth depth pm c r);
      let res = cbor_raw_iterator_init_from_slice (cbor_match_map_entry_with_depth (nat_pred depth)) cbor_serialized_map_iterator_match c'.cbor_map_ptr;
      with p _post.
        rewrite trade (cbor_raw_iterator_match (cbor_match_map_entry_with_depth (nat_pred depth)) cbor_serialized_map_iterator_match p res (Map?.v r)) _post
             as trade (cbor_map_iterator_match_with_depth (nat_pred depth) p res (Map?.v r)) _post;
      Trade.trans _ _ (cbor_match_with_depth depth pm c r);
      with p . assert (cbor_raw_iterator_match (cbor_match_map_entry_with_depth (nat_pred depth)) cbor_serialized_map_iterator_match p res (Map?.v r));
      fold (cbor_map_iterator_match_with_depth (nat_pred depth) p res (Map?.v r));
      res
    }
  }
}

fn cbor_map_iterator_is_empty_with_depth
  (d: Ghost.erased nat)
  (c: cbor_map_iterator)
  (#pm: perm)
  (#r: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
    cbor_map_iterator_match_with_depth d pm c r
returns res: bool
ensures
    cbor_map_iterator_match_with_depth d pm c r **
    pure (res == Nil? r)
{
  unfold (cbor_map_iterator_match_with_depth d pm c r);
  let res = cbor_raw_iterator_is_empty
    (cbor_match_map_entry_with_depth d)
    cbor_serialized_map_iterator_match
    cbor_serialized_map_iterator_is_empty
    c;
  fold (cbor_map_iterator_match_with_depth d pm c r);
  res
}

fn cbor_map_iterator_next_with_depth
  (d: Ghost.erased nat)
  (pi: R.ref cbor_map_iterator)
  (#pm: perm)
  (#i: Ghost.erased cbor_map_iterator)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
    R.pts_to pi i **
    cbor_map_iterator_match_with_depth d pm i l **
    pure (Cons? l)
returns res: cbor_map_entry
ensures exists* a p i' q .
    cbor_match_map_entry_with_depth d p res a **
    R.pts_to pi i' **
    cbor_map_iterator_match_with_depth d pm i' q **
    trade
      (cbor_match_map_entry_with_depth d p res a ** cbor_map_iterator_match_with_depth d pm i' q)
      (cbor_map_iterator_match_with_depth d pm i l) **
    pure (Ghost.reveal l == a :: q)
{
  unfold (cbor_map_iterator_match_with_depth d pm i l);
  let res = cbor_raw_iterator_next
    (cbor_match_map_entry_with_depth d)
    cbor_serialized_map_iterator_match
    (cbor_serialized_map_iterator_next_with_depth d)
    pi;
  with i'. assert (R.pts_to pi i');
  with l' . rewrite cbor_raw_iterator_match #cbor_map_entry
      #(raw_data_item & raw_data_item)
      (cbor_match_map_entry_with_depth d)
      cbor_serialized_map_iterator_match
      pm
      i'
      l'
    as
    cbor_raw_iterator_match #cbor_map_entry
      #(raw_data_item & raw_data_item)
      (cbor_match_map_entry_with_depth d)
      cbor_serialized_map_iterator_match
      pm
      i'
      (List.Tot.Base.tl l)
  ;
  fold (cbor_map_iterator_match_with_depth d pm i' (List.Tot.tl l));
  with _pre1 _pre2 _post.
    rewrite trade (_pre1 ** _pre2) _post
         as trade (_pre1 ** cbor_map_iterator_match_with_depth d pm
          (reveal u#0 #(cbor_raw_iterator cbor_map_entry) i')
          (List.Tot.Base.tl u#0
              #(raw_data_item & raw_data_item)
              (reveal u#0 #(list u#0 (raw_data_item & raw_data_item)) l))) (cbor_map_iterator_match_with_depth d pm i l);
  res
}

// A non-empty inline array/map at cbor_match_with_depth depth witnesses depth >= 1.
// Used by the depth-recursive comparison loops to discharge nat_pred depth < depth
// when iterating a non-empty container.
ghost
fn cbor_match_with_depth_array_pos (depth: Ghost.erased nat) (p: perm) (a: cbor_array) (v: raw_data_item { Array? v })
  requires cbor_match_with_depth depth p (CBOR_Case_Array a) v
  ensures cbor_match_with_depth depth p (CBOR_Case_Array a) v ** pure (Cons? (Array?.v v) ==> Ghost.reveal depth >= 1)
{
  cbor_match_with_depth_array_elim depth p a v;
  with s . assert (pts_to a.cbor_array_ptr #(p `perm_mul` a.cbor_array_array_perm) s);
  array_peek depth v (p `perm_mul` a.cbor_array_payload_perm) s;
  Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
}

ghost
fn cbor_match_with_depth_map_pos (depth: Ghost.erased nat) (p: perm) (a: cbor_map) (v: raw_data_item { Map? v })
  requires cbor_match_with_depth depth p (CBOR_Case_Map a) v
  ensures cbor_match_with_depth depth p (CBOR_Case_Map a) v ** pure (Cons? (Map?.v v) ==> Ghost.reveal depth >= 1)
{
  cbor_match_with_depth_map_elim depth p a v;
  with s . assert (pts_to a.cbor_map_ptr #(p `perm_mul` a.cbor_map_array_perm) s);
  map_peek depth v (p `perm_mul` a.cbor_map_payload_perm) s;
  Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
}

// Depth-aware tagged payload getter: yields the payload one depth level down.
// Inline tagged -> via the depth elim; serialized tagged -> via cbor_read (the
// payload is non-inline, so it lifts to cbor_match_with_depth for free).
fn cbor_match_tagged_get_payload_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Tagged? r })
  requires cbor_match_with_depth depth pm c r
  returns res: cbor_raw
  ensures exists* pm' .
    cbor_match_with_depth (nat_pred depth) pm' res (Tagged?.v r) **
    trade
      (cbor_match_with_depth (nat_pred depth) pm' res (Tagged?.v r))
      (cbor_match_with_depth depth pm c r)
{
  cbor_match_with_depth_cases depth pm c r;
  match c {
    norewrite
    CBOR_Case_Serialized_Tagged cs -> {
      cbor_match_with_depth_eq_match_ser_tagged depth pm cs r;
      Trade.rewrite_with_trade
        (cbor_match_with_depth depth pm c r)
        (cbor_match_serialized_tagged cs pm r);
      let res = cbor_match_serialized_tagged_get_payload cs;
      Trade.trans _ _ (cbor_match_with_depth depth pm c r);
      cbor_match_with_depth_intro_noninline (nat_pred depth) 1.0R res (Tagged?.v r);
      Trade.trans _ _ (cbor_match_with_depth depth pm c r);
      res
    }
    norewrite
    CBOR_Case_Tagged ct -> {
      Trade.rewrite_with_trade
        (cbor_match_with_depth depth pm c r)
        (cbor_match_with_depth depth pm (CBOR_Case_Tagged ct) r);
      cbor_match_with_depth_tagged_elim depth pm ct r;
      Trade.trans _ _ (cbor_match_with_depth depth pm c r);
      let res = !ct.cbor_tagged_ptr;
      Trade.elim_hyp_l _ _ (cbor_match_with_depth depth pm c r);
      res
    }
  }
}

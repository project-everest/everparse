module CBOR.Pulse.Raw.EverParse.Iterator
#lang-pulse
open CBOR.Spec.Util
open CBOR.Pulse.Raw.Util
open CBOR.Pulse.Raw.Iterator
open Pulse.Lib.Slice open Pulse.Lib.Pervasives open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module LP = LowParse.Pulse.VCList
module U64 = FStar.UInt64

let cbor_raw_serialized_iterator_match
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: list elt_high)
: Tot slprop
= exists* l' . LP.pts_to_serialized (LP.serialize_nlist c.glen s) c.s #(pm *. c.p) l' ** pure (
     U64.v c.len <= c.glen /\
     l == fst (List.Tot.splitAt (U64.v c.len) l')
  )

ghost
fn cbor_raw_serialized_iterator_unfold
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: list elt_high)
requires
  cbor_raw_serialized_iterator_match s pm c l
ensures exists* l' .
  LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l' **
  pure (
    U64.v c.len <= c.glen /\
    l == fst (List.Tot.splitAt (U64.v c.len) l')
  ) **
  trade
    (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l')
    (cbor_raw_serialized_iterator_match s pm c l)
{
  unfold (cbor_raw_serialized_iterator_match s pm c l);
  with l' . assert (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l');
  intro
    (Trade.trade
      (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l')
      (cbor_raw_serialized_iterator_match s pm c l)
    )
    #emp
    fn _
  {
    fold (cbor_raw_serialized_iterator_match s pm c l)
  };
  ()
}

ghost
fn cbor_raw_serialized_iterator_fold // this function cannot be used to truncate iterators since we want to preserve the list l.
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: LP.nlist (c.glen) elt_high)
requires
  LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l ** pure (
    Ghost.reveal c.glen == U64.v c.len
  )
ensures
  cbor_raw_serialized_iterator_match s pm c l **
  trade
    (cbor_raw_serialized_iterator_match s pm c l)
    (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l)
{
  List.Tot.append_l_nil l;
  list_splitAt_append_elim l [];
  fold (cbor_raw_serialized_iterator_match s pm c l);
  intro
    (Trade.trade
      (cbor_raw_serialized_iterator_match s pm c l)
      (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l)
    )
    #emp
    fn _
  {
    unfold (cbor_raw_serialized_iterator_match s pm c l);
    with l' . assert (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l');
    List.Tot.append_l_nil l';
    list_splitAt_append_elim l' [];
    rewrite (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l')
      as (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l)
  };
  ()
}

ghost
fn cbor_raw_serialized_iterator_fold_with_perm
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (glen: nat)
  (sl: slice LP.byte)
  (pm': perm)
  (l': LP.nlist (glen) elt_high)
  (c: cbor_raw_serialized_iterator)
  (pm: perm)
  (l: list elt_high)
requires
  LP.pts_to_serialized (LP.serialize_nlist (glen) s) sl #(pm') l' ** pure (
    Ghost.reveal c.glen == glen /\
    c.s == sl /\
    U64.v c.len <= Ghost.reveal c.glen /\
    l == fst (List.Tot.splitAt (U64.v c.len) l') /\
    pm' == pm *. c.p +. pm *. c.p
  )
ensures
  cbor_raw_serialized_iterator_match s pm c l **
  trade
    (cbor_raw_serialized_iterator_match s pm c l)
    (LP.pts_to_serialized (LP.serialize_nlist (glen) s) sl #(pm') l')
{
  rewrite each sl as c.s;
  LP.pts_to_serialized_share (LP.serialize_nlist (glen) s) c.s;
  fold (cbor_raw_serialized_iterator_match s pm c l);
  intro
    (Trade.trade
      (cbor_raw_serialized_iterator_match s pm c l)
      (LP.pts_to_serialized (LP.serialize_nlist (glen) s) c.s #(pm') l')
    )
    #(LP.pts_to_serialized (LP.serialize_nlist (glen) s) c.s #(pm' /. 2.0R) l') 
    fn _
  {
    unfold (cbor_raw_serialized_iterator_match s pm c l);
    LP.pts_to_serialized_gather (LP.serialize_nlist (glen) s) c.s;
    ()
  };
  rewrite each c.s as sl;
  ()
}

ghost
fn cbor_raw_serialized_iterator_is_empty_equiv
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong /\ k.parser_kind_low > 0 })
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: list elt_high)
requires
  cbor_raw_serialized_iterator_match s pm c l
ensures
  cbor_raw_serialized_iterator_match s pm c l ** pure (Nil? l <==> c.len == 0uL)
{
  cbor_raw_serialized_iterator_unfold s pm c l;
  Trade.elim _ _;
}

inline_for_extraction
fn cbor_raw_serialized_iterator_is_empty
  (#elt_high: Type0)
  (#k: Ghost.erased LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { (Ghost.reveal k).parser_kind_subkind == Some LP.ParserStrong /\ (Ghost.reveal k).parser_kind_low > 0 })
: cbor_raw_serialized_iterator_is_empty_t #elt_high (cbor_raw_serialized_iterator_match s)
= (c: cbor_raw_serialized_iterator)
  (#pm: perm)
  (#l: Ghost.erased (list elt_high))
{
  cbor_raw_serialized_iterator_is_empty_equiv s pm c l;
  (c.len = 0uL)
}

inline_for_extraction
fn cbor_raw_serialized_iterator_length
  (#elt_high: Type0)
  (#k: Ghost.erased LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { (Ghost.reveal k).parser_kind_subkind == Some LP.ParserStrong /\ (Ghost.reveal k).parser_kind_low > 0 })
: cbor_raw_serialized_iterator_length_t #elt_high (cbor_raw_serialized_iterator_match s)
= (c: cbor_raw_serialized_iterator)
  (#pm: perm)
  (#l: Ghost.erased (list elt_high))
{
  cbor_raw_serialized_iterator_unfold s pm c l;
  with l' . assert (LP.pts_to_serialized (LP.serialize_nlist c.glen s) c.s #(pm *. c.p) l');
  CBOR.Spec.Util.list_splitAt_length (U64.v c.len) l';
  Trade.elim _ _;
  c.len
}

let cbor_raw_serialized_iterator_next_cont
  (#elt_low #elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (elt_match: perm -> elt_low -> elt_high -> slprop)
= (x: S.slice LP.byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased elt_high) ->
  stt elt_low
    (LP.pts_to_serialized s x #pm v)
    (fun res -> exists* pm' . elt_match pm' res v **
      trade
        (elt_match pm' res v)
        (LP.pts_to_serialized s x #pm v)
    )

module LPC = LowParse.Pulse.Combinators

inline_for_extraction
fn cbor_raw_serialized_iterator_next
  (#elt_low #elt_high: Type0)
  (#k: Ghost.erased LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { (Ghost.reveal k).parser_kind_subkind == Some LP.ParserStrong /\ (Ghost.reveal k).parser_kind_low > 0 })
  (j: LP.jumper p)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (phi: cbor_raw_serialized_iterator_next_cont s elt_match)
: cbor_raw_serialized_iterator_next_t #elt_low #elt_high elt_match (cbor_raw_serialized_iterator_match s)
=
  (pi: R.ref (cbor_raw_iterator elt_low))
  (#pm: perm)
  (i: cbor_raw_serialized_iterator)
  (#l: Ghost.erased (list elt_high))
{
  cbor_raw_serialized_iterator_unfold s pm i l;
  with l' . assert (LP.pts_to_serialized (LP.serialize_nlist i.glen s) i.s #(pm *. i.p) l');
  LP.nlist_cons_as_nondep_then s i.glen i.s;
  Trade.trans _ _ (cbor_raw_serialized_iterator_match s pm i l);
  let glen' : Ghost.erased nat = i.glen - 1;
  let k' : Ghost.erased LP.parser_kind = LP.parse_nlist_kind glen' k;
  let p' : LP.parser k' (LP.nlist glen' elt_high) = LP.parse_nlist glen' p;
  let s' : LP.serializer p' = LP.serialize_nlist glen' s;
  let v' : Ghost.erased (elt_high & LP.nlist glen' elt_high) = Ghost.hide (List.Tot.hd l', List.Tot.tl l');
  assert (LP.pts_to_serialized
    (LPC.serialize_nondep_then s s')
    i.s
    #(pm *. i.p)
    v'
  );
  let s1, s2 = LowParse.Pulse.Combinators.split_nondep_then
    s
    j
    #k'
    #p'
    s'
    i.s;
  unfold (LPC.split_nondep_then_post s s' i.s (pm *. i.p) v' (s1, s2));
  unfold (LPC.split_nondep_then_post' s s' i.s (pm *. i.p) v' s1 s2);
  trade_trans_nounify _ _ _ (cbor_raw_serialized_iterator_match s pm i l);
  let res = phi s1;
  with pm' . assert (elt_match pm' res (fst v'));
  Trade.rewrite_with_trade
    (elt_match pm' res (fst v'))
    (elt_match pm' res (List.Tot.hd l));
  Trade.trans (elt_match pm' res (List.Tot.hd l)) _ _;
  let i' : cbor_raw_serialized_iterator = {
    s = s2;
    p = i.p /. 2.0R;
    len = U64.sub i.len 1uL;
    glen = glen';
  };
  pi := CBOR_Raw_Iterator_Serialized i';
  perm_half_mult pm i.p;
  cbor_raw_serialized_iterator_fold_with_perm s glen' s2 (pm *. i.p) (List.Tot.tl l') i' pm (List.Tot.tl l);
  Trade.prod
    (elt_match _ res (List.Tot.hd l))
    _
    (cbor_raw_serialized_iterator_match s pm i' (List.Tot.tl l))
    _;
  trade_trans_nounify _ _ _ (cbor_raw_serialized_iterator_match s pm i l);
  res
}

let rec list_splitAt_splitAt
  (#t: Type)
  (l: list t)
  (n1 n2: nat)
: Lemma
  (requires (n1 >= n2))
  (ensures (
    let l1 = fst (List.Tot.splitAt n1 l) in
    let l2 = fst (List.Tot.splitAt n2 l1) in
    l2 == fst (List.Tot.splitAt n2 l)
  ))
  (decreases n2)
= if n2 = 0
  then ()
  else match l with
  | [] -> ()
  | _ :: q -> list_splitAt_splitAt q (n1 - 1) (n2 - 1)

#restart-solver

inline_for_extraction
fn cbor_raw_serialized_iterator_truncate
  (#elt_high: Type0)
  (#k: Ghost.erased LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { (Ghost.reveal k).parser_kind_subkind == Some LP.ParserStrong /\ (Ghost.reveal k).parser_kind_low > 0 })
: cbor_raw_serialized_iterator_truncate_t #elt_high (cbor_raw_serialized_iterator_match s)
=
  (c: _)
  (len: _)
  (#pm: perm)
  (#l: Ghost.erased (list elt_high))
{
  cbor_raw_serialized_iterator_unfold s pm c l;
  with l' . assert (LP.pts_to_serialized (LP.serialize_nlist (c.glen) s) c.s #(pm *. c.p) l');
  list_splitAt_splitAt l' (U64.v c.len) (U64.v len);
  let c' : cbor_raw_serialized_iterator = {
    s = c.s;
    glen = c.glen;
    len = len;
    p = (pm *. c.p) /. 2.0R;
  };
  cbor_raw_serialized_iterator_fold_with_perm
    s
    (Ghost.reveal c.glen)
    c.s
    (pm *. c.p)
    l'
    c'
    1.0R
    (fst (List.Tot.splitAt (U64.v len) l));
  Trade.trans _ _ (cbor_raw_serialized_iterator_match s pm c l);
  c'
}

ghost
fn cbor_raw_serialized_iterator_share
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { (k).parser_kind_subkind == Some LP.ParserStrong /\ (k).parser_kind_low > 0 })
: cbor_raw_serialized_iterator_share_t #elt_high (cbor_raw_serialized_iterator_match s)
=
  (c: _)
  (#pm: perm)
  (#l: (list elt_high))
{
  unfold (cbor_raw_serialized_iterator_match s pm c l);
  LP.pts_to_serialized_share (LP.serialize_nlist (c.glen) s) c.s;
  half_mul_l pm c.p;
  fold (cbor_raw_serialized_iterator_match s (pm /. 2.0R) c l);
  fold (cbor_raw_serialized_iterator_match s (pm /. 2.0R) c l);
}

ghost
fn cbor_raw_serialized_iterator_gather
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { (k).parser_kind_subkind == Some LP.ParserStrong /\ (k).parser_kind_low > 0 })
: cbor_raw_serialized_iterator_gather_t #elt_high (cbor_raw_serialized_iterator_match s)
=
  (c: _)
  (#pm1: perm)
  (#l1: (list elt_high))
  (#pm2: perm)
  (#l2: (list elt_high))
{
  unfold (cbor_raw_serialized_iterator_match s pm1 c l1);
  unfold (cbor_raw_serialized_iterator_match s pm2 c l2);
  LP.pts_to_serialized_gather (LP.serialize_nlist (c.glen) s) c.s;
  perm_mul_add_l pm1 pm2 c.p;
  fold (cbor_raw_serialized_iterator_match s (pm1 +. pm2) c l1);
}

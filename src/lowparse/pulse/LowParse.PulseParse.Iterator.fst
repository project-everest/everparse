module LowParse.PulseParse.Iterator
#lang-pulse
include LowParse.PulseParse.Base
include LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT

noeq
type base_iterator ([@@@strictly_positive] t: Type) =
| Empty
| Singleton of ref t
| Slice of S.slice t
| Serialized: (count: SZ.t) -> (payload: S.slice U8.t) -> base_iterator t

noeq
type iterator ([@@@strictly_positive] t: Type) =
| Base of base_iterator t
| Append:
  (count: SZ.t) ->
  (before: base_iterator t) ->
  (after: ref (iterator t)) ->
  iterator t

module SM = Pulse.Lib.SeqMatch

let base_iterator_match
  (#t: Type)
  (#u: Type)
  (vmatch: t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (i: base_iterator t)
  (l: list u)
: Tot slprop
= match i with
  | Empty -> pure (Nil? l)
  | Singleton s -> exists* x y .
    pts_to s x **
    vmatch x y **
    pure (l == [y])
  | Slice s -> exists* l' .
    pts_to s l' **
    SM.seq_list_match l' l vmatch
  | Serialized count pl -> exists* l' .
    pts_to_parsed (parse_nlist (SZ.v count) p) pl l' **
    pure ((l' <: list u) == l)

let rec iterator_match
  (#t: Type)
  (#u: Type)
  (vmatch: t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (i: iterator t)
  (l: list u)
: Tot slprop
= match i with
  | Base i -> base_iterator_match vmatch p i l
  | Append count before after ->
    exists* i1 i2 l2 .
      base_iterator_match vmatch p before i1 **
      pts_to after i2 **
      iterator_match vmatch p i2 l2 **
      pure (
        SZ.v count <= List.Tot.length i1 + List.Tot.length l2 /\
        l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1 l2))
      )

let rec lemma_splitAt_fst_length (#a: Type) (n: nat) (l: list a)
  : Lemma
    (requires n <= List.Tot.length l)
    (ensures List.Tot.length (fst (List.Tot.splitAt n l)) == n)
    (decreases n)
  = if n = 0 then () else lemma_splitAt_fst_length (n - 1) (List.Tot.tl l)

fn base_iterator_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (i: base_iterator t)
  (#l: Ghost.erased (list u))
requires base_iterator_match vmatch p i l
returns res: SZ.t
ensures base_iterator_match vmatch p i l ** pure (SZ.v res == List.Tot.length l)
{
  match i {
    Empty -> {
      unfold (base_iterator_match vmatch p (Empty #t) l);
      fold (base_iterator_match vmatch p (Empty #t) l);
      rewrite (base_iterator_match vmatch p (Empty #t) l)
           as (base_iterator_match vmatch p i l);
      0sz
    }
    Singleton s -> {
      unfold (base_iterator_match vmatch p (Singleton s) l);
      fold (base_iterator_match vmatch p (Singleton s) l);
      rewrite (base_iterator_match vmatch p (Singleton s) l)
           as (base_iterator_match vmatch p i l);
      1sz
    }
    Slice sl -> {
      unfold (base_iterator_match vmatch p (Slice sl) l);
      SM.seq_list_match_length vmatch _ l;
      S.pts_to_len sl;
      let res = S.len sl;
      fold (base_iterator_match vmatch p (Slice sl) l);
      rewrite (base_iterator_match vmatch p (Slice sl) l)
           as (base_iterator_match vmatch p i l);
      res
    }
    Serialized count pl -> {
      unfold (base_iterator_match vmatch p (Serialized count pl) l);
      fold (base_iterator_match vmatch p (Serialized count pl) l);
      rewrite (base_iterator_match vmatch p (Serialized count pl) l)
           as (base_iterator_match vmatch p i l);
      count
    }
  }
}

fn iterator_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (i: iterator t)
  (#l: Ghost.erased (list u))
requires iterator_match vmatch p i l
returns res: SZ.t
ensures iterator_match vmatch p i l ** pure (SZ.v res == List.Tot.length l)
{
  match i {
    Base bi -> {
      unfold (iterator_match vmatch p (Base bi) l);
      let res = base_iterator_length vmatch p bi;
      fold (iterator_match vmatch p (Base bi) l);
      rewrite (iterator_match vmatch p (Base bi) l)
           as (iterator_match vmatch p i l);
      res
    }
    Append count before after -> {
      unfold (iterator_match vmatch p (Append count before after) l);
      with _i1 _i2 _l2 . assert (
        base_iterator_match vmatch p before _i1 **
        pts_to after _i2 **
        iterator_match vmatch p _i2 _l2 **
        pure (
          SZ.v count <= List.Tot.length _i1 + List.Tot.length _l2 /\
          Ghost.reveal l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append _i1 _l2))
        )
      );
      List.Tot.append_length _i1 _l2;
      lemma_splitAt_fst_length (SZ.v count) (List.Tot.append _i1 _l2);
      fold (iterator_match vmatch p (Append count before after) l);
      rewrite (iterator_match vmatch p (Append count before after) l)
           as (iterator_match vmatch p i l);
      count
    }
  }
}

fn iterator_is_empty
  (#t: Type0)
  (#u: Type0)
  (vmatch: t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (i: iterator t)
  (#l: Ghost.erased (list u))
requires iterator_match vmatch p i l
returns res: bool
ensures iterator_match vmatch p i l ** pure (res == Nil? l)
{
  let len = iterator_length vmatch p i;
  (len = 0sz)
}

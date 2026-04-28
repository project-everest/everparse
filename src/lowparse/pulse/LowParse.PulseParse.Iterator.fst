module LowParse.PulseParse.Iterator
#lang-pulse
include LowParse.PulseParse.Base
include LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module U8 = FStar.UInt8
module SZ = FStar.SizeT

inline_for_extraction
let share_t
  (#t1 #t2: Type)
  (vmatch: perm -> t1 -> t2 -> slprop)
=
  (x1: t1) ->
  (#p: perm) ->
  (#x2: t2) ->
  stt_ghost unit emp_inames
  (vmatch p x1 x2)
  (fun _ ->
    let open FStar.Real in
    vmatch (p /. 2.0R) x1 x2 ** vmatch (p /. 2.0R) x1 x2
  )

inline_for_extraction
let gather_t
  (#t1 #t2: Type)
  (vmatch: perm -> t1 -> t2 -> slprop)
=
  (x1: t1) ->
  (#p: perm) ->
  (#x2: t2) ->
  (#p': perm) ->
  (#x2': t2) ->
  stt_ghost unit emp_inames
  (vmatch p x1 x2 ** vmatch p' x1 x2')
  (fun _ ->
    let open FStar.Real in
    vmatch (p +. p') x1 x2 **
    pure (x2 == x2')
  )

noeq
type base_iterator ([@@@strictly_positive] t: Type) =
| Empty
| Singleton: (sp: perm) -> (sv: perm) -> (sr: ref t) -> base_iterator t
| Slice: (sp: perm) -> (sv: perm) -> (ss: S.slice t) -> base_iterator t
| Serialized: (sp: perm) -> (count: SZ.t) -> (payload: S.slice U8.t) -> base_iterator t

noeq
type iterator ([@@@strictly_positive] t: Type) =
| Base of base_iterator t
| Append:
  (count: SZ.t) ->
  (before: base_iterator t) ->
  (ap: perm) ->
  (after: ref (iterator t)) ->
  iterator t

module SM = Pulse.Lib.SeqMatch

let base_iterator_match
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (i: base_iterator t)
  (l: list u)
: Tot slprop
= match i with
  | Empty -> pure (Nil? l)
  | Singleton sp sv s -> exists* x y .
    pts_to s #sp x **
    vmatch sv x y **
    pure (l == [y])
  | Slice sp sv s -> exists* l' .
    pts_to s #sp l' **
    SM.seq_list_match l' l (vmatch sv)
  | Serialized sp count pl -> exists* l' .
    pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #sp l' **
    pure ((l' <: list u) == l)

let rec iterator_match
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (i: iterator t)
  (l: list u)
: Tot slprop
= match i with
  | Base i -> base_iterator_match vmatch p i l
  | Append count before ap after ->
    exists* i1 i2 l2 .
      base_iterator_match vmatch p before i1 **
      pts_to after #ap i2 **
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
  (vmatch: perm -> t -> u -> slprop)
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
    Singleton sp sv s -> {
      unfold (base_iterator_match vmatch p (Singleton sp sv s) l);
      fold (base_iterator_match vmatch p (Singleton sp sv s) l);
      rewrite (base_iterator_match vmatch p (Singleton sp sv s) l)
           as (base_iterator_match vmatch p i l);
      1sz
    }
    Slice sp sv sl -> {
      unfold (base_iterator_match vmatch p (Slice sp sv sl) l);
      SM.seq_list_match_length (vmatch sv) _ l;
      S.pts_to_len sl;
      let res = S.len sl;
      fold (base_iterator_match vmatch p (Slice sp sv sl) l);
      rewrite (base_iterator_match vmatch p (Slice sp sv sl) l)
           as (base_iterator_match vmatch p i l);
      res
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match vmatch p (Serialized sp count pl) l);
      fold (base_iterator_match vmatch p (Serialized sp count pl) l);
      rewrite (base_iterator_match vmatch p (Serialized sp count pl) l)
           as (base_iterator_match vmatch p i l);
      count
    }
  }
}

fn iterator_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
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
    Append count before ap after -> {
      unfold (iterator_match vmatch p (Append count before ap after) l);
      with _i1 _i2 _l2 . assert (
        base_iterator_match vmatch p before _i1 **
        pts_to after #ap _i2 **
        iterator_match vmatch p _i2 _l2 **
        pure (
          SZ.v count <= List.Tot.length _i1 + List.Tot.length _l2 /\
          Ghost.reveal l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append _i1 _l2))
        )
      );
      List.Tot.append_length _i1 _l2;
      lemma_splitAt_fst_length (SZ.v count) (List.Tot.append _i1 _l2);
      fold (iterator_match vmatch p (Append count before ap after) l);
      rewrite (iterator_match vmatch p (Append count before ap after) l)
           as (iterator_match vmatch p i l);
      count
    }
  }
}

fn iterator_is_empty
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
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

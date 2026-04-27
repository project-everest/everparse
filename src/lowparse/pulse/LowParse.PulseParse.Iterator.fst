module LowParse.PulseParse.Iterator
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
    exists* i1 i2 l1 l2 .
      base_iterator_match vmatch p before i1 **
      pts_to after i2 **
      iterator_match vmatch p i2 l2 **
      pure (
        SZ.v count <= List.Tot.length l1 + List.Tot.length l2 /\
        l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append l1 l2))
      )

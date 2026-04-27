module LowParse.PulseParse.Iterator
include LowParse.PulseParse.Base
include LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT

noeq
type iterator ([@@@strictly_positive] t: Type) =
| Empty
| Slice of S.slice t
| Serialized: (count: SZ.t) -> (payload: S.slice U8.t) -> iterator t
| Insert:
  (before: ref (iterator t)) ->
  (item: ref t) ->
  (after: ref (iterator t)) ->
  iterator t

module SM = Pulse.Lib.SeqMatch

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
  | Empty -> pure (Nil? l)
  | Slice s -> exists* l' .
    pts_to s l' **
    SM.seq_list_match l' l vmatch
  | Serialized count pl -> exists* l' .
    pts_to_parsed (parse_nlist (SZ.v count) p) pl l' **
    pure ((l' <: list u) == l)
  | Insert before item after ->
    exists* i1 i2 l1 y z l2 .
      pts_to before i1 **
      pts_to item y **
      pts_to after i2 **
      iterator_match vmatch p i1 l1 **
      vmatch y z **
      iterator_match vmatch p i2 l2 **
      pure (l == List.Tot.append l1 (z :: l2))

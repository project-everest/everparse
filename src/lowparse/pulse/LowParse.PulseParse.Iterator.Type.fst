module LowParse.PulseParse.Iterator.Type
#lang-pulse

(* Types-only fragment of LowParse.PulseParse.Iterator.

   This module exists so that Karamel bundles needing only the iterator
   types (for the C-extracted type headers) can depend on it without
   pulling in the function-bodies of LowParse.PulseParse.Iterator. *)

open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module U8 = FStar.UInt8
module SZ = FStar.SizeT

noeq
type base_mixed_list ([@@@strictly_positive] t: Type) =
| Empty
| Singleton: (sp: perm) -> (sv: perm) -> (sr: ref t) -> base_mixed_list t
| Slice: (sp: perm) -> (sv: perm) -> (ss: S.slice t) -> base_mixed_list t
| Serialized: (sp: perm) -> (count: SZ.t) -> (payload: S.slice U8.t) -> base_mixed_list t

noeq
type mixed_list ([@@@strictly_positive] t: Type) =
| Base of base_mixed_list t
| Append:
  (depth: Ghost.erased nat) ->
  (cb: SZ.t) ->
  (ca: SZ.t { SZ.fits (SZ.v cb + SZ.v ca) }) ->
  (ob: SZ.t) ->
  (bp: perm) ->
  (before: ref (mixed_list t)) ->
  (oa: SZ.t) ->
  (ap: perm) ->
  (after: ref (mixed_list t)) ->
  mixed_list t

noeq
type iterator ([@@@strictly_positive] t: Type) =
| IBase: (before: base_mixed_list t) -> iterator t
| IPair: (before: base_mixed_list t) -> (after: mixed_list t) -> iterator t

let base_mixed_list_length
  (#t: Type)
  (i: base_mixed_list t)
: Tot SZ.t
= match i with
  | Empty -> 0sz
  | Singleton _ _ _ -> 1sz
  | Slice _ _ sl -> S.len sl
  | Serialized _ count _ -> count

let mixed_list_length
  (#t: Type)
  (i: mixed_list t)
: Tot SZ.t
= match i with
  | Base bi -> base_mixed_list_length bi
  | Append _ cb ca _ _ _ _ _ _ -> SZ.add cb ca

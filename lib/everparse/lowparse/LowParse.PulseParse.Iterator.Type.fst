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
module IO = LowParse.PulseParse.Iterator.IntOps

noeq
type base_mixed_list (i: Type0) ([@@@strictly_positive] t: Type) =
| Empty
| Singleton: (sp: perm) -> (sv: perm) -> (sr: ref t) -> base_mixed_list i t
| Slice: (sp: perm) -> (sv: perm) -> (ss: S.slice t) -> (count: i) -> base_mixed_list i t
| Serialized: (sp: perm) -> (count: i) -> (payload: S.slice U8.t) -> base_mixed_list i t

noeq
type mixed_list (i: Type0) ([@@@strictly_positive] t: Type) =
| Base of base_mixed_list i t
| Append:
  (depth: Ghost.erased nat) ->
  (cb: i) ->
  (ca: i) ->
  (tot: i) ->
  (ob: i) ->
  (bp: perm) ->
  (before: ref (mixed_list i t)) ->
  (oa: i) ->
  (ap: perm) ->
  (after: ref (mixed_list i t)) ->
  (sc: perm) ->
  mixed_list i t

noeq
type iterator (i: Type0) ([@@@strictly_positive] t: Type) =
| IBase: (before: base_mixed_list i t) -> iterator i t
| IPair: (before: base_mixed_list i t) -> (after: mixed_list i t) -> iterator i t

inline_for_extraction
let base_mixed_list_length
  (#i: Type0) (io: IO.int_ops i)
  (#t: Type)
  (b: base_mixed_list i t)
: Tot i
= match b with
  | Empty -> io.zero
  | Singleton _ _ _ -> io.one
  | Slice _ _ _ count -> count
  | Serialized _ count _ -> count

inline_for_extraction
let mixed_list_length
  (#i: Type0) (io: IO.int_ops i)
  (#t: Type)
  (m: mixed_list i t)
: Tot i
= match m with
  | Base bi -> base_mixed_list_length io bi
  | Append _ _ _ tot _ _ _ _ _ _ _ -> tot

// Option H: base_iterator is a type alias for base_mixed_list. The associated
// _start/_next/_next_eos Pulse functions walk base_mixed_list directly,
// avoiding the IBase|IPair tag dispatch and the larger iterator struct
// (which has to accommodate the IPair branch). This is the perf path used
// by the parser-produced CBOR_Case_{Array,Map}_Base arms.
let base_iterator (i: Type0) (t: Type0) : Type0 = base_mixed_list i t

inline_for_extraction
let base_iterator_length
  (#i: Type0) (io: IO.int_ops i)
  (#t: Type)
  (b: base_iterator i t)
: Tot i
= base_mixed_list_length io b

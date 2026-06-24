module CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder
#lang-pulse

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Nondet.Common

module Spec = CBOR.Spec.API.Format
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module IT = LowParse.PulseParse.Iterator.Type
module U64 = FStar.UInt64
module L = FStar.List.Tot

(* Ownership of a structurally-built nondeterministic-CBOR array. *)
val cbor_nondet_array_owned (x: cbor_nondet_t) (l: list Spec.cbor) : slprop

(* Empty array. *)
inline_for_extraction
fn cbor_nondet_array_empty (_: unit)
requires emp
returns res: cbor_nondet_t
ensures cbor_nondet_array_owned res []

(* Singleton array from a single element (plus a scratch reference). *)
inline_for_extraction
fn cbor_nondet_array_singleton
  (x: cbor_nondet_t) (ry: R.ref cbor_nondet_t)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbor_nondet_t)
requires
  cbor_nondet_match pm x v ** R.pts_to ry w0
returns res: cbor_nondet_t
ensures
  cbor_nondet_array_owned res [Ghost.reveal v] **
  Trade.trade
    (cbor_nondet_array_owned res [Ghost.reveal v])
    (cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w))

(* Append of two owned arrays. *)
inline_for_extraction
fn cbor_nondet_array_append
  (x1 x2: cbor_nondet_t)
  (r_before r_after: R.ref (IT.mixed_list cbor_nondet_t))
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased (IT.mixed_list cbor_nondet_t))
requires
  cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
  R.pts_to r_before vb0 ** R.pts_to r_after va0
returns res: option cbor_nondet_t
ensures
  (match res with
   | None ->
     cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
    (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
    pure (~ (FStar.UInt.fits (L.length (Ghost.reveal l1) + L.length (Ghost.reveal l2)) U64.n))
   | Some r ->
     cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)) **
     Trade.trade
       (cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
       (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))

(* Finalize: turn an owned array into a normal nondeterministic CBOR object. *)
inline_for_extraction
fn cbor_nondet_array_finalize
  (x: cbor_nondet_t)
  (#l: Ghost.erased (list Spec.cbor))
requires
  cbor_nondet_array_owned x l
returns _: unit
ensures
  exists* (l': (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n })).
    cbor_nondet_match 1.0R x (Spec.pack (Spec.CArray l')) **
    Trade.trade
      (cbor_nondet_match 1.0R x (Spec.pack (Spec.CArray l')))
      (cbor_nondet_array_owned x l) **
    pure ((l' <: list Spec.cbor) == Ghost.reveal l)

(* The length of an owned array fits in a u64; lets callers discharge the
   refinement of [cbor_nondet_array_finalize] after a chain of appends. *)
val cbor_nondet_array_owned_length_fits
  (x: cbor_nondet_t) (#l: Ghost.erased (list Spec.cbor))
: stt_ghost unit emp_inames
    (cbor_nondet_array_owned x l)
    (fun _ -> cbor_nondet_array_owned x l **
      pure (FStar.UInt.fits (L.length (Ghost.reveal l)) U64.n))

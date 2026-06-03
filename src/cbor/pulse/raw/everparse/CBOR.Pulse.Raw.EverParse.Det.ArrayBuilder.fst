module CBOR.Pulse.Raw.EverParse.Det.ArrayBuilder
#lang-pulse
friend CBOR.Pulse.API.Det.Type
friend CBOR.Pulse.Raw.EverParse.Det.Impl

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Det.Type
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Det.Impl

module Spec = CBOR.Spec.API.Format
module SpecRaw = CBOR.Spec.Raw
module SpecRawBase = CBOR.Spec.Raw.Base
module Optimal = CBOR.Spec.Raw.Optimal
module AB = CBOR.Pulse.Raw.EverParse.ArrayBuilder
module Aux = CBOR.Pulse.Raw.EverParse.Det.Impl.Aux
module RawMatch = CBOR.Pulse.Raw.EverParse.Match
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module IT = LowParse.PulseParse.Iterator.Type
module U64 = FStar.UInt64
module L = FStar.List.Tot

(* ================================================================ *)
(* Ownership at the deterministic-CBOR Spec level                   *)
(* ================================================================ *)

let cbor_det_array_owned (x: cbor_det_t) (l: list Spec.cbor) : slprop =
  AB.cbor_array_owned x (Aux.det_raw_list l)

(* det_raw_list distributes over append *)

let det_raw_list_append (l1 l2: list Spec.cbor)
: Lemma (Aux.det_raw_list (L.append l1 l2) ==
         L.append (Aux.det_raw_list l1) (Aux.det_raw_list l2))
= Aux.det_raw_list_eq l1;
  Aux.det_raw_list_eq l2;
  Aux.det_raw_list_eq (L.append l1 l2);
  L.append_l_nil (Aux.det_raw_list l1);
  L.map_append SpecRaw.mk_det_raw_cbor l1 l2

(* ================================================================ *)
(* Empty array                                                      *)
(* ================================================================ *)

inline_for_extraction
fn cbor_det_array_empty (_: unit)
requires emp
returns res: cbor_det_t
ensures cbor_det_array_owned res []
{
  let res = AB.cbor_array_empty ();
  Aux.det_raw_list_eq ([] <: list Spec.cbor);
  rewrite (AB.cbor_array_owned res [])
    as (AB.cbor_array_owned res (Aux.det_raw_list ([] <: list Spec.cbor)));
  fold (cbor_det_array_owned res ([] <: list Spec.cbor));
  res
}

(* ================================================================ *)
(* Singleton array                                                  *)
(* ================================================================ *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_det_array_singleton
  (x: cbor_det_t) (ry: R.ref cbor_det_t)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbor_det_t)
requires
  cbor_det_match pm x v ** R.pts_to ry w0
returns res: cbor_det_t
ensures
  cbor_det_array_owned res [Ghost.reveal v] **
  Trade.trade
    (cbor_det_array_owned res [Ghost.reveal v])
    (cbor_det_match pm x v ** (exists* w. R.pts_to ry w))
{
  unfold (cbor_det_match pm x v);
  let res = AB.cbor_array_singleton x ry
    #pm #(Ghost.hide (SpecRaw.mk_det_raw_cbor (Ghost.reveal v)));
  Aux.det_raw_list_eq [Ghost.reveal v];
  rewrite (AB.cbor_array_owned res [SpecRaw.mk_det_raw_cbor (Ghost.reveal v)])
    as (AB.cbor_array_owned res (Aux.det_raw_list [Ghost.reveal v]));
  fold (cbor_det_array_owned res [Ghost.reveal v]);
  Trade.intro_trade
    (cbor_det_array_owned res [Ghost.reveal v])
    (cbor_det_match pm x v ** (exists* w. R.pts_to ry w))
    (Trade.trade
      (AB.cbor_array_owned res [SpecRaw.mk_det_raw_cbor (Ghost.reveal v)])
      (RawMatch.cbor_raw_match pm x (SpecRaw.mk_det_raw_cbor (Ghost.reveal v)) ** (exists* w. R.pts_to ry w)))
    fn _ {
      unfold (cbor_det_array_owned res [Ghost.reveal v]);
      rewrite (AB.cbor_array_owned res (Aux.det_raw_list [Ghost.reveal v]))
        as (AB.cbor_array_owned res [SpecRaw.mk_det_raw_cbor (Ghost.reveal v)]);
      Trade.elim
        (AB.cbor_array_owned res [SpecRaw.mk_det_raw_cbor (Ghost.reveal v)])
        (RawMatch.cbor_raw_match pm x (SpecRaw.mk_det_raw_cbor (Ghost.reveal v)) ** (exists* w. R.pts_to ry w));
      fold (cbor_det_match pm x v);
    };
  res
}

#pop-options

(* ================================================================ *)
(* Append                                                           *)
(* ================================================================ *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_det_array_append
  (x1 x2: cbor_det_t)
  (r_before r_after: R.ref (IT.mixed_list cbor_raw))
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased (IT.mixed_list cbor_raw))
requires
  cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
  R.pts_to r_before vb0 ** R.pts_to r_after va0
returns res: option cbor_det_t
ensures
  (match res with
   | None ->
     cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
     (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
     pure (~ (FStar.UInt.fits (L.length (Ghost.reveal l1) + L.length (Ghost.reveal l2)) U64.n))
   | Some r ->
     cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)) **
     Trade.trade
       (cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
       (cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))
{
  unfold (cbor_det_array_owned x1 l1);
  unfold (cbor_det_array_owned x2 l2);
  let res = AB.cbor_array_append x1 x2 r_before r_after
    #(Aux.det_raw_list l1) #(Aux.det_raw_list l2);
  match res {
    None -> {
      Aux.length_det_raw_list l1;
      Aux.length_det_raw_list l2;
      fold (cbor_det_array_owned x1 l1);
      fold (cbor_det_array_owned x2 l2);
      None #cbor_det_t
    }
    Some r -> {
      det_raw_list_append l1 l2;
      rewrite (AB.cbor_array_owned r (L.append (Aux.det_raw_list l1) (Aux.det_raw_list l2)))
        as (AB.cbor_array_owned r (Aux.det_raw_list (L.append (Ghost.reveal l1) (Ghost.reveal l2))));
      fold (cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)));
      Trade.intro_trade
        (cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
        (cbor_det_array_owned x1 l1 ** cbor_det_array_owned x2 l2 **
         (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va))
        (Trade.trade
          (AB.cbor_array_owned r (L.append (Aux.det_raw_list l1) (Aux.det_raw_list l2)))
          (AB.cbor_array_owned x1 (Aux.det_raw_list l1) **
           AB.cbor_array_owned x2 (Aux.det_raw_list l2) **
           (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))
        fn _ {
          unfold (cbor_det_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)));
          rewrite (AB.cbor_array_owned r (Aux.det_raw_list (L.append (Ghost.reveal l1) (Ghost.reveal l2))))
            as (AB.cbor_array_owned r (L.append (Aux.det_raw_list l1) (Aux.det_raw_list l2)));
          Trade.elim
            (AB.cbor_array_owned r (L.append (Aux.det_raw_list l1) (Aux.det_raw_list l2)))
            (AB.cbor_array_owned x1 (Aux.det_raw_list l1) **
             AB.cbor_array_owned x2 (Aux.det_raw_list l2) **
             (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va));
          fold (cbor_det_array_owned x1 l1);
          fold (cbor_det_array_owned x2 l2);
        };
      Some #cbor_det_t r
    }
  }
}

#pop-options

(* ================================================================ *)
(* Finalize: owned array -> deterministic CBOR object               *)
(* ================================================================ *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_det_array_finalize
  (x: cbor_det_t)
  (#l: Ghost.erased (list Spec.cbor))
requires
  cbor_det_array_owned x l
returns _: unit
ensures
  exists* (l': (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n })).
    cbor_det_match 1.0R x (Spec.pack (Spec.CArray l')) **
    Trade.trade
      (cbor_det_match 1.0R x (Spec.pack (Spec.CArray l')))
      (cbor_det_array_owned x l) **
    pure ((l' <: list Spec.cbor) == Ghost.reveal l)
{
  unfold (cbor_det_array_owned x l);
  AB.cbor_array_owned_length_fits x;
  Aux.length_det_raw_list l;
  let lw : Ghost.erased (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n }) =
    Ghost.hide (Ghost.reveal l);
  let y : Ghost.erased Spec.cbor = Ghost.hide (Spec.pack (Spec.CArray (Ghost.reveal lw)));
  Spec.unpack_pack (Spec.CArray (Ghost.reveal lw));
  Aux.mk_det_raw_cbor_array_eq (Ghost.reveal y) (Ghost.reveal lw);
  unfold (AB.cbor_array_owned x (Aux.det_raw_list l));
  with xh. assert (RawMatch.cbor_raw_match 1.0R x xh);
  assert (pure (xh == SpecRaw.mk_det_raw_cbor (Ghost.reveal y)));
  rewrite (RawMatch.cbor_raw_match 1.0R x xh)
    as (RawMatch.cbor_raw_match 1.0R x (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)));
  fold (cbor_det_match 1.0R x y);
  Trade.intro_trade
    (cbor_det_match 1.0R x y)
    (cbor_det_array_owned x l)
    emp
    fn _ {
      unfold (cbor_det_match 1.0R x y);
      rewrite (RawMatch.cbor_raw_match 1.0R x (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)))
        as (RawMatch.cbor_raw_match 1.0R x xh);
      fold (AB.cbor_array_owned x (Aux.det_raw_list l));
      fold (cbor_det_array_owned x l);
    };
  rewrite (cbor_det_match 1.0R x y)
    as (cbor_det_match 1.0R x (Spec.pack (Spec.CArray (Ghost.reveal lw))));
  rewrite (Trade.trade
            (cbor_det_match 1.0R x y)
            (cbor_det_array_owned x l))
    as (Trade.trade
         (cbor_det_match 1.0R x (Spec.pack (Spec.CArray (Ghost.reveal lw))))
         (cbor_det_array_owned x l));
}

#pop-options

(* The length of an owned array fits in a u64 (needed to discharge the
   refinement of [cbor_det_array_finalize] after a chain of appends). *)
ghost
fn cbor_det_array_owned_length_fits
  (x: cbor_det_t) (#l: Ghost.erased (list Spec.cbor))
requires cbor_det_array_owned x l
ensures cbor_det_array_owned x l ** pure (FStar.UInt.fits (L.length (Ghost.reveal l)) U64.n)
{
  unfold (cbor_det_array_owned x l);
  AB.cbor_array_owned_length_fits x;
  fold (cbor_det_array_owned x l);
}

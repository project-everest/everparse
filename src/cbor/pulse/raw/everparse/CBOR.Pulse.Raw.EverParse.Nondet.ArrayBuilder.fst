module CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder
#lang-pulse
friend CBOR.Pulse.API.Nondet.Type
friend CBOR.Pulse.API.Nondet.Common

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Nondet.Common
open CBOR.Pulse.Raw.EverParse.Type

module Spec = CBOR.Spec.API.Format
module SpecRaw = CBOR.Spec.Raw
module SpecRawBase = CBOR.Spec.Raw.Base
module AB = CBOR.Pulse.Raw.EverParse.ArrayBuilder
module RawMatch = CBOR.Pulse.Raw.EverParse.Match
module Common = CBOR.Pulse.API.Nondet.Common
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module IT = LowParse.PulseParse.Iterator.Type
module I = LowParse.PulseParse.Iterator
module U64 = FStar.UInt64
module L = FStar.List.Tot
module SZ = FStar.SizeT
module SpecEP = CBOR.Spec.Raw.EverParse
module Make = CBOR.Pulse.Raw.EverParse.Make
module Comb = LowParse.Pulse.Combinators
module Proj = LowParse.PulseParse.Projectors
module Append = LowParse.PulseParse.Iterator.Append
module Optimal = CBOR.Spec.Raw.Optimal
module Cst = CBOR.Spec.Constants

(* ================================================================ *)
(* Ownership predicate                                              *)
(* ================================================================ *)

let cbor_nondet_array_owned (x: cbor_nondet_t) (l: list Spec.cbor) : slprop =
  exists* (lraw: list SpecRawBase.raw_data_item).
    AB.cbor_array_owned x lraw **
    pure (List.Tot.for_all SpecRaw.valid_raw_data_item lraw /\
          l == List.Tot.map SpecRaw.mk_cbor lraw)

(* ================================================================ *)
(* Helpers                                                          *)
(* ================================================================ *)

(* Forward direction: the header computed from a CBOR_Case_Array value matches
   the header of the reconstructed Array spec node. *)
let array_get_header_build
  (vx: cbor_array cbor_raw)
  (ru: SpecRawBase.raw_uint64)
  (l: list SpecRawBase.raw_data_item)
: Lemma
  (requires
    L.length l == U64.v ru.value /\
    (ru.value <: U64.t) == U64.uint_to_t (SZ.v (IT.mixed_list_length vx.cbor_array_ptr)) /\
    (ru.size <: SpecRawBase.integer_size) == vx.cbor_array_length_size)
  (ensures
    RawMatch.cbor_raw_get_header (CBOR_Case_Array vx) ==
      Some (dfst (SpecEP.synth_raw_data_item_recip (SpecRawBase.Array ru l))) /\
    (let (| b, _ |) = dfst (SpecEP.synth_raw_data_item_recip (SpecRawBase.Array ru l)) in
     b.major_type = Cst.cbor_major_type_array))
= assert_norm (Cst.cbor_major_type_array `FStar.UInt8.lt` Cst.cbor_major_type_simple_value == true);
  let v'' : SpecRawBase.raw_data_item = SpecRawBase.Array ru l in
  let h1 = SpecEP.raw_uint64_as_argument Cst.cbor_major_type_array ru in
  let r = SpecEP.get_array_length v'' (dfst (SpecEP.synth_raw_data_item_recip v'')) in
  ()

(* From the header relation pinned by a match on a CBOR_Case_Array value,
   recover the abstract array length. *)
let array_len_from_header
  (vx: cbor_array cbor_raw)
  (v'': SpecRawBase.raw_data_item)
: Lemma
  (requires SpecRawBase.Array? v'' /\
    RawMatch.cbor_raw_get_header (CBOR_Case_Array vx) ==
      Some (dfst (SpecEP.synth_raw_data_item_recip v'')))
  (ensures
    (SpecRawBase.Array?.len v'' <: SpecRawBase.raw_uint64) ==
    ({ size = vx.cbor_array_length_size;
       value = U64.uint_to_t (SZ.v (IT.mixed_list_length vx.cbor_array_ptr)) } <: SpecRawBase.raw_uint64))
= let ru : SpecRawBase.raw_uint64 =
    { size = vx.cbor_array_length_size;
      value = U64.uint_to_t (SZ.v (IT.mixed_list_length vx.cbor_array_ptr)) } in
  assert_norm (Cst.cbor_major_type_array `FStar.UInt8.lt` Cst.cbor_major_type_simple_value == true);
  let h1 = SpecEP.raw_uint64_as_argument Cst.cbor_major_type_array ru in
  let r = SpecEP.get_array_length v'' (dfst (SpecEP.synth_raw_data_item_recip v'')) in
  ()

(* Extract the header pure fact from a cbor_raw_match. *)
ghost fn cbor_raw_match_get_header
  (pm: perm) (x: cbor_nondet_t) (#y: Ghost.erased SpecRawBase.raw_data_item)
requires RawMatch.cbor_raw_match pm x y
ensures RawMatch.cbor_raw_match pm x y **
  pure (RawMatch.cbor_raw_get_header x == Some (dfst (SpecEP.synth_raw_data_item_recip y)))
{
  RawMatch.cbor_raw_match_unfold_aux x;
  unfold (RawMatch.cbor_raw_match_aux SpecEP.parse_raw_data_item RawMatch.cbor_raw_match pm x (Ghost.reveal y));
  unfold (Comb.vmatch_synth
    (Proj.vmatch_dep_pair_with_proj
       RawMatch.cbor_raw_match_header
       RawMatch.cbor_raw_id_proj
       (RawMatch.cbor_raw_match_content RawMatch.cbor_raw_match SpecEP.parse_raw_data_item pm))
    SpecEP.synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (Proj.vmatch_dep_pair_with_proj
    RawMatch.cbor_raw_match_header
    RawMatch.cbor_raw_id_proj
    (RawMatch.cbor_raw_match_content RawMatch.cbor_raw_match SpecEP.parse_raw_data_item pm)
    x
    (SpecEP.synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (RawMatch.cbor_raw_match_header
    (RawMatch.cbor_raw_id_proj.pair_proj_get x)
    (dfst (SpecEP.synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (RawMatch.cbor_raw_get_header (RawMatch.cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (SpecEP.synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (RawMatch.cbor_raw_get_header x ==
           Some (dfst (SpecEP.synth_raw_data_item_recip (Ghost.reveal y)))));
  let the_prop = RawMatch.cbor_raw_get_header x ==
    Some (dfst (SpecEP.synth_raw_data_item_recip (Ghost.reveal y)));
  let sq = elim_pure_explicit the_prop;
  intro_pure the_prop sq;
  rewrite
    (pure (RawMatch.cbor_raw_get_header x ==
           Some (dfst (SpecEP.synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (RawMatch.cbor_raw_get_header (RawMatch.cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (SpecEP.synth_raw_data_item_recip (Ghost.reveal y)))));
  fold (RawMatch.cbor_raw_match_header
    (RawMatch.cbor_raw_id_proj.pair_proj_get x)
    (dfst (SpecEP.synth_raw_data_item_recip (Ghost.reveal y))));
  fold (Proj.vmatch_dep_pair_with_proj
    RawMatch.cbor_raw_match_header
    RawMatch.cbor_raw_id_proj
    (RawMatch.cbor_raw_match_content RawMatch.cbor_raw_match SpecEP.parse_raw_data_item pm)
    x
    (SpecEP.synth_raw_data_item_recip (Ghost.reveal y)));
  fold (Comb.vmatch_synth
    (Proj.vmatch_dep_pair_with_proj
       RawMatch.cbor_raw_match_header
       RawMatch.cbor_raw_id_proj
       (RawMatch.cbor_raw_match_content RawMatch.cbor_raw_match SpecEP.parse_raw_data_item pm))
    SpecEP.synth_raw_data_item_recip
    x (Ghost.reveal y));
  fold (RawMatch.cbor_raw_match_aux SpecEP.parse_raw_data_item RawMatch.cbor_raw_match pm x (Ghost.reveal y));
  RawMatch.cbor_raw_match_fold_aux x;
}

(* ================================================================ *)
(* Empty array                                                      *)
(* ================================================================ *)

inline_for_extraction
fn cbor_nondet_array_empty (_: unit)
requires emp
returns res: cbor_nondet_t
ensures cbor_nondet_array_owned res []
{
  let res = AB.cbor_array_empty ();
  rewrite (AB.cbor_array_owned res [])
    as (AB.cbor_array_owned res ([] <: list SpecRawBase.raw_data_item));
  fold (cbor_nondet_array_owned res ([] <: list Spec.cbor));
  res
}

(* ================================================================ *)
(* Manual array constructor exposing the array node structure       *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

fn mk_array_owned_with_ptr
  (f64: squash SZ.fits_u64)
  (len_size: SpecRawBase.integer_size)
  (ml: IT.mixed_list cbor_nondet_t)
  (#l: Ghost.erased (list SpecRawBase.raw_data_item))
requires
  I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml l **
  pure (
    let len = SZ.v (IT.mixed_list_length ml) in
    FStar.UInt.fits len 64 /\
    SpecRawBase.raw_uint64_size_prop len_size (U64.uint_to_t len) /\
    len_size == AB.minimal_len_size (U64.uint_to_t len) /\
    L.length l == len
  )
returns res: cbor_nondet_t
ensures
  AB.cbor_array_owned res l **
  pure (CBOR_Case_Array? res /\
    ((CBOR_Case_Array?.v res).cbor_array_ptr <: IT.mixed_list cbor_raw) == ml /\
    (CBOR_Case_Array?.v res).cbor_array_length_size == len_size /\
    (CBOR_Case_Array?.v res).cbor_array_slice_perm == 1.0R) **
  Trade.trade
    (AB.cbor_array_owned res l)
    (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml l)
{
  let the_prop =
    (let len = SZ.v (IT.mixed_list_length ml) in
     FStar.UInt.fits len 64 /\
     SpecRawBase.raw_uint64_size_prop len_size (U64.uint_to_t len) /\
     len_size == AB.minimal_len_size (U64.uint_to_t len) /\
     L.length l == len);
  let sq = elim_pure_explicit the_prop;
  let len_sz = IT.mixed_list_length ml;
  let len64 = SZ.sizet_to_uint64 len_sz;
  let ru : SpecRawBase.raw_uint64 = { size = len_size; value = len64 };
  let v : cbor_array cbor_raw = {
    cbor_array_length_size = len_size;
    cbor_array_ptr = ml;
    cbor_array_slice_perm = 1.0R;
  };
  let res = CBOR_Case_Array v;
  let xh : Ghost.erased SpecRawBase.raw_data_item = SpecRawBase.Array ru l;
  RawMatch.cbor_raw_match_content_eq_array RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R
    (dfst (dfst (SpecEP.synth_raw_data_item_recip xh)))
    (dsnd (dfst (SpecEP.synth_raw_data_item_recip xh)))
    v
    (dsnd (SpecEP.synth_raw_data_item_recip xh));
  rewrite
    (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml l)
    as
    (RawMatch.cbor_raw_match_content RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R
       (dfst (SpecEP.synth_raw_data_item_recip xh)) res (dsnd (SpecEP.synth_raw_data_item_recip xh)));
  Make.cbor_raw_match_fold_from_content_array 1.0R res xh ();
  assert (pure (U64.v len64 == SZ.v len_sz));
  assert (pure (len64 == U64.uint_to_t (L.length l)));
  assert (pure (ru == Optimal.mk_raw_uint64 (U64.uint_to_t (L.length l))));
  fold (AB.cbor_array_owned res l);
  Trade.intro_trade
    (AB.cbor_array_owned res l)
    (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml l)
    emp
    fn _ {
      AB.cbor_array_owned_to_ml res ml l;
      drop_ (Trade.trade
        (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml l)
        (AB.cbor_array_owned res l));
    };
  res
}

#pop-options

(* ================================================================ *)
(* Singleton array                                                  *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

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
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let v' = cbor_nondet_match_elim x;
  drop_ (Trade.trade
    (RawMatch.cbor_raw_match pm x v')
    (cbor_nondet_match pm x v));
  // Build the singleton mixed_list manually, keeping half of ry's pts_to (H).
  R.write ry x;
  R.share ry;
  let sp_val : Ghost.erased perm = 1.0R /. 2.0R;
  let sv_val : Ghost.erased perm = pm;
  let ml : IT.mixed_list cbor_nondet_t = IT.Base (IT.Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry);
  rewrite (R.pts_to ry #(1.0R /. 2.0R) x)
    as (R.pts_to ry #(1.0R *. Ghost.reveal sp_val) x);
  rewrite (RawMatch.cbor_raw_match pm x (Ghost.reveal v'))
    as (RawMatch.cbor_raw_match (1.0R *. Ghost.reveal sv_val) x (Ghost.reveal v'));
  fold (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 1 1.0R
    (IT.Singleton #cbor_nondet_t (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) [Ghost.reveal v']);
  fold (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 1 1.0R
    (IT.Base (IT.Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal v']);
  rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 1 1.0R
    (IT.Base (IT.Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal v'])
    as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml)) 1.0R ml [Ghost.reveal v']);
  fold (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml [Ghost.reveal v']);
  // Build res with known structure.
  let len_size = AB.minimal_len_size 1uL;
  AB.minimal_len_size_prop 1uL;
  let res = mk_array_owned_with_ptr f64 len_size ml #[Ghost.reveal v'];
  drop_ (Trade.trade
    (AB.cbor_array_owned res [Ghost.reveal v'])
    (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml [Ghost.reveal v']));
  fold (cbor_nondet_array_owned res [Ghost.reveal v]);
  Trade.intro_trade
    (cbor_nondet_array_owned res [Ghost.reveal v])
    (cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w))
    (R.pts_to ry #(1.0R /. 2.0R) x **
     pure (CBOR_Case_Array? res /\
           ((CBOR_Case_Array?.v res).cbor_array_ptr <: IT.mixed_list cbor_raw) == ml))
    fn _ {
      unfold (cbor_nondet_array_owned res [Ghost.reveal v]);
      with lraw. assert (AB.cbor_array_owned res lraw);
      AB.cbor_array_owned_to_ml res ml lraw;
      drop_ (Trade.trade
        (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml lraw)
        (AB.cbor_array_owned res lraw));
      unfold (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml lraw);
      rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml)) 1.0R ml lraw)
        as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 1 1.0R
              (IT.Base (IT.Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) lraw);
      unfold (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 1 1.0R
              (IT.Base (IT.Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) lraw);
      unfold (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 1 1.0R
              (IT.Singleton #cbor_nondet_t (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) lraw);
      with xc yc. assert (
        R.pts_to ry #(1.0R *. Ghost.reveal sp_val) xc **
        RawMatch.cbor_raw_match (1.0R *. Ghost.reveal sv_val) xc yc);
      rewrite (R.pts_to ry #(1.0R *. Ghost.reveal sp_val) xc)
        as (R.pts_to ry #(1.0R /. 2.0R) xc);
      R.gather ry;
      rewrite (RawMatch.cbor_raw_match (1.0R *. Ghost.reveal sv_val) xc yc)
        as (RawMatch.cbor_raw_match pm x yc);
      rewrite (R.pts_to ry #(1.0R /. 2.0R +. 1.0R /. 2.0R) x)
        as (R.pts_to ry x);
      fold (cbor_nondet_match pm x v);
      fold (exists* w. R.pts_to ry w);
    };
  res
}

#pop-options

(* ================================================================ *)
(* Append                                                           *)
(* ================================================================ *)

(* Extract minimality of the length-size field from an owned array. *)
fn array_owned_minimal
  (x: cbor_nondet_t) (len64: U64.t) (#l: Ghost.erased (l': list SpecRawBase.raw_data_item { FStar.UInt.fits (L.length l') U64.n }))
requires AB.cbor_array_owned x (Ghost.reveal l) ** pure (U64.v len64 == L.length (Ghost.reveal l))
returns _: unit
ensures AB.cbor_array_owned x (Ghost.reveal l) **
  pure (CBOR_Case_Array? x /\
    (CBOR_Case_Array?.v x).cbor_array_slice_perm == 1.0R /\
    (CBOR_Case_Array?.v x).cbor_array_length_size == (Optimal.mk_raw_uint64 len64).size)
{
  unfold (AB.cbor_array_owned x l);
  with xh. assert (RawMatch.cbor_raw_match 1.0R x xh);
  cbor_raw_match_get_header 1.0R x #xh;
  array_len_from_header (CBOR_Case_Array?.v x) xh;
  fold (AB.cbor_array_owned x l);
}

(* Rebuild an owned array for a GIVEN cbor_raw value from a mixed_list_match.
   This is ghost so it can be invoked inside a trade-elimination closure. *)
#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

ghost fn rebuild_owned
  (x: cbor_nondet_t) (ml: IT.mixed_list cbor_nondet_t) (len64: U64.t)
  (#l: Ghost.erased (list SpecRawBase.raw_data_item))
requires
  I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml l **
  pure (FStar.UInt.fits (L.length l) U64.n /\
    CBOR_Case_Array? x /\
    ((CBOR_Case_Array?.v x).cbor_array_ptr <: IT.mixed_list cbor_raw) == ml /\
    (CBOR_Case_Array?.v x).cbor_array_slice_perm == 1.0R /\
    U64.v len64 == L.length l /\
    (CBOR_Case_Array?.v x).cbor_array_length_size == (Optimal.mk_raw_uint64 len64).size)
returns _: unit
ensures
  AB.cbor_array_owned x l
{
  let v : cbor_array cbor_raw = CBOR_Case_Array?.v x;
  let ru : SpecRawBase.raw_uint64 = Optimal.mk_raw_uint64 len64;
  let xh : Ghost.erased SpecRawBase.raw_data_item = SpecRawBase.Array ru l;
  I.mixed_list_match_length RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml l;
  RawMatch.cbor_raw_match_content_eq_array RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R
    (dfst (dfst (SpecEP.synth_raw_data_item_recip xh)))
    (dsnd (dfst (SpecEP.synth_raw_data_item_recip xh)))
    v
    (dsnd (SpecEP.synth_raw_data_item_recip xh));
  rewrite
    (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml l)
    as
    (RawMatch.cbor_raw_match_content RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R
       (dfst (SpecEP.synth_raw_data_item_recip xh)) x (dsnd (SpecEP.synth_raw_data_item_recip xh)));
  array_get_header_build v ru l;
  let sq : squash (
    RawMatch.cbor_raw_get_header x == Some (dfst (SpecEP.synth_raw_data_item_recip (Ghost.reveal xh))) /\
    (let (| b, _ |) = dfst (SpecEP.synth_raw_data_item_recip (Ghost.reveal xh)) in
     b.major_type = Cst.cbor_major_type_array)) = ();
  Make.cbor_raw_match_fold_from_content_array 1.0R x xh sq;
  assert (pure (len64 == U64.uint_to_t (L.length l)));
  assert (pure (ru == Optimal.mk_raw_uint64 (U64.uint_to_t (L.length l))));
  fold (AB.cbor_array_owned x l);
}

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

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
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  unfold (cbor_nondet_array_owned x1 l1);
  with lraw1. assert (AB.cbor_array_owned x1 lraw1);
  unfold (cbor_nondet_array_owned x2 l2);
  with lraw2. assert (AB.cbor_array_owned x2 lraw2);

  (* Extract the minimality + structural facts about x1 and x2 while keeping
     ownership. These are pure and persist after we fold back. *)
  unfold (AB.cbor_array_owned x1 lraw1);
  with xh1. assert (RawMatch.cbor_raw_match 1.0R x1 xh1);
  cbor_raw_match_get_header 1.0R x1 #xh1;
  array_len_from_header (CBOR_Case_Array?.v x1) xh1;
  fold (AB.cbor_array_owned x1 lraw1);

  unfold (AB.cbor_array_owned x2 lraw2);
  with xh2. assert (RawMatch.cbor_raw_match 1.0R x2 xh2);
  cbor_raw_match_get_header 1.0R x2 #xh2;
  array_len_from_header (CBOR_Case_Array?.v x2) xh2;
  fold (AB.cbor_array_owned x2 lraw2);

  (* Eliminate ownership to the underlying mixed lists. *)
  let ml_a = AB.cbor_array_owned_elim x1 lraw1;
  let ml_b = AB.cbor_array_owned_elim x2 lraw2;
  I.mixed_list_match_length RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_a lraw1;
  I.mixed_list_match_length RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_b lraw2;
  let len_a = IT.mixed_list_length ml_a;
  let len_b = IT.mixed_list_length ml_b;
  let la64 = SZ.sizet_to_uint64 len_a;
  let lb64 = SZ.sizet_to_uint64 len_b;
  let limit = U64.sub 0xffffffffffffffffuL lb64;
  if U64.gt la64 limit {
    (* Overflow: restore both ownership predicates and report failure. *)
    Trade.elim
      (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_a (Ghost.reveal lraw1))
      (AB.cbor_array_owned x1 lraw1);
    Trade.elim
      (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_b (Ghost.reveal lraw2))
      (AB.cbor_array_owned x2 lraw2);
    fold (cbor_nondet_array_owned x1 l1);
    fold (cbor_nondet_array_owned x2 l2);
    AB.array_append_overflow la64 lb64 (SZ.v len_a) (SZ.v len_b);
    List.Tot.Properties.map_lemma SpecRaw.mk_cbor lraw1;
    List.Tot.Properties.map_lemma SpecRaw.mk_cbor lraw2;
    None #cbor_nondet_t
  } else {
    let sum64 = U64.add la64 lb64;
    SZ.fits_u64_implies_fits (SZ.v len_a + SZ.v len_b);

    (* These pure facts feed the back-trade. *)
    assert (pure ((CBOR_Case_Array?.v x1).cbor_array_length_size == (Optimal.mk_raw_uint64 la64).size));
    assert (pure ((CBOR_Case_Array?.v x2).cbor_array_length_size == (Optimal.mk_raw_uint64 lb64).size));

    (* ---- Build the Append node manually, keeping ref halves outside. ---- *)
    let depth : Ghost.erased nat =
      (if I.mixed_list_depth ml_a > I.mixed_list_depth ml_b
       then I.mixed_list_depth ml_a else I.mixed_list_depth ml_b) + 1;
    let bp : Ghost.erased perm = (1.0R /. 2.0R) /. 1.0R;
    R.write r_before ml_a;
    R.share r_before;
    R.write r_after ml_b;
    R.share r_after;
    let ml_res : IT.mixed_list cbor_raw =
      IT.Append #cbor_raw (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after;
    let lres : Ghost.erased (list SpecRawBase.raw_data_item) = L.append (Ghost.reveal lraw1) (Ghost.reveal lraw2);
    Append.perm_mul_div_cancel' 1.0R (1.0R /. 2.0R);
    rewrite (R.pts_to r_before #(1.0R /. 2.0R) ml_a)
      as (R.pts_to r_before #(1.0R *. Ghost.reveal bp) ml_a);
    rewrite (R.pts_to r_after #(1.0R /. 2.0R) ml_b)
      as (R.pts_to r_after #(1.0R *. Ghost.reveal bp) ml_b);
    rewrite (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_a (Ghost.reveal lraw1))
      as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item (I.append_off_before 0 (SZ.v 0sz) (SZ.v len_a)) (I.append_n_before 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a)) 1.0R ml_a (Ghost.reveal lraw1));
    rewrite (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_b (Ghost.reveal lraw2))
      as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item (I.append_off_after 0 (SZ.v 0sz) (SZ.v len_a)) (I.append_n_after 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a)) 1.0R ml_b (Ghost.reveal lraw2));
    List.Tot.Properties.append_length (Ghost.reveal lraw1) (Ghost.reveal lraw2);
    intro_pure (
      0 + SZ.v (IT.mixed_list_length ml_res) <= SZ.v len_a + SZ.v len_b /\
      SZ.v 0sz + SZ.v len_a <= SZ.v (IT.mixed_list_length ml_a) /\
      SZ.v 0sz + SZ.v len_b <= SZ.v (IT.mixed_list_length ml_b) /\
      List.Tot.length (Ghost.reveal lraw1) == I.append_n_before 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a) /\
      List.Tot.length (Ghost.reveal lraw2) == I.append_n_after 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a) /\
      Ghost.reveal lres == L.append (Ghost.reveal lraw1) (Ghost.reveal lraw2) /\
      I.mixed_list_depth ml_a < Ghost.reveal depth /\
      I.mixed_list_depth ml_b < Ghost.reveal depth
    ) ();
    fold (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml_res)) 1.0R
      (IT.Append #cbor_raw (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after)
      (Ghost.reveal lres));
    rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml_res)) 1.0R
      (IT.Append #cbor_raw (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after)
      (Ghost.reveal lres))
      as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml_res)) 1.0R ml_res (Ghost.reveal lres));
    fold (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_res (Ghost.reveal lres));
    (* The elim trades for x1/x2 are no longer usable (their mixed lists were
       consumed into the node); drop them. *)
    drop_ (Trade.trade
      (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_a (Ghost.reveal lraw1))
      (AB.cbor_array_owned x1 lraw1));
    drop_ (Trade.trade
      (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_b (Ghost.reveal lraw2))
      (AB.cbor_array_owned x2 lraw2));

    (* ---- Build owned for res from the node. ---- *)
    let len_size = AB.minimal_len_size sum64;
    AB.minimal_len_size_prop sum64;
    let res = mk_array_owned_with_ptr f64 len_size ml_res #lres;
    drop_ (Trade.trade
      (AB.cbor_array_owned res lres)
      (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_res (Ghost.reveal lres)));

    (* nondet ownership of res, over l1 ++ l2 *)
    L.map_append SpecRaw.mk_cbor (Ghost.reveal lraw1) (Ghost.reveal lraw2);
    L.for_all_append SpecRaw.valid_raw_data_item (Ghost.reveal lraw1) (Ghost.reveal lraw2);
    fold (cbor_nondet_array_owned res (L.append (Ghost.reveal l1) (Ghost.reveal l2)));

    (* ---- Back-trade. ---- *)
    Trade.intro_trade
      (cbor_nondet_array_owned res (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
      (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
       (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va))
      (R.pts_to r_before #(1.0R /. 2.0R) ml_a **
       R.pts_to r_after #(1.0R /. 2.0R) ml_b **
       pure (
         CBOR_Case_Array? res /\
         ((CBOR_Case_Array?.v res).cbor_array_ptr <: IT.mixed_list cbor_raw) == ml_res /\
         (Ghost.reveal ml_res ==
            IT.Append #cbor_raw (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after) /\
         1.0R *. Ghost.reveal bp == 1.0R /. 2.0R /\
         CBOR_Case_Array? x1 /\
         ((CBOR_Case_Array?.v x1).cbor_array_ptr <: IT.mixed_list cbor_raw) == ml_a /\
         (CBOR_Case_Array?.v x1).cbor_array_slice_perm == 1.0R /\
         (CBOR_Case_Array?.v x1).cbor_array_length_size == (Optimal.mk_raw_uint64 la64).size /\
         U64.v la64 == SZ.v len_a /\
         CBOR_Case_Array? x2 /\
         ((CBOR_Case_Array?.v x2).cbor_array_ptr <: IT.mixed_list cbor_raw) == ml_b /\
         (CBOR_Case_Array?.v x2).cbor_array_slice_perm == 1.0R /\
         (CBOR_Case_Array?.v x2).cbor_array_length_size == (Optimal.mk_raw_uint64 lb64).size /\
         U64.v lb64 == SZ.v len_b /\
         SZ.v len_a == L.length (Ghost.reveal lraw1) /\
         SZ.v len_b == L.length (Ghost.reveal lraw2) /\
         Ghost.reveal l1 == L.map SpecRaw.mk_cbor (Ghost.reveal lraw1) /\
         Ghost.reveal l2 == L.map SpecRaw.mk_cbor (Ghost.reveal lraw2)
       ))
      fn _ {
        unfold (cbor_nondet_array_owned res (L.append (Ghost.reveal l1) (Ghost.reveal l2)));
        with lr. assert (AB.cbor_array_owned res lr);
        AB.cbor_array_owned_to_ml res ml_res lr;
        drop_ (Trade.trade
          (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_res (Ghost.reveal lr))
          (AB.cbor_array_owned res lr));
        (* structural split of the Append node *)
        unfold (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_res (Ghost.reveal lr));
        rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml_res)) 1.0R ml_res (Ghost.reveal lr))
          as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml_res)) 1.0R
                (IT.Append #cbor_raw (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after)
                (Ghost.reveal lr));
        unfold (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml_res)) 1.0R
                (IT.Append #cbor_raw (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after)
                (Ghost.reveal lr));
        with ib_u ia_u l1_u l2_u. assert (
          R.pts_to r_before #(1.0R *. Ghost.reveal bp) ib_u **
          I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item (I.append_off_before 0 (SZ.v 0sz) (SZ.v len_a)) (I.append_n_before 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a)) 1.0R ib_u l1_u **
          R.pts_to r_after #(1.0R *. Ghost.reveal bp) ia_u **
          I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item (I.append_off_after 0 (SZ.v 0sz) (SZ.v len_a)) (I.append_n_after 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a)) 1.0R ia_u l2_u
        );
        rewrite (R.pts_to r_before #(1.0R *. Ghost.reveal bp) ib_u)
          as (R.pts_to r_before #(1.0R /. 2.0R) ib_u);
        R.gather r_before;
        rewrite (R.pts_to r_before #(1.0R /. 2.0R +. 1.0R /. 2.0R) ml_a)
          as (R.pts_to r_before ml_a);
        rewrite (R.pts_to r_after #(1.0R *. Ghost.reveal bp) ia_u)
          as (R.pts_to r_after #(1.0R /. 2.0R) ia_u);
        R.gather r_after;
        rewrite (R.pts_to r_after #(1.0R /. 2.0R +. 1.0R /. 2.0R) ml_b)
          as (R.pts_to r_after ml_b);
        I.mixed_list_match_n_length RawMatch.cbor_raw_match SpecEP.parse_raw_data_item (I.append_off_before 0 (SZ.v 0sz) (SZ.v len_a)) (I.append_n_before 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a)) 1.0R ib_u l1_u;
        I.mixed_list_match_n_length RawMatch.cbor_raw_match SpecEP.parse_raw_data_item (I.append_off_after 0 (SZ.v 0sz) (SZ.v len_a)) (I.append_n_after 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a)) 1.0R ia_u l2_u;
        rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item (I.append_off_before 0 (SZ.v 0sz) (SZ.v len_a)) (I.append_n_before 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a)) 1.0R ib_u l1_u)
          as (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_a l1_u);
        rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecEP.parse_raw_data_item (I.append_off_after 0 (SZ.v 0sz) (SZ.v len_a)) (I.append_n_after 0 (SZ.v (IT.mixed_list_length ml_res)) (SZ.v len_a)) 1.0R ia_u l2_u)
          as (I.mixed_list_match RawMatch.cbor_raw_match SpecEP.parse_raw_data_item 1.0R ml_b l2_u);
        (* relate split lists to the spec lists *)
        L.map_append SpecRaw.mk_cbor l1_u l2_u;
        List.Tot.Properties.append_injective
          (L.map SpecRaw.mk_cbor l1_u) (Ghost.reveal l1)
          (L.map SpecRaw.mk_cbor l2_u) (Ghost.reveal l2);
        L.for_all_append SpecRaw.valid_raw_data_item l1_u l2_u;
        (* rebuild ownership (let Pulse infer the plain list from the resource) *)
        rebuild_owned x1 ml_a la64;
        rebuild_owned x2 ml_b lb64;
        fold (cbor_nondet_array_owned x1 l1);
        fold (cbor_nondet_array_owned x2 l2);
        fold (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va);
      };
    Some #cbor_nondet_t res
  }
}

#pop-options

(* ================================================================ *)
(* Finalize                                                         *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

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
{
  unfold (cbor_nondet_array_owned x l);
  with lraw. assert (AB.cbor_array_owned x lraw);
  AB.cbor_array_owned_length_fits x;
  unfold (AB.cbor_array_owned x lraw);
  with xh. assert (RawMatch.cbor_raw_match 1.0R x xh);
  cbor_raw_match_get_header 1.0R x #xh;
  array_len_from_header (CBOR_Case_Array?.v x) xh;
  SpecRaw.valid_eq SpecRaw.basic_data_model xh;
  SpecRaw.mk_cbor_eq xh;
  assert (pure (L.length l == L.length lraw));
  let lw : Ghost.erased (l'': list Spec.cbor { FStar.UInt.fits (L.length l'') U64.n }) =
    Ghost.hide (Ghost.reveal l);
  assert (pure ((CBOR_Case_Array?.v x).cbor_array_length_size ==
    (Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (Ghost.reveal lw)))).size));
  fold (cbor_nondet_match 1.0R x (Spec.pack (Spec.CArray (Ghost.reveal lw))));
  Trade.intro_trade
    (cbor_nondet_match 1.0R x (Spec.pack (Spec.CArray (Ghost.reveal lw))))
    (cbor_nondet_array_owned x l)
    (pure (CBOR_Case_Array? x /\
           (CBOR_Case_Array?.v x).cbor_array_slice_perm == 1.0R /\
           (CBOR_Case_Array?.v x).cbor_array_length_size ==
             (Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (Ghost.reveal lw)))).size))
    fn _ {
      unfold (cbor_nondet_match 1.0R x (Spec.pack (Spec.CArray (Ghost.reveal lw))));
      with v''. assert (RawMatch.cbor_raw_match 1.0R x v'');
      cbor_raw_match_get_header 1.0R x #v'';
      Spec.unpack_pack (Spec.CArray (Ghost.reveal lw));
      SpecRaw.mk_cbor_eq v'';
      SpecRaw.valid_eq SpecRaw.basic_data_model v'';
      array_len_from_header (CBOR_Case_Array?.v x) v'';
      assert (pure (L.length lw == L.length (SpecRawBase.Array?.v v'')));
      assert (pure ((SpecRawBase.Array?.len v'' <: SpecRawBase.raw_uint64) ==
        Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (SpecRawBase.Array?.v v'')))));
      fold (AB.cbor_array_owned x (SpecRawBase.Array?.v v''));
      fold (cbor_nondet_array_owned x l);
    };
  ()
}

#pop-options


(* The length of an owned array fits in a u64 (needed to discharge the
   refinement of [cbor_nondet_array_finalize] after a chain of appends). *)
ghost
fn cbor_nondet_array_owned_length_fits
  (x: cbor_nondet_t) (#l: Ghost.erased (list Spec.cbor))
requires cbor_nondet_array_owned x l
ensures cbor_nondet_array_owned x l ** pure (FStar.UInt.fits (L.length (Ghost.reveal l)) U64.n)
{
  unfold (cbor_nondet_array_owned x l);
  AB.cbor_array_owned_length_fits x;
  fold (cbor_nondet_array_owned x l);
}

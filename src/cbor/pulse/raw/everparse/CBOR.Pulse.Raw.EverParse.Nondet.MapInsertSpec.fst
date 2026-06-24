module CBOR.Pulse.Raw.EverParse.Nondet.MapInsertSpec
#lang-pulse
friend CBOR.Pulse.API.Nondet.Common

(* NOTE on the Some-branch result value:

   The specification-level result of inserting (vk, vv) into the map [y] is
   [Spec.pack (Spec.CMap (Spec.cbor_map_union (CMap?.c (unpack y)) (singleton vk vv)))].
   Writing [Spec.CMap (...)] literally in the [ensures] triggers the refinement
   obligation [FStar.UInt.fits (cbor_map_length (...)) U64.n] at the
   ensures-well-formedness stage, which cannot be discharged abstractly (the
   function's precondition does not provide it).

   Following the deterministic bridge we therefore use the EXISTENTIAL form for
   the Some branch: we existentially quantify a spec value [vres : Spec.cbor]
   and merely assert, as a pure fact, that [CMap? (unpack vres)] holds and that
   [CMap?.c (unpack vres)] equals the union map.  This avoids ever writing
   [Spec.CMap (...)] literally and is equally strong for callers. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Nondet.Common
open CBOR.Pulse.Raw.EverParse.Type

module Spec = CBOR.Spec.API.Format
module SpecRaw = CBOR.Spec.Raw
module SpecRawBase = CBOR.Spec.Raw.Base
module Valid = CBOR.Spec.Raw.Valid
module MapPrepend = CBOR.Spec.Raw.MapPrepend
module MI = CBOR.Pulse.Raw.EverParse.Nondet.MapInsert
module RawMatch = CBOR.Pulse.Raw.EverParse.Match
module RawType = CBOR.Pulse.Raw.EverParse.Type
module Optimal = CBOR.Spec.Raw.Optimal
module IT = LowParse.PulseParse.Iterator.Type
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module L = FStar.List.Tot
module U64 = FStar.UInt64
module SZ = FStar.SizeT

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

(* From validity of the prepended map, derive absence of the fresh key (up to
   raw_equiv) from the existing keys.  [valid_eq] unfolds map validity to a
   [list_no_setoid_repeats] over the keys, whose head-vs-tail clause is exactly
   the [not existsb] absence fact. *)
let some_absence
  (xh_result: SpecRawBase.raw_data_item)
  (vkr vvr: SpecRawBase.raw_data_item)
  (rest: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
: Lemma
  (requires (
    SpecRawBase.Map? xh_result /\
    Valid.valid_raw_data_item xh_result == true /\
    (SpecRawBase.Map?.v xh_result <: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
      == (vkr, vvr) :: rest
  ))
  (ensures (~ (L.existsb (Valid.raw_equiv vkr) (L.map fst rest))))
= Valid.valid_eq Valid.basic_data_model xh_result

(* Union bridge for the Some branch: prepending a fresh (vkr, vvr) entry to a
   valid map corresponds, abstractly, to a left-biased union with the singleton
   {mk_cbor vkr -> mk_cbor vvr}. *)
let some_union
  (xh xh_result vkr vvr: SpecRawBase.raw_data_item)
: Lemma
  (requires (
    SpecRawBase.Map? xh /\ SpecRawBase.Map? xh_result /\
    Valid.valid_raw_data_item xh == true /\
    Valid.valid_raw_data_item xh_result == true /\
    Valid.valid_raw_data_item vkr == true /\
    Valid.valid_raw_data_item vvr == true /\
    (SpecRawBase.Map?.v xh_result <: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
      == (vkr, vvr) :: (SpecRawBase.Map?.v xh <: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
  ))
  (ensures (
    Spec.CMap? (Spec.unpack (SpecRaw.mk_cbor xh)) /\
    Spec.CMap? (Spec.unpack (SpecRaw.mk_cbor xh_result)) /\
    (Spec.CMap?.c (Spec.unpack (SpecRaw.mk_cbor xh_result)) <: Spec.cbor_map) ==
      Spec.cbor_map_union
        (Spec.CMap?.c (Spec.unpack (SpecRaw.mk_cbor xh)))
        (Spec.cbor_map_singleton (SpecRaw.mk_cbor vkr) (SpecRaw.mk_cbor vvr))
  ))
= some_absence xh_result vkr vvr (SpecRawBase.Map?.v xh);
  assert (xh == SpecRawBase.Map (SpecRawBase.Map?.len xh) (SpecRawBase.Map?.v xh));
  assert (xh_result == SpecRawBase.Map (SpecRawBase.Map?.len xh_result) (SpecRawBase.Map?.v xh_result));
  MapPrepend.mk_cbor_map_prepend
    (SpecRawBase.Map?.len xh) (SpecRawBase.Map?.v xh)
    vkr vvr
    (SpecRawBase.Map?.len xh_result)

(* Disjunction bridge for the None branch. *)
let none_bridge
  (xh vkr: SpecRawBase.raw_data_item)
  (y vk: Spec.cbor)
: Lemma
  (requires (
    SpecRawBase.Map? xh /\
    Valid.valid_raw_data_item xh == true /\
    Valid.valid_raw_data_item vkr == true /\
    SpecRaw.mk_cbor xh == y /\ SpecRaw.mk_cbor vkr == vk /\
    Spec.CMap? (Spec.unpack y) /\
    (L.existsb (Valid.raw_equiv vkr) (L.map fst (MI.map_payload xh)) \/
     ~ (FStar.UInt.fits (L.length (MI.map_payload xh) + 1) 64))
  ))
  (ensures (
    Spec.cbor_map_defined vk (Spec.CMap?.c (Spec.unpack y)) \/
    ~ (FStar.UInt.fits (Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack y)) + 1) U64.n)
  ))
= assert (xh == SpecRawBase.Map (SpecRawBase.Map?.len xh) (SpecRawBase.Map?.v xh));
  assert (MI.map_payload xh == (SpecRawBase.Map?.v xh <: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)));
  if L.existsb (Valid.raw_equiv vkr) (L.map fst (MI.map_payload xh))
  then
    MapPrepend.mk_cbor_map_defined_of_existsb
      (SpecRawBase.Map?.len xh) (SpecRawBase.Map?.v xh) vkr
  else
    SpecRaw.mk_cbor_eq xh

inline_for_extraction
fn cbor_nondet_map_entry_insert_spec
  (f64: squash SZ.fits_u64)
  (x key value: cbor_nondet_t)
  (r1 r2: R.ref (IT.mixed_list (cbor_map_entry cbor_raw)))
  (ry: R.ref (cbor_map_entry cbor_raw))
  (#p: perm) (#y: Ghost.erased (v: Spec.cbor { Spec.CMap? (Spec.unpack v) }))
  (#pkv: perm) (#vk #vv: Ghost.erased Spec.cbor)
requires
  cbor_nondet_match p x y **
  cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
  (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy) **
  pure (Spec.CMap? (Spec.unpack y))
returns res: option cbor_nondet_t
ensures (match res with
  | None ->
    cbor_nondet_match p x y **
    cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
    (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy) **
    pure (Spec.cbor_map_defined vk (Spec.CMap?.c (Spec.unpack y)) \/
          ~ (FStar.UInt.fits (Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack y)) + 1) U64.n))
  | Some m ->
    exists* (p_res: perm) (vres: Spec.cbor).
      cbor_nondet_match p_res m vres **
      Trade.trade
        (cbor_nondet_match p_res m vres)
        (cbor_nondet_match p x y **
         cbor_nondet_match pkv key vk ** cbor_nondet_match pkv value vv **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy)) **
      pure (Spec.CMap? (Spec.unpack vres) /\
            (Spec.CMap?.c (Spec.unpack vres) <: Spec.cbor_map) ==
              Spec.cbor_map_union (Spec.CMap?.c (Spec.unpack y)) (Spec.cbor_map_singleton vk vv)))
{
  (* Go to the raw level for each input, threading the restore-trades. *)
  let xh = cbor_nondet_match_elim x;
  let vkr = cbor_nondet_match_elim key;
  let vvr = cbor_nondet_match_elim value;
  (* The raw witness of [x] is a Map, since its spec value is a CMap. *)
  SpecRaw.mk_cbor_eq (Ghost.reveal xh);
  assert (pure (SpecRawBase.Map? (Ghost.reveal xh)));
  (* Run the verified raw core; implicits #xh/#vk/#vv are read off the
     cbor_raw_match slprops in context. *)
  let res = MI.cbor_raw_nondet_map_entry_insert f64 x key value r1 r2 ry;
  match res {
    None -> {
      none_bridge (Ghost.reveal xh) (Ghost.reveal vkr) (Ghost.reveal y) (Ghost.reveal vk);
      Trade.elim (RawMatch.cbor_raw_match p x (Ghost.reveal xh)) (cbor_nondet_match p x y);
      Trade.elim (RawMatch.cbor_raw_match pkv key (Ghost.reveal vkr)) (cbor_nondet_match pkv key vk);
      Trade.elim (RawMatch.cbor_raw_match pkv value (Ghost.reveal vvr)) (cbor_nondet_match pkv value vv);
      None #cbor_nondet_t
    }
    Some m -> {
      with pm_result xh_result. assert (
        RawMatch.cbor_raw_match pm_result m xh_result **
        Trade.trade
          (RawMatch.cbor_raw_match pm_result m xh_result)
          (RawMatch.cbor_raw_match p x (Ghost.reveal xh) **
           RawMatch.cbor_raw_match pkv key (Ghost.reveal vkr) **
           RawMatch.cbor_raw_match pkv value (Ghost.reveal vvr) **
           (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy))
      );
      assert (pure (MI.map_payload (Ghost.reveal xh) ==
        (SpecRawBase.Map?.v (Ghost.reveal xh) <: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))));
      assert (pure (
        (SpecRawBase.Map?.v xh_result <: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ==
        (Ghost.reveal vkr, Ghost.reveal vvr) ::
          (SpecRawBase.Map?.v (Ghost.reveal xh) <: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))));
      some_union (Ghost.reveal xh) xh_result (Ghost.reveal vkr) (Ghost.reveal vvr);
      (* Rebuild the nondet match for the result. *)
      cbor_nondet_match_intro m #pm_result #xh_result;
      (* p_res = pm_result /. 2.0R, vres = mk_cbor xh_result *)
      (* Compose the trades:
         T_intro : nondet_match p_res m vres ==> raw_match pm_result m xh_result
         T_raw   : raw_match pm_result m xh_result ==> (raw x ** raw key ** raw value ** refs) *)
      Trade.trans
        (cbor_nondet_match (pm_result /. 2.0R) m (SpecRaw.mk_cbor xh_result))
        (RawMatch.cbor_raw_match pm_result m xh_result)
        (RawMatch.cbor_raw_match p x (Ghost.reveal xh) **
         RawMatch.cbor_raw_match pkv key (Ghost.reveal vkr) **
         RawMatch.cbor_raw_match pkv value (Ghost.reveal vvr) **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy));
      (* Upgrade each raw match back to its nondet match, leaving refs alone. *)
      Trade.refl (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy);
      Trade.prod
        (RawMatch.cbor_raw_match pkv value (Ghost.reveal vvr)) (cbor_nondet_match pkv value vv)
        (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy)
        (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy);
      Trade.prod
        (RawMatch.cbor_raw_match pkv key (Ghost.reveal vkr)) (cbor_nondet_match pkv key vk)
        (RawMatch.cbor_raw_match pkv value (Ghost.reveal vvr) **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy))
        (cbor_nondet_match pkv value vv **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy));
      Trade.prod
        (RawMatch.cbor_raw_match p x (Ghost.reveal xh)) (cbor_nondet_match p x y)
        (RawMatch.cbor_raw_match pkv key (Ghost.reveal vkr) **
         RawMatch.cbor_raw_match pkv value (Ghost.reveal vvr) **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy))
        (cbor_nondet_match pkv key vk **
         cbor_nondet_match pkv value vv **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy));
      Trade.trans
        (cbor_nondet_match (pm_result /. 2.0R) m (SpecRaw.mk_cbor xh_result))
        (RawMatch.cbor_raw_match p x (Ghost.reveal xh) **
         RawMatch.cbor_raw_match pkv key (Ghost.reveal vkr) **
         RawMatch.cbor_raw_match pkv value (Ghost.reveal vvr) **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy))
        (cbor_nondet_match p x y **
         cbor_nondet_match pkv key vk **
         cbor_nondet_match pkv value vv **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy));
      Some #cbor_nondet_t m
    }
  }
}

#pop-options

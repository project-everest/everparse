module CBOR.Pulse.Raw.EverParse.Det.MapInsertSpec
#lang-pulse
friend CBOR.Pulse.API.Det.Type
friend CBOR.Pulse.Raw.EverParse.Det.Impl

(* NOTE on the Some-branch result value:

   The specification-level result of inserting (vk, vv) into the map [y] is
   [Spec.pack (Spec.CMap (Spec.cbor_map_union (CMap?.c (unpack y)) (singleton vk vv)))].
   Writing [Spec.CMap (...)] literally in the [ensures] triggers the refinement
   obligation [FStar.UInt.fits (cbor_map_length (...)) U64.n] at the
   ensures-well-formedness stage, which cannot be discharged abstractly (the
   function's precondition does not provide it).

   Following the task guidance we therefore use the EXISTENTIAL form for the
   Some branch: we existentially quantify a spec value [vres : Spec.cbor] and
   merely assert, as a pure fact, that [CMap? (unpack vres)] holds and that
   [CMap?.c (unpack vres)] equals the union map.  This avoids ever writing
   [Spec.CMap (...)] literally and is equally strong for callers. *)

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Det.Type
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Det.Impl

module Spec = CBOR.Spec.API.Format
module SpecRaw = CBOR.Spec.Raw
module SpecRawBase = CBOR.Spec.Raw.Base
module SpecMap = CBOR.Spec.Raw.Map
module MapLexInsert = CBOR.Spec.Raw.MapLexInsert
module RF = CBOR.Spec.Raw.Format
module MI = CBOR.Pulse.Raw.EverParse.Det.MapInsert
module RawMatch = CBOR.Pulse.Raw.EverParse.Match
module Optimal = CBOR.Spec.Raw.Optimal
module Valid = CBOR.Spec.Raw.Valid
module IT = LowParse.PulseParse.Iterator.Type
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module L = FStar.List.Tot
module U64 = FStar.UInt64
module SZ = FStar.SizeT

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

let order0_eq ()
: Lemma (MapLexInsert.order0 == RF.deterministically_encoded_cbor_map_key_order)
= assert_norm (MapLexInsert.order0 == RF.deterministically_encoded_cbor_map_key_order)

inline_for_extraction
fn cbor_det_map_entry_insert_spec
  (f64: squash SZ.fits_u64)
  (x key value: cbor_det_t)
  (r1 r2 r3 r4: R.ref (IT.mixed_list (cbor_map_entry cbor_raw)))
  (ry: R.ref (cbor_map_entry cbor_raw))
  (#p: perm) (#y: Ghost.erased (v: Spec.cbor { Spec.CMap? (Spec.unpack v) }))
  (#pkv: perm) (#vk #vv: Ghost.erased Spec.cbor)
requires
  cbor_det_match p x y **
  cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
  (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy) **
  pure (Spec.CMap? (Spec.unpack y))
returns res: option cbor_det_t
ensures (match res with
  | None ->
    cbor_det_match p x y **
    cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
    (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy) **
    pure (Spec.cbor_map_defined vk (Spec.CMap?.c (Spec.unpack y)) \/
          ~ (FStar.UInt.fits (Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack y)) + 1) U64.n))
  | Some m ->
    exists* (p_res: perm) (vres: Spec.cbor).
      cbor_det_match p_res m vres **
      Trade.trade
        (cbor_det_match p_res m vres)
        (cbor_det_match p x y **
         cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
         (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy)) **
      pure (Spec.CMap? (Spec.unpack vres) /\
            (Spec.CMap?.c (Spec.unpack vres) <: Spec.cbor_map) ==
              Spec.cbor_map_union (Spec.CMap?.c (Spec.unpack y)) (Spec.cbor_map_singleton vk vv)))
{
  let m_hl : Ghost.erased Spec.cbor_map =
    Ghost.hide (Spec.CMap?.c (Spec.unpack (Ghost.reveal y)));
  (* Learn the shape of the raw encoding of [y]. *)
  SpecRaw.mk_cbor_eq_map (Ghost.reveal y);
  assert (pure (SpecRawBase.Map? (SpecRaw.mk_det_raw_cbor (Ghost.reveal y))));
  assert (pure (SpecRawBase.Map?.v (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)) ==
                SpecRaw.mk_det_raw_cbor_map_raw (Ghost.reveal m_hl)));
  assert (pure (L.sorted (Valid.map_entry_order RF.deterministically_encoded_cbor_map_key_order _)
                  (SpecRawBase.Map?.v (SpecRaw.mk_det_raw_cbor (Ghost.reveal y))) == true));
  order0_eq ();
  assert (pure (L.sorted (Valid.map_entry_order MapLexInsert.order0 _)
                  (SpecRawBase.Map?.v (SpecRaw.mk_det_raw_cbor (Ghost.reveal y))) == true));
  (* Run the verified raw core.  Implicits are inferred from the unfolded
     cbor_det_match (#xh = mk_det_raw_cbor y, #vk = mk_det_raw_cbor vk, ...). *)
  let res = MI.cbor_raw_det_map_entry_insert f64 x key value r1 r2 r3 r4 ry;
  match res {
    None -> {
      (* Bridge the raw None-disjunction to the Spec level. *)
      let _ = RF.lemma_compare_prop;
      SpecMap.map_insert_sorted
        RF.deterministically_encoded_cbor_map_key_order
        RF.cbor_compare
        (SpecRaw.mk_det_raw_cbor_map_raw (Ghost.reveal m_hl))
        (SpecRaw.mk_det_raw_cbor (Ghost.reveal vk), SpecRaw.mk_det_raw_cbor (Ghost.reveal vv));
      SpecRaw.mk_det_raw_cbor_map_raw_snoc (Ghost.reveal m_hl) (Ghost.reveal vk) (Ghost.reveal vv);
      None #cbor_det_t
    }
    Some m -> {
      with pm_result xh_result. assert (
        RawMatch.cbor_raw_match pm_result m xh_result **
        Trade.trade
          (RawMatch.cbor_raw_match pm_result m xh_result)
          (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)) **
           RawMatch.cbor_raw_match pkv key (SpecRaw.mk_det_raw_cbor (Ghost.reveal vk)) **
           RawMatch.cbor_raw_match pkv value (SpecRaw.mk_det_raw_cbor (Ghost.reveal vv)) **
           (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy))
      );
      (* The inserted key was absent (Some? path), so we can build the union. *)
      SpecRaw.mk_det_raw_cbor_map_raw_snoc (Ghost.reveal m_hl) (Ghost.reveal vk) (Ghost.reveal vv);
      let m_union : Ghost.erased Spec.cbor_map =
        Ghost.hide (Spec.cbor_map_union (Ghost.reveal m_hl)
                      (Spec.cbor_map_singleton (Ghost.reveal vk) (Ghost.reveal vv)));
      (* map_payload xh_result == mk_det_raw_cbor_map_raw m_union *)
      assert (pure (MI.map_payload xh_result == SpecRaw.mk_det_raw_cbor_map_raw (Ghost.reveal m_union)));
      (* Key absent ==> the maps are disjoint, so length is additive. *)
      assert (pure (~ (Spec.cbor_map_defined (Ghost.reveal vk) (Ghost.reveal m_hl))));
      Spec.cbor_map_length_singleton (Ghost.reveal vk) (Ghost.reveal vv);
      assert (pure (Spec.cbor_map_disjoint (Ghost.reveal m_hl)
                      (Spec.cbor_map_singleton (Ghost.reveal vk) (Ghost.reveal vv))));
      Spec.cbor_map_length_disjoint_union (Ghost.reveal m_hl)
        (Spec.cbor_map_singleton (Ghost.reveal vk) (Ghost.reveal vv));
      (* fits: length of result fits u64 (from the raw post conjunct). *)
      assert (pure (L.length (MI.map_payload xh_result) ==
                    Spec.cbor_map_length (Ghost.reveal m_union)));
      assert (pure (FStar.UInt.fits (Spec.cbor_map_length (Ghost.reveal m_union)) U64.n));
      (* Construct the spec result value. *)
      let cm : Ghost.erased Spec.cbor_case = Ghost.hide (Spec.CMap (Ghost.reveal m_union));
      let vres : Ghost.erased Spec.cbor = Ghost.hide (Spec.pack (Ghost.reveal cm));
      Spec.unpack_pack (Ghost.reveal cm);
      assert (pure (Spec.CMap? (Spec.unpack (Ghost.reveal vres))));
      assert (pure (Spec.CMap?.c (Spec.unpack (Ghost.reveal vres)) == Ghost.reveal m_union));
      (* Relate xh_result to mk_det_raw_cbor vres. *)
      SpecRaw.mk_cbor_eq_map (Ghost.reveal vres);
      assert (pure (xh_result == SpecRaw.mk_det_raw_cbor (Ghost.reveal vres)));
      rewrite (RawMatch.cbor_raw_match pm_result m xh_result)
        as (RawMatch.cbor_raw_match pm_result m (SpecRaw.mk_det_raw_cbor (Ghost.reveal vres)));
      fold (cbor_det_match pm_result m (Ghost.reveal vres));
      (* Lift the raw restore-trade to the Spec level. *)
      Trade.intro_trade
        (cbor_det_match pm_result m (Ghost.reveal vres))
        (cbor_det_match p x y **
         cbor_det_match pkv key vk ** cbor_det_match pkv value vv **
         (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy))
        (Trade.trade
          (RawMatch.cbor_raw_match pm_result m xh_result)
          (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)) **
           RawMatch.cbor_raw_match pkv key (SpecRaw.mk_det_raw_cbor (Ghost.reveal vk)) **
           RawMatch.cbor_raw_match pkv value (SpecRaw.mk_det_raw_cbor (Ghost.reveal vv)) **
           (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy)))
        fn _ {
          unfold (cbor_det_match pm_result m (Ghost.reveal vres));
          rewrite (RawMatch.cbor_raw_match pm_result m (SpecRaw.mk_det_raw_cbor (Ghost.reveal vres)))
            as (RawMatch.cbor_raw_match pm_result m xh_result);
          Trade.elim
            (RawMatch.cbor_raw_match pm_result m xh_result)
            (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor (Ghost.reveal y)) **
             RawMatch.cbor_raw_match pkv key (SpecRaw.mk_det_raw_cbor (Ghost.reveal vk)) **
             RawMatch.cbor_raw_match pkv value (SpecRaw.mk_det_raw_cbor (Ghost.reveal vv)) **
             (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy));
          fold (cbor_det_match p x y);
          fold (cbor_det_match pkv key vk);
          fold (cbor_det_match pkv value vv);
        };
      Some #cbor_det_t m
    }
  }
}

#pop-options

module CBOR.SteelST.Map.Iterator.Init.Map
open CBOR.SteelST.Map.Base

open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Map.Base
open CBOR.SteelST.Type.Def

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let cbor_map_iterator_init_map
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { Cbor.Map? v /\ CBOR_Case_Map? a })
: STT cbor_map_iterator_t
    (raw_data_item_match p a v)
    (fun i ->
      cbor_map_iterator_match p i (Cbor.Map?.v v) `star`
      (cbor_map_iterator_match p i (Cbor.Map?.v v) `implies_`
        raw_data_item_match p a v)
    )
= raw_data_item_match_perm_le_full_perm a;
  let len = cbor_map_length a in
  let ar = destr_cbor_map a in
  let fp = GR.alloc () in // I could reuse the footprint from `a`, but `destr_cbor_map` does not expose it
  gref_lower_perm fp p;
  let res = {
    cbor_map_iterator_length = len;
    cbor_map_iterator_payload = CBOR_Map_Iterator_Payload_Map ar.cbor_map_payload ar.footprint;
    footprint = fp;
  }
  in
  vpattern_rewrite_with_implies (fun r -> GR.pts_to r _ _) res.footprint;
  implies_trans (GR.pts_to res.footprint p ()) (GR.pts_to fp p ()) (GR.pts_to fp full_perm ());
  rewrite_with_implies
    (cbor_map_iterator_match_map p res (maybe_cbor_map v))
    (cbor_map_iterator_match p res (Cbor.Map?.v v));
  intro_implies
    (cbor_map_iterator_match_map p res (maybe_cbor_map v))
    (A.pts_to ar.cbor_map_payload p ar.footprint `star`
      raw_data_item_map_match p ar.footprint (maybe_cbor_map v)
    )
    (GR.pts_to res.footprint p () `implies_` GR.pts_to fp full_perm ())
    (fun _ ->
      let _ = gen_elim () in
      elim_implies (GR.pts_to _ _ _) (GR.pts_to _ _ _);
      GR.free _;
      rewrite
        (A.pts_to _ _ _)
        (A.pts_to ar.cbor_map_payload p ar.footprint);
      rewrite
        (raw_data_item_map_match p _ _)
        (raw_data_item_map_match p ar.footprint (maybe_cbor_map v))
    );
  implies_trans
    (cbor_map_iterator_match_map p res (maybe_cbor_map v))
    (A.pts_to ar.cbor_map_payload p ar.footprint `star`
      raw_data_item_map_match p ar.footprint (maybe_cbor_map v)
    )
    (raw_data_item_match p a v);
  implies_trans
    (cbor_map_iterator_match p res (Cbor.Map?.v v))
    (cbor_map_iterator_match_map p res (maybe_cbor_map v))
    (raw_data_item_match p a v);
  return res

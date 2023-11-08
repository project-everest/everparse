module CBOR.SteelST.Map.Iterator.Init.Serialized
open CBOR.SteelST.Map.Base

open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Map.Base

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

#push-options "--z3rlimit 64"
#restart-solver

let cbor_map_iterator_init_serialized
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { Cbor.Map? v /\ CBOR_Case_Serialized? a })
: STT cbor_map_iterator_t
    (raw_data_item_match p a v)
    (fun i ->
      cbor_map_iterator_match p i (Cbor.Map?.v v) `star`
      (cbor_map_iterator_match p i (Cbor.Map?.v v) `implies_`
        raw_data_item_match p a v)
    )
= raw_data_item_match_perm_le_full_perm a;
  let len = cbor_map_length a in
  let s = destr_cbor_serialized a in
  let _ = gen_elim () in
  let ar = CBOR.SteelST.Raw.Map.focus_map_with_ghost_length s.cbor_serialized_payload (U64.v len) in
  let _ = gen_elim () in
  implies_trans
    (LPS.aparse (LPS.parse_nlist (U64.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _ _)
    (LPS.aparse CborST.parse_raw_data_item _ _)
    (raw_data_item_match p a v);
  let var0 = vpattern (LPS.aparse (LPS.parse_nlist (U64.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _) in
  let fp = GR.alloc () in // same as above, I could use the footprint from `a` but `destr_cbor_serialized` does not expose it
  gref_lower_perm fp p;
  [@@inline_let]
  let res = {
    cbor_map_iterator_length = len;
    cbor_map_iterator_payload = CBOR_Map_Iterator_Payload_Serialized ar (LPA.set_array_perm (LPS.array_of var0) (LPA.array_perm (LPS.array_of var0) `div_perm` p));
    footprint = fp;
  }
  in
  vpattern_rewrite_with_implies (fun r -> GR.pts_to r _ _) res.footprint;
  implies_trans (GR.pts_to res.footprint p ()) (GR.pts_to fp p ()) (GR.pts_to fp full_perm ());
  let var = LPS.rewrite_aparse_with_implies ar (LPS.parse_nlist (U64.v res.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) in
  implies_trans
    (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) ar var)
    (LPS.aparse (LPS.parse_nlist (U64.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _ _)
    (raw_data_item_match p a v);
  rewrite_with_implies
    (cbor_map_iterator_match_serialized p res (Cbor.Map?.v v))
    (cbor_map_iterator_match p res (Cbor.Map?.v v));
  intro_implies
    (cbor_map_iterator_match_serialized p res (Cbor.Map?.v v))
    (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) ar var)
    (GR.pts_to res.footprint p () `implies_` GR.pts_to fp full_perm ())
    (fun _ ->
      let _ = gen_elim () in
      elim_implies (GR.pts_to _ _ _) (GR.pts_to _ _ _);
      GR.free _;
      rewrite
        (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _ _)
        (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) ar var)
    );
  implies_trans
    (cbor_map_iterator_match p res (Cbor.Map?.v v))
    (cbor_map_iterator_match_serialized p res (Cbor.Map?.v v))
    (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) ar var);
  implies_trans
    (cbor_map_iterator_match p res (Cbor.Map?.v v))
    (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) ar var)
    (raw_data_item_match p a v);
  return res

#pop-options

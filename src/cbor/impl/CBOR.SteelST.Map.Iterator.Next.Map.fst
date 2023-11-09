module CBOR.SteelST.Map.Iterator.Next.Map
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

#push-options "--z3rlimit 64"
#restart-solver

let cbor_map_iterator_match_map_elim
  (#opened: _)
  (p: perm)
  (c: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: STGhost (squash (CBOR_Map_Iterator_Payload_Map? c.cbor_map_iterator_payload)) opened
    (cbor_map_iterator_match_map p c l)
    (fun _ ->
      GR.pts_to c.footprint p () `star`
      A.pts_to (CBOR_Map_Iterator_Payload_Map?.payload c.cbor_map_iterator_payload) p (CBOR_Map_Iterator_Payload_Map?.footprint c.cbor_map_iterator_payload) `star`
      raw_data_item_map_match p (CBOR_Map_Iterator_Payload_Map?.footprint c.cbor_map_iterator_payload) l
    )
    True
    (fun _ ->
      U64.v c.cbor_map_iterator_length == List.Tot.length l
    )
= let _ = gen_elim () in
  let res : squash (CBOR_Map_Iterator_Payload_Map? c.cbor_map_iterator_payload) = () in
  rewrite (A.pts_to _ p _) (A.pts_to (CBOR_Map_Iterator_Payload_Map?.payload c.cbor_map_iterator_payload) p (CBOR_Map_Iterator_Payload_Map?.footprint c.cbor_map_iterator_payload));
  rewrite (raw_data_item_map_match p _ _) (raw_data_item_map_match p (CBOR_Map_Iterator_Payload_Map?.footprint c.cbor_map_iterator_payload) l);
  res

let cbor_map_iterator_next_map
  (#p: perm)
  (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (#i1 #i2: Ghost.erased cbor_map_iterator_t)
  (i: cbor_map_iterator_t { i == Ghost.reveal i2 })
  (pi: R.ref cbor_map_iterator_t { Cons? l /\ CBOR_Map_Iterator_Payload_Map? i.cbor_map_iterator_payload })
: STT cbor_map_entry
    (R.pts_to pi full_perm i1 `star` cbor_map_iterator_match p i2 l)
    (fun c -> exists_ (fun i' ->
      R.pts_to pi full_perm i' `star`
      raw_data_item_map_entry_match p c (List.Tot.hd l) `star`
      cbor_map_iterator_match p i' (List.Tot.tl l) `star`
      ((raw_data_item_map_entry_match p c (List.Tot.hd l) `star`
        cbor_map_iterator_match p i' (List.Tot.tl l)) `implies_`
        cbor_map_iterator_match p i2 l
      )
    ))
= rewrite_with_implies
    (cbor_map_iterator_match p _ l)
    (cbor_map_iterator_match_map p i l);
  let _ = cbor_map_iterator_match_map_elim p i l in
  let a = match i.cbor_map_iterator_payload with
  | CBOR_Map_Iterator_Payload_Map payload _ -> payload
  in
  let fp : Ghost.erased _ = CBOR_Map_Iterator_Payload_Map?.footprint i.cbor_map_iterator_payload in
  rewrite
    (A.pts_to _ p _)
    (A.pts_to a p fp);
  rewrite
    (raw_data_item_map_match p _ _)
    (raw_data_item_map_match p fp l);
  intro_implies
    ((A.pts_to a p fp `star` GR.pts_to i.footprint p ()) `star` raw_data_item_map_match p fp l)
    (cbor_map_iterator_match_map p i l)
    emp
    (fun _ -> noop (); noop ());
  implies_trans
    ((A.pts_to a p fp `star` GR.pts_to i.footprint p ()) `star` raw_data_item_map_match p fp l)
    (cbor_map_iterator_match_map p i l)
    (cbor_map_iterator_match p _ l);
  let len' = i.cbor_map_iterator_length `U64.sub` 1uL in
  SM.seq_list_match_cons_eq  fp l (raw_data_item_map_entry_match p);
  Seq.seq_of_list_tl l;
  SM.seq_list_match_length (raw_data_item_map_entry_match p) _ _;
  A.pts_to_length _ _;
  rewrite_with_implies
    (raw_data_item_map_match p fp l)
    (SM.seq_list_match_cons0 fp l (raw_data_item_map_entry_match p) SM.seq_list_match);
  implies_trans_r1
    (A.pts_to a _ _ `star` GR.pts_to i.footprint _ _)
    (SM.seq_list_match_cons0 fp l (raw_data_item_map_entry_match p) SM.seq_list_match)
    (raw_data_item_map_match p fp l)
    (cbor_map_iterator_match p _ _);
  let _ = gen_elim () in
  let res = A.index a 0sz in
  vpattern_rewrite (fun c1 -> raw_data_item_map_entry_match p c1 _) res;
  let c2 = vpattern_replace_erased (fun c2 -> SM.seq_list_match c2 (List.Tot.tl l) (raw_data_item_map_entry_match p)) in
  Seq.lemma_cons_inj (Seq.head fp) res (Seq.tail fp) c2;
  intro_implies
    (raw_data_item_map_entry_match p res (List.Tot.hd l) `star` SM.seq_list_match c2 (List.Tot.tl l) (raw_data_item_map_entry_match p))
    (SM.seq_list_match_cons0 fp l (raw_data_item_map_entry_match p) SM.seq_list_match)
    emp
    (fun _ -> noop (); noop ());
  rewrite_with_implies
    (SM.seq_list_match c2 (List.Tot.tl l) (raw_data_item_map_entry_match p))
    (raw_data_item_map_match p c2 (List.Tot.tl l));
  implies_trans_r1
    (raw_data_item_map_entry_match p res (List.Tot.hd l))
    (raw_data_item_map_match p c2 (List.Tot.tl l))
    (SM.seq_list_match c2 (List.Tot.tl l) (raw_data_item_map_entry_match p))
    (SM.seq_list_match_cons0 fp l (raw_data_item_map_entry_match p) SM.seq_list_match);
  let _ = A.ghost_split a 1sz in
  let ar' = A.split_r a 1sz in
  rewrite (A.pts_to (A.split_r a _) _ _) (A.pts_to ar' p (Ghost.reveal c2));
  intro_implies
    (A.pts_to ar' p c2)
    (A.pts_to a p fp)
    (A.pts_to (A.split_l a _) _ _)
    (fun _ ->
      let _ = A.ghost_join (A.split_l _ _) ar' () in
      rewrite
        (A.pts_to _ _ _)
        (A.pts_to a p fp)
    );
  implies_reg_r (A.pts_to ar' _ _) (A.pts_to a _ _) (GR.pts_to i.footprint _ _);
  implies_trans_l1
    (A.pts_to ar' p c2 `star` GR.pts_to i.footprint _ _)
    (A.pts_to a p fp `star` GR.pts_to i.footprint _ _)
    (SM.seq_list_match_cons0 fp l (raw_data_item_map_entry_match p) SM.seq_list_match)
    (cbor_map_iterator_match p _ l);
  implies_trans_r1
    (A.pts_to ar' p c2 `star` GR.pts_to i.footprint _ _)
    (raw_data_item_map_entry_match p res (List.Tot.hd l) `star` raw_data_item_map_match p c2 (List.Tot.tl l))
    (SM.seq_list_match_cons0 fp l (raw_data_item_map_entry_match p) SM.seq_list_match)
    (cbor_map_iterator_match p _ l);
  implies_with_tactic
    (raw_data_item_map_entry_match p res (List.Tot.hd l) `star` (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star` raw_data_item_map_match p c2 (List.Tot.tl l)))
    ((A.pts_to ar' p c2 `star` GR.pts_to i.footprint p ()) `star` (raw_data_item_map_entry_match p res (List.Tot.hd l) `star` raw_data_item_map_match p c2 (List.Tot.tl l)));
  implies_trans
    (raw_data_item_map_entry_match p res (List.Tot.hd l) `star` (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star` raw_data_item_map_match p c2 (List.Tot.tl l)))
    ((A.pts_to ar' p c2 `star` GR.pts_to i.footprint p ()) `star` (raw_data_item_map_entry_match p res (List.Tot.hd l) `star` raw_data_item_map_match p c2 (List.Tot.tl l)))
    (cbor_map_iterator_match p _ l);
  let i' = {
    cbor_map_iterator_length = len';
    cbor_map_iterator_payload = CBOR_Map_Iterator_Payload_Map ar' c2;
    footprint = i.footprint;
  }
  in
  R.write pi i';
  vpattern_rewrite_with_implies (fun r -> GR.pts_to r _ _) i'.footprint;
  rewrite_with_implies
    (cbor_map_iterator_match_map p i' (List.Tot.tl l))
    (cbor_map_iterator_match p i' (List.Tot.tl l));
  intro_implies
    (cbor_map_iterator_match_map p i' (List.Tot.tl l))
    (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star`  raw_data_item_map_match p c2 (List.Tot.tl l))
    (GR.pts_to i'.footprint p () `implies_` GR.pts_to i.footprint p ())
    (fun _ ->
      let _ = cbor_map_iterator_match_map_elim p i' (List.Tot.tl l) in
      elim_implies (GR.pts_to i'.footprint p ()) (GR.pts_to i.footprint p ());
      rewrite (A.pts_to _ p _) (A.pts_to ar' p c2);
      rewrite (raw_data_item_map_match p _ (List.Tot.tl l)) (raw_data_item_map_match p c2 (List.Tot.tl l))
    );
  implies_trans
    (cbor_map_iterator_match p i' (List.Tot.tl l))
    (cbor_map_iterator_match_map p i' (List.Tot.tl l))
    (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star` raw_data_item_map_match p c2 (List.Tot.tl l));
  implies_trans_r1
    (raw_data_item_map_entry_match p res (List.Tot.hd l))
    (cbor_map_iterator_match p i' (List.Tot.tl l))
    (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star` raw_data_item_map_match p c2 (List.Tot.tl l))
    (cbor_map_iterator_match p _ l);
  return res

#pop-options

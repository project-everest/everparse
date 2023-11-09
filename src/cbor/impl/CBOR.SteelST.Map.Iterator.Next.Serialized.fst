module CBOR.SteelST.Map.Iterator.Next.Serialized
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

let cbor_map_iterator_next_serialized
  (#p: perm)
  (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (#i1 #i2: Ghost.erased cbor_map_iterator_t)
  (i: cbor_map_iterator_t { i == Ghost.reveal i2 })
  (pi: R.ref cbor_map_iterator_t { Cons? l /\ CBOR_Map_Iterator_Payload_Serialized? i.cbor_map_iterator_payload })
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
    (cbor_map_iterator_match_serialized p i l);
  let _ = gen_elim () in
  GR.pts_to_perm i.footprint;
  let a = CBOR_Map_Iterator_Payload_Serialized?.payload i.cbor_map_iterator_payload in
  let va = vpattern_replace (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _) in
  vpattern_rewrite (fun a -> LPS.aparse (LPS.parse_nlist (U64.v i.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a _) a;
  intro_implies
    (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a va `star` GR.pts_to i.footprint p ())
    (cbor_map_iterator_match_serialized p i l)
    emp
    (fun _ -> noop (); noop ());
  implies_trans
    (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a va `star` GR.pts_to i.footprint p ())
    (cbor_map_iterator_match_serialized p i l)
    (cbor_map_iterator_match p i2 l);
  let len' = i.cbor_map_iterator_length `U64.sub` 1uL in
  let ga' = LPS.elim_nlist_cons
    (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)
    (U64.v i.cbor_map_iterator_length)
    (U64.v len')
    a
  in
  let _ = gen_elim () in
  let gar = LowParse.SteelST.Combinators.g_split_pair CborST.parse_raw_data_item CborST.parse_raw_data_item a in
  let _ = gen_elim () in  
  let sz_key = LPS.get_parsed_size CborST.jump_raw_data_item a in
  let ar = LPS.hop_aparse_aparse_with_size CborST.parse_raw_data_item CborST.parse_raw_data_item a sz_key gar in
  let sz_value = LPS.get_parsed_size CborST.jump_raw_data_item ar in
  let a' = LPS.hop_aparse_aparse_with_size CborST.parse_raw_data_item (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) ar sz_value ga' in
  let vkey = vpattern_replace (LPS.aparse CborST.parse_raw_data_item a) in
  let vvalue = vpattern_replace (LPS.aparse CborST.parse_raw_data_item ar) in
  let va1 = vpattern_replace (LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a') in
  intro_implies
    (LPS.aparse CborST.parse_raw_data_item a vkey `star` LPS.aparse CborST.parse_raw_data_item ar vvalue `star` LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va1)
    (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a va)
    emp
    (fun _ ->
      let _ = LowParse.SteelST.Combinators.merge_pair CborST.parse_raw_data_item CborST.parse_raw_data_item a ar in
      let _ = LPS.intro_nlist_cons (U64.v i.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item) (U64.v len') a a' in
      vpattern_rewrite
        (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a)
        va
    );
  implies_trans_l1
    (LPS.aparse CborST.parse_raw_data_item a vkey `star` LPS.aparse CborST.parse_raw_data_item ar vvalue `star` LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va1)
    (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a va)
    (GR.pts_to i.footprint p ())
    (cbor_map_iterator_match p i2 l);
  implies_with_tactic
    ((LPS.aparse CborST.parse_raw_data_item a vkey `star` LPS.aparse CborST.parse_raw_data_item ar vvalue) `star` (LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va1 `star` GR.pts_to i.footprint p ()))
    ((LPS.aparse CborST.parse_raw_data_item a vkey `star` LPS.aparse CborST.parse_raw_data_item ar vvalue `star` LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va1) `star` GR.pts_to i.footprint p ());
  implies_trans
    ((LPS.aparse CborST.parse_raw_data_item a vkey `star` LPS.aparse CborST.parse_raw_data_item ar vvalue) `star` (LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va1 `star` GR.pts_to i.footprint p ()))
    ((LPS.aparse CborST.parse_raw_data_item a vkey `star` LPS.aparse CborST.parse_raw_data_item ar vvalue `star` LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va1) `star` GR.pts_to i.footprint p ())
    (cbor_map_iterator_match p i2 l);
  let res_key = read_valid_cbor_from_buffer_with_size_strong p a sz_key in
  let res_value = read_valid_cbor_from_buffer_with_size_strong p ar sz_value in
  let res = mk_cbor_map_entry res_key res_value in
  rewrite_with_implies
    (raw_data_item_match p res_key _)
    (raw_data_item_match p (cbor_map_entry_key res) (fstp (List.Tot.hd l)));
  implies_trans
    (raw_data_item_match p (cbor_map_entry_key res) (fstp (List.Tot.hd l)))
    (raw_data_item_match p res_key _)
    (LPS.aparse CborST.parse_raw_data_item a _);
  rewrite_with_implies
    (raw_data_item_match p res_value _)
    (raw_data_item_match p (cbor_map_entry_value res) (sndp (List.Tot.hd l)));
  implies_trans
    (raw_data_item_match p (cbor_map_entry_value res) (sndp (List.Tot.hd l)))
    (raw_data_item_match p res_value _)
    (LPS.aparse CborST.parse_raw_data_item ar _);
  implies_join
    (raw_data_item_match p (cbor_map_entry_key res) (fstp (List.Tot.hd l)))
    (LPS.aparse CborST.parse_raw_data_item a _)
    (raw_data_item_match p (cbor_map_entry_value res) (sndp (List.Tot.hd l)))
    (LPS.aparse CborST.parse_raw_data_item ar _);
  implies_trans_l1
    (raw_data_item_map_entry_match p res (List.Tot.hd l))
    (LPS.aparse CborST.parse_raw_data_item a vkey `star` LPS.aparse CborST.parse_raw_data_item ar vvalue)
    (LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va1 `star` GR.pts_to i.footprint p ())
    (cbor_map_iterator_match p i2 l);
  let i' = {
    cbor_map_iterator_length = len';
    cbor_map_iterator_payload = CBOR_Map_Iterator_Payload_Serialized a' (LPA.set_array_perm (LPS.array_of va1) (LPA.array_perm (LPS.array_of va1) `div_perm` p));
    footprint = i.footprint;
  }
  in
  R.write pi i';
  vpattern_rewrite_with_implies (fun r -> GR.pts_to r _ _) i'.footprint;
  let va' = LPS.rewrite_aparse_with_implies a' (LPS.parse_nlist (U64.v i'.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) in
  implies_join
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va')
    (LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va1)
    (GR.pts_to i'.footprint p ())
    (GR.pts_to i.footprint p ());
  implies_trans_r1
    (raw_data_item_map_entry_match p res (List.Tot.hd l))
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va' `star` GR.pts_to i'.footprint p ())
    (LPS.aparse (LPS.parse_nlist (U64.v len') (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va1 `star` GR.pts_to i.footprint p ())
    (cbor_map_iterator_match p i2 l);
  rewrite_with_implies
    (cbor_map_iterator_match_serialized p i' (List.Tot.tl l))
    (cbor_map_iterator_match p i' (List.Tot.tl l));
  intro_implies
    (cbor_map_iterator_match_serialized p i' (List.Tot.tl l))
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va' `star` GR.pts_to i'.footprint p ())
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite
        (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _ _)
        (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va')
    );
  implies_trans
    (cbor_map_iterator_match p i' (List.Tot.tl l))
    (cbor_map_iterator_match_serialized p i' (List.Tot.tl l))
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va' `star` GR.pts_to i'.footprint p ());
  implies_trans_r1
    (raw_data_item_map_entry_match p res (List.Tot.hd l))
    (cbor_map_iterator_match p i' (List.Tot.tl l))
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a' va' `star` GR.pts_to i'.footprint p ())
    (cbor_map_iterator_match p i2 l);
  return res

#pop-options

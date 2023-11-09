module CBOR.SteelST.Map.Base
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Match
open CBOR.SteelST.Type.Def

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let destr_cbor_map
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_map
    (raw_data_item_match p a v)
    (fun res ->
      A.pts_to res.cbor_map_payload p res.footprint `star`
      LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match p) `star`
      ((A.pts_to res.cbor_map_payload p res.footprint `star`
        LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match p)) `implies_`
        raw_data_item_match p a v
      )
    )
    (CBOR_Case_Map? a)
    (fun res ->
      Cbor.Map? v /\
      U64.v res.cbor_map_length == List.Tot.length (Cbor.Map?.v v)
    )
= 
  let CBOR_Case_Map res fp = a in
  destr_cbor_map' a;
  assert_norm
    (raw_data_item_match p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)) ==
      raw_data_item_match_map0 p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)) (raw_data_item_map_match' p));
  rewrite
    (A.pts_to _ _ _)
    (A.pts_to res.cbor_map_payload p res.footprint);
  rewrite
    (LPS.seq_list_match _ (maybe_cbor_map v) (raw_data_item_map_entry_match p))
    (LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match p));
  
  intro_implies
    (A.pts_to res.cbor_map_payload p res.footprint `star`
      LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match p)
    )
    (raw_data_item_match p a v)
    (GR.pts_to _ _ _)
    (fun _ ->
      constr_cbor_map' p a v res.cbor_map_payload res.footprint (maybe_cbor_map v) _
    );
  return res

let cbor_map_length
  #p #v a
= raw_data_item_match_get_case a;
  match a with
  | CBOR_Case_Map _ _ ->
    let a' = destr_cbor_map a in
    elim_implies
      (A.pts_to _ _ _ `star` raw_data_item_map_match p _ _)
      (raw_data_item_match p _ _);
    return a'.cbor_map_length
  | _ ->
    let s = destr_cbor_serialized a in
    let _ = gen_elim () in
    let res = CborST.read_argument_as_uint64 s.cbor_serialized_payload in
    elim_implies
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match p _ _);
    return res

let dummy_cbor_map_iterator = {
  cbor_map_iterator_length = 0uL;
  cbor_map_iterator_payload = CBOR_Map_Iterator_Payload_Map A.null Seq.empty;
  footprint = dummy_cbor_footprint;
}

let cbor_map_iterator_match_map_prop
  (c: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (a: A.array cbor_map_entry)
  (fp: Seq.seq cbor_map_entry)
: Tot prop
=
      U64.v c.cbor_map_iterator_length == List.Tot.length l /\
      c.cbor_map_iterator_payload == CBOR_Map_Iterator_Payload_Map a (Ghost.hide fp)


[@@__reduce__]
let cbor_map_iterator_match_map
  (p: perm)
  (c: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
= exists_ (fun a -> exists_ (fun fp ->
    GR.pts_to c.footprint p () `star`
    A.pts_to a p fp `star`
    raw_data_item_map_match p fp l `star`
    pure (
    cbor_map_iterator_match_map_prop c l a fp
  )))

let cbor_map_iterator_match_serialized_prop
  (p: perm)
  (c: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (a: LPS.byte_array)
  (fp: LPS.v (LPS.parse_nlist_kind (U64.v c.cbor_map_iterator_length) (LPS.and_then_kind CborST.parse_raw_data_item_kind CborST.parse_raw_data_item_kind)) (LPS.nlist (U64.v c.cbor_map_iterator_length) (Cbor.raw_data_item & Cbor.raw_data_item)))
: Tot prop
= 
  fp.LPS.contents == l /\
  begin match c.cbor_map_iterator_payload with
  | CBOR_Map_Iterator_Payload_Serialized a' fp' ->
    a == a' /\
    LPS.array_of fp == LPA.set_array_perm fp' (p `prod_perm` LPA.array_perm fp')
  | _ -> False
  end

[@@__reduce__]
let cbor_map_iterator_match_serialized
  (p: perm)
  (c: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
= exists_ (fun a -> exists_ (fun fp ->
    GR.pts_to c.footprint p () `star`
    LPS.aparse (LPS.parse_nlist (U64.v c.cbor_map_iterator_length) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) a fp `star`
    pure (cbor_map_iterator_match_serialized_prop p c l a fp)
  ))

let cbor_map_iterator_match
  p c l
= match c.cbor_map_iterator_payload with
  | CBOR_Map_Iterator_Payload_Map _ _ -> cbor_map_iterator_match_map p c l
  | _ -> cbor_map_iterator_match_serialized p c l

#push-options "--z3rlimit 32"
#restart-solver

let cbor_map_iterator_match_length
  (#opened: _)
  (#p: perm)
  (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (i: cbor_map_iterator_t)
: STGhost unit opened
    (cbor_map_iterator_match p i l)
    (fun _ -> cbor_map_iterator_match p i l)
    True
    (fun _ -> U64.v i.cbor_map_iterator_length == List.Tot.length l)
= match i.cbor_map_iterator_payload with
  | CBOR_Map_Iterator_Payload_Map _ _ ->
    rewrite
      (cbor_map_iterator_match p i l)
      (cbor_map_iterator_match_map p i l);
    let _ = gen_elim () in
    rewrite
      (cbor_map_iterator_match_map p i l)
      (cbor_map_iterator_match p i l)
  | CBOR_Map_Iterator_Payload_Serialized _ _ ->
    rewrite
      (cbor_map_iterator_match p i l)
      (cbor_map_iterator_match_serialized p i l);
    let _ = gen_elim () in
    rewrite
      (cbor_map_iterator_match_serialized p i l)
      (cbor_map_iterator_match p i l)

#pop-options

module CBOR.SteelST.Map
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Map.Base

open CBOR.SteelST.Map.Iterator.Init.Map
open CBOR.SteelST.Map.Iterator.Init.Serialized
open CBOR.SteelST.Map.Iterator.Next.Map
open CBOR.SteelST.Map.Iterator.Next.Serialized
friend CBOR.SteelST.Map.Iterator.Init.Map
friend CBOR.SteelST.Map.Iterator.Init.Serialized
friend CBOR.SteelST.Map.Iterator.Next.Map
friend CBOR.SteelST.Map.Iterator.Next.Serialized

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

inline_for_extraction
noextract
let size_comp_for_map_entry
  (size:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_size_comp_for va c
  )
  (#p: perm)
  (va: Ghost.erased (Cbor.raw_data_item & Cbor.raw_data_item))
  (c: cbor_map_entry)
  (sz: SZ.t)
  (perr: R.ref bool)
: STT SZ.t
    (raw_data_item_map_entry_match p c (Ghost.reveal va) `star`
      R.pts_to perr full_perm false
    )
    (fun res ->
      raw_data_item_map_entry_match p c (Ghost.reveal va) `star`
      exists_ (fun err ->
        R.pts_to perr full_perm err `star`
        pure (LowParse.SteelST.Write.size_comp_for_post (LPS.serialize_nondep_then CborST.serialize_raw_data_item CborST.serialize_raw_data_item) va sz res err)
    ))
= LPS.serialize_nondep_then_eq CborST.serialize_raw_data_item CborST.serialize_raw_data_item va;
  let sz1 = size _ (cbor_map_entry_key c) sz perr in
  let _ = gen_elim () in
  let err = R.read perr in
  if err
  then begin
    noop ();
    noop ();
    return sz1
  end else begin
    noop ();
    let sz2 = size _ (cbor_map_entry_value c) sz1 perr in
    let _ = gen_elim () in
    noop ();
    return sz2
  end

let constr_cbor_map
  #c' #v' a len
= [@@inline_let]
  let ares : cbor_map = {
    cbor_map_length = len;
    cbor_map_payload = a;
    footprint = c';
  }
  in
  let fp = GR.alloc () in
  [@@inline_let]
  let res = CBOR_Case_Map ares fp in
  noop ();
  SM.seq_list_match_weaken
    c' v'
    (raw_data_item_map_entry_match full_perm)
    (raw_data_item_map_entry_match' v' (raw_data_item_match full_perm))
    (fun x y ->
      rewrite
        (raw_data_item_map_entry_match full_perm x y)
        (raw_data_item_map_entry_match' v' (raw_data_item_match full_perm) x y)
    );
  rewrite_with_implies_with_tactic
    (raw_data_item_match_map0 full_perm (CBOR_Case_Map ares fp) (Cbor.Map v') (raw_data_item_map_match' full_perm))
    (raw_data_item_match full_perm (CBOR_Case_Map ares fp) (Cbor.Map v'));
  rewrite_with_implies
    (raw_data_item_match full_perm (CBOR_Case_Map ares fp) (Cbor.Map v'))
    (raw_data_item_match full_perm res (Cbor.Map v'));
  implies_trans
    (raw_data_item_match full_perm res (Cbor.Map v'))
    (raw_data_item_match full_perm (CBOR_Case_Map ares fp) (Cbor.Map v'))
    (raw_data_item_match_map0 full_perm (CBOR_Case_Map ares fp) (Cbor.Map v') (raw_data_item_map_match' full_perm));
  intro_implies
    (raw_data_item_match_map0 full_perm (CBOR_Case_Map ares fp) (Cbor.Map v') (raw_data_item_map_match' full_perm))
    (A.pts_to a full_perm c' `star` raw_data_item_map_match full_perm c' v')
    emp
    (fun _ ->
      let _ = gen_elim () in
      GR.free _;
      rewrite
        (A.pts_to _ _ _)
        (A.pts_to a full_perm c');
      rewrite
        (raw_data_item_map_match' full_perm _ _)
        (raw_data_item_map_match' full_perm c' v');
      SM.seq_list_match_weaken
        c' v'
        (raw_data_item_map_entry_match' v' (raw_data_item_match full_perm))
        (raw_data_item_map_entry_match full_perm)
        (fun x y ->
          rewrite
            (raw_data_item_map_entry_match' v' (raw_data_item_match full_perm) x y)
            (raw_data_item_map_entry_match full_perm x y)
        )
    );
  implies_trans
    (raw_data_item_match full_perm res (Cbor.Map v'))
    (raw_data_item_match_map0 full_perm (CBOR_Case_Map ares fp) (Cbor.Map v') (raw_data_item_map_match' full_perm))
    (A.pts_to a full_perm c' `star` raw_data_item_map_match full_perm c' v');
  return res

#push-options "--z3rlimit 64"
#restart-solver

let serialize_cbor_map_eq
  (c: Cbor.raw_data_item { Cbor.Map? c })
: Lemma
  (
    let s0 = LPS.serialize CborST.serialize_raw_data_item c in
    let s1 = LPS.serialize CborST.serialize_header (CborST.uint64_as_argument Cbor.major_type_map (U64.uint_to_t (List.Tot.length (Cbor.Map?.v c)))) in
    let s2 = LPS.serialize (LPS.serialize_nlist (List.Tot.length (Cbor.Map?.v c)) (LPS.serialize_nondep_then CborST.serialize_raw_data_item CborST.serialize_raw_data_item)) (Cbor.Map?.v c) in
    s0 == s1 `Seq.append` s2 /\ Seq.length s0 == Seq.length s1 + Seq.length s2
  )
= CborST.serialize_raw_data_item_aux_correct c;
  LPS.serialize_synth_eq
    _
    CborST.synth_raw_data_item
    (LPS.serialize_dtuple2 CborST.serialize_header CborST.serialize_content)
    CborST.synth_raw_data_item_recip
    ()
    c;
  LPS.serialize_dtuple2_eq CborST.serialize_header CborST.serialize_content (CborST.synth_raw_data_item_recip c)

inline_for_extraction
noextract
let size_comp_for_map
  (size:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_size_comp_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Map? c})
: Tot (cbor_size_comp_for va c)
= fun #p sz perr ->
    let _ = A.intro_fits_u64 () in
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Map? va) = () in
    serialize_cbor_map_eq va;
    let c' = destr_cbor_map c in
    let l = Ghost.hide (maybe_cbor_map va) in
    assert (Ghost.reveal l == Cbor.Map?.v va);
    rewrite_with_implies
      (LPS.seq_list_match c'.footprint _ (raw_data_item_map_entry_match p))
      (LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match p));
    implies_trans_r1
      (A.pts_to _ _ _)
      (LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match p))
      (LPS.seq_list_match c'.footprint _ (raw_data_item_map_entry_match p))
      (raw_data_item_match p _ _);
    LPS.seq_list_match_length (raw_data_item_map_entry_match p) _ _;
    A.pts_to_length _ _;
    let sz1 = CBOR.SteelST.Raw.Write.size_comp_uint64_header Cbor.major_type_map c'.cbor_map_length sz perr in
    let _ = gen_elim () in
    let err1 = R.read perr in
    if err1
    then begin
      noop ();
      elim_implies
        (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match p))
        (raw_data_item_match p _ _);
      return sz1
    end else begin
      noop ();
      let sz2 = LPS.array_payload_as_nlist_size
        (LPS.serialize_nondep_then CborST.serialize_raw_data_item CborST.serialize_raw_data_item)
        (raw_data_item_map_entry_match p)
        (fun x y sz perr ->
          let res = size_comp_for_map_entry size y x sz perr in
          let _ = gen_elim () in
          return res
        )
        #c'.footprint
        #l
        (SZ.uint64_to_sizet c'.cbor_map_length)
        c'.cbor_map_payload
        sz1
        perr
      in
      let _ = gen_elim () in
      elim_implies
        (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match p))
        (raw_data_item_match p _ _);
      return sz2
    end

noextract
unfold
let l2r_write_map_entry_post
  (va: Ghost.erased (Cbor.raw_data_item & Cbor.raw_data_item))
  (vout: LPA.array LPS.byte)
  (vres: LPS.v (LPS.and_then_kind CborST.parse_raw_data_item_kind CborST.parse_raw_data_item_kind) (Cbor.raw_data_item & Cbor.raw_data_item))
  (vout': LPA.array LPS.byte)
: Tot prop
=  
       LPA.merge_into (LPS.array_of vres) vout' vout /\
       vres.LPS.contents == Ghost.reveal va

[@@__reduce__]
let l2r_writer_for_map_entry_post
  (p: perm)
  (va: Ghost.erased (Cbor.raw_data_item & Cbor.raw_data_item))
  (c: cbor_map_entry)
  (vout: LPA.array LPS.byte)
  (out: LW.t)
  (res: LPS.byte_array)
  (vres: LPS.v (LPS.and_then_kind CborST.parse_raw_data_item_kind CborST.parse_raw_data_item_kind) (Cbor.raw_data_item & Cbor.raw_data_item))
  (vout': LPA.array LPS.byte)
: Tot vprop
=
  raw_data_item_map_entry_match p c (Ghost.reveal va) `star`
  LPS.aparse (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item) res vres `star`
  LW.vp out vout' `star`
  pure (
    l2r_write_map_entry_post va vout vres vout'
  )

inline_for_extraction
noextract
let l2r_writer_for_map_entry
  (write:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_l2r_writer_for va c
  )
  (va: Ghost.erased (Cbor.raw_data_item & Cbor.raw_data_item))
  (c: cbor_map_entry)
  (#p: perm)
  (#vout: LPA.array LPS.byte)
  (out: LW.t)
: ST LPS.byte_array
    (raw_data_item_map_entry_match p c (Ghost.reveal va) `star`
      LW.vp out vout
    )
    (fun res -> exists_ (fun vres -> exists_ (fun vout' ->
      l2r_writer_for_map_entry_post p va c vout out res vres vout'
    )))
    (Seq.length (LPS.serialize (LPS.serialize_nondep_then CborST.serialize_raw_data_item CborST.serialize_raw_data_item) va) <= LPA.length vout)
    (fun _ -> True)
= LPS.serialize_nondep_then_eq CborST.serialize_raw_data_item CborST.serialize_raw_data_item va;
  noop ();
  let res = write _ (cbor_map_entry_key c) out in
  let _ = gen_elim () in
  let _ = LPS.elim_aparse_with_serializer CborST.serialize_raw_data_item res in
  let res_pl = write _ (cbor_map_entry_value c) out in
  let _ = gen_elim () in
  let vout' = vpattern_replace (LW.vp out) in
  let _ = LPS.elim_aparse_with_serializer CborST.serialize_raw_data_item res_pl in
  let _ = LPA.join res res_pl in
  let vres = LPS.intro_aparse_with_serializer (LPS.serialize_nondep_then CborST.serialize_raw_data_item CborST.serialize_raw_data_item) va res in
  assert_ (l2r_writer_for_map_entry_post p va c vout out res vres vout');
  return res

inline_for_extraction
noextract
let l2r_writer_for_map
  (write:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_l2r_writer_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Map? c})
: Tot (cbor_l2r_writer_for va c)
= fun #p #vout out ->
    let _ = A.intro_fits_u64 () in
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Map? va) = () in
    serialize_cbor_map_eq va;
    let c' = destr_cbor_map c in
    let l = Ghost.hide (maybe_cbor_map va) in
    assert (Ghost.reveal l == Cbor.Map?.v va);
    rewrite_with_implies
      (LPS.seq_list_match c'.footprint _ (raw_data_item_map_entry_match p))
      (LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match p));
    implies_trans_r1
      (A.pts_to _ _ _)
      (LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match p))
      (LPS.seq_list_match c'.footprint _ (raw_data_item_map_entry_match p))
      (raw_data_item_match p _ _);
    LPS.seq_list_match_length (raw_data_item_map_entry_match p) _ _;
    A.pts_to_length _ _;
    let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header Cbor.major_type_map c'.cbor_map_length out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer CborST.serialize_header res in
    let res_pl = LPS.l2r_write_array_payload_as_nlist
      (LPS.serialize_nondep_then CborST.serialize_raw_data_item CborST.serialize_raw_data_item)
      (raw_data_item_map_entry_match p)
      (fun x y out ->
         let res = l2r_writer_for_map_entry write y x out in
         let _ = gen_elim () in
         return res
      )
      #c'.footprint
      #l
      (SZ.uint64_to_sizet c'.cbor_map_length)
      c'.cbor_map_payload
      out
    in
    let _ = gen_elim () in
    let vout' = vpattern_replace (LW.vp out) in
    let _ = LPS.elim_aparse_with_serializer (LPS.serialize_nlist (SZ.v (SZ.uint64_to_sizet c'.cbor_map_length)) (LPS.serialize_nondep_then CborST.serialize_raw_data_item CborST.serialize_raw_data_item)) res_pl in
    let _ = LPA.join res res_pl in
    let _ = gen_elim () in
    let vres = LPS.intro_aparse_with_serializer CborST.serialize_raw_data_item va res in
    elim_implies
      (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match p))
      (raw_data_item_match p _ _);
    assert_ (cbor_l2r_writer_for_post p va c vout out res vres vout'); // FIXME: WHY WHY WHY?
    return res

#pop-options

let cbor_map_iterator_init
  a
= raw_data_item_match_get_case a;
  match a with
  | CBOR_Case_Map _ _ ->
    return (cbor_map_iterator_init_map a)
  | _ ->
    return (cbor_map_iterator_init_serialized a)

let cbor_map_iterator_is_done
  i
= cbor_map_iterator_match_length i;
  return (i.cbor_map_iterator_length = 0uL)

let cbor_map_iterator_next
  pi
= let i = R.read pi in
  match i.cbor_map_iterator_payload with
  | CBOR_Map_Iterator_Payload_Map _ _ ->
    return (cbor_map_iterator_next_map i pi)
  | _ ->
    return (cbor_map_iterator_next_serialized i pi)

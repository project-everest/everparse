module CBOR.SteelST.Map
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Type

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

noeq
type cbor_map_iterator_payload_t =
| CBOR_Map_Iterator_Payload_Map:
    payload: A.array cbor_map_entry ->
    footprint: Ghost.erased (Seq.seq cbor_map_entry) ->
    cbor_map_iterator_payload_t
| CBOR_Map_Iterator_Payload_Serialized:
    payload: cbor_serialized_payload_t ->
    footprint: cbor_serialized_footprint_t ->
    cbor_map_iterator_payload_t

// NOTE: this type could be made abstract (with val and
// CAbstractStruct, and then hiding cbor_array_iterator_payload_t
// altogether), but then, users couldn't allocate on stack
noeq
type cbor_map_iterator_t = {
  cbor_map_iterator_length: U64.t;
  cbor_map_iterator_payload: cbor_map_iterator_payload_t;
  footprint: cbor_footprint_t;
}

[@@inline_let]
let dummy_cbor_map_iterator = {
  cbor_map_iterator_length = 0uL;
  cbor_map_iterator_payload = CBOR_Map_Iterator_Payload_Map A.null Seq.empty;
  footprint = dummy_cbor_footprint;
}

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
      U64.v c.cbor_map_iterator_length == List.Tot.length l /\
      c.cbor_map_iterator_payload == CBOR_Map_Iterator_Payload_Map a (Ghost.hide fp)
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

#push-options "--z3rlimit 64"
#restart-solver

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
  let _ = gen_elim () in
  let a = CBOR_Map_Iterator_Payload_Map?.payload i.cbor_map_iterator_payload in
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
    (A.pts_to _ _ _ `star` GR.pts_to _ _ _)
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
  rewrite (A.pts_to (A.split_r _ _) _ _) (A.pts_to ar' p (Ghost.reveal c2));
  intro_implies
    (A.pts_to ar' p c2)
    (A.pts_to a p fp)
    (A.pts_to (A.split_l _ _) _ _)
    (fun _ ->
      let _ = A.ghost_join (A.split_l _ _) ar' () in
      rewrite
        (A.pts_to _ _ _)
        (A.pts_to a p fp)
    );
  implies_reg_r (A.pts_to _ _ _) (A.pts_to _ _ _) (GR.pts_to _ _ _);
  implies_trans_l1
    (A.pts_to ar' p c2 `star` GR.pts_to _ _ _)
    (A.pts_to a p fp `star` GR.pts_to _ _ _)
    (SM.seq_list_match_cons0 fp l (raw_data_item_map_entry_match p) SM.seq_list_match)
    (cbor_map_iterator_match p _ l);
  implies_trans_r1
    (A.pts_to ar' p c2 `star` GR.pts_to _ _ _)
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
      let _ = gen_elim () in
      elim_implies (GR.pts_to i'.footprint p ()) (GR.pts_to i.footprint p ());
      rewrite (A.pts_to _ _ _) (A.pts_to ar' p c2);
      rewrite (raw_data_item_map_match p _ _) (raw_data_item_map_match p c2 (List.Tot.tl l))
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

let cbor_map_iterator_next
  pi
= let i = R.read pi in
  match i.cbor_map_iterator_payload with
  | CBOR_Map_Iterator_Payload_Map _ _ ->
    return (cbor_map_iterator_next_map i pi)
  | _ ->
    return (cbor_map_iterator_next_serialized i pi)

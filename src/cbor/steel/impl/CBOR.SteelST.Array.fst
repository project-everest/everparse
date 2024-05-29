module CBOR.SteelST.Array
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Match
open CBOR.SteelST.Type.Def

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let raw_data_item_match_array_intro
  (#opened: _)
  (#p: perm)
  (#c': Seq.seq cbor)
  (#v': list Cbor.raw_data_item)
  (fp: cbor_footprint_t)
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: STGhostT unit opened
    (A.pts_to a p c' `star`
      GR.pts_to fp p () `star`
      raw_data_item_array_match p c' v')
    (fun _ ->
      raw_data_item_match
        p
        (CBOR_Case_Array
          ({
            cbor_array_length = len;
            cbor_array_payload = a;
            footprint = c';
          })
          fp
        )
        (Cbor.Array v')
    )
= noop ();
  rewrite_with_tactic
    (raw_data_item_match_array0
      p
      (CBOR_Case_Array
        ({
          cbor_array_length = len;
          cbor_array_payload = a;
          footprint = c';
        })
        fp
      )
      (Cbor.Array v')
      (raw_data_item_array_match p)
    )
    (raw_data_item_match p _ _)

let raw_data_item_match_array_elim
  (#opened: _)
  (#p: perm)
  (a: cbor_array)
  (fp: cbor_footprint_t)
  (v: Cbor.raw_data_item)
: STGhost (squash (Cbor.Array? v)) opened
    (raw_data_item_match p (CBOR_Case_Array a fp) v)
    (fun _ ->
      A.pts_to a.cbor_array_payload p a.footprint `star`
      GR.pts_to fp p () `star`
      raw_data_item_array_match p a.footprint (Cbor.Array?.v v)
    )
    True
    (fun _ -> U64.v a.cbor_array_length == List.Tot.length (Cbor.Array?.v v))
= raw_data_item_match_get_case _;
  let sq : squash (Cbor.Array? v) = () in
  let Cbor.Array v' = v in
  vpattern_rewrite (raw_data_item_match p _) (Cbor.Array v');
  rewrite_with_tactic
    (raw_data_item_match p _ _)
    (raw_data_item_match_array0 p (CBOR_Case_Array a fp) (Cbor.Array v') (raw_data_item_array_match p));
  let _ = gen_elim () in
  rewrite (A.pts_to _ _ _) (A.pts_to a.cbor_array_payload p a.footprint);
  rewrite (GR.pts_to _ _ _) (GR.pts_to fp p ());
  rewrite (raw_data_item_array_match p _ _) (raw_data_item_array_match p a.footprint (Cbor.Array?.v v));
  sq

let cbor_constr_array
  #c' #v' a len
= let fp = GR.alloc () in
  [@@inline_let]
  let ares : cbor_array = {
    cbor_array_length = len;
    cbor_array_payload = a;
    footprint = c';
  }
  in
  [@@inline_let]
  let res = CBOR_Case_Array ares fp in
  raw_data_item_match_array_intro fp a len;
  rewrite (raw_data_item_match full_perm _ _) (raw_data_item_match full_perm res (Cbor.Array v'));
  intro_implies
    (raw_data_item_match full_perm res (Cbor.Array v'))
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match full_perm c' v'
    )
    emp
    (fun _ ->
      rewrite (raw_data_item_match full_perm _ _) (raw_data_item_match full_perm (CBOR_Case_Array ares fp) (Cbor.Array v'));
      let _ = raw_data_item_match_array_elim _ _ _ in
      rewrite (A.pts_to _ _ _) (A.pts_to a full_perm c');
      GR.free _;
      rewrite (raw_data_item_array_match full_perm _ _) (raw_data_item_array_match full_perm c' v')
    );
  return res

let cbor_destr_array
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_array
    (raw_data_item_match p a v)
    (fun res ->
      A.pts_to res.cbor_array_payload p res.footprint `star`
      raw_data_item_array_match p res.footprint (maybe_cbor_array v) `star`
      ((A.pts_to res.cbor_array_payload p res.footprint `star`
        raw_data_item_array_match p res.footprint (maybe_cbor_array v)) `implies_`
        raw_data_item_match p a v
      )
    )
    (CBOR_Case_Array? a)
    (fun res ->
      Cbor.Array? v /\
      U64.v res.cbor_array_length == List.Tot.length (maybe_cbor_array v)
    )
= raw_data_item_match_get_case _;
  let CBOR_Case_Array res fp = a in
  vpattern_rewrite
    (fun a -> raw_data_item_match p a _)
    (CBOR_Case_Array res fp);
  let _ = raw_data_item_match_array_elim _ _ _ in
  vpattern_rewrite (raw_data_item_array_match p _) (maybe_cbor_array v);
  intro_implies
    (A.pts_to res.cbor_array_payload p res.footprint `star`
      raw_data_item_array_match p res.footprint (maybe_cbor_array v))
    (raw_data_item_match p a v)
    (GR.pts_to _ _ _)
    (fun _ ->
      raw_data_item_match_array_intro fp _ res.cbor_array_length;
      rewrite (raw_data_item_match p _ _) (raw_data_item_match p _ _)
    );
  return res

let cbor_array_length
  #p #v a
= raw_data_item_match_get_case a;
  match a with
  | CBOR_Case_Array _ _ ->
    let a' = cbor_destr_array a in
    elim_implies
      (A.pts_to _ _ _ `star` raw_data_item_array_match p _ _)
      (raw_data_item_match p _ _);
    return a'.cbor_array_length
  | _ ->
    let s = destr_cbor_serialized a in
    let _ = gen_elim () in
    let res = CborST.read_argument_as_uint64 s.cbor_serialized_payload in
    elim_implies
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match p _ _);
    return res

let cbor_array_index_case_array
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
  (i: SZ.t {
    Cbor.Array? v /\
    SZ.v i < List.Tot.length (Cbor.Array?.v v) /\
    CBOR_Case_Array? a
  })
: STT cbor
    (raw_data_item_match p a v)
    (fun a' ->
      raw_data_item_match p a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `star`
      (raw_data_item_match p a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `implies_`
        raw_data_item_match p a v)
    )
= raw_data_item_match_get_case a;
  noop ();
  let ar = cbor_destr_array a in
  A.pts_to_length ar.cbor_array_payload _;
  SM.seq_list_match_length (raw_data_item_match p) ar.footprint (maybe_cbor_array v);
  let res = A.index ar.cbor_array_payload i in
  intro_implies
    (raw_data_item_array_match p ar.footprint (maybe_cbor_array v))
    (raw_data_item_match p a v)
    (A.pts_to _ _ _ `star`
      ((A.pts_to _ _ _ `star` raw_data_item_array_match p _ _) `implies_` raw_data_item_match p _ _)
    )
    (fun _ ->
       elim_implies
       (A.pts_to _ _ _ `star` raw_data_item_array_match p _ _)
       (raw_data_item_match p _ _)
    );
  rewrite_with_implies
    (raw_data_item_array_match p ar.footprint (maybe_cbor_array v))
    (SM.seq_list_match ar.footprint (maybe_cbor_array v) (raw_data_item_match p));
  implies_trans
    (SM.seq_list_match ar.footprint (maybe_cbor_array v) (raw_data_item_match p))
    (raw_data_item_array_match p ar.footprint (maybe_cbor_array v))
    (raw_data_item_match p a v);
  let _ = SM.seq_list_match_index (raw_data_item_match p) ar.footprint (maybe_cbor_array v) (SZ.v i) in
  implies_trans
    (raw_data_item_match p (Seq.index ar.footprint (SZ.v i)) (List.Tot.index (maybe_cbor_array v) (SZ.v i)))
    (SM.seq_list_match ar.footprint (maybe_cbor_array v) (raw_data_item_match p))
    (raw_data_item_match p a v);
  rewrite_with_implies
    (raw_data_item_match p (Seq.index ar.footprint (SZ.v i)) (List.Tot.index (maybe_cbor_array v) (SZ.v i)))
    (raw_data_item_match p res (List.Tot.index (Cbor.Array?.v v) (SZ.v i)));
  implies_trans
    (raw_data_item_match p res (List.Tot.index (Cbor.Array?.v v) (SZ.v i)))
    (raw_data_item_match p (Seq.index ar.footprint (SZ.v i)) (List.Tot.index (maybe_cbor_array v) (SZ.v i)))
    (raw_data_item_match p a v);
  return res

let cbor_array_index_case_serialized
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
  (i: SZ.t {
    Cbor.Array? v /\
    SZ.v i < List.Tot.length (Cbor.Array?.v v) /\
    CBOR_Case_Serialized? a
  })
: STT cbor
    (raw_data_item_match p a v)
    (fun a' ->
      raw_data_item_match p a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `star`
      (raw_data_item_match p a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `implies_`
        raw_data_item_match p a v)
    )
= raw_data_item_match_perm_le_full_perm a;
  let s = destr_cbor_serialized a in
  let _ = gen_elim () in
  let n = Ghost.hide (List.Tot.length (Cbor.Array?.v v)) in
  let a = CBOR.SteelST.Raw.Array.focus_array_with_ghost_length n s.cbor_serialized_payload in
  let _ = gen_elim () in
  implies_trans
    (LPS.aparse (LPS.parse_nlist n CborST.parse_raw_data_item) _ _)
    (LPS.aparse CborST.parse_raw_data_item _ _)
    (raw_data_item_match p _ _);
  let _ = LPS.aparse_nlist_aparse_list_with_implies CborST.parse_raw_data_item n a in
  implies_trans
    (LPS.aparse (LPS.parse_list CborST.parse_raw_data_item) _ _)
    (LPS.aparse (LPS.parse_nlist n CborST.parse_raw_data_item) _ _)
    (raw_data_item_match p _ _);
  let elt = LowParse.SteelST.List.Nth.list_nth_with_implies CborST.jump_raw_data_item a i in
  let _ = gen_elim () in
  implies_trans
    (LPS.aparse CborST.parse_raw_data_item _ _)
    (LPS.aparse (LPS.parse_list CborST.parse_raw_data_item) _ _)
    (raw_data_item_match p _ _);
  let sz = LPS.get_parsed_size CborST.jump_raw_data_item elt in
  let res = read_valid_cbor_from_buffer_with_size_strong p elt sz in
  implies_trans
    (raw_data_item_match p res _)
    (LPS.aparse CborST.parse_raw_data_item _ _)
    (raw_data_item_match p _ _);
  vpattern_rewrite_with_implies
    (raw_data_item_match p res)
    (List.Tot.index (Cbor.Array?.v v) (SZ.v i));
  implies_trans
    (raw_data_item_match p res _)
    (raw_data_item_match p res _)
    (raw_data_item_match p _ _);
  return res
    
let cbor_array_index
  a i
= raw_data_item_match_get_case a;
  match a with
  | CBOR_Case_Array _ _ ->
    return (cbor_array_index_case_array a i)
  | _ ->
    return (cbor_array_index_case_serialized a i)

let cbor_dummy_array_iterator = {
  cbor_array_iterator_length = 0uL;
  cbor_array_iterator_payload = CBOR_Array_Iterator_Payload_Array A.null Seq.empty;
  footprint = dummy_cbor_footprint;
}

[@@__reduce__]
let cbor_array_iterator_match_array
  (p: perm)
  (c: cbor_array_iterator_t)
  (l: list Cbor.raw_data_item)
: Tot vprop
= exists_ (fun a -> exists_ (fun fp ->
    GR.pts_to c.footprint p () `star`
    A.pts_to a p fp `star`
    raw_data_item_array_match p fp l `star`
    pure (
      U64.v c.cbor_array_iterator_length == List.Tot.length l /\
      c.cbor_array_iterator_payload == CBOR_Array_Iterator_Payload_Array a (Ghost.hide fp)
  )))

let cbor_array_iterator_match_serialized_prop
  (p: perm)
  (c: cbor_array_iterator_t)
  (l: list Cbor.raw_data_item)
  (a: LPS.byte_array)
  (fp: LPS.v (LPS.parse_nlist_kind (U64.v c.cbor_array_iterator_length) CborST.parse_raw_data_item_kind) (LPS.nlist (U64.v c.cbor_array_iterator_length) Cbor.raw_data_item))
: Tot prop
= 
  fp.LPS.contents == l /\
  begin match c.cbor_array_iterator_payload with
  | CBOR_Array_Iterator_Payload_Serialized a' fp' ->
    a == a' /\
    LPS.array_of fp == LPA.set_array_perm fp' (p `prod_perm` LPA.array_perm fp')
  | _ -> False
  end

[@@__reduce__]
let cbor_array_iterator_match_serialized
  (p: perm)
  (c: cbor_array_iterator_t)
  (l: list Cbor.raw_data_item)
: Tot vprop
= exists_ (fun a -> exists_ (fun fp ->
    GR.pts_to c.footprint p () `star`
    LPS.aparse (LPS.parse_nlist (U64.v c.cbor_array_iterator_length) CborST.parse_raw_data_item) a fp `star`
    pure (cbor_array_iterator_match_serialized_prop p c l a fp)
  ))

let cbor_array_iterator_match
  p c l
= match c.cbor_array_iterator_payload with
  | CBOR_Array_Iterator_Payload_Array _ _ -> cbor_array_iterator_match_array p c l
  | _ -> cbor_array_iterator_match_serialized p c l

#push-options "--z3rlimit 32"
#restart-solver

let cbor_array_iterator_match_length
  (#opened: _)
  (#p: perm)
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (i: cbor_array_iterator_t)
: STGhost unit opened
    (cbor_array_iterator_match p i l)
    (fun _ -> cbor_array_iterator_match p i l)
    True
    (fun _ -> U64.v i.cbor_array_iterator_length == List.Tot.length l)
= match i.cbor_array_iterator_payload with
  | CBOR_Array_Iterator_Payload_Array _ _ ->
    rewrite
      (cbor_array_iterator_match p i l)
      (cbor_array_iterator_match_array p i l);
    let _ = gen_elim () in
    rewrite
      (cbor_array_iterator_match_array p i l)
      (cbor_array_iterator_match p i l)
  | CBOR_Array_Iterator_Payload_Serialized _ _ ->
    rewrite
      (cbor_array_iterator_match p i l)
      (cbor_array_iterator_match_serialized p i l);
    let _ = gen_elim () in
    rewrite
      (cbor_array_iterator_match_serialized p i l)
      (cbor_array_iterator_match p i l)

#pop-options

let cbor_array_iterator_init_array
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { Cbor.Array? v /\ CBOR_Case_Array? a })
: STT cbor_array_iterator_t
    (raw_data_item_match p a v)
    (fun i ->
      cbor_array_iterator_match p i (Cbor.Array?.v v) `star`
      (cbor_array_iterator_match p i (Cbor.Array?.v v) `implies_`
        raw_data_item_match p a v)
    )
= raw_data_item_match_perm_le_full_perm a;
  let len = cbor_array_length a in
  let ar = cbor_destr_array a in
  let fp = GR.alloc () in // I could reuse the footprint from `a`, but `cbor_destr_array` does not expose it
  gref_lower_perm fp p;
  let res = {
    cbor_array_iterator_length = len;
    cbor_array_iterator_payload = CBOR_Array_Iterator_Payload_Array ar.cbor_array_payload ar.footprint;
    footprint = fp;
  }
  in
  vpattern_rewrite_with_implies (fun r -> GR.pts_to r _ _) res.footprint;
  implies_trans (GR.pts_to res.footprint p ()) (GR.pts_to fp p ()) (GR.pts_to fp full_perm ());
  rewrite_with_implies
    (cbor_array_iterator_match_array p res (maybe_cbor_array v))
    (cbor_array_iterator_match p res (Cbor.Array?.v v));
  intro_implies
    (cbor_array_iterator_match_array p res (maybe_cbor_array v))
    (A.pts_to ar.cbor_array_payload p ar.footprint `star`
      raw_data_item_array_match p ar.footprint (maybe_cbor_array v)
    )
    (GR.pts_to res.footprint p () `implies_` GR.pts_to fp full_perm ())
    (fun _ ->
      let _ = gen_elim () in
      elim_implies (GR.pts_to _ _ _) (GR.pts_to _ _ _);
      GR.free _;
      rewrite
        (A.pts_to _ _ _)
        (A.pts_to ar.cbor_array_payload p ar.footprint);
      rewrite
        (raw_data_item_array_match p _ _)
        (raw_data_item_array_match p ar.footprint (maybe_cbor_array v))
    );
  implies_trans
    (cbor_array_iterator_match_array p res (maybe_cbor_array v))
    (A.pts_to ar.cbor_array_payload p ar.footprint `star`
      raw_data_item_array_match p ar.footprint (maybe_cbor_array v)
    )
    (raw_data_item_match p a v);
  implies_trans
    (cbor_array_iterator_match p res (Cbor.Array?.v v))
    (cbor_array_iterator_match_array p res (maybe_cbor_array v))
    (raw_data_item_match p a v);
  return res

#push-options "--z3rlimit 64"
#restart-solver

let cbor_array_iterator_init_serialized
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { Cbor.Array? v /\ CBOR_Case_Serialized? a })
: STT cbor_array_iterator_t
    (raw_data_item_match p a v)
    (fun i ->
      cbor_array_iterator_match p i (Cbor.Array?.v v) `star`
      (cbor_array_iterator_match p i (Cbor.Array?.v v) `implies_`
        raw_data_item_match p a v)
    )
= raw_data_item_match_perm_le_full_perm a;
  let len = cbor_array_length a in
  let s = destr_cbor_serialized a in
  let _ = gen_elim () in
  let ar = CBOR.SteelST.Raw.Array.focus_array_with_ghost_length (U64.v len) s.cbor_serialized_payload in
  let _ = gen_elim () in
  implies_trans
    (LPS.aparse (LPS.parse_nlist (U64.v len) CborST.parse_raw_data_item) _ _)
    (LPS.aparse CborST.parse_raw_data_item _ _)
    (raw_data_item_match p a v);
  let var0 = vpattern (LPS.aparse (LPS.parse_nlist (U64.v len) CborST.parse_raw_data_item) _) in
  let fp = GR.alloc () in // same as above, I could use the footprint from `a` but `destr_cbor_serialized` does not expose it
  gref_lower_perm fp p;
  [@@inline_let]
  let res = {
    cbor_array_iterator_length = len;
    cbor_array_iterator_payload = CBOR_Array_Iterator_Payload_Serialized ar (LPA.set_array_perm (LPS.array_of var0) (LPA.array_perm (LPS.array_of var0) `div_perm` p));
    footprint = fp;
  }
  in
  vpattern_rewrite_with_implies (fun r -> GR.pts_to r _ _) res.footprint;
  implies_trans (GR.pts_to res.footprint p ()) (GR.pts_to fp p ()) (GR.pts_to fp full_perm ());
  let var = LPS.rewrite_aparse_with_implies ar (LPS.parse_nlist (U64.v res.cbor_array_iterator_length) CborST.parse_raw_data_item) in
  implies_trans
    (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_array_iterator_length) CborST.parse_raw_data_item) ar var)
    (LPS.aparse (LPS.parse_nlist (U64.v len) CborST.parse_raw_data_item) _ _)
    (raw_data_item_match p a v);
  rewrite_with_implies
    (cbor_array_iterator_match_serialized p res (Cbor.Array?.v v))
    (cbor_array_iterator_match p res (Cbor.Array?.v v));
  intro_implies
    (cbor_array_iterator_match_serialized p res (Cbor.Array?.v v))
    (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_array_iterator_length) CborST.parse_raw_data_item) ar var)
    (GR.pts_to res.footprint p () `implies_` GR.pts_to fp full_perm ())
    (fun _ ->
      let _ = gen_elim () in
      elim_implies (GR.pts_to _ _ _) (GR.pts_to _ _ _);
      GR.free _;
      rewrite
        (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_array_iterator_length) CborST.parse_raw_data_item) _ _)
        (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_array_iterator_length) CborST.parse_raw_data_item) ar var)
    );
  implies_trans
    (cbor_array_iterator_match p res (Cbor.Array?.v v))
    (cbor_array_iterator_match_serialized p res (Cbor.Array?.v v))
    (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_array_iterator_length) CborST.parse_raw_data_item) ar var);
  implies_trans
    (cbor_array_iterator_match p res (Cbor.Array?.v v))
    (LPS.aparse (LPS.parse_nlist (U64.v res.cbor_array_iterator_length) CborST.parse_raw_data_item) ar var)
    (raw_data_item_match p a v);
  return res

#pop-options

let cbor_array_iterator_init
  a
= raw_data_item_match_get_case a;
  match a with
  | CBOR_Case_Array _ _ ->
    return (cbor_array_iterator_init_array a)
  | _ ->
    return (cbor_array_iterator_init_serialized a)

let cbor_array_iterator_is_done
  i
= cbor_array_iterator_match_length i;
  return (i.cbor_array_iterator_length = 0uL)

#push-options "--z3rlimit 64"
#restart-solver

let cbor_array_iterator_next_array
  (#p: perm)
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (#i1 #i2: Ghost.erased cbor_array_iterator_t)
  (i: cbor_array_iterator_t { i == Ghost.reveal i2 })
  (pi: R.ref cbor_array_iterator_t { Cons? l /\ CBOR_Array_Iterator_Payload_Array? i.cbor_array_iterator_payload })
: STT cbor
    (R.pts_to pi full_perm i1 `star` cbor_array_iterator_match p i2 l)
    (fun c -> exists_ (fun i' ->
      R.pts_to pi full_perm i' `star`
      raw_data_item_match p c (List.Tot.hd l) `star`
      cbor_array_iterator_match p i' (List.Tot.tl l) `star`
      ((raw_data_item_match p c (List.Tot.hd l) `star`
        cbor_array_iterator_match p i' (List.Tot.tl l)) `implies_`
        cbor_array_iterator_match p i2 l
      )
    ))
= rewrite_with_implies
    (cbor_array_iterator_match p _ l)
    (cbor_array_iterator_match_array p i l);
  let _ = gen_elim () in
  let a = match i.cbor_array_iterator_payload with
  | CBOR_Array_Iterator_Payload_Array payload _ -> payload
  in
  let fp : Ghost.erased _ = CBOR_Array_Iterator_Payload_Array?.footprint i.cbor_array_iterator_payload in
  rewrite
    (A.pts_to _ p _)
    (A.pts_to a p fp);
  rewrite
    (raw_data_item_array_match p _ _)
    (raw_data_item_array_match p fp l);
  intro_implies
    ((A.pts_to a p fp `star` GR.pts_to i.footprint p ()) `star` raw_data_item_array_match p fp l)
    (cbor_array_iterator_match_array p i l)
    emp
    (fun _ -> noop (); noop ());
  implies_trans
    ((A.pts_to a p fp `star` GR.pts_to i.footprint p ()) `star` raw_data_item_array_match p fp l)
    (cbor_array_iterator_match_array p i l)
    (cbor_array_iterator_match p _ l);
  let len' = i.cbor_array_iterator_length `U64.sub` 1uL in
  SM.seq_list_match_cons_eq  fp l (raw_data_item_match p);
  Seq.seq_of_list_tl l;
  SM.seq_list_match_length (raw_data_item_match p) _ _;
  A.pts_to_length _ _;
  rewrite_with_implies
    (raw_data_item_array_match p fp l)
    (SM.seq_list_match_cons0 fp l (raw_data_item_match p) SM.seq_list_match);
  implies_trans_r1
    (A.pts_to _ _ _ `star` GR.pts_to _ _ _)
    (SM.seq_list_match_cons0 fp l (raw_data_item_match p) SM.seq_list_match)
    (raw_data_item_array_match p fp l)
    (cbor_array_iterator_match p _ _);
  let _ = gen_elim () in
  let res = A.index a 0sz in
  vpattern_rewrite (fun c1 -> raw_data_item_match p c1 _) res;
  let c2 = vpattern_replace_erased (fun c2 -> SM.seq_list_match c2 (List.Tot.tl l) (raw_data_item_match p)) in
  Seq.lemma_cons_inj (Seq.head fp) res (Seq.tail fp) c2;
  intro_implies
    (raw_data_item_match p res (List.Tot.hd l) `star` SM.seq_list_match c2 (List.Tot.tl l) (raw_data_item_match p))
    (SM.seq_list_match_cons0 fp l (raw_data_item_match p) SM.seq_list_match)
    emp
    (fun _ -> noop (); noop ());
  rewrite_with_implies
    (SM.seq_list_match c2 (List.Tot.tl l) (raw_data_item_match p))
    (raw_data_item_array_match p c2 (List.Tot.tl l));
  implies_trans_r1
    (raw_data_item_match p res (List.Tot.hd l))
    (raw_data_item_array_match p c2 (List.Tot.tl l))
    (SM.seq_list_match c2 (List.Tot.tl l) (raw_data_item_match p))
    (SM.seq_list_match_cons0 fp l (raw_data_item_match p) SM.seq_list_match);
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
    (SM.seq_list_match_cons0 fp l (raw_data_item_match p) SM.seq_list_match)
    (cbor_array_iterator_match p _ l);
  implies_trans_r1
    (A.pts_to ar' p c2 `star` GR.pts_to _ _ _)
    (raw_data_item_match p res (List.Tot.hd l) `star` raw_data_item_array_match p c2 (List.Tot.tl l))
    (SM.seq_list_match_cons0 fp l (raw_data_item_match p) SM.seq_list_match)
    (cbor_array_iterator_match p _ l);
  implies_with_tactic
    (raw_data_item_match p res (List.Tot.hd l) `star` (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star` raw_data_item_array_match p c2 (List.Tot.tl l)))
    ((A.pts_to ar' p c2 `star` GR.pts_to i.footprint p ()) `star` (raw_data_item_match p res (List.Tot.hd l) `star` raw_data_item_array_match p c2 (List.Tot.tl l)));
  implies_trans
    (raw_data_item_match p res (List.Tot.hd l) `star` (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star` raw_data_item_array_match p c2 (List.Tot.tl l)))
    ((A.pts_to ar' p c2 `star` GR.pts_to i.footprint p ()) `star` (raw_data_item_match p res (List.Tot.hd l) `star` raw_data_item_array_match p c2 (List.Tot.tl l)))
    (cbor_array_iterator_match p _ l);
  let i' = {
    cbor_array_iterator_length = len';
    cbor_array_iterator_payload = CBOR_Array_Iterator_Payload_Array ar' c2;
    footprint = i.footprint;
  }
  in
  R.write pi i';
  vpattern_rewrite_with_implies (fun r -> GR.pts_to r _ _) i'.footprint;
  rewrite_with_implies
    (cbor_array_iterator_match_array p i' (List.Tot.tl l))
    (cbor_array_iterator_match p i' (List.Tot.tl l));
  intro_implies
    (cbor_array_iterator_match_array p i' (List.Tot.tl l))
    (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star`  raw_data_item_array_match p c2 (List.Tot.tl l))
    (GR.pts_to i'.footprint p () `implies_` GR.pts_to i.footprint p ())
    (fun _ ->
      let _ = gen_elim () in
      elim_implies (GR.pts_to i'.footprint p ()) (GR.pts_to i.footprint p ());
      rewrite (A.pts_to _ _ _) (A.pts_to ar' p c2);
      rewrite (raw_data_item_array_match p _ _) (raw_data_item_array_match p c2 (List.Tot.tl l))
    );
  implies_trans
    (cbor_array_iterator_match p i' (List.Tot.tl l))
    (cbor_array_iterator_match_array p i' (List.Tot.tl l))
    (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star` raw_data_item_array_match p c2 (List.Tot.tl l));
  implies_trans_r1
    (raw_data_item_match p res (List.Tot.hd l))
    (cbor_array_iterator_match p i' (List.Tot.tl l))
    (A.pts_to ar' p c2 `star` GR.pts_to i.footprint p () `star` raw_data_item_array_match p c2 (List.Tot.tl l))
    (cbor_array_iterator_match p _ l);
  return res

let cbor_array_iterator_next_serialized
  (#p: perm)
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (#i1 #i2: Ghost.erased cbor_array_iterator_t)
  (i: cbor_array_iterator_t { i == Ghost.reveal i2 })
  (pi: R.ref cbor_array_iterator_t { Cons? l /\ CBOR_Array_Iterator_Payload_Serialized? i.cbor_array_iterator_payload })
: STT cbor
    (R.pts_to pi full_perm i1 `star` cbor_array_iterator_match p i2 l)
    (fun c -> exists_ (fun i' ->
      R.pts_to pi full_perm i' `star`
      raw_data_item_match p c (List.Tot.hd l) `star`
      cbor_array_iterator_match p i' (List.Tot.tl l) `star`
      ((raw_data_item_match p c (List.Tot.hd l) `star`
        cbor_array_iterator_match p i' (List.Tot.tl l)) `implies_`
        cbor_array_iterator_match p i2 l
      )
    ))
= rewrite_with_implies
    (cbor_array_iterator_match p _ l)
    (cbor_array_iterator_match_serialized p i l);
  let _ = gen_elim () in
  GR.pts_to_perm i.footprint;
  let a = match i.cbor_array_iterator_payload with
  | CBOR_Array_Iterator_Payload_Serialized payload _ -> payload
  in
  let va = vpattern_replace (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_array_iterator_length) CborST.parse_raw_data_item) _) in
  vpattern_rewrite (fun a -> LPS.aparse (LPS.parse_nlist (U64.v i.cbor_array_iterator_length) CborST.parse_raw_data_item) a _) a;
  intro_implies
    (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_array_iterator_length) CborST.parse_raw_data_item) a va `star` GR.pts_to i.footprint p ())
    (cbor_array_iterator_match_serialized p i l)
    emp
    (fun _ -> noop (); noop ());
  implies_trans
    (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_array_iterator_length) CborST.parse_raw_data_item) a va `star` GR.pts_to i.footprint p ())
    (cbor_array_iterator_match_serialized p i l)
    (cbor_array_iterator_match p i2 l);
  let len' = i.cbor_array_iterator_length `U64.sub` 1uL in
  let ga' = LPS.elim_nlist_cons
    CborST.parse_raw_data_item
    (U64.v i.cbor_array_iterator_length)
    (U64.v len')
    a
  in
  let _ = gen_elim () in
  let vl = vpattern_replace (LPS.aparse CborST.parse_raw_data_item a) in
  let sz = LPS.get_parsed_size CborST.jump_raw_data_item a in
  let a' = LPS.hop_aparse_aparse_with_size CborST.parse_raw_data_item (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a sz ga' in
  let va1 = vpattern_replace (LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a') in
  intro_implies
    (LPS.aparse CborST.parse_raw_data_item a vl `star` LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a' va1)
    (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_array_iterator_length) CborST.parse_raw_data_item) a va)
    emp
    (fun _ ->
      let _ = LPS.intro_nlist_cons (U64.v i.cbor_array_iterator_length) CborST.parse_raw_data_item (U64.v len') a a' in
      vpattern_rewrite
        (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_array_iterator_length) CborST.parse_raw_data_item) a)
        va
    );
  implies_trans_l1
    (LPS.aparse CborST.parse_raw_data_item a vl `star` LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a' va1)
    (LPS.aparse (LPS.parse_nlist (U64.v i.cbor_array_iterator_length) CborST.parse_raw_data_item) a va)
    (GR.pts_to i.footprint p ())
    (cbor_array_iterator_match p i2 l);
  implies_with_tactic
    (LPS.aparse CborST.parse_raw_data_item a vl `star` (LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a' va1 `star` GR.pts_to i.footprint p ()))
    ((LPS.aparse CborST.parse_raw_data_item a vl `star` LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a' va1) `star` GR.pts_to i.footprint p ());
  implies_trans
    (LPS.aparse CborST.parse_raw_data_item a vl `star` (LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a' va1 `star` GR.pts_to i.footprint p ()))
    ((LPS.aparse CborST.parse_raw_data_item a vl `star` LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a' va1) `star` GR.pts_to i.footprint p ())
    (cbor_array_iterator_match p i2 l);
  let res = read_valid_cbor_from_buffer_with_size_strong p a sz in
  vpattern_rewrite_with_implies (raw_data_item_match p res) (List.Tot.hd l);
  implies_trans
    (raw_data_item_match p res (List.Tot.hd l))
    (raw_data_item_match p res _)
    (LPS.aparse CborST.parse_raw_data_item a vl);
  implies_trans_l1
    (raw_data_item_match p res (List.Tot.hd l))
    (LPS.aparse CborST.parse_raw_data_item a vl)
    (LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a' va1 `star` GR.pts_to i.footprint p ())
    (cbor_array_iterator_match p i2 l);
  let i' = {
    cbor_array_iterator_length = len';
    cbor_array_iterator_payload = CBOR_Array_Iterator_Payload_Serialized a' (LPA.set_array_perm (LPS.array_of va1) (LPA.array_perm (LPS.array_of va1) `div_perm` p));
    footprint = i.footprint;
  }
  in
  R.write pi i';
  vpattern_rewrite_with_implies (fun r -> GR.pts_to r _ _) i'.footprint;
  let va' = LPS.rewrite_aparse_with_implies a' (LPS.parse_nlist (U64.v i'.cbor_array_iterator_length) CborST.parse_raw_data_item) in
  implies_join
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_array_iterator_length) CborST.parse_raw_data_item) a' va')
    (LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a' va1)
    (GR.pts_to i'.footprint p ())
    (GR.pts_to i.footprint p ());
  implies_trans_r1
    (raw_data_item_match p res (List.Tot.hd l))
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_array_iterator_length) CborST.parse_raw_data_item) a' va' `star` GR.pts_to i'.footprint p ())
    (LPS.aparse (LPS.parse_nlist (U64.v len') CborST.parse_raw_data_item) a' va1 `star` GR.pts_to i.footprint p ())
    (cbor_array_iterator_match p i2 l);
  rewrite_with_implies
    (cbor_array_iterator_match_serialized p i' (List.Tot.tl l))
    (cbor_array_iterator_match p i' (List.Tot.tl l));
  intro_implies
    (cbor_array_iterator_match_serialized p i' (List.Tot.tl l))
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_array_iterator_length) CborST.parse_raw_data_item) a' va' `star` GR.pts_to i'.footprint p ())
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite
        (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_array_iterator_length) CborST.parse_raw_data_item) _ _)
        (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_array_iterator_length) CborST.parse_raw_data_item) a' va')
    );
  implies_trans
    (cbor_array_iterator_match p i' (List.Tot.tl l))
    (cbor_array_iterator_match_serialized p i' (List.Tot.tl l))
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_array_iterator_length) CborST.parse_raw_data_item) a' va' `star` GR.pts_to i'.footprint p ());
  implies_trans_r1
    (raw_data_item_match p res (List.Tot.hd l))
    (cbor_array_iterator_match p i' (List.Tot.tl l))
    (LPS.aparse (LPS.parse_nlist (U64.v i'.cbor_array_iterator_length) CborST.parse_raw_data_item) a' va' `star` GR.pts_to i'.footprint p ())
    (cbor_array_iterator_match p i2 l);
  return res

#pop-options

let cbor_array_iterator_next
  pi
= let i = R.read pi in
  match i.cbor_array_iterator_payload with
  | CBOR_Array_Iterator_Payload_Array _ _ ->
    return (cbor_array_iterator_next_array i pi)
  | _ ->
    return (cbor_array_iterator_next_serialized i pi)

inline_for_extraction
noextract
let read_cbor_array_payload
  (p: perm)
  (n0: U64.t)
  (vl0: LPS.v (LowParse.Spec.VCList.parse_nlist_kind (U64.v n0) CborST.parse_raw_data_item_kind) (LowParse.Spec.VCList.nlist (U64.v n0) Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (#va0: Ghost.erased (Seq.seq cbor))
  (a0: A.array cbor)
: ST (Ghost.erased (Seq.seq cbor))
    (A.pts_to a0 full_perm va0 `star`
      LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) CborST.parse_raw_data_item) l0 vl0
    )
    (fun res ->
      A.pts_to a0 full_perm res `star`
      raw_data_item_array_match p res vl0.contents `star`
      (raw_data_item_array_match p res vl0.contents `implies_`
        LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) CborST.parse_raw_data_item) l0 vl0
      )
    )
    (A.length a0 == U64.v n0 /\
      p `lesser_equal_perm` full_perm /\
      SZ.fits_u64
    )
    (fun _ -> True)
=
  let n0_as_sz = SZ.uint64_to_sizet n0 in
  let vl = LPS.rewrite_aparse_with_implies l0 (LPS.parse_nlist (SZ.v n0_as_sz) CborST.parse_raw_data_item) in
  let res = LPS.read_array_payload_from_nlist CborST.jump_raw_data_item (raw_data_item_match p) (fun a alen -> read_valid_cbor_from_buffer_with_size_strong p a alen) n0_as_sz l0 a0 in
  implies_trans
    (LPS.seq_list_match res vl.contents (raw_data_item_match p))
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (SZ.v n0_as_sz) CborST.parse_raw_data_item) l0 vl)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) CborST.parse_raw_data_item) l0 vl0);
  rewrite_with_implies_with_tactic
    (LPS.seq_list_match res vl.contents (raw_data_item_match p))
    (raw_data_item_array_match p res vl.contents);
  implies_trans
    (raw_data_item_array_match p res vl.contents)
    (LPS.seq_list_match res vl.contents (raw_data_item_match p))
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) CborST.parse_raw_data_item) l0 vl0);
  rewrite_with_implies
    (raw_data_item_array_match p res vl.contents)
    (raw_data_item_array_match p res vl0.contents);
  implies_trans
    (raw_data_item_array_match p res vl0.contents)
    (raw_data_item_array_match p res vl.contents)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) CborST.parse_raw_data_item) l0 vl0);
  return res

let array_lower_perm
  (#t: Type)
  (#opened: _)
  (#high: perm)
  (#v: Seq.seq t)
  (r: A.array t)
  (low: perm)
: STGhost unit opened
    (A.pts_to r high v)
    (fun _ -> A.pts_to r low v `star`
      (A.pts_to r low v `implies_` A.pts_to r high v)
    )
    (low `lesser_equal_perm` high)
    (fun _ -> True)
= if FStar.StrongExcludedMiddle.strong_excluded_middle (low == high)
  then
    vpattern_rewrite_with_implies
      (fun p -> A.pts_to _ p _)
      low
  else begin
    let diff = diff_perm high low in
    A.share r high low diff;
    intro_implies
      (A.pts_to r low v)
      (A.pts_to r high v)
      (A.pts_to r diff v)
      (fun _ ->
        A.gather r low diff;
        vpattern_rewrite (fun p -> A.pts_to _ p _) high
      )
  end

#push-options "--z3rlimit 64"
#restart-solver

let cbor_read_array
  #p #obj input a0 len
= 
  raw_data_item_match_perm_le_full_perm input;
  A.pts_to_length a0 _;
  raw_data_item_match_get_case input;
  match input with
  | CBOR_Case_Array _ _ ->
    let res = cbor_destr_array input in
    A.pts_to_length res.cbor_array_payload _;
    SM.seq_list_match_length (raw_data_item_match p) res.footprint (maybe_cbor_array obj);
    implies_concl_r
      (A.pts_to _ _ _ `star` raw_data_item_array_match p _ _)
      (raw_data_item_match p _ _)
      (exists_ (A.pts_to a0 full_perm));
    return res.cbor_array_payload
  | _ ->
    let s = destr_cbor_serialized input in
    let _ = gen_elim () in
    let a = CBOR.SteelST.Raw.Array.focus_array_with_ghost_length (U64.v len) s.cbor_serialized_payload in
    let _ = gen_elim () in
    implies_trans
      (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) CborST.parse_raw_data_item) a _)
      (LPS.aparse CborST.parse_raw_data_item s.cbor_serialized_payload _)
      (raw_data_item_match p input _);
    let _ = A.intro_fits_u64 () in
    let va = read_cbor_array_payload p len _ a a0 in
    implies_trans
      (raw_data_item_array_match p va _)
      (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) CborST.parse_raw_data_item) a _)
      (raw_data_item_match p input _);
    rewrite_with_implies
      (raw_data_item_array_match p _ _)
      (raw_data_item_array_match p va (maybe_cbor_array obj));
    SM.seq_list_match_length (raw_data_item_match p) va (maybe_cbor_array obj);
    implies_trans
      (raw_data_item_array_match p va (maybe_cbor_array obj))
      (raw_data_item_array_match p _ _)
      (raw_data_item_match p input _);
    array_lower_perm a0 p;
    intro_implies
      (A.pts_to a0 full_perm va)
      (exists_ (A.pts_to a0 full_perm))
      emp
      (fun _ -> noop ());
    implies_trans
      (A.pts_to _ _ _)
      (A.pts_to _ _ _)
      (exists_ (A.pts_to _ _));
    implies_join
      (A.pts_to _ _ _)
      (exists_ (A.pts_to _ _))
      (raw_data_item_array_match p _ _)
      (raw_data_item_match p _ _);
    implies_swap_r
      (A.pts_to _ _ _ `star` raw_data_item_array_match p _ _)
      (exists_ (A.pts_to _ _))
      (raw_data_item_match p _ _);
    return a0

#pop-options

#push-options "--split_queries always"
#restart-solver

let serialize_cbor_array_eq
  (c: Cbor.raw_data_item { Cbor.Array? c })
: Lemma
  (
    let s0 = LPS.serialize CborST.serialize_raw_data_item c in
    let s1 = LPS.serialize CborST.serialize_header (CborST.uint64_as_argument Cbor.cbor_major_type_array (U64.uint_to_t (List.Tot.length (Cbor.Array?.v c)))) in
    let s2 = LPS.serialize (LPS.serialize_nlist (List.Tot.length (Cbor.Array?.v c)) CborST.serialize_raw_data_item) (Cbor.Array?.v c) in
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

#pop-options

#push-options "--z3rlimit 64"
#restart-solver

inline_for_extraction
noextract
let size_comp_for_array
  (size:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_size_comp_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Array? c})
: Tot (cbor_size_comp_for va c)
= fun #p sz perr ->
    let _ = A.intro_fits_u64 () in
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Array? va) = () in
    serialize_cbor_array_eq va;
    let c' = cbor_destr_array c in
    let l = Ghost.hide (maybe_cbor_array va) in
    assert (Ghost.reveal l == Cbor.Array?.v va);
    rewrite_with_implies_with_tactic
      (raw_data_item_array_match p _ _)
      (LPS.seq_list_match c'.footprint l (raw_data_item_match p));
    implies_trans_r1
      (A.pts_to _ _ _)
      (LPS.seq_list_match c'.footprint l (raw_data_item_match p))
      (raw_data_item_array_match p _ _)
      (raw_data_item_match p _ _);
    LPS.seq_list_match_length (raw_data_item_match p) _ _;
    A.pts_to_length _ _;
    let sz1 = CBOR.SteelST.Raw.Write.size_comp_uint64_header Cbor.cbor_major_type_array c'.cbor_array_length sz perr in
    let _ = gen_elim () in
    let err1 = R.read perr in
    if err1
    then begin
      noop ();
      elim_implies
        (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l (raw_data_item_match p))
        (raw_data_item_match p _ _);
      return sz1
    end else begin
      noop ();
      let sz2 = LPS.array_payload_as_nlist_size
        CborST.serialize_raw_data_item
        (raw_data_item_match p)
        (fun x y sz perr ->
          let res = size y x sz perr in
          let _ = gen_elim () in
          return res
        )
        #c'.footprint
        #l
        (SZ.uint64_to_sizet c'.cbor_array_length)
        c'.cbor_array_payload
        sz1
        perr
      in
      let _ = gen_elim () in
      elim_implies
        (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l (raw_data_item_match p))
        (raw_data_item_match p _ _);
      return sz2
    end

#restart-solver

inline_for_extraction
noextract
let l2r_writer_for_array
  (write:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_l2r_writer_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Array? c})
: Tot (cbor_l2r_writer_for va c)
= fun #p #vout out ->
    let _ = A.intro_fits_u64 () in
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Array? va) = () in
    serialize_cbor_array_eq va;
    let c' = cbor_destr_array c in
    let l = Ghost.hide (maybe_cbor_array va) in
    assert (Ghost.reveal l == Cbor.Array?.v va);
    rewrite_with_implies_with_tactic
      (raw_data_item_array_match p _ _)
      (LPS.seq_list_match c'.footprint l (raw_data_item_match p));
    implies_trans_r1
      (A.pts_to _ _ _)
      (LPS.seq_list_match c'.footprint l (raw_data_item_match p))
      (raw_data_item_array_match p _ _)
      (raw_data_item_match p _ _);
    LPS.seq_list_match_length (raw_data_item_match p) _ _;
    A.pts_to_length _ _;
    let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header Cbor.cbor_major_type_array c'.cbor_array_length out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer CborST.serialize_header res in
    let res_pl = LPS.l2r_write_array_payload_as_nlist
      CborST.serialize_raw_data_item
      (raw_data_item_match p)
      (fun x y out ->
         let res = write y x out in
         let _ = gen_elim () in
         return res
      )
      #c'.footprint
      #l
      (SZ.uint64_to_sizet c'.cbor_array_length)
      c'.cbor_array_payload
      out
    in
    let _ = gen_elim () in
    let vout' = vpattern_replace (LW.vp out) in
    let _ = LPS.elim_aparse_with_serializer (LPS.serialize_nlist (SZ.v (SZ.uint64_to_sizet c'.cbor_array_length)) CborST.serialize_raw_data_item) res_pl in
    let _ = LPA.join res res_pl in
    let _ = gen_elim () in
    let vres = LPS.intro_aparse_with_serializer CborST.serialize_raw_data_item va res in
    elim_implies
      (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l (raw_data_item_match p))
      (raw_data_item_match p _ _);
    assert_ (cbor_l2r_writer_for_post p va c vout out res vres vout'); // FIXME: WHY WHY WHY?
    return res

#pop-options

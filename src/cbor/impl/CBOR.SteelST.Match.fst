module CBOR.SteelST.Match
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.Spec // for serialize_cbor
friend CBOR.SteelST.Type // for type definition
friend CBOR.SteelST.Type.Def // for footprint types
open CBOR.SteelST.Type.Def

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let prod_perm
  (p1 p2: perm)
: Tot perm
= MkPerm ((let open FStar.Real in ( *. )) p1.v p2.v)

let raw_data_item_match_serialized_prop
  (p: perm)
  (fp: cbor_footprint_t)
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: LPS.byte_array)
  (w: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Serialized c fp' ->
    c.cbor_serialized_size == LPA.len (LPS.array_of w) /\
    c.cbor_serialized_payload == a /\
    LPS.array_of w == LPA.set_array_perm c.footprint (p `prod_perm` LPA.array_perm c.footprint) /\
    fp == fp' /\
    w.LPS.contents == v
  | _ -> False

[@@__reduce__]
let raw_data_item_match_serialized0
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun (a: LPS.byte_array) -> exists_ (fun (w: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item) -> exists_ (fun fp ->
    GR.pts_to fp p () `star`
    LPS.aparse CborST.parse_raw_data_item a w `star`
    pure (
      raw_data_item_match_serialized_prop p fp c v a w
    )
  )))

let raw_data_item_match_simple_value_prop
  (fp: cbor_footprint_t)
  (c: cbor)
  (v: Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Simple_value c fp' ->
    v == Cbor.Simple c /\
    fp == fp'
  | _ -> False

[@@__reduce__]
let raw_data_item_match_simple_value0
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun fp ->
    GR.pts_to fp p () `star`
    pure (raw_data_item_match_simple_value_prop fp c v)
  )

let raw_data_item_match_int_prop
  (fp: cbor_footprint_t)
  (c: cbor)
  (v: Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Int64 c fp' ->
    v == Cbor.Int64 c.cbor_int_type c.cbor_int_value /\
    fp == fp'
  | _ -> False

[@@__reduce__]
let raw_data_item_match_int0
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun fp ->
    GR.pts_to fp p () `star`
    pure (raw_data_item_match_int_prop fp c v)
  )

let raw_data_item_match_string_prop
  (p0: perm)
  (fp: cbor_footprint_t)
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: A.array U8.t)
  (p: perm)
  (w: Seq.seq U8.t)
: Tot prop
= match c with
  | CBOR_Case_String c fp' p' ->
    U64.v c.cbor_string_length == Seq.length w /\
    v == Cbor.String c.cbor_string_type w /\
    p == p0 `prod_perm` p' /\
    fp' == fp /\
    c.cbor_string_payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_string0
  (p0: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun a -> exists_ (fun p -> exists_ (fun w -> exists_ (fun fp ->
    GR.pts_to fp p0 () `star`
    A.pts_to a p w `star`
    pure (raw_data_item_match_string_prop p0 fp c v a p w)
  ))))

unfold
let raw_data_item_match_tagged_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: R.ref cbor)
  (c': cbor)
  (v': Cbor.raw_data_item)
: Tot prop
= match v, c with
  | Cbor.Tagged tag v2, CBOR_Case_Tagged c ->
    c.cbor_tagged0_tag == tag /\
    Ghost.reveal c.footprint == c' /\
    v2 == v' /\
    c.cbor_tagged0_payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_tagged0
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun a -> exists_ (fun c' -> exists_ (fun v' ->
    R.pts_to a p c' `star`
    raw_data_item_match c' v' `star`
    pure (raw_data_item_match_tagged_prop c v a c' v')
  )))

let raw_data_item_match_array_prop
  (fp: cbor_footprint_t)
  (c: cbor)
  (v: Cbor.raw_data_item)
  (s: Seq.seq cbor)
  (a: A.array cbor)
: GTot prop
= match c, v with
  | CBOR_Case_Array c fp', Cbor.Array l ->
    U64.v c.cbor_array_length == List.Tot.length l /\
    Ghost.reveal c.footprint == s /\
    fp' == fp /\
    c.cbor_array_payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_array0
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Array? v })
  (raw_data_item_array_match: (Seq.seq cbor -> (v': list Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: A.array cbor) -> exists_ (fun (c': Seq.seq cbor) -> exists_ (fun fp ->
    GR.pts_to fp p () `star`
    A.pts_to a p c' `star`
    raw_data_item_array_match c' (Cbor.Array?.v v) `star`
    pure (
      raw_data_item_match_array_prop fp c v c' a
    )
  )))

let raw_data_item_match_map_prop
  (fp: cbor_footprint_t)
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: A.array cbor_map_entry)
  (s: Seq.seq cbor_map_entry)
: GTot prop
= match c, v with
  | CBOR_Case_Map c fp', Cbor.Map l ->
    U64.v c.cbor_map_length == List.Tot.length l /\
    Ghost.reveal c.footprint == s /\
    fp' == fp /\
    c.cbor_map_payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_map0
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Map? v })
  (raw_data_item_map_match: (Seq.seq cbor_map_entry -> (v': list (Cbor.raw_data_item & Cbor.raw_data_item) { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: A.array cbor_map_entry) -> exists_ (fun (c': Seq.seq cbor_map_entry) -> exists_ (fun fp ->
    GR.pts_to fp p () `star`
    A.pts_to a p c' `star`
    raw_data_item_map_match c' (Cbor.Map?.v v) `star`
    pure (
      raw_data_item_match_map_prop fp c v a c'
    )
  )))

let raw_data_item_map_entry_match'
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << l }) -> vprop))
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item) { v1 << l })
: Tot vprop
= raw_data_item_map_entry_match1 c1 v1 raw_data_item_match

let rec raw_data_item_match
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= match c, v with
  | CBOR_Case_Serialized _ _, _ -> raw_data_item_match_serialized0 p c v
  | CBOR_Case_Simple_value _ _, Cbor.Simple _ -> raw_data_item_match_simple_value0 p c v
  | CBOR_Case_Int64 _ _, Cbor.Int64 _ _ -> raw_data_item_match_int0 p c v
  | CBOR_Case_String _ _ _, Cbor.String _ _ -> raw_data_item_match_string0 p c v
  | CBOR_Case_Array _ _, Cbor.Array _ -> raw_data_item_match_array0 p c v (raw_data_item_array_match' p)
  | CBOR_Case_Map _ _, Cbor.Map _ -> raw_data_item_match_map0 p c v (raw_data_item_map_match' p)
  | CBOR_Case_Tagged _, Cbor.Tagged _ _ -> raw_data_item_match_tagged0 p c v (raw_data_item_match p)
  | _ -> pure False

and raw_data_item_array_match'
  (p: perm)
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= LPS.seq_list_match c v (raw_data_item_match p)

and raw_data_item_map_match'
  (p: perm)
  (c: Seq.seq cbor_map_entry)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
  (decreases v)
= LPS.seq_list_match c v (raw_data_item_map_entry_match' v (raw_data_item_match p))

#set-options "--ide_id_info_off"

let raw_data_item_match_get_case
  (#opened: _)
  (#p: perm)
  (#v: Cbor.raw_data_item)
  (c: cbor)
: STGhost unit opened
    (raw_data_item_match p c v)
    (fun _ -> raw_data_item_match p c v)
    True
    (fun _ -> match c, v with
    | CBOR_Case_Serialized _ _, _
    | CBOR_Case_Array _ _, Cbor.Array _
    | CBOR_Case_Int64 _ _, Cbor.Int64 _ _
    | CBOR_Case_Map _ _, Cbor.Map _
    | CBOR_Case_Simple_value _ _, Cbor.Simple _
    | CBOR_Case_String _ _ _, Cbor.String _ _
    | CBOR_Case_Tagged _, Cbor.Tagged _ _
      -> True
    | _ -> False
    )
= match c, v with
    | CBOR_Case_Serialized _ _, _
    | CBOR_Case_Array _ _, Cbor.Array _
    | CBOR_Case_Int64 _ _, Cbor.Int64 _ _
    | CBOR_Case_Map _ _, Cbor.Map _
    | CBOR_Case_Simple_value _ _, Cbor.Simple _
    | CBOR_Case_String _ _ _, Cbor.String _ _
    | CBOR_Case_Tagged _, Cbor.Tagged _ _
      -> noop ()
    | _ ->
      rewrite (raw_data_item_match p c v) (pure False);
      let _ = gen_elim () in
      rewrite emp (raw_data_item_match p c v)

let raw_data_item_match_perm_le_full_perm
  (#opened: _)
  (#p: perm)
  (#v: Cbor.raw_data_item)
  (c: cbor)
: STGhost unit opened
    (raw_data_item_match p c v)
    (fun _ -> raw_data_item_match p c v)
    True
    (fun _ -> p `lesser_equal_perm` full_perm)
= match c, v with
    | CBOR_Case_Serialized _ _, _ ->
      rewrite
        (raw_data_item_match p c v)
        (raw_data_item_match_serialized0 p c v);
      let _ = gen_elim () in
      GR.pts_to_perm _;
      rewrite 
        (raw_data_item_match_serialized0 p c v)
        (raw_data_item_match p c v)
    | CBOR_Case_Int64 _ _, Cbor.Int64 _ _ ->
      rewrite
        (raw_data_item_match p c v)
        (raw_data_item_match_int0 p c v);
      let _ = gen_elim () in
      GR.pts_to_perm _;
      rewrite
        (raw_data_item_match_int0 p c v)
        (raw_data_item_match p c v)
    | CBOR_Case_Simple_value _ _, Cbor.Simple _ ->
      rewrite
        (raw_data_item_match p c v)
        (raw_data_item_match_simple_value0 p c v);
      let _ = gen_elim () in
      GR.pts_to_perm _;
      rewrite
        (raw_data_item_match_simple_value0 p c v)
        (raw_data_item_match p c v)
    | CBOR_Case_String _ _ _, Cbor.String _ _ ->
      rewrite
        (raw_data_item_match p c v)
        (raw_data_item_match_string0 p c v);
      let _ = gen_elim () in
      GR.pts_to_perm _;
      rewrite
        (raw_data_item_match_string0 p c v)
        (raw_data_item_match p c v)
    | CBOR_Case_Array a sfp, Cbor.Array v0 ->
      assert_norm (
        raw_data_item_match p (CBOR_Case_Array a sfp) (Cbor.Array v0) ==
          raw_data_item_match_array0 p (CBOR_Case_Array a sfp) (Cbor.Array v0) (raw_data_item_array_match' p)
      );
      rewrite
        (raw_data_item_match p c v)
        (raw_data_item_match_array0 p c v (raw_data_item_array_match' p));
      let _ = gen_elim () in
      GR.pts_to_perm _;
      rewrite
        (raw_data_item_match_array0 p c v (raw_data_item_array_match' p))
        (raw_data_item_match p c v)
    | CBOR_Case_Map a sfp, Cbor.Map v0 ->
      assert_norm (
        raw_data_item_match p (CBOR_Case_Map a sfp) (Cbor.Map v0) ==
          raw_data_item_match_map0 p (CBOR_Case_Map a sfp) (Cbor.Map v0) (raw_data_item_map_match' p)
      );
      rewrite
        (raw_data_item_match p c v)
        (raw_data_item_match_map0 p c v (raw_data_item_map_match' p));
      let _ = gen_elim () in
      GR.pts_to_perm _;
      rewrite
        (raw_data_item_match_map0 p c v (raw_data_item_map_match' p))
        (raw_data_item_match p c v)
    | CBOR_Case_Tagged a, Cbor.Tagged tg v0 ->
      assert_norm (
        raw_data_item_match p (CBOR_Case_Tagged a) (Cbor.Tagged tg v0) ==
          raw_data_item_match_tagged0 p (CBOR_Case_Tagged a) (Cbor.Tagged tg v0) (raw_data_item_match p)
      );
      rewrite
        (raw_data_item_match p c v)
        (raw_data_item_match_tagged0 p c v (raw_data_item_match p));
      let _ = gen_elim () in
      R.pts_to_perm _;
      rewrite
        (raw_data_item_match_tagged0 p c v (raw_data_item_match p))
        (raw_data_item_match p c v)
    | _ ->
      rewrite
        (raw_data_item_match p c v)
        (pure False);
      let _ = gen_elim () in
      rewrite // by contradiction
        emp
        (raw_data_item_match p c v)

let diff_perm
  (high low: perm)
: Pure perm
  (requires (
    low `lesser_equal_perm` high /\
    (~ (low == high))
  ))
  (ensures (fun diff ->
    high == low `sum_perm` diff
  ))
= MkPerm ((let open FStar.Real in ( -. )) high.v low.v)

let gref_lower_perm
  (#t: Type)
  (#opened: _)
  (#high: perm)
  (#v: t)
  (r: GR.ref t)
  (low: perm)
: STGhost unit opened
    (GR.pts_to r high v)
    (fun _ -> GR.pts_to r low v `star`
      (GR.pts_to r low v `implies_` GR.pts_to r high v)
    )
    (low `lesser_equal_perm` high)
    (fun _ -> True)
= if FStar.StrongExcludedMiddle.strong_excluded_middle (low == high)
  then
    vpattern_rewrite_with_implies
      (fun p -> GR.pts_to _ p _)
      low
  else begin
    let diff = diff_perm high low in
    GR.share_gen r low diff;
    intro_implies
      (GR.pts_to r low v)
      (GR.pts_to r high v)
      (GR.pts_to r diff v)
      (fun _ ->
        GR.gather #_ #_ #low r;
        vpattern_rewrite (fun p -> GR.pts_to _ p _) high
      )
  end

let div_perm
  (a b: perm)
: Pure perm
    (requires True)
    (ensures (fun q ->
      a == b `prod_perm` q
    ))
= MkPerm ((let open FStar.Real in ( /. )) a.v b.v)

let read_valid_cbor_from_buffer_with_size_strong
  (#va: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item)
  (p: perm)
  (a: LPS.byte_array)
  (alen: SZ.t)
: ST cbor
    (LPS.aparse CborST.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match p c' va.contents `star`
      (raw_data_item_match p c' va.contents `implies_` LPS.aparse CborST.parse_raw_data_item a va)
    )
    (alen == LPA.len (LPS.array_of va) /\
      p `lesser_equal_perm` full_perm
    )
    (fun c' -> CBOR_Case_Serialized? c')
= [@@inline_let]
  let c_pl : cbor_serialized = ({
    cbor_serialized_size = alen;
    cbor_serialized_payload = a;
    footprint = LPA.set_array_perm (LPS.array_of va) (div_perm (LPA.array_perm (LPS.array_of va)) p);
  })
  in
  let fp = GR.alloc () in
  gref_lower_perm fp p;
  [@@inline_let]
  let c' = CBOR_Case_Serialized c_pl fp in
  noop ();
  rewrite_with_implies
    (raw_data_item_match_serialized0 p (CBOR_Case_Serialized c_pl fp) va.contents)
    (raw_data_item_match p c' va.contents);
  intro_implies
    (raw_data_item_match_serialized0 p (CBOR_Case_Serialized c_pl fp) va.contents)
    (LPS.aparse CborST.parse_raw_data_item a va)
    (GR.pts_to fp p () `implies_` GR.pts_to fp full_perm ())
    (fun _ ->
      let _ = gen_elim () in
      rewrite (GR.pts_to _ _ _) (GR.pts_to fp p ());
      elim_implies (GR.pts_to _ _ _) (GR.pts_to _ _ _);
      GR.free _;
      rewrite (LPS.aparse CborST.parse_raw_data_item _ _) (LPS.aparse CborST.parse_raw_data_item a va) // works thanks to c_pl.footprint
    );
  implies_trans
    (raw_data_item_match p c' va.contents)
    (raw_data_item_match_serialized0 p (CBOR_Case_Serialized c_pl fp) va.contents)
    (LPS.aparse CborST.parse_raw_data_item a va);
  return c'

let read_valid_cbor_from_buffer_with_size
  (#va: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
  (alen: SZ.t)
: ST cbor
    (LPS.aparse CborST.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match full_perm c' va.contents
    )
    (alen == LPA.len (LPS.array_of va))
    (fun c' -> CBOR_Case_Serialized? c')
= let c' = read_valid_cbor_from_buffer_with_size_strong full_perm a alen in
  drop (_ `implies_` _);
  return c'

let read_valid_cbor_from_buffer
  (#va: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
: STT cbor
    (LPS.aparse CborST.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match full_perm c' va.contents
    )
= let alen = LPS.get_parsed_size CborST.jump_raw_data_item a in
  read_valid_cbor_from_buffer_with_size a alen

let destr_cbor_serialized
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_serialized
    (raw_data_item_match p c va)
    (fun c' -> exists_ (fun vc ->
      LPS.aparse CborST.parse_raw_data_item c'.cbor_serialized_payload vc `star`
      (LPS.aparse CborST.parse_raw_data_item c'.cbor_serialized_payload vc `implies_`
        raw_data_item_match p c va
      ) `star`
      pure (
        vc.LPS.contents == Ghost.reveal va /\
        LPA.length (LPS.array_of vc) == SZ.v c'.cbor_serialized_size
    )))
    (CBOR_Case_Serialized? c)
    (fun _ -> True)
= let CBOR_Case_Serialized c' fp = c in
  rewrite_with_implies
    (raw_data_item_match p c va)
    (raw_data_item_match_serialized0 p (CBOR_Case_Serialized c' fp) va);
  let _ = gen_elim () in
  rewrite (GR.pts_to _ _ _) (GR.pts_to fp p ());
  let vc = vpattern_replace (LPS.aparse CborST.parse_raw_data_item _) in
  vpattern_rewrite (fun a -> LPS.aparse CborST.parse_raw_data_item a _) c'.cbor_serialized_payload;
  intro_implies
    (LPS.aparse CborST.parse_raw_data_item c'.cbor_serialized_payload vc)
    (raw_data_item_match_serialized0 p (CBOR_Case_Serialized c' fp) va)
    (GR.pts_to fp p ())
    (fun _ ->
      noop (); noop () // FIXME: WHY WHY WHY do I need an explicit bind here?
    );
  implies_trans
    (LPS.aparse CborST.parse_raw_data_item c'.cbor_serialized_payload vc)
    (raw_data_item_match_serialized0 p (CBOR_Case_Serialized c' fp) va)
    (raw_data_item_match p c va);
  return c'

let elim_aparse_with_serializer_with_implies
  (#opened: _)
  (#k: LPS.parser_kind)
  (#t: Type)
  (#vp: LPS.v k t)
  (#p: LPS.parser k t)
  (s: LPS.serializer p)
  (a: LPS.byte_array)
: STGhost (LPA.v LPS.byte) opened
    (LPS.aparse p a vp)
    (fun va -> LPA.arrayptr a va `star` (LPA.arrayptr a va `implies_` LPS.aparse p a vp))
    True
    (fun va ->
      LPA.array_of va == LPS.array_of vp /\
      LPS.arrayptr_parse p va == Some vp /\
      LPS.serialize s vp.contents == LPA.contents_of va
    )
= let res = LPS.elim_aparse_with_serializer s a in
  intro_implies
    (LPA.arrayptr a res)
    (LPS.aparse p a vp)
    emp
    (fun _ ->
      let _ = LPS.intro_aparse p a in
      vpattern_rewrite (LPS.aparse p a) vp
    );
  res

let cbor_compare_aux
  #p1 #p2 #v1 #v2 a1 a2
= Cbor.cbor_compare_correct v1 v2;
  match a1, a2 with
  | CBOR_Case_Serialized _ _, CBOR_Case_Serialized _ _ ->
    let s1 = destr_cbor_serialized a1 in
    let _ = gen_elim () in
    let _ = elim_aparse_with_serializer_with_implies CborST.serialize_raw_data_item s1.cbor_serialized_payload in
    implies_trans
      (LPA.arrayptr s1.cbor_serialized_payload _)
      (LPS.aparse CborST.parse_raw_data_item s1.cbor_serialized_payload _)
      (raw_data_item_match p1 a1 v1);
    let s2 = destr_cbor_serialized a2 in
    let _ = gen_elim () in
    let _ = elim_aparse_with_serializer_with_implies CborST.serialize_raw_data_item s2.cbor_serialized_payload in
    implies_trans
      (LPA.arrayptr s2.cbor_serialized_payload _)
      (LPS.aparse CborST.parse_raw_data_item s2.cbor_serialized_payload _)
      (raw_data_item_match p2 a2 v2);
    let i = LowParse.SteelST.SeqBytes.byte_array_lex_compare s1.cbor_serialized_size s1.cbor_serialized_payload s2.cbor_serialized_size s2.cbor_serialized_payload in
    elim_implies
      (LPA.arrayptr s1.cbor_serialized_payload _)
      (raw_data_item_match p1 a1 v1);
    elim_implies
      (LPA.arrayptr s2.cbor_serialized_payload _)
      (raw_data_item_match p2 a2 v2);
    let res = if i `FStar.Int16.lt` 0s then -1s else if 0s `FStar.Int16.lt` i then 1s else 0s in
    return res
  | _ -> return 2s // implemented in Pulse

(* Serialization *)

inline_for_extraction
noextract
let cbor_size_comp_for
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: Tot Type
= (#p: perm) ->
  (sz: SZ.t) ->
  (perr: R.ref bool) ->
  STT SZ.t
    (raw_data_item_match p c (Ghost.reveal va) `star`
      R.pts_to perr full_perm false
    )
    (fun res ->
      raw_data_item_match p c (Ghost.reveal va) `star`
      exists_ (fun err ->
        R.pts_to perr full_perm err `star`
        pure (LowParse.SteelST.Write.size_comp_for_post CborST.serialize_raw_data_item va sz res err)
    ))

noextract
unfold
let l2r_write_cbor_post
  (va: Ghost.erased Cbor.raw_data_item)
  (vout: LPA.array LPS.byte)
  (vres: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item)
  (vout': LPA.array LPS.byte)
: Tot prop
=  
       LPA.merge_into (LPS.array_of vres) vout' vout /\
       vres.LPS.contents == Ghost.reveal va

[@@__reduce__]
let cbor_l2r_writer_for_post
  (p: perm)
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (vout: LPA.array LPS.byte)
  (out: LW.t)
  (res: LPS.byte_array)
  (vres: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item)
  (vout': LPA.array LPS.byte)
: Tot vprop
=
  raw_data_item_match p c (Ghost.reveal va) `star`
  LPS.aparse CborST.parse_raw_data_item res vres `star`
  LW.vp out vout' `star`
  pure (
    l2r_write_cbor_post va vout vres vout'
  )

inline_for_extraction
noextract
let cbor_l2r_writer_for
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: Tot Type
= (#p: perm) ->
  (#vout: LPA.array LPS.byte) ->
  (out: LW.t) ->
  ST LPS.byte_array
    (raw_data_item_match p c (Ghost.reveal va) `star`
      LW.vp out vout
    )
    (fun res -> exists_ (fun (vres: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item) -> exists_ (fun (vout': LPA.array LPS.byte) ->
      cbor_l2r_writer_for_post p va c vout out res vres vout'
    )))
    (Seq.length (LPS.serialize CborST.serialize_raw_data_item va) <= LPA.length vout)
    (fun _ -> True)

let size_comp_for_serialized
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Serialized? c})
: Tot (cbor_size_comp_for va c)
= fun #p sz perr ->
    let c' = destr_cbor_serialized c in
    let _ = gen_elim () in
    LPS.aparse_serialized_length CborST.serialize_raw_data_item _;
    elim_implies
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match p _ _);
    if c'.cbor_serialized_size `SZ.gt` sz
    then begin
      noop ();
      R.write perr true;
      return sz
    end else begin
      [@@inline_let]
      let res = sz `SZ.sub` c'.cbor_serialized_size in
      noop ();
      return res
    end

let l2r_writer_for_serialized
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Serialized? c})
: Tot (cbor_l2r_writer_for va c)
= fun #p #vout out ->
    let c' = destr_cbor_serialized c in
    let _ = gen_elim () in
    LPS.aparse_serialized_length CborST.serialize_raw_data_item _;
    let _ = LPS.elim_aparse_with_implies CborST.parse_raw_data_item c'.cbor_serialized_payload in
    implies_trans
      (LPA.arrayptr c'.cbor_serialized_payload _)
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match p _ _);
    let res = LW.split out c'.cbor_serialized_size in
    let _ = gen_elim () in
    let vout' = vpattern_replace (LW.vp out) in
    let _ = LPA.copy c'.cbor_serialized_payload res c'.cbor_serialized_size in
    let vres = LPS.intro_aparse CborST.parse_raw_data_item res in
    elim_implies
      (LPA.arrayptr c'.cbor_serialized_payload _)
      (raw_data_item_match p _ _);
    assert_ (cbor_l2r_writer_for_post p va c vout out res vres vout'); // FIXME: WHY WHY WHY?
    return res

(* Destructors *)

let maybe_cbor_map
  (v: Cbor.raw_data_item)
: GTot (list (Cbor.raw_data_item & Cbor.raw_data_item))
= match v with
  | Cbor.Map l -> l
  | _ -> []

let destr_cbor_map'
  (#opened: _)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { CBOR_Case_Map? a})
: STGhost unit opened
    (raw_data_item_match p a v)
    (fun res ->
      A.pts_to (CBOR_Case_Map?.v a).cbor_map_payload p (CBOR_Case_Map?.v a).footprint `star`
      LPS.seq_list_match (CBOR_Case_Map?.v a).footprint (maybe_cbor_map v) (raw_data_item_map_entry_match p) `star`
      GR.pts_to (CBOR_Case_Map?.self_footprint a) p ()
    )
    True
    (fun res ->
      Cbor.Map? v /\
      U64.v (CBOR_Case_Map?.v a).cbor_map_length == List.Tot.length (Cbor.Map?.v v)
    )
= raw_data_item_match_get_case _;
  let sq : squash (Cbor.Map? v) = () in
  let CBOR_Case_Map res fp = a in
  assert_norm
    (raw_data_item_match p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)) ==
      raw_data_item_match_map0 p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)) (raw_data_item_map_match' p));
  rewrite
    (raw_data_item_match p _ _)
    (raw_data_item_match_map0 p a v (raw_data_item_map_match' p));
  let _ = gen_elim () in
  rewrite
    (GR.pts_to _ _ _)
    (GR.pts_to (CBOR_Case_Map?.self_footprint a) p ());
  rewrite
    (A.pts_to _ _ _)
    (A.pts_to (CBOR_Case_Map?.v a).cbor_map_payload p (CBOR_Case_Map?.v a).footprint);
  rewrite
    (raw_data_item_map_match' p _ _)
    (raw_data_item_map_match' p (CBOR_Case_Map?.v a).footprint (maybe_cbor_map v));
  rewrite_with_tactic
    (raw_data_item_map_match' p (CBOR_Case_Map?.v a).footprint (maybe_cbor_map v))
    (LPS.seq_list_match (CBOR_Case_Map?.v a).footprint (maybe_cbor_map v) (raw_data_item_map_entry_match' (maybe_cbor_map v) (raw_data_item_match p)));
  LPS.seq_list_match_weaken (CBOR_Case_Map?.v a).footprint (maybe_cbor_map v) (raw_data_item_map_entry_match' (maybe_cbor_map v) (raw_data_item_match p)) (raw_data_item_map_entry_match p)
    (fun x y ->
      rewrite
        (raw_data_item_map_entry_match' (maybe_cbor_map v) (raw_data_item_match p) x y)
        (raw_data_item_map_entry_match p x y)
    )

let constr_cbor_map'
  (#opened: _)
  (p: perm)
  (a: cbor)
  (v: Cbor.raw_data_item)
  (pl: A.array cbor_map_entry)
  (vfp: Seq.seq cbor_map_entry)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (fp: GR.ref unit)
: STGhost unit opened
    (
      A.pts_to pl p vfp `star`
      LPS.seq_list_match vfp l (raw_data_item_map_entry_match p) `star`
      GR.pts_to fp p ()
    )
    (fun _ ->
      raw_data_item_match p a v
    )
    (
      Cbor.Map? v /\
      CBOR_Case_Map? a /\
      U64.v (CBOR_Case_Map?.v a).cbor_map_length == List.Tot.length (Cbor.Map?.v v) /\
      l == maybe_cbor_map v /\
      pl == (CBOR_Case_Map?.v a).cbor_map_payload /\
      vfp == Ghost.reveal (CBOR_Case_Map?.v a).footprint /\
      fp == (CBOR_Case_Map?.self_footprint a)
    )
    (fun _ -> True)
=
  let CBOR_Case_Map res fp = a in
  assert_norm
    (raw_data_item_match p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)) ==
      raw_data_item_match_map0 p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)) (raw_data_item_map_match' p));
  LPS.seq_list_match_weaken vfp l (raw_data_item_map_entry_match p) (raw_data_item_map_entry_match' l (raw_data_item_match p))
    (fun x y ->
       rewrite
         (raw_data_item_map_entry_match p x y)
         (raw_data_item_map_entry_match' l (raw_data_item_match p) x y)
    );
  rewrite_with_tactic
    (LPS.seq_list_match vfp l (raw_data_item_map_entry_match' l (raw_data_item_match p)))
    (raw_data_item_map_match' p vfp l);
  rewrite
    (raw_data_item_map_match' p vfp l) 
    (raw_data_item_map_match' p vfp (Cbor.Map?.v (Cbor.Map (maybe_cbor_map v))));
  rewrite
    (raw_data_item_match_map0 p a (Cbor.Map (maybe_cbor_map v)) (raw_data_item_map_match' p))
    (raw_data_item_match p a v)

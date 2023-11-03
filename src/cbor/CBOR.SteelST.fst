module CBOR.SteelST
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.Spec // for serialize_cbor

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let cbor_serialized_payload_t = LPS.byte_array
let cbor_serialized_footprint_t = LPA.array LPS.byte

let cbor_footprint_t = GR.ref unit
let dummy_cbor_footprint = magic ()

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

assume
val ref_pts_to_perm (#a: _) (#u: _) (#p: _) (#v: _) (r: R.ref a)
  : STGhost unit u
      (R.pts_to r p v)
      (fun _ -> R.pts_to r p v)
      True
      (fun _ -> p `lesser_equal_perm` full_perm)

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
      ref_pts_to_perm _;
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

assume
val gref_share_gen
  (#t: Type)
  (#opened: _)
  (#p: perm)
  (#v: t)
  (r: GR.ref t)
  (p1 p2: perm)
: STGhost unit opened
    (GR.pts_to r p v)
    (fun _ -> GR.pts_to r p1 v `star` GR.pts_to r p2 v)
    (p == p1 `sum_perm` p2)
    (fun _ -> True)

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
    gref_share_gen r low diff;
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

let serialize_cbor_error
  (x: Seq.seq U8.t)
: Lemma
  (requires (LPS.parse CborST.parse_raw_data_item x == None))
  (ensures (read_cbor_error_postcond x))
= let prf
    (v: Cbor.raw_data_item)
    (suff: Seq.seq U8.t)
  : Lemma
    (requires (x == Cbor.serialize_cbor v `Seq.append` suff))
    (ensures False)
  = LPS.parse_strong_prefix CborST.parse_raw_data_item (Cbor.serialize_cbor v) x
  in
  Classical.forall_intro_2 (fun v suff -> Classical.move_requires (prf v) suff)

#push-options "--z3rlimit 64"
#restart-solver

let read_cbor'
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (a: A.array U8.t)
  (sz: SZ.t)
: ST read_cbor_t
    (A.pts_to a p va)
    (fun res -> read_cbor_post a p va res)
    (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    (fun res ->
      match res with
      | ParseError -> True
      | ParseSuccess r -> CBOR_Case_Serialized? r.read_cbor_payload
    )
= A.pts_to_length a _;
  let a' = LPA.intro_arrayptr_with_implies a in
  let _ = gen_elim () in
  let va' = vpattern (LPA.arrayptr a') in
  vpattern_rewrite_with_implies (LPA.arrayptr a') va';
  implies_trans
    (LPA.arrayptr a' va')
    (LPA.arrayptr a' _)
    (A.pts_to a p va);
  let res = R.with_local 0ul #_ #(res: read_cbor_t {
      match res with
      | ParseError -> True
      | ParseSuccess r -> CBOR_Case_Serialized? r.read_cbor_payload
  }) (fun perr ->
    let sz' = CborST.validate_raw_data_item a' sz perr in
    let _ = gen_elim () in
    let err = R.read perr in
    if err = 0ul
    then begin
      noop ();
      LPS.parsed_data_is_serialize CborST.serialize_raw_data_item va;
      let rem' = LPS.peek_strong_with_size_with_implies CborST.parse_raw_data_item a' sz' in
      let _ = gen_elim () in
      implies_trans
        (LPS.aparse CborST.parse_raw_data_item a' _ `star` LPA.arrayptr rem' _)
        (LPA.arrayptr a' _)
        (A.pts_to a p va);
      let vpl = vpattern (LPS.aparse CborST.parse_raw_data_item a') in
      let vrem = vpattern (LPA.arrayptr rem') in
      let rem = LPA.elim_arrayptr_with_implies rem' in
      A.pts_to_length rem _;
      vpattern_rewrite_with_implies (fun p -> A.pts_to rem p _) p;
      implies_trans
        (A.pts_to rem p _)
        (A.pts_to rem _ _)
        (LPA.arrayptr rem' _);
      implies_trans_r1 
        (LPS.aparse CborST.parse_raw_data_item a' _)
        (A.pts_to rem p _)
        (LPA.arrayptr rem' _)
        (A.pts_to a p va);
      let c = read_valid_cbor_from_buffer_with_size_strong full_perm a' sz' in
      implies_trans_l1
        (raw_data_item_match full_perm c _)
        (LPS.aparse CborST.parse_raw_data_item a' _)
        (A.pts_to rem p _)
        (A.pts_to a p va);
      [@@inline_let]
      let res = {
        read_cbor_payload = c;
        read_cbor_remainder = rem;
        read_cbor_remainder_length = sz `SZ.sub` sz';
      }
      in
      vpattern_rewrite_with_implies
        (fun c -> raw_data_item_match full_perm c _)
        res.read_cbor_payload;
      implies_trans_l1
        (raw_data_item_match full_perm res.read_cbor_payload _)
        (raw_data_item_match full_perm c _)
        (A.pts_to rem p _)
        (A.pts_to a p va);
      vpattern_rewrite_with_implies
        (fun rem -> A.pts_to rem p _)
        res.read_cbor_remainder;
      implies_trans_r1
        (raw_data_item_match full_perm res.read_cbor_payload _)
        (A.pts_to res.read_cbor_remainder _ _)
        (A.pts_to rem _ _)
        (A.pts_to a p va);
      rewrite
        (read_cbor_success_post a p va res)
        (read_cbor_post a p va (ParseSuccess res));
      return (ParseSuccess res)
    end else begin
      noop ();
      serialize_cbor_error va;
      noop ();
      elim_implies
        (LPA.arrayptr a' va')
        (A.pts_to a p va);
      rewrite
        (read_cbor_error_post a p va)
        (read_cbor_post a p va ParseError);
      return ParseError
    end
  )
  in
  return res

#pop-options

let read_cbor
  #va #p a sz
= read_cbor' a sz

let serialize_deterministically_encoded_cbor_error
  (x: Seq.seq U8.t)
  (c: read_cbor_success_t)
  (v0: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Lemma
  (requires (
    read_cbor_success_postcond x c v0 rem /\
    Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v0 == false
  ))
  (ensures (read_deterministically_encoded_cbor_error_postcond x))
= Cbor.serialize_cbor_with_test_correct v0 rem (fun c' _ -> Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order c' == true)

let read_deterministically_encoded_cbor
  #va #p a sz
= A.pts_to_length a _;
  let _ = A.intro_fits_u64 () in
  let res = read_cbor' a sz in
  if ParseError? res
  then begin
    rewrite
      (read_cbor_post a p va res)
      (read_cbor_error_post a p va);
    let _ = gen_elim () in
    rewrite
      (read_deterministically_encoded_cbor_error_post a p va)
      (read_deterministically_encoded_cbor_post a p va res);
    return res
  end else begin
    let r = ParseSuccess?._0 res in
    rewrite
      (read_cbor_post a p va res)
      (read_cbor_success_post a p va r);
    let _ = gen_elim () in
    let s = destr_cbor_serialized r.read_cbor_payload in
    let _ = gen_elim () in
    let test = CBOR.SteelST.Raw.Map.check_raw_data_item
      (CBOR.SteelST.Raw.Map.check_data_item_wf_head CBOR.SteelST.Raw.Map.deterministically_encoded_cbor_map_key_order_impl ())
      s.cbor_serialized_payload
    in
    elim_implies
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match full_perm _ _);
    if test
    then begin
      noop ();
      noop (); // FIXME: WHY WHY WHY do I need that many noop()s ?
      rewrite
        (read_deterministically_encoded_cbor_success_post a p va r)
        (read_deterministically_encoded_cbor_post a p va res);
      return res
    end else begin
      let v = vpattern_erased (raw_data_item_match full_perm _) in
      let rem = vpattern_erased (A.pts_to _ _) in
      serialize_deterministically_encoded_cbor_error va r v rem;
      elim_implies
        (raw_data_item_match full_perm _ _ `star` A.pts_to _ _ _)
        (A.pts_to a p va);
      rewrite
        (read_deterministically_encoded_cbor_error_post a p va)
        (read_deterministically_encoded_cbor_post a p va ParseError);
      return ParseError
    end
  end

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

let destr_cbor_int64
  #p #va c
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 c' fp ->
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_int0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_int0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs fp ->
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_serialized0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse CborST.parse_raw_data_item a _) cs.cbor_serialized_payload;
    let typ = CborST.read_major_type cs.cbor_serialized_payload in
    let value = CborST.read_int64 cs.cbor_serialized_payload in
    let c' : cbor_int = {
      cbor_int_type = typ;
      cbor_int_value = value;
    }
    in
    noop ();
    elim_implies
      (raw_data_item_match_serialized0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'

let size_comp_for_int64
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Int64? va })
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let c' = destr_cbor_int64 c in
    let res = CBOR.SteelST.Raw.Write.size_comp_int64 c'.cbor_int_type c'.cbor_int_value sz perr in
    let _ = gen_elim () in
    return res

let l2r_writer_for_int64
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Int64? va })
: Tot (cbor_l2r_writer_for va c)
= fun out ->
    let c' = destr_cbor_int64 c in
    let res = CBOR.SteelST.Raw.Write.l2r_write_int64 c'.cbor_int_type c'.cbor_int_value out in
    let _ = gen_elim () in
    return res

let constr_cbor_int64
  ty value
= let fp = GR.alloc () in
  [@@inline_let]
  let c = CBOR_Case_Int64 ({ cbor_int_type = ty; cbor_int_value = value }) fp in
  noop ();
  rewrite
    (raw_data_item_match_int0 full_perm c (Cbor.Int64 ty value))
    (raw_data_item_match full_perm c (Cbor.Int64 ty value));
  return c

let destr_cbor_simple_value
  #p #va c
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Simple_value c' _ ->
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_simple_value0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_simple_value0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs _ ->
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_serialized0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse CborST.parse_raw_data_item a _) cs.cbor_serialized_payload;
    let c' = CborST.read_simple_value cs.cbor_serialized_payload in
    elim_implies
      (raw_data_item_match_serialized0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'

let size_comp_for_simple_value
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Simple? va })
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let c' = destr_cbor_simple_value c in
    let res = CBOR.SteelST.Raw.Write.size_comp_simple_value c' sz perr in
    let _ = gen_elim () in
    return res

let l2r_writer_for_simple_value
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Simple? va })
: Tot (cbor_l2r_writer_for va c)
= fun out ->
    let c' = destr_cbor_simple_value c in
    let res = CBOR.SteelST.Raw.Write.l2r_write_simple_value c' out in
    let _ = gen_elim () in
    return res

let constr_cbor_simple_value
  value
= let fp = GR.alloc () in
  [@@inline_let]
  let c = CBOR_Case_Simple_value value fp in
  noop ();
  rewrite
    (raw_data_item_match_simple_value0 full_perm c (Cbor.Simple value))
    (raw_data_item_match full_perm c (Cbor.Simple value));
  return c

let destr_cbor_string
  #p #va c
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_String c' fp p' ->
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_string0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    let vc' = vpattern_erased (A.pts_to _ _) in
    let np = p `prod_perm` p' in
    rewrite (A.pts_to _ _ _) (A.pts_to c'.cbor_string_payload np vc');
    intro_implies
      (A.pts_to c'.cbor_string_payload np vc')
      (raw_data_item_match_string0 p c (Ghost.reveal va))
      (GR.pts_to _ _ _)
      (fun _ ->
        noop ();
        noop ()
      );
    implies_trans
      (A.pts_to c'.cbor_string_payload np vc')
      (raw_data_item_match_string0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'
  | _ ->
    let cs = destr_cbor_serialized c in
    let _ = gen_elim () in
    let typ = CborST.read_major_type cs.cbor_serialized_payload in
    let len = CborST.read_argument_as_uint64 cs.cbor_serialized_payload in
    let lpayload = CborST.focus_string cs.cbor_serialized_payload in
    let _ = gen_elim () in
    implies_trans
      (LPA.arrayptr _ _)
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match _ _ _);
    let payload = LPA.elim_arrayptr_with_implies lpayload in
    let _ = gen_elim () in
    implies_trans
      (A.pts_to _ _ _)
      (LPA.arrayptr _ _)
      (raw_data_item_match _ _ _);
    [@@inline_let]
    let c' : cbor_string = {
      cbor_string_type = typ;
      cbor_string_length = len;
      cbor_string_payload = payload;
    }
    in
    vpattern_rewrite_with_implies
      (fun a -> A.pts_to a _ _)
      c'.cbor_string_payload;
    implies_trans
      (A.pts_to _ _ _)
      (A.pts_to _ _ _)
      (raw_data_item_match _ _ _);
    return c'

#push-options "--z3rlimit 64"
#restart-solver

let size_comp_for_string
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.String? va })
: Tot (cbor_size_comp_for va c)
= fun #p sz perr ->
    let _ = A.intro_fits_u64 () in
    let c' = destr_cbor_string c in
    let _ = gen_elim () in
    let res = CBOR.SteelST.Raw.Write.size_comp_string c'.cbor_string_type c'.cbor_string_length (Cbor.String?.v va) sz perr in
    let _ = gen_elim () in
    elim_implies
      (A.pts_to _ _ _)
      (raw_data_item_match p _ _);
    return res

let serialize_cbor_string_eq
  (c: Cbor.raw_data_item { Cbor.String? c })
: Lemma
  (
    let s0 = LPS.serialize CborST.serialize_raw_data_item c in
    let s1 = LPS.serialize CborST.serialize_header (CborST.uint64_as_argument (Cbor.String?.typ c) (U64.uint_to_t (Seq.length (Cbor.String?.v c)))) in
    s0 == s1 `Seq.append` Cbor.String?.v c
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

let l2r_write_cbor_string
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {Cbor.String? va})
: Tot (cbor_l2r_writer_for va c)
= fun #p #vout out ->
  let _ = A.intro_fits_u64 () in
  serialize_cbor_string_eq va;
  noop ();
  let c' = destr_cbor_string c in
  let _ = gen_elim () in
  let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header c'.cbor_string_type c'.cbor_string_length out in
  let _ = gen_elim () in
  let _ = LPS.elim_aparse_with_serializer CborST.serialize_header res in
  let len = SZ.uint64_to_sizet c'.cbor_string_length in
  let res_pl = LW.split out len in
  let _ = gen_elim () in
  let vout' = vpattern_replace (LW.vp out) in
  let vres_pl = vpattern (LPA.arrayptr res_pl) in
  let res_pl_a = LPA.elim_arrayptr res_pl in
  vpattern_rewrite (fun p -> A.pts_to res_pl_a p _) full_perm;
  A.pts_to_length c'.cbor_string_payload _;
  A.pts_to_length res_pl_a _;
  let _ = A.memcpy c'.cbor_string_payload res_pl_a len in
  let res_pl = LPA.intro_arrayptr res_pl_a in
  let _ = gen_elim () in
  let vres_pl' = vpattern (LPA.arrayptr res_pl) in
  LPA.array_equal (LPA.array_of vres_pl) (LPA.array_of vres_pl');
  noop ();
  let _ = LPA.join res res_pl in
  let vres = LPS.intro_aparse_with_serializer CborST.serialize_raw_data_item va res in
  elim_implies
    (A.pts_to _ _ _)
    (raw_data_item_match p c (Ghost.reveal va));
  assert_ (cbor_l2r_writer_for_post p va c vout out res vres vout'); // FIXME: WHY WHY WHY?
  return res

#pop-options

let constr_cbor_string
  #va #p typ a len
= let fp = GR.alloc () in
  [@@inline_let]
  let c' = CBOR_Case_String
    ({
      cbor_string_type = typ;
      cbor_string_payload = a;
      cbor_string_length = len;
    })
    fp
    p
  in
  noop ();
  rewrite_with_implies
    (raw_data_item_match_string0 full_perm c' (Cbor.String typ va))
    (raw_data_item_match full_perm c' (Cbor.String typ va));
  intro_implies
    (raw_data_item_match_string0 full_perm c' (Cbor.String typ va))
    (A.pts_to a p va)
    emp
    (fun _ ->
      let _ = gen_elim () in
      GR.free _;
      rewrite (A.pts_to _ _ _) (A.pts_to a p va)
    );
  implies_trans
    (raw_data_item_match full_perm c' (Cbor.String typ (va)))
    (raw_data_item_match_string0 full_perm c' (Cbor.String typ (va)))
    (A.pts_to a p va);
  return c'

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

let constr_cbor_array
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

let destr_cbor_array
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
    let a' = destr_cbor_array a in
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
  let ar = destr_cbor_array a in
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

[@@inline_let]
let dummy_cbor_array_iterator = {
  cbor_array_iterator_length = 0uL;
  cbor_array_iterator_payload = CBOR_Array_Iterator_Payload_Array A.null Seq.empty;
  footprint = magic ();
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
  let ar = destr_cbor_array a in
  let fp = GR.alloc () in // I could reuse the footprint from `a`, but `destr_cbor_array` does not expose it
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
  let a = CBOR_Array_Iterator_Payload_Array?.payload i.cbor_array_iterator_payload in
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
  let a = CBOR_Array_Iterator_Payload_Serialized?.payload i.cbor_array_iterator_payload in
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

let read_cbor_array
  #p #obj input a0 len
= 
  raw_data_item_match_perm_le_full_perm input;
  A.pts_to_length a0 _;
  raw_data_item_match_get_case input;
  match input with
  | CBOR_Case_Array _ _ ->
    let res = destr_cbor_array input in
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
    let s1 = LPS.serialize CborST.serialize_header (CborST.uint64_as_argument Cbor.major_type_array (U64.uint_to_t (List.Tot.length (Cbor.Array?.v c)))) in
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
    let c' = destr_cbor_array c in
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
    let sz1 = CBOR.SteelST.Raw.Write.size_comp_uint64_header Cbor.major_type_array c'.cbor_array_length sz perr in
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
    let c' = destr_cbor_array c in
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
    let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header Cbor.major_type_array c'.cbor_array_length out in
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

let destr_cbor_tagged0
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_tagged0
    (raw_data_item_match p a v)
    (fun res ->
      R.pts_to res.cbor_tagged0_payload p res.footprint `star`
      raw_data_item_match p res.footprint (maybe_cbor_tagged_payload v) `star`
      ((R.pts_to res.cbor_tagged0_payload p res.footprint `star`
        raw_data_item_match p res.footprint (maybe_cbor_tagged_payload v)) `implies_`
        raw_data_item_match p a v
      )
    )
    (CBOR_Case_Tagged? a)
    (fun res ->
      a == CBOR_Case_Tagged res /\
      Cbor.Tagged? v /\
      res.cbor_tagged0_tag == Cbor.Tagged?.tag v
    )
= raw_data_item_match_get_case _;
  let _ : squash (Cbor.Tagged? v) = () in
  let g_tag = Ghost.hide (Cbor.Tagged?.tag v) in
  let g_payload = Ghost.hide (Cbor.Tagged?.v v) in
  let CBOR_Case_Tagged res = a in
  rewrite_with_implies
    (raw_data_item_match p a v)
    (raw_data_item_match p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload));
  rewrite_with_implies_with_tactic
    (raw_data_item_match p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload))
    (raw_data_item_match_tagged0 p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload) (raw_data_item_match p));
  implies_trans
    (raw_data_item_match_tagged0 p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload) (raw_data_item_match p))
    (raw_data_item_match p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload))
    (raw_data_item_match p a v);
  let _ = gen_elim () in
  let _ : squash (res.cbor_tagged0_tag == Ghost.reveal g_tag) = () in
  let _ : squash (maybe_cbor_tagged_payload v == Ghost.reveal g_payload) = () in
  let _ : squash (Ghost.reveal g_payload << Cbor.Tagged g_tag g_payload) = () in // FIXME: WHY WHY WHY?
  rewrite (R.pts_to _ _ _) (R.pts_to res.cbor_tagged0_payload p res.footprint);
  rewrite (raw_data_item_match p _ _) (raw_data_item_match p res.footprint (maybe_cbor_tagged_payload v));
  intro_implies
    (R.pts_to res.cbor_tagged0_payload p res.footprint `star`
      raw_data_item_match p res.footprint (maybe_cbor_tagged_payload v))
    (raw_data_item_match p a v)
    (raw_data_item_match_tagged0 p _ _ (raw_data_item_match p) `implies_` raw_data_item_match p a _)
    (fun _ ->
      elim_implies
        (raw_data_item_match_tagged0 p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload) (raw_data_item_match p))
        (raw_data_item_match p a _)
    );
  return res

let implies_consumes_l
  (#opened: _)
  (p q r: vprop)
: STGhostT unit opened
    (p `star` ((p `star` q) `implies_` r))
    (fun _ -> q `implies_` r)
= intro_implies
    q
    r
    (p `star` ((p `star` q) `implies_` r))
    (fun _ -> elim_implies (p `star` q) r)

let implies_consumes_r
  (#opened: _)
  (p q r: vprop)
: STGhostT unit opened
    (q `star` ((p `star` q) `implies_` r))
    (fun _ -> p `implies_` r)
= implies_with_tactic (q `star` p) (p `star` q);
  implies_trans (q `star` p) (p `star` q) r;
  implies_consumes_l q p r

#push-options "--z3rlimit 64"
#restart-solver

let destr_cbor_tagged
  #p #v a
=
  raw_data_item_match_get_case a;
  match a with
  | CBOR_Case_Tagged _ ->
    let r = destr_cbor_tagged0 a in
    let pl = R.read r.cbor_tagged0_payload in
    implies_consumes_l
      (R.pts_to _ _ _)
      (raw_data_item_match _ _ _)
      (raw_data_item_match _ _ _);
    let res = {
      cbor_tagged_tag = r.cbor_tagged0_tag;
      cbor_tagged_payload = pl;
    }
    in
    vpattern_rewrite_with_implies
      (fun pl -> raw_data_item_match p pl _)
      res.cbor_tagged_payload;
    implies_trans
      (raw_data_item_match p _ (maybe_cbor_tagged_payload v))
      (raw_data_item_match p _ (maybe_cbor_tagged_payload v))
      (raw_data_item_match p a v);
    return res
  | _ ->
    raw_data_item_match_perm_le_full_perm a;
    let s = destr_cbor_serialized a in
    let _ = gen_elim () in
    let tag = CBOR.SteelST.Raw.read_argument_as_uint64 s.cbor_serialized_payload in
    let s' = CBOR.SteelST.Raw.Read.focus_tagged s.cbor_serialized_payload in
    let _ = gen_elim () in
    implies_trans
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match p _ _);
    let sz = LPS.get_parsed_size CborST.jump_raw_data_item s' in
    let pl = read_valid_cbor_from_buffer_with_size_strong p s' sz in
    implies_trans
      (raw_data_item_match p _ _)
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match p _ _);
    [@@inline_let]
    let res = {
      cbor_tagged_tag = tag;
      cbor_tagged_payload = pl;
    }
    in
    rewrite_with_implies
      (raw_data_item_match p _ _)
      (raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v));
    implies_trans
      (raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v))
      (raw_data_item_match p _ _)
      (raw_data_item_match p a v);
    return res

let constr_cbor_tagged
  #c' #v' tag a
= [@@inline_let]
  let res_tg = {
    cbor_tagged0_tag = tag;
    cbor_tagged0_payload = a;
    footprint = c';
  }
  in
  [@@inline_let]
  let prf () : squash (Ghost.reveal v' << Cbor.Tagged tag v') =
    let w = Cbor.Tagged tag v' in
    match w with
    | Cbor.Tagged _ v_ -> assert (v_ << w)
  in
  [@@inline_let]
  let _ = prf () in
  noop ();
  rewrite_with_implies_with_tactic
    (raw_data_item_match_tagged0 full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v') (raw_data_item_match full_perm))
    (raw_data_item_match full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v'));
  intro_implies
    (raw_data_item_match_tagged0 full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v') (raw_data_item_match full_perm))
    (R.pts_to a full_perm c' `star`
      raw_data_item_match full_perm c' v')
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite
        (R.pts_to _ _ _)
        (R.pts_to a full_perm c');
      rewrite
        (raw_data_item_match full_perm _ _)
        (raw_data_item_match full_perm c' v')
    );
  implies_trans
    (raw_data_item_match full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v'))
    (raw_data_item_match_tagged0 full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v') (raw_data_item_match full_perm))
    (R.pts_to a full_perm c' `star`
      raw_data_item_match full_perm c' v');
  [@@inline_let]
  let res = CBOR_Case_Tagged res_tg in
  rewrite_with_implies
    (raw_data_item_match full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v'))
    (raw_data_item_match full_perm res (Cbor.Tagged tag v'));
  implies_trans
    (raw_data_item_match full_perm res (Cbor.Tagged tag v'))
    (raw_data_item_match full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v'))
    (R.pts_to a full_perm c' `star`
      raw_data_item_match full_perm c' v');
  return res

let serialize_cbor_tagged_eq
  (c: Cbor.raw_data_item { Cbor.Tagged? c })
: Lemma
  (
    let s0 = LPS.serialize CborST.serialize_raw_data_item c in
    let s1 = LPS.serialize CborST.serialize_header (CborST.uint64_as_argument Cbor.major_type_tagged (Cbor.Tagged?.tag c)) in
    let s2 = LPS.serialize CborST.serialize_raw_data_item (Cbor.Tagged?.v c) in
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
let size_comp_for_tagged
  (size:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_size_comp_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Tagged? c})
: Tot (cbor_size_comp_for va c)
= fun #p sz perr ->
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Tagged? va) = () in
    serialize_cbor_tagged_eq va;
    let c' = destr_cbor_tagged c in
    let sz1 = CBOR.SteelST.Raw.Write.size_comp_uint64_header Cbor.major_type_tagged c'.cbor_tagged_tag sz perr in
    let _ = gen_elim () in
    let err1 = R.read perr in
    if err1
    then begin
      noop ();
      elim_implies
        (raw_data_item_match p _ _)
        (raw_data_item_match p _ _);
      return sz1
    end else begin
      noop ();
      let sz2 = size _ c'.cbor_tagged_payload sz1 perr in
      let _ = gen_elim () in
      elim_implies
        (raw_data_item_match p _ _)
        (raw_data_item_match p _ _);
      return sz2
    end

inline_for_extraction
noextract
let l2r_writer_for_tagged
  (write:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_l2r_writer_for va c
  )
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Tagged? c})
: Tot (cbor_l2r_writer_for va c)
= fun #p #vout out ->
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Tagged? va) = () in
    serialize_cbor_tagged_eq va;
    let c' = destr_cbor_tagged c in
    let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header Cbor.major_type_tagged c'.cbor_tagged_tag out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer CborST.serialize_header res in
    let res_pl = write _ c'.cbor_tagged_payload out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer CborST.serialize_raw_data_item res_pl in
    let _ = LPA.join res res_pl in
    let vres = LPS.intro_aparse_with_serializer CborST.serialize_raw_data_item va res in
    let vout' = vpattern_replace (LW.vp out) in
    elim_implies
      (raw_data_item_match p _ _)
      (raw_data_item_match p _ _);
    assert_ (cbor_l2r_writer_for_post p va c vout out res vres vout'); // FIXME: WHY WHY WHY?
    return res

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
= raw_data_item_match_get_case _;
  let sq : squash (Cbor.Map? v) = () in
  let CBOR_Case_Map res fp = a in
  rewrite_with_implies
    (raw_data_item_match p _ _)
    (raw_data_item_match p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)));
  rewrite_with_implies_with_tactic
    (raw_data_item_match p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)))
    (raw_data_item_match_map0 p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)) (raw_data_item_map_match' p));
  implies_trans
    (raw_data_item_match_map0 p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)) (raw_data_item_map_match' p))
    (raw_data_item_match p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)))
    (raw_data_item_match p _ _);
  let _ = gen_elim () in
  rewrite
    (A.pts_to _ _ _)
    (A.pts_to res.cbor_map_payload p res.footprint);
  rewrite
    (raw_data_item_map_match' p _ _)
    (raw_data_item_map_match' p res.footprint (maybe_cbor_map v));
  rewrite_with_tactic
    (raw_data_item_map_match' p res.footprint (maybe_cbor_map v))
    (LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match' (maybe_cbor_map v) (raw_data_item_match p)));
  LPS.seq_list_match_weaken res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match' (maybe_cbor_map v) (raw_data_item_match p)) (raw_data_item_map_entry_match p)
    (fun x y ->
      rewrite
        (raw_data_item_map_entry_match' (maybe_cbor_map v) (raw_data_item_match p) x y)
        (raw_data_item_map_entry_match p x y)
    );
  intro_implies
    (A.pts_to res.cbor_map_payload p res.footprint `star`
      LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match p))
    (raw_data_item_match p a v)
    (GR.pts_to _ p () `star`
      (raw_data_item_match_map0 p (CBOR_Case_Map res fp) (Cbor.Map (maybe_cbor_map v)) (raw_data_item_map_match' p) `implies_`
        raw_data_item_match p a v)
    )
    (fun _ ->
      LPS.seq_list_match_weaken res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match p) (raw_data_item_map_entry_match' (maybe_cbor_map v) (raw_data_item_match p))
        (fun x y ->
          rewrite
            (raw_data_item_map_entry_match p x y)
            (raw_data_item_map_entry_match' (maybe_cbor_map v) (raw_data_item_match p) x y)
        );
      rewrite_with_tactic
        (LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match' (maybe_cbor_map v) (raw_data_item_match p)))
        (raw_data_item_map_match' p res.footprint (maybe_cbor_map v));
      rewrite
        (raw_data_item_map_match' p res.footprint (maybe_cbor_map v)) 
        (raw_data_item_map_match' p res.footprint (Cbor.Map?.v (Cbor.Map (maybe_cbor_map v))));
      elim_implies
        (raw_data_item_match_map0 p _ _ (raw_data_item_map_match' p))
        (raw_data_item_match p a v)
    );
  return res

#pop-options

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
  let sz1 = size _ c.cbor_map_entry_key sz perr in
  let _ = gen_elim () in
  let err = R.read perr in
  if err
  then begin
    noop ();
    noop ();
    return sz1
  end else begin
    noop ();
    let sz2 = size _ c.cbor_map_entry_value sz1 perr in
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
  let res = write _ c.cbor_map_entry_key out in
  let _ = gen_elim () in
  let _ = LPS.elim_aparse_with_serializer CborST.serialize_raw_data_item res in
  let res_pl = write _ c.cbor_map_entry_value out in
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

let cbor_get_major_type
  #p #v a
= raw_data_item_match_get_case a;
  match a with
  | CBOR_Case_Map _ _ ->
    noop ();
    return Cbor.major_type_map
  | CBOR_Case_Array _ _ ->
    noop ();
    return Cbor.major_type_array
  | CBOR_Case_Tagged _ ->
    noop ();
    return Cbor.major_type_tagged
  | CBOR_Case_Simple_value _ _ ->
    noop ();
    return Cbor.major_type_simple_value
  | CBOR_Case_String _ _ _ ->
    let s = destr_cbor_string a in
    let _ = gen_elim () in
    elim_implies (A.pts_to _ _ _) (raw_data_item_match p _ _);
    return s.cbor_string_type
  | CBOR_Case_Int64 _ _ ->
    let i = destr_cbor_int64 a in
    return i.cbor_int_type
  | _ ->
    let s = destr_cbor_serialized a in
    let _ = gen_elim () in
    let res = CborST.read_major_type s.cbor_serialized_payload in
    elim_implies (LPS.aparse CborST.parse_raw_data_item _ _) (raw_data_item_match p _ _);
    return res

let cbor_is_equal
  #p1 #v1 a1 #p2 #v2 a2
=
  let _ = A.intro_fits_u64 () in
  let type1 = cbor_get_major_type a1 in
  let type2 = cbor_get_major_type a2 in
  if type1 <> type2
  then begin
    noop ();
    return false
  end
  else begin
    if type1 = Cbor.major_type_uint64 || type1 = Cbor.major_type_neg_int64
    then begin
      let i1 = destr_cbor_int64 a1 in
      let i2 = destr_cbor_int64 a2 in
      return (i1.cbor_int_value = i2.cbor_int_value)
    end
    else if type1 = Cbor.major_type_simple_value
    then begin
      let i1 = destr_cbor_simple_value a1 in
      let i2 = destr_cbor_simple_value a2 in
      return (i1 = i2)
    end
    else if type1 = Cbor.major_type_byte_string || type1 = Cbor.major_type_text_string
    then begin
      let s1 = destr_cbor_string a1 in
      let _ = gen_elim () in
      let s2 = destr_cbor_string a2 in
      let _ = gen_elim () in
      let t1 = LPA.intro_arrayptr_with_implies s1.cbor_string_payload in
      let _ = gen_elim () in
      let t2 = LPA.intro_arrayptr_with_implies s2.cbor_string_payload in
      let _ = gen_elim () in
      let res = LowParse.SteelST.Assoc.eq_byte_arrays t1 (SZ.uint64_to_sizet s1.cbor_string_length) t2 (SZ.uint64_to_sizet s2.cbor_string_length) in
      elim_implies (LPA.arrayptr t1 _) (A.pts_to _ _ _);
      elim_implies (LPA.arrayptr t2 _) (A.pts_to _ _ _);
      elim_implies (A.pts_to s1.cbor_string_payload _ _) (raw_data_item_match p1 _ _);
      elim_implies (A.pts_to s2.cbor_string_payload _ _) (raw_data_item_match p2 _ _);
      return res
    end
    else begin
      // TODO: tagged, arrays and maps
      noop ();
      return false
    end
  end

assume val cbor_map_get_case_map
  (#pkey: perm)
  (#vkey: Ghost.erased Cbor.raw_data_item)
  (key: cbor)
  (#pmap: perm)
  (#vmap: Ghost.erased Cbor.raw_data_item)
  (map: cbor { Cbor.Map? vmap })
: ST cbor_map_get_t
    (raw_data_item_match pkey key vkey `star` raw_data_item_match pmap map vmap)
    (fun res -> raw_data_item_match pkey key vkey `star` cbor_map_get_post pmap vkey vmap map res)
    (~ (Cbor.Tagged? vkey \/ Cbor.Array? vkey \/ Cbor.Map? vkey) /\
      CBOR_Case_Map? map
    )
    (fun res -> Found? res == Some? (Cbor.list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap)))

let mk_cbor_nlist_assoc_eq_keys
  (pkey: perm)
  (vkey: Ghost.erased Cbor.raw_data_item)
  (key: cbor {
    ~ (Cbor.Tagged? vkey \/ Cbor.Array? vkey \/ Cbor.Map? vkey)
  })
: Tot (LowParse.SteelST.Assoc.nlist_assoc_eq_keys CborST.parse_raw_data_item (Ghost.reveal vkey) (raw_data_item_match pkey key vkey))
= fun #va a sz ->
    let x = read_valid_cbor_from_buffer_with_size_strong full_perm a sz in
    let res = cbor_is_equal key x in
    elim_implies
      (raw_data_item_match full_perm x _)
      (LPS.aparse CborST.parse_raw_data_item _ _);
    return res

let cbor_map_get_case_serialized
  (#pkey: perm)
  (#vkey: Ghost.erased Cbor.raw_data_item)
  (key: cbor)
  (#pmap: perm)
  (#vmap: Ghost.erased Cbor.raw_data_item)
  (map: cbor { Cbor.Map? vmap })
: ST cbor_map_get_t
    (raw_data_item_match pkey key vkey `star` raw_data_item_match pmap map vmap)
    (fun res ->
      raw_data_item_match pkey key vkey `star` cbor_map_get_post pmap vkey vmap map res `star` 
      pure (Found? res == Some? (Cbor.list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap)))
    )
    (~ (Cbor.Tagged? vkey \/ Cbor.Array? vkey \/ Cbor.Map? vkey) /\
      CBOR_Case_Serialized? map
    )
    (fun _ -> True)
= raw_data_item_match_perm_le_full_perm map;
  let _ = A.intro_fits_u64 () in
  let s = destr_cbor_serialized map in
  let _ = gen_elim () in
  let len64 = CborST.read_argument_as_uint64 s.cbor_serialized_payload in
  let len = SZ.uint64_to_sizet len64 in
  let m = CBOR.SteelST.Raw.Map.focus_map_with_ghost_length s.cbor_serialized_payload (SZ.v len) in
  let _ = gen_elim () in
  implies_trans
    (LPS.aparse (LPS.parse_nlist (SZ.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _ _)
    (LPS.aparse CborST.parse_raw_data_item _ _)
    (raw_data_item_match pmap map vmap);
  let vm = vpattern (LPS.aparse (LPS.parse_nlist (SZ.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _) in
  vpattern_rewrite_with_implies
    (LPS.aparse (LPS.parse_nlist (SZ.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _)
    vm;
  implies_trans
    (LPS.aparse (LPS.parse_nlist (SZ.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _ _)
    (LPS.aparse (LPS.parse_nlist (SZ.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _ _)
    (raw_data_item_match pmap map vmap);
  R.with_local m (fun pa ->
    noop ();
    let found = LowParse.SteelST.Assoc.nlist_assoc
      CborST.jump_raw_data_item
      CborST.jump_raw_data_item
      #vkey
      #(raw_data_item_match pkey key vkey)
      (mk_cbor_nlist_assoc_eq_keys pkey vkey key)
      len
      m
      pa
    in
    if found
    then begin
      noop ();
      rewrite
        (LowParse.SteelST.Assoc.nlist_assoc_post CborST.parse_raw_data_item CborST.parse_raw_data_item vkey (raw_data_item_match pkey key vkey) (SZ.v len) vm m pa found)
        (LowParse.SteelST.Assoc.nlist_assoc_post_success CborST.parse_raw_data_item CborST.parse_raw_data_item vkey (raw_data_item_match pkey key vkey) (SZ.v len) vm m pa);
      let _ = gen_elim () in
      implies_trans
        (LPS.aparse CborST.parse_raw_data_item _ _)
        (LPS.aparse (LPS.parse_nlist (SZ.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _ _)
        (raw_data_item_match pmap map vmap);
      let a = R.read pa in
      vpattern_rewrite_with_implies
        (fun a -> LPS.aparse CborST.parse_raw_data_item a _)
        a;
      implies_trans
        (LPS.aparse CborST.parse_raw_data_item _ _)
        (LPS.aparse CborST.parse_raw_data_item _ _)
        (raw_data_item_match pmap map vmap);
      let sz = LPS.get_parsed_size CborST.jump_raw_data_item a in
      let res_succ = read_valid_cbor_from_buffer_with_size_strong pmap a sz in
      implies_trans
        (raw_data_item_match pmap res_succ _)
        (LPS.aparse CborST.parse_raw_data_item _ _)
        (raw_data_item_match pmap map vmap);
      rewrite
        (cbor_map_get_post_found pmap vkey vmap map res_succ)
        (cbor_map_get_post pmap vkey vmap map (Found res_succ));
      return (Found res_succ)
    end else begin
      noop ();
      rewrite
        (LowParse.SteelST.Assoc.nlist_assoc_post CborST.parse_raw_data_item CborST.parse_raw_data_item vkey (raw_data_item_match pkey key vkey) (SZ.v len) vm m pa found)
        (LowParse.SteelST.Assoc.nlist_assoc_post_failure CborST.parse_raw_data_item CborST.parse_raw_data_item vkey (raw_data_item_match pkey key vkey) (SZ.v len) vm m pa);
      let _ = gen_elim () in
      elim_implies
        (LPS.aparse (LPS.parse_nlist (SZ.v len) (LPS.nondep_then CborST.parse_raw_data_item CborST.parse_raw_data_item)) _ _)
        (raw_data_item_match pmap map vmap);
      rewrite
        (cbor_map_get_post_not_found pmap vkey vmap map)
        (cbor_map_get_post pmap vkey vmap map NotFound);
      return NotFound
    end
  )

let cbor_map_get
  key map
= raw_data_item_match_get_case map;
  match map with
  | CBOR_Case_Map _ _ ->
    let res = cbor_map_get_case_map key map in
    return res
  | _ ->
    let res = cbor_map_get_case_serialized key map in
    let _ = gen_elim () in
    return res

let rec cbor_size_comp
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (#p: perm)
  (sz: SZ.t)
  (perr: R.ref bool)
: STT SZ.t // FIXME: WHY WHY WHY do I need to expand the type annotation to avoid the termination check?
    (raw_data_item_match p c (Ghost.reveal va) `star`
      R.pts_to perr full_perm false
    )
    (fun res ->
      raw_data_item_match p c (Ghost.reveal va) `star`
      exists_ (fun err ->
        R.pts_to perr full_perm err `star`
        pure (LowParse.SteelST.Write.size_comp_for_post CborST.serialize_raw_data_item va sz res err)
    ))
=
  raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 _ _ -> size_comp_for_int64 va c sz perr
  | CBOR_Case_Simple_value _ _ -> size_comp_for_simple_value va c sz perr
  | CBOR_Case_String _ _ _ -> size_comp_for_string va c sz perr
  | CBOR_Case_Tagged _ -> size_comp_for_tagged cbor_size_comp va c sz perr
  | CBOR_Case_Array _ _ -> size_comp_for_array cbor_size_comp va c sz perr
  | CBOR_Case_Map _ _ -> size_comp_for_map cbor_size_comp va c sz perr
  | _ -> size_comp_for_serialized c sz perr

let rec cbor_l2r_write
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (#p: perm)
  (#vout: LPA.array LPS.byte)
  (out: LW.t)
: ST LPS.byte_array // FIXME: WHY WHY WHY do I need to expand the type annotation to avoid the termination check?
    (raw_data_item_match p c (Ghost.reveal va) `star`
      LW.vp out vout
    )
    (fun res -> exists_ (fun (vres: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item) -> exists_ (fun (vout': LPA.array LPS.byte) ->
      cbor_l2r_writer_for_post p va c vout out res vres vout'
    )))
    (Seq.length (LPS.serialize CborST.serialize_raw_data_item va) <= LPA.length vout)
    (fun _ -> True)
=
  raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 _ _ -> l2r_writer_for_int64 va c out
  | CBOR_Case_Simple_value _ _ -> l2r_writer_for_simple_value va c out
  | CBOR_Case_String _ _ _ -> l2r_write_cbor_string va c out
  | CBOR_Case_Tagged _ -> l2r_writer_for_tagged cbor_l2r_write c out
  | CBOR_Case_Array _ _ -> l2r_writer_for_array cbor_l2r_write va c out
  | CBOR_Case_Map _ _ -> l2r_writer_for_map cbor_l2r_write va c out
  | _ -> l2r_writer_for_serialized c out

let write_cbor
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (#vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (sz: SZ.t)
: ST SZ.t
    (raw_data_item_match p c (Ghost.reveal va) `star`
      A.pts_to out full_perm vout
    )
    (fun res -> 
      raw_data_item_match p c (Ghost.reveal va) `star`
      exists_ (write_cbor_post va c vout out res)
    )
    (SZ.v sz == A.length out)
    (fun _ -> True)
= A.pts_to_length out _;
  R.with_local false (fun perr ->
    let sz' = cbor_size_comp va c sz perr in
    let _ = gen_elim () in
    let err = R.read perr in
    if err
    then begin
      noop ();
      noop ();
      return 0sz
    end else begin
      noop ();
      let a = LPA.intro_arrayptr out in
      let _ = gen_elim () in
      let va' = vpattern_replace (LPA.arrayptr a) in
      R.with_local sz (fun psz ->
      R.with_local a (fun pa ->
        let res = sz `SZ.sub` sz' in
        let w = LW.intro_vp #_ #_ #a pa psz in
        let lhs = cbor_l2r_write va c w in
        let _ = gen_elim () in
        let rhs = LW.elim_vp w in
        let _ = gen_elim () in
        let _ = LPS.elim_aparse_with_serializer CborST.serialize_raw_data_item lhs in
        let _ = LPA.join lhs rhs in
        let _ = LPA.elim_arrayptr lhs in
        let vout' = vpattern_replace_erased (A.pts_to _ _) in
        rewrite (A.pts_to _ _ _) (A.pts_to out full_perm vout');
        return res
      ))
    end
  )

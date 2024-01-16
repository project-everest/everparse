module CBOR.SteelST.Perm
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Match
open CBOR.SteelST.Type.Def

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

(* Share and gather *)

let rec seq_list_match_gather
  (#opened: _)
  (#t #t': Type)
  (p1 p2 p: t -> t' -> vprop)
  (s: Seq.seq t)
  (l1 l2: list t')
  (prf: (
    (#opened: _) ->
    (x: t) ->
    (x1': t' { x1' << l1 }) ->
    (x2': t') ->
    STGhost unit opened
      (p1 x x1' `star` p2 x x2')
      (fun _ -> p x x1')
      True
      (fun _ -> x1' == x2')
  ))
: STGhost unit opened
    (SM.seq_list_match s l1 p1 `star` SM.seq_list_match s l2 p2)
    (fun _ -> SM.seq_list_match s l1 p)
    True
    (fun _ -> l1 == l2)
    (decreases l1)
= SM.seq_list_match_length p1 s l1;
  SM.seq_list_match_length p2 s l2;
  if Nil? l1
  then begin
    rewrite
      (SM.seq_list_match s l1 p1)
      (SM.seq_list_match_nil0 s);
    rewrite
      (SM.seq_list_match s l2 p2)
      (SM.seq_list_match_nil0 s);
    let _ = gen_elim () in
    rewrite
      (SM.seq_list_match_nil0 s)
      (SM.seq_list_match s l1 p)
  end else begin
    let a1 :: q1 = l1 in
    let a2 :: q2 = l2 in
    SM.seq_list_match_cons_eq s l1 p1;
    SM.seq_list_match_cons_eq s l2 p2;
    SM.seq_list_match_cons_eq s l1 p;
    noop ();
    rewrite
      (SM.seq_list_match s l1 p1)
      (SM.seq_list_match_cons0 s l1 p1 SM.seq_list_match);
    let _ = gen_elim () in
    let x1 = vpattern_replace (fun x -> p1 x _) in
    let s1' = vpattern_replace (fun s -> SM.seq_list_match s (List.Tot.tl l1) p1) in
    rewrite
      (SM.seq_list_match s l2 p2)
      (SM.seq_list_match_cons0 s l2 p2 SM.seq_list_match);
    let _ = gen_elim () in
    let x2 = vpattern_replace (fun x -> p2 x _) in
    let s2' = vpattern_replace (fun s -> SM.seq_list_match s (List.Tot.tl l2) p2) in
    Seq.lemma_cons_inj x1 x2 s1' s2';
    noop ();
    vpattern_rewrite (fun x -> p2 x _) x1;
    vpattern_rewrite (fun s -> SM.seq_list_match s (List.Tot.tl l2) p2) s1';
    prf x1 _ _;
    seq_list_match_gather p1 p2 p s1' (List.Tot.tl l1) (List.Tot.tl l2) prf;
    rewrite
      (SM.seq_list_match_cons0 s l1 p SM.seq_list_match)
      (SM.seq_list_match s l1 p)
  end

#push-options "--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"

#restart-solver
let perm_prod_sum_distr_l
  (p1 p2 p: perm)
: Lemma
  ((p1 `prod_perm` p) `sum_perm` (p2 `prod_perm` p) == (p1 `sum_perm` p2) `prod_perm` p)
  [SMTPat ((p1 `sum_perm` p2) `prod_perm` p)]
= let prod = (let open FStar.Real in ( *. )) in
  let sum = (let open FStar.Real in ( +. )) in
  let lhs = (p1 `prod_perm` p) `sum_perm` (p2 `prod_perm` p) in
  let lhs_v = (p1.v `prod` p.v) `sum` (p2.v `prod` p.v) in
  assert_norm (lhs.v == lhs_v);
  let rhs = (p1 `sum_perm` p2) `prod_perm` p in
  let rhs_v = (p1.v `sum` p2.v) `prod` p.v in
  assert_norm (rhs.v == rhs_v);
  assert (lhs_v == rhs_v)

#pop-options

let rec cbor_gather
  (#opened: _)
  (c: cbor)
  (v1 v2: Cbor.raw_data_item)
  (p1 p2: perm)
: STGhost unit opened
    (raw_data_item_match p1 c v1 `star` raw_data_item_match p2 c v2)
    (fun _ -> raw_data_item_match (p1 `sum_perm` p2) c v1)
    True
    (fun _ -> v1 == v2)
    (decreases v1)
= raw_data_item_match_get_case #_ #p1 #v1 c;
  raw_data_item_match_get_case #_ #p2 #v2 c;
  match c with
  
  | CBOR_Case_Serialized s fp ->
    rewrite
      (raw_data_item_match p1 c v1)
      (raw_data_item_match_serialized0 p1 c v1);
    let _ = gen_elim () in
    vpattern_rewrite (fun r -> GR.pts_to r p1 ()) fp;
    let w1 = vpattern_replace (LPS.aparse CborST.parse_raw_data_item _) in
    vpattern_rewrite (fun a -> LPS.aparse CborST.parse_raw_data_item a _) s.cbor_serialized_payload;
    rewrite
      (raw_data_item_match p2 c v2)
      (raw_data_item_match_serialized0 p2 c v2);
    let _ = gen_elim () in
    vpattern_rewrite (fun r -> GR.pts_to r p2 ()) fp;
    let w2 = vpattern_replace (fun w -> LPS.aparse CborST.parse_raw_data_item s.cbor_serialized_payload w1 `star` LPS.aparse CborST.parse_raw_data_item _ w) in
    vpattern_rewrite (fun a -> LPS.aparse CborST.parse_raw_data_item a w2) s.cbor_serialized_payload;
    GR.gather #_ #_ #p1 #p2 fp;
    let _ = LPS.gather_aparse CborST.parse_raw_data_item #w1 #w2 s.cbor_serialized_payload in
    rewrite
      (raw_data_item_match_serialized0 (p1 `sum_perm` p2) c v1)
      (raw_data_item_match (p1 `sum_perm` p2) c v1)

  | CBOR_Case_Simple_value v fp ->
    rewrite
      (raw_data_item_match p1 c v1)
      (raw_data_item_match_simple_value0 p1 c v1);
    let _ = gen_elim () in
    vpattern_rewrite (fun r -> GR.pts_to r p1 ()) fp;
    rewrite
      (raw_data_item_match p2 c v2)
      (raw_data_item_match_simple_value0 p2 c v2);
    let _ = gen_elim () in
    vpattern_rewrite (fun r -> GR.pts_to r p2 ()) fp;
    GR.gather #_ #_ #p1 #p2 fp;
    rewrite
      (raw_data_item_match_simple_value0 (p1 `sum_perm` p2) c v1)
      (raw_data_item_match (p1 `sum_perm` p2) c v1)

  | CBOR_Case_Int64 v fp ->
    rewrite
      (raw_data_item_match p1 c v1)
      (raw_data_item_match_int0 p1 c v1);
    let _ = gen_elim () in
    vpattern_rewrite (fun r -> GR.pts_to r p1 ()) fp;
    rewrite
      (raw_data_item_match p2 c v2)
      (raw_data_item_match_int0 p2 c v2);
    let _ = gen_elim () in
    vpattern_rewrite (fun r -> GR.pts_to r p2 ()) fp;
    GR.gather #_ #_ #p1 #p2 fp;
    rewrite
      (raw_data_item_match_int0 (p1 `sum_perm` p2) c v1)
      (raw_data_item_match (p1 `sum_perm` p2) c v1)

  | CBOR_Case_String v fp p ->
    rewrite
      (raw_data_item_match p1 c v1)
      (raw_data_item_match_string0 p1 c v1);
    let _ = gen_elim () in
    vpattern_rewrite (fun r -> GR.pts_to r p1 ()) fp;
    vpattern_rewrite (fun a -> A.pts_to a _ _) v.cbor_string_payload;
    let q1 = vpattern_replace (fun p -> A.pts_to _ p _) in
    rewrite
      (raw_data_item_match p2 c v2)
      (raw_data_item_match_string0 p2 c v2);
    let _ = gen_elim () in
    vpattern_rewrite (fun r -> GR.pts_to r p2 ()) fp;
    vpattern_rewrite (fun a -> A.pts_to v.cbor_string_payload _ _ `star` A.pts_to a _ _) v.cbor_string_payload;
    let q2 = vpattern_replace (fun p -> A.pts_to _ q1 _ `star` A.pts_to _ p _) in
    GR.gather #_ #_ #p1 #p2 fp;
    A.gather v.cbor_string_payload q1 q2;
    rewrite
      (raw_data_item_match_string0 (p1 `sum_perm` p2) c v1)
      (raw_data_item_match (p1 `sum_perm` p2) c v1)

  | CBOR_Case_Tagged v ->
    let Cbor.Tagged tg1 v1' = v1 in
    let Cbor.Tagged tg2 v2' = v2 in
    assert_norm (
      raw_data_item_match p1 (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') ==
      raw_data_item_match_tagged0 p1 (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') (raw_data_item_match p1)
    );
    assert_norm (
      raw_data_item_match p2 (CBOR_Case_Tagged v) (Cbor.Tagged tg2 v2') ==
      raw_data_item_match_tagged0 p2 (CBOR_Case_Tagged v) (Cbor.Tagged tg2 v2') (raw_data_item_match p2)
    );
    assert_norm (
      raw_data_item_match (p1 `sum_perm` p2) (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') ==
      raw_data_item_match_tagged0 (p1 `sum_perm` p2) (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') (raw_data_item_match (p1 `sum_perm` p2))
    );
    rewrite
      (raw_data_item_match p1 c v1)
      (raw_data_item_match_tagged0 p1 c v1 (raw_data_item_match p1));
    let _ = gen_elim () in
    rewrite (R.pts_to _ _ _) (R.pts_to v.cbor_tagged0_payload p1 v.footprint);
    vpattern_rewrite (fun c -> raw_data_item_match p1 c _) v.footprint;
    rewrite
      (raw_data_item_match p2 c v2)
      (raw_data_item_match_tagged0 p2 c v2 (raw_data_item_match p2));
    let _ = gen_elim () in
    vpattern_rewrite (fun p -> R.pts_to v.cbor_tagged0_payload _ _ `star` R.pts_to _ p _) p2;
    vpattern_rewrite (fun r -> R.pts_to v.cbor_tagged0_payload _ _ `star` R.pts_to r _ _) v.cbor_tagged0_payload;
    vpattern_rewrite (fun c -> raw_data_item_match p2 c _) v.footprint;
    R.gather #_ #_ #p1 p2 v.cbor_tagged0_payload;
    cbor_gather v.footprint _ _ p1 p2;
    rewrite
      (raw_data_item_match_tagged0 (p1 `sum_perm` p2) c v1 (raw_data_item_match (p1 `sum_perm` p2)))
      (raw_data_item_match (p1 `sum_perm` p2) c v1)

  | CBOR_Case_Array v fp ->
    let Cbor.Array v1' = v1 in
    let Cbor.Array v2' = v2 in
    assert_norm
      (raw_data_item_match p1 (CBOR_Case_Array v fp) (Cbor.Array v1') ==
        raw_data_item_match_array0 p1 (CBOR_Case_Array v fp) (Cbor.Array v1') (raw_data_item_array_match p1)
      );
    assert_norm
      (raw_data_item_match (p1 `sum_perm` p2) (CBOR_Case_Array v fp) (Cbor.Array v1') ==
        raw_data_item_match_array0 (p1 `sum_perm` p2) (CBOR_Case_Array v fp) (Cbor.Array v1') (raw_data_item_array_match (p1 `sum_perm` p2))
      );
    noop ();
    rewrite
      (raw_data_item_match p1 c v1)
      (raw_data_item_match_array0 p1 c v1 (raw_data_item_array_match p1));
    let _ = gen_elim () in
    rewrite (GR.pts_to _ _ _) (GR.pts_to fp p1 ());
    rewrite (A.pts_to _ _ _) (A.pts_to v.cbor_array_payload p1 v.footprint);
    rewrite (raw_data_item_array_match _ _ _) (SM.seq_list_match v.footprint (Cbor.Array?.v v1) (raw_data_item_match p1));
    assert_norm
      (raw_data_item_match p2 (CBOR_Case_Array v fp) (Cbor.Array v2') ==
        raw_data_item_match_array0 p2 (CBOR_Case_Array v fp) (Cbor.Array v2') (raw_data_item_array_match p2)
      );
    noop ();
    rewrite
      (raw_data_item_match p2 c v2)
      (raw_data_item_match_array0 p2 c v2 (raw_data_item_array_match p2));
    let _ = gen_elim () in
    vpattern_rewrite (fun r -> GR.pts_to fp _ _ `star` GR.pts_to r _ _) fp;
    rewrite (A.pts_to _ p2 _) (A.pts_to v.cbor_array_payload p2 v.footprint);
    rewrite (raw_data_item_array_match _ _ _) (SM.seq_list_match v.footprint (Cbor.Array?.v v2) (raw_data_item_match p2));
    GR.gather #_ #_ #p1 #p2 fp;
    A.gather v.cbor_array_payload p1 p2;
    seq_list_match_gather
      (raw_data_item_match p1)
      (raw_data_item_match p2)
      (raw_data_item_match (p1 `sum_perm` p2))
      v.footprint
      (Cbor.Array?.v v1)
      (Cbor.Array?.v v2)
      (fun x x1' x2' ->
        cbor_gather x x1' x2' p1 p2
      );
    rewrite
      (SM.seq_list_match v.footprint (Cbor.Array?.v v1) (raw_data_item_match (p1 `sum_perm` p2)))
      (raw_data_item_array_match (p1 `sum_perm` p2) v.footprint (Cbor.Array?.v v1));
    rewrite
      (raw_data_item_match_array0 (p1 `sum_perm` p2) c v1 (raw_data_item_array_match (p1 `sum_perm` p2)))
      (raw_data_item_match (p1 `sum_perm` p2) c v1)

  | CBOR_Case_Map _ _ ->
    let _ : squash (Cbor.Map? v1) = () in
    let _ : squash (Cbor.Map? v2) = () in
    destr_cbor_map' #_ #p1 c;
    destr_cbor_map' #_ #p2 c;
    GR.gather #_ #_ #p1 #p2 (CBOR_Case_Map?.self_footprint c);
    A.gather (CBOR_Case_Map?.v c).cbor_map_payload p1 p2;
    seq_list_match_gather
      (raw_data_item_map_entry_match p1)
      (raw_data_item_map_entry_match p2)
      (raw_data_item_map_entry_match (p1 `sum_perm` p2))
      (CBOR_Case_Map?.v c).footprint
      (maybe_cbor_map v1)
      (maybe_cbor_map v2)
      (fun x x1' x2' ->
        cbor_gather (cbor_map_entry_key x) (fstp x1') (fstp x2') p1 p2;
        cbor_gather (cbor_map_entry_value x) (sndp x1') (sndp x2') p1 p2
      );
    constr_cbor_map'
      (p1 `sum_perm` p2)
      c
      v1
      (CBOR_Case_Map?.v c).cbor_map_payload
      (CBOR_Case_Map?.v c).footprint
      (maybe_cbor_map v1)
      (CBOR_Case_Map?.self_footprint c)

let rec seq_list_match_share
  (#opened: _)
  (#t #t': Type)
  (p p1 p2: t -> t' -> vprop)
  (s: Seq.seq t)
  (l: list t')
  (prf: (
    (#opened: _) ->
    (x: t) ->
    (x': t' { x' << l }) ->
    STGhostT unit opened
      (p x x')
      (fun _ -> p1 x x' `star` p2 x x')
  ))
: STGhostT unit opened
    (SM.seq_list_match s l p)
    (fun _ -> SM.seq_list_match s l p1 `star` SM.seq_list_match s l p2)
    (decreases l)
= if Nil? l
  then begin
    rewrite
      (SM.seq_list_match s l p)
      (SM.seq_list_match_nil0 s);
    let _ = gen_elim () in
    rewrite
      (SM.seq_list_match_nil0 s)
      (SM.seq_list_match s l p1);
    rewrite
      (SM.seq_list_match_nil0 s)
      (SM.seq_list_match s l p2)
  end else begin
    SM.seq_list_match_cons_eq s l p1;
    SM.seq_list_match_cons_eq s l p2;
    SM.seq_list_match_cons_eq s l p;
    noop ();
    rewrite
      (SM.seq_list_match s l p)
      (SM.seq_list_match_cons0 s l p SM.seq_list_match);
    let _ = gen_elim () in
    prf _ _;
    seq_list_match_share p p1 p2 _ _ prf;
    rewrite
      (SM.seq_list_match_cons0 s l p1 SM.seq_list_match)
      (SM.seq_list_match s l p1);
    rewrite
      (SM.seq_list_match_cons0 s l p2 SM.seq_list_match)
      (SM.seq_list_match s l p2)
  end

let rec cbor_share
  (#opened: _)
  (c: cbor)
  (v1: Cbor.raw_data_item)
  (p p1 p2: perm)
: STGhost unit opened
    (raw_data_item_match p c v1)
    (fun _ -> raw_data_item_match p1 c v1 `star` raw_data_item_match p2 c v1)
    (p == p1 `sum_perm` p2)
    (fun _ -> True)
    (decreases v1)
= raw_data_item_match_get_case #_ #p #v1 c;
  match c with
  
  | CBOR_Case_Serialized s fp ->
    rewrite
      (raw_data_item_match p c v1)
      (raw_data_item_match_serialized0 p c v1);
    let _ = gen_elim () in
    GR.share_gen _ p1 p2;
    let w = LPS.share_aparse CborST.parse_raw_data_item _ (p1 `prod_perm` LPA.array_perm s.footprint) (p2 `prod_perm` LPA.array_perm s.footprint) in
    let _ = gen_elim () in
    begin
      noop ();
      rewrite
        (raw_data_item_match_serialized0 p1 c v1)
        (raw_data_item_match p1 c v1)
    end <: STGhostT unit opened (LPS.aparse CborST.parse_raw_data_item _ (fstp w) `star` GR.pts_to _ p1 ()) (fun _ -> raw_data_item_match p1 c v1);
    rewrite
      (raw_data_item_match_serialized0 p2 c v1)
      (raw_data_item_match p2 c v1)

  | CBOR_Case_Simple_value v fp ->
    rewrite
      (raw_data_item_match p c v1)
      (raw_data_item_match_simple_value0 p c v1);
    let _ = gen_elim () in
    GR.share_gen _ p1 p2;
    rewrite
      (raw_data_item_match_simple_value0 p1 c v1)
      (raw_data_item_match p1 c v1);
    rewrite
      (raw_data_item_match_simple_value0 p2 c v1)
      (raw_data_item_match p2 c v1)

  | CBOR_Case_Int64 v fp ->
    rewrite
      (raw_data_item_match p c v1)
      (raw_data_item_match_int0 p c v1);
    let _ = gen_elim () in
    GR.share_gen _ p1 p2;
    rewrite
      (raw_data_item_match_int0 p1 c v1)
      (raw_data_item_match p1 c v1);
    rewrite
      (raw_data_item_match_int0 p2 c v1)
      (raw_data_item_match p2 c v1)

  | CBOR_Case_String v fp p' ->
    rewrite
      (raw_data_item_match p c v1)
      (raw_data_item_match_string0 p c v1);
    let _ = gen_elim () in
    GR.share_gen _ p1 p2;
    A.share _ _ (p1 `prod_perm` p') (p2 `prod_perm` p');
    begin
      noop ();
      rewrite
        (raw_data_item_match_string0 p1 c v1)
        (raw_data_item_match p1 c v1)
    end <: STGhostT unit opened (A.pts_to _ (p1 `prod_perm` p') _ `star` GR.pts_to _ p1 _) (fun _ -> raw_data_item_match p1 c v1);
    rewrite
      (raw_data_item_match_string0 p2 c v1)
      (raw_data_item_match p2 c v1)

  | CBOR_Case_Tagged v ->
    let Cbor.Tagged tg1 v1' = v1 in
    assert_norm (
      raw_data_item_match p1 (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') ==
      raw_data_item_match_tagged0 p1 (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') (raw_data_item_match p1)
    );
    assert_norm (
      raw_data_item_match p2 (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') ==
      raw_data_item_match_tagged0 p2 (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') (raw_data_item_match p2)
    );
    assert_norm (
      raw_data_item_match p (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') ==
      raw_data_item_match_tagged0 p (CBOR_Case_Tagged v) (Cbor.Tagged tg1 v1') (raw_data_item_match p)
    );
    rewrite
      (raw_data_item_match p c v1)
      (raw_data_item_match_tagged0 p c v1 (raw_data_item_match p));
    let _ = gen_elim () in
    R.share_gen _ p1 p2;
    cbor_share _ _ _ p1 p2;
    rewrite
      (raw_data_item_match_tagged0 p1 c v1 (raw_data_item_match p1))
      (raw_data_item_match p1 c v1);
    rewrite
      (raw_data_item_match_tagged0 p2 c v1 (raw_data_item_match p2))
      (raw_data_item_match p2 c v1)

  | CBOR_Case_Array v fp ->
    let Cbor.Array v1' = v1 in
    assert_norm
      (raw_data_item_match p1 (CBOR_Case_Array v fp) (Cbor.Array v1') ==
        raw_data_item_match_array0 p1 (CBOR_Case_Array v fp) (Cbor.Array v1') (raw_data_item_array_match p1)
      );
    assert_norm
      (raw_data_item_match p (CBOR_Case_Array v fp) (Cbor.Array v1') ==
        raw_data_item_match_array0 p (CBOR_Case_Array v fp) (Cbor.Array v1') (raw_data_item_array_match p)
      );
    assert_norm
      (raw_data_item_match p2 (CBOR_Case_Array v fp) (Cbor.Array v1') ==
        raw_data_item_match_array0 p2 (CBOR_Case_Array v fp) (Cbor.Array v1') (raw_data_item_array_match p2)
      );
    noop ();
    rewrite
      (raw_data_item_match p c v1)
      (raw_data_item_match_array0 p c v1 (raw_data_item_array_match p));
    let _ = gen_elim () in
    vpattern_rewrite (A.pts_to _ _) (Ghost.reveal v.footprint);
    rewrite (raw_data_item_array_match _ _ _) (SM.seq_list_match v.footprint (Cbor.Array?.v v1) (raw_data_item_match p));
    GR.share_gen _ p1 p2;
    A.share _ _ p1 p2;
    seq_list_match_share
      (raw_data_item_match p)
      (raw_data_item_match p1)
      (raw_data_item_match p2)
      v.footprint
      (Cbor.Array?.v v1)
      (fun x x1' ->
        cbor_share x x1' p p1 p2
      );
    rewrite
      (SM.seq_list_match v.footprint (Cbor.Array?.v v1) (raw_data_item_match p1))
      (raw_data_item_array_match p1 v.footprint (Cbor.Array?.v v1));
    rewrite
      (raw_data_item_match_array0 p1 c v1 (raw_data_item_array_match p1))
      (raw_data_item_match p1 c v1);
    rewrite
      (SM.seq_list_match v.footprint (Cbor.Array?.v v1) (raw_data_item_match p2))
      (raw_data_item_array_match p2 v.footprint (Cbor.Array?.v v1));
    rewrite
      (raw_data_item_match_array0 p2 c v1 (raw_data_item_array_match p2))
      (raw_data_item_match p2 c v1)

  | CBOR_Case_Map _ _ ->
    let _ : squash (Cbor.Map? v1) = () in
    destr_cbor_map' c;
    GR.share_gen _ p1 p2;
    A.share _ _ p1 p2;
    seq_list_match_share
      (raw_data_item_map_entry_match p)
      (raw_data_item_map_entry_match p1)
      (raw_data_item_map_entry_match p2)
      _
      _
      (fun x x1' ->
        cbor_share (cbor_map_entry_key x) (fstp x1') p p1 p2;
        cbor_share (cbor_map_entry_value x) (sndp x1') p p1 p2
      );
    constr_cbor_map' p1 c v1 _ _ _ _;
    constr_cbor_map' p2 c v1 _ _ _ _

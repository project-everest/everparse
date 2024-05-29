module CDDL.Spec.MapGroupGen.Base

module FE = FStar.FunctionalExtensionality

let cbor_map = ghost_map Cbor.raw_data_item Cbor.raw_data_item

let map_group_item : Type0 =
  (cbor_map & cbor_map)

noeq
type map_group_sem_result =
| MapGroupResult of FStar.GSet.set map_group_item
| MapGroupCutFailure

let map_group_post'
  (l: cbor_map)
  (res: FStar.GSet.set map_group_item)
: Tot prop
=
      forall l' .
      FStar.GSet.mem l' res ==>  map_group_item_post l l'

let map_group_post
  (l: cbor_map)
  (res: map_group_sem_result)
: Tot prop
= match res with
  | MapGroupResult res -> map_group_post' l res
  | MapGroupCutFailure -> True

let map_group_codom
  (l: cbor_map)
: Tot Type0
= (res: map_group_sem_result {
      map_group_post l res
  })

let map_group : Type0 =
  FE.restricted_g_t
    (cbor_map)
    (map_group_codom)

let map_group_always_false : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun _ -> MapGroupResult FStar.GSet.empty)

let map_group_nop : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l -> MapGroupResult (FStar.GSet.singleton (ghost_map_empty, l)))

let ghost_map_is_empty
  (#key #value: Type)
  (m: ghost_map key value)
: Ghost bool
  (requires True)
  (ensures fun res -> res == true <==> m == ghost_map_empty)
= FStar.StrongExcludedMiddle.strong_excluded_middle (m == ghost_map_empty)

let map_group_end : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l -> if ghost_map_is_empty l then map_group_nop l else map_group_always_false l)

unfold
let map_group_match_item_witness_pred (key value: typ) (l: cbor_map) (l': cbor_map & cbor_map) (x: Cbor.raw_data_item & Cbor.raw_data_item) : Tot prop =
  map_group_item_post l l' /\
  fst l' == ghost_map_singleton (fst x) (snd x) /\
  key (fst x) /\
  value (snd x)

let pred2_equiv_trans
  (#t #t': Type)
  (p1 p2 p3: t -> t' -> prop)
: Lemma
  (requires (
    (forall x x' . p1 x x' <==> p2 x x') /\
    (forall x x' . p2 x x' <==> p3 x x')
  ))
  (ensures (
    (forall x x' . p1 x x' <==> p3 x x')
  ))
= ()

let map_group_match_item_comprehend
  (key value: typ)
  (l: cbor_map)
  l'
: GTot bool
=
    FStar.StrongExcludedMiddle.strong_excluded_middle (exists x .
      map_group_match_item_witness_pred key value l l' x
    )

let map_group_match_item' (key value: typ) (l: cbor_map) : FStar.GSet.set map_group_item =
  FStar.GSet.comprehend (map_group_match_item_comprehend key value l)

let map_group_match_item_elim (key value: typ) (l: cbor_map) l' : Ghost _
  (requires (FStar.GSet.mem l' (map_group_match_item' key value l)))
  (ensures (fun x -> map_group_match_item_witness_pred key value l l' x))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (map_group_match_item_witness_pred key value l l')

let map_group_match_item_cut_failure_witness_pred (key: typ) (s: FStar.GSet.set map_group_item) (l': (map_group_item & (Cbor.raw_data_item & Cbor.raw_data_item))) : Tot prop =
  let (elt, entry) = l' in
  let (_, rem) = elt in
  let (k, _) = entry in
  FStar.GSet.mem elt s /\
  ghost_map_mem entry rem /\
  key k

let maybe_indefinite_description_ghost (#t: Type) (p: t -> prop) : Ghost (option t)
  (requires True)
  (ensures fun res ->
    (Some? res <==> (exists l . p l)) /\
    begin match res with
    | None -> True
    | Some l -> p l
    end
  )
= if FStar.StrongExcludedMiddle.strong_excluded_middle (exists l . p l)
  then Some (FStar.IndefiniteDescription.indefinite_description_ghost _ p)
  else None

#restart-solver
let gset_is_empty
  (#t: Type)
  (s: FStar.GSet.set t)
: Ghost (option t)
    (requires True)
    (ensures fun res -> 
    (None? res <==> s == FStar.GSet.empty) /\
    begin match res with
    | None -> True
    | Some x -> FStar.GSet.mem x s
    end
    )
= match maybe_indefinite_description_ghost (fun x -> FStar.GSet.mem x s) with
  | Some x -> Some x
  | None ->
    assert (s `FStar.GSet.equal` FStar.GSet.empty);
    None

let map_group_match_item_cut_pre
  (l: cbor_map)
  (s: FStar.GSet.set map_group_item)
: GTot (FStar.GSet.set map_group_item)
= 
    match gset_is_empty s with
    | None -> FStar.GSet.singleton (ghost_map_empty, l)
    | _ -> s

let map_group_match_item_cut
  (key: typ)
  (l: cbor_map)
  (s: FStar.GSet.set map_group_item)
: GTot map_group_sem_result
= 
  let s' = map_group_match_item_cut_pre l s in
  match maybe_indefinite_description_ghost (map_group_match_item_cut_failure_witness_pred key s') with
  | Some _ -> MapGroupCutFailure
  | _ -> MapGroupResult s

let map_group_match_item (cut: bool) (key value: typ) : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l ->
      let s = map_group_match_item' key value l in
      if cut
      then map_group_match_item_cut key l s
      else MapGroupResult s
    )

let map_group_match_item_ext
  cut key value key' value'
= assert (forall l l' x . map_group_match_item_witness_pred key value l l' x <==> map_group_match_item_witness_pred key' value' l l' x);
  assert (forall s l' . map_group_match_item_cut_failure_witness_pred key s l' <==> map_group_match_item_cut_failure_witness_pred key' s l');
  assert (forall x . map_group_match_item' key value x `FStar.GSet.equal` map_group_match_item' key' value' x);
  assert (map_group_match_item cut key value `FE.feq_g` map_group_match_item cut key' value')

let gset_map_witness_pred (#t1 #t2: Type) (f: t1 -> GTot t2) (s: FStar.GSet.set t1) x2 x1 : GTot prop =
  x2 == f x1 /\ FStar.GSet.mem x1 s

let gset_map (#t1 #t2: Type) (f: t1 -> GTot t2) (s: FStar.GSet.set t1) : FStar.GSet.set t2 =
  FStar.GSet.comprehend (fun x2 -> FStar.StrongExcludedMiddle.strong_excluded_middle (exists x1 .
    gset_map_witness_pred f s x2 x1
  ))

let gset_map_elim #t1 #t2 (f: t1 -> GTot t2) (s: FStar.GSet.set t1) (x2: t2) : Ghost t1
  (requires FStar.GSet.mem x2 (gset_map f s))
  (ensures fun x1 -> gset_map_witness_pred f s x2 x1)
= FStar.IndefiniteDescription.indefinite_description_ghost _ (gset_map_witness_pred f s x2)

let map_group_match_item_alt_pred
  (key value: typ)
  (l: cbor_map)
  (kv: (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot prop
= ghost_map_mem kv l /\
  matches_map_group_entry key value kv

let map_group_match_item_alt_r
  l0
  (ll, lr)
= (ll, ghost_map_union l0 lr)

let map_group_match_item_alt (key value: typ) (l: cbor_map) : GTot _ =
  match maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value l) with
  | None -> FStar.GSet.empty
  | Some kv ->
    let l1 = ghost_map_singleton (fst kv) (snd kv) in
    let l2 = ghost_map_sub l l1 in
    FStar.GSet.union (FStar.GSet.singleton (l1, l2))
      (gset_map (map_group_match_item_alt_r l1) (map_group_match_item' key value l2))

#restart-solver
let map_group_match_item_alt_map_group_match_item
  (key value: typ) (l: cbor_map) l'
: Lemma
  (FStar.GSet.mem l' (map_group_match_item_alt key value l) ==> FStar.GSet.mem l' (map_group_match_item' key value l))
=
  if FStar.GSet.mem l' (map_group_match_item_alt key value l)
  then begin
    let Some kv = maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value l) in
    let l1 = ghost_map_singleton (fst kv) (snd kv) in
    let l2 = ghost_map_sub l l1 in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (l' == (l1, l2))
    then assert (map_group_match_item_witness_pred key value l l' kv)
    else begin
      let x = gset_map_elim (map_group_match_item_alt_r l1) (map_group_match_item' key value l2) l' in
      let kv' = map_group_match_item_elim key value l2 x in
      ghost_map_union_assoc l1 (fst x) (snd x);
      ghost_map_disjoint_union_comm l1 (fst x);
      ghost_map_union_assoc (fst x) l1 (snd x);
      assert (map_group_match_item_witness_pred key value l l' kv')
    end
  end

let map_group_match_item_map_group_match_item_alt
  (key value: typ) (l: cbor_map) l'
: Lemma
  (FStar.GSet.mem l' (map_group_match_item' key value l) ==> FStar.GSet.mem l' (map_group_match_item_alt key value l))
= if FStar.GSet.mem l' (map_group_match_item' key value l)
  then begin
    let kv' = map_group_match_item_elim key value l l' in
    assert (map_group_match_item_alt_pred key value l kv');
    let Some kv = maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value l) in
    let l1 = ghost_map_singleton (fst kv) (snd kv) in
    let l2 = ghost_map_sub l l1 in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (kv == kv')
    then ghost_map_disjoint_union_simpl_l l1 l2 (snd l')
    else begin
      assert (ghost_map_mem kv' l2);
      let l2' = snd l' `ghost_map_sub` l1 in
      ghost_map_disjoint_union_comm l1 l2';
      ghost_map_union_assoc (fst l') l1 l2';
      ghost_map_disjoint_union_comm (fst l') l1;
      ghost_map_union_assoc l1 (fst l') l2';
      ghost_map_disjoint_union_simpl_l l1 (fst l' `ghost_map_union` l2') l2;
      assert (map_group_match_item_witness_pred key value l2 (fst l', l2') kv');
      assert (gset_map_witness_pred (map_group_match_item_alt_r l1) (map_group_match_item' key value l2) l' (fst l', l2'))
    end
  end

let map_group_equiv
  (m1 m2: map_group)
: Tot prop
= forall l . match m1 l, m2 l with
  | MapGroupCutFailure, MapGroupCutFailure -> True
  | MapGroupResult s1, MapGroupResult s2 -> s1 `FStar.GSet.equal` s2
  | _ -> False

let map_group_equiv_eq
  (m1 m2: map_group)
: Lemma
  (map_group_equiv m1 m2 <==> m1 == m2)
  [SMTPat (map_group_equiv m1 m2)]
= assert (FE.feq_g m1 m2 <==> m1 == m2)

let map_group_match_item_alt_correct
  (key value: typ) (l: cbor_map)
: Lemma
  (map_group_match_item_alt key value l == map_group_match_item' key value l)
= Classical.forall_intro (map_group_match_item_map_group_match_item_alt key value l);
  Classical.forall_intro (map_group_match_item_alt_map_group_match_item key value l);
  assert (map_group_match_item_alt key value l `FStar.GSet.equal` map_group_match_item' key value l)

let map_group_choice (m1 m2: map_group) : map_group =
  FE.on_dom_g cbor_map #map_group_codom (fun l ->
    // greedy PEG semantics for `//`
    match m1 l with
    | MapGroupCutFailure -> MapGroupCutFailure
    | MapGroupResult res1 ->
      if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
      then m2 l
      else MapGroupResult res1
  )

let map_group_choice_assoc
  (g1 g2 g3: map_group)
: Lemma
  ((g1 `map_group_choice` g2) `map_group_choice` g3 == g1 `map_group_choice` (g2 `map_group_choice` g3))
= assert (((g1 `map_group_choice` g2) `map_group_choice` g3) `map_group_equiv` (g1 `map_group_choice` (g2 `map_group_choice` g3)))

let map_group_choice_always_false_l
  (g: map_group)
: Lemma
  (map_group_choice map_group_always_false g == g)
= assert (map_group_choice map_group_always_false g `map_group_equiv` g)

let map_group_choice_always_false_r
  (g: map_group)
: Lemma
  (map_group_choice g map_group_always_false == g)
= assert (map_group_choice g map_group_always_false `map_group_equiv` g)

let map_group_concat_witness_pred
  (m1 m2: map_group)
  (l: cbor_map)
  (l': (cbor_map & cbor_map))
  (l1l2: ((cbor_map & cbor_map) & (cbor_map & cbor_map)))
: Tot prop
= let (l1, l2) = l1l2 in
  MapGroupResult? (m1 l) /\
  FStar.GSet.mem l1 (MapGroupResult?._0 (m1 l)) /\
  MapGroupResult? (m2 (snd l1)) /\
  FStar.GSet.mem l2 (MapGroupResult?._0 (m2 (snd l1))) /\
  fst l' `ghost_map_feq` (fst l1 `ghost_map_union` fst l2) /\
  snd l' == snd l2

let ghost_map_disjoint_union_elim
  (#key #value: Type)
  (m m1 m2: ghost_map key value)
: Lemma
  (requires ghost_map_disjoint m (m1 `ghost_map_union` m2))
  (ensures ghost_map_disjoint m m1 /\ ghost_map_disjoint m m2)
= ()

let ghost_map_disjoint_union_intro
  (#key #value: Type)
  (m m1 m2: ghost_map key value)
: Lemma
  (requires ghost_map_disjoint m m1 /\ ghost_map_disjoint m m2)
  (ensures ghost_map_disjoint m (m1 `ghost_map_union` m2))
= ()

#push-options "--z3rlimit 16"

#restart-solver
let map_group_concat_witness_pred_correct
  (m1 m2: map_group)
  (l: cbor_map)
  (l': (cbor_map & cbor_map))
  (l1l2: ((cbor_map & cbor_map) & (cbor_map & cbor_map)))
: Lemma
  (requires map_group_concat_witness_pred m1 m2 l l' l1l2)
  (ensures map_group_item_post l l' /\
    fst (fst l1l2) `ghost_map_disjoint` fst (snd l1l2))
  [SMTPat (map_group_concat_witness_pred m1 m2 l l' l1l2)]
= let (l1, l2) = l1l2 in
  ghost_map_union_assoc (fst l1) (fst l2) (snd l2);
  assert ((fst l1 `ghost_map_union` fst l2) `ghost_map_union` snd l2 == l);
  assert (fst l1 `ghost_map_disjoint` snd l1);
  assert (snd l1 == fst l2 `ghost_map_union` snd l2);
  ghost_map_disjoint_union_elim (fst l1) (fst l2) (snd l2);
  assert (fst l1 `ghost_map_disjoint` fst l2);
  assert (fst l2 `ghost_map_disjoint` snd l2);
  assert (ghost_map_disjoint (fst l1 `ghost_map_union` fst l2) (snd l2))

#pop-options

let map_group_concat_cut_failure_witness_pred
  (m1 m2: map_group)
  (l: cbor_map)
  (l1: map_group_item)
: Tot prop
= MapGroupResult? (m1 l) /\
  FStar.GSet.mem l1 (MapGroupResult?._0 (m1 l)) /\
  MapGroupCutFailure? (m2 (snd l1))

let map_group_concat (m1 m2: map_group) : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l -> 
      if MapGroupCutFailure? (m1 l)
      then MapGroupCutFailure
      else if FStar.StrongExcludedMiddle.strong_excluded_middle (exists l1 . map_group_concat_cut_failure_witness_pred m1 m2 l l1)
      then MapGroupCutFailure
      else MapGroupResult (
        FStar.GSet.comprehend (fun l' -> FStar.StrongExcludedMiddle.strong_excluded_middle (exists l1l2 . map_group_concat_witness_pred m1 m2 l l' l1l2))
    ))
  
let map_group_concat_elim (m1 m2: map_group) (l: cbor_map) l' : Ghost _
  (requires (match map_group_concat m1 m2 l with
  | MapGroupResult s -> FStar.GSet.mem l' s
  | _ -> False
  ))
  (ensures fun l1l2 ->
    map_group_concat_witness_pred m1 m2 l l' l1l2
  )
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l1l2 -> map_group_concat_witness_pred m1 m2 l l' l1l2)

let map_group_equiv_intro
  (m1 m2: map_group)
  (prf0: (l: cbor_map) -> Lemma (MapGroupCutFailure? (m1 l) == MapGroupCutFailure? (m2 l)))
  (prf12: (l: cbor_map) ->
    (l': _) ->
    Lemma
    (requires (match m1 l, m2 l with
    | MapGroupResult s1, MapGroupResult _ -> FStar.GSet.mem l' s1
    | _ -> False
    ))
    (ensures (match m2 l with
    | MapGroupResult s2 -> FStar.GSet.mem l' s2
    | _ -> True
    ))
  )
  (prf21: (l: cbor_map) ->
    (l': _) ->
    Lemma
    (requires (match m1 l, m2 l with
    | MapGroupResult _, MapGroupResult s2 -> FStar.GSet.mem l' s2
    | _ -> False
    ))
    (ensures (match m1 l with
    | MapGroupResult s1 -> FStar.GSet.mem l' s1
    | _ -> True
    ))
  )
: Lemma
  (map_group_equiv m1 m2)
= Classical.forall_intro prf0;
  Classical.forall_intro_2 (fun l l' -> Classical.move_requires (prf12 l) l');
  Classical.forall_intro_2 (fun l l' -> Classical.move_requires (prf21 l) l')

let map_group_equiv_intro_equiv
  (m1 m2: map_group)
  (prf0: (l: cbor_map) -> Lemma (MapGroupCutFailure? (m1 l) == MapGroupCutFailure? (m2 l)))
  (prf: (l: cbor_map) ->
    (l': _) ->
    Lemma
    (requires (
      MapGroupResult? (m1 l) /\ MapGroupResult? (m2 l)
    ))
    (ensures (match m1 l, m2 l with
    | MapGroupResult s1, MapGroupResult s2 -> (FStar.GSet.mem l' s1 <==> FStar.GSet.mem l' s2)
    | _ -> True
    ))
  )
: Lemma
  (map_group_equiv m1 m2)
= map_group_equiv_intro m1 m2 prf0 (fun l l' -> prf0 l; prf l l') (fun l l' -> prf0 l; prf l l')

let map_group_equiv_intro_equiv_rec
  (m1 m2: map_group)
  (prf0: (l: cbor_map) -> 
    (prf: (
      (l1: cbor_map { ghost_map_length l1 < ghost_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    Lemma (MapGroupCutFailure? (m1 l) == MapGroupCutFailure? (m2 l)))
  (prf: (l: cbor_map) ->
    (prf: (
      (l1: cbor_map { ghost_map_length l1 < ghost_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    (l': _) ->
    Lemma
    (requires (
      MapGroupResult? (m1 l) /\ MapGroupResult? (m2 l)
    ))
    (ensures (match m1 l, m2 l with
    | MapGroupResult s1, MapGroupResult s2 -> (FStar.GSet.mem l' s1 <==> FStar.GSet.mem l' s2)
    | _ -> True
    ))
  )
: Lemma
  (map_group_equiv m1 m2)
= let rec prf'
      (l: cbor_map)
  : Lemma
      (ensures (m1 l == m2 l))
      (decreases (ghost_map_length l))
  = prf0 l prf';
    match m1 l with
    | MapGroupCutFailure -> ()
    | MapGroupResult s1 ->
      Classical.forall_intro (Classical.move_requires (prf l prf'));
      assert (s1 `FStar.GSet.equal` MapGroupResult?._0 (m2 l))
  in
  map_group_equiv_intro_equiv m1 m2 (fun l -> prf' l) (fun l _ -> prf' l)

let map_group_equiv_intro_rec
  (m1 m2: map_group)
  (prf0: (l: cbor_map) -> 
    (prf: (
      (l1: cbor_map { ghost_map_length l1 < ghost_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    Lemma (MapGroupCutFailure? (m1 l) == MapGroupCutFailure? (m2 l)))
  (prf12: (l: cbor_map) ->
    (prf: (
      (l1: cbor_map { ghost_map_length l1 < ghost_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    (l': _) ->
    Lemma
    (requires (match m1 l, m2 l with
    | MapGroupResult s1, MapGroupResult _ -> FStar.GSet.mem l' s1
    | _ -> False
    ))
    (ensures (match m2 l with
    | MapGroupResult s2 -> FStar.GSet.mem l' s2
    | _ -> True
    ))
  )
  (prf21: (l: cbor_map) ->
    (prf: (
      (l1: cbor_map { ghost_map_length l1 < ghost_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    (l': _) ->
    Lemma
    (requires (match m1 l, m2 l with
    | MapGroupResult _, MapGroupResult s2 -> FStar.GSet.mem l' s2
    | _ -> False
    ))
    (ensures (match m1 l with
    | MapGroupResult s1 -> FStar.GSet.mem l' s1
    | _ -> True
    ))
  )
: Lemma
  (map_group_equiv m1 m2)
= map_group_equiv_intro_equiv_rec m1 m2 prf0 (fun l prf l' ->
    Classical.move_requires (prf12 l prf) l';
    Classical.move_requires (prf21 l prf) l'
  )

let ghost_map_disjoint_union_assoc_domain
  (#key #value: Type)
  (f1 f2 f3: ghost_map key value)
: Lemma
  (ensures (
    (f1 `ghost_map_disjoint` f2 /\ (f1 `ghost_map_union` f2) `ghost_map_disjoint` f3) <==>
      (f2 `ghost_map_disjoint` f3 /\ f1 `ghost_map_disjoint` (f2 `ghost_map_union` f3))
  ))
= ()

let ghost_map_disjoint_union_assoc
  (#key #value: Type)
  (f1 f2 f3: ghost_map key value)
: Lemma
  (requires
      (f1 `ghost_map_disjoint` f2 /\ (f1 `ghost_map_union` f2) `ghost_map_disjoint` f3) \/
      (f2 `ghost_map_disjoint` f3 /\ f1 `ghost_map_disjoint` (f2 `ghost_map_union` f3))
  )
  (ensures
    (f1 `ghost_map_union` (f2 `ghost_map_union` f3) == (f1 `ghost_map_union` f2) `ghost_map_union` f3)
  )
= assert ((f1 `ghost_map_union` (f2 `ghost_map_union` f3)) `ghost_map_feq` ((f1 `ghost_map_union` f2) `ghost_map_union` f3))

#push-options "--z3rlimit 32"

#restart-solver
let map_group_concat_assoc' (m1 m2 m3: map_group) : Lemma
  (map_group_concat m1 (map_group_concat m2 m3) `map_group_equiv` map_group_concat (map_group_concat m1 m2) m3)
= map_group_equiv_intro
    (map_group_concat m1 (map_group_concat m2 m3))
    (map_group_concat (map_group_concat m1 m2) m3)
    (fun l -> match m1 l with
    | MapGroupCutFailure -> ()
    | MapGroupResult s1 ->
      if FStar.StrongExcludedMiddle.strong_excluded_middle (exists l1 . map_group_concat_cut_failure_witness_pred m1 m2 l l1)
      then
        let l1 = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l1 -> map_group_concat_cut_failure_witness_pred m1 m2 l l1) in
        assert (map_group_concat_cut_failure_witness_pred m1 (map_group_concat m2 m3) l l1)
      else if FStar.StrongExcludedMiddle.strong_excluded_middle (exists l12 . map_group_concat_cut_failure_witness_pred (map_group_concat m1 m2) m3 l l12)
      then
        let l12 = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l12 -> map_group_concat_cut_failure_witness_pred (map_group_concat m1 m2) m3 l l12) in
        let (l1, l2) = map_group_concat_elim m1 m2 l l12 in
        assert (map_group_concat_cut_failure_witness_pred m2 m3 (snd l1) l2);
        assert (map_group_concat_cut_failure_witness_pred m1 (map_group_concat m2 m3) l l1)
      else if FStar.StrongExcludedMiddle.strong_excluded_middle (exists l1 . map_group_concat_cut_failure_witness_pred m1 (map_group_concat m2 m3) l l1)
      then
        let l1 = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l1 -> map_group_concat_cut_failure_witness_pred m1 (map_group_concat m2 m3) l l1) in
        assert (MapGroupResult? (m2 (snd l1)));
        let l2 = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l2 -> map_group_concat_cut_failure_witness_pred m2 m3 (snd l1) l2) in
        let l12 = (fst l1 `ghost_map_union` fst l2, snd l2) in
        assert (map_group_concat_witness_pred m1 m2 l l12 (l1, l2));
        assert (map_group_concat_cut_failure_witness_pred (map_group_concat m1 m2) m3 l l12)
      else ()
    )
    (fun l l' -> 
      let (l1, l23) = map_group_concat_elim m1 (map_group_concat m2 m3) l l' in
      ghost_map_disjoint_mem_union' (fst l1) (fst l23) ();
      let (l2, l3) = map_group_concat_elim m2 m3 (snd l1) l23 in
      ghost_map_disjoint_mem_union' (fst l2) (fst l3) ();
      assert (FStar.GSet.mem l1 (MapGroupResult?._0 (m1 l)));
      assert (FStar.GSet.mem l2 (MapGroupResult?._0 (m2 (snd l1))));
      assert (FStar.GSet.mem l3 (MapGroupResult?._0 (m3 (snd l2))));
      let l12 = (fst l1 `ghost_map_union` fst l2, snd l2) in
      ghost_map_disjoint_mem_union' (fst l1) (fst l2) ();
      assert (map_group_concat_witness_pred m1 m2 l l12 (l1, l2));
      ghost_map_disjoint_union_assoc (fst l1) (fst l2) (fst l3);
      ghost_map_disjoint_mem_union' (fst l12) (fst l3) ();
      assert (map_group_concat_witness_pred (map_group_concat m1 m2) m3 l l' (l12, l3))
    )
    (fun l l' ->
      let (l12, l3) = map_group_concat_elim (map_group_concat m1 m2) m3 l l' in
      ghost_map_disjoint_mem_union' (fst l12) (fst l3) ();
      let (l1, l2) = map_group_concat_elim m1 m2 l l12 in
      ghost_map_disjoint_mem_union' (fst l1) (fst l2) ();
      let l23 = (fst l2 `ghost_map_union` fst l3, snd l3) in
      ghost_map_disjoint_mem_union' (fst l2) (fst l3) ();
      assert (map_group_concat_witness_pred m2 m3 (snd l1) l23 (l2, l3));
      ghost_map_disjoint_union_assoc (fst l1) (fst l2) (fst l3);
      ghost_map_disjoint_mem_union' (fst l1) (fst l23) ();
      assert (map_group_concat_witness_pred m1 (map_group_concat m2 m3) l l' (l1, l23))
    )

#pop-options

let map_group_concat_assoc m1 m2 m3 =
  map_group_concat_assoc' m1 m2 m3

#restart-solver
let map_group_concat_nop_l
  (m: map_group)
: Lemma
  (map_group_concat map_group_nop m == m)
= map_group_equiv_intro
    (map_group_concat map_group_nop m)
    m
    (fun l -> match m l with
    | MapGroupCutFailure -> assert (map_group_concat_cut_failure_witness_pred map_group_nop m l (ghost_map_empty, l))
    | MapGroupResult _ -> ()
    )
    (fun l l' ->
      let (l1, l2) = map_group_concat_elim map_group_nop m l l' in
      assert (fst l' `ghost_map_feq` fst l2)
    )
    (fun l l' ->
      assert (map_group_concat_witness_pred map_group_nop m l l' ((ghost_map_empty, l), l'))
    )

let map_group_concat_nop_r
  (m: map_group)
: Lemma
  (map_group_concat m map_group_nop == m)
= map_group_equiv_intro
    (map_group_concat m map_group_nop)
    m
    (fun _ -> ())
    (fun l l' ->
      let (l1, l2) = map_group_concat_elim m map_group_nop l l' in
      assert (fst l' `ghost_map_feq` fst l1)
    )
    (fun l l' -> 
      assert (map_group_concat_witness_pred m map_group_nop l l' (l', (ghost_map_empty, snd l')))
    )

let map_group_concat_always_false
  (m: map_group)
: Lemma
  (map_group_concat map_group_always_false m == map_group_always_false)
= map_group_equiv_intro_equiv
    (map_group_concat map_group_always_false m)
    map_group_always_false
    (fun _ -> ())
    (fun _ _ -> ())

let bound_map_group
  (l0: cbor_map)
  (m: (l: cbor_map { ghost_map_length l < ghost_map_length l0 }) ->
  Ghost _
    (requires True)
    (ensures fun l' -> map_group_post l l')
  )
: map_group
= FE.on_dom_g cbor_map #map_group_codom
    (fun l -> if ghost_map_length l >= ghost_map_length l0 then map_group_nop l else m l)

let bound_map_group_ext
  (l0: cbor_map)
  (m1 m2: (l: cbor_map { ghost_map_length l < ghost_map_length l0 }) ->
  Ghost _
    (requires True)
    (ensures fun l' -> map_group_post l l')
  )
: Lemma
  (requires forall (l: cbor_map { ghost_map_length l < ghost_map_length l0 }) .
    m1 l == m2 l
  )
  (ensures bound_map_group l0 m1 == bound_map_group l0 m2)
= map_group_equiv_intro (bound_map_group l0 m1) (bound_map_group l0 m2)
    (fun l -> ())
    (fun l l' -> ())
    (fun l l' -> ())

let bound_map_group_ext'
  (l0: cbor_map)
  (m1 m2: (l: cbor_map { ghost_map_length l < ghost_map_length l0 }) ->
  Ghost _
    (requires True)
    (ensures fun l' -> map_group_post l l')
  )
  (prf: (l: cbor_map { ghost_map_length l < ghost_map_length l0 }) -> Lemma
    (m1 l == m2 l)
  )
: Lemma
  (ensures bound_map_group l0 m1 == bound_map_group l0 m2)
= Classical.forall_intro prf;
  bound_map_group_ext l0 m1 m2

#restart-solver
let map_group_concat_eq_r
  (m1 m2 m2': map_group)
  (l: cbor_map)
  (prf: (l1: _) -> Lemma
    (requires (match m1 l with
    | MapGroupResult s -> FStar.GSet.mem l1 s
    | _ -> False
    ))
    (ensures (m2 (snd l1) == m2' (snd l1)))
  )
: Lemma
  ((m1 `map_group_concat` m2) l == (m1 `map_group_concat` m2') l)
= Classical.forall_intro (Classical.move_requires prf);
  begin match (m1 `map_group_concat` m2) l, (m1 `map_group_concat` m2') l with
  | MapGroupResult s1, MapGroupResult s2 -> assert (s1 `FStar.GSet.equal` s2)
  | _ -> ()
  end

let map_group_is_productive
  (m: map_group)
: Tot prop
=
  forall l . match m l with
  | MapGroupCutFailure -> True
  | MapGroupResult s -> forall l' . FStar.GSet.mem l' s ==> ghost_map_length (snd l') < ghost_map_length l

let map_group_is_productive_always_false = ()

let map_group_is_productive_match_item
  (cut: bool)
  (key value: typ)
: Lemma
  (map_group_is_productive (map_group_match_item cut key value))
= ()

let map_group_is_productive_choice
  (m1 m2: map_group)
: Lemma
  (requires (
    map_group_is_productive m1 /\
    map_group_is_productive m2
  ))
  (ensures (
    map_group_is_productive (m1 `map_group_choice` m2)
  ))
= ()

let map_group_is_productive_concat
  (m1 m2: map_group)
: Lemma
  (requires (
    map_group_is_productive m1 \/
    map_group_is_productive m2
  ))
  (ensures (
    map_group_is_productive (m1 `map_group_concat` m2)
  ))
= ()

let map_group_is_productive_concat_bound
  (l0: cbor_map)
  (m1: map_group { map_group_is_productive m1 })
  (l1: cbor_map { ghost_map_length l1 <= ghost_map_length l0 })
  (m2: map_group)
: Lemma
  ((m1 `map_group_concat` bound_map_group l0 m2) l1 == (m1 `map_group_concat` m2) l1)
= map_group_concat_eq_r
    m1 (bound_map_group l0 m2) m2 l1 (fun _ -> ())

// greedy PEG semantics for `*`
let rec map_group_zero_or_more'
  (m: map_group)
  (l: cbor_map)
: GTot (l': _ {
    map_group_post l l'
  })
  (decreases (ghost_map_length l))
= match m l with
  | MapGroupCutFailure -> MapGroupCutFailure
  | MapGroupResult res1 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
    then map_group_nop l
    else map_group_concat m (bound_map_group l (map_group_zero_or_more' m)) l

let map_group_zero_or_more m =
  FE.on_dom_g cbor_map #map_group_codom (map_group_zero_or_more' m)

let map_group_zero_or_more_eq
  (m: map_group)
  (l: cbor_map)
: Lemma
  (ensures (map_group_zero_or_more m l == (match m l with
  | MapGroupCutFailure -> MapGroupCutFailure
  | MapGroupResult res1 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
    then map_group_nop l
    else map_group_concat m (bound_map_group l (map_group_zero_or_more m)) l
  )))
  (decreases (ghost_map_length l))
= assert (forall l . map_group_zero_or_more m l == map_group_zero_or_more' m l);
  assert_norm (map_group_zero_or_more' m l == (match m l with
  | MapGroupCutFailure -> MapGroupCutFailure
  | MapGroupResult res1 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
    then map_group_nop l
    else map_group_concat m (bound_map_group l (map_group_zero_or_more' m)) l
  ));
  bound_map_group_ext l (map_group_zero_or_more m) (map_group_zero_or_more' m)

#restart-solver
let map_group_match_item_for_eq_none
  (cut: bool)
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (requires (
    ~ (ghost_map_defined k l)
  ))
  (ensures (
    map_group_match_item_for cut k ty l == MapGroupResult FStar.GSet.empty
  ))
= map_group_match_item_alt_correct (t_literal k) ty l

#restart-solver
let map_group_match_item_for_eq
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (ensures (
    map_group_match_item_for false k ty l == begin match apply_ghost_map l k with
    | Some v ->
      if ty v
      then
        let s = ghost_map_singleton k v in
        MapGroupResult (FStar.GSet.singleton (s, l `ghost_map_sub` s))
      else
        MapGroupResult FStar.GSet.empty
    | _ -> MapGroupResult FStar.GSet.empty
    end
  ))
= map_group_match_item_alt_correct (t_literal k) ty l;
  match maybe_indefinite_description_ghost (map_group_match_item_alt_pred (t_literal k) ty l) with
  | None ->
    begin match apply_ghost_map l k with
    | None -> ()
    | Some v -> if ty v
      then assert (map_group_match_item_alt_pred (t_literal k) ty l (k, v))
      else ()
    end
  | Some (k', v) ->
    assert (k == k');
    assert (apply_ghost_map l k == Some v);
    let l1 = ghost_map_singleton k v in
    let l2 = l `ghost_map_sub` l1 in
    map_group_match_item_for_eq_none false k ty l2;
    assert (FStar.GSet.equal
      (gset_map (map_group_match_item_alt_r l1) (map_group_match_item' (t_literal k) ty l2))
      FStar.GSet.empty
    );
    assert (FStar.GSet.equal
      (FStar.GSet.singleton (l1, l2) `FStar.GSet.union` FStar.GSet.empty)
      (FStar.GSet.singleton (l1, l2))
    )

#restart-solver
let map_group_match_item_for_eq_gen
  (cut: bool)
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (ensures (
    map_group_match_item_for cut k ty l == begin match apply_ghost_map l k with
    | Some v ->
      if ty v
      then
        let s = ghost_map_singleton k v in
        MapGroupResult (FStar.GSet.singleton (s, l `ghost_map_sub` s))
      else if cut
      then MapGroupCutFailure
      else
        MapGroupResult FStar.GSet.empty
    | _ -> MapGroupResult FStar.GSet.empty
    end
  ))
= map_group_match_item_for_eq k ty l;
  if cut
  then match apply_ghost_map l k with
  | None -> ()
  | Some v ->
    let l1 = ghost_map_singleton k v in
    let l2 = l `ghost_map_sub` l1 in
    if ty v
    then match maybe_indefinite_description_ghost (map_group_match_item_cut_failure_witness_pred (t_literal k) (FStar.GSet.singleton (l1, l2))) with
    | None -> ()
    | Some _ -> assert False
    else begin
      assert (map_group_match_item_for false k ty l == MapGroupResult FStar.GSet.empty);
      assert (None? (gset_is_empty #map_group_item FStar.GSet.empty));
      assert (map_group_match_item_cut_pre l FStar.GSet.empty == FStar.GSet.singleton (ghost_map_empty, l));
      assert (map_group_match_item_cut_failure_witness_pred (t_literal k) (FStar.GSet.singleton (ghost_map_empty, l)) ((ghost_map_empty, l), (k, v)));
      assert (Some? (maybe_indefinite_description_ghost (map_group_match_item_cut_failure_witness_pred (t_literal k) (FStar.GSet.singleton (ghost_map_empty, l)))));
      assert (map_group_match_item_for true k ty l == MapGroupCutFailure)
    end

let gset_equal_intro
  (#t: Type)
  (s1 s2: FStar.GSet.set t)
  (prf12: (x: t) -> Lemma
    (requires FStar.GSet.mem x s1)
    (ensures FStar.GSet.mem x s2)
  )
  (prf21: (x: t) -> Lemma
    (requires FStar.GSet.mem x s2)
    (ensures FStar.GSet.mem x s1)
  )
: Lemma
  (s1 == s2)
= Classical.forall_intro (Classical.move_requires prf12);
  Classical.forall_intro (Classical.move_requires prf21);
  assert (s1 `FStar.GSet.equal` s2)

let map_group_match_item_length
  (key value: typ)
  (l: cbor_map)
  l'
: Lemma
  (requires FStar.GSet.mem l' (map_group_match_item' key value l))
  (ensures ghost_map_length (snd l') < ghost_map_length l)
  [SMTPat (FStar.GSet.mem l' (map_group_match_item' key value l))]
= ()

#restart-solver
let map_group_zero_or_more_zero_or_one_eq
  (m: map_group)
: Lemma
  (map_group_zero_or_more (map_group_zero_or_one m) == map_group_zero_or_more m)
=
  assert ((ghost_map_empty #Cbor.raw_data_item #Cbor.raw_data_item  `ghost_map_union` ghost_map_empty) `ghost_map_feq` ghost_map_empty);
  map_group_equiv_intro_rec
    (map_group_zero_or_more (map_group_zero_or_one m))
    (map_group_zero_or_more m)
    (fun l prf ->
      map_group_zero_or_more_eq (map_group_zero_or_one m) l;
      map_group_zero_or_more_eq m l;
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_zero_or_one m)) (map_group_zero_or_more m)
    )
    (fun l prf l' ->
      map_group_zero_or_more_eq (map_group_zero_or_one m) l;
      map_group_zero_or_more_eq m l;
      assert (~ (map_group_zero_or_one m l == MapGroupResult FStar.GSet.empty));
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_zero_or_one m)) (map_group_zero_or_more m);
      let (l1, l2) = map_group_concat_elim (map_group_zero_or_one m) (bound_map_group l (map_group_zero_or_more m)) l l' in
      ()
    )
    (fun l prf l' ->
      map_group_zero_or_more_eq (map_group_zero_or_one m) l;
      map_group_zero_or_more_eq m l;
      assert (~ (map_group_zero_or_one m l == MapGroupResult FStar.GSet.empty));
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_zero_or_one m)) (map_group_zero_or_more m);
      match gset_is_empty (MapGroupResult?._0 (m l)) with
      | None ->
        assert (map_group_concat_witness_pred (map_group_zero_or_one m) (bound_map_group l (map_group_zero_or_more m)) l l'
          (
            (ghost_map_empty, l),
            (ghost_map_empty, l)
          )
        )
      | _ -> 
        let (l1, l2) = map_group_concat_elim m (bound_map_group l (map_group_zero_or_more m)) l l' in
        ()
    )

let apply_map_group_det_old (m: map_group) (l: cbor_map) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)
= match m l with
  | MapGroupCutFailure -> MapGroupCutFail
  | MapGroupResult s ->
  if FStar.StrongExcludedMiddle.strong_excluded_middle (s == FStar.GSet.empty)
  then MapGroupFail
  else if FStar.StrongExcludedMiddle.strong_excluded_middle (exists x . s == FStar.GSet.singleton x)
  then
    let x = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun x -> s == FStar.GSet.singleton x) in
    MapGroupDet (fst x) (snd x)
  else MapGroupNonDet

let gset_is_singleton (#t: Type) (s: FStar.GSet.set t) (x: t) : Tot prop =
  s == FStar.GSet.singleton x

let apply_map_group_det (m: map_group) (l: cbor_map) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)
= match m l with
  | MapGroupCutFailure -> MapGroupCutFail
  | MapGroupResult s ->
  begin match gset_is_empty s with
  | None -> MapGroupFail
  | _ ->
    begin match maybe_indefinite_description_ghost (gset_is_singleton s) with
    | Some x -> MapGroupDet (fst x) (snd x)
    | _ -> MapGroupNonDet
    end
  end

let apply_map_group_det_eq_old
  (m: map_group)
  (l: cbor_map)
: Lemma
  (apply_map_group_det m l == apply_map_group_det_old m l)
= ()

#restart-solver
let apply_map_group_det_eq_singleton (m: map_group) (l: cbor_map) (x : (_ & _)) : Lemma
  (requires (match m l with
  | MapGroupResult s -> s `FStar.GSet.equal` FStar.GSet.singleton x
  | _ -> False
  ))
  (ensures (apply_map_group_det m l == MapGroupDet (fst x) (snd x)))
= let MapGroupResult s = m l in
  assert (s == FStar.GSet.singleton x);
  if FStar.StrongExcludedMiddle.strong_excluded_middle (s == FStar.GSet.empty)
  then assert (x `FStar.GSet.mem` FStar.GSet.empty)
  else begin
    assert (exists x . s == FStar.GSet.singleton x);
    assert (MapGroupDet? (apply_map_group_det m l))
  end

#restart-solver
let apply_map_group_det_eq_map (m1 m2: map_group) (l: cbor_map) : Lemma
  (requires m1 l == m2 l)
  (ensures apply_map_group_det m1 l == apply_map_group_det m2 l)
= match apply_map_group_det m1 l with
  | MapGroupDet c1 l1 -> apply_map_group_det_eq_singleton m2 l (c1, l1)
  | _ -> ()

let apply_map_group_det_always_false (l: cbor_map) : Lemma
  (apply_map_group_det map_group_always_false l == MapGroupFail)
= ()

#restart-solver
let apply_map_group_det_nop (l: cbor_map) : Lemma
  (apply_map_group_det map_group_nop l == MapGroupDet ghost_map_empty l)
= ()

let apply_map_group_det_end l = ()

let apply_map_group_det_map_group_equiv
  m1 m2
= map_group_equiv_intro m1 m2
    (fun l -> ())
    (fun l l' ->
      let MapGroupDet _ s1 = apply_map_group_det m1 l in
      let (k1, l1) = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun s1 -> m1 l == MapGroupResult (FStar.GSet.singleton s1)) in
      let (k2, l2) = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun s2 -> m2 l == MapGroupResult (FStar.GSet.singleton s2)) in
      assert (l1 == l2);
      ghost_map_equiv k1 k2
    )
    (fun l l' ->
      let MapGroupDet _ s1 = apply_map_group_det m1 l in
      let (k1, l1) = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun s1 -> m1 l == MapGroupResult (FStar.GSet.singleton s1)) in
      let (k2, l2) = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun s2 -> m2 l == MapGroupResult (FStar.GSet.singleton s2)) in
      assert (l1 == l2);
      ghost_map_equiv k1 k2
    )

let apply_map_group_det_map_group_equiv' (m1 m2: map_group)
  (phi1: (l: _) -> Lemma
    (~ (MapGroupNonDet? (apply_map_group_det m1 l))
  ))
  (phi2: (l: _) -> Lemma
    (apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
: Lemma
  (ensures m1 == m2)
= Classical.forall_intro phi1;
  Classical.forall_intro phi2;
  apply_map_group_det_map_group_equiv m1 m2

let gset_singleton_inj
  (#t: Type)
  (x1 x2: t)
: Lemma
  (requires FStar.GSet.singleton x1 == FStar.GSet.singleton x2)
  (ensures x1 == x2)
= assert (x1 `FStar.GSet.mem` FStar.GSet.singleton x2)

#restart-solver
let apply_map_group_det_choice (m1 m2: map_group) (l: cbor_map)
= match apply_map_group_det m1 l with
  | MapGroupFail -> apply_map_group_det_eq_map (m1 `map_group_choice` m2) m2 l
  | _ -> apply_map_group_det_eq_map (m1 `map_group_choice` m2) m1 l

val apply_map_group_det_old_concat (m1 m2: map_group) (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) : Lemma
  (match apply_map_group_det_old m1 l with
  | MapGroupCutFail -> apply_map_group_det_old (m1 `map_group_concat` m2) l == MapGroupCutFail
  | MapGroupFail -> apply_map_group_det_old (m1 `map_group_concat` m2) l == MapGroupFail
  | MapGroupDet c1 l1 ->
    apply_map_group_det_old (m1 `map_group_concat` m2) l == begin match apply_map_group_det_old m2 l1 with
    | MapGroupDet c2 l2 -> MapGroupDet (c1 `ghost_map_union` c2) l2
    | res -> res
    end
  | _ -> True)

#push-options "--z3rlimit 32"

#restart-solver
let apply_map_group_det_old_concat (m1 m2: map_group) (l: cbor_map)
= match apply_map_group_det_old m1 l with
  | MapGroupCutFail -> ()
  | MapGroupFail ->
    assert (m1 l == MapGroupResult FStar.GSet.empty);
    assert (forall x . ~ (FStar.GSet.mem x (MapGroupResult?._0 (m1 l))));
    assert (match map_group_concat m1 m2 l with
    | MapGroupResult s -> s `FStar.GSet.equal` FStar.GSet.empty
    | _ -> False)
  | MapGroupDet c1 lr1 ->
    let l1 = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun x -> m1 l == MapGroupResult (FStar.GSet.singleton x)) in
    assert ((c1, lr1) `FStar.GSet.mem` FStar.GSet.singleton l1);
    begin match apply_map_group_det_old m2 lr1 with
    | MapGroupCutFail -> assert (map_group_concat_cut_failure_witness_pred m1 m2 l l1)
    | MapGroupFail -> assert (match map_group_concat m1 m2 l with
    | MapGroupResult s -> s `FStar.GSet.equal` FStar.GSet.empty
    | _ -> False)
    | MapGroupDet c2 lr2 ->
      let l2 = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun x -> m2 lr1 == MapGroupResult (FStar.GSet.singleton x)) in
      assert ((c2, lr2) `FStar.GSet.mem` FStar.GSet.singleton l2);
      let l0 = (ghost_map_union (fst l1) (fst l2), snd l2) in
      gset_equal_intro
        (MapGroupResult?._0 (map_group_concat m1 m2 l))
        (FStar.GSet.singleton l0)
        (fun _ -> ())
        (fun _ ->
          assert (map_group_concat_witness_pred m1 m2 l l0
            (l1, l2)
          )
        );
      assert (map_group_concat m1 m2 l == MapGroupResult (FStar.GSet.singleton l0));
      assert (fst l1 == c1);
      assert (fst l2 == c2);
      assert (snd l2 == lr2)
    | MapGroupNonDet ->
      let Some l2 = gset_is_empty (MapGroupResult?._0 (m2 lr1)) in
      let l0 = (ghost_map_union (fst l1) (fst l2), snd l2) in
      assert (map_group_concat_witness_pred m1 m2 l l0
        (l1, l2)
      );
      assert (FStar.GSet.mem l0 (MapGroupResult?._0 (map_group_concat m1 m2 l)));
      assert (~ (map_group_concat m1 m2 l == MapGroupResult FStar.GSet.empty));
      if FStar.StrongExcludedMiddle.strong_excluded_middle (exists x . map_group_concat m1 m2 l == MapGroupResult (FStar.GSet.singleton x))
      then begin
        assert (match map_group_concat m1 m2 l with
        |  MapGroupResult s -> s `FStar.GSet.equal` FStar.GSet.singleton l0
        | _ -> False);
        gset_equal_intro
          (MapGroupResult?._0 (m2 lr1))
          (FStar.GSet.singleton l2)
          (fun l2' ->
            let l0' = (ghost_map_union (fst l1) (fst l2'), snd l2') in
            assert (map_group_concat_witness_pred m1 m2 l l0'
              (l1, l2')
            );
            assert (FStar.GSet.mem l0' (MapGroupResult?._0 (map_group_concat m1 m2 l)));
            assert (l0' == l0);
            ghost_map_disjoint_mem_union' (fst l1) (fst l2') ();
            ghost_map_disjoint_mem_union' (fst l1) (fst l2) ();
            ghost_map_equiv (fst l2') (fst l2);
            assert (l2' == l2)
          )
          (fun _ -> ())
      end
      else ()
    end
  | _ -> ()

let apply_map_group_det_concat (m1 m2: map_group) (l: cbor_map) =
  apply_map_group_det_old_concat m1 m2 l

#pop-options

#restart-solver
let apply_map_group_det_match_item_for
  (cut: bool)
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: cbor_map)
= map_group_match_item_for_eq_gen cut k ty l;
  match apply_ghost_map l k with
  | Some v ->
    if ty v
    then begin
      let l1 = ghost_map_singleton k v in
      let l2 = ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) l in
      ghost_map_equiv
        (l `ghost_map_sub` l1)
        l2;
      let MapGroupResult s = map_group_match_item_for cut k ty l in
      assert (gset_is_singleton s (l1, l2));
      let Some l' = maybe_indefinite_description_ghost (gset_is_singleton s) in
      gset_singleton_inj l' (l1, l2)
    end
    else ()
  | _ -> ()

// FIXME: swap `notp f` with `f`?
let map_group_filter_item
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> GTot bool)
  (l: cbor_map)
: GTot (cbor_map & cbor_map)
=
  ghost_map_filter (notp_g f) l,
  ghost_map_filter f l

let map_group_item_post_filter
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> GTot bool)
  (l: cbor_map)
: Lemma
  (map_group_item_post l (map_group_filter_item f l))
  [SMTPat (map_group_filter_item f l)]
= ghost_map_split f l

let map_group_filter
  f
= FE.on_dom_g cbor_map #map_group_codom (fun l ->
    MapGroupResult (FStar.GSet.singleton (map_group_filter_item f l))
  )

let apply_map_group_det_filter
  f l
= apply_map_group_det_eq_singleton (map_group_filter f) l (map_group_filter_item f l)

let orp_g (#t: Type) (p1 p2: t -> GTot bool) (x: t) : GTot bool =
  p1 x || p2 x

let ghost_map_filter_union
  (#key #value: Type)
  (p1 p2: (key & value) -> GTot bool)
  (m: ghost_map key value)
: Lemma
  (ghost_map_filter p1 m `ghost_map_union`
    ghost_map_filter p2 m ==
    ghost_map_filter (p1 `orp_g` p2) m
  )
= ghost_map_ext
    (ghost_map_filter p1 m `ghost_map_union`
      ghost_map_filter p2 m)
    (ghost_map_filter (p1 `orp_g` p2) m)

let ghost_map_filter_not_filter_not_strong
  (p1 p2: (Cbor.raw_data_item & Cbor.raw_data_item) -> GTot bool)
  (l: cbor_map)
: Lemma
  (ghost_map_filter (notp_g p1) l `ghost_map_union`
    ghost_map_filter (notp_g p2) (ghost_map_filter p1 l) ==
    ghost_map_filter (notp_g (p1 `andp_g` p2)) l
  )
= ghost_map_filter_filter p1 (notp_g p2) l;
  ghost_map_filter_union (notp_g p1) (p1 `andp_g` notp_g p2) l;
  ghost_map_filter_ext
    (notp_g p1 `orp_g` (p1 `andp_g` notp_g p2))
    (notp_g (p1 `andp_g` p2))
    l

#restart-solver
let map_group_filter_filter
  p1 p2
=
  apply_map_group_det_map_group_equiv'
    (map_group_filter p1 `map_group_concat` map_group_filter p2)
    (map_group_filter (andp_g p1 p2))
    (fun l -> map_group_is_det_concat (map_group_filter p1) (map_group_filter p2))
    (fun l -> 
      ghost_map_filter_filter p1 p2 l;
      ghost_map_filter_not_filter_not_strong p1 p2 l
    )

#restart-solver
let map_group_zero_or_one_match_item_filter_matched
  (key value: typ)
  (p: (Cbor.raw_data_item & Cbor.raw_data_item) -> GTot bool)
  (l: cbor_map)
  kv l'
: Lemma
  (requires (
    (forall x . p x ==> notp_g (matches_map_group_entry key value) x) /\
    map_group_item_post l (ghost_map_singleton (fst kv) (snd kv), l') /\
    matches_map_group_entry key value kv
  ))
  (ensures (
    ghost_map_singleton (fst kv) (snd kv) `ghost_map_union` ghost_map_filter (notp_g p) l' ==
      ghost_map_filter (notp_g p) l /\
    ghost_map_filter p l' ==
      ghost_map_filter p l
  ))
= let s = ghost_map_singleton (fst kv) (snd kv) in
  ghost_map_disjoint_union_filter (notp_g p) s l';
  ghost_map_equiv s (ghost_map_filter (notp_g p) s);
  ghost_map_disjoint_union_filter p s l';
  ghost_map_equiv ghost_map_empty (ghost_map_filter p s)

#push-options "--z3rlimit 128"

#restart-solver
let map_group_zero_or_one_match_item_filter
  key value p
= map_group_equiv_intro
    (map_group_zero_or_one (map_group_match_item false key value) `map_group_concat` map_group_filter p)
    (map_group_filter p)
    (fun _ -> ())
    (fun l l' ->
      let MapGroupResult s = map_group_match_item false key value l in
      match gset_is_empty s with
      | None -> map_group_concat_nop_l (map_group_filter p)
      | Some _ ->
        let (l1, _) = map_group_concat_elim (map_group_zero_or_one (map_group_match_item false key value)) (map_group_filter p) l l' in
        let kv = map_group_match_item_elim key value l l1 in
        assert (fst l1 == ghost_map_singleton (fst kv) (snd kv));
        assert (map_group_filter p (snd l1) == MapGroupResult (FStar.GSet.singleton (map_group_filter_item p (snd l1))));
        map_group_zero_or_one_match_item_filter_matched key value p l kv (snd l1);
        assert (snd l' == ghost_map_filter p l)
    )
    (fun l l' ->
      let MapGroupResult s = map_group_match_item false key value l in
      match gset_is_empty s with
      | None -> map_group_concat_nop_l (map_group_filter p)
      | Some l1 ->
        let kv = map_group_match_item_elim key value l l1 in
        map_group_zero_or_one_match_item_filter_matched key value p l kv (snd l1);
        assert (map_group_concat_witness_pred (map_group_zero_or_one (map_group_match_item false key value)) (map_group_filter p) l l' (l1, (ghost_map_filter (notp_g p) (snd l1), ghost_map_filter p (snd l1))))
    )

#restart-solver
let map_group_concat_bound_map_group_elim
  (m1 m2: map_group)
  (l1 l2: cbor_map)
  (prf: (l': _) -> Lemma
    (requires (match m1 l1 with
    | MapGroupResult s -> FStar.GSet.mem l' s
    | _ -> False
    ))
    (ensures (ghost_map_length (snd l') < ghost_map_length l2))
  )
: Lemma
  ((m1 `map_group_concat` bound_map_group l2 m2) l1 ==
    (m1 `map_group_concat` m2) l1)
= Classical.forall_intro (Classical.move_requires prf);
  match m1 l1 with
  | MapGroupCutFailure -> ()
  | MapGroupResult s ->
    begin match (m1 `map_group_concat` bound_map_group l2 m2) l1, (m1 `map_group_concat` m2) l1 with
    | MapGroupResult s, MapGroupResult s' -> assert (s `FStar.GSet.equal` s')
    | _ -> ()
    end

#pop-options

let map_group_concat_eq_l
  (m1 m1' m2: map_group)
  (l: cbor_map)
: Lemma
  (requires (
    m1 l == m1' l
  ))
  (ensures (
    (m1 `map_group_concat` m2) l ==
      (m1' `map_group_concat` m2) l
  ))
= match (m1 `map_group_concat` m2) l, (m1' `map_group_concat` m2) l with
  | MapGroupResult s, MapGroupResult s' -> assert (s `FStar.GSet.equal` s')
  | _ -> ()

#restart-solver
let map_group_zero_or_one_bound_match_item_filter
  (key value: typ)
  (l: cbor_map)
: Lemma
  (ensures (
    let p = notp_g (matches_map_group_entry key value) in
    (map_group_zero_or_one (map_group_match_item false key value) `map_group_concat` bound_map_group l (map_group_filter p)) l == map_group_filter p l
  ))
= let p = notp_g (matches_map_group_entry key value) in
  map_group_match_item_alt_correct key value l;
  match maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value l) with
  | None ->
    map_group_concat_eq_l (map_group_zero_or_one (map_group_match_item false key value)) map_group_nop (bound_map_group l (map_group_filter p)) l;
    map_group_concat_nop_l (bound_map_group l (map_group_filter p));
    ghost_map_equiv
      (ghost_map_filter (notp_g p) l)
      ghost_map_empty;
    ghost_map_equiv
      (ghost_map_filter p l)
      l
  | Some _ ->
    assert (Some? (gset_is_empty (map_group_match_item' key value l)));
    map_group_concat_bound_map_group_elim
      (map_group_zero_or_one (map_group_match_item false key value))
      (map_group_filter p)
      l l
      (fun _ -> ());
    map_group_zero_or_one_match_item_filter key value p

#restart-solver
let map_group_zero_or_one_map_group_match_item_no_cut_nonempty
  (key value: typ)
  (l: cbor_map)
: Lemma
  (~ (map_group_zero_or_one (map_group_match_item false key value) l == MapGroupResult FStar.GSet.empty))
= let MapGroupResult s = map_group_match_item false key value l in
  let MapGroupResult s' = map_group_zero_or_one (map_group_match_item false key value) l in
  match gset_is_empty s with
  | None -> assert (FStar.GSet.mem (ghost_map_empty, l) s')
  | _ -> ()

#push-options "--z3rlimit 16"

#restart-solver
let map_group_zero_or_more_match_item_filter (key value: typ) : Lemma
  (ensures
    map_group_zero_or_more (map_group_match_item false key value) == map_group_filter (notp_g (matches_map_group_entry key value))
  )
= let f = (notp_g (matches_map_group_entry key value)) in
  map_group_equiv_intro_equiv_rec
    (map_group_zero_or_more (map_group_match_item false key value))
    (map_group_filter (notp_g (matches_map_group_entry key value)))
    (fun l prf ->
      map_group_zero_or_more_zero_or_one_eq (map_group_match_item false key value);
      map_group_zero_or_more_eq (map_group_zero_or_one (map_group_match_item false key value)) l;
      map_group_zero_or_one_map_group_match_item_no_cut_nonempty key value l;
      Classical.forall_intro prf    
    )
    (fun l prf l' ->
      map_group_zero_or_more_zero_or_one_eq (map_group_match_item false key value);
      map_group_zero_or_more_eq (map_group_zero_or_one (map_group_match_item false key value)) l;
      map_group_zero_or_one_map_group_match_item_no_cut_nonempty key value l;
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_match_item false key value)) (map_group_filter f);
      map_group_zero_or_one_bound_match_item_filter key value l
    )

#pop-options

let eq_trans
  (#t: Type)
  (x1 x2 x3: t)
  (sq12: squash (x1 == x2))
  (sq23: squash (x2 == x3))
: Tot (squash (x1 == x3))
= ()

let apply_map_group_det_ext
  (m1 m2: map_group)
  (l: cbor_map)
: Lemma
  (requires (m1 l == m2 l))
  (ensures (apply_map_group_det m1 l == apply_map_group_det m2 l))
= ()

#restart-solver
let rec map_group_zero_or_more_det
  (g: det_map_group)
  (l: cbor_map)
: Lemma
  (ensures (~ (MapGroupNonDet? (apply_map_group_det (map_group_zero_or_more g) l))))
  (decreases (ghost_map_length l))
= map_group_zero_or_more_eq g l;
  match apply_map_group_det g l with
  | MapGroupDet consumed rem ->
    ghost_map_length_is_empty consumed;
    if ghost_map_length consumed = 0
    then begin
      assert (rem == l);
      map_group_concat_eq_r g (bound_map_group l (map_group_zero_or_more g)) map_group_nop l (fun l' -> ());
      assert (map_group_zero_or_more g l == map_group_concat g map_group_nop l);
      map_group_concat_nop_r g;
      assert (map_group_zero_or_more g l == g l);
      apply_map_group_det_ext (map_group_zero_or_more g) g l
    end
    else begin
      assert (ghost_map_length rem < ghost_map_length l);
      map_group_concat_eq_r g (bound_map_group l (map_group_zero_or_more g)) (map_group_zero_or_more g) l (fun l' -> ());
      apply_map_group_det_ext (map_group_zero_or_more g) (map_group_concat g (map_group_zero_or_more g)) l;
      map_group_zero_or_more_det g rem
    end
  | _ -> ()

#restart-solver
let map_group_zero_or_more_map_group_match_item_for
  (cut: bool)
  (key: Cbor.raw_data_item)
  (value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item_for cut key value) ==
    map_group_zero_or_one (map_group_match_item_for cut key value)
  )
= let g = map_group_match_item_for cut key value in
  apply_map_group_det_map_group_equiv0
    (map_group_zero_or_more g)
    (map_group_zero_or_one g)
    (fun l -> map_group_zero_or_more_det g l)
    (fun l ->
      map_group_zero_or_more_eq g l;
      match apply_map_group_det g l with
      | MapGroupCutFail -> ()
      | MapGroupFail -> ()
      | MapGroupDet consumed rem ->
        assert (ghost_map_length rem < ghost_map_length l);
        map_group_concat_eq_r g (bound_map_group l (map_group_zero_or_more g)) map_group_nop l (fun l' ->
          map_group_zero_or_more_eq g (snd l');
          map_group_match_item_for_eq_gen cut key value (snd l');
          assert (apply_ghost_map (snd l') key == None)
        );
        assert (map_group_zero_or_more g l == (g `map_group_concat` map_group_nop) l);
        map_group_concat_nop_r g;
        assert (map_group_zero_or_more g l == g l);
        apply_map_group_det_ext (map_group_zero_or_more g) g l
    )

let map_group_fail_shorten_intro
  (g: map_group)
  (prf: (m1: _) -> (m2: _) -> Lemma
    (requires (ghost_map_disjoint m1 m2 /\
      MapGroupFail? (apply_map_group_det g (m1 `ghost_map_union` m2))
    ))
    (ensures MapGroupFail? (apply_map_group_det g m1))
  )
: Lemma
  (map_group_fail_shorten g)
= Classical.forall_intro_2 (fun m1 -> Classical.move_requires (prf m1))

#restart-solver
let map_group_fail_shorten_match_item
  (cut: bool)
  (key value: typ)
: Lemma
  (map_group_fail_shorten (map_group_match_item cut key value))
= map_group_fail_shorten_intro (map_group_match_item cut key value) (fun m1 m2 ->
    map_group_match_item_alt_correct key value (m1 `ghost_map_union` m2);
    map_group_match_item_alt_correct key value m1;
    let s12 = map_group_match_item_alt key value (m1 `ghost_map_union` m2) in
    match maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value (m1 `ghost_map_union` m2)) with
    | None ->
      assert (forall x . map_group_match_item_alt_pred key value m1 x ==> map_group_match_item_alt_pred key value (m1 `ghost_map_union` m2) x);
      assert (None? (maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value m1)));
      ghost_map_disjoint_mem_union' m1 m2 ();
      assert (forall x . map_group_match_item_cut_failure_witness_pred key (FStar.GSet.singleton (ghost_map_empty, m1)) x ==> begin
        let (_, entry) = x in
        map_group_match_item_cut_failure_witness_pred key (FStar.GSet.singleton (ghost_map_empty, m1 `ghost_map_union` m2)) ((ghost_map_empty, m1 `ghost_map_union` m2), entry)
      end);
      ()
    | Some kv ->
      let s = ghost_map_singleton (fst kv) (snd kv) in
      assert (FStar.GSet.mem (s, (m1 `ghost_map_union` m2) `ghost_map_sub` s) s12)
  )

#restart-solver
let rec map_group_zero_or_more_choice'
  (g1 g2: map_group)
  (l: cbor_map)
: Lemma
  (requires (
    map_group_fail_shorten g1 /\
    map_group_is_productive g1 /\
    map_group_is_productive g2
  ))
  (ensures (
    map_group_zero_or_more (g1 `map_group_choice` g2) l == (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2) l
  ))
  (decreases (ghost_map_length l))
= let lhs = map_group_zero_or_more (g1 `map_group_choice` g2) l in
  let rhs = (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2) l in
  map_group_zero_or_more_eq (g1 `map_group_choice` g2) l;
  map_group_zero_or_more_eq g1 l;
  match g1 l with
  | MapGroupCutFailure -> ()
  | MapGroupResult s1 ->
    begin match gset_is_empty s1 with
    | None ->
      map_group_concat_eq_l
        (map_group_zero_or_more g1)
        map_group_nop
        (map_group_zero_or_more g2)
        l;
      assert (rhs == (map_group_nop `map_group_concat` map_group_zero_or_more g2) l);
      map_group_concat_nop_l (map_group_zero_or_more g2);
      assert (rhs == (map_group_zero_or_more g2) l);
      map_group_zero_or_more_eq g2 l;
      begin match g2 l with
      | MapGroupCutFailure -> ()
      | MapGroupResult s2 ->
        begin match gset_is_empty s2 with
        | None ->
          assert (lhs == map_group_nop l);
          assert (rhs == map_group_nop l)
        | Some _ ->
          map_group_concat_eq_l
            (g1 `map_group_choice` g2)
            g2
            (bound_map_group l (map_group_zero_or_more (g1 `map_group_choice` g2)))
            l;
          bound_map_group_ext' l (map_group_zero_or_more (g1 `map_group_choice` g2)) (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2) (fun l' -> map_group_zero_or_more_choice' g1 g2 l');
          map_group_is_productive_concat_bound l g2 l (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2);
          map_group_is_productive_concat_bound l g2 l (map_group_zero_or_more g2);
          map_group_concat_eq_r
            g2
            (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2)
            (map_group_zero_or_more g2)
            l
            (fun l' ->
              map_group_zero_or_more_eq g1 (snd l');
              map_group_concat_eq_l
                (map_group_zero_or_more g1)
                map_group_nop
                (map_group_zero_or_more g2)
                (snd l');
              ()
            );
          ()
        end
      end
    | _ ->
      map_group_concat_eq_l
        (g1 `map_group_choice` g2)
        g1
        (bound_map_group l (map_group_zero_or_more (g1 `map_group_choice` g2)))
        l;
      bound_map_group_ext' l (map_group_zero_or_more (g1 `map_group_choice` g2)) (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2) (fun l' -> map_group_zero_or_more_choice' g1 g2 l');
      map_group_is_productive_concat_bound l g1 l (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2);
      assert (lhs == (g1 `map_group_concat` (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2)) l);
      map_group_concat_eq_l
        (map_group_zero_or_more g1)
        (g1 `map_group_concat` bound_map_group l (map_group_zero_or_more g1))
        (map_group_zero_or_more g2)
        l;
      map_group_is_productive_concat_bound l g1 l (map_group_zero_or_more g1);
      map_group_concat_eq_l
        (g1 `map_group_concat` bound_map_group l (map_group_zero_or_more g1))
        (g1 `map_group_concat` map_group_zero_or_more g1)
        (map_group_zero_or_more g2)
        l;
      map_group_concat_assoc g1 (map_group_zero_or_more g1) (map_group_zero_or_more g2);
      assert (rhs == (g1 `map_group_concat` (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2)) l)
    end    

let map_group_zero_or_more_choice
  (g1 g2: map_group)
: Lemma
  (requires (
    map_group_fail_shorten g1 /\
    map_group_is_productive g1 /\
    map_group_is_productive g2
  ))
  (ensures (
    map_group_zero_or_more (g1 `map_group_choice` g2) == map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2
  ))
= Classical.forall_intro (Classical.move_requires (map_group_zero_or_more_choice' g1 g2));
  assert (map_group_zero_or_more (g1 `map_group_choice` g2) `FE.feq_g` (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2)
  )

let map_group_zero_or_one_choice
  (g1 g2: map_group)
: Lemma
  (map_group_zero_or_one (g1 `map_group_choice` g2) == g1 `map_group_choice` map_group_zero_or_one g2)
= map_group_choice_assoc g1 g2 map_group_nop

let matches_map_group (g: map_group) (l: list (Cbor.raw_data_item & Cbor.raw_data_item)) : GTot bool =
  let m = ghost_map_of_list l in
  MapGroupResult? (g m) &&
  FStar.StrongExcludedMiddle.strong_excluded_middle (exists gm .
    FStar.GSet.mem (gm, ghost_map_empty) (MapGroupResult?._0 (g m))
  )

let matches_map_group_det (g: map_group) m
= ()

let t_map g = fun x ->
  match x with
  | Cbor.Map m ->
    FStar.StrongExcludedMiddle.strong_excluded_middle (List.Tot.no_repeats_p (List.Tot.map fst m)) &&
    matches_map_group g m
  | _ -> false

let t_map_eq
  g x
= ()

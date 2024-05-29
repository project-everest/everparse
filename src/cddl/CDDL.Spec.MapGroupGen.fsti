module CDDL.Spec.MapGroupGen
include CDDL.Spec.MapGroupGen.Base
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

let ghost_map_disjoint_from_footprint
  (m: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
  (f: typ)
: Tot prop
= forall x . ghost_map_mem x m ==> ~ (f (fst x))

let map_group_footprint
  (g: map_group)
  (f: typ)
: Tot prop
= forall m m' . (ghost_map_disjoint m m' /\ ghost_map_disjoint_from_footprint m' f) ==>
  begin match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
  | MapGroupCutFail, MapGroupCutFail
  | MapGroupFail, MapGroupFail -> True
  | MapGroupDet _ r, MapGroupDet _ r' -> r' == r `ghost_map_union` m'
  | _ -> False
  end

let map_group_footprint_equiv
  (g: map_group)
  (f1 f2: typ)
: Lemma
  (requires
    map_group_footprint g f1 /\
    typ_equiv f1 f2
  )
  (ensures map_group_footprint g f2)
= ()

#restart-solver
let map_group_footprint_elim
  (g: map_group)
  (f: typ)
  (m m' : ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires
    map_group_footprint g f /\
    ghost_map_disjoint m m' /\
    ghost_map_disjoint_from_footprint m' f
  )
  (ensures
  begin match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
  | MapGroupCutFail, MapGroupCutFail
  | MapGroupFail, MapGroupFail -> True
  | MapGroupDet _ r, MapGroupDet _ r' -> r' == r `ghost_map_union` m'
  | _ -> False
  end
  )
= ()

#restart-solver
let map_group_footprint_intro
  (g: map_group)
  (f: typ)
  (prf: (m: _) -> (m' : ghost_map Cbor.raw_data_item Cbor.raw_data_item) ->
    Lemma
    (requires
      ghost_map_disjoint m m' /\
      ghost_map_disjoint_from_footprint m' f
    )
    (ensures
    begin match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
    | MapGroupCutFail, MapGroupCutFail
    | MapGroupFail, MapGroupFail -> True
    | MapGroupDet _ r, MapGroupDet _ r' -> r' == r `ghost_map_union` m'
    | _ -> False
    end
    )
  )
: Lemma
  (map_group_footprint g f)
= Classical.forall_intro_2 (fun m -> Classical.move_requires (prf m))

#restart-solver
let map_group_footprint_consumed
  (g: map_group)
  (f: typ)
  (m m': _)
: Lemma
  (requires
    map_group_footprint g f /\
    ghost_map_disjoint m m' /\
    ghost_map_disjoint_from_footprint m' f /\
    (MapGroupDet? (apply_map_group_det g m) \/ MapGroupDet? (apply_map_group_det g (m `ghost_map_union` m')))
  )
  (ensures (
    match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
    | MapGroupDet c _, MapGroupDet c' _ -> c == c'
    | _ -> False
  ))
  [SMTPat (map_group_footprint g f); SMTPat (apply_map_group_det g (m `ghost_map_union` m'))]
= let MapGroupDet c r = apply_map_group_det g m in
  let MapGroupDet c' r' = apply_map_group_det g (m `ghost_map_union` m') in
  ghost_map_union_assoc c r m';
  ghost_map_disjoint_union_simpl_r c c' r'

#restart-solver
let map_group_footprint_is_consumed
  (g: map_group)
  (f: typ)
  (m: _)
: Lemma
  (requires
    map_group_footprint g f
  )
  (ensures (
    match apply_map_group_det g m, apply_map_group_det g (ghost_map_filter (matches_map_group_entry f any) m) with
    | MapGroupDet _ _, MapGroupDet _ _
    | MapGroupFail, MapGroupFail
    | MapGroupCutFail, MapGroupCutFail -> True
    | _ -> False
  ))
= ghost_map_split (matches_map_group_entry f any) m

#restart-solver
let map_group_footprint_is_consumed_ghost_map_of_list
  (g: map_group)
  (f: typ)
  (m: _)
: Lemma
  (requires
    map_group_footprint g f /\
    List.Tot.no_repeats_p (List.Tot.map fst m)
  )
  (ensures (
    forall (f': _ -> bool) .
    (forall x . f' x == matches_map_group_entry f any x) ==>
    begin match apply_map_group_det g (ghost_map_of_list m), apply_map_group_det g (ghost_map_of_list (List.Tot.filter f' m)) with
    | MapGroupDet _ _, MapGroupDet _ _
    | MapGroupFail, MapGroupFail
    | MapGroupCutFail, MapGroupCutFail -> True
    | _ -> False
    end
  ))
= let prf
      (f': _ -> bool)
  : Lemma
    (requires (forall x . f' x == matches_map_group_entry f any x))
    (ensures 
      begin match apply_map_group_det g (ghost_map_of_list m), apply_map_group_det g (ghost_map_of_list (List.Tot.filter f' m)) with
      | MapGroupDet _ _, MapGroupDet _ _
      | MapGroupFail, MapGroupFail
      | MapGroupCutFail, MapGroupCutFail -> True
      | _ -> False
      end
    )
  = ghost_map_equiv
      (ghost_map_filter f' (ghost_map_of_list m))
      (ghost_map_filter (matches_map_group_entry f any) (ghost_map_of_list m));
    map_group_footprint_is_consumed g f (ghost_map_of_list m)
  in
  Classical.forall_intro (Classical.move_requires prf)

let map_group_footprint_consumed_disjoint
  (g: map_group)
  (f f': typ)
  (m: _)
: Lemma
  (requires
    map_group_footprint g f /\
    f `typ_disjoint` f' /\
    MapGroupDet? (apply_map_group_det g m)
  )
  (ensures (
    match apply_map_group_det g m with
    | MapGroupDet c _ ->
      ghost_map_disjoint_from_footprint c f'
    | _ -> False
  ))
= ghost_map_split (matches_map_group_entry f any) m;
  map_group_footprint_consumed g f (ghost_map_filter (matches_map_group_entry f any) m) (ghost_map_filter (notp_g (matches_map_group_entry f any)) m)

#restart-solver
let map_group_footprint_concat
  (g1 g2: map_group)
  (f1 f2: typ)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2
  ))
  (ensures (
    map_group_footprint (map_group_concat g1 g2) (t_choice f1 f2)
  ))
= ()

#restart-solver
let map_group_footprint_choice
  (g1 g2: map_group)
  (f1 f2: typ)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2
  ))
  (ensures (
    map_group_footprint (map_group_choice g1 g2) (t_choice f1 f2)
  ))
= ()

#restart-solver
let map_group_footprint_zero_or_one
  (g1: map_group)
  (f1: typ)
: Lemma
  (requires (
    map_group_footprint g1 f1
  ))
  (ensures (
    map_group_footprint (map_group_zero_or_one g1) f1
  ))
= ()

#restart-solver
let map_group_footprint_consumes_all
  (g1: map_group)
  (f1: typ)
  (m1: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 ghost_map_empty
  ))
  (ensures (
    ghost_map_filter (matches_map_group_entry f1 any) m1 == m1 /\
    ghost_map_filter (notp_g (matches_map_group_entry f1 any)) m1 == ghost_map_empty
  ))
= let phi1 = matches_map_group_entry f1 any in
  ghost_map_split phi1 m1;
  map_group_footprint_elim g1 f1 (ghost_map_filter phi1 m1) (ghost_map_filter (notp_g phi1) m1); 
  map_group_footprint_consumed g1 f1 (ghost_map_filter phi1 m1) (ghost_map_filter (notp_g phi1) m1);
  let MapGroupDet c1 r1 = apply_map_group_det g1 (ghost_map_filter phi1 m1) in
  let MapGroupDet c' r' = apply_map_group_det g1 (ghost_map_filter phi1 m1 `ghost_map_union` ghost_map_filter (notp_g phi1) m1) in
  assert (ghost_map_empty == r1 `ghost_map_union` ghost_map_filter (notp_g phi1) m1);
  ghost_map_ext ghost_map_empty (ghost_map_filter (notp_g phi1) m1);
  ()

#restart-solver
let map_group_footprint_concat_consumes_all
  (g1 g2: map_group)
  (f1 f2: typ)
  (m1 m2: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 ghost_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 ghost_map_empty /\
    typ_disjoint f1 f2
  ))
  (ensures (
    m1 `ghost_map_disjoint` m2 /\
    apply_map_group_det (g1 `map_group_concat` g2) (m1 `ghost_map_union` m2) == MapGroupDet (m1 `ghost_map_union` m2) ghost_map_empty
  ))
= map_group_footprint_consumes_all g1 f1 m1;
  map_group_footprint_consumes_all g2 f2 m2;
  ()

#restart-solver
let map_group_footprint_match_item_for
  (cut: bool)
  (key: Cbor.raw_data_item)
  (value: typ)
: Lemma
  (ensures (
    map_group_footprint (map_group_match_item_for cut key value) (t_literal key)
  ))
  [SMTPat (map_group_footprint (map_group_match_item_for cut key value))]
= let g = map_group_match_item_for cut key value in
  map_group_footprint_intro
    g
    (t_literal key)
    (fun m m' ->
       assert (~ (ghost_map_defined key m'));
       match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
       | MapGroupDet _ r, MapGroupDet _ r' ->
         ghost_map_ext r' (r `ghost_map_union` m')
       | _ -> ()
    )

#restart-solver
let map_group_footprint_filter
  (phi: _ -> GTot bool)
  (f: typ)
: Lemma
  (requires
    forall (x: (Cbor.raw_data_item & Cbor.raw_data_item)) . notp_g phi x ==> f (fst x)
  )
  (ensures (
    map_group_footprint (map_group_filter phi) f
  ))
  [SMTPat (map_group_footprint (map_group_filter phi) f)]
= let g = map_group_filter phi in
  map_group_footprint_intro
    g
    f
    (fun m m' ->
      let MapGroupDet _ r = apply_map_group_det g m in
      let MapGroupDet _ r' = apply_map_group_det g (m `ghost_map_union` m') in
      ghost_map_disjoint_union_filter phi m m';
      ghost_map_filter_for_all phi m';
      assert (r' == r `ghost_map_union` m')
    )

let map_group_footprint_zero_or_more_match_item
  (key value: typ)
: Lemma
  (map_group_footprint (map_group_zero_or_more (map_group_match_item false key value)) key)
  [SMTPat (map_group_footprint (map_group_zero_or_more (map_group_match_item false key value)))]
= ()

let restrict_map_group
  (g g': map_group)
: Tot prop
= forall m .
  begin match apply_map_group_det g m, apply_map_group_det g' m with
  | MapGroupCutFail, MapGroupCutFail
  | MapGroupFail, MapGroupFail -> True
  | MapGroupDet c r, MapGroupDet c' r' -> (forall x . ghost_map_mem x c' ==> ghost_map_mem x c)
  | _ -> False
  end

let restrict_map_group_intro
  (g g': map_group)
  (prf1: (m: _) -> Lemma
    begin match apply_map_group_det g m, apply_map_group_det g' m with
    | MapGroupCutFail, MapGroupCutFail
    | MapGroupFail, MapGroupFail -> True
    | MapGroupDet c r, MapGroupDet c' r' -> ghost_map_included c' c
    | _ -> False
    end
  )
: Lemma
  (restrict_map_group g g')
= Classical.forall_intro prf1

let restrict_map_group_refl
  (g: det_map_group)
: Lemma
  (restrict_map_group g g)
  [SMTPat (restrict_map_group g g)]
= ()

let restrict_map_group_match_item_for
  (cut: bool)
  (key: Cbor.raw_data_item)
  (value: typ)
: Lemma
  (restrict_map_group (map_group_match_item_for cut key value) (map_group_match_item_for cut key value))
= ()

let restrict_map_group_filter
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> GTot bool)
: Lemma
  (restrict_map_group (map_group_filter f) map_group_nop)
  [SMTPat (restrict_map_group (map_group_filter f) map_group_nop)]
= ()

let restrict_map_group_zero_or_more_match_item
  (key value: typ)
: Lemma
  (restrict_map_group (map_group_zero_or_more (map_group_match_item false key value)) map_group_nop)
  [SMTPat (restrict_map_group (map_group_zero_or_more (map_group_match_item false key value)))]
= ()

let restrict_map_group_zero_or_one_no_cut
  (g: det_map_group)
: Lemma
  (requires (forall m . ~ (MapGroupCutFail? (apply_map_group_det g m))))
  (ensures (restrict_map_group (map_group_zero_or_one g) map_group_nop))
  [SMTPat (restrict_map_group (map_group_zero_or_one g) map_group_nop)]
= ()

let restrict_map_group_choice
  (g1 g1' g2 g2': map_group)
: Lemma
  (requires (
    restrict_map_group g1 g1' /\
    restrict_map_group g2 g2'
  ))
  (ensures (
    restrict_map_group (g1 `map_group_choice` g2) (g1' `map_group_choice` g2')
  ))
  [SMTPat (restrict_map_group (g1 `map_group_choice` g2) (g1' `map_group_choice` g2'))]
= ()

let restrict_map_group_zero_or_one
  (g1 g1': map_group)
: Lemma
  (requires (
    restrict_map_group g1 g1'
  ))
  (ensures (
    restrict_map_group (map_group_zero_or_one g1) (map_group_zero_or_one g1')
  ))
  [SMTPat (restrict_map_group (map_group_zero_or_one g1) (map_group_zero_or_one g1'))]
= ()

let map_group_footprint_weaken
  (g: map_group)
  (f f': typ)
: Lemma
  (requires
    map_group_footprint g f /\
    f `typ_included` f'
  )
  (ensures
    map_group_footprint g f'
  )
= ()

val restrict_map_group_concat
  (g1: map_group)
  (f1: typ)
  (g1': map_group)
  (g2: map_group)
  (g2': map_group)
  (f2': typ)
: Lemma
  (requires (
    restrict_map_group g1 g1' /\
    map_group_footprint g1 f1 /\
    map_group_footprint g1' f1 /\
    restrict_map_group g2 g2' /\
    map_group_footprint g2' f2' /\
    typ_disjoint f1 f2'
  ))
  (ensures (
    restrict_map_group (g1 `map_group_concat` g2) (g1' `map_group_concat` g2')
  ))

let map_group_choice_compatible
  (left right: map_group)
: Tot prop
= forall x . match apply_map_group_det right x with
  | MapGroupDet _ rem -> rem == ghost_map_empty ==> MapGroupFail? (apply_map_group_det left x)
  | _ -> True

#restart-solver
let map_group_choice_compatible_intro
  (left right: map_group)
  (prf: (x: _) -> Lemma
    (requires begin match apply_map_group_det right x with
     | MapGroupDet _ rem -> rem == ghost_map_empty
     | _ -> False
    end)
    (ensures MapGroupFail? (apply_map_group_det left x))
  )
: Lemma
  (map_group_choice_compatible left right)
= Classical.forall_intro (Classical.move_requires prf)

#restart-solver
val map_group_choice_compatible_match_item_for
  (cut: bool)
  (key: Cbor.raw_data_item)
  (value: typ)
  (right: map_group)
  (fp: typ)
: Lemma
  (requires (
    t_literal key `typ_disjoint` fp /\
    map_group_footprint right fp
  ))
  (ensures (
    map_group_choice_compatible (map_group_match_item_for cut key value) right
  ))

let map_group_choice_compatible_no_cut
  (left right: map_group)
: Tot prop
= forall x . match apply_map_group_det right x with
  | MapGroupDet _ rem -> rem == ghost_map_empty ==> ~ (MapGroupCutFail? (apply_map_group_det left x))
  | _ -> True

let map_group_choice_compatible_implies_no_cut
  (left right: map_group)
: Lemma
  (map_group_choice_compatible left right ==> map_group_choice_compatible_no_cut left right)
= ()

#restart-solver
let map_group_fail_concat_intro
  (g1: det_map_group)
  (f1: typ)
  (g2: det_map_group)
  (f2: typ)
  (x: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\ (
    MapGroupFail? (apply_map_group_det g1 x) \/ (
    (~ (MapGroupCutFail? (apply_map_group_det g1 x))) /\
    MapGroupFail? (apply_map_group_det g2 x)
  ))))
  (ensures (
    MapGroupFail? (apply_map_group_det (g1 `map_group_concat` g2) x)
  ))
= if MapGroupFail? (apply_map_group_det g1 x)
  then ()
  else begin
    let MapGroupDet c1 r1 = apply_map_group_det g1 x in
    map_group_footprint_consumed_disjoint g1 f1 f2 x;
    ghost_map_disjoint_union_comm c1 r1
  end

let map_group_consumes_all
  (g: map_group)
  (x: ghost_map _ _)
: Tot prop
= match apply_map_group_det g x with
  | MapGroupDet _ r -> r == ghost_map_empty
  | _ -> False

let map_group_choice_compatible_concat_left
  (g1: det_map_group)
  (f1: typ)
  (g2: det_map_group)
  (f2: typ)
  (g: map_group)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\
    (map_group_choice_compatible g1 g \/ (
      map_group_choice_compatible_no_cut g1 g /\
      map_group_choice_compatible g2 g)
    )
  ))
  (ensures (
    map_group_choice_compatible (g1 `map_group_concat` g2) g
  ))
= Classical.forall_intro (Classical.move_requires (map_group_fail_concat_intro g1 f1 g2 f2))

#restart-solver
let map_group_concat_no_cut_intro
  (g1: det_map_group)
  (f1: typ)
  (g2: det_map_group)
  (f2: typ)
  (x: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\ (
    (~ (MapGroupCutFail? (apply_map_group_det g1 x))) /\
    (~ (MapGroupCutFail? (apply_map_group_det g2 x)))
  )))
  (ensures (
    (~ (MapGroupCutFail? (apply_map_group_det (g1 `map_group_concat` g2) x)))
  ))
= if MapGroupFail? (apply_map_group_det g1 x)
  then ()
  else begin
    let MapGroupDet c1 r1 = apply_map_group_det g1 x in
    map_group_footprint_consumed_disjoint g1 f1 f2 x;
    ghost_map_disjoint_union_comm c1 r1
  end

#restart-solver
let map_group_choice_compatible_no_cut_concat_left
  (g1: det_map_group)
  (f1: typ)
  (g2: det_map_group)
  (f2: typ)
  (g: map_group)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\
    map_group_choice_compatible_no_cut g1 g /\
    map_group_choice_compatible_no_cut g2 g
  ))
  (ensures (
    map_group_choice_compatible_no_cut (g1 `map_group_concat` g2) g
  ))
= Classical.forall_intro (Classical.move_requires (map_group_concat_no_cut_intro g1 f1 g2 f2))

#restart-solver
let map_group_choice_compatible_choice_left
  (g1: det_map_group)
  (g2: det_map_group)
  (g: map_group)
: Lemma
  (requires (
    map_group_choice_compatible g1 g /\
    map_group_choice_compatible g2 g
  ))
  (ensures (
    map_group_choice_compatible (g1 `map_group_choice` g2) g
  ))
= ()

#restart-solver
let map_group_choice_compatible_no_cut_choice_left
  (g1: det_map_group)
  (g2: det_map_group)
  (g: map_group)
: Lemma
  (requires (
    map_group_choice_compatible_no_cut g1 g /\
    map_group_choice_compatible_no_cut g2 g
  ))
  (ensures (
    map_group_choice_compatible_no_cut (g1 `map_group_choice` g2) g
  ))
= ()

#restart-solver
let map_group_choice_compatible_no_cut_zero_or_one_left
  (g1: det_map_group)
  (g: map_group)
: Lemma
  (requires (
    map_group_choice_compatible_no_cut g1 g
  ))
  (ensures (
    map_group_choice_compatible_no_cut (map_group_zero_or_one g1) g
  ))
= ()

#restart-solver
let map_group_choice_compatible_choice_right
  (g: det_map_group)
  (g1: det_map_group)
  (g2: det_map_group)
: Lemma
  (requires (
    map_group_choice_compatible g g1 /\
    map_group_choice_compatible g g2
  ))
  (ensures (
    map_group_choice_compatible g (g1 `map_group_choice` g2)
  ))
= ()

#restart-solver
let map_group_choice_compatible_no_cut_choice_right
  (g: det_map_group)
  (g1: det_map_group)
  (g2: det_map_group)
: Lemma
  (requires (
    map_group_choice_compatible_no_cut g g1 /\
    map_group_choice_compatible_no_cut g g2
  ))
  (ensures (
    map_group_choice_compatible_no_cut g (g1 `map_group_choice` g2)
  ))
= ()

let map_group_choice_compatible_no_cut_match_item_for_no_cut
  (key: Cbor.raw_data_item)
  (value: typ)
  (g: det_map_group)
: Lemma
  (map_group_choice_compatible_no_cut (map_group_match_item_for false key value) g)
= ()

let map_group_choice_compatible_no_cut_zero_or_more_match_item_left
  (key: typ)
  (value: typ)
  (g: det_map_group)
: Lemma
  (map_group_choice_compatible_no_cut (map_group_zero_or_more (map_group_match_item false key value)) g)
= ()

let map_group_choice_compatible_no_cut_match_item_for_cut
  (key: Cbor.raw_data_item)
  (value: typ)
  (g: det_map_group)
  (f: typ)
: Lemma
  (requires (
    map_group_footprint g f /\
    typ_disjoint (t_literal key) f
  ))
  (ensures (
    map_group_choice_compatible_no_cut (map_group_match_item_for true key value) g
  ))
= map_group_choice_compatible_match_item_for true key value g f

val map_group_footprint_concat_consumes_all_recip
  (g1 g2: map_group)
  (f1 f2: typ)
  (m: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Ghost (ghost_map Cbor.raw_data_item Cbor.raw_data_item & ghost_map Cbor.raw_data_item Cbor.raw_data_item)
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\
    map_group_consumes_all (g1 `map_group_concat` g2) m
  ))
  (ensures (fun (m1, m2) ->
    m1 `ghost_map_disjoint` m2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 ghost_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 ghost_map_empty /\
    m1 `ghost_map_union` m2 == m
  ))

#restart-solver
let map_group_footprint_concat_consumes_all_recip'
  (g1 g2: map_group)
  (f1 f2: typ)
  (m: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\
    map_group_consumes_all (g1 `map_group_concat` g2) m
  ))
  (ensures exists m1m2 .
    (let (m1, m2) = m1m2 in
    m1 `ghost_map_disjoint` m2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 ghost_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 ghost_map_empty /\
    m1 `ghost_map_union` m2 == m
  ))
= let (_, _) = map_group_footprint_concat_consumes_all_recip g1 g2 f1 f2 m in
  ()

#restart-solver
let map_group_choice_compatible_match_item_for_concat_right
  (k: Cbor.raw_data_item)
  (v: typ)
  (g1 g2: det_map_group)
  (f1 f2: typ)
: Lemma
  (requires (
    map_group_choice_compatible (map_group_match_item_for false k v) g1 /\
    map_group_choice_compatible (map_group_match_item_for false k v) g2 /\
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2
  ))
  (ensures (
    map_group_choice_compatible (map_group_match_item_for false k v) (map_group_concat g1 g2)
  ))
= Classical.forall_intro (Classical.move_requires (map_group_footprint_concat_consumes_all_recip' g1 g2 f1 f2))
    
#restart-solver
let map_group_choice_compatible_match_item_for_zero_or_one_right
  (cut: bool)
  (k: Cbor.raw_data_item)
  (v: typ)
  (g: det_map_group)
: Lemma
  (requires (
    map_group_choice_compatible (map_group_match_item_for cut k v) g
  ))
  (ensures (
    map_group_choice_compatible (map_group_match_item_for cut k v) (map_group_zero_or_one g)
  ))
= ()

#restart-solver
let map_group_choice_compatible_match_item_for_same
  (k: Cbor.raw_data_item)
  (v1 v2: typ)
  (cut2: bool)
: Lemma
  (requires (
    typ_disjoint v1 v2
  ))
  (ensures (
    map_group_choice_compatible (map_group_match_item_for false k v1) (map_group_match_item_for cut2 k v2)
  ))
= ()

let ghost_map_in_footprint
  (m: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
  (f: typ)
: Tot prop
= forall x . ghost_map_mem x m ==> (f (fst x))

unfold
let map_group_parser_spec_arg_common
  (source: det_map_group)
  (source_fp: typ)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item)) // list needed because I need to preserve the order of elements when parsing a table
: Tot prop
= 
    let m = ghost_map_of_list x in
    List.Tot.no_repeats_p (List.Tot.map fst x) /\
    map_group_footprint source source_fp /\
    ghost_map_in_footprint m source_fp

unfold
let map_group_parser_spec_arg_prop
  (source: det_map_group)
  (source_fp: typ)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item)) // list needed because I need to preserve the order of elements when parsing a table
: Tot prop
= map_group_parser_spec_arg_common source source_fp x /\
  MapGroupDet? (apply_map_group_det source (ghost_map_of_list x))

let map_group_parser_spec_arg
  (source: det_map_group)
  (source_fp: typ)
: Tot Type0
= (x: list (Cbor.raw_data_item & Cbor.raw_data_item) {
    map_group_parser_spec_arg_prop source source_fp x
  })

let map_group_parser_spec_ret
  (source: det_map_group)
  (source_fp: typ)
  (#target: Type0)
  (target_size: target -> GTot nat)
  (target_prop: target -> prop)
  (x: map_group_parser_spec_arg source source_fp)
: Tot Type0
= (y: target { 
    target_size y <= List.Tot.length x // not everything is parsed, especially for choice
    /\ target_prop y
  })

let map_group_parser_spec
  (source: det_map_group)
  (source_fp: typ)
  (#target: Type0)
  (target_size: target -> GTot nat)
  (target_prop: target -> prop)
: Type0
= (x: map_group_parser_spec_arg source source_fp) -> GTot (map_group_parser_spec_ret source source_fp target_size target_prop x)

unfold
let map_group_serializer_spec_arg_prop
  (source: det_map_group)
  (source_fp: typ)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item)) // list needed because I need to preserve the order of elements when parsing a table
: Tot prop
= map_group_parser_spec_arg_common source source_fp x /\
  begin match apply_map_group_det source (ghost_map_of_list x) with
  | MapGroupDet _ res -> res == ghost_map_empty // everything is consumed
  | _ -> False
  end

#restart-solver
let map_group_serializer_spec
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (p: map_group_parser_spec source source_fp target_size target_prop)
: Type0
= (x: target { target_prop x }) -> GTot (y: list _ {
    map_group_serializer_spec_arg_prop source source_fp y /\
    target_size x == List.Tot.length y /\
    p y == x
  })

[@@erasable]
noeq
type mg_spec
  (source: det_map_group)
  (source_fp: typ)
  (target: Type0)
: Type
= {
  mg_size: target -> GTot nat;
  mg_serializable: target -> prop;
  mg_parser: map_group_parser_spec source source_fp mg_size mg_serializable;
  mg_serializer: map_group_serializer_spec mg_parser;
}

let mg_spec_coerce_target_prop
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (p: mg_spec source source_fp target)
  (target_size': target -> GTot nat {
    forall x . target_size' x == p.mg_size x
  })
  (target_prop': target -> prop {
    forall x . target_prop' x <==> p.mg_serializable x
  })
: mg_spec source source_fp target
= {
  mg_size = target_size';
  mg_serializable = target_prop';
  mg_parser = (p.mg_parser <: map_group_parser_spec source source_fp target_size' target_prop');
  mg_serializer = p.mg_serializer;
}

let rec list_forall_memP_filter
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (forall x . List.Tot.memP x l ==> f x))
  (ensures (List.Tot.filter f l == l))
= match l with
  | [] -> ()
  | _ :: q -> list_forall_memP_filter f q

let rec list_filter_append
  (#t: Type)
  (f: t -> bool)
  (l1 l2: list t)
: Lemma
  (ensures List.Tot.filter f (l1 `List.Tot.append` l2) == List.Tot.filter f l1 `List.Tot.append` List.Tot.filter f l2)
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_filter_append f q l2

let rec list_filter_for_none
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (forall x . List.Tot.memP x l ==> ~ (f x)))
  (ensures List.Tot.filter f l == [])
= match l with
  | [] -> ()
  | _ :: q -> list_filter_for_none f q

val parser_spec_map_group
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (p: map_group_parser_spec source source_fp target_size target_prop {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
  (target_prop' : target -> prop {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64)
  })
: Tot (parser_spec (t_map source0) target target_prop')

val parser_spec_map_group_eq
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (p: map_group_parser_spec source source_fp target_size target_prop {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
  (target_prop' : target -> prop {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64)
  })
  (x: CBOR.Spec.raw_data_item { t_map source0 x })
: Lemma
  (exists (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool) .
    (forall x . Ghost.reveal f x == matches_map_group_entry source_fp any x) /\
    (let x' = List.Tot.filter f (Cbor.Map?.v x) in
    map_group_parser_spec_arg_prop source source_fp x' /\
    parser_spec_map_group source0 p target_prop' x == p x'
  ))
  [SMTPat (parser_spec_map_group source0 p target_prop' x)]

#restart-solver
let serializer_spec_map_group
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (#p: map_group_parser_spec source source_fp target_size target_prop)
  (s: map_group_serializer_spec p {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
  (target_prop' : target -> prop {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64)
  })
: Tot (serializer_spec (parser_spec_map_group source0 p target_prop'))
= fun z ->
  let l = s z in
  let MapGroupDet _ rem = apply_map_group_det source0 (ghost_map_of_list l) in
  ghost_map_equiv rem ghost_map_empty;
  let res = Cbor.Map l in
  assert (t_map source0 res);
  Classical.forall_intro (fun f -> Classical.move_requires (list_forall_memP_filter #(Cbor.raw_data_item & Cbor.raw_data_item) f) l);
  assert (parser_spec_map_group source0 p target_prop' res == z);
  res

let spec_map_group_serializable
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (p: mg_spec source source_fp target)
  (x: target)
: Tot prop
= p.mg_serializable x /\
  p.mg_size x < pow2 64

let spec_map_group
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (p: mg_spec source source_fp target {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
: Tot (spec (t_map source0) target)
= {
  serializable = spec_map_group_serializable p;
  parser = parser_spec_map_group source0 p.mg_parser _;
  serializer = serializer_spec_map_group source0 p.mg_serializer _;
}

let map_group_parser_spec_bij
  (#source: det_map_group)
  (#source_fp: typ)
  (#target1: Type0)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (f: map_group_parser_spec source source_fp target_size1 target_prop1)
  (#target2: Type0)
  (target_size2: target2 -> GTot nat)
  (target_prop2: target2 -> prop)
  (bij: bijection target1 target2 {
    (forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)) /\
    (forall x2 . target_prop2 x2 <==> target_prop1 (bij.bij_to_from x2))
  })
: Tot (map_group_parser_spec source source_fp target_size2 target_prop2)
= fun x -> bij.bij_from_to (f x)

let map_group_serializer_spec_bij
  (#source: det_map_group)
  (#source_fp: typ)
  (#target1: Type0)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (#f: map_group_parser_spec source source_fp target_size1 target_prop1)
  (s: map_group_serializer_spec f)
  (#target2: Type0)
  (target_size2: target2 -> GTot nat)
  (target_prop2: target2 -> prop)
  (bij: bijection target1 target2 {
    (forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)) /\
    (forall x2 . target_prop2 x2 <==> target_prop1 (bij.bij_to_from x2))
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_bij f target_size2 target_prop2 bij))
= fun x -> s (bij.bij_to_from x)

let mg_spec_bij_size
  (#source: det_map_group)
  (#source_fp: typ)
  (#target1: Type0)
  (f: mg_spec source source_fp target1)
  (#target2: Type0)
  (bij: bijection target1 target2)
  (x: target2)
: GTot nat
= f.mg_size (bij.bij_to_from x)

let mg_spec_bij_serializable
  (#source: det_map_group)
  (#source_fp: typ)
  (#target1: Type0)
  (f: mg_spec source source_fp target1)
  (#target2: Type0)
  (bij: bijection target1 target2)
  (x: target2)
: Tot prop
= f.mg_serializable (bij.bij_to_from x)

let mg_spec_bij
  (#source: det_map_group)
  (#source_fp: typ)
  (#target1: Type0)
  (f: mg_spec source source_fp target1)
  (#target2: Type0)
  (bij: bijection target1 target2)
: Tot (mg_spec source source_fp target2)
= {
  mg_size = mg_spec_bij_size f bij;
  mg_serializable = mg_spec_bij_serializable f bij;
  mg_parser = map_group_parser_spec_bij f.mg_parser _ _ bij;
  mg_serializer = map_group_serializer_spec_bij f.mg_serializer _ _ bij;
}

let map_group_parser_spec_match_item_for
  (cut: bool)
  (k: Cbor.raw_data_item)
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> prop)
  (p: parser_spec ty target target_prop)
  (target_size: target -> GTot nat {
    forall x . target_size x == 1
  })
: Tot (map_group_parser_spec (map_group_match_item_for cut k ty) (t_literal k) target_size target_prop)
= fun x ->
  let Some v = Cbor.list_ghost_assoc k x in
  ghost_map_equiv (ghost_map_of_list x) (ghost_map_of_list [k, v]);
  ghost_map_length_of_list [k, v];
  p v

let map_group_serializer_spec_match_item_for
  (cut: bool)
  (k: Cbor.raw_data_item)
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> prop)
  (#p: parser_spec ty target target_prop)
  (s: serializer_spec p)
  (target_size: target -> GTot nat {
    forall x . target_size x == 1
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_match_item_for cut k p target_size))
= fun x ->
  map_group_footprint_match_item_for cut k ty;
  let v = s x in
  let res = [k, v] in
  let mres = ghost_map_of_list res in
  ghost_map_equiv mres (ghost_map_singleton k v);
  let MapGroupDet _ rem = apply_map_group_det (map_group_match_item_for cut k ty) mres in
  ghost_map_equiv rem ghost_map_empty;
  res

let mg_spec_match_item_for_size
  (target: Type)
  (x: target)
: GTot nat
= 1

let mg_spec_match_item_for
  (cut: bool)
  (k: Cbor.raw_data_item)
  (#ty: typ)
  (#target: Type)
  (p: spec ty target)
: Tot (mg_spec (map_group_match_item_for cut k ty) (t_literal k) target)
= {
  mg_size = mg_spec_match_item_for_size target;
  mg_serializable = p.serializable;
  mg_parser = map_group_parser_spec_match_item_for cut k p.parser _;
  mg_serializer = map_group_serializer_spec_match_item_for cut k p.serializer _;
}

val map_group_parser_spec_concat
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (target_size: (target1 & target2) -> GTot nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2 /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
  (target_prop: (target1 & target2) -> prop {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
: Tot (map_group_parser_spec (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2) target_size target_prop)

#restart-solver
val map_group_parser_spec_concat_eq
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (target_size: (target1 & target2) -> GTot nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2 /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
  (target_prop: (target1 & target2) -> prop {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
  (l: map_group_parser_spec_arg (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2))
: Lemma
  (exists (f1: _ -> bool) (f2: _ -> bool) .
    (forall x . f1 x == matches_map_group_entry source_fp1 any x) /\
    (forall x . f2 x == matches_map_group_entry source_fp2 any x) /\ (
    let l1 = List.Tot.filter f1 l in
    let l2 = List.Tot.filter f2 l in
    map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
    map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
    map_group_parser_spec_concat p1 p2 target_size target_prop l == (p1 l1, p2 l2)
  ))
  [SMTPat (map_group_parser_spec_concat p1 p2 target_size target_prop l)]

let orp (#t: Type) (p1 p2: t -> bool) (x: t) : bool =
  p1 x || p2 x

#restart-solver
let map_group_serializer_spec_concat
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (#p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (s1: map_group_serializer_spec p1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (#p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (s2: map_group_serializer_spec p2)
  (target_size: (target1 & target2) -> GTot nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2 /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
  (target_prop: (target1 & target2) -> prop {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_concat p1 p2 target_size target_prop))
= fun x ->
    map_group_footprint_concat source1 source2 source_fp1 source_fp2;
    let (x1, x2) = x in
    let l1 = s1 x1 in
    let l2 = s2 x2 in
    let res = l1 `List.Tot.append` l2 in
    map_group_footprint_concat_consumes_all source1 source2 source_fp1 source_fp2 (ghost_map_of_list l1) (ghost_map_of_list l2);
    List.Tot.append_length l1 l2;
    assert (ghost_map_in_footprint (ghost_map_of_list l1) (source_fp1 `t_choice` source_fp2));
    assert (ghost_map_in_footprint (ghost_map_of_list l2) (source_fp1 `t_choice` source_fp2));
    assert (ghost_map_in_footprint (ghost_map_of_list l1 `ghost_map_union` ghost_map_of_list l2) (source_fp1 `t_choice` source_fp2));
    ghost_map_of_list_append l1 l2;
    ghost_map_length_of_list (l1 `List.Tot.append` l2);
    assert (map_group_serializer_spec_arg_prop (source1 `map_group_concat` source2) (source_fp1 `t_choice` source_fp2) res);
    let prf
      (f1 : _ -> bool) (f2 : _ -> bool)
    : Lemma
      (requires (
        (forall x . f1 x == matches_map_group_entry source_fp1 any x) /\
        (forall x . f2 x == matches_map_group_entry source_fp2 any x)
      ))
      (ensures (
        (forall x . (f1 `orp` f2) x == matches_map_group_entry (source_fp1 `t_choice` source_fp2) any x) /\
        l1 == List.Tot.filter f1 res /\
        l2 == List.Tot.filter f2 res
      ))
    = assert (forall x . (f1 `orp` f2) x == matches_map_group_entry (source_fp1 `t_choice` source_fp2) any x);
      list_filter_append f1 l1 l2;
      list_forall_memP_filter f1 l1;
      list_filter_for_none f1 l2;
      List.Tot.append_l_nil l1;
      list_filter_for_none f2 l1;
      list_forall_memP_filter f2 l2;
      list_filter_append f2 l1 l2
    in
    Classical.forall_intro_2 (fun f1 -> Classical.move_requires (prf f1));
    assert (map_group_parser_spec_concat p1 p2 target_size target_prop res == x);
    res

let mg_spec_concat_size
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (p1: mg_spec source1 source_fp1 target1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (p2: mg_spec source2 source_fp2 target2)
  (x: (target1 & target2))
: GTot nat
= p1.mg_size (fst x) + p2.mg_size (snd x)

let mg_spec_concat_serializable
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (p1: mg_spec source1 source_fp1 target1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (p2: mg_spec source2 source_fp2 target2)
  (x: (target1 & target2))
: Tot prop
= p1.mg_serializable (fst x) /\ p2.mg_serializable (snd x)

let mg_spec_concat
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (p1: mg_spec source1 source_fp1 target1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (p2: mg_spec source2 source_fp2 target2 {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2
  })
: Tot (mg_spec (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2) (target1 & target2))
= {
  mg_size = mg_spec_concat_size p1 p2;
  mg_serializable = mg_spec_concat_serializable p1 p2;
  mg_parser = map_group_parser_spec_concat p1.mg_parser p2.mg_parser _ _;
  mg_serializer = map_group_serializer_spec_concat p1.mg_serializer p2.mg_serializer _ _;
}

val map_group_parser_spec_choice
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2 {
    map_group_footprint source2 source_fp2
  })
  (target_size: (target1 `either` target2) -> GTot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> prop {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })  
: Tot (map_group_parser_spec (map_group_choice source1 source2) (source_fp1 `t_choice` source_fp2) target_size target_prop)

val map_group_parser_spec_choice_eq
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2 {
    map_group_footprint source2 source_fp2
  })
  (target_size: (target1 `either` target2) -> GTot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> prop {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })  
  (l: map_group_parser_spec_arg (map_group_choice source1 source2) (source_fp1 `t_choice` source_fp2))
: Lemma
    (requires True)
    (ensures (
        let l' = map_group_parser_spec_choice p1 p2 target_size target_prop l in
        exists (f1: _ -> bool) (f2: _ -> bool) .
        (forall x . f1 x == matches_map_group_entry source_fp1 any x) /\
        (forall x . f2 x == matches_map_group_entry source_fp2 any x) /\ (
        let l1 = List.Tot.filter f1 l in
        let l2 = List.Tot.filter f2 l in
        let test = MapGroupDet? (apply_map_group_det source1 (ghost_map_of_list l1)) in
        ghost_map_of_list l1 == ghost_map_filter (matches_map_group_entry source_fp1 any) (ghost_map_of_list l) /\
        ghost_map_of_list l2 == ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l) /\
        (test ==> (
          map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
          (l' <: (target1 `either` target2)) == Inl (p1 l1)
        )) /\
        (~ test ==> (
          map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
          (l' <: (target1 `either` target2)) == Inr (p2 l2)
        ))
    )))
    [SMTPat (map_group_parser_spec_choice p1 p2 target_size target_prop l)]

#restart-solver
let map_group_serializer_spec_choice
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (#p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (s1: map_group_serializer_spec p1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (#p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (s2: map_group_serializer_spec p2 {
    map_group_footprint source2 source_fp2 /\
    map_group_choice_compatible source1 source2
  })
  (target_size: (target1 `either` target2) -> GTot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> prop {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })  
: Tot (map_group_serializer_spec (map_group_parser_spec_choice p1 p2 target_size target_prop))
= fun x ->
    let res : list (Cbor.raw_data_item & Cbor.raw_data_item) =
      match x with
      | Inl y -> s1 y
      | Inr y -> s2 y
    in
    assert (map_group_serializer_spec_arg_prop (source1 `map_group_choice` source2) (source_fp1 `t_choice` source_fp2) res);
    assert (target_size x == List.Tot.length res);
    Classical.forall_intro (fun f -> Classical.move_requires (list_forall_memP_filter f) res);
    let _ : squash (map_group_parser_spec_choice p1 p2 target_size target_prop res == x) =
      match x with
      | Inl y -> ()
      | Inr y ->
        assert (MapGroupDet? (apply_map_group_det source2 (ghost_map_of_list res)));
        assert (MapGroupFail? (apply_map_group_det source1 (ghost_map_of_list res)));
        map_group_footprint_is_consumed_ghost_map_of_list source1 source_fp1 res;
        assert (map_group_parser_spec_choice p1 p2 target_size target_prop res == x)
    in
    res

let mg_spec_choice_size
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (p1: mg_spec source1 source_fp1 target1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (p2: mg_spec source2 source_fp2 target2)
  (x: either target1 target2)
: GTot nat
= match x with
  | Inl x1 -> p1.mg_size x1
  | Inr x2 -> p2.mg_size x2

let mg_spec_choice_serializable
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (p1: mg_spec source1 source_fp1 target1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (p2: mg_spec source2 source_fp2 target2)
  (x: either target1 target2)
: Tot prop
= match x with
  | Inl x1 -> p1.mg_serializable x1
  | Inr x2 -> p2.mg_serializable x2

let mg_spec_choice
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (p1: mg_spec source1 source_fp1 target1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (p2: mg_spec source2 source_fp2 target2 {
    map_group_footprint source2 source_fp2 /\
    map_group_choice_compatible source1 source2
  })
: Tot (mg_spec (map_group_choice source1 source2) (source_fp1 `t_choice` source_fp2) (either target1 target2))
= {
  mg_size = mg_spec_choice_size p1 p2;
  mg_serializable = mg_spec_choice_serializable p1 p2;
  mg_parser = map_group_parser_spec_choice p1.mg_parser p2.mg_parser _ _;
  mg_serializer = map_group_serializer_spec_choice p1.mg_serializer p2.mg_serializer _ _;
}

(*
let rec map_group_parser_spec_zero_or_more'
  (#source: det_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size {
    map_group3_concat_unique_strong source source
  })
  (target_size' : list target -> nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (x: map_group_parser_spec_arg (map_group3_zero_or_more source) target_size')
: GTot (map_group_parser_spec_ret (map_group3_zero_or_more source) target_size' x)
  (decreases (List.Tot.length x))
= match source x with
  | None ->
    assert (x == []);
    let res : list target = [] in
    assert (Nil? res);
    assert (target_size' res == 0);
    res
  | Some (l1, l2) ->
    if Nil? l1
    then []
    else begin
      map_group3_concat_unique_weak_zero_or_more_right source source;
      List.Tot.append_length l1 l2;
      let q = map_group_parser_spec_zero_or_more' p target_size' l2 in
      p l1 :: q
    end

let map_group_parser_spec_zero_or_more
  (#source: det_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size {
    map_group3_concat_unique_strong source source
  })
  (target_size' : list target -> nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
: Tot (map_group_parser_spec (map_group3_zero_or_more source) target_size')
= map_group_parser_spec_zero_or_more' p target_size'

let nonempty_map_group : Type0 =
  (a: map_group {
    forall l . match a l with
    | Some (consumed, _) -> Cons? consumed
    | _ -> True
  })

let rec map_group_serializer_spec_zero_or_more'
  (#source: nonempty_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source target_size)
  (s: map_group_serializer_spec p {
    map_group3_concat_unique_strong source source
  })
  (target_size' : list target -> nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (x: list target)
: GTot (y: map_group_parser_spec_arg (map_group3_zero_or_more source) target_size' {
    map_group_parser_spec_zero_or_more p target_size' y == x
  })
  (decreases x)
= match x with
  | [] -> []
  | a :: q ->
    map_group3_concat_unique_weak_zero_or_more_right source source;
    let l1 = s a in
    let l2 = map_group_serializer_spec_zero_or_more' s target_size' q in
    let res = l1 `List.Tot.append` l2 in
    res

let map_group_serializer_spec_zero_or_more
  (#source: nonempty_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source target_size)
  (s: map_group_serializer_spec p {
    map_group3_concat_unique_strong source source
  })
  (target_size' : list target -> nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_zero_or_more p target_size'))
= map_group_serializer_spec_zero_or_more' s target_size'

let nelist (a: Type) : Type0 = (l: list a { Cons? l })

let map_group_parser_spec_one_or_more
  (#source: det_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size {
    map_group3_concat_unique_strong source source
  })
  (target_size1 : list target -> nat {
    forall (l: list target) . target_size1 l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size1 (List.Tot.tl l))
  })
  (target_size2 : nelist target -> nat {
    forall (l: nelist target) . target_size2 l == target_size1 l
  })
: Tot (map_group_parser_spec (map_group3_one_or_more source) target_size2)
= fun x ->
  map_group3_concat_unique_weak_zero_or_more_right source source;
  let Some (l1, l2) = source x in
  List.Tot.append_length l1 l2;
  p l1 :: map_group_parser_spec_zero_or_more p target_size1 l2

let map_group_serializer_spec_one_or_more
  (#source: nonempty_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source target_size)
  (s: map_group_serializer_spec p {
    map_group3_concat_unique_strong source source
  })
  (target_size1 : list target -> nat {
    forall (l: list target) . target_size1 l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size1 (List.Tot.tl l))
  })
  (target_size2 : nelist target -> nat {
    forall (l: nelist target) . target_size2 l == target_size1 l
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_one_or_more p target_size1 target_size2))
= fun x ->
  map_group3_concat_unique_weak_zero_or_more_right source source;
  let hd :: tl = x in
  let l1 = s hd in
  let l2 = map_group_serializer_spec_zero_or_more s target_size1 tl in
  List.Tot.append_length l1 l2;
  l1 `List.Tot.append` l2

let map_group_parser_spec_zero_or_one
  (#source: det_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size)
  (target_size': option target -> nat {
    forall x . target_size' x == begin match x with
    | None -> 0
    | Some x -> target_size x
    end
  })
: Tot (map_group_parser_spec (map_group3_zero_or_one source) target_size')
= fun x ->
    if Some? (source x)
    then Some (p x)
    else None

let map_group_serializer_spec_zero_or_one
  (#source: nonempty_map_group) // needed because the empty case must map to None only
  (#target: Type)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source target_size)
  (s: map_group_serializer_spec p)
  (target_size': option target -> nat {
    forall x . target_size' x == begin match x with
    | None -> 0
    | Some x -> target_size x
    end
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_zero_or_one p target_size'))
= fun x ->
    match x with
    | None -> []
    | Some y -> s y

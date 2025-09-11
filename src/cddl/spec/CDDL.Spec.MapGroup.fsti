module CDDL.Spec.MapGroup
include CDDL.Spec.MapGroup.Base
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module U = CBOR.Spec.Util
module Map = CDDL.Spec.Map
open CBOR.Spec.API.Type

let map_constraint = (cbor & cbor) -> bool

let cbor_map_disjoint_from_footprint
  (m: cbor_map)
  (f: map_constraint)
: Tot prop
= forall x . Some? (cbor_map_get m x) ==> ~ (f (x, Some?.v (cbor_map_get m x)))

let cbor_map_disjoint_from_footprint_cbor_map_union
  (m1 m2: cbor_map)
  (f: map_constraint)
: Lemma
  (requires (
    cbor_map_disjoint_from_footprint m1 f /\
    cbor_map_disjoint_from_footprint m2 f
  ))
  (ensures (
    cbor_map_disjoint_from_footprint (cbor_map_union m1 m2) f
  ))
  [SMTPat (cbor_map_disjoint_from_footprint (cbor_map_union m1 m2) f)]
= ()

let map_group_footprint
  (g: map_group)
  (f: map_constraint)
: Tot prop
= forall m m' . (cbor_map_disjoint m m' /\ cbor_map_disjoint_from_footprint m' f) ==>
  begin match apply_map_group_det g m, apply_map_group_det g (m `cbor_map_union` m') with
  | MapGroupCutFail, MapGroupCutFail
  | MapGroupFail, MapGroupFail -> True
  | MapGroupDet _ r, MapGroupDet _ r' -> r' == r `cbor_map_union` m'
  | _ -> False
  end

let map_constraint_equiv
  (f1 f2: map_constraint)
: Tot prop
= forall x . f1 x == f2 x

let map_group_footprint_equiv
  (g: map_group)
  (f1 f2: map_constraint)
: Lemma
  (requires
    map_group_footprint g f1 /\
    map_constraint_equiv f1 f2
  )
  (ensures map_group_footprint g f2)
= ()

let map_constraint_included
  (f1 f2: map_constraint)
: Tot prop
= (forall x . f1 x ==> f2 x)

let map_group_footprint_implies
  (g: map_group)
  (f1 f2: map_constraint)
: Lemma
  (requires
    map_group_footprint g f1 /\
    map_constraint_included f1 f2
  )
  (ensures map_group_footprint g f2)
= ()

#restart-solver
let map_group_footprint_elim
  (g: map_group)
  (f: map_constraint)
  (m m' : cbor_map)
: Lemma
  (requires
    map_group_footprint g f /\
    cbor_map_disjoint m m' /\
    cbor_map_disjoint_from_footprint m' f
  )
  (ensures
  begin match apply_map_group_det g m, apply_map_group_det g (m `cbor_map_union` m') with
  | MapGroupCutFail, MapGroupCutFail
  | MapGroupFail, MapGroupFail -> True
  | MapGroupDet c r, MapGroupDet c' r' -> c' == c /\ r' == r `cbor_map_union` m'
  | _ -> False
  end
  )
= match apply_map_group_det g m, apply_map_group_det g (m `cbor_map_union` m') with
  | MapGroupDet c r, MapGroupDet c' r' ->
    assert (r' == r `cbor_map_union` m');
    assert (cbor_map_equal c' c)
  | _ -> ()

#restart-solver
let map_group_footprint_intro
  (g: map_group)
  (f: map_constraint)
  (prf: (m: _) -> (m' : cbor_map) ->
    Lemma
    (requires
      cbor_map_disjoint m m' /\
      cbor_map_disjoint_from_footprint m' f
    )
    (ensures
    begin match apply_map_group_det g m, apply_map_group_det g (m `cbor_map_union` m') with
    | MapGroupCutFail, MapGroupCutFail
    | MapGroupFail, MapGroupFail -> True
    | MapGroupDet _ r, MapGroupDet _ r' -> r' == r `cbor_map_union` m'
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
  (f: map_constraint)
  (m m': _)
: Lemma
  (requires
    map_group_footprint g f /\
    cbor_map_disjoint m m' /\
    cbor_map_disjoint_from_footprint m' f /\
    (MapGroupDet? (apply_map_group_det g m) \/ MapGroupDet? (apply_map_group_det g (m `cbor_map_union` m')))
  )
  (ensures (
    match apply_map_group_det g m, apply_map_group_det g (m `cbor_map_union` m') with
    | MapGroupDet c _, MapGroupDet c' _ -> c == c'
    | _ -> False
  ))
  [SMTPat (map_group_footprint g f); SMTPat (apply_map_group_det g (m `cbor_map_union` m'))]
= let MapGroupDet c r = apply_map_group_det g m in
  let MapGroupDet c' r' = apply_map_group_det g (m `cbor_map_union` m') in
  cbor_map_union_assoc c r m';
  cbor_map_disjoint_union_simpl_r c c' r'

#restart-solver
let map_group_footprint_is_consumed
  (g: map_group)
  (f: map_constraint)
  (m: _)
: Lemma
  (requires
    map_group_footprint g f
  )
  (ensures (
    match apply_map_group_det g m, apply_map_group_det g (cbor_map_filter f m) with
    | MapGroupDet _ _, MapGroupDet _ _
    | MapGroupFail, MapGroupFail
    | MapGroupCutFail, MapGroupCutFail -> True
    | _ -> False
  ))
= cbor_map_split f m

let map_constraint_disjoint
  (f1 f2: map_constraint)
: Tot prop
= forall x . ~  (f1 x /\ f2 x)

let map_group_footprint_consumed_disjoint
  (g: map_group)
  (f f' : map_constraint)
  (m: _)
: Lemma
  (requires
    map_group_footprint g f /\
    f `map_constraint_disjoint` f' /\
    MapGroupDet? (apply_map_group_det g m)
  )
  (ensures (
    match apply_map_group_det g m with
    | MapGroupDet c _ ->
      cbor_map_disjoint_from_footprint c f'
    | _ -> False
  ))
= cbor_map_split f m;
  map_group_footprint_consumed g f (cbor_map_filter f m) (cbor_map_filter (U.notp f) m)

let map_constraint_choice
  (f1 f2: map_constraint)
  (x: (cbor & cbor))
: Tot bool
= f1 x || f2 x

#restart-solver
let map_group_footprint_concat
  (g1 g2: map_group)
  (f1 f2: map_constraint)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2
  ))
  (ensures (
    map_group_footprint (map_group_concat g1 g2) (map_constraint_choice f1 f2)
  ))
  [SMTPat (map_group_footprint g1 f1); SMTPat (map_group_footprint g2 f2); SMTPat (map_group_concat g1 g2)]
= ()

#restart-solver
let map_group_footprint_choice
  (g1 g2: map_group)
  (f1 f2: map_constraint)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2
  ))
  (ensures (
    map_group_footprint (map_group_choice g1 g2) (map_constraint_choice f1 f2)
  ))
  [SMTPat (map_group_footprint g1 f1); SMTPat (map_group_footprint g2 f2); SMTPat (map_group_choice g1 g2)]
= ()

#restart-solver
let map_group_footprint_zero_or_one
  (g1: map_group)
  (f1: map_constraint)
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
  (f1: map_constraint)
  (m1: cbor_map)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 cbor_map_empty
  ))
  (ensures (
    cbor_map_filter (f1) m1 == m1 /\
    cbor_map_filter (U.notp (f1)) m1 == cbor_map_empty
  ))
= cbor_map_split f1 m1;
  map_group_footprint_elim g1 f1 (cbor_map_filter f1 m1) (cbor_map_filter (U.notp f1) m1); 
  map_group_footprint_consumed g1 f1 (cbor_map_filter f1 m1) (cbor_map_filter (U.notp f1) m1);
  let MapGroupDet c1 r1 = apply_map_group_det g1 (cbor_map_filter f1 m1) in
  let MapGroupDet c' r' = apply_map_group_det g1 (cbor_map_filter f1 m1 `cbor_map_union` cbor_map_filter (U.notp f1) m1) in
  assert (cbor_map_empty == r1 `cbor_map_union` cbor_map_filter (U.notp f1) m1);
  cbor_map_ext cbor_map_empty (cbor_map_filter (U.notp f1) m1);
  ()

#restart-solver
let map_group_footprint_concat_consumes_all
  (g1 g2: map_group)
  (f1 f2: map_constraint)
  (m1 m2: cbor_map)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 cbor_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 cbor_map_empty /\
    cbor_map_disjoint m1 m2 /\ // this is no longer guaranteed by the footprints
    map_constraint_disjoint f1 f2
  ))
  (ensures (
    m1 `cbor_map_disjoint` m2 /\
    apply_map_group_det (g1 `map_group_concat` g2) (m1 `cbor_map_union` m2) == MapGroupDet (m1 `cbor_map_union` m2) cbor_map_empty
  ))
= map_group_footprint_consumes_all g1 f1 m1;
  map_group_footprint_consumes_all g2 f2 m2;
  let x = apply_map_group_det (g1 `map_group_concat` g2) (m1 `cbor_map_union` m2) in
  assert (MapGroupDet? x);
  assert (MapGroupDet?.consumed x `cbor_map_equal` (m1 `cbor_map_union` m2));
  assert (MapGroupDet?.remaining x `cbor_map_equal` cbor_map_empty);
  ()

let map_group_match_item_for_footprint // FIXME: necessary because Pulse does not handle `if then else` in `pure` conditions
  (cut: bool)
  (k: cbor)
  (dest: typ)
: Tot map_constraint
= matches_map_group_entry (t_literal k) (if cut then any else dest)

#restart-solver
let map_group_footprint_match_item_for
  (cut: bool)
  (key: cbor)
  (value: typ)
: Lemma
  (ensures (
    map_group_footprint (map_group_match_item_for cut key value) (map_group_match_item_for_footprint cut key value)
  ))
  [SMTPat (map_group_footprint (map_group_match_item_for cut key value))]
= let g = map_group_match_item_for cut key value in
  map_group_footprint_intro
    g
    (map_group_match_item_for_footprint cut key value)
    (fun m m' ->
      match cbor_map_get m key with
      | Some v ->
        assert (None? (cbor_map_get m' key));
        if value v
        then begin
          match apply_map_group_det g m, apply_map_group_det g (m `cbor_map_union` m') with
          | MapGroupDet _ r, MapGroupDet _ r' ->
            cbor_map_ext r' (r `cbor_map_union` m')
          | _ -> ()
        end
        else ()
      | _ -> ()
    )

#restart-solver
let map_group_footprint_filter
  (phi: _ -> Tot bool)
  (f: map_constraint)
: Lemma
  (requires
    forall (x: (cbor & cbor)) . U.notp phi x ==> f x
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
      let MapGroupDet _ r' = apply_map_group_det g (m `cbor_map_union` m') in
      cbor_map_disjoint_union_filter phi m m';
      cbor_map_filter_for_all phi m';
      assert (r' == r `cbor_map_union` m')
    )

let map_group_footprint_zero_or_more_match_item
  (key value: typ)
: Lemma
  (map_group_footprint (map_group_zero_or_more (map_group_match_item false key value)) (matches_map_group_entry key value))
  [SMTPat (map_group_zero_or_more (map_group_match_item false key value))]
= ()

let map_group_footprint_match_item_cut
  (key value: typ)
: Lemma
  (map_group_footprint (map_group_match_item true key value) (matches_map_group_entry key any))
  [SMTPat (map_group_match_item true key value)]
= map_group_footprint_intro
    (map_group_match_item true key value)
    (matches_map_group_entry key any)
    (fun m m' ->
      assert (cbor_map_equal (cbor_map_filter (matches_map_group_entry key any) (cbor_map_union m m')) (cbor_map_filter (matches_map_group_entry key any) m));
      assert (cbor_map_equal (cbor_map_filter (CBOR.Spec.Util.notp (matches_map_group_entry key any)) (cbor_map_union m m')) (cbor_map_union (cbor_map_filter (CBOR.Spec.Util.notp (matches_map_group_entry key any)) m) m'))
    )

let map_group_footprint_cut
  (k: typ)
: Lemma
  (ensures (map_group_footprint (map_group_cut k) (matches_map_group_entry k any)))
  [SMTPat (map_group_cut k)]
= ()

let cbor_map_included (c' c : cbor_map) : Tot prop =
  (forall x . Some? (cbor_map_get c' x) ==> cbor_map_get c' x == cbor_map_get c x)

let restrict_map_group
  (g g': map_group)
: Tot prop
= forall m .
  begin match apply_map_group_det g m, apply_map_group_det g' m with
  | MapGroupCutFail, MapGroupCutFail
  | MapGroupFail, MapGroupFail -> True
  | MapGroupDet c r, MapGroupDet c' r' -> cbor_map_included c' c
  | _ -> False
  end

let restrict_map_group_intro
  (g g': map_group)
  (prf1: (m: _) -> Lemma
    begin match apply_map_group_det g m, apply_map_group_det g' m with
    | MapGroupCutFail, MapGroupCutFail
    | MapGroupFail, MapGroupFail -> True
    | MapGroupDet c r, MapGroupDet c' r' -> cbor_map_included c' c
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
  (key: cbor)
  (value: typ)
: Lemma
  (restrict_map_group (map_group_match_item_for cut key value) (map_group_match_item_for cut key value))
= ()

let restrict_map_group_filter
  (f: map_constraint)
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

let map_group_footprint_weaken = map_group_footprint_implies

(*
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
*)

let map_group_choice_compatible
  (left right: map_group)
: Tot prop
= forall x . match apply_map_group_det right x with
  | MapGroupDet _ rem -> rem == cbor_map_empty ==> MapGroupFail? (apply_map_group_det left x)
  | _ -> True

#restart-solver
let map_group_choice_compatible_intro
  (left right: map_group)
  (prf: (x: _) -> Lemma
    (requires begin match apply_map_group_det right x with
     | MapGroupDet _ rem -> rem == cbor_map_empty
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
  (key: cbor)
  (value: typ)
  (right: map_group)
  (fp: map_constraint)
: Lemma
  (requires (
    (map_group_match_item_for_footprint cut key value) `map_constraint_disjoint` fp /\
    map_group_footprint right fp
  ))
  (ensures (
    map_group_choice_compatible (map_group_match_item_for cut key value) right
  ))

let map_group_choice_compatible_no_cut
  (left right: map_group)
: Tot prop
= forall x . match apply_map_group_det right x with
  | MapGroupDet _ rem -> rem == cbor_map_empty ==> ~ (MapGroupCutFail? (apply_map_group_det left x))
  | _ -> True

let map_group_choice_compatible_implies_no_cut
  (left right: map_group)
: Lemma
  (map_group_choice_compatible left right ==> map_group_choice_compatible_no_cut left right)
= ()

#restart-solver
let map_group_fail_concat_intro
  (g1: det_map_group)
  (f1: map_constraint)
  (g2: det_map_group)
  (f2: map_constraint)
  (x: cbor_map)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2 /\ (
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
    cbor_map_disjoint_union_comm c1 r1
  end

let map_group_consumes_all
  (g: map_group)
  (x: cbor_map)
: Tot prop
= match apply_map_group_det g x with
  | MapGroupDet _ r -> r == cbor_map_empty
  | _ -> False

let map_group_choice_compatible_concat_left
  (g1: det_map_group)
  (f1: map_constraint)
  (g2: det_map_group)
  (f2: map_constraint)
  (g: map_group)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2 /\
    (map_group_choice_compatible g1 g \/ (
      map_group_choice_compatible_no_cut g1 g /\
      map_group_choice_compatible g2 g)
    )
  ))
  (ensures (
    map_group_choice_compatible (g1 `map_group_concat` g2) g
  ))
= Classical.forall_intro (Classical.move_requires (map_group_fail_concat_intro g1 f1 g2 f2))

let map_group_choice_compatible_concat_left1
  (g1: det_map_group)
  (f1: map_constraint)
  (g2: det_map_group)
  (f2: map_constraint)
  (g: map_group)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2 /\
    map_group_choice_compatible g1 g
  ))
  (ensures (
    map_group_choice_compatible (g1 `map_group_concat` g2) g
  ))
= map_group_choice_compatible_concat_left g1 f1 g2 f2 g

let map_group_choice_compatible_concat_left2
  (g1: det_map_group)
  (f1: map_constraint)
  (g2: det_map_group)
  (f2: map_constraint)
  (g: map_group)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2 /\
    map_group_choice_compatible_no_cut g1 g /\
    map_group_choice_compatible g2 g
  ))
  (ensures (
    map_group_choice_compatible (g1 `map_group_concat` g2) g
  ))
= map_group_choice_compatible_concat_left g1 f1 g2 f2 g

#restart-solver
let map_group_concat_no_cut_intro
  (g1: det_map_group)
  (f1: map_constraint)
  (g2: det_map_group)
  (f2: map_constraint)
  (x: cbor_map)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2 /\ (
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
    cbor_map_disjoint_union_comm c1 r1
  end

#restart-solver
let map_group_choice_compatible_no_cut_concat_left
  (g1: det_map_group)
  (f1: map_constraint)
  (g2: det_map_group)
  (f2: map_constraint)
  (g: map_group)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2 /\
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
  (key: cbor)
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

module Util = CBOR.Spec.Util

let map_group_filtered_table
  (key value: typ)
  (except: map_constraint)
: Tot map_group
= map_group_filter (Util.notp (Util.andp (matches_map_group_entry key value) (Util.notp except)))

let map_group_choice_compatible_no_cut_filtered_table
  (key: typ)
  (value: typ)
  (except: map_constraint)
  (g: det_map_group)
: Lemma
  (map_group_choice_compatible_no_cut (map_group_filtered_table key value except) g)
= ()

let map_group_choice_compatible_no_cut_match_item_for_cut
  (key: cbor)
  (value: typ)
  (g: det_map_group)
  (f: map_constraint)
: Lemma
  (requires (
    map_group_footprint g f /\
    map_constraint_disjoint (matches_map_group_entry (t_literal key) any) f
  ))
  (ensures (
    map_group_choice_compatible_no_cut (map_group_match_item_for true key value) g
  ))
= map_group_choice_compatible_match_item_for true key value g f

val map_group_footprint_concat_consumes_all_recip
  (g1 g2: map_group)
  (f1 f2: map_constraint)
  (m: cbor_map)
: Pure (cbor_map & cbor_map)
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2 /\
    map_group_consumes_all (g1 `map_group_concat` g2) m
  ))
  (ensures (fun (m1, m2) ->
    m1 `cbor_map_disjoint` m2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 cbor_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 cbor_map_empty /\
    cbor_map_disjoint_from_footprint m1 f2 /\
    cbor_map_disjoint_from_footprint m2 f1 /\
    m1 `cbor_map_union` m2 == m
  ))

#restart-solver
let map_group_footprint_concat_consumes_all_recip'
  (g1 g2: map_group)
  (f1 f2: map_constraint)
  (m: cbor_map)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2 /\
    map_group_consumes_all (g1 `map_group_concat` g2) m
  ))
  (ensures exists m1m2 .
    (let (m1, m2) = m1m2 in
    m1 `cbor_map_disjoint` m2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 cbor_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 cbor_map_empty /\
    cbor_map_disjoint_from_footprint m1 f2 /\
    cbor_map_disjoint_from_footprint m2 f1 /\
    m1 `cbor_map_union` m2 == m
  ))
= let (_, _) = map_group_footprint_concat_consumes_all_recip g1 g2 f1 f2 m in
  ()

val matches_map_group_equiv_concat'
  (g1 g1' g2 g2': det_map_group)
  (f1 f1' f2 f2': map_constraint)
  (m: cbor_map)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g1' f1' /\
    map_group_footprint g2 f2 /\
    map_group_footprint g2'  f2' /\
    matches_map_group_equiv g1 g1' /\
    matches_map_group_equiv g2 g2' /\
    map_constraint_disjoint f1 f2 /\
    map_constraint_disjoint f1' f2' /\
    matches_map_group (map_group_concat g1 g2) m
  ))
  (ensures (
    matches_map_group (map_group_concat g1' g2') m
  ))

#restart-solver
let matches_map_group_equiv_concat
  (g1 g1' g2 g2': det_map_group)
  (f1 f1' f2 f2': map_constraint)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g1' f1' /\
    map_group_footprint g2 f2 /\
    map_group_footprint g2'  f2' /\
    matches_map_group_equiv g1 g1' /\
    matches_map_group_equiv g2 g2' /\
    map_constraint_disjoint f1 f2 /\
    map_constraint_disjoint f1' f2'
  ))
  (ensures (
    matches_map_group_equiv (map_group_concat g1 g2) (map_group_concat g1' g2')
  ))
= Classical.forall_intro (Classical.move_requires (matches_map_group_equiv_concat' g1 g1' g2 g2' f1 f1' f2 f2'));
  Classical.forall_intro (Classical.move_requires (matches_map_group_equiv_concat' g1' g1 g2' g2 f1' f1 f2' f2))

#restart-solver
let map_group_choice_compatible_match_item_for_concat_right
  (k: cbor)
  (v: typ)
  (g1 g2: det_map_group)
  (f1 f2: map_constraint)
: Lemma
  (requires (
    map_group_choice_compatible (map_group_match_item_for false k v) g1 /\
    map_group_choice_compatible (map_group_match_item_for false k v) g2 /\
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2
  ))
  (ensures (
    map_group_choice_compatible (map_group_match_item_for false k v) (map_group_concat g1 g2)
  ))
= Classical.forall_intro (Classical.move_requires (map_group_footprint_concat_consumes_all_recip' g1 g2 f1 f2))
    
#restart-solver
let map_group_choice_compatible_match_item_for_zero_or_one_right
  (cut: bool)
  (k: cbor)
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
  (k: cbor)
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

let cbor_map_in_footprint
  (m: cbor_map)
  (f: map_constraint)
: Tot prop
= forall x . Some? (cbor_map_get m x) ==> (f (x, Some?.v (cbor_map_get m x)))

#restart-solver
let matches_map_group_comm_aux'
  (g2 g3 g4: det_map_group)
  (t2 t3 t4: map_constraint)
  (m: cbor_map)
: Lemma
  (requires (
    map_group_footprint g2 t2 /\
    map_group_footprint g3 t3 /\
    map_group_footprint g4 t4 /\
    map_constraint_disjoint t3 t4 /\
    map_constraint_disjoint t2 (map_constraint_choice t3 t4) /\
    matches_map_group
      (map_group_concat g2 (map_group_concat g3 g4))
      m
  ))
  (ensures (
    matches_map_group
      (map_group_concat g3 (map_group_concat g2 g4))
      m
  ))
= let (m2, m34) = map_group_footprint_concat_consumes_all_recip g2 (map_group_concat g3 g4) t2 (map_constraint_choice t3 t4) m in
  let (m3, m4) = map_group_footprint_concat_consumes_all_recip g3 g4 t3 t4 m34 in
  assert (m `cbor_map_equal` cbor_map_union m3 (cbor_map_union m2 m4));
  map_group_footprint_consumed_disjoint g2 t2 t3 m2;
  map_group_footprint_consumed_disjoint g4 t4 t3 m4;
  map_group_footprint_elim g3 t3 m3 (cbor_map_union m2 m4);
  assert (apply_map_group_det g3 m == MapGroupDet m3 (cbor_map_union m2 m4));
  map_group_footprint_consumed_disjoint g4 t4 t2 m4;
  map_group_footprint_elim g2 t2 m2 m4;
  assert (apply_map_group_det g2 (cbor_map_union m2 m4) == MapGroupDet m2 m4);
  assert (apply_map_group_det g4 m4 == MapGroupDet m4 cbor_map_empty);
  assert (apply_map_group_det (map_group_concat g2 g4) (cbor_map_union m2 m4) ==
    MapGroupDet (cbor_map_union m2 m4) cbor_map_empty
  );
  assert (apply_map_group_det (map_group_concat g3 (map_group_concat g2 g4)) m ==
    MapGroupDet (cbor_map_union m3 (cbor_map_union m2 m4)) cbor_map_empty
  );
  ()

#restart-solver
let matches_map_group_comm_aux
  (g2 g3 g4: det_map_group)
  (t2 t3 t4: map_constraint)
  (m: cbor_map)
: Lemma
  (requires (
    map_group_footprint g2 t2 /\
    map_group_footprint g3 t3 /\
    map_group_footprint g4 t4 /\
    map_constraint_disjoint t3 t4 /\
    map_constraint_disjoint t2 (map_constraint_choice t3 t4)
  ))
  (ensures (
    matches_map_group
      (map_group_concat g2 (map_group_concat g3 g4))
      m <==>
    matches_map_group
      (map_group_concat g3 (map_group_concat g2 g4))
      m
  ))
= Classical.move_requires (matches_map_group_comm_aux' g2 g3 g4 t2 t3 t4) m;
  Classical.move_requires (matches_map_group_comm_aux' g3 g2 g4 t3 t2 t4) m

let matches_map_group_comm'
  (g1 g2 g3 g4: det_map_group)
  (t1 t2 t3 t4: map_constraint)
  (m: cbor_map)
: Lemma
  (requires (
    map_group_footprint g1 t1 /\
    map_group_footprint g2 t2 /\
    map_group_footprint g3 t3 /\
    map_group_footprint g4 t4 /\
    map_constraint_disjoint t3 t4 /\ (
    let t34 = map_constraint_choice t3 t4 in
    map_constraint_disjoint t2 t34 /\
    map_constraint_disjoint t1 (map_constraint_choice t2 t34)
  )))
  (ensures (
    matches_map_group
      (map_group_concat g1 (map_group_concat g2 (map_group_concat g3 g4)))
      m <==>
    matches_map_group
      (map_group_concat g1 (map_group_concat g3 (map_group_concat g2 g4)))
      m
  ))
= matches_map_group_comm_aux g1 g2 (map_group_concat g3 g4) t1 t2 (map_constraint_choice t3 t4) m;
  matches_map_group_comm_aux g2 (map_group_concat g1 g3) g4 t2 (map_constraint_choice t1 t3) t4 m

let matches_map_group_comm
  (g1 g2 g3 g4 g5: det_map_group)
  (t1 t2 t3 t4 t5: map_constraint)
  (m: cbor_map)
: Lemma
  (requires (
    map_group_footprint g1 t1 /\
    map_group_footprint g2 t2 /\
    map_group_footprint g3 t3 /\
    map_group_footprint g4 t4 /\
    map_group_footprint g5 t5 /\
    map_constraint_disjoint t4 t5 /\ (
    let t45 = map_constraint_choice t4 t5 in
    map_constraint_disjoint t3 t45 /\ (
    let t345 = map_constraint_choice t3 t45 in
    map_constraint_disjoint t2 t345 /\
    map_constraint_disjoint t1 (map_constraint_choice t2 t345)
  ))))
  (ensures (
    matches_map_group
      (map_group_concat g1 (map_group_concat g2 (map_group_concat g3 (map_group_concat g4 g5))))
      m <==>
    matches_map_group
      (map_group_concat g1 (map_group_concat g4 (map_group_concat g3 (map_group_concat g2 g5))))
      m
  ))
= matches_map_group_comm' g1 g2 (map_group_concat g3 g4) g5 t1 t2 (map_constraint_choice t3 t4) t5 m;
  matches_map_group_comm' (map_group_concat g1 g3) g4 g2 g5 (map_constraint_choice t1 t3) t4 t2 t5 m;
  matches_map_group_comm' g1 g4 g3 (map_group_concat g2 g5) t1 t4 t3 (map_constraint_choice t2 t5) m

unfold
let map_group_parser_spec_arg_common
  (source: det_map_group)
  (source_fp: map_constraint)
  (m: cbor_map)
: Tot prop
= 
    map_group_footprint source source_fp /\
    cbor_map_in_footprint m source_fp

unfold
let map_group_parser_spec_arg_prop
  (source: det_map_group)
  (source_fp: map_constraint)
  (x: cbor_map)
: Tot prop
= map_group_parser_spec_arg_common source source_fp x /\
  MapGroupDet? (apply_map_group_det source x)

let map_group_parser_spec_arg
  (source: det_map_group)
  (source_fp: map_constraint)
: Tot Type0
= (x: cbor_map {
    map_group_parser_spec_arg_prop source source_fp x
  })

let map_group_parser_spec_ret
  (source: det_map_group)
  (source_fp: map_constraint)
  (#target: Type0)
  (target_size: target -> Tot nat)
  (target_prop: target -> bool)
  (x: map_group_parser_spec_arg source source_fp)
: Tot Type0
= (y: target { 
    target_size y <= cbor_map_length x // not everything is parsed, especially for choice
    /\ target_prop y
  })

let map_group_parser_spec
  (source: det_map_group)
  (source_fp: map_constraint)
  (#target: Type0)
  (target_size: target -> Tot nat)
  (target_prop: target -> bool)
: Type0
= (x: map_group_parser_spec_arg source source_fp) -> Tot (map_group_parser_spec_ret source source_fp target_size target_prop x)

unfold
let map_group_serializer_spec_arg_prop
  (source: det_map_group)
  (source_fp: map_constraint)
  (x: cbor_map)
: Tot prop
= map_group_parser_spec_arg_common source source_fp x /\
  begin match apply_map_group_det source x with
  | MapGroupDet _ res -> res `cbor_map_equal` cbor_map_empty // everything is consumed
  | _ -> False
  end

let map_group_serializer_spec_ret
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target: Type0)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: map_group_parser_spec source source_fp target_size target_prop)
  (x: target { target_prop x })
: Tot Type
= (y: cbor_map {
    map_group_serializer_spec_arg_prop source source_fp y /\
    target_size x == cbor_map_length y /\
    p y == x
  })

let map_group_serializer_spec_ret_intro
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target: Type0)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: map_group_parser_spec source source_fp target_size target_prop)
  (x: target { target_prop x })
  (y: cbor_map)
  (sq1: squash (map_group_serializer_spec_arg_prop source source_fp y))
  (sq2: squash (target_size x == cbor_map_length y))
  (sq3: squash (p y == x))
: Tot (map_group_serializer_spec_ret p x)
= y

#restart-solver
let map_group_serializer_spec
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target: Type0)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: map_group_parser_spec source source_fp target_size target_prop)
: Type0
= (x: target { target_prop x }) -> Tot (map_group_serializer_spec_ret p x)

let map_group_parser_spec_domain_inj
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
: Tot prop
=
  forall (x x': cbor_map) (k: cbor) . (map_group_parser_spec_arg_prop source1 source_fp1 x /\ map_group_serializer_spec_arg_prop source1 source_fp1 x' /\ (p1 x <: target1) == p1 x' /\ cbor_map_defined k x') ==> cbor_map_defined k x

noeq
type mg_spec
  (source: det_map_group)
  (source_fp: map_constraint)
  (target: Type0)
  (inj: bool)
: Type
= {
  mg_size: target -> Tot nat;
  mg_serializable: target -> bool;
  mg_parser: map_group_parser_spec source source_fp mg_size mg_serializable;
  mg_parser_domain_inj: squash (map_group_parser_spec_domain_inj mg_parser);
  mg_serializer: map_group_serializer_spec mg_parser;
  mg_inj: squash (inj ==> (forall (c: cbor_map { map_group_serializer_spec_arg_prop source source_fp c }) . mg_serializer (mg_parser c) == c));
}

let mg_spec_ext
  (#source: det_map_group)
  (#source_fp1: map_constraint)
  (#target: Type0)
  (#inj: bool)
  (p: mg_spec source source_fp1 target inj)
  (source_fp2: map_constraint {
    map_constraint_equiv source_fp1 source_fp2
  })
  (target_size': target -> Tot nat {
    forall x . target_size' x == p.mg_size x
  })
  (target_prop': target -> bool {
    forall x . target_prop' x <==> p.mg_serializable x
  })
: mg_spec source source_fp2 target inj
= {
  mg_size = target_size';
  mg_serializable = target_prop';
  mg_parser = (p.mg_parser <: map_group_parser_spec source source_fp2 target_size' target_prop');
  mg_parser_domain_inj = ();
  mg_serializer = p.mg_serializer;
  mg_inj = ();
}

val parser_spec_map_group
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target: Type0)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: map_group_parser_spec source source_fp target_size target_prop {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
  (target_prop' : target -> bool {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64)
  })
: Tot (parser_spec (t_map source0) target target_prop')

val parser_spec_map_group_eq
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target: Type0)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: map_group_parser_spec source source_fp target_size target_prop {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
  (target_prop' : target -> bool {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64)
  })
  (w: cbor { t_map source0 w })
: Lemma
  (let x = CMap?.c (unpack w) in
    (let x' = cbor_map_filter (source_fp) x in
    map_group_parser_spec_arg_prop source source_fp x' /\
    parser_spec_map_group source0 p target_prop' w == p x'
  ))
  [SMTPat (parser_spec_map_group source0 p target_prop' w)]

#restart-solver
let serializer_spec_map_group
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target: Type0)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (#p: map_group_parser_spec source source_fp target_size target_prop)
  (s: map_group_serializer_spec p {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
  (target_prop' : target -> bool {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64)
  })
: Tot (serializer_spec (parser_spec_map_group source0 p target_prop'))
= fun z ->
  let l = s z in
  let MapGroupDet _ rem = apply_map_group_det source0 l in
  cbor_map_equiv rem cbor_map_empty;
  let res = pack (CMap l) in
  assert (t_map source0 res);
  parser_spec_map_group_eq source0 p target_prop' res;
  assert (cbor_map_equal (cbor_map_filter (source_fp) l) l);
  assert (parser_spec_map_group source0 p target_prop' res == z);
  res

let spec_map_group_serializable
  (#target: Type0)
  (sz: target -> nat)
  (ser: target -> bool)
  (x: target)
: Tot bool
= ser x &&
  sz x < pow2 64

(*
let spec_map_group_restrict
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#inj: bool)
  (p: mg_spec source source_fp target inj {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
: Tot (spec (t_map source0) target false)
= {
  serializable = spec_map_group_serializable p.mg_size p.mg_serializable;
  parser = parser_spec_map_group source0 p.mg_parser _;
  serializer = serializer_spec_map_group source0 p.mg_serializer _;
  parser_inj = ();
}
*)

let spec_map_group_inj
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target: Type0)
  (#inj: bool)
  (p: mg_spec source source_fp target inj {
    map_group_footprint source source_fp
  })
  (c: cbor { t_map source c })
: Lemma
  (requires inj)
  (ensures serializer_spec_map_group source p.mg_serializer (spec_map_group_serializable p.mg_size p.mg_serializable) (parser_spec_map_group source p.mg_parser (spec_map_group_serializable p.mg_size p.mg_serializable) c) == c)
= let CMap l = unpack c in
  let f = source_fp in
  cbor_map_split f l;
  let l' = cbor_map_filter f l in
  map_group_footprint_elim source source_fp l' (cbor_map_filter (U.notp f) l);
  assert (cbor_map_equal l' l)

let spec_map_group
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target: Type0)
  (#inj: bool)
  (p: mg_spec source source_fp target inj {
    map_group_footprint source source_fp
  })
: Tot (spec (t_map source) target inj)
= {
  serializable = spec_map_group_serializable p.mg_size p.mg_serializable;
  parser = parser_spec_map_group source p.mg_parser _;
  serializer = serializer_spec_map_group source p.mg_serializer _;
  parser_inj = Classical.forall_intro (Classical.move_requires (spec_map_group_inj p));
}

let map_group_parser_spec_bij
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target1: Type0)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (f: map_group_parser_spec source source_fp target_size1 target_prop1)
  (#target2: Type0)
  (target_size2: target2 -> Tot nat)
  (target_prop2: target2 -> bool)
  (bij: bijection target1 target2 {
    (forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)) /\
    (forall x2 . target_prop2 x2 <==> target_prop1 (bij.bij_to_from x2))
  })
: Tot (map_group_parser_spec source source_fp target_size2 target_prop2)
= fun x -> bij.bij_from_to (f x)

let map_group_serializer_spec_bij
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target1: Type0)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#f: map_group_parser_spec source source_fp target_size1 target_prop1)
  (s: map_group_serializer_spec f)
  (#target2: Type0)
  (target_size2: target2 -> Tot nat)
  (target_prop2: target2 -> bool)
  (bij: bijection target1 target2 {
    (forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)) /\
    (forall x2 . target_prop2 x2 <==> target_prop1 (bij.bij_to_from x2))
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_bij f target_size2 target_prop2 bij))
= fun x -> s (bij.bij_to_from x)

let mg_spec_bij_size
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target1: Type0)
  (#inj: bool)
  (f: mg_spec source source_fp target1 inj)
  (#target2: Type0)
  (bij: bijection target1 target2)
  (x: target2)
: Tot nat
= f.mg_size (bij.bij_to_from x)

let mg_spec_bij_serializable
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target1: Type0)
  (#inj: bool)
  (f: mg_spec source source_fp target1 inj)
  (#target2: Type0)
  (bij: bijection target1 target2)
  (x: target2)
: Tot bool
= f.mg_serializable (bij.bij_to_from x)

let mg_spec_bij
  (#source: det_map_group)
  (#source_fp: map_constraint)
  (#target1: Type0)
  (#inj: bool)
  (f: mg_spec source source_fp target1 inj)
  (#target2: Type0)
  (bij: bijection target1 target2)
: Tot (mg_spec source source_fp target2 inj)
= {
  mg_size = mg_spec_bij_size f bij;
  mg_serializable = mg_spec_bij_serializable f bij;
  mg_parser = map_group_parser_spec_bij f.mg_parser _ _ bij;
  mg_parser_domain_inj = ();
  mg_serializer = map_group_serializer_spec_bij f.mg_serializer _ _ bij;
  mg_inj = ();
}

let map_constraint_empty : map_constraint =
  matches_map_group_entry t_always_false any

let map_group_parser_spec_nop
  (target_size: unit -> Tot nat {
    forall x . target_size x == 0
  })
  (target_prop: unit -> bool {
    forall x . target_prop x
  })
: map_group_parser_spec map_group_nop map_constraint_empty target_size target_prop
= fun x -> ()

let map_group_serializer_spec_nop
  (target_size: unit -> Tot nat {
    forall x . target_size x == 0
  })
  (target_prop: unit -> bool {
    forall x . target_prop x
  })
: map_group_serializer_spec (map_group_parser_spec_nop target_size target_prop)
= fun _ -> cbor_map_empty

let mg_spec_size_nop () : Tot nat = 0

let mg_spec_serializable_nop () : Tot bool = true

let mg_spec_nop :
  mg_spec map_group_nop map_constraint_empty unit true
= {
  mg_size = mg_spec_size_nop;
  mg_serializable = mg_spec_serializable_nop;
  mg_parser = map_group_parser_spec_nop _ _;
  mg_parser_domain_inj = ();
  mg_serializer = map_group_serializer_spec_nop _ _;
  mg_inj = ()
}

let map_group_parser_spec_match_item_for
  (cut: bool)
  (k: cbor)
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> bool)
  (p: parser_spec ty target target_prop)
  (target_size: target -> Tot nat {
    forall x . target_size x == 1
  })
: Tot (map_group_parser_spec (map_group_match_item_for cut k ty) (map_group_match_item_for_footprint cut k ty) target_size target_prop)
= fun x ->
  let Some v = cbor_map_get x k in
  cbor_map_equiv x (cbor_map_singleton k v);
  p v

let map_group_serializer_spec_match_item_for
  (cut: bool)
  (k: cbor)
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> bool)
  (#p: parser_spec ty target target_prop)
  (s: serializer_spec p)
  (target_size: target -> Tot nat {
    forall x . target_size x == 1
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_match_item_for cut k p target_size))
= fun x ->
  map_group_footprint_match_item_for cut k ty;
  let v = s x in
  let res = cbor_map_singleton k v in
  let MapGroupDet _ rem = apply_map_group_det (map_group_match_item_for cut k ty) res in
  cbor_map_equiv rem cbor_map_empty;
  res

let mg_spec_match_item_for_size
  (target: Type)
  (x: target)
: Tot nat
= 1

let mg_spec_match_item_for
  (cut: bool)
  (k: cbor)
  (#ty: typ)
  (#target: Type)
  (#inj: bool)
  (p: spec ty target inj)
: Tot (mg_spec (map_group_match_item_for cut k ty) (map_group_match_item_for_footprint cut k ty) target inj)
= {
  mg_size = mg_spec_match_item_for_size target;
  mg_serializable = p.serializable;
  mg_parser = map_group_parser_spec_match_item_for cut k p.parser _;
  mg_parser_domain_inj = ();
  mg_serializer = map_group_serializer_spec_match_item_for cut k p.serializer _;
  mg_inj = ();
}

val map_group_concat_footprint_disjoint
  (source1: det_map_group)
  (source_fp1: map_constraint)
  (source2: det_map_group)
  (source_fp2: map_constraint {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    map_constraint_disjoint source_fp1 source_fp2
  })
  (m: cbor_map {
    map_group_serializer_spec_arg_prop (map_group_concat source1 source2) (source_fp1 `map_constraint_choice` source_fp2) m
  })
: Lemma
  (ensures (
    let m1 = cbor_map_filter (source_fp1) m in
    let m2 = cbor_map_filter (source_fp2) m in
    cbor_map_disjoint m1 m2 /\
    cbor_map_union m1 m2 == m /\
    apply_map_group_det source1 m1 == MapGroupDet m1 cbor_map_empty /\
    apply_map_group_det source1 m == MapGroupDet m1 m2 /\
    apply_map_group_det source2 m2 == MapGroupDet m2 cbor_map_empty
  ))

let map_constraint_disjoint_domains
  (fp1 fp2: map_constraint)
: Tot prop
= forall kv1 kv2 . (fp1 kv1 /\ fp2 kv2) ==> fst kv1 <> fst kv2

let map_constraint_disjoint_domains_implies_disjoint
  (fp1 fp2: map_constraint)
: Lemma
  (requires (map_constraint_disjoint_domains fp1 fp2))
  (ensures (map_constraint_disjoint fp1 fp2))
= ()

val map_group_parser_spec_concat
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (s1: map_group_serializer_spec p1)
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (#p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (s2: map_group_serializer_spec p2)
  (target_size: (target1 & target2) -> Tot nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    (
      (map_constraint_disjoint source_fp1 source_fp2 /\
        map_group_parser_spec_domain_inj p1 /\
        map_group_parser_spec_domain_inj p2
      ) \/ map_constraint_disjoint_domains source_fp1 source_fp2 // this disjunction is provided for the future, if we ever want domain_inj to be governed by a Boolean argument on mg_spec rather than always holding.
    ) /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
  (target_prop: (target1 & target2) -> bool {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x) /\ cbor_map_disjoint (s1 (fst x)) (s2 (snd x)))
  })
: Tot (map_group_parser_spec (map_group_concat source1 source2) (source_fp1 `map_constraint_choice` source_fp2) target_size target_prop)

#restart-solver
val map_group_parser_spec_concat_eq
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (s1: map_group_serializer_spec p1)
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (#p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (s2: map_group_serializer_spec p2)
  (target_size: (target1 & target2) -> Tot nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    (
      (map_constraint_disjoint source_fp1 source_fp2 /\
        map_group_parser_spec_domain_inj p1 /\
        map_group_parser_spec_domain_inj p2
      ) \/ map_constraint_disjoint_domains source_fp1 source_fp2
    ) /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
  (target_prop: (target1 & target2) -> bool {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x) /\ cbor_map_disjoint (s1 (fst x)) (s2 (snd x)))
  })
  (l: map_group_parser_spec_arg (map_group_concat source1 source2) (source_fp1 `map_constraint_choice` source_fp2))
: Lemma
  (
    let l1 = cbor_map_filter (source_fp1) l in
    let l2 = cbor_map_filter (source_fp2) l in
    map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
    map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
    map_group_parser_spec_concat s1 s2 target_size target_prop l == (p1 l1, p2 l2)
  )
  [SMTPat (map_group_parser_spec_concat s1 s2 target_size target_prop l)]

#restart-solver
let map_group_serializer_spec_concat
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (s1: map_group_serializer_spec p1)
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (#p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (s2: map_group_serializer_spec p2)
  (target_size: (target1 & target2) -> Tot nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    (
      (map_constraint_disjoint source_fp1 source_fp2 /\
        map_group_parser_spec_domain_inj p1 /\
        map_group_parser_spec_domain_inj p2
      ) \/ map_constraint_disjoint_domains source_fp1 source_fp2
    ) /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
  (target_prop: (target1 & target2) -> bool {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x) /\
      cbor_map_disjoint (s1 (fst x)) (s2 (snd x))
    )
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_concat s1 s2 target_size target_prop))
= fun x ->
    map_group_footprint_concat source1 source2 source_fp1 source_fp2;
    let (x1, x2) = x in
    let l1 = s1 x1 in
    let l2 = s2 x2 in
    let res = l1 `cbor_map_union` l2 in
    assert (cbor_map_disjoint l1 l2);
    map_group_footprint_concat_consumes_all source1 source2 source_fp1 source_fp2 (l1) (l2);
    assert (cbor_map_in_footprint (l1) (source_fp1 `map_constraint_choice` source_fp2));
    assert (cbor_map_in_footprint (l2) (source_fp1 `map_constraint_choice` source_fp2));
    assert (cbor_map_in_footprint (l1 `cbor_map_union` l2) (source_fp1 `map_constraint_choice` source_fp2));
    assert (map_group_serializer_spec_arg_prop (source1 `map_group_concat` source2) (source_fp1 `map_constraint_choice` source_fp2) res);
    let f1 = source_fp1 in
    let f2 = source_fp2 in
    let f = (source_fp1 `map_constraint_choice` source_fp2) in
    cbor_map_filter_ext (f1 `orp` f2) f res;
    assert (cbor_map_equal l1 (cbor_map_filter f1 l1));
    assert (cbor_map_equal cbor_map_empty (cbor_map_filter f1 l2));
    assert (cbor_map_equal l1 (cbor_map_filter f1 res));
    assert (cbor_map_equal l2 (cbor_map_filter f2 l2));
    assert (cbor_map_equal cbor_map_empty (cbor_map_filter f2 l1));
    assert (cbor_map_equal l2 (cbor_map_filter f2 res));
    assert (map_group_parser_spec_concat s1 s2 target_size target_prop res == x);
    cbor_map_length_disjoint_union l1 l2;
    res

let mg_spec_concat_size
  (#target1: Type)
  (p1: target1 -> nat)
  (#target2: Type)
  (p2: target2 -> nat)
  (x: (target1 & target2))
: Tot nat
= p1 (fst x) + p2 (snd x)

let mg_spec_concat_serializable
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (s1: map_group_serializer_spec p1)
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (#p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (s2: map_group_serializer_spec p2)
  (x: (target1 & target2))
: Tot bool
= target_prop1 (fst x) && target_prop2 (snd x) && cbor_map_disjoint_tot (s1 (fst x)) (s2 (snd x))

let mg_spec_concat_inj
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1)
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#inj2: bool)
  (p2: mg_spec source2 source_fp2 target2 inj2 {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    map_constraint_disjoint source_fp1 source_fp2
  })
  (m: cbor_map { map_group_serializer_spec_arg_prop (map_group_concat source1 source2) (source_fp1 `map_constraint_choice` source_fp2) m })
: Lemma
  (requires (inj1 && inj2))
  (ensures (
    map_group_serializer_spec_concat p1.mg_serializer p2.mg_serializer (mg_spec_concat_size p1.mg_size p2.mg_size) (mg_spec_concat_serializable p1.mg_serializer p2.mg_serializer) (map_group_parser_spec_concat p1.mg_serializer p2.mg_serializer (mg_spec_concat_size p1.mg_size p2.mg_size) (mg_spec_concat_serializable p1.mg_serializer p2.mg_serializer) m) == m
  ))
= map_group_concat_footprint_disjoint source1 source_fp1 source2 source_fp2 m

let mg_spec_concat_domain_inj'
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1)
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#inj2: bool)
  (p2: mg_spec source2 source_fp2 target2 inj2 {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    map_constraint_disjoint source_fp1 source_fp2
  })
  (x x' : cbor_map)
  (k: cbor)
: Lemma
  (requires (
    map_group_parser_spec_arg_prop (map_group_concat source1 source2) (map_constraint_choice source_fp1 source_fp2) x /\
    map_group_serializer_spec_arg_prop (map_group_concat source1 source2) (map_constraint_choice source_fp1 source_fp2) x' /\
    (map_group_parser_spec_concat p1.mg_serializer p2.mg_serializer (mg_spec_concat_size p1.mg_size p2.mg_size) (mg_spec_concat_serializable p1.mg_serializer p2.mg_serializer) x <: (target1 & target2)) == map_group_parser_spec_concat p1.mg_serializer p2.mg_serializer (mg_spec_concat_size p1.mg_size p2.mg_size) (mg_spec_concat_serializable p1.mg_serializer p2.mg_serializer) x' /\
    cbor_map_defined k x'
  ))
  (ensures (
    cbor_map_defined k x
  ))
= map_group_parser_spec_concat_eq p1.mg_serializer p2.mg_serializer (mg_spec_concat_size p1.mg_size p2.mg_size) (mg_spec_concat_serializable p1.mg_serializer p2.mg_serializer) x;
  map_group_parser_spec_concat_eq p1.mg_serializer p2.mg_serializer (mg_spec_concat_size p1.mg_size p2.mg_size) (mg_spec_concat_serializable p1.mg_serializer p2.mg_serializer) x';
  let x1 = cbor_map_filter source_fp1 x in
  let x2 = cbor_map_filter source_fp2 x in
  assert (cbor_map_equal' x (cbor_map_union x1 x2));
  let x1' = cbor_map_filter source_fp1 x' in
  let x2' = cbor_map_filter source_fp2 x' in
  assert (cbor_map_equal' x' (cbor_map_union x1' x2'));
  let (x1_, x2_) = map_group_footprint_concat_consumes_all_recip source1 source2 source_fp1 source_fp2 x' in
  map_group_footprint_elim source1 source_fp1 x1_ x2_;
  assert (cbor_map_equal' x1_ x1');
  assert (cbor_map_equal' x2_ x2');
  assert (p1.mg_parser x1 == p1.mg_parser x1');
  assert (map_group_parser_spec_arg_common source1 source_fp1 x1');
  assert (MapGroupDet? (apply_map_group_det source1 x1'));
  assert (map_group_serializer_spec_arg_prop source1 source_fp1 x1');
  assert (forall k . cbor_map_defined k x1' ==> cbor_map_defined k x1);
  assert (p2.mg_parser x2 == p2.mg_parser x2');
  assert (map_group_parser_spec_arg_common source2 source_fp2 x2');
  assert (MapGroupDet? (apply_map_group_det source2 x2'));
  assert (map_group_serializer_spec_arg_prop source2 source_fp2 x2');
  assert (forall k . cbor_map_defined k x2' ==> cbor_map_defined k x2);
  assert (cbor_map_defined k x' ==> cbor_map_defined k x);
  ()

let mg_spec_concat_domain_inj
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1)
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#inj2: bool)
  (p2: mg_spec source2 source_fp2 target2 inj2 {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    map_constraint_disjoint source_fp1 source_fp2
  })
  (x x' : cbor_map)
  (k: cbor)
: Lemma
  (ensures (
    map_group_parser_spec_arg_prop (map_group_concat source1 source2) (map_constraint_choice source_fp1 source_fp2) x /\
    map_group_serializer_spec_arg_prop (map_group_concat source1 source2) (map_constraint_choice source_fp1 source_fp2) x' /\
    (map_group_parser_spec_concat p1.mg_serializer p2.mg_serializer (mg_spec_concat_size p1.mg_size p2.mg_size) (mg_spec_concat_serializable p1.mg_serializer p2.mg_serializer) x <: (target1 & target2)) == map_group_parser_spec_concat p1.mg_serializer p2.mg_serializer (mg_spec_concat_size p1.mg_size p2.mg_size) (mg_spec_concat_serializable p1.mg_serializer p2.mg_serializer) x' /\
    cbor_map_defined k x'
  ) ==> (
    cbor_map_defined k x
  ))
= Classical.move_requires (mg_spec_concat_domain_inj' p1 p2 x x') k

let mg_spec_concat
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1)
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#inj2: bool)
  (p2: mg_spec source2 source_fp2 target2 inj2 {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    map_constraint_disjoint source_fp1 source_fp2
  })
: Tot (mg_spec (map_group_concat source1 source2) (source_fp1 `map_constraint_choice` source_fp2) (target1 & target2) (inj1 && inj2))
= {
  mg_size = mg_spec_concat_size p1.mg_size p2.mg_size;
  mg_serializable = mg_spec_concat_serializable p1.mg_serializer p2.mg_serializer;
  mg_parser = map_group_parser_spec_concat p1.mg_serializer p2.mg_serializer _ _;
  mg_parser_domain_inj = Classical.forall_intro_3 (mg_spec_concat_domain_inj p1 p2);
  mg_serializer = map_group_serializer_spec_concat p1.mg_serializer p2.mg_serializer _ _;
  mg_inj = Classical.forall_intro (Classical.move_requires (mg_spec_concat_inj p1 p2));
}

val map_group_parser_spec_choice
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2 {
    map_group_footprint source2 source_fp2
  })
  (target_size: (target1 `either` target2) -> Tot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> bool {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })  
: Tot (map_group_parser_spec (map_group_choice source1 source2) (source_fp1 `map_constraint_choice` source_fp2) target_size target_prop)

val map_group_parser_spec_choice_eq
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2 {
    map_group_footprint source2 source_fp2
  })
  (target_size: (target1 `either` target2) -> Tot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> bool {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })  
  (l: map_group_parser_spec_arg (map_group_choice source1 source2) (source_fp1 `map_constraint_choice` source_fp2))
: Lemma
    (requires True)
    (ensures (
        let l' = map_group_parser_spec_choice p1 p2 target_size target_prop l in
        let f1 = source_fp1 in
        let f2 = source_fp2 in
        let l1 = cbor_map_filter f1 l in
        let l2 = cbor_map_filter f2 l in
        let test = MapGroupDet? (apply_map_group_det source1 (l1)) in
        l1 == cbor_map_filter (source_fp1) (l) /\
        l2 == cbor_map_filter (source_fp2) (l) /\
        (test ==> (
          map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
          (l' <: (target1 `either` target2)) == Inl (p1 l1)
        )) /\
        ((~ test) ==> (
          map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
          (l' <: (target1 `either` target2)) == Inr (p2 l2)
        ))
    ))
    [SMTPat (map_group_parser_spec_choice p1 p2 target_size target_prop l)]

#restart-solver
val map_group_serializer_spec_choice
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (s1: map_group_serializer_spec p1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (#p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (s2: map_group_serializer_spec p2 {
    map_group_footprint source2 source_fp2 /\
    map_group_choice_compatible source1 source2
  })
  (target_size: (target1 `either` target2) -> Tot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> bool {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })  
: Tot (map_group_serializer_spec (map_group_parser_spec_choice p1 p2 target_size target_prop))

#restart-solver
val map_group_serializer_spec_choice_eq
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (s1: map_group_serializer_spec p1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (#p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (s2: map_group_serializer_spec p2 {
    map_group_footprint source2 source_fp2 /\
    map_group_choice_compatible source1 source2
  })
  (target_size: (target1 `either` target2) -> Tot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> bool {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })
  (x: (target1 `either` target2) { target_prop x })
: Lemma
  (ensures (map_group_serializer_spec_choice s1 s2 target_size target_prop x <: cbor_map) == begin
      match x with
      | Inl y -> s1 y
      | Inr y -> s2 y
  end)
  [SMTPat (map_group_serializer_spec_choice s1 s2 target_size target_prop x)]

let mg_spec_choice_size
  (#target1: Type)
  (p1: target1 -> nat)
  (#target2: Type)
  (p2: target2 -> nat)
  (x: either target1 target2)
: Tot nat
= match x with
  | Inl x1 -> p1 x1
  | Inr x2 -> p2 x2

let mg_spec_choice_serializable
  (#target1: Type)
  (p1: target1 -> bool)
  (#target2: Type)
  (p2: target2 -> bool)
  (x: either target1 target2)
: Tot bool
= match x with
  | Inl x1 -> p1 x1
  | Inr x2 -> p2 x2

val mg_spec_choice_inj
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#inj2: bool)
  (p2: mg_spec source2 source_fp2 target2 inj2 {
    map_group_footprint source2 source_fp2 /\
    map_group_choice_compatible source1 source2
  })
  (c: cbor_map { map_group_serializer_spec_arg_prop (map_group_choice source1 source2) (map_constraint_choice source_fp1 source_fp2) c })
: Lemma
  (requires (inj1 && inj2))
  (ensures map_group_serializer_spec_choice p1.mg_serializer p2.mg_serializer (mg_spec_choice_size p1.mg_size p2.mg_size) (mg_spec_choice_serializable p1.mg_serializable p2.mg_serializable) (map_group_parser_spec_choice p1.mg_parser p2.mg_parser (mg_spec_choice_size p1.mg_size p2.mg_size) (mg_spec_choice_serializable p1.mg_serializable p2.mg_serializable) c) == c)

val mg_spec_choice_domain_inj
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#inj2: bool)
  (p2: mg_spec source2 source_fp2 target2 inj2 {
    map_group_footprint source2 source_fp2 /\
    map_group_choice_compatible source1 source2
  })
  (x x' : cbor_map)
  (k: cbor)
: Lemma
  (ensures (
    map_group_parser_spec_arg_prop (map_group_choice source1 source2) (map_constraint_choice source_fp1 source_fp2) x /\
    map_group_serializer_spec_arg_prop (map_group_choice source1 source2) (map_constraint_choice source_fp1 source_fp2) x' /\
    (map_group_parser_spec_choice p1.mg_parser p2.mg_parser (mg_spec_choice_size p1.mg_size p2.mg_size) (mg_spec_choice_serializable p1.mg_serializable p2.mg_serializable) x <: (either target1 target2)) == map_group_parser_spec_choice p1.mg_parser p2.mg_parser (mg_spec_choice_size p1.mg_size p2.mg_size) (mg_spec_choice_serializable p1.mg_serializable p2.mg_serializable) x' /\
    cbor_map_defined k x'
  ) ==> (
    cbor_map_defined k x
  ))

let mg_spec_choice
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#inj2: bool)
  (p2: mg_spec source2 source_fp2 target2 inj2 {
    map_group_footprint source2 source_fp2 /\
    map_group_choice_compatible source1 source2
  })
: Tot (mg_spec (map_group_choice source1 source2) (source_fp1 `map_constraint_choice` source_fp2) (either target1 target2) (inj1 && inj2))
= {
  mg_size = mg_spec_choice_size p1.mg_size p2.mg_size;
  mg_serializable = mg_spec_choice_serializable p1.mg_serializable p2.mg_serializable;
  mg_parser = map_group_parser_spec_choice p1.mg_parser p2.mg_parser _ _;
  mg_parser_domain_inj = Classical.forall_intro_3 (mg_spec_choice_domain_inj p1 p2);
  mg_serializer = map_group_serializer_spec_choice p1.mg_serializer p2.mg_serializer _ _;
  mg_inj = Classical.forall_intro (Classical.move_requires (mg_spec_choice_inj p1 p2));
}

let map_group_footprint_disjoint_productive_choice_compatible
  (source1 source2: det_map_group)
  (source_fp1 source_fp2: map_constraint)
: Lemma
  (requires (
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    map_constraint_disjoint source_fp1 source_fp2 /\
    MapGroupFail? (apply_map_group_det source1 cbor_map_empty)
  ))
  (ensures (
    map_group_choice_compatible source1 source2
  ))
= map_group_choice_compatible_intro source1 source2 (fun x ->
    if x = cbor_map_empty
    then ()
    else begin
      map_group_footprint_consumes_all source2 source_fp2 x;
      map_group_footprint_consumed_disjoint source2 source_fp2 source_fp1 x;
      map_group_footprint_elim source1 source_fp1 cbor_map_empty x
    end
  )

let map_group_size_zero_or_one
  (#target1: Type)
  (sz: target1 -> nat)
  (x: option target1)
: nat
= match x with
  | None -> 0
  | Some x -> sz x

let map_group_serializable_zero_or_one
  (#target1: Type)
  (sz: target1 -> bool)
  (x: option target1)
: bool
= match x with
  | None -> true
  | Some x -> sz x

let bij_from_either_unit_to_option
  (t: Type)
: Tot (bijection (either t unit) (option t))
=
      {
        bij_from_to = (fun x -> match x with Inl x -> Some x | _ -> None);
        bij_to_from = (fun x -> match x with Some x -> Inl x | _ -> Inr ());
        bij_from_to_from = ();
        bij_to_from_to = ();
      }

let map_group_parser_spec_zero_or_one
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#target_size1: target1 -> nat)
  (#target_ser1: target1 -> bool)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_ser1)
  (_: squash (
    map_group_footprint source1 source_fp1 /\
    MapGroupFail? (apply_map_group_det source1 cbor_map_empty)
  ))
: Tot (map_group_parser_spec (map_group_zero_or_one source1) source_fp1 (map_group_size_zero_or_one target_size1) (map_group_serializable_zero_or_one target_ser1))
= map_group_parser_spec_bij
    (map_group_parser_spec_choice
      p1
      mg_spec_nop.mg_parser
      (mg_spec_choice_size
        target_size1
        mg_spec_nop.mg_size
      )
      (mg_spec_choice_serializable
        target_ser1
        mg_spec_nop.mg_serializable
      )
    )
    (map_group_size_zero_or_one target_size1)
    (map_group_serializable_zero_or_one target_ser1)
    (bij_from_either_unit_to_option _)

let mg_spec_zero_or_one
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1 {
    map_group_footprint source1 source_fp1 /\
    MapGroupFail? (apply_map_group_det source1 cbor_map_empty)
  })
: Tot (mg_spec (map_group_zero_or_one source1) source_fp1 (option target1) inj1)
= map_group_footprint_disjoint_productive_choice_compatible source1 map_group_nop source_fp1 map_constraint_empty;
  mg_spec_ext
    (mg_spec_bij
      (mg_spec_choice p1 mg_spec_nop)
      (bij_from_either_unit_to_option _)
    )
    source_fp1
    (map_group_size_zero_or_one p1.mg_size)
    (map_group_serializable_zero_or_one p1.mg_serializable)

let mg_spec_zero_or_one_parser_eq
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1 {
    map_group_footprint source1 source_fp1 /\
    MapGroupFail? (apply_map_group_det source1 cbor_map_empty)
  })
: Lemma
  (ensures ((mg_spec_zero_or_one p1).mg_parser == map_group_parser_spec_zero_or_one p1.mg_parser ()))
  [SMTPat (mg_spec_zero_or_one p1)]
= assert_norm ((mg_spec_zero_or_one p1).mg_parser == map_group_parser_spec_zero_or_one p1.mg_parser ())

let map_group_zero_or_more_match_item_length
  (#tkey #tvalue: Type)
  (x: Map.t tkey (list tvalue))
: Tot nat
= Map.length x

let map_entry_serializable
  (#tkey #tvalue: Type)
  (#key: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (#value: typ)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (x: (tkey & list tvalue))
: Tot bool
= pkey.serializable (fst x) &&
  List.Tot.length (snd x) = 1 &&
  pvalue.serializable (List.Tot.hd (snd x)) &&
  not (except (pkey.serializer (fst x), pvalue.serializer (List.Tot.hd (snd x))))

let mk_map_singleton
  (#tkey #tvalue: Type)
  (#key: typ)
  (pkey: spec key tkey true)
  (x: tkey { pkey.serializable x })
  (y: tvalue)
: Tot (Map.t tkey (list tvalue))
= Map.singleton x
      (fun (k: tkey) ->
        if pkey.serializable k
        then begin
          assert (pkey.serializer x == pkey.serializer k ==> pkey.parser (pkey.serializer x) == pkey.parser (pkey.serializer k));
          pkey.serializer x = pkey.serializer k
        end
        else false
      )
      [y]

let map_group_footprint_filtered_table
  (key value: typ)
  (except: map_constraint)
: Lemma
  (map_group_footprint (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
= ()

let map_group_filtered_table_ext
  (key value: typ)
  (except: map_constraint)
  (key'  value' : typ)
  (except': map_constraint)
: Lemma
  (requires (
    typ_equiv key key' /\
    typ_equiv value value' /\
    map_constraint_equiv except except'
  ))
  (ensures (
    map_group_filtered_table key value except == map_group_filtered_table key' value' except'
  ))
= map_group_filter_ext
    (Util.notp (Util.andp (matches_map_group_entry key value) (Util.notp except)))
    (Util.notp (Util.andp (matches_map_group_entry key' value') (Util.notp except')))

let map_group_filtered_table_no_except
  (key value: typ)
: Lemma
  (map_group_filtered_table key value map_constraint_empty == map_group_zero_or_more (map_group_match_item false key value))
= map_group_zero_or_more_match_item_filter key value;
  map_group_filter_ext
    (Util.notp (matches_map_group_entry key value))
    (Util.notp (Util.andp (matches_map_group_entry key value) (Util.notp map_constraint_empty)))

let map_group_zero_or_more_match_item_parser_op
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: map_group_parser_spec_arg (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
  (accu: Map.t tkey (list tvalue))
  (x: cbor)
: Tot (Map.t tkey (list tvalue))
= match cbor_map_get m x with
  | None -> accu
  | Some y ->
(*  
    if except (x, y)
    then accu
    else if value y
    then 
*)    
    Map.union accu (mk_map_singleton pkey (pkey.parser x) (pvalue.parser y))
//    else accu

let map_group_zero_or_more_match_item_parser_op_comm
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: map_group_parser_spec_arg (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
  (accu: Map.t tkey (list tvalue))
  (x1 x2: cbor)
: Lemma
  (ensures (map_group_zero_or_more_match_item_parser_op pkey pvalue except m (map_group_zero_or_more_match_item_parser_op pkey pvalue except m accu x1) x2 `Map.equal` map_group_zero_or_more_match_item_parser_op pkey pvalue except m (map_group_zero_or_more_match_item_parser_op pkey pvalue except m accu x2) x1
  ))
  [SMTPat (map_group_zero_or_more_match_item_parser_op pkey pvalue except m (map_group_zero_or_more_match_item_parser_op pkey pvalue except m accu x1) x2)]
= ()

let rec list_fold_map_group_zero_or_more_match_item_parser_op_mem
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: map_group_parser_spec_arg (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
  (accu: Map.t tkey (list tvalue))
  (l: list cbor)
  (k: tkey)
  (v: list tvalue)
: Lemma
  (ensures (
    let m' = List.Tot.fold_left (map_group_zero_or_more_match_item_parser_op pkey pvalue except m) accu l in
    (Map.get m' k == Some v <==> (match Map.get accu k with
    | Some v_ -> v_ == v
    | None ->
      pkey.serializable k /\
      List.Tot.memP (pkey.serializer k) l /\
      begin match cbor_map_get m (pkey.serializer k) with
      | None -> False
      | Some v' ->
        value v' /\
        (~ (except (pkey.serializer k, v'))) /\
        [pvalue.parser v'] == v
      end
    ))
  ))
  (decreases l)
=   begin match l with
    | [] -> ()
    | a :: q ->
      list_fold_map_group_zero_or_more_match_item_parser_op_mem pkey pvalue except m (map_group_zero_or_more_match_item_parser_op pkey pvalue except m accu a) q k v
    end

let map_group_zero_or_more_match_item_parser_op_length
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: map_group_parser_spec_arg (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
  (accu: Map.t tkey (list tvalue))
  (l: cbor)
: Lemma
  (ensures (
    let m' = (map_group_zero_or_more_match_item_parser_op pkey pvalue except m) accu l in
    Map.length m' <= Map.length accu + 1
  ))
= match cbor_map_get m l with
  | None -> ()
  | Some y ->
    if value y
    then
      if except (l, y)
      then ()
      else if Map.defined (pkey.parser l) accu
      then assert (map_group_zero_or_more_match_item_parser_op pkey pvalue except m accu l `Map.equal` accu)
      else Map.length_disjoint_union accu (mk_map_singleton pkey (pkey.parser l) (pvalue.parser y))
    else ()

let rec list_fold_map_group_zero_or_more_match_item_parser_length
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: map_group_parser_spec_arg (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
  (accu: Map.t tkey (list tvalue))
  (l: list cbor)
: Lemma
  (ensures (
    let m' = List.Tot.fold_left (map_group_zero_or_more_match_item_parser_op pkey pvalue except m) accu l in
    Map.length m' <= Map.length accu + List.Tot.length l
  ))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    map_group_zero_or_more_match_item_parser_op_length pkey pvalue except m accu a;
    list_fold_map_group_zero_or_more_match_item_parser_length pkey pvalue except m (map_group_zero_or_more_match_item_parser_op pkey pvalue except m accu a) q

let map_group_zero_or_more_match_item_parser'
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: map_group_parser_spec_arg (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
: Tot (Map.t tkey (list tvalue))
= cbor_map_fold (map_group_zero_or_more_match_item_parser_op pkey pvalue except m) (Map.empty _ _) m

let map_group_zero_or_more_match_item_parser'_mem
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: map_group_parser_spec_arg (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
  (kv: (tkey & list tvalue))
: Lemma
  (ensures (
    let m' = map_group_zero_or_more_match_item_parser' pkey pvalue except m in
    (Map.mem kv m' <==> (
      let (k, v) = kv in
      pkey.serializable k /\
      exists (kv': (cbor & cbor)) . cbor_map_mem kv' m /\
      fst kv' == pkey.serializer k /\
      value (snd kv') /\
      (~ (except (pkey.serializer k, snd kv'))) /\
      [pvalue.parser (snd kv')] == v
    ))
  ))
  [SMTPat (Map.mem kv (map_group_zero_or_more_match_item_parser' pkey pvalue except m))]
= let l = cbor_map_key_list m in
  cbor_map_fold_eq (map_group_zero_or_more_match_item_parser_op pkey pvalue except m) (Map.empty _ _) m l;
  list_fold_map_group_zero_or_more_match_item_parser_op_mem pkey pvalue except m (Map.empty _ _) l (fst kv) (snd kv)

let map_group_zero_or_more_match_item_parser'_length
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: map_group_parser_spec_arg (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
: Lemma
  (ensures (
    Map.length (map_group_zero_or_more_match_item_parser' pkey pvalue except m) <= cbor_map_length m
  ))
  [SMTPat (Map.length (map_group_zero_or_more_match_item_parser' pkey pvalue except m))]
= let l = cbor_map_key_list m in
  cbor_map_fold_eq (map_group_zero_or_more_match_item_parser_op pkey pvalue except m) (Map.empty _ _) m l;
  list_fold_map_group_zero_or_more_match_item_parser_length pkey pvalue except m (Map.empty _ _) l

let map_group_zero_or_more_match_item_serializable
    (#key: typ)
    (#tkey: Type0)
    (sp1: (spec key tkey true))  
    (#value: typ)
    (#tvalue: Type0)
    (#inj: bool)
    (sp2: (spec value tvalue inj))
    (except: map_constraint)
:  (x: Map.t tkey (list tvalue)) ->
  Tot bool
= Map.for_all (map_entry_serializable ( sp1) ( sp2) except)

let map_constraint_value_injective
  (#tvalue: Type)
  (#value: typ)
  (#serializable: tvalue -> bool)
  (key: typ)
  (pvalue: parser_spec value tvalue serializable)
  (except: map_constraint)
: Tot prop
= forall (k v1 v2: cbor) . (key k /\ value v1 /\ value v2 /\ pvalue v1 == pvalue v2) ==> except (k, v1) == except (k, v2)

let map_constraint_value_injective_inj
  (#tvalue: Type)
  (key #value: typ)
  (pvalue: spec value tvalue true)
  (except: map_constraint)
: Lemma
  (map_constraint_value_injective key pvalue.parser except)
= ()

let map_constraint_value_injective_and_or
  (#tvalue: Type)
  (key #value: typ)
  (#serializable: tvalue -> bool)
  (pvalue: parser_spec value tvalue serializable)
  (except1 except2: map_constraint)
: Lemma
  (requires 
    map_constraint_value_injective key pvalue except1 /\
    map_constraint_value_injective key pvalue except2
  )
  (ensures
    map_constraint_value_injective key pvalue (Util.andp except1 except2) /\
    map_constraint_value_injective key pvalue (orp except1 except2)
  )
= ()

let map_constraint_value_injective_not
  (#tvalue: Type)
  (key #value: typ)
  (#serializable: tvalue -> bool)
  (pvalue: parser_spec value tvalue serializable)
  (except1: map_constraint)
: Lemma
  (requires 
    map_constraint_value_injective key pvalue except1
  )
  (ensures
    map_constraint_value_injective key pvalue (Util.notp except1)
  )
= ()

let map_constraint_value_injective_ext
  (#tvalue: Type)
  (key #value: typ)
  (#serializable: tvalue -> bool)
  (pvalue: parser_spec value tvalue serializable)
  (except1 except2: map_constraint)
: Lemma
  (requires 
    map_constraint_equiv except1 except2
  )
  (ensures
    map_constraint_value_injective key pvalue except1 <==> map_constraint_value_injective key pvalue except2
  )
= ()

let map_constraint_value_injective_empty
  (#tvalue: Type)
  (key #value: typ)
  (#serializable: tvalue -> bool)
  (pvalue: parser_spec value tvalue serializable)
: Lemma
  (map_constraint_value_injective key pvalue map_constraint_empty)
= ()

let map_constraint_value_injective_key_except
  (#tvalue: Type)
  (key #value: typ)
  (#serializable: tvalue -> bool)
  (pvalue: parser_spec value tvalue serializable)
  (key_except: typ)
: Lemma
  (map_constraint_value_injective key pvalue (matches_map_group_entry key_except any))
= ()

let map_group_zero_or_more_match_item_parser
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint { map_constraint_value_injective key pvalue.parser except })
: Tot (map_group_parser_spec (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)) (map_group_zero_or_more_match_item_length) (map_group_zero_or_more_match_item_serializable pkey pvalue except))
= fun x -> map_group_zero_or_more_match_item_parser' pkey pvalue except x

let map_group_zero_or_more_match_item_serializer_op
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: Map.t tkey (list tvalue) { map_group_zero_or_more_match_item_serializable pkey pvalue except m })
  (accu: cbor_map)
  (x: tkey)
: Tot (cbor_map)
= match Map.get m x with
  | None -> accu
  | Some y ->
    cbor_map_union accu (cbor_map_singleton (pkey.serializer x) (pvalue.serializer (List.Tot.hd y)))

val map_group_zero_or_more_match_item_serializer_op_comm
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: Map.t tkey (list tvalue) { map_group_zero_or_more_match_item_serializable pkey pvalue except m })
  (accu: cbor_map)
  (x1 x2: tkey)
: Lemma
  (ensures (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m accu x1) x2 `cbor_map_equal` map_group_zero_or_more_match_item_serializer_op pkey pvalue except m (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m accu x2) x1
  ))
  [SMTPat (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m accu x1) x2)]
// = ()

let rec list_fold_map_group_zero_or_more_match_item_serializer_op_mem
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: Map.t tkey (list tvalue) { map_group_zero_or_more_match_item_serializable pkey pvalue except m })
  (accu: cbor_map)
  (l: list tkey)
  (kv: (cbor & cbor))
: Lemma
  (ensures (
    let m' = List.Tot.fold_left (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m) accu l in
    (cbor_map_mem kv m' <==> (match cbor_map_get accu (fst kv) with
    | Some v_ -> v_ == snd kv
    | None ->
      let (k, v) = kv in
      key k /\
      value v /\
      ~ (except (k, v)) /\
      List.Tot.memP (pkey.parser k) l /\
      begin match Map.get m (pkey.parser k) with
      | None -> False
      | Some v' ->
        List.Tot.length v' == 1 /\
        v == pvalue.serializer (List.Tot.hd v')
      end
    ))
  ))
  (decreases l)
= begin match l with
    | [] -> ()
    | a :: q ->
      list_fold_map_group_zero_or_more_match_item_serializer_op_mem pkey pvalue except m (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m accu a) q kv
  end

val list_fold_map_group_zero_or_more_match_item_serializer_length
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: Map.t tkey (list tvalue) { map_group_zero_or_more_match_item_serializable pkey pvalue except m })
  (accu: cbor_map)
  (l: list tkey)
: Lemma
  (requires (
    List.Tot.no_repeats_p l /\
    (forall x . List.Tot.memP x l ==> Map.defined x m) /\
    (forall x . ~ (List.Tot.memP x l /\ cbor_map_defined (pkey.serializer x) accu))
  ))
  (ensures (
    let m' = List.Tot.fold_left (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m) accu l in
    cbor_map_length m' == cbor_map_length accu + List.Tot.length l
  ))
  (decreases l)

let map_group_zero_or_more_match_item_serializer'
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: Map.t tkey (list tvalue) { map_group_zero_or_more_match_item_serializable pkey pvalue except m })
: Tot cbor_map
= Set.fold (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m) cbor_map_empty (Map.key_set pkey m)

let map_group_zero_or_more_match_item_serializer'_mem_aux
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: Map.t tkey (list tvalue) { map_group_zero_or_more_match_item_serializable pkey pvalue except m })
  (kv: (cbor & cbor))
: Tot prop
=
  let (k, v) = kv in
      key k /\
      value v /\
      ~ (except kv) /\
      exists kv' . Map.mem kv' m /\
      fst kv' == (pkey.parser k) /\
      List.Tot.length (snd kv') == 1 /\
      v == pvalue.serializer (List.Tot.hd (snd kv'))

let map_group_zero_or_more_match_item_serializer'_mem
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: Map.t tkey (list tvalue) { map_group_zero_or_more_match_item_serializable pkey pvalue except m })
  (kv: (cbor & cbor))
: Lemma
  (ensures (
    let m' = map_group_zero_or_more_match_item_serializer' pkey pvalue except m in
    (cbor_map_mem kv m' <==> (map_group_zero_or_more_match_item_serializer'_mem_aux pkey pvalue except m kv))
  ))
  [SMTPat (cbor_map_mem kv (map_group_zero_or_more_match_item_serializer' pkey pvalue except m))]
= let s = Map.key_set pkey m in
  let l = Set.set_as_list s in
  Set.fold_eq (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m) cbor_map_empty s l;
  list_fold_map_group_zero_or_more_match_item_serializer_op_mem pkey pvalue except m cbor_map_empty l kv

let map_group_zero_or_more_match_item_serializer'_length
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: Map.t tkey (list tvalue) { map_group_zero_or_more_match_item_serializable pkey pvalue except m })
: Lemma
  (ensures (
    cbor_map_length (map_group_zero_or_more_match_item_serializer' pkey pvalue except m) == Map.length m
  ))
  [SMTPat (cbor_map_length (map_group_zero_or_more_match_item_serializer' pkey pvalue except m))]
= let s = Map.key_set pkey m in
  let l = Set.set_as_list s in
  Set.fold_eq (map_group_zero_or_more_match_item_serializer_op pkey pvalue except m) cbor_map_empty s l;
  list_fold_map_group_zero_or_more_match_item_serializer_length pkey pvalue except m cbor_map_empty l

#restart-solver
let map_group_zero_or_more_match_item_serializer
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint { map_constraint_value_injective key pvalue.parser except })
: Tot (map_group_serializer_spec (map_group_zero_or_more_match_item_parser pkey pvalue except))
= fun x ->
  let y = map_group_zero_or_more_match_item_serializer' pkey pvalue except x in
  assert (forall x . Some? (cbor_map_get y x) ==> cbor_map_mem (x, Some?.v (cbor_map_get y x)) y);
  let py = map_group_zero_or_more_match_item_parser' pkey pvalue except y in
  assert (forall (kv: (tkey & list tvalue)) . Map.mem kv x ==> cbor_map_mem (pkey.serializer (fst kv), pvalue.serializer (List.Tot.hd (snd kv))) y);
  assert (Map.equal' py x);
  y

let map_group_zero_or_more_match_item_parser_inj
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (m: cbor_map { map_group_serializer_spec_arg_prop (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)) m })
: Lemma
  (requires inj)
  (ensures (
    map_group_zero_or_more_match_item_serializer pkey pvalue except (map_group_zero_or_more_match_item_parser pkey pvalue except m) `cbor_map_equal'` m
  ))
= let y = map_group_zero_or_more_match_item_parser pkey pvalue except m in
  let sy = map_group_zero_or_more_match_item_serializer pkey pvalue except y in
  assert (forall k . Some? (cbor_map_get m k) ==> cbor_map_mem (k, Some?.v (cbor_map_get m k)) m);
  assert (forall k . Map.defined k y ==> Map.mem (k, Some?.v (Map.get y k)) y);
  assert (cbor_map_filter (Util.andp (matches_map_group_entry key value) (Util.notp except)) m `cbor_map_equal` m);
  assert (forall (kv: (cbor & cbor)) . cbor_map_mem kv m ==> value (snd kv));
  assert (forall (kv: (cbor & cbor)) . cbor_map_mem kv m ==> (value (snd kv) /\ Map.mem (pkey.parser (fst kv), [pvalue.parser (snd kv)]) y));
  ()

let map_group_zero_or_more_match_item_parser_domain_inj'
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint { map_constraint_value_injective key pvalue.parser except })
  (x x' : cbor_map)
  (k: cbor)
: Lemma
  (requires (
    map_group_parser_spec_arg_prop (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)) x /\
    map_group_serializer_spec_arg_prop (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)) x' /\
    (map_group_zero_or_more_match_item_parser pkey pvalue except x <: Map.t tkey (list tvalue)) == 
      map_group_zero_or_more_match_item_parser pkey pvalue except x' /\
    cbor_map_defined k x'
  ))
  (ensures (
    cbor_map_defined k x
  ))
= let Some v = cbor_map_get x' k in
  assert (cbor_map_mem (k, v) x');
  assert (Map.mem (pkey.parser k, [pvalue.parser v]) (map_group_zero_or_more_match_item_parser pkey pvalue except x'));
  assert (cbor_map_defined k x)

let map_group_zero_or_more_match_item_parser_domain_inj
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint { map_constraint_value_injective key pvalue.parser except })
  (x x' : cbor_map)
  (k: cbor)
: Lemma
  (ensures (
    map_group_parser_spec_arg_prop (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)) x /\
    map_group_serializer_spec_arg_prop (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)) x' /\
    (map_group_zero_or_more_match_item_parser pkey pvalue except x <: Map.t tkey (list tvalue)) == 
      map_group_zero_or_more_match_item_parser pkey pvalue except x' /\
    cbor_map_defined k x'
  ) ==> (
    cbor_map_defined k x
  ))
= Classical.move_requires (map_group_zero_or_more_match_item_parser_domain_inj' pkey pvalue except x x') k

let mg_zero_or_more_match_item
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint { inj \/ map_constraint_value_injective key pvalue.parser except })
: Tot (mg_spec (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)) (Map.t tkey (list tvalue)) inj)
= {
  mg_size = map_group_zero_or_more_match_item_length;
  mg_serializable = (map_group_zero_or_more_match_item_serializable pkey pvalue except);
  mg_parser = map_group_zero_or_more_match_item_parser pkey pvalue except;
  mg_parser_domain_inj = Classical.forall_intro_3 (map_group_zero_or_more_match_item_parser_domain_inj pkey pvalue except);
  mg_serializer = map_group_zero_or_more_match_item_serializer pkey pvalue except;
  mg_inj = Classical.forall_intro (Classical.move_requires (map_group_zero_or_more_match_item_parser_inj pkey pvalue except));
}

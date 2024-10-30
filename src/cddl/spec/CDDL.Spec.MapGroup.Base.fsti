module CDDL.Spec.MapGroup.Base
include CDDL.Spec.Base
module Cbor = CBOR.Spec.API.Type
module U8 = FStar.UInt8
module U64 = FStar.UInt64

let map_group_item_post
  (l: Cbor.cbor_map)
  (l': (Cbor.cbor_map & Cbor.cbor_map))
: Tot bool
=
  fst l' `Cbor.cbor_map_disjoint_tot` snd l' &&
  (fst l' `Cbor.cbor_map_union` snd l') = l

let map_group_item_post_prop
  (l: Cbor.cbor_map)
  (l': (Cbor.cbor_map & Cbor.cbor_map))
: Tot prop
=
  fst l' `Cbor.cbor_map_disjoint` snd l' /\
  (fst l' `Cbor.cbor_map_union` snd l') `Cbor.cbor_map_equal` l

let map_group_item_post_equiv
  (l: Cbor.cbor_map)
  (l': (Cbor.cbor_map & Cbor.cbor_map))
: Lemma
  (ensures (map_group_item_post l l' <==> map_group_item_post_prop l l'))
  [SMTPat (map_group_item_post l l')]
= ()

val map_group : Type0

val map_group_always_false : map_group

val map_group_nop : map_group

val map_group_end : map_group

let matches_map_group_entry
  (key value: typ)
  (x: (Cbor.cbor & Cbor.cbor))
: Tot bool
= key (fst x) && value (snd x)

val map_group_match_item (cut: bool) (key value: typ) : map_group

val map_group_match_item_ext (cut: bool) (key value: typ) (key' value' : typ) : Lemma
  (requires (
    typ_equiv key key' /\
    typ_equiv value value'
  ))
  (ensures (
    map_group_match_item cut key value == map_group_match_item cut key' value'
  ))

val map_group_choice (m1 m2: map_group) : map_group

val map_group_choice_assoc
  (g1 g2 g3: map_group)
: Lemma
  ((g1 `map_group_choice` g2) `map_group_choice` g3 == g1 `map_group_choice` (g2 `map_group_choice` g3))
  [SMTPatOr [
//    [SMTPat (map_group_choice g1 (map_group_choice g2 g3))];
    [SMTPat (map_group_choice (map_group_choice g1 g2) g3)]
  ]]

val map_group_choice_always_false_l
  (g: map_group)
: Lemma
  (map_group_choice map_group_always_false g == g)
  [SMTPat (map_group_choice map_group_always_false g)]

val map_group_choice_always_false_r
  (g: map_group)
: Lemma
  (map_group_choice g map_group_always_false == g)
  [SMTPat (map_group_choice g map_group_always_false)]

let map_group_zero_or_one (m: map_group) : map_group =
  map_group_choice m map_group_nop

val map_group_concat (m1 m2: map_group) : map_group

val map_group_concat_assoc (m1 m2 m3: map_group) : Lemma
  (map_group_concat m1 (map_group_concat m2 m3) == map_group_concat (map_group_concat m1 m2) m3)
  [SMTPatOr [
//    [SMTPat (map_group_concat m1 (map_group_concat m2 m3))];
    [SMTPat (map_group_concat (map_group_concat m1 m2) m3)]
  ]]

val map_group_concat_nop_l
  (m: map_group)
: Lemma
  (map_group_concat map_group_nop m == m)
  [SMTPat (map_group_concat map_group_nop m)]

val map_group_concat_nop_r
  (m: map_group)
: Lemma
  (map_group_concat m map_group_nop == m)
  [SMTPat (map_group_concat m map_group_nop)]

val map_group_concat_always_false
  (m: map_group)
: Lemma
  (map_group_concat map_group_always_false m == map_group_always_false)
  [SMTPat (map_group_concat map_group_always_false m)]

val map_group_is_productive
  (m: map_group)
: Tot prop

val map_group_is_productive_always_false: squash (map_group_is_productive map_group_always_false)

val map_group_is_productive_match_item
  (cut: bool)
  (key value: typ)
: Lemma
  (map_group_is_productive (map_group_match_item cut key value))
  [SMTPat (map_group_is_productive (map_group_match_item cut key value))]

val map_group_is_productive_choice
  (m1 m2: map_group)
: Lemma
  (requires (
    map_group_is_productive m1 /\
    map_group_is_productive m2
  ))
  (ensures (
    map_group_is_productive (m1 `map_group_choice` m2)
  ))
  [SMTPat (map_group_is_productive (m1 `map_group_choice` m2))]

val map_group_is_productive_concat
  (m1 m2: map_group)
: Lemma
  (requires (
    map_group_is_productive m1 \/
    map_group_is_productive m2
  ))
  (ensures (
    map_group_is_productive (m1 `map_group_concat` m2)
  ))
  [SMTPat (map_group_is_productive (m1 `map_group_concat` m2))]

val map_group_zero_or_more
  (m: map_group)
: map_group

let map_group_one_or_more (m: map_group) : map_group =
  map_group_concat m (map_group_zero_or_more m)

let map_group_match_item_for
  (cut: bool)
  (k: Cbor.cbor)
  (ty: typ)
: Tot map_group
= map_group_match_item cut (t_literal k) ty

val map_group_zero_or_more_zero_or_one_eq
  (m: map_group)
: Lemma
  (map_group_zero_or_more (map_group_zero_or_one m) == map_group_zero_or_more m)

[@@erasable]
noeq
type map_group_result =
| MapGroupCutFail
| MapGroupFail
| MapGroupDet:
  (consumed: Cbor.cbor_map) ->
  (remaining: Cbor.cbor_map) ->
  map_group_result
| MapGroupNonDet

let map_group_result_prop (l: Cbor.cbor_map) (r: map_group_result) : Tot prop =
  match r with
  | MapGroupDet c m -> map_group_item_post l (c, m)
  | _ -> True

val apply_map_group_det (m: map_group) (l: Cbor.cbor_map) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)

val apply_map_group_det_always_false (l: Cbor.cbor_map) : Lemma
  (apply_map_group_det map_group_always_false l == MapGroupFail)
  [SMTPat (apply_map_group_det map_group_always_false l)]

val apply_map_group_det_nop (l: Cbor.cbor_map) : Lemma
  (apply_map_group_det map_group_nop l == MapGroupDet Cbor.cbor_map_empty l)
  [SMTPat (apply_map_group_det map_group_nop l)]

val apply_map_group_det_end (l: Cbor.cbor_map) : Lemma
  (apply_map_group_det map_group_end Cbor.cbor_map_empty == MapGroupDet Cbor.cbor_map_empty Cbor.cbor_map_empty /\
    ((~ (l == Cbor.cbor_map_empty)) ==> apply_map_group_det map_group_end l == MapGroupFail)
  )
  [SMTPat (apply_map_group_det map_group_end l)]

let map_group_is_det (m: map_group) : prop =
  forall l . ~ (MapGroupNonDet? (apply_map_group_det m l))

let det_map_group = (m: map_group { map_group_is_det m })

val apply_map_group_det_map_group_equiv (m1: det_map_group) (m2: map_group) : Lemma
  (requires
    (forall l . apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
  (ensures m1 == m2)

let apply_map_group_det_map_group_equiv0 (m1 m2: map_group)
  (prf1: (l: Cbor.cbor_map) -> Lemma
    (~ (MapGroupNonDet? (apply_map_group_det m1 l)))
  )
  (prf2: (l: Cbor.cbor_map) -> Lemma
    (apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
: Lemma
  (ensures m1 == m2)
= Classical.forall_intro prf1;
  Classical.forall_intro prf2;
  apply_map_group_det_map_group_equiv m1 m2

val apply_map_group_det_choice (m1 m2: map_group) (l: Cbor.cbor_map) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupCutFail -> apply_map_group_det (m1 `map_group_choice` m2) l == MapGroupCutFail
  | MapGroupFail -> apply_map_group_det (m1 `map_group_choice` m2) l == apply_map_group_det m2 l
  | MapGroupDet c1 l1 -> apply_map_group_det (m1 `map_group_choice` m2) l == MapGroupDet c1 l1
  | _ -> True
  )
  [SMTPat (apply_map_group_det (map_group_choice m1 m2) l)]

val apply_map_group_det_concat (m1 m2: map_group) (l: Cbor.cbor_map) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupCutFail -> apply_map_group_det (m1 `map_group_concat` m2) l == MapGroupCutFail
  | MapGroupFail -> apply_map_group_det (m1 `map_group_concat` m2) l == MapGroupFail
  | MapGroupDet c1 l1 ->
    apply_map_group_det (m1 `map_group_concat` m2) l == begin match apply_map_group_det m2 l1 with
    | MapGroupDet c2 l2 -> MapGroupDet (c1 `Cbor.cbor_map_union` c2) l2
    | res -> res
    end
  | _ -> True)
  [SMTPat (apply_map_group_det (map_group_concat m1 m2) l)]

let map_group_is_det_concat (m1 m2: det_map_group) : Lemma
    (ensures (
      map_group_is_det (m1 `map_group_concat` m2)
    ))
    [SMTPat (map_group_is_det (m1 `map_group_concat` m2))]
= ()

val apply_map_group_det_match_item_for
  (cut: bool)
  (k: Cbor.cbor)
  (ty: typ)
  (l: Cbor.cbor_map)
: Lemma
  (apply_map_group_det (map_group_match_item_for cut k ty) l == (match Cbor.cbor_map_get l k with
  | None ->  MapGroupFail
  | Some x ->
    if ty x
    then MapGroupDet (Cbor.cbor_map_singleton k x) (Cbor.cbor_map_filter (CBOR.Spec.Util.notp (matches_map_group_entry (t_literal k) ty)) l)
    else if cut
    then MapGroupCutFail
    else MapGroupFail
  ))
  [SMTPat (apply_map_group_det (map_group_match_item_for cut k ty) l)]

let map_group_is_det_match_item_for
  (cut: bool)
  (k: Cbor.cbor)
  (ty: typ)
: Lemma
  (map_group_is_det (map_group_match_item_for cut k ty))
= ()

val map_group_filter
  (f: (Cbor.cbor & Cbor.cbor) -> Tot bool)
: map_group

val apply_map_group_det_filter
  (f: (Cbor.cbor & Cbor.cbor) -> Tot bool)
  (l: Cbor.cbor_map)
: Lemma
  (apply_map_group_det (map_group_filter f) l ==
    MapGroupDet (Cbor.cbor_map_filter (CBOR.Spec.Util.notp f) l) (Cbor.cbor_map_filter f l)
  )
  [SMTPat (apply_map_group_det (map_group_filter f) l)]

val map_group_filter_filter (p1 p2: (Cbor.cbor & Cbor.cbor) -> Tot bool) : Lemma
  (map_group_filter p1 `map_group_concat` map_group_filter p2 == map_group_filter (CBOR.Spec.Util.andp p1 p2))
  [SMTPat (map_group_filter p1 `map_group_concat` map_group_filter p2)]

let map_group_filter_ext (p1 p2: _ -> Tot bool) : Lemma
  (requires forall x . p1 x == p2 x)
  (ensures map_group_filter p1 == map_group_filter p2)
=
  assert (forall x . Cbor.cbor_map_filter p1 x `Cbor.cbor_map_equal` Cbor.cbor_map_filter p2 x);
  assert (forall x . Cbor.cbor_map_filter (CBOR.Spec.Util.notp p1) x `Cbor.cbor_map_equal` Cbor.cbor_map_filter (CBOR.Spec.Util.notp p2) x);
  apply_map_group_det_map_group_equiv
    (map_group_filter p1)
    (map_group_filter p2)

val map_group_zero_or_one_match_item_filter (key value: typ) (p: (Cbor.cbor & Cbor.cbor) -> Tot bool) : Lemma
  (requires (
    forall x . p x ==> CBOR.Spec.Util.notp (matches_map_group_entry key value) x
  ))
  (ensures
    map_group_zero_or_one (map_group_match_item false key value) `map_group_concat` map_group_filter p == map_group_filter p
  )
  [SMTPat (map_group_zero_or_one (map_group_match_item false key value) `map_group_concat` map_group_filter p)]

val map_group_zero_or_more_match_item_filter (key value: typ) : Lemma
  (map_group_zero_or_more (map_group_match_item false key value) ==
    map_group_filter (CBOR.Spec.Util.notp (matches_map_group_entry key value))
  )
  [SMTPat (map_group_zero_or_more (map_group_match_item false key value))]

let map_group_zero_or_more_match_item_choice_left
  (key1 key2 value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item false (key1 `t_choice` key2) value) ==
    map_group_zero_or_more (map_group_match_item false key1 value) `map_group_concat`
    map_group_zero_or_more (map_group_match_item false key2 value)
  )
= map_group_filter_ext
    (CBOR.Spec.Util.notp (matches_map_group_entry (key1 `t_choice` key2) value))
    (CBOR.Spec.Util.notp (matches_map_group_entry key1 value) `CBOR.Spec.Util.andp`
      CBOR.Spec.Util.notp (matches_map_group_entry key2 value)
    )

val map_group_zero_or_more_map_group_match_item_for
  (cut: bool)
  (key: Cbor.cbor)
  (value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item_for cut key value) ==
    map_group_zero_or_one (map_group_match_item_for cut key value)
  )

let map_group_fail_shorten
  (g: map_group)
: Tot prop
= forall (m1 m2: _) .
  (Cbor.cbor_map_disjoint m1 m2 /\ MapGroupFail? (apply_map_group_det g (m1 `Cbor.cbor_map_union` m2))) ==>
  MapGroupFail? (apply_map_group_det g m1)

val map_group_fail_shorten_match_item
  (cut: bool)
  (key value: typ)
: Lemma
  (map_group_fail_shorten (map_group_match_item cut key value))
  [SMTPat (map_group_fail_shorten (map_group_match_item cut key value))]

val map_group_zero_or_more_choice
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

val matches_map_group (g: map_group) (m: Cbor.cbor_map) : Tot bool

val matches_map_group_det (g: map_group) (m: Cbor.cbor_map) : Lemma
  (match apply_map_group_det g m with
  | MapGroupCutFail
  | MapGroupFail -> ~ (matches_map_group g m)
  | MapGroupDet _ m' -> matches_map_group g m <==> m' == Cbor.cbor_map_empty
  | _ -> True)
  [SMTPat (matches_map_group g m)]

val t_map (g: map_group) : typ

val t_map_eq
  (g: map_group)
  (x: Cbor.cbor)
: Lemma
  (t_map g x == true <==> begin match Cbor.unpack x with
    | Cbor.CMap m ->
      matches_map_group g m
    | _ -> False
  end)
  [SMTPat (t_map g x)]

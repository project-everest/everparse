module CDDL.Spec.MapGroup
module U = CBOR.Spec.Util

#push-options "--z3rlimit 32"

#restart-solver
let restrict_map_group_concat
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
= restrict_map_group_intro
    (g1 `map_group_concat` g2)
    (g1' `map_group_concat` g2')
    (fun m ->
      match apply_map_group_det g1 m with
      | MapGroupDet c1 r1 ->
        let MapGroupDet c1' r1' = apply_map_group_det g1' m in
        let d1 = c1 `cbor_map_sub` c1' in
        cbor_map_union_assoc c1' d1 r1;
        cbor_map_disjoint_union_simpl_l c1' (d1 `cbor_map_union` r1) r1';
        cbor_map_disjoint_union_comm d1 r1;
        assert (r1' == r1 `cbor_map_union` d1);
        map_group_footprint_consumed_disjoint g1 f1 f2' m;
        assert (cbor_map_disjoint_from_footprint d1 f2');
        map_group_footprint_elim g2' f2' r1 d1;
        begin match apply_map_group_det g2 r1 with
        | MapGroupDet c2 r2 ->
          let MapGroupDet c2' r2' = apply_map_group_det g2' r1 in
          assert (c2' `cbor_map_included` c2);
          assert ((c1' `cbor_map_union` c2') `cbor_map_included` (c1 `cbor_map_union` c2))
        | _ -> ()
        end
      | _ -> ()
    )

let map_group_choice_compatible_match_item_with_cut
  (key: typ)
  (value: typ)
  (right: map_group)
  (fp: typ)
: Lemma
  (requires (
    key `typ_disjoint` fp /\
    map_group_footprint right fp
  ))
  (ensures (
    map_group_choice_compatible (map_group_match_item true key value) right
  ))
= map_group_choice_compatible_intro (map_group_match_item true key value) right (fun x ->
    let phi = matches_map_group_entry fp any in
    cbor_map_split phi x;
    map_group_footprint_elim right fp (cbor_map_filter phi x) (cbor_map_filter (U.notp phi) x)
  )

let map_group_choice_compatible_match_item_for
  (cut: bool)
  (key: cbor)
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
= map_group_choice_compatible_intro (map_group_match_item_for cut key value) right (fun x ->
    let phi = matches_map_group_entry fp any in
    cbor_map_split phi x;
    map_group_footprint_elim right fp (cbor_map_filter phi x) (cbor_map_filter (U.notp phi) x)
  )

#pop-options

#push-options "--z3rlimit 32"

#restart-solver
let map_group_footprint_concat_consumes_all_recip
  (g1 g2: map_group)
  (f1 f2: typ)
  (m: cbor_map)
: Pure (cbor_map & cbor_map)
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\
    map_group_consumes_all (g1 `map_group_concat` g2) m
  ))
  (ensures (fun (m1, m2) ->
    m1 `cbor_map_disjoint` m2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 cbor_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 cbor_map_empty /\
    m1 `cbor_map_union` m2 == m
  ))
= cbor_map_split (matches_map_group_entry f1 any) m;
  let m1 = cbor_map_filter (matches_map_group_entry f1 any) m in
  let m1' = cbor_map_filter (U.notp (matches_map_group_entry f1 any)) m in
  map_group_footprint_elim g1 f1 m1 m1';
  let MapGroupDet _ r1 = apply_map_group_det g1 m1 in 
  let MapGroupDet _ r1' = apply_map_group_det g1 m in
  assert (r1' == r1 `cbor_map_union` m1');
  cbor_map_disjoint_union_comm r1 m1';
  cbor_map_split (matches_map_group_entry f2 any) m1';
  let m2 = cbor_map_filter (matches_map_group_entry f2 any) m1' in
  let m2' = cbor_map_filter (U.notp (matches_map_group_entry f2 any)) m1' in
  cbor_map_union_assoc m2 m2' r1;
  cbor_map_disjoint_mem_union' m2' r1 ();
  assert (cbor_map_included r1 m1);
  assert (cbor_map_disjoint_from_footprint m1 f2);
  assert (cbor_map_disjoint_from_footprint r1 f2);
  assert (cbor_map_disjoint_from_footprint m2' f2);
  map_group_footprint_elim g2 f2 m2 (m2' `cbor_map_union` r1);
  let MapGroupDet _ r2 = apply_map_group_det g2 m2 in
  let MapGroupDet _ r2' = apply_map_group_det g2 r1' in
  assert (r2' == cbor_map_empty);
  assert (r2' == r2 `cbor_map_union` (m2' `cbor_map_union` r1));
  cbor_map_equiv r2 cbor_map_empty;
  cbor_map_equiv m2' cbor_map_empty;
  cbor_map_equiv r1 cbor_map_empty;
  (m1, m2)

#pop-options

#restart-solver

let parser_spec_map_group'
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
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
  (x: cbor { t_map source0 x })
: Pure (y: target { target_prop y })
    (requires True)
    (ensures fun y ->
      (let x = CMap?.c (unpack x) in
        (let x' = cbor_map_filter (matches_map_group_entry source_fp any) x in
        map_group_parser_spec_arg_prop source source_fp x' /\
        y == p x'
      ))
    )
=
    let CMap a = unpack x in
    let a' = cbor_map_filter (matches_map_group_entry source_fp any) a in
    cbor_map_split (matches_map_group_entry source_fp any) a;
    let res = p a' in
    res

let parser_spec_map_group
  source0 #source #source_fp #target #target_size #target_prop p target_prop'
= fun x -> parser_spec_map_group' source0 p target_prop' x

let parser_spec_map_group_eq
  source0 #source #source_fp p target_prop' x
= let f = (matches_map_group_entry source_fp any) in
  assert (
    (let x' = cbor_map_filter f (CMap?.c (unpack x)) in
    map_group_parser_spec_arg_prop source source_fp x' /\
    parser_spec_map_group source0 p target_prop' x == p x'
  ))

#push-options "--z3rlimit 64"

#restart-solver

let map_group_concat_footprint_disjoint
  (source1: det_map_group)
  (source_fp1: typ)
  (source2: det_map_group)
  (source_fp2: typ {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2
  })
  (m: cbor_map)
: Lemma
  (requires (
    map_group_serializer_spec_arg_prop (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2) m
  ))
  (ensures (
    let m1 = cbor_map_filter (matches_map_group_entry source_fp1 any) m in
    let m2 = cbor_map_filter (matches_map_group_entry source_fp2 any) m in
    cbor_map_disjoint m1 m2 /\
    cbor_map_union m1 m2 == m /\
    apply_map_group_det source1 m1 == MapGroupDet m1 cbor_map_empty /\
    apply_map_group_det source1 m == MapGroupDet m1 m2 /\
    apply_map_group_det source2 m2 == MapGroupDet m2 cbor_map_empty
  ))
= let m1 = cbor_map_filter (matches_map_group_entry source_fp1 any) m in
  let m2 = cbor_map_filter (matches_map_group_entry source_fp2 any) m in
  assert (cbor_map_disjoint m1 m2);
  let m12 = cbor_map_union m1 m2 in
  let m' = cbor_map_sub m m12 in
  assert (cbor_map_disjoint_from_footprint m' source_fp1);
  cbor_map_union_assoc m1 m2 m';
  map_group_footprint_elim source1 source_fp1 m1 (cbor_map_union m2 m');
  let MapGroupDet cm1 rm1 = apply_map_group_det source1 m1 in
  cbor_map_union_assoc rm1 m2 m';
  cbor_map_disjoint_union_comm rm1 m2;
  cbor_map_union_assoc m2 rm1 m';
  assert (cbor_map_union rm1 (cbor_map_union m2 m') == cbor_map_union m2 (cbor_map_union rm1 m'));
  assert (cbor_map_disjoint_from_footprint m1 source_fp2);
  assert (cbor_map_disjoint_from_footprint rm1 source_fp2);
  assert (cbor_map_disjoint_from_footprint m' source_fp2);
  map_group_footprint_elim source2 source_fp2 m2 (cbor_map_union rm1 m');
  let MapGroupDet cm2 rm2 = apply_map_group_det source2 m2 in
  assert (apply_map_group_det (map_group_concat source1 source2) m == MapGroupDet (cbor_map_union cm1 cm2) (cbor_map_union rm1 (cbor_map_union rm2 m')));
  assert (cbor_map_equal rm1 cbor_map_empty);
  assert (cbor_map_equal rm2 cbor_map_empty);
  assert (cbor_map_equal m' cbor_map_empty);
  assert (cbor_map_union m1 m2 == m);
  assert (apply_map_group_det source1 m1 == MapGroupDet m1 cbor_map_empty);
  assert (apply_map_group_det source1 m == MapGroupDet m1 m2);
  assert (apply_map_group_det source2 m2 == MapGroupDet m2 cbor_map_empty)

#pop-options


#push-options "--z3rlimit 32"

#restart-solver
let map_group_parser_spec_concat'
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (p2: map_group_parser_spec source2 source_fp2 target_size2 target_prop2)
  (target_size: (target1 & target2) -> Tot nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2 /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
  (target_prop: (target1 & target2) -> bool {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
  (l: map_group_parser_spec_arg (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2))
: Pure (map_group_parser_spec_ret (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2) target_size target_prop l)
    (requires True)
    (ensures fun l' ->
    let l1 = cbor_map_filter (matches_map_group_entry source_fp1 any) l in
    let l2 = cbor_map_filter (matches_map_group_entry source_fp2 any) l in
    map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
    map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
    (l' <: (target1 & target2)) == (p1 l1, p2 l2)
  )
=
  map_group_footprint_is_consumed source1 source_fp1 (l);
  let res1 = p1 (cbor_map_filter (matches_map_group_entry source_fp1 any) l) in
  let MapGroupDet c1 r1 = apply_map_group_det source1 (cbor_map_filter (matches_map_group_entry source_fp1 any) (l)) in
  cbor_map_disjoint_union_comm r1 (cbor_map_filter (matches_map_group_entry source_fp2 any) (l));
  cbor_map_split (matches_map_group_entry source_fp1 any) (l);
  let MapGroupDet c1' r1' = apply_map_group_det source1 (l) in
  cbor_map_equiv
    (cbor_map_filter (U.notp (matches_map_group_entry source_fp1 any)) (l))
    (cbor_map_filter (matches_map_group_entry source_fp2 any) (l));
  map_group_footprint_consumed source1 source_fp1 (cbor_map_filter (matches_map_group_entry source_fp1 any) (l)) (cbor_map_filter (matches_map_group_entry source_fp2 any) (l));
  cbor_map_union_assoc c1 r1 (cbor_map_filter (matches_map_group_entry source_fp2 any) (l));
  assert (r1' == r1 `cbor_map_union` cbor_map_filter (matches_map_group_entry source_fp2 any) (l));
  map_group_footprint_consumed source2 source_fp2 (cbor_map_filter (matches_map_group_entry source_fp2 any) (l)) r1;
  let res2 = p2 (cbor_map_filter ((matches_map_group_entry source_fp2 any)) l) in
  cbor_map_length_disjoint_union
    ( (cbor_map_filter ( (matches_map_group_entry source_fp1 any)) l))
    ( (cbor_map_filter ( (matches_map_group_entry source_fp2 any)) l));
  let res = (res1, res2) in
  res

#pop-options

let map_group_parser_spec_concat
  #source1 #source_fp1 #target1 #target_size1 p1 #source2 #source_fp2 #target2 #target_size2 p2 target_size target_prop
= fun l -> map_group_parser_spec_concat' p1 p2 target_size target_prop l

#restart-solver
let map_group_parser_spec_concat_eq
  #source1 #source_fp1 #target1 #target_size1 p1 #source2 #source_fp2 #target2 #target_size2 p2 target_size target_prop
  l
= let f1 =  (matches_map_group_entry source_fp1 any) in
  let f2 =  (matches_map_group_entry source_fp2 any) in
  assert (
    let l1 = cbor_map_filter f1 l in
    let l2 = cbor_map_filter f2 l in
    map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
    map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
    map_group_parser_spec_concat p1 p2 target_size target_prop l == (p1 l1, p2 l2)
  )

#push-options "--z3rlimit 32"

#restart-solver
let map_group_parser_spec_choice'
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (p1: map_group_parser_spec source1 source_fp1 target_size1 target_prop1 {
    map_group_footprint source1 source_fp1
  })
  (#source2: det_map_group)
  (#source_fp2: typ)
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
  (l: map_group_parser_spec_arg (map_group_choice source1 source2) (source_fp1 `t_choice` source_fp2))
: Pure (map_group_parser_spec_ret (map_group_choice source1 source2) (source_fp1 `t_choice` source_fp2) target_size target_prop l)
    (requires True)
    (ensures (fun l' ->
        let f1 = matches_map_group_entry source_fp1 any in
        let f2 = matches_map_group_entry source_fp2 any in
        let l1 = cbor_map_filter f1 l in
        let l2 = cbor_map_filter f2 l in
        let test = MapGroupDet? (apply_map_group_det source1 (l1)) in
        l1 == cbor_map_filter (matches_map_group_entry source_fp1 any) (l) /\
        l2 == cbor_map_filter (matches_map_group_entry source_fp2 any) (l) /\
        (test ==> (
          map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
          (l' <: (target1 `either` target2)) == Inl (p1 l1)
        )) /\
        ((~ test) ==> (
          map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
          (l' <: (target1 `either` target2)) == Inr (p2 l2)
        ))
    ))
= let m1 = cbor_map_filter (matches_map_group_entry source_fp1 any) (l) in
  cbor_map_split (matches_map_group_entry source_fp1 any) (l);
  map_group_footprint_elim source1 source_fp1 m1 (cbor_map_filter (U.notp (matches_map_group_entry source_fp1 any)) (l));
  match apply_map_group_det source1 m1 with
  | MapGroupDet _ _ -> Inl (p1 (cbor_map_filter ((matches_map_group_entry source_fp1 any)) l))
  | _ ->
    begin
      map_group_footprint_is_consumed source2 source_fp2 (l);
      Inr (p2 (cbor_map_filter ((matches_map_group_entry source_fp2 any)) l))
    end

#pop-options

let map_group_parser_spec_choice
  p1 p2 target_size
= fun x -> map_group_parser_spec_choice' p1 p2 target_size x

let map_group_parser_spec_choice_eq
  #source1 #source_fp1 #target1 #target_size1 p1 #source2 #source_fp2 #target2 #target_size2 #target_prop2 p2 target_size target_prop l
= let l' = map_group_parser_spec_choice p1 p2 target_size target_prop l in
  assert (
        let f1 = matches_map_group_entry source_fp1 any in
        let f2 = matches_map_group_entry source_fp2 any in
        let l1 = cbor_map_filter f1 l in
        let l2 = cbor_map_filter f2 l in
        let test = MapGroupDet? (apply_map_group_det source1 (l1)) in
        l1 == cbor_map_filter (matches_map_group_entry source_fp1 any) (l) /\
        l2 == cbor_map_filter (matches_map_group_entry source_fp2 any) (l) /\
        (test ==> (
          map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
          (l' <: (target1 `either` target2)) == Inl (p1 l1)
        )) /\
        ((~ test) ==> (
          map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
          (l' <: (target1 `either` target2)) == Inr (p2 l2)
        ))
  )

#push-options "--z3rlimit 32"

let map_group_zero_or_more_match_item_serializer_op_comm
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (key_except: typ)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (m: Map.t tkey (list tvalue) { map_group_zero_or_more_match_item_serializable pkey key_except pvalue m })
  (accu: cbor_map)
  (x1 x2: tkey)
= ()

#pop-options

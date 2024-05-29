module CDDL.Spec.MapGroupGen

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
        let d1 = c1 `ghost_map_sub` c1' in
        ghost_map_union_assoc c1' d1 r1;
        ghost_map_disjoint_union_simpl_l c1' (d1 `ghost_map_union` r1) r1';
        ghost_map_disjoint_union_comm d1 r1;
        assert (r1' == r1 `ghost_map_union` d1);
        map_group_footprint_consumed_disjoint g1 f1 f2' m;
        assert (ghost_map_disjoint_from_footprint d1 f2');
        map_group_footprint_elim g2' f2' r1 d1;
        begin match apply_map_group_det g2 r1 with
        | MapGroupDet c2 r2 ->
          let MapGroupDet c2' r2' = apply_map_group_det g2' r1 in
          assert (c2' `ghost_map_included` c2);
          assert ((c1' `ghost_map_union` c2') `ghost_map_included` (c1 `ghost_map_union` c2))
        | _ -> ()
        end
      | _ -> ()
    )

let map_group_choice_compatible_match_item_for
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
= map_group_choice_compatible_intro (map_group_match_item_for cut key value) right (fun x ->
    let phi = matches_map_group_entry fp any in
    ghost_map_split phi x;
    map_group_footprint_elim right fp (ghost_map_filter phi x) (ghost_map_filter (notp_g phi) x)
  )

#pop-options

#push-options "--z3rlimit 32"

#restart-solver
let map_group_footprint_concat_consumes_all_recip
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
= ghost_map_split (matches_map_group_entry f1 any) m;
  let m1 = ghost_map_filter (matches_map_group_entry f1 any) m in
  let m1' = ghost_map_filter (notp_g (matches_map_group_entry f1 any)) m in
  map_group_footprint_elim g1 f1 m1 m1';
  let MapGroupDet _ r1 = apply_map_group_det g1 m1 in
  let MapGroupDet _ r1' = apply_map_group_det g1 m in
  assert (r1' == r1 `ghost_map_union` m1');
  ghost_map_disjoint_union_comm r1 m1';
  ghost_map_split (matches_map_group_entry f2 any) m1';
  let m2 = ghost_map_filter (matches_map_group_entry f2 any) m1' in
  let m2' = ghost_map_filter (notp_g (matches_map_group_entry f2 any)) m1' in
  ghost_map_union_assoc m2 m2' r1;
  ghost_map_disjoint_mem_union' m2' r1 ();
  assert (ghost_map_included r1 m1);
  assert (ghost_map_disjoint_from_footprint m1 f2);
  assert (ghost_map_disjoint_from_footprint r1 f2);
  assert (ghost_map_disjoint_from_footprint m2' f2);
  map_group_footprint_elim g2 f2 m2 (m2' `ghost_map_union` r1);
  let MapGroupDet _ r2 = apply_map_group_det g2 m2 in
  let MapGroupDet _ r2' = apply_map_group_det g2 r1' in
  assert (r2' == ghost_map_empty);
  assert (r2' == r2 `ghost_map_union` (m2' `ghost_map_union` r1));
  ghost_map_equiv r2 ghost_map_empty;
  ghost_map_equiv m2' ghost_map_empty;
  ghost_map_equiv r1 ghost_map_empty;
  (m1, m2)

#pop-options

#restart-solver
let parser_spec_map_group'
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
  (x: Cbor.raw_data_item { t_map source0 x })
: Ghost target
    (requires True)
    (ensures (fun res ->
      let f = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any) in
      (forall x . Ghost.reveal f x == matches_map_group_entry source_fp any x) /\
      (let x' = List.Tot.filter f (Cbor.Map?.v x) in
      map_group_parser_spec_arg_prop source source_fp x' /\
      res == p x'
    )))
=
    let Cbor.Map a = x in
    let a' = List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any)) a in
    ghost_map_split (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any)) (ghost_map_of_list a);
    let res = p a' in
    res

let parser_spec_map_group
  source0 p target_prop'
= fun x -> parser_spec_map_group' source0 p target_prop' x

let parser_spec_map_group_eq
  source0 #source #source_fp p target_prop' x
= let f = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any) in
  assert (
    (forall x . Ghost.reveal f x == matches_map_group_entry source_fp any x) /\
    (let x' = List.Tot.filter f (Cbor.Map?.v x) in
    map_group_parser_spec_arg_prop source source_fp x' /\
    parser_spec_map_group source0 p target_prop' x == p x'
  ))

#push-options "--z3rlimit 32"

#restart-solver
let map_group_parser_spec_concat'
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
: Ghost (map_group_parser_spec_ret (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2) target_size target_prop l)
    (requires True)
    (ensures (fun l' ->
        let f1 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any) in
        let f2 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any) in
        (forall x . f1 x == matches_map_group_entry source_fp1 any x) /\
        (forall x . f2 x == matches_map_group_entry source_fp2 any x) /\ (
        let l1 = List.Tot.filter f1 l in
        let l2 = List.Tot.filter f2 l in
        map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
        map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
        (l' <: (target1 & target2)) == ((p1 l1 <: target1), (p2 l2 <: target2))
      )
    ))
=
  ghost_map_equiv
    (ghost_map_filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any)) (ghost_map_of_list l))
    (ghost_map_filter (matches_map_group_entry source_fp1 any) (ghost_map_of_list l));
  map_group_footprint_is_consumed source1 source_fp1 (ghost_map_of_list l);
  let res1 = p1 (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any)) l) in
  let MapGroupDet c1 r1 = apply_map_group_det source1 (ghost_map_filter (matches_map_group_entry source_fp1 any) (ghost_map_of_list l)) in
  ghost_map_disjoint_union_comm r1 (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  ghost_map_split (matches_map_group_entry source_fp1 any) (ghost_map_of_list l);
  let MapGroupDet c1' r1' = apply_map_group_det source1 (ghost_map_of_list l) in
  ghost_map_equiv
    (ghost_map_filter (notp_g (matches_map_group_entry source_fp1 any)) (ghost_map_of_list l))
    (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  map_group_footprint_consumed source1 source_fp1 (ghost_map_filter (matches_map_group_entry source_fp1 any) (ghost_map_of_list l)) (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  ghost_map_union_assoc c1 r1 (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  assert (r1' == r1 `ghost_map_union` ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  map_group_footprint_consumed source2 source_fp2 (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l)) r1;
  ghost_map_equiv
    (ghost_map_filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any)) (ghost_map_of_list l))
    (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  let res2 = p2 (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any)) l) in
  ghost_map_length_disjoint_union
    (ghost_map_of_list (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any)) l))
    (ghost_map_of_list (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any)) l));
  let res = (res1, res2) in
  res

#pop-options

let map_group_parser_spec_concat
  p1 p2 target_size target_prop
= map_group_parser_spec_concat' p1 p2 target_size target_prop

#restart-solver
let map_group_parser_spec_concat_eq
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
= let f1 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any) in
  let f2 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any) in
  assert (
    (forall x . f1 x == matches_map_group_entry source_fp1 any x) /\
    (forall x . f2 x == matches_map_group_entry source_fp2 any x) /\ (
    let l1 = List.Tot.filter f1 l in
    let l2 = List.Tot.filter f2 l in
    map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
    map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
    map_group_parser_spec_concat p1 p2 target_size target_prop l == (p1 l1, p2 l2)
  ))

#push-options "--z3rlimit 32"

#restart-solver
let map_group_parser_spec_choice'
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
: Ghost (map_group_parser_spec_ret (map_group_choice source1 source2) (source_fp1 `t_choice` source_fp2) target_size target_prop l)
    (requires True)
    (ensures (fun l' ->
        let f1 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any) in
        let f2 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any) in
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
= let m1 = ghost_map_filter (matches_map_group_entry source_fp1 any) (ghost_map_of_list l) in
  ghost_map_equiv
    (ghost_map_filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any)) (ghost_map_of_list l))
    m1;
  ghost_map_split (matches_map_group_entry source_fp1 any) (ghost_map_of_list l);
  map_group_footprint_elim source1 source_fp1 m1 (ghost_map_filter (notp_g (matches_map_group_entry source_fp1 any)) (ghost_map_of_list l));
  ghost_map_equiv
    (ghost_map_filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any)) (ghost_map_of_list l))
    (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  match apply_map_group_det source1 m1 with
  | MapGroupDet _ _ -> Inl (p1 (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any)) l))
  | _ ->
    begin
      map_group_footprint_is_consumed source2 source_fp2 (ghost_map_of_list l);
      Inr (p2 (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any)) l))
    end

#pop-options

let map_group_parser_spec_choice
  p1 p2 target_size
= fun x -> map_group_parser_spec_choice' p1 p2 target_size x

#push-options "--z3rlimit 32"

#restart-solver
let map_group_parser_spec_choice_eq
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
=
        let l' = map_group_parser_spec_choice p1 p2 target_size target_prop l in
        let f1 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any) in
        let f2 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any) in
    assert (
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
    ))

#pop-options

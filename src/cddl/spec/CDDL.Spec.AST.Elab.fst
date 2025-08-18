module CDDL.Spec.AST.Elab
include CDDL.Spec.AST.Elab.Base
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

[@@"opaque_to_smt"]
let rec typ_disjoint
  (fuel: nat)
: typ_disjoint_t
= fun e t1 t2 ->
  if fuel = 0
  then ROutOfFuel
  else
    let fuel' : nat = fuel - 1 in
    CDDL.Spec.AST.Elab.Disjoint.Type.typ_disjoint (typ_disjoint fuel') (array_group_disjoint fuel') e t1 t2

and array_group_disjoint
  (fuel: nat)
: array_group_disjoint_t
= fun e close1 close2 a1 a2 ->
  if fuel = 0
  then ROutOfFuel
  else
    let fuel' : nat = fuel - 1 in
    CDDL.Spec.AST.Elab.Disjoint.Array.array_group_disjoint (typ_disjoint fuel') (array_group_disjoint fuel') fuel e close1 close2 a1 a2

[@@"opaque_to_smt"]
let rec typ_included
  (fuel: nat)
  : typ_included_t
= fun e t1 t2 ->
  if fuel = 0
  then ROutOfFuel
  else
    let fuel' : nat = fuel - 1 in
    CDDL.Spec.AST.Elab.Included.Type.typ_included
      (typ_disjoint fuel)
      (typ_included fuel')
      (typ_included2 fuel')
      e t1 t2
      
and typ_included2
  (fuel: nat)
  : typ_included_t
= fun e t1 t2 ->
  if fuel = 0
  then ROutOfFuel
  else
    let fuel' : nat = fuel - 1 in
    CDDL.Spec.AST.Elab.Included.Type2.typ_included2
      (typ_included fuel')
      (typ_included2 fuel')
      (array_group_included fuel')
      e t1 t2

and array_group_included
  (fuel: nat)
: array_group_included_t
= fun e close a1 a2 ->
  if fuel = 0
  then ROutOfFuel
  else
    let fuel' : nat = fuel - 1 in
    CDDL.Spec.AST.Elab.Included.Array.array_group_included
      (typ_included fuel')
      (array_group_included fuel')
      (array_group_disjoint fuel)
      fuel
      e close a1 a2

[@@"opaque_to_smt"]
let rec typ_diff_disjoint
  (fuel: nat)
: typ_diff_disjoint_t
= fun env t1 d1 t2 d2 ->
  if fuel = 0
  then ROutOfFuel
  else
    let fuel' : nat = fuel - 1 in
    CDDL.Spec.AST.Elab.Disjoint.TypeDiff.typ_diff_disjoint
      (typ_disjoint fuel)
      (typ_included fuel)
      (typ_diff_disjoint fuel')
      env t1 d1 t2 d2
      
[@@"opaque_to_smt"]
let rec map_group_choice_compatible_no_cut
  (fuel: nat)
: map_group_choice_compatible_no_cut_t
= fun env s1 s2 ->
  if fuel = 0
  then ROutOfFuel
  else
    let fuel' : nat = fuel - 1 in
    CDDL.Spec.AST.Elab.MGCCNoCut.map_group_choice_compatible_no_cut
      (map_group_choice_compatible_no_cut fuel')
      (typ_disjoint fuel)
      (typ_included fuel)
      fuel
      env s1 s2

[@@"opaque_to_smt"]
let rec map_group_choice_compatible
  (fuel: nat)
: map_group_choice_compatible_t
= fun env s1 s2 ->
  if fuel = 0
  then ROutOfFuel
  else
    let fuel' : nat = fuel - 1 in
    CDDL.Spec.AST.Elab.MGCC.map_group_choice_compatible
      (map_group_choice_compatible fuel')
      (typ_disjoint fuel)
      (typ_included fuel)
      fuel
      env s1 s2

let rec mk_elab_map_group
  (fuel: nat)
  (env: ast_env)
  (g: group)
: Tot (result elab_map_group)
  (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match g with
  | GElem cut (TNamed name (TElem (ELiteral key))) value ->
    RSuccess (MGMatch cut (Some name) key value)  
  | GElem cut (TElem (ELiteral key)) value ->
    RSuccess (MGMatch cut (name_from_literal key) key value)
  | GElem cut (TDef nkey) value ->
    begin match env.e_sem_env.se_bound nkey with
    | Some NType ->
      let t = env.e_env nkey in // this type is supposed to be already rewritten
      mk_elab_map_group fuel' env (GElem cut t value)
    | _ -> RFailure ("mk_elab_map_group: GElem TDef: " ^ nkey ^ " is not a type" )
    end
  | GElem true key value ->
    RSuccess (MGMatchWithCut key value)
  | GAlwaysFalse -> RSuccess MGAlwaysFalse
  | GNop -> RSuccess MGNop
  | GZeroOrOne g ->
    begin match mk_elab_map_group fuel' env g with
    | RSuccess g' -> RSuccess (MGChoice g' MGNop)
    | err -> err
    end
  | GZeroOrMore (GElem false key value) ->
    RSuccess (MGTable key value MCFalse)
  | GConcat g1 g2 ->
    begin match mk_elab_map_group fuel' env g1 with
    | RSuccess g1' ->
      begin match mk_elab_map_group fuel' env g2 with
      | RSuccess g2' -> RSuccess (MGConcat g1' g2')
      | err -> err
      end
    | err -> err
    end
  | GChoice g1 g2 ->
    begin match mk_elab_map_group fuel' env g1 with
    | RSuccess g1' ->
      begin match mk_elab_map_group fuel' env g2 with
      | RSuccess g2' -> RSuccess (MGChoice g1' g2')
      | err -> err
      end
    | err -> err
    end
  | GDef n ->
    begin match env.e_sem_env.se_bound n with
    | Some NGroup ->
      let g1 = env.e_env n in
      let (g2, res) = rewrite_group fuel true g1 in
      if res
      then mk_elab_map_group fuel' env g2
      else ROutOfFuel
    | _ -> RFailure ("mk_elab_map_group: undefined group: " ^ n)
    end
  | GZeroOrMore (GDef n) ->
    begin match env.e_sem_env.se_bound n with
    | Some NGroup ->
      let g1 = env.e_env n in
      let (g2, res) = rewrite_group fuel true (GZeroOrMore g1) in
      if res
      then mk_elab_map_group fuel' env g2
      else ROutOfFuel
    | _ -> RFailure ("mk_elab_map_group: undefined group: " ^ n)
    end
  | _ -> RFailure ("mk_elab_map_group: unsupported" ^ CDDL.Spec.AST.Print.group_to_string g)

let rec mk_elab_map_group_bounded
  (fuel: nat)
  (env: ast_env)
  (g: group)
: Lemma
  (requires (group_bounded env.e_sem_env.se_bound g))
  (ensures (match mk_elab_map_group fuel env g with
  | RSuccess g' -> bounded_elab_map_group env.e_sem_env.se_bound g'
  | _ -> True
  ))
  (decreases fuel)
  [SMTPat (group_bounded env.e_sem_env.se_bound g); SMTPat (mk_elab_map_group fuel env g)]
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match g with
  | GZeroOrOne g_ -> mk_elab_map_group_bounded fuel' env g_
  | GConcat g1 g2
  | GChoice g1 g2 ->
    mk_elab_map_group_bounded fuel' env g1;
    mk_elab_map_group_bounded fuel' env g2
  | GDef n ->
    let g' = (env.e_env n) in
    rewrite_group_bounded env.e_sem_env.se_bound fuel true g';
    mk_elab_map_group_bounded fuel' env (fst (rewrite_group fuel true g'))
  | GZeroOrMore (GDef n) ->
    begin match env.e_sem_env.se_bound n with
    | Some NGroup ->
      let g1 = env.e_env n in
      let (g2, res) = rewrite_group fuel true (GZeroOrMore g1) in
      if res
      then begin
        rewrite_group_bounded env.e_sem_env.se_bound fuel true (GZeroOrMore g1);
        mk_elab_map_group_bounded fuel' env g2
      end
      else ()
    end
  | GElem cut (TDef nkey) value ->
    let t = env.e_env nkey in
    mk_elab_map_group_bounded fuel' env (GElem cut t value)
  | _ -> ()

let rec mk_elab_map_group_correct
  (fuel: nat)
  (env: ast_env)
  (g: group)
: Lemma
  (requires (group_bounded env.e_sem_env.se_bound g))
  (ensures (match mk_elab_map_group fuel env g with
  | RSuccess g' ->
    bounded_elab_map_group env.e_sem_env.se_bound g' /\
    elab_map_group_sem env.e_sem_env g' == map_group_sem env.e_sem_env g
  | _ -> True
  ))
  (decreases fuel)
=
  mk_elab_map_group_bounded fuel env g;
  if fuel = 0 then () else
  let fuel' : nat = fuel - 1 in
  match g with
  | GChoice g1 g2
  | GConcat g1 g2 ->
    mk_elab_map_group_correct fuel' env g1;
    mk_elab_map_group_correct fuel' env g2
  | GZeroOrOne g_ ->
    mk_elab_map_group_correct fuel' env g_
  | GZeroOrMore (GElem false key value) ->
    Spec.map_group_filter_ext
      (Util.notp (Util.andp (Spec.matches_map_group_entry (typ_sem env.e_sem_env key) (typ_sem env.e_sem_env value)) (Util.notp Spec.map_constraint_empty)))
      (Util.notp (Spec.matches_map_group_entry (typ_sem env.e_sem_env key) (typ_sem env.e_sem_env value)))
  | GDef n ->
    let g' = (env.e_env n) in
    rewrite_group_correct env.e_sem_env fuel true g';
    mk_elab_map_group_correct fuel' env (fst (rewrite_group fuel true g'))
  | GZeroOrMore (GDef n) ->
    let g' = (env.e_env n) in
    rewrite_group_correct env.e_sem_env fuel true (GZeroOrMore g');
    mk_elab_map_group_correct fuel' env (fst (rewrite_group fuel true (GZeroOrMore g')))
  | GElem cut (TDef nkey) value ->
    let t = env.e_env nkey in
    assert (Spec.typ_equiv (typ_sem env.e_sem_env t) (sem_of_type_sem (env.e_sem_env.se_env nkey)));
    Spec.map_group_match_item_ext cut (typ_sem env.e_sem_env t) (typ_sem env.e_sem_env value) (sem_of_type_sem (env.e_sem_env.se_env nkey)) (typ_sem env.e_sem_env value);
    assert (map_group_sem env.e_sem_env (GElem cut t value) == map_group_sem env.e_sem_env (GElem cut (TDef nkey) value));
    mk_elab_map_group_correct fuel' env (GElem cut t value)
  | _ -> ()

let typ_inter_underapprox_postcond
  (env: ast_env)
  (t1 t2: typ)
  (t': result typ)
: GTot prop
=
    typ_bounded env.e_sem_env.se_bound t1 /\
    typ_bounded env.e_sem_env.se_bound t2 /\
    begin match t' with
    | RSuccess t' ->
      typ_bounded env.e_sem_env.se_bound t' /\
      Spec.typ_included (typ_sem env.e_sem_env t') (typ_sem env.e_sem_env t1 `Util.andp` typ_sem env.e_sem_env t2)
    | RFailure _ -> False
    | _ -> True
    end

let rec typ_inter_underapprox
  (fuel: nat)
  (env: ast_env)
  (t1 t2: typ)
: Pure (result typ)
  (requires (
    typ_bounded env.e_sem_env.se_bound t1 /\
    typ_bounded env.e_sem_env.se_bound t2
  ))
  (ensures fun t' ->
    typ_inter_underapprox_postcond env t1 t2 t'
  )
  (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t1 with
  | TChoice t1l t1r ->
    begin match typ_inter_underapprox fuel' env t1l t2 with
    | RSuccess t1l' ->
      begin match typ_inter_underapprox fuel' env t1r t2 with
      | RSuccess t1r' -> RSuccess (mk_TChoice t1l' t1r')
      | res -> res
      end
    | res -> res
    end
  | TDef i ->
    let t1' = env.e_env i in
    typ_inter_underapprox fuel' env t1' t2
  | _ ->
    begin match typ_included fuel env t1 t2 with
    | RSuccess _ -> RSuccess t1
    | RFailure _ -> RSuccess (TElem EAlwaysFalse)
    | ROutOfFuel -> ROutOfFuel
    end

let rec extract_cut
  (g: elab_map_group)
: Tot map_constraint
= match g with
  | MGMatch cut _ key value -> MCKeyValue (TElem (ELiteral key)) (if cut then TElem EAny else value)
  | MGMatchWithCut key _ -> MCKeyValue key (TElem EAny)
  | MGChoice g1 _ -> extract_cut g1
  | _ -> MCFalse

let rec bounded_extract_cut
  (env: name_env)
  (g: elab_map_group)
: Lemma
  (requires (bounded_elab_map_group env g))
  (ensures (let (key) = extract_cut g in
  bounded_map_constraint env key
  ))
  (decreases g)
  [SMTPat (bounded_elab_map_group env g); SMTPat (extract_cut g)]
= match g with
  | MGChoice g1 _ -> bounded_extract_cut env g1
  | _ -> ()

let cbor_map_disjoint_from_footprint_always_false
  (m: Cbor.cbor_map)
: Lemma
  (Spec.cbor_map_disjoint_from_footprint m Spec.map_constraint_empty)
= ()

#push-options "--z3rlimit 32"

#restart-solver
let rec extract_cut_correct
  (env: sem_env)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
: Lemma
  (requires (bounded_elab_map_group env.se_bound g))
  (ensures (
    let (key) = extract_cut g in
    bounded_elab_map_group env.se_bound g /\
    bounded_map_constraint env.se_bound key /\
    begin
      match Spec.apply_map_group_det (elab_map_group_sem env g) m with
      | Spec.MapGroupDet _ m1 -> Spec.cbor_map_disjoint_from_footprint m1 (map_constraint_sem env key)
      | Spec.MapGroupFail -> Spec.cbor_map_disjoint_from_footprint m (map_constraint_sem env key)
      | _ -> True
    end
  ))
  (decreases g)
= let (key) = extract_cut g in
  assert (bounded_map_constraint env.se_bound key);
  match g with
  | MGChoice g1 _ ->
    extract_cut_correct env g1 m
  | MGMatch true _ key _ -> ()
  | MGMatchWithCut key _ -> ()
  | _ -> cbor_map_disjoint_from_footprint_always_false m

#pop-options

let rec annot_tables
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
: Pure (result (map_constraint & elab_map_group))
    (requires (
      bounded_map_constraint env.e_sem_env.se_bound cut /\
      bounded_elab_map_group env.e_sem_env.se_bound g
    ))
    (ensures (fun res -> match res with
    | RSuccess (cut', g') -> 
      bounded_map_constraint env.e_sem_env.se_bound cut' /\
      bounded_elab_map_group env.e_sem_env.se_bound g'
    | ROutOfFuel -> False
    | _ -> True
    ))
    (decreases g)
= match g with
  | MGChoice g1 g2 ->
    begin match annot_tables fuel env cut g1 with
    | RSuccess (cut1, g1') ->
      let (extracted_cut) = extract_cut g1 in
      begin match annot_tables fuel env (MCOr cut extracted_cut) g2 with
      | RSuccess (cut2, g2') ->
        let cut' = MCAnd cut1 cut2 in
        RSuccess (cut', MGChoice g1' g2')
      | res -> res
      end
    | res -> res
    end
  | MGConcat g1 g2 ->
    begin match annot_tables fuel env cut g1 with
    | RSuccess (cut1, g1') ->
      begin match annot_tables fuel env cut1 g2 with
      | RSuccess (cut2, g2') -> RSuccess (cut2, MGConcat g1' g2')
      | res -> res
      end
    | res -> res
    end
  | MGTable key value MCFalse ->
    let except = cut in
    RSuccess (MCOr cut (MCKeyValue key value), MGTable key value except)
  | MGTable _ _ _ -> RFailure "annot_tables cannot be run twice"
  | MGMatch cut' _ key value ->
    let fp = (MCKeyValue (TElem (ELiteral key)) (TElem EAny)) in
    RSuccess (MCOr cut fp, g) // TODO: rewrite the group if cut' is true and key \included cut
  | MGMatchWithCut key _ ->
    let fp = MCKeyValue key (TElem EAny) in
    RSuccess (MCOr cut fp, g)
  | MGCut key ->
    let fp = MCKeyValue key (TElem EAny) in
    RSuccess (MCOr cut fp, g)
  | MGAlwaysFalse -> RSuccess (MCFalse, g)
  | MGNop -> RSuccess (cut, g)

let annot_tables_correct_postcond0
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
  (cut' : map_constraint)
  (g' : elab_map_group)
: GTot prop
=
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\ (
      let a = Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m in
      bounded_map_constraint env.e_sem_env.se_bound cut' /\
      bounded_elab_map_group env.e_sem_env.se_bound g' /\
      a == Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m /\
      (Spec.MapGroupDet? a ==> (let Spec.MapGroupDet _ m' = a in Spec.cbor_map_disjoint_from_footprint m' (map_constraint_sem env.e_sem_env cut')))
    )

let annot_tables_correct_postcond
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
: GTot prop
=
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    begin match  (annot_tables fuel env cut g) with
    | RSuccess (cut', g') ->
    annot_tables_correct_postcond0 fuel env cut g m cut' g' 
    | _ -> True
    end        

let annot_tables_correct_postcond_intro
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
  (sq1: squash (
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g
  ))
  (cut': map_constraint)
  (g': elab_map_group)
  (sq2: squash (annot_tables fuel env cut g == RSuccess (cut', g')))
  (sq3: squash (bounded_map_constraint env.e_sem_env.se_bound cut'))
  (sq4: squash (bounded_elab_map_group env.e_sem_env.se_bound g'))
  (sq5: squash (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m == Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m))
  (sq6: squash (
      begin match Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m with
      | Spec.MapGroupDet _ m' -> Spec.cbor_map_disjoint_from_footprint m' (map_constraint_sem env.e_sem_env cut')
      | _ -> True
      end
  ))
: Lemma
  (annot_tables_correct_postcond fuel env cut g m)
= ()

let annot_tables_correct_postcond_intro_none
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
  (sq1: squash (
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g
  ))
  (cut': map_constraint)
  (g': elab_map_group)
  (sq2: squash (annot_tables fuel env cut g == RSuccess (cut', g')))
  (sq3: squash (bounded_map_constraint env.e_sem_env.se_bound cut'))
  (sq4: squash (bounded_elab_map_group env.e_sem_env.se_bound g'))
  (sq5: squash (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m == Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m))
  (sq6: squash (~ (Spec.MapGroupDet? (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m))))
: Lemma
  (annot_tables_correct_postcond fuel env cut g m)
= ()

#restart-solver
let annot_tables_correct_postcond_intro_some
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
  (sq1: squash (
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g
  ))
  (cut': map_constraint)
  (g': elab_map_group)
  (sq2: squash (annot_tables fuel env cut g == RSuccess (cut', g')))
  (sq3: squash (bounded_map_constraint env.e_sem_env.se_bound cut'))
  (sq4: squash (bounded_elab_map_group env.e_sem_env.se_bound g'))
  (sq5: squash (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m == Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m))
  (sq6: squash (
      Spec.MapGroupDet? (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m)
  ))
  (m': Cbor.cbor_map)
  (sq65: squash (let Spec.MapGroupDet _ m_ = Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m in m_ == m'))
  (sq7: squash (Spec.cbor_map_disjoint_from_footprint m' (map_constraint_sem env.e_sem_env cut')))
: Lemma
  (annot_tables_correct_postcond fuel env cut g m)
= ()

let annot_tables_correct_postcond_intro_not_success
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
  (sq1: squash (
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g
  ))
  (sq2: squash (~ (RSuccess? (annot_tables fuel env cut g))))
: Lemma
  (annot_tables_correct_postcond fuel env cut g m)
= ()

let cbor_map_filter_ext_strong
  (f1 f2: (Cbor.cbor & Cbor.cbor) -> Tot bool)
  (m: Cbor.cbor_map)
: Lemma
  (requires forall x . Cbor.cbor_map_mem x m ==> f1 x == f2 x)
  (ensures Cbor.cbor_map_filter f1 m == Cbor.cbor_map_filter f2 m)
= Cbor.cbor_map_ext (Cbor.cbor_map_filter f1 m) (Cbor.cbor_map_filter f2 m)

let cbor_map_filter_disjoint_from_footprint
  (c1 c2: Spec.map_constraint)
  (m: Cbor.cbor_map)
: Lemma
  (requires (Spec.map_constraint_disjoint c1 c2))
  (ensures (Spec.cbor_map_disjoint_from_footprint (Cbor.cbor_map_filter c1 m) c2))
= ()

#push-options "--z3rlimit 32"

#restart-solver
let annot_tables_correct_aux_match
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (c: bool)
  (name: option string)
  (key: literal)
  (value: typ)
  (m: Cbor.cbor_map)
  (sq: squash (
    let g = MGMatch c name key value in
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    Spec.cbor_map_disjoint_from_footprint m (map_constraint_sem env.e_sem_env cut)
  ))
: Tot (squash (
    let g = MGMatch c name key value in
    annot_tables_correct_postcond fuel env cut g m
  ))
=
    Spec.apply_map_group_det_match_item_for c (eval_literal key) (typ_sem env.e_sem_env value) m;
    let fp = (MCKeyValue (TElem (ELiteral key)) (TElem EAny)) in
    let fp' = map_constraint_sem env.e_sem_env fp in
    Spec.map_group_footprint_match_item_for c (eval_literal key) (typ_sem env.e_sem_env value);
    let cut' = MCOr cut fp in
    let g = MGMatch c name key value in
    let sq1 : squash (
      bounded_map_constraint env.e_sem_env.se_bound cut /\
      bounded_elab_map_group env.e_sem_env.se_bound g
    ) = () in
    let sq2 : squash (annot_tables fuel env cut g == RSuccess (cut', g)) =
      assert (annot_tables fuel env cut (MGMatch c name key value) == RSuccess (cut', MGMatch c name key value)) by (FStar.Tactics.trefl ())
    in
    begin match Cbor.cbor_map_get m (eval_literal key) with
    | None ->
//      annot_tables_correct_postcond_intro_none fuel env cut g m () cut' g sq2 () () () ();
      ()
    | Some x -> 
      if typ_sem env.e_sem_env value x
      then begin
        let f1 = (Util.notp (Spec.matches_map_group_entry (Spec.t_literal (eval_literal key)) (typ_sem env.e_sem_env value))) in
        let f2 = (Util.notp (Spec.matches_map_group_entry (Spec.t_literal (eval_literal key)) (Spec.any))) in
        let m1 = Cbor.cbor_map_filter f1 m in
        let m2 = Cbor.cbor_map_filter f2 m in
        assert (Cbor.cbor_map_equal m1 m2);
        cbor_map_filter_disjoint_from_footprint (f2) fp' m;
//        annot_tables_correct_postcond_intro_some fuel env cut g m () cut' g () () () () () m1 () ();
        ()
      end
      else begin
//        annot_tables_correct_postcond_intro_none fuel env cut g m (_ by (FStar.Tactics.smt ())) cut' g sq2 () () () ();
        ()
      end
    end

#restart-solver
let annot_tables_correct_aux_table
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (key: typ)
  (value: typ)
  (m: Cbor.cbor_map)
  (sq: squash (
    let g = MGTable key value MCFalse in
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    Spec.cbor_map_disjoint_from_footprint m (map_constraint_sem env.e_sem_env cut)
  ))
: Tot (squash (
    let g = MGTable key value MCFalse in
    annot_tables_correct_postcond fuel env cut g m
  ))
= 
  let g = MGTable key value MCFalse in
      let nf = Util.notp (Util.andp (Spec.matches_map_group_entry (typ_sem env.e_sem_env key) (typ_sem env.e_sem_env value)) (Util.notp Spec.map_constraint_empty)) in
      let mnf = Cbor.cbor_map_filter nf m in
      let mnnf = Cbor.cbor_map_filter (Util.notp nf) m in
      assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m == Spec.MapGroupDet mnnf mnf);
      let g' = MGTable key value cut in
      let cut' = MCOr cut (MCKeyValue key value) in
      assert (annot_tables fuel env cut g == RSuccess (cut', g'));
      let nf' = Util.notp (Util.andp (Spec.matches_map_group_entry (typ_sem env.e_sem_env key) (typ_sem env.e_sem_env value)) (Util.notp (map_constraint_sem env.e_sem_env cut))) in
      let mnf' = Cbor.cbor_map_filter nf' m in
      let mnnf' = Cbor.cbor_map_filter (Util.notp nf') m in
      assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m == Spec.MapGroupDet mnnf' mnf');
      cbor_map_filter_ext_strong nf nf' m;
      assert (mnf == mnf');
      assert (Cbor.cbor_map_equal mnnf mnnf');
      assert (Spec.cbor_map_disjoint_from_footprint mnf (map_constraint_sem env.e_sem_env cut'));
      assert (annot_tables_correct_postcond fuel env cut g m)

#pop-options

let annot_tables_correct_aux'_t
  (g: elab_map_group)
=
  (fuel: nat) ->
  (env: ast_env) ->
  (cut: map_constraint) ->
  (m: Cbor.cbor_map) ->
  (sq: squash (
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    Spec.cbor_map_disjoint_from_footprint m (map_constraint_sem env.e_sem_env cut)
  )) ->
  Lemma (ensures annot_tables_correct_postcond fuel env cut g m)

#push-options "--z3rlimit 128 --ifuel 8 --fuel 4 --split_queries always"

let annot_tables_correct_aux'_choice
  (g: elab_map_group { MGChoice? g })
  (annot_tables_correct_aux': (g' : elab_map_group { g' << g }) -> annot_tables_correct_aux'_t g')
: Tot (annot_tables_correct_aux'_t g)
= fun fuel env cut m sq ->
  let MGChoice g1 g2 = g in
    let (extracted_cut) = extract_cut g1 in
    annot_tables_correct_aux' g1 fuel env cut m ();
//    mk_TChoice_sem env.e_sem_env cut extracted_cut;
    extract_cut_correct env.e_sem_env g1 m;
    begin match Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g1) m with
    | Spec.MapGroupFail ->
      annot_tables_correct_aux' g2 fuel env (MCOr cut extracted_cut) m ();
      assert (annot_tables_correct_postcond fuel env cut g m)
    | _ -> assert (annot_tables_correct_postcond fuel env cut g m)
    end

let annot_tables_concat
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g1 g2: elab_map_group)
  (cut1: map_constraint)
  (g1': elab_map_group)
  (cut2: map_constraint)
  (g2' : elab_map_group)
: Lemma
  (requires (
      bounded_map_constraint env.e_sem_env.se_bound cut /\
      bounded_elab_map_group env.e_sem_env.se_bound g1 /\
      bounded_elab_map_group env.e_sem_env.se_bound g2 /\
      annot_tables fuel env cut g1 == RSuccess (cut1, g1') /\
      annot_tables fuel env cut1 g2 == RSuccess (cut2, g2')
  ))
    (ensures (
      annot_tables fuel env cut (MGConcat g1 g2) == RSuccess (cut2, MGConcat g1' g2')
    ))
= ()

let annot_tables_concat_not_success
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g1 g2: elab_map_group)
  (cut1: map_constraint)
  (g1': elab_map_group)
: Lemma
  (requires (
      bounded_map_constraint env.e_sem_env.se_bound cut /\
      bounded_elab_map_group env.e_sem_env.se_bound g1 /\
      bounded_elab_map_group env.e_sem_env.se_bound g2 /\
      annot_tables fuel env cut g1 == RSuccess (cut1, g1') /\
      ~ (RSuccess? (annot_tables fuel env cut1 g2))
  ))
    (ensures (
      ~ (RSuccess? (annot_tables fuel env cut (MGConcat g1 g2)))
    ))
= ()

let annot_tables_correct_aux'_concat
  (g: elab_map_group { MGConcat? g })
  (annot_tables_correct_aux': (g' : elab_map_group { g' << g }) -> annot_tables_correct_aux'_t g')
: Tot (annot_tables_correct_aux'_t g)
= fun fuel env cut m sq ->
  let MGConcat g1 g2 = g in
  assert (bounded_elab_map_group env.e_sem_env.se_bound g1);
  assert (bounded_elab_map_group env.e_sem_env.se_bound g2);
    begin match annot_tables fuel env cut g1 with
    | RSuccess (cut1, g1') ->
      annot_tables_correct_aux' g1 fuel env cut m ();
      begin match Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g1) m with
      | Spec.MapGroupDet _ m1 ->
        annot_tables_correct_aux' g2 fuel env cut1 m1 ();
        assert (annot_tables_correct_postcond fuel env cut g m)
      | res ->
        assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m == res);
        assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g1') m == res);
        begin match annot_tables fuel env cut1 g2 with
        | RSuccess (cut2, g2') ->
          assert (Spec.apply_map_group_det (Spec.map_group_concat (elab_map_group_sem env.e_sem_env g1') (elab_map_group_sem env.e_sem_env g2')) m == res);
          elab_map_group_sem_concat env.e_sem_env g1' g2';
          annot_tables_concat fuel env cut g1 g2 cut1 g1' cut2 g2';
          annot_tables_correct_postcond_intro_none fuel env cut (MGConcat g1 g2) m () cut2 (MGConcat g1' g2') () () () () ();
          assert (annot_tables_correct_postcond fuel env cut g m)
        | _ ->
          annot_tables_concat_not_success fuel env cut g1 g2 cut1 g1';
          annot_tables_correct_postcond_intro_not_success fuel env cut g m () ();
          assert (annot_tables_correct_postcond fuel env cut g m)
        end
      end
    | _ -> assert (annot_tables_correct_postcond fuel env cut g m)
    end

#restart-solver
let rec annot_tables_correct_aux'
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
  (sq: squash (
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    Spec.cbor_map_disjoint_from_footprint m (map_constraint_sem env.e_sem_env cut)
  ))
: Lemma (ensures annot_tables_correct_postcond fuel env cut g m)
  (decreases g)
= 
  match g with
  | MGChoice g1 g2 ->
    annot_tables_correct_aux'_choice g (fun g' fuel env cut m sq -> annot_tables_correct_aux' fuel env cut g' m sq) fuel env cut m sq
  | MGConcat g1 g2 ->
    annot_tables_correct_aux'_concat g (fun g' fuel env cut m sq -> annot_tables_correct_aux' fuel env cut g' m sq) fuel env cut m sq
  | MGMatch c name key value ->
    annot_tables_correct_aux_match fuel env cut c name key value m ()
  | MGTable key value MCFalse ->
    annot_tables_correct_aux_table fuel env cut key value m ()
  | _ -> assert (annot_tables_correct_postcond fuel env cut g m)

#pop-options

let annot_tables_correct'
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
: Lemma
  (requires (
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    Spec.cbor_map_disjoint_from_footprint m (map_constraint_sem env.e_sem_env cut)
  ))
  (ensures (
    bounded_map_constraint env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    begin match annot_tables fuel env cut g with
    | RSuccess (cut', g') ->
      let a = Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m in
      bounded_map_constraint env.e_sem_env.se_bound cut' /\
      bounded_elab_map_group env.e_sem_env.se_bound g' /\
      a == Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m /\
      begin match a with
      | Spec.MapGroupDet _ m' -> Spec.cbor_map_disjoint_from_footprint m' (map_constraint_sem env.e_sem_env cut')
      | _ -> True
      end
    | _ -> True
    end        
  ))
= annot_tables_correct_aux' fuel env cut g m ()

let annot_tables_correct
  (fuel: nat)
  (env: ast_env)
  (g: elab_map_group)
: Lemma
  (requires (
    bounded_elab_map_group env.e_sem_env.se_bound g
  ))
  (ensures (
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    begin match annot_tables fuel env (MCFalse) g with
    | RSuccess (cut', g') ->
      bounded_map_constraint env.e_sem_env.se_bound cut' /\
      bounded_elab_map_group env.e_sem_env.se_bound g' /\
      elab_map_group_sem env.e_sem_env g == elab_map_group_sem env.e_sem_env g'
    | _ -> True
    end        
  ))
= match annot_tables fuel env (MCFalse) g with
  | RSuccess (_, g') ->
    assert (forall (m: Cbor.cbor_map) . Spec.cbor_map_disjoint_from_footprint m (map_constraint_sem env.e_sem_env (MCFalse)));
    Classical.forall_intro (Classical.move_requires (annot_tables_correct' fuel env (MCFalse) g));
    Spec.apply_map_group_det_map_group_equiv (elab_map_group_sem env.e_sem_env g) (elab_map_group_sem env.e_sem_env g')
  | _ -> ()

[@@"opaque_to_smt"]
let mk_mc_and
  (fuel: nat)
  (env: ast_env)
  (g1 g2: map_constraint)
: Pure (result map_constraint)
    (requires 
      bounded_map_constraint env.e_sem_env.se_bound g1 /\
      bounded_map_constraint env.e_sem_env.se_bound g2
    )
    (ensures fun g' ->
      bounded_map_constraint env.e_sem_env.se_bound g1 /\
      bounded_map_constraint env.e_sem_env.se_bound g2 /\
      begin match g' with
      | RSuccess g' ->
        bounded_map_constraint env.e_sem_env.se_bound g' /\
        Spec.map_constraint_equiv (map_constraint_sem env.e_sem_env g') (Util.andp (map_constraint_sem env.e_sem_env g1) (map_constraint_sem env.e_sem_env g2))
      | RFailure _ -> False
      | ROutOfFuel -> True
      end
    )
= begin match map_constraint_included (typ_disjoint fuel) (typ_included fuel) env g1 g2 with
  | RSuccess _ -> RSuccess g1
  | ROutOfFuel -> ROutOfFuel
  | _ ->
    begin match map_constraint_included (typ_disjoint fuel) (typ_included fuel) env g2 g1 with
    | RSuccess _ -> RSuccess g2
    | ROutOfFuel -> ROutOfFuel
    | _ -> RSuccess (MCAnd g1 g2)
    end
  end

[@@"opaque_to_smt"]
let mk_mc_or
  (fuel: nat)
  (env: ast_env)
  (g1 g2: map_constraint)
: Pure (result map_constraint)
    (requires 
      bounded_map_constraint env.e_sem_env.se_bound g1 /\
      bounded_map_constraint env.e_sem_env.se_bound g2
    )
    (ensures fun g' ->
      bounded_map_constraint env.e_sem_env.se_bound g1 /\
      bounded_map_constraint env.e_sem_env.se_bound g2 /\
      begin match g' with
      | RSuccess g' ->
        bounded_map_constraint env.e_sem_env.se_bound g' /\
        Spec.map_constraint_equiv (map_constraint_sem env.e_sem_env g') (Spec.map_constraint_choice (map_constraint_sem env.e_sem_env g1) (map_constraint_sem env.e_sem_env g2))
      | RFailure _ -> False
      | ROutOfFuel -> True
      end
    )
= begin match map_constraint_included (typ_disjoint fuel) (typ_included fuel) env g1 g2 with
  | RSuccess _ -> RSuccess g2
  | ROutOfFuel -> ROutOfFuel
  | _ ->
    begin match map_constraint_included (typ_disjoint fuel) (typ_included fuel) env g2 g1 with
    | RSuccess _ -> RSuccess g1
    | ROutOfFuel -> ROutOfFuel
    | _ -> RSuccess (MCOr g1 g2)
    end
  end

let rec annot_tables'
  (fuel: nat)
  (env: ast_env)
  (cut: map_constraint)
  (g: elab_map_group)
: Pure (result (map_constraint & elab_map_group))
    (requires (
      bounded_map_constraint env.e_sem_env.se_bound cut /\
      bounded_elab_map_group env.e_sem_env.se_bound g
    ))
    (ensures (fun res -> match res with
    | RSuccess (cut', g') -> 
      bounded_map_constraint env.e_sem_env.se_bound cut' /\
      bounded_elab_map_group env.e_sem_env.se_bound g'
    | _ -> True
    ))
    (decreases g)
= match g with
  | MGChoice g1 g2 ->
    begin match annot_tables' fuel env cut g1 with
    | RSuccess (cut1, g1') ->
      let (extracted_cut) = extract_cut g1 in
      begin match mk_mc_or fuel env cut extracted_cut with
      | RSuccess cut_ ->
        begin match annot_tables' fuel env cut_ g2 with
        | RSuccess (cut2, g2') ->
          begin match mk_mc_and fuel env cut1 cut2 with
          | RSuccess cut' ->
            RSuccess (cut', MGChoice g1' g2')
          | res -> coerce_failure res
          end
        | res -> res
        end
      | res -> coerce_failure res
      end
    | res -> res
    end
  | MGConcat g1 g2 ->
    begin match annot_tables' fuel env cut g1 with
    | RSuccess (cut1, g1') ->
      begin match annot_tables' fuel env cut1 g2 with
      | RSuccess (cut2, g2') -> RSuccess (cut2, MGConcat g1' g2')
      | res -> res
      end
    | res -> res
    end
  | MGTable key value MCFalse ->
    let except = cut in
    begin match mk_mc_or fuel env cut (MCKeyValue key value) with
    | RSuccess mc' ->  RSuccess (mc', MGTable key value except)
    | res -> coerce_failure res
    end
  | MGTable _ _ _ -> RFailure "annot_tables cannot be run twice"
  | MGMatch cut' name key value ->
    let fp = (MCKeyValue (TElem (ELiteral key)) (TElem EAny)) in
    begin match mk_mc_or fuel env cut fp with
    | RSuccess mc' -> RSuccess (mc', g) // TODO: rewrite the group if cut' is true and key \included cut
    | res -> coerce_failure res
    end
  | MGMatchWithCut key _ ->
    let fp = MCKeyValue key (TElem EAny) in
    begin match mk_mc_or fuel env cut fp with
    | RSuccess cut' -> RSuccess (cut', g)
    | res -> coerce_failure res
    end
  | MGCut key ->
    let fp = MCKeyValue key (TElem EAny) in
    begin match mk_mc_or fuel env cut fp with
    | RSuccess cut' -> RSuccess (cut', g)
    | res -> coerce_failure res
    end
  | MGAlwaysFalse -> RSuccess (MCFalse, g)
  | MGNop -> RSuccess (cut, g)

let annot_tables'_correct'_post
  (fuel: nat)
  (env: ast_env)
  (cut1 cut2: map_constraint)
  (g: elab_map_group)
: Tot prop
=
      bounded_map_constraint env.e_sem_env.se_bound cut1 /\
      bounded_map_constraint env.e_sem_env.se_bound cut2 /\
      bounded_elab_map_group env.e_sem_env.se_bound g /\
      (RSuccess? (annot_tables' fuel env cut1 g) ==> RSuccess? (annot_tables fuel env cut2 g)) /\
      begin match annot_tables' fuel env cut1 g with
      | RSuccess (cut1', g1') ->
        begin match annot_tables fuel env cut2 g with
        | RSuccess (cut2', g2') ->
          bounded_map_constraint env.e_sem_env.se_bound cut1' /\
          bounded_elab_map_group env.e_sem_env.se_bound g1' /\
          bounded_map_constraint env.e_sem_env.se_bound cut2' /\
          bounded_elab_map_group env.e_sem_env.se_bound g2' /\
          Spec.map_constraint_equiv (map_constraint_sem env.e_sem_env cut1') (map_constraint_sem env.e_sem_env cut2') /\
          elab_map_group_sem env.e_sem_env g1' == elab_map_group_sem env.e_sem_env g2'
        |  _ -> False
        end
      | _ -> True
      end

let map_group_filtered_table_except_ext
  (key value: Spec.typ)
  (except1 except2: Spec.map_constraint)
: Lemma
  (requires (
    Spec.map_constraint_equiv except1 except2
  ))
  (ensures (
    Spec.map_group_filtered_table key value except1 == Spec.map_group_filtered_table key value except2
  ))
= 
      Spec.map_group_filter_ext
        (Util.notp (Util.andp (Spec.matches_map_group_entry key value) (Util.notp except1)))
        (Util.notp (Util.andp (Spec.matches_map_group_entry key value) (Util.notp except2)))

#push-options "--z3rlimit 64 --ifuel 6 --fuel 4 --split_queries always"

#restart-solver

let rec annot_tables'_correct'
  (fuel: nat)
  (env: ast_env)
  (cut1 cut2: map_constraint)
  (g: elab_map_group)
: Lemma
    (requires (
      bounded_map_constraint env.e_sem_env.se_bound cut1 /\
      bounded_map_constraint env.e_sem_env.se_bound cut2 /\
      Spec.map_constraint_equiv (map_constraint_sem env.e_sem_env cut1) (map_constraint_sem env.e_sem_env cut2) /\
      bounded_elab_map_group env.e_sem_env.se_bound g
    ))
    (ensures (
      annot_tables'_correct'_post fuel env cut1 cut2 g
    ))
    (decreases g)
= match g with
  | MGChoice g1 g2 ->
    annot_tables'_correct' fuel env cut1 cut2 g1;
    begin match annot_tables' fuel env cut1 g1 with
    | RSuccess (cut11, g11) ->
      assert (RSuccess? (annot_tables fuel env cut2 g1));
      let RSuccess (cut12, g12) = annot_tables fuel env cut2 g1 in
      assert (elab_map_group_sem env.e_sem_env g11 == elab_map_group_sem env.e_sem_env g12);
      let extracted_cut = extract_cut g1 in
      begin match mk_mc_or fuel env cut1 extracted_cut with
      | RSuccess cut_ ->
        annot_tables'_correct' fuel env cut_ (MCOr cut2 extracted_cut) g2;
        begin match annot_tables' fuel env cut_ g2 with
        | RSuccess (cut21, g21) -> ()
        | _ -> ()
        end
      | _ -> ()
      end
    | _ -> ()
    end
  | MGConcat g1 g2 ->
    annot_tables'_correct' fuel env cut1 cut2 g1;
    begin match annot_tables' fuel env cut1 g1 with
    | RSuccess (cut11, g11) ->
      let RSuccess (cut12, g12) = annot_tables fuel env cut2 g1 in
      annot_tables'_correct' fuel env cut11 cut12 g2;
      begin match annot_tables' fuel env cut11 g2 with
      | RSuccess (cut21, g21) ->
        let RSuccess (cut22, g22) = annot_tables fuel env cut12 g2 in
        assert (elab_map_group_sem env.e_sem_env g11 == elab_map_group_sem env.e_sem_env g12);
        assert (elab_map_group_sem env.e_sem_env g21 == elab_map_group_sem env.e_sem_env g22);
        elab_map_group_sem_concat env.e_sem_env g11 g21;
        elab_map_group_sem_concat env.e_sem_env g12 g22;
        assert (elab_map_group_sem env.e_sem_env (MGConcat g11 g21) == elab_map_group_sem env.e_sem_env (MGConcat g12 g22));
        assert (Spec.map_constraint_equiv (map_constraint_sem env.e_sem_env cut21) (map_constraint_sem env.e_sem_env cut22));
        assert (annot_tables fuel env cut2 g == RSuccess (cut22, MGConcat g12 g22));
        assert (annot_tables'_correct'_post fuel env cut1 cut2 g);
        ()
      | _ -> ()
      end
    | _ -> ()
    end
  | MGTable key value MCFalse ->
    begin match mk_mc_or fuel env cut1 (MCKeyValue key value) with
    | RSuccess mc' ->
      assert (Spec.map_constraint_equiv
        (map_constraint_sem env.e_sem_env mc')
        (map_constraint_sem env.e_sem_env (MCOr cut2 (MCKeyValue key value)))
      );
      map_group_filtered_table_except_ext
        (typ_sem env.e_sem_env key) (typ_sem env.e_sem_env value)
        (map_constraint_sem env.e_sem_env cut1)
        (map_constraint_sem env.e_sem_env cut2);
      ()
    | _ -> ()
    end
  | _ -> ()

#pop-options

let annot_tables'_correct
  (fuel: nat)
  (env: ast_env)
  (g: elab_map_group)
: Lemma
    (requires (
      bounded_elab_map_group env.e_sem_env.se_bound g
    ))
    (ensures (
      bounded_elab_map_group env.e_sem_env.se_bound g /\
      begin match annot_tables' fuel env MCFalse g with
      | RSuccess (cut', g') ->
        bounded_map_constraint env.e_sem_env.se_bound cut' /\
        bounded_elab_map_group env.e_sem_env.se_bound g' /\
        elab_map_group_sem env.e_sem_env g == elab_map_group_sem env.e_sem_env g'
      | _ -> True
      end
    ))
= annot_tables_correct fuel env g;
  annot_tables'_correct' fuel env MCFalse MCFalse g

#push-options "--z3rlimit 128 --split_queries always --query_stats --fuel 4 --ifuel 8"

#restart-solver
let rec mk_wf_typ
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (guard_choices: bool)
  (g: typ)
: Pure (result (ast0_wf_typ g))
    (requires typ_bounded env.e_sem_env.se_bound g)
    (ensures fun r -> match r with
    | RSuccess s -> spec_wf_typ env.e_sem_env guard_choices g s
    | _ -> True
    )
    (decreases fuel) // because of the restrict_map_group computation
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match g with
  | TNamed _ t ->
    begin match mk_wf_typ fuel' env guard_choices t with
    | RSuccess s -> RSuccess (WfTRewrite g t s)
    | res -> coerce_failure res
    end
  | TElem e ->
    RSuccess (WfTElem e)
  | TArray g' ->
    begin match mk_wf_array_group fuel' env g' with
    | RSuccess s' -> RSuccess (WfTArray g' s')
    | res -> coerce_failure res
    end
  | TMap m ->
    mk_elab_map_group_correct fuel env m;
    begin match mk_elab_map_group fuel env m with
    | RSuccess m1 ->
(*  
    begin match mk_wf_validate_map_group fuel' env Spec.t_always_false Spec.t_always_false (TElem EAlwaysFalse) (TElem EAlwaysFalse) m with
    | RSuccess s1 ->
      begin match restrict_map_group fuel env (TElem EAlwaysFalse) m with
      | RSuccess m2 ->
        rewrite_group_correct env.e_sem_env fuel m2;
        let m3 = rewrite_group fuel _ m2 in
*)      
      begin match annot_tables' fuel env MCFalse m1 with
      | RSuccess (_, m2) ->
        annot_tables'_correct fuel env m1;
        begin match mk_wf_parse_map_group fuel' env m2 with
        | RSuccess s3 -> RSuccess (WfTMap m (* _ _ s1.wf *) m2 s3)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end      
    | res -> coerce_failure res
    end
  | TTagged tag t' ->
    begin match mk_wf_typ fuel' env true t' with
    | RSuccess s' -> RSuccess (WfTTagged tag t' s')
    | res -> coerce_failure res
    end
  | TChoice t1 t2 ->
    begin match if guard_choices then typ_disjoint fuel env t1 t2 else RSuccess () with
    | RSuccess _ ->
      begin match mk_wf_typ fuel' env guard_choices t1 with
      | RSuccess s1 ->
        begin match mk_wf_typ fuel' env guard_choices t2 with
        | RSuccess s2 -> RSuccess (WfTChoice t1 t2 s1 s2)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | TDef n -> RSuccess (WfTDef n)
  | TDetCbor base dest ->
    let res1 = typ_included fuel env base (TElem EByteString) in
    if not (RSuccess? res1)
    then coerce_failure res1
    else let res2 = typ_included fuel env (TElem EByteString) base in
    if not (RSuccess? res2)
    then coerce_failure res2
    else begin match mk_wf_typ fuel' env true dest with
    | RSuccess wfdest -> RSuccess (WfTDetCbor base dest wfdest)
    | res -> coerce_failure res
    end
  | TRange tlo included thi ->
    begin match extract_range_value env.e_sem_env g with
    | None -> RFailure "mk_wf_typ: TRange: invalid range"
    | Some (lo, hi) ->
      let lo = eval_int_value lo in
      let hi = eval_int_value hi in
      if lo > hi
      then RFailure "mk_wf_typ: empty range"
      else if (lo < - pow2 63 && hi >= 0) || (lo < 0 && hi >= pow2 63)
      then RFailure "mk_wf_typ: TRange too wide, not representable"
      else begin
        assert_norm (pow2 64 == pow2 63 + pow2 63);
        assert (lo >= 0 ==> hi < pow2 64);
        assert (hi < 0 ==> lo >= - pow2 64);
        assert ((lo < 0 /\ hi >= 0) ==> (lo >= - pow2 63 /\ hi < pow2 63));
        assert (
          begin if lo >= 0
          then hi < pow2 64
          else if hi < 0
          then lo >= - pow2 64
          else (lo >= - pow2 63 /\ hi < pow2 63)
          end
        );
        let res = WfTIntRange tlo included thi lo hi in
        assert (bounded_wf_typ env.e_sem_env.se_bound _ res);
        RSuccess res
      end
    end
  | TSize base ti ->
    begin match typ_included fuel env base (TElem EUInt) with
    | ROutOfFuel -> ROutOfFuel
    | RSuccess _ ->
      let res2 = typ_included fuel env (TElem EUInt) base in
      if not (RSuccess? res2)
      then coerce_failure res2
      else begin match extract_int_value env.e_sem_env ti with
      | None -> RFailure "mk_wf_typ: uint .size, not int"
      | Some ri ->
        let j = eval_int_value ri in
        if j < 0
        then RFailure "mk_wf_typ: uint .size negative"
        else let i = (let open FStar.Mul in 8 * j) in
        if i >= 64
        then begin
          FStar.Math.Lemmas.pow2_le_compat i 64;
          RSuccess (WfTRewrite _ _ (WfTElem EUInt))
        end
        else begin
          FStar.Math.Lemmas.pow2_lt_compat 64 i;
          RSuccess (WfTRewrite _ _ (WfTIntRange (TElem (ELiteral (LInt 0))) true (TElem (ELiteral (LInt (pow2 i - 1)))) 0 (pow2 i - 1)))
        end
      end
    | RFailure _ ->
      begin match extract_range_value env.e_sem_env ti with
      | None -> RFailure "string .size not range"
      | Some (rlo, rhi) ->
        let lo = eval_int_value rlo in
        let hi = eval_int_value rhi in
        begin match typ_included fuel env base (TElem EByteString) with
        | ROutOfFuel -> ROutOfFuel
        | RSuccess _ ->
          let res3 = typ_included fuel env (TElem EByteString) base in
          if not (RSuccess? res3)
          then coerce_failure res3
          else if 0 <= lo && lo <= hi
          then RSuccess (WfTStrSize (U8.v Cbor.cbor_major_type_byte_string) base ti lo hi)
          else RFailure "mk_wf_typ: bstr .size with empty range"
        | RFailure _ ->
          let res4 = typ_included fuel env base (TElem ETextString) in
          if not (RSuccess? res4)
          then coerce_failure res4
          else let res5 = typ_included fuel env (TElem ETextString) base in
          if not (RSuccess? res5)
          then coerce_failure res5
          else if 0 <= lo && lo <= hi
          then RSuccess (WfTStrSize (U8.v Cbor.cbor_major_type_text_string) base ti lo hi)
          else RFailure "mk_wf_typ tstr .size with empty range"
        end
      end
    end

and mk_wf_array_group
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (g: group)
: Pure (result (ast0_wf_array_group g))
    (requires group_bounded env.e_sem_env.se_bound g)
    (ensures fun r -> match r with
    | RSuccess s -> spec_wf_array_group env.e_sem_env g s
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match g with
  | GElem _cut _key ty ->
    begin match mk_wf_typ fuel' env true ty with
    | RSuccess s -> RSuccess (WfAElem _cut _key ty s)
    | res -> coerce_failure res
    end
  | GZeroOrOne g' ->
    begin match array_group_is_nonempty fuel env g' with
    | RSuccess _ ->
      begin match mk_wf_array_group fuel' env g' with
      | RSuccess s' -> RSuccess (WfAZeroOrOne g' s')
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | GConcat g1 g2 ->
    begin match mk_wf_array_group fuel' env g1 with
    | RSuccess s1 ->
      begin match mk_wf_array_group fuel' env g2 with
      | RSuccess s2 ->
        begin match array_group_concat_unique_weak (array_group_disjoint fuel) fuel env s1 s2 with
        | RSuccess _ -> RSuccess (WfAConcat g1 g2 s1 s2)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | GChoice g1 g2 ->
    begin match array_group_disjoint fuel env false true g1 g2 with
    | RSuccess _ ->
      begin match mk_wf_array_group fuel' env g1 with
      | RSuccess s1 ->
        begin match mk_wf_array_group fuel' env g2 with
        | RSuccess s2 -> RSuccess (WfAChoice g1 g2 s1 s2)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | GDef n ->
    let g2 = env.e_env n in
    begin match mk_wf_array_group fuel' env g2 with
    | RSuccess s2 -> RSuccess (WfARewrite g g2 s2)
    | res -> coerce_failure res
    end
  | GNop -> RFailure "mk_wf_array_group: unsupported: GNop"
  | GAlwaysFalse -> RFailure "mk_wf_array_group: unsupported: GAlwaysFalse"
  | g ->
    let g' = match g with
    | GZeroOrMore g' -> g'
    | GOneOrMore g' -> g'
    in
    begin match array_group_is_nonempty fuel env g' with
    | RSuccess _ ->
      begin match mk_wf_array_group fuel' env g' with
      | RSuccess s' ->
        begin match array_group_concat_unique_strong (array_group_disjoint fuel) fuel env s' g' with
        | RSuccess _ -> RSuccess (WfAZeroOrOneOrMore g' s' g)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end

and mk_wf_parse_map_group
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (g: elab_map_group)
: Pure (result (ast0_wf_parse_map_group g))
    (requires bounded_elab_map_group env.e_sem_env.se_bound g)
    (ensures fun r -> match r with
    | RSuccess s -> spec_wf_parse_map_group env.e_sem_env g s
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match g with
  | MGChoice g' MGNop ->
    begin match apply_map_group_det_empty_fail g' with
    | RSuccess true ->
      apply_map_group_det_empty_fail_correct env.e_sem_env g';
      begin match mk_wf_parse_map_group fuel' env g' with
      | RSuccess s' -> RSuccess (WfMZeroOrOne g' s')
      | res -> coerce_failure res
      end
    | RSuccess _ -> RFailure "mk_wf_parse_map_group: group does not fail on empty"
    | res -> coerce_failure res
    end
  | MGChoice g1 g2 ->
    begin match mk_wf_parse_map_group fuel' env g1 with
    | RSuccess s1 ->
      begin match mk_wf_parse_map_group fuel' env g2 with
      | RSuccess s2 -> 
        begin match map_group_choice_compatible fuel env s1 s2 with
        | RSuccess _ -> RSuccess (WfMChoice g1 s1 g2 s2)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | MGMatch cut name key value ->
    begin match mk_wf_typ fuel' env true value with
    | RSuccess tvalue -> RSuccess (WfMLiteral cut name key value tvalue)
    | res -> coerce_failure res
    end
  | MGTable key value except ->
    begin match mk_wf_typ fuel' env true key with
    | RSuccess tkey ->
      begin match mk_wf_typ fuel' env true value with
      | RSuccess tvalue -> 
        begin match mk_wf_map_constraint fuel' env except with
        | RSuccess texcept ->
          RSuccess (WfMZeroOrMore key value except tkey tvalue texcept)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | MGConcat g1 g2 ->
    begin match map_group_footprint (typ_disjoint fuel) fuel env g1 with
    | RSuccess te1 ->
      begin match map_group_footprint (typ_disjoint fuel) fuel env g2 with
      | RSuccess te2 ->
        begin match map_constraint_disjoint (typ_disjoint fuel) (typ_included fuel) env te1 te2 with
        | RSuccess _ ->
          begin match mk_wf_parse_map_group fuel' env g1 with
          | RSuccess s1 ->
            begin match mk_wf_parse_map_group fuel' env g2 with
            | RSuccess s2 -> RSuccess (WfMConcat g1 s1 g2 s2)
            | res -> coerce_failure res
            end
          | res -> coerce_failure res
          end
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | MGNop -> RSuccess (WfMNop ())
  | _ -> RFailure "mk_wf_parse_map_group: unsupported"

and mk_wf_map_constraint
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (g: map_constraint)
: Pure (result (ast0_wf_map_constraint g))
    (requires bounded_map_constraint env.e_sem_env.se_bound g)
    (ensures fun r -> match r with
    | RSuccess s -> spec_wf_map_constraint env.e_sem_env g s
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel'  : nat = fuel - 1 in
  match g with
  | MCFalse -> RSuccess WfMCFalse
  | MCKeyValue k v ->
    begin match mk_wf_typ fuel' env false k with
    | RSuccess tk ->
      begin match mk_wf_typ fuel' env false v with
      | RSuccess tv ->
        RSuccess (WfMCKeyValue k tk v tv)
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | MCNot g1 ->
    begin match mk_wf_map_constraint fuel' env g1 with
    | RSuccess tg1 -> RSuccess (WfMCNot g1 tg1)
    | res -> coerce_failure res
    end
  | MCAnd g1 g2 ->
    begin match mk_wf_map_constraint fuel' env g1 with
    | RSuccess tg1 ->
      begin match mk_wf_map_constraint fuel' env g2 with
      | RSuccess tg2 -> RSuccess (WfMCAnd g1 tg1 g2 tg2)
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | MCOr g1 g2 ->
    begin match mk_wf_map_constraint fuel' env g1 with
    | RSuccess tg1 ->
      begin match mk_wf_map_constraint fuel' env g2 with
      | RSuccess tg2 -> RSuccess (WfMCOr g1 tg1 g2 tg2)
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end

(*
and mk_wf_validate_map_group
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (left_elems: Spec.typ)
  (left_tables: Spec.typ)
  (left_elems0: typ)
  (left_tables0: typ)
  (g: group)
: Pure (result (mk_wf_validate_map_group_t left_elems left_tables g))
    (requires group_bounded _ env.e_sem_env.se_bound g /\
      typ_bounded env.e_sem_env.se_bound left_elems0 /\
      typ_bounded env.e_sem_env.se_bound left_tables0 /\
      typ_sem env.e_sem_env left_elems0 `Spec.typ_equiv` left_elems /\
      typ_sem env.e_sem_env left_tables0 `Spec.typ_equiv` left_tables
    )
    (ensures fun r -> match r with
    | RSuccess s -> spec_wf_validate_map_group env.e_sem_env left_elems left_tables g s.left_elems1 s.left_tables1 s.wf /\
      typ_bounded env.e_sem_env.se_bound s.left_elems10 /\
      typ_bounded env.e_sem_env.se_bound s.left_tables10 /\
      typ_sem env.e_sem_env s.left_elems10 `Spec.typ_equiv` s.left_elems1 /\
      typ_sem env.e_sem_env s.left_tables10 `Spec.typ_equiv` s.left_tables1
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match g with
  | GChoice g1 g2 ->
    begin match mk_wf_validate_map_group fuel' env left_elems left_tables left_elems0 left_tables0 g1 with
    | RSuccess s1 ->
      begin match mk_wf_validate_map_group fuel' env left_elems left_tables left_elems0 left_tables0 g2 with
      | RSuccess s2 ->
        RSuccess {
          left_elems1 = s1.left_elems1 `Spec.t_choice` s2.left_elems1;
          left_tables1 = s1.left_tables1 `Spec.t_choice` s2.left_tables1;
          wf = RMChoice left_elems left_tables g1 s1.left_elems1 s1.left_tables1 s1.wf g2 s2.left_elems1 s2.left_tables1 s2.wf;
          left_elems10 = s1.left_elems10 `TChoice` s2.left_elems10;
          left_tables10 = s1.left_tables10 `TChoice` s2.left_tables10;
        }
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | GConcat g1 g2 ->
    begin match mk_wf_validate_map_group fuel' env left_elems left_tables left_elems0 left_tables0 g1 with
    | RSuccess s1 ->
      begin match mk_wf_validate_map_group fuel' env s1.left_elems1 s1.left_tables1 s1.left_elems10 s1.left_tables10 g2 with
      | RSuccess s2 ->
        RSuccess {
          left_elems1 = s2.left_elems1;
          left_tables1 = s2.left_tables1;
          wf = RMConcat left_elems left_tables g1 s1.left_elems1 s1.left_tables1 s1.wf g2 s2.left_elems1 s2.left_tables1 s2.wf;
          left_elems10 = s2.left_elems10;
          left_tables10 = s2.left_tables10;
        }
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | GZeroOrOne g' ->
    begin match mk_wf_validate_map_group fuel' env left_elems left_tables left_elems0 left_tables0 g' with
    | RSuccess s' ->
      RSuccess {
        left_elems1 = s'.left_elems1;
        left_tables1 = s'.left_tables1;
        wf = RMZeroOrOne left_elems left_tables g' s'.left_elems1 s'.left_tables1 s'.wf;
        left_elems10 = s'.left_elems10;
        left_tables10 = s'.left_tables10;
      }
    | res -> coerce_failure res
    end
  | GMapElem _ cut (TElem (ELiteral key)) value ->
    begin match typ_disjoint env fuel (left_elems0 `TChoice` left_tables0) (TElem (ELiteral key)) with
    | RSuccess _ ->
      begin match mk_wf_typ fuel' env value with
      | RSuccess tvalue -> RSuccess {
          left_elems1 = _;
          left_tables1 = _;
          wf = RMElemLiteral left_elems left_tables cut key value tvalue;
          left_elems10 = left_elems0 `TChoice` TElem (ELiteral key);
          left_tables10 = left_tables0;
        }
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | GZeroOrMore (GMapElem _ false key value) ->
    begin match typ_disjoint env fuel left_tables0 key with
    | RSuccess _ ->
      begin match mk_wf_typ fuel' env key with
      | RSuccess tkey ->
        begin match mk_wf_typ fuel' env value with
        | RSuccess tvalue -> RSuccess {
          left_elems1 = _;
          left_tables1 = _;
          wf = RMZeroOrMore left_elems left_tables key value tkey tvalue (typ_sem env.e_sem_env key);
          left_elems10 = left_elems0;
          left_tables10 = left_tables0 `TChoice` key;
        }
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end    
  | _ -> RFailure "mk_wf_validate_map_group: unsupported"
*)

#pop-options

let mk_wf_typ_bounded
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (g: typ)
: Pure (result (ast0_wf_typ g))
    (requires (typ_bounded env.e_sem_env.se_bound g))
    (ensures (fun res -> match res with
    | RSuccess s' ->
      typ_bounded env.e_sem_env.se_bound g /\
      bounded_wf_typ env.e_sem_env.se_bound g s' /\
      spec_wf_typ env.e_sem_env true g s'
    | _ -> True
    ))
=
    rewrite_typ_correct env.e_sem_env fuel g;
    let (g', res) = rewrite_typ fuel g in
    if res then
    match mk_wf_typ fuel env true g' with
    | RSuccess s' -> RSuccess (WfTRewrite g g' s')
    | res -> coerce_failure res
    else ROutOfFuel

let mk_wf_typ_post
  (e: ast_env)
  (t: typ)
  (res: result (ast0_wf_typ t))
: Tot prop
= match res with
    | RSuccess t_wf ->
      typ_bounded e.e_sem_env.se_bound t /\
      bounded_wf_typ e.e_sem_env.se_bound t t_wf /\
      spec_wf_typ e.e_sem_env true t t_wf
    | _ -> True

let mk_wf_typ'
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (g: typ)
: Tot (res: result (ast0_wf_typ g) { mk_wf_typ_post env g res })
= if typ_bounded env.e_sem_env.se_bound g
  then mk_wf_typ_bounded fuel env g
  else RFailure "mk_wf_typ: not bounded"

let prune_result
  (#t: Type)
  (r: result t)
: Tot (result unit)
= match r with
  | RSuccess _ -> RSuccess ()
  | res -> coerce_failure res

let typ_of
  (e: ast_env)
  (name: string)
: Tot typ
= match e.e_sem_env.se_bound name with
  | Some NType -> e.e_env name
  | _ -> TElem EAlwaysFalse

let mk_wf_typ_fuel_for
  (e: ast_env)
  (t: typ)
: Tot Type0
= (fuel: nat { prune_result (mk_wf_typ' fuel e t) == RSuccess () })

[@@sem_attr]
let mk_wf_typ_fuel_for_intro
  (fuel: nat)
  (e: ast_env)
  (t: typ)
  (prf: squash (prune_result (mk_wf_typ' fuel e t) == RSuccess ()))
: Tot (mk_wf_typ_fuel_for e t)
= fuel

[@@sem_attr]
let compute_wf_typ
  (e: wf_ast_env)
  (new_name: string)
  (new_name_is_type: squash (e.e_sem_env.se_bound new_name == None))
  (t: typ)
  (fuel: mk_wf_typ_fuel_for e t)
: Tot (t_wf: ast0_wf_typ t {
    wf_ast_env_extend_typ_with_weak_pre e new_name t t_wf
  })
= let t_wf = RSuccess?._0 (mk_wf_typ' fuel e t) in
  assert (wf_ast_env_extend_typ_with_weak_pre e new_name t t_wf);
  t_wf

let compute_wf_typ'_post
  (e: ast_env)
  (new_name: string)
  (t: typ)
  (res: result (ast0_wf_typ t))
: Tot prop
= match res with
    | RSuccess t_wf ->
      wf_ast_env_extend_typ_with_weak_pre e new_name t t_wf
    | _ -> True

[@@sem_attr]
let compute_wf_typ'
  (e: ast_env)
  (new_name: string)
  (new_name_is_type: squash (e.e_sem_env.se_bound new_name == None))
  (t: typ)
  (fuel: nat)
: Tot (res: result (ast0_wf_typ t) {
    compute_wf_typ'_post e new_name t res
  })
= match mk_wf_typ' fuel e t with
  | RSuccess res -> RSuccess res
  | RFailure s -> RFailure s
  | ROutOfFuel -> ROutOfFuel

[@@sem_attr]
let extract_computed_wf_typ'
  (e: ast_env)
  (new_name: string)
  (t: typ)
  (fuel: nat)
  ([@@@erasable] res: Ghost.erased (result (ast0_wf_typ t)) {
    compute_wf_typ'_post e new_name t res
  })
  (res': result (ast0_wf_typ t))
  (sq: squash (res' == Ghost.reveal res))
  (res_success: squash (RSuccess? res'))
: Tot (t_wf: ast0_wf_typ t {
      wf_ast_env_extend_typ_with_weak_pre e new_name t t_wf /\
      typ_bounded e.e_sem_env.se_bound t
  })
= RSuccess?._0 res'

[@@sem_attr]
let wf_ast_env_extend_typ
  (e: wf_ast_env)
  (new_name: string)
  (new_name_is_type: squash (e.e_sem_env.se_bound new_name == None))
  (t: typ)
  (fuel: mk_wf_typ_fuel_for e t)
: Tot (e': wf_ast_env {
      ast_env_included e e' /\
      e'.e_sem_env.se_bound new_name == Some NType /\
      t == e'.e_env new_name
  })
= let t_wf = RSuccess?._0 (mk_wf_typ' fuel e t) in
  assert (wf_ast_env_extend_typ_with_weak_pre e new_name t t_wf);
  wf_ast_env_extend_typ_with_weak e new_name t t_wf

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
      (typ_diff_disjoint fuel)
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
      (typ_diff_disjoint fuel)
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
  | GElem cut (TElem (ELiteral key)) value ->
    RSuccess (MGMatch cut key value)
  | GElem true key value ->
    RSuccess (MGMatchWithCut key (TElem EAlwaysFalse) value)
  | GAlwaysFalse -> RSuccess MGAlwaysFalse
  | GNop -> RSuccess MGNop
  | GZeroOrOne g ->
    begin match mk_elab_map_group fuel' env g with
    | RSuccess g' -> RSuccess (MGChoice g' MGNop)
    | err -> err
    end
  | GZeroOrMore (GElem false key value) ->
    RSuccess (MGTable key (TElem EAlwaysFalse) value)
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
  | _ -> RFailure "mk_elab_map_group: unsupported"

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
      (Util.notp (Spec.matches_map_group_entry (Util.andp (typ_sem env.e_sem_env key) (Util.notp Spec.t_always_false)) (typ_sem env.e_sem_env value)))
      (Util.notp (Spec.matches_map_group_entry (typ_sem env.e_sem_env key) (typ_sem env.e_sem_env value)))
  | GElem cut key value ->
    Spec.map_group_match_item_ext
      cut
      (Util.andp (typ_sem env.e_sem_env key) (Util.notp Spec.t_always_false))
      (typ_sem env.e_sem_env value)
      (typ_sem env.e_sem_env key)
      (typ_sem env.e_sem_env value)
  | GDef n ->
    let g' = (env.e_env n) in
    rewrite_group_correct env.e_sem_env fuel true g';
    mk_elab_map_group_correct fuel' env (fst (rewrite_group fuel true g'))
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
: Tot typ
= match g with
  | MGMatch true key _ -> (TElem (ELiteral key))
  | MGMatchWithCut key (TElem EAlwaysFalse) _ -> key
  | MGChoice g1 _ -> extract_cut g1
  | _ -> (TElem EAlwaysFalse)

let rec bounded_extract_cut
  (env: name_env)
  (g: elab_map_group)
: Lemma
  (requires (bounded_elab_map_group env g))
  (ensures (let (key) = extract_cut g in
  typ_bounded env key
  ))
  (decreases g)
  [SMTPat (bounded_elab_map_group env g); SMTPat (extract_cut g)]
= match g with
  | MGChoice g1 _ -> bounded_extract_cut env g1
  | _ -> ()

let cbor_map_disjoint_from_footprint_always_false
  (m: Cbor.cbor_map)
: Lemma
  (Spec.cbor_map_disjoint_from_footprint m Spec.t_always_false)
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
    typ_bounded env.se_bound key /\
    begin
      match Spec.apply_map_group_det (elab_map_group_sem env g) m with
      | Spec.MapGroupDet _ m1 -> Spec.cbor_map_disjoint_from_footprint m1 (typ_sem env key)
      | Spec.MapGroupFail -> Spec.cbor_map_disjoint_from_footprint m (typ_sem env key)
      | _ -> True
    end
  ))
  (decreases g)
= let (key) = extract_cut g in
  assert (typ_bounded env.se_bound key);
  match g with
  | MGChoice g1 _ ->
    extract_cut_correct env g1 m
  | MGMatch true key _ -> ()
  | MGMatchWithCut key (TElem EAlwaysFalse) _ ->
    let ty = typ_sem env key in
    assert (CDDL.Spec.Base.typ_equiv ty (Util.andp ty (Util.notp (elem_typ_sem EAlwaysFalse))));
    ()
  | _ -> cbor_map_disjoint_from_footprint_always_false m

#pop-options

let rec annot_tables
  (fuel: nat)
  (env: ast_env)
  (cut: typ)
  (g: elab_map_group)
: Pure (result (typ & elab_map_group))
    (requires (
      typ_bounded env.e_sem_env.se_bound cut /\
      bounded_elab_map_group env.e_sem_env.se_bound g
    ))
    (ensures (fun res -> match res with
    | RSuccess (cut', g') -> 
      typ_bounded env.e_sem_env.se_bound cut' /\
      bounded_elab_map_group env.e_sem_env.se_bound g'
    | _ -> True
    ))
    (decreases g)
= match g with
  | MGChoice g1 g2 ->
    begin match annot_tables fuel env cut g1 with
    | RSuccess (cut1, g1') ->
      let (extracted_cut) = extract_cut g1 in
      begin match annot_tables fuel env (mk_TChoice cut extracted_cut) g2 with
      | RSuccess (cut2, g2') ->
        begin match typ_inter_underapprox fuel env cut1 cut2 with
        | RSuccess cut' -> RSuccess (cut', MGChoice g1' g2')
        | res -> coerce_failure res
        end
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
  | MGTable key (TElem EAlwaysFalse) value ->
    begin match typ_inter_underapprox fuel env cut key with
    | RSuccess key_except ->
      RSuccess (cut, MGTable key key_except value)
    | res -> coerce_failure res
    end
  | MGTable _ _ _ -> RFailure "annot_tables cannot be run twice"
  | MGMatch _ key _ ->
    begin match typ_included fuel env (TElem (ELiteral key)) cut with
    | RSuccess _ -> RSuccess (cut, MGAlwaysFalse)
    | RFailure _ -> RSuccess (mk_TChoice cut (TElem (ELiteral key)), g)
    | ROutOfFuel -> ROutOfFuel
    end
  | MGMatchWithCut key (TElem EAlwaysFalse) value ->
    begin match typ_inter_underapprox fuel env cut key with
    | RSuccess key_except -> RSuccess (mk_TChoice cut key, MGMatchWithCut key key_except value)
    | res -> coerce_failure res
    end
  | MGMatchWithCut _ _ _ -> RFailure "annot_tables cannot be run twice: MGMatchWithCut"
  | MGCut key -> RSuccess (mk_TChoice cut key, g)
  | MGAlwaysFalse -> RSuccess (TElem EAny, g)
  | MGNop -> RSuccess (cut, g)

let annot_tables_correct_postcond
  (fuel: nat)
  (env: ast_env)
  (cut: typ)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
: GTot prop
=
    typ_bounded env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    begin match annot_tables fuel env cut g with
    | RSuccess (cut', g') ->
      let a = Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m in
      typ_bounded env.e_sem_env.se_bound cut' /\
      bounded_elab_map_group env.e_sem_env.se_bound g' /\
      a == Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m /\
      begin match a with
      | Spec.MapGroupDet _ m' -> Spec.cbor_map_disjoint_from_footprint m' (typ_sem env.e_sem_env cut')
      | _ -> True
      end
    | _ -> True
    end        

let cbor_map_filter_ext_strong
  (f1 f2: (Cbor.cbor & Cbor.cbor) -> Tot bool)
  (m: Cbor.cbor_map)
: Lemma
  (requires forall x . Cbor.cbor_map_mem x m ==> f1 x == f2 x)
  (ensures Cbor.cbor_map_filter f1 m == Cbor.cbor_map_filter f2 m)
= Cbor.cbor_map_ext (Cbor.cbor_map_filter f1 m) (Cbor.cbor_map_filter f2 m)

#restart-solver
let apply_map_group_det_match_item_cut_is_equal
  (k1: Spec.typ)
  (k2: Spec.typ)
  (ty: Spec.typ)
  (l: Cbor.cbor_map)
: Lemma
  (requires (
    Cbor.cbor_map_filter (Spec.matches_map_group_entry k1 Spec.any) l == 
    Cbor.cbor_map_filter (Spec.matches_map_group_entry k2 Spec.any) l    
  ))
  (ensures (
    Spec.apply_map_group_det (Spec.map_group_match_item true k1 ty) l ==  Spec.apply_map_group_det (Spec.map_group_match_item true k2 ty) l
  ))
= let s = Cbor.cbor_map_filter (Spec.matches_map_group_entry k1 Spec.any) l in
  assert (Cbor.cbor_map_equal (Cbor.cbor_map_sub l s) (Cbor.cbor_map_filter (CBOR.Spec.Util.notp (Spec.matches_map_group_entry k1 Spec.any)) l));
  assert (Cbor.cbor_map_equal (Cbor.cbor_map_sub l s) (Cbor.cbor_map_filter (CBOR.Spec.Util.notp (Spec.matches_map_group_entry k2 Spec.any)) l));
  assert ((Cbor.cbor_map_filter (CBOR.Spec.Util.notp (Spec.matches_map_group_entry k1 Spec.any)) l) == (Cbor.cbor_map_filter (CBOR.Spec.Util.notp (Spec.matches_map_group_entry k2 Spec.any)) l));
  Spec.apply_map_group_det_match_item_cut k1 ty l;
  Spec.apply_map_group_det_match_item_cut k2 ty l;
  ()

let cbor_map_disjoint_from_footprint_choice
  (m: Cbor.cbor_map)
  (f1 f2: Spec.typ)
: Lemma
  (requires (
    Spec.cbor_map_disjoint_from_footprint m f1 /\
    Spec.cbor_map_disjoint_from_footprint m f2
  ))
  (ensures (
    Spec.cbor_map_disjoint_from_footprint m (Spec.t_choice f1 f2)
  ))
= ()

#push-options "--z3rlimit 256 --ifuel 8 --fuel 4 --query_stats --split_queries always"

#restart-solver
let rec annot_tables_correct_aux'
  (fuel: nat)
  (env: ast_env)
  (cut: typ)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
  (sq: squash (
    typ_bounded env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    Spec.cbor_map_disjoint_from_footprint m (typ_sem env.e_sem_env cut)
  ))
: Lemma (ensures (annot_tables_correct_postcond fuel env cut g m))
  (decreases g)
= 
  match g with
  | MGChoice g1 g2 ->
    let (extracted_cut) = extract_cut g1 in
    annot_tables_correct_aux' fuel env cut g1 m ();
    mk_TChoice_sem env.e_sem_env cut extracted_cut;
    extract_cut_correct env.e_sem_env g1 m;
    begin match Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g1) m with
    | Spec.MapGroupFail ->
      annot_tables_correct_aux' fuel env (mk_TChoice cut extracted_cut) g2 m ();
      assert (annot_tables_correct_postcond fuel env cut g m)
    | _ -> assert (annot_tables_correct_postcond fuel env cut g m)
    end
  | MGConcat g1 g2 ->
    begin match annot_tables fuel env cut g1 with
    | RSuccess (cut1, g1') ->
      annot_tables_correct_aux' fuel env cut g1 m ();
      begin match Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g1) m with
      | Spec.MapGroupDet _ m1 ->
        annot_tables_correct_aux' fuel env cut1 g2 m1 ();
        assert (annot_tables_correct_postcond fuel env cut g m)
      | res ->
        assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m == res);
        assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g1') m == res);
        begin match annot_tables fuel env cut1 g2 with
        | RSuccess (cut2, g2') ->
          assert (Spec.apply_map_group_det (Spec.map_group_concat (elab_map_group_sem env.e_sem_env g1') (elab_map_group_sem env.e_sem_env g2')) m == res);
          assert (annot_tables_correct_postcond fuel env cut g m)
        | _ -> assert (annot_tables_correct_postcond fuel env cut g m)
        end
      end
    | _ -> assert (annot_tables_correct_postcond fuel env cut g m)
    end
  | MGMatch c key value ->
    Spec.apply_map_group_det_match_item_for c (eval_literal key) (typ_sem env.e_sem_env value) m;
    begin match typ_included fuel env (TElem (ELiteral key)) cut with
    | RSuccess _ ->
      assert (None? (Cbor.cbor_map_get m (eval_literal key)));
      assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m == Spec.MapGroupFail);
      assert (Spec.apply_map_group_det Spec.map_group_always_false m == Spec.MapGroupFail);
      assert (annot_tables_correct_postcond fuel env cut g m)
    | _ -> assert (annot_tables_correct_postcond fuel env cut g m)
    end
  | MGMatchWithCut key (TElem EAlwaysFalse) value ->
    let tkey = typ_sem env.e_sem_env key in
    let tvalue = (typ_sem env.e_sem_env value) in
    Spec.map_group_match_item_ext true tkey tvalue (Util.andp tkey (Util.notp (elem_typ_sem EAlwaysFalse))) tvalue;
    assert (elab_map_group_sem env.e_sem_env g == Spec.map_group_match_item true tkey tvalue);
    Spec.apply_map_group_det_match_item_cut tkey tvalue m;
    begin match typ_inter_underapprox fuel env cut key with
    | RSuccess key_except ->
      let tkey' = (Util.andp (typ_sem env.e_sem_env key) (Util.notp (typ_sem env.e_sem_env key_except))) in
      let f = (Spec.matches_map_group_entry tkey Spec.any) in
      let nf = Util.notp f in
      let mnf = Cbor.cbor_map_filter nf m in
      let mf = Cbor.cbor_map_filter f m in
      let g' = MGMatchWithCut key key_except value in
      assert (annot_tables fuel env cut g == RSuccess (mk_TChoice cut key, g'));
      assert (elab_map_group_sem env.e_sem_env g' == Spec.map_group_match_item true tkey' tvalue);
      Spec.apply_map_group_det_match_item_cut tkey' tvalue m;
      let f' = (Spec.matches_map_group_entry (Util.andp (typ_sem env.e_sem_env key) (Util.notp (typ_sem env.e_sem_env key_except))) Spec.any) in
      let nf' = Util.notp f in
      let mnf' = Cbor.cbor_map_filter nf' m in
      let mf' = Cbor.cbor_map_filter f' m in
      cbor_map_filter_ext_strong f f' m;
      assert (mf == mf');
      cbor_map_filter_ext_strong nf nf' m;
      assert (mnf == mnf');
      apply_map_group_det_match_item_cut_is_equal tkey tkey' tvalue m;
      assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m == Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m);
      assert (Spec.cbor_map_disjoint_from_footprint mnf (typ_sem env.e_sem_env key));
      assert (Spec.cbor_map_disjoint_from_footprint mnf (typ_sem env.e_sem_env cut));
      cbor_map_disjoint_from_footprint_choice mnf (typ_sem env.e_sem_env cut) (typ_sem env.e_sem_env key);
      assert (annot_tables_correct_postcond fuel env cut g m)
    | _ -> assert (annot_tables_correct_postcond fuel env cut g m)
    end
  | MGTable key (TElem EAlwaysFalse) value ->
    begin match typ_inter_underapprox fuel env cut key with
    | RSuccess key_except ->
      let nf = Util.notp (Spec.matches_map_group_entry (Util.andp (typ_sem env.e_sem_env key) (Util.notp (typ_sem env.e_sem_env (TElem EAlwaysFalse)))) (typ_sem env.e_sem_env value)) in
      let mnf = Cbor.cbor_map_filter nf m in
      let mnnf = Cbor.cbor_map_filter (Util.notp nf) m in
      assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m == Spec.MapGroupDet mnnf mnf);
      let g' = MGTable key key_except value in
      assert (annot_tables fuel env cut g == RSuccess (cut, g'));
      let nf' = Util.notp (Spec.matches_map_group_entry (Util.andp (typ_sem env.e_sem_env key) (Util.notp (typ_sem env.e_sem_env key_except))) (typ_sem env.e_sem_env value)) in
      let mnf' = Cbor.cbor_map_filter nf' m in
      let mnnf' = Cbor.cbor_map_filter (Util.notp nf') m in
      assert (Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m == Spec.MapGroupDet mnnf' mnf');
      cbor_map_filter_ext_strong nf nf' m;
      assert (mnf == mnf');
      assert (Cbor.cbor_map_equal mnnf mnnf');
      assert (Spec.cbor_map_disjoint_from_footprint mnf (typ_sem env.e_sem_env cut));
      assert (annot_tables_correct_postcond fuel env cut g m)
    | _ -> assert (annot_tables_correct_postcond fuel env cut g m)
    end
  | _ -> assert (annot_tables_correct_postcond fuel env cut g m)

#pop-options

let annot_tables_correct'
  (fuel: nat)
  (env: ast_env)
  (cut: typ)
  (g: elab_map_group)
  (m: Cbor.cbor_map)
: Lemma
  (requires (
    typ_bounded env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    Spec.cbor_map_disjoint_from_footprint m (typ_sem env.e_sem_env cut)
  ))
  (ensures (
    typ_bounded env.e_sem_env.se_bound cut /\
    bounded_elab_map_group env.e_sem_env.se_bound g /\
    begin match annot_tables fuel env cut g with
    | RSuccess (cut', g') ->
      let a = Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g) m in
      typ_bounded env.e_sem_env.se_bound cut' /\
      bounded_elab_map_group env.e_sem_env.se_bound g' /\
      a == Spec.apply_map_group_det (elab_map_group_sem env.e_sem_env g') m /\
      begin match a with
      | Spec.MapGroupDet _ m' -> Spec.cbor_map_disjoint_from_footprint m' (typ_sem env.e_sem_env cut')
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
    begin match annot_tables fuel env (TElem EAlwaysFalse) g with
    | RSuccess (cut', g') ->
      typ_bounded env.e_sem_env.se_bound cut' /\
      bounded_elab_map_group env.e_sem_env.se_bound g' /\
      elab_map_group_sem env.e_sem_env g == elab_map_group_sem env.e_sem_env g'
    | _ -> True
    end        
  ))
= match annot_tables fuel env (TElem EAlwaysFalse) g with
  | RSuccess (_, g') ->
    assert (forall (m: Cbor.cbor_map) . Spec.cbor_map_disjoint_from_footprint m (typ_sem env.e_sem_env (TElem EAlwaysFalse)));
    Classical.forall_intro (Classical.move_requires (annot_tables_correct' fuel env (TElem EAlwaysFalse) g));
    Spec.apply_map_group_det_map_group_equiv (elab_map_group_sem env.e_sem_env g) (elab_map_group_sem env.e_sem_env g')
  | _ -> ()
  
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
      begin match annot_tables fuel env (TElem EAlwaysFalse) m1 with
      | RSuccess (_, m2) ->
        annot_tables_correct fuel env m1;
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
  | MGMatch cut key value ->
    begin match mk_wf_typ fuel' env true value with
    | RSuccess tvalue -> RSuccess (WfMLiteral cut key value tvalue)
    | res -> coerce_failure res
    end
  | MGMatchWithCut key key_except value ->
    begin match mk_wf_typ fuel' env true key with
    | RSuccess tkey ->
      begin match mk_wf_typ fuel' env false key_except with
      | RSuccess tkey_except ->
        begin match mk_wf_typ fuel' env true value with
        | RSuccess tvalue -> RSuccess (WfMMatchWithCut key key_except value tkey tkey_except tvalue)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | MGTable key key_except value ->
    begin match mk_wf_typ fuel' env true key with
    | RSuccess tkey ->
      begin match mk_wf_typ fuel' env false key_except with
      | RSuccess tkey_except ->
        begin match mk_wf_typ fuel' env true value with
        | RSuccess tvalue -> RSuccess (WfMZeroOrMore key key_except value tkey tkey_except tvalue)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | MGConcat g1 g2 ->
    begin match map_group_footprint (typ_disjoint fuel) fuel env g1 with
    | RSuccess (t1, t_ex1) ->
      begin match map_group_footprint (typ_disjoint fuel) fuel env g2 with
      | RSuccess (t2, t_ex2) ->
        begin match typ_diff_disjoint fuel env t1 t_ex1 t2 t_ex2 with
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

module CDDL.Spec.AST.Elab.Base
include CDDL.Spec.AST.Base
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

[@@PpxDerivingShow]
noeq
type result (t: Type) =
| RSuccess of t
| RFailure of string
| ROutOfFuel

(* Rewriting *)

[@@ sem_attr]
let rec map_group_is_productive
  (g: group)
: Tot (result unit)
= match g with
  | GOneOrMore g' -> map_group_is_productive g'
  | GAlwaysFalse
  | GElem _ _ _ -> RSuccess ()
  | GNop -> RFailure "map_group_is_productive: GNop"
  | GZeroOrOne _ -> RFailure "map_group_is_productive: GZeroOrOne"
  | GZeroOrMore _ -> RFailure "map_group_is_productive: GZeroOrMore"
  | GChoice g1 g2 ->
    begin match map_group_is_productive g1 with
    | RSuccess _ -> map_group_is_productive g2
    | res -> res
    end
  | GConcat g1 g2 ->
    begin match map_group_is_productive g1 with
    | RFailure _ -> map_group_is_productive g2
    | res -> res
    end
  | GDef _ -> RFailure "map_group_is_productive: GDef"

let rec map_group_is_productive_correct
  (env: sem_env)
  (g: group)
: Lemma
  (requires (
    group_bounded env.se_bound g /\
    RSuccess? (map_group_is_productive g)
  ))
  (ensures (
    Spec.map_group_is_productive (map_group_sem env g)
  ))
= match g with
  | GOneOrMore g' ->
    map_group_is_productive_correct env g'
  | GChoice g1 g2 ->
    map_group_is_productive_correct env g1;
    map_group_is_productive_correct env g2
  | GConcat g1 g2 ->
    if RSuccess? (map_group_is_productive g1)
    then map_group_is_productive_correct env g1
    else map_group_is_productive_correct env g2
  | _ -> ()

[@@ sem_attr]
let rec apply_map_group_det_empty_fail
  (g: elab_map_group)
: Tot (result bool)
= match g with
  | MGAlwaysFalse
  | MGMatch _ _ _
  | MGMatchWithCut _ _ -> RSuccess true
  | MGCut _
  | MGTable _ _ _
  | MGNop -> RSuccess false
  | MGChoice g1 g2 ->
    begin match apply_map_group_det_empty_fail g1 with
    | RSuccess true -> apply_map_group_det_empty_fail g2
    | res -> res
    end
  | MGConcat g1 g2 ->
    begin match apply_map_group_det_empty_fail g1 with
    | RSuccess false -> apply_map_group_det_empty_fail g2
    | res -> res
    end

let rec apply_map_group_det_empty_fail_correct
  (env: sem_env)
  (g: elab_map_group)
: Lemma
  (requires (
    bounded_elab_map_group env.se_bound g /\
    RSuccess? (apply_map_group_det_empty_fail g)
  ))
  (ensures (
    match apply_map_group_det_empty_fail g, Spec.apply_map_group_det (elab_map_group_sem env g) Cbor.cbor_map_empty with
    | RSuccess true, Spec.MapGroupFail
    | RSuccess false, Spec.MapGroupDet _ _ -> True
    | _ -> False
  ))
= match g with
  | MGChoice g1 g2 ->
    apply_map_group_det_empty_fail_correct env g1;
    begin match apply_map_group_det_empty_fail g1 with
    | RSuccess true -> apply_map_group_det_empty_fail_correct env g2
    | _ -> ()
    end
  | MGConcat g1 g2 ->
    apply_map_group_det_empty_fail_correct env g1;
    begin match apply_map_group_det_empty_fail g1 with
    | RSuccess false ->
      let Spec.MapGroupDet _ rem = Spec.apply_map_group_det (elab_map_group_sem env g1) Cbor.cbor_map_empty in
      assert (Cbor.cbor_map_equal rem Cbor.cbor_map_empty);
      apply_map_group_det_empty_fail_correct env g2
    | _ -> ()
    end
  | MGMatch cut k v ->
    Spec.apply_map_group_det_match_item_for cut (eval_literal k) (typ_sem env v) Cbor.cbor_map_empty
  | _ -> ()

let coerce_failure
  (#t1 #t2: Type)
  (r: result t1 { ~ (RSuccess? r) })
: Tot (result t2)
= match r with
  | RFailure msg -> RFailure msg
  | ROutOfFuel -> ROutOfFuel

[@@ sem_attr]
let rec rewrite_typ
  (fuel: nat)
  (t: typ)
: Tot (typ & bool)
= if fuel = 0
  then (t, false)
  else let fuel' : nat = fuel - 1 in
  match t with
  | TChoice (TChoice t1 t2) t3 -> rewrite_typ fuel' (TChoice t1 (TChoice t2 t3))
  | TChoice t (TElem EAlwaysFalse)
  | TChoice (TElem EAlwaysFalse) t
    -> rewrite_typ fuel' t
  | TChoice t1 t2 ->
    let (t1', res1) = rewrite_typ fuel' t1 in
    let (t2', res2) = rewrite_typ fuel' t2 in
    if res1 && res2
    then
      let t' = TChoice t1' t2' in
      if t' = t
      then (t', true)
      else rewrite_typ fuel' t'
    else (t, false)
  | TArray g ->
    let (g', res) = rewrite_group fuel' false g in
    (TArray g', res)
  | TMap g ->
    let (g', res) = rewrite_group fuel' true g in
    (TMap g', res)
  | TDetCbor base dest ->
    let (base', res1) = rewrite_typ fuel' base in
    let (dest', res2) = rewrite_typ fuel' dest in
    (TDetCbor base' dest', res1 && res2)
  | TSize base range ->
    let (base', res) = rewrite_typ fuel' base in
    // NOTE: I cannot rewrite `range` because it is matched syntactically
    (TSize base' range, res)
  | _ -> (t, true)

and rewrite_group
  (fuel: nat)
  (is_map_group: bool)
  (g: group)
: Tot (group & bool)
= if fuel = 0
  then (g, false)
  else let fuel' : nat = fuel - 1 in
  match g with
  | GConcat GAlwaysFalse _ -> (GAlwaysFalse, true)
  | GConcat GNop g -> rewrite_group fuel' is_map_group g
  | GConcat g GNop -> rewrite_group fuel' is_map_group g
  | GConcat t1 t2 ->
    if is_map_group && GConcat? t2
    then
      let GConcat t2 t3 = t2 in
      rewrite_group fuel' is_map_group (GConcat (GConcat t1 t2) t3)
    else if (not is_map_group) && GConcat? t1
    then
      let GConcat t0 t1 = t1 in
      rewrite_group fuel' is_map_group (GConcat t0 (GConcat t1 t2))
    else
    let (t1', res1) = rewrite_group fuel' is_map_group t1 in
    let (t2', res2) = rewrite_group fuel' is_map_group t2 in
    if res1 && res2
    then
      let g' = GConcat t1' t2' in
      if g' = g
      then (g', true)
      else rewrite_group fuel' is_map_group g'
    else (g, false)
  | GChoice GAlwaysFalse g -> rewrite_group fuel' is_map_group g
  | GChoice g GAlwaysFalse -> rewrite_group fuel' is_map_group g
  | GChoice (GChoice t1 t2) t3 -> rewrite_group fuel' is_map_group (GChoice t1 (GChoice t2 t3))
  | GChoice t1 t2 ->
    let (t1', res1) = rewrite_group fuel' is_map_group t1 in
    let (t2', res2) = rewrite_group fuel' is_map_group t2 in
    if res1 && res2
    then
      let g' = GChoice t1' t2' in
      if g' = g
      then (g', true)
      else rewrite_group fuel' is_map_group g'
    else (g, false)
  | GZeroOrMore g1 ->
    let result = match is_map_group, g1 with
    | true, GElem cut (TElem (ELiteral key)) value ->
      Some (rewrite_group fuel' is_map_group (GZeroOrOne (GElem cut (TElem (ELiteral key)) value)))
    | true, GChoice (GElem cut key value) g' ->
      if RSuccess? (map_group_is_productive g')
      then Some (rewrite_group fuel' is_map_group (GConcat (GZeroOrMore (GElem cut key value)) (GZeroOrMore g')))
      else None
    | _ -> None
    in
    begin match result with
    | Some g' -> g'
    | None -> 
      let (g1', res1) = rewrite_group fuel' is_map_group g1 in
      if res1
      then
        let g' = GZeroOrMore (g1') in
        if g' = g
        then (g', true)
        else rewrite_group fuel' is_map_group g'
      else (g, false)
    end
  | GZeroOrOne g ->
    let (g1, res1) = rewrite_group fuel' is_map_group g in
    (GZeroOrOne g1, res1)
  | GOneOrMore g ->
    let (g1, res1) = rewrite_group fuel' is_map_group g in
    (GOneOrMore g1, res1)
  | GElem cut key value ->
    let (key', res1) = rewrite_typ fuel' key in
    let (value', res2) = rewrite_typ fuel' value in
    (GElem cut (key') (value'), res1 && res2)
  | GDef n -> (GDef n, true)
  | GAlwaysFalse -> (GAlwaysFalse, true)
  | GNop -> (GNop, true)

#restart-solver
let rec rewrite_typ_bounded
  (env: name_env)
  (fuel: nat)
  (t: typ)
: Lemma
  (requires (
    typ_bounded env t
  ))
  (ensures (
    let t' = fst (rewrite_typ fuel t) in
    typ_bounded env t'
  ))
  (decreases fuel)
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | TChoice (TChoice t1 t2) t3 ->
    rewrite_typ_bounded env fuel' (TChoice t1 (TChoice t2 t3))
  | TChoice t (TElem EAlwaysFalse)
  | TChoice (TElem EAlwaysFalse) t
  | TSize t _
    -> rewrite_typ_bounded env fuel' t
  | TDetCbor t1 t2
  | TChoice t1 t2 ->
    rewrite_typ_bounded env fuel' t1;
    rewrite_typ_bounded env fuel' t2;
    rewrite_typ_bounded env fuel' (TChoice (fst (rewrite_typ fuel' t1)) (fst (rewrite_typ fuel' t2)))
  | TArray g ->
    rewrite_group_bounded env fuel' false g
  | TMap g ->
    rewrite_group_bounded env fuel' true g
  | _ -> ()

and rewrite_group_bounded
  (env: name_env)
  (fuel: nat)
  (is_map_group: bool)
  (t: group)
: Lemma
  (requires (
    group_bounded env t
  ))
  (ensures (
    let t' = fst (rewrite_group fuel is_map_group t) in
    group_bounded env t'
  ))
  (decreases fuel)
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | GConcat GAlwaysFalse _ -> ()
  | GConcat GNop g -> rewrite_group_bounded env fuel' is_map_group g
  | GConcat g GNop -> rewrite_group_bounded env fuel' is_map_group g
  | GConcat t1 t2 ->
    if is_map_group && GConcat? t2
    then begin
      let GConcat t2 t3 = t2 in
      rewrite_group_bounded env fuel' is_map_group (GConcat (GConcat t1 t2) t3)
    end else if (not is_map_group) && GConcat? t1
    then begin
      let GConcat t0 t1 = t1 in
      rewrite_group_bounded env fuel' is_map_group (GConcat t0 (GConcat t1 t2))
    end else
    let (t1', _) = rewrite_group fuel' is_map_group t1 in
    let (t2', _) = rewrite_group fuel' is_map_group t2 in
    rewrite_group_bounded env fuel' is_map_group t1;
    rewrite_group_bounded env fuel' is_map_group t2;
    rewrite_group_bounded env fuel' is_map_group (GConcat t1' t2')
  | GChoice GAlwaysFalse g -> rewrite_group_bounded env fuel' is_map_group g
  | GChoice g GAlwaysFalse -> rewrite_group_bounded env fuel' is_map_group g
  | GChoice (GChoice t1 t2) t3 ->
    rewrite_group_bounded env fuel' is_map_group (GChoice t1 (GChoice t2 t3))
  | GChoice t1 t2 ->
    let (t1', _) = rewrite_group fuel' is_map_group t1 in
    let (t2', _) = rewrite_group fuel' is_map_group t2 in
    rewrite_group_bounded env fuel' is_map_group t1;
    rewrite_group_bounded env fuel' is_map_group t2;
    rewrite_group_bounded env fuel' is_map_group (GChoice t1' t2')
  | GZeroOrMore g1 ->
    assert (group_bounded env g1);
    begin match is_map_group, g1 with
    | true, GElem cut (TElem (ELiteral key)) value ->
      rewrite_group_bounded env fuel' is_map_group (GZeroOrOne (GElem cut (TElem (ELiteral key)) value) <: group)
    | true, GChoice (GElem cut key value) g' ->
      if RSuccess? (map_group_is_productive g')
      then begin
        rewrite_group_bounded env fuel' is_map_group (GConcat (GZeroOrMore (GElem cut key value)) (GZeroOrMore g'))
      end
    | _ -> ()
    end;
    rewrite_group_bounded env fuel' is_map_group g1;
    let (g2, _) = rewrite_group fuel' is_map_group g1 in
    rewrite_group_bounded env fuel' is_map_group (GZeroOrMore g2)
  | GOneOrMore g1 ->
    rewrite_group_bounded env fuel' is_map_group g1;
    let (g2, _) = rewrite_group fuel' is_map_group g1 in
    rewrite_group_bounded env fuel' is_map_group (GOneOrMore g2)
  | GElem cut key value ->
    rewrite_typ_bounded env fuel' key;
    rewrite_typ_bounded env fuel' value
  | GZeroOrOne g1 ->
    rewrite_group_bounded env fuel' is_map_group g1
  | GAlwaysFalse
  | GNop
  | GDef _ -> ()

let rewrite_group_correct_postcond
  (env: sem_env)
  (fuel: nat)
  (is_map_group: bool)
  (t: group)
: Tot prop
=
  group_bounded env.se_bound t /\
  begin
    let t' = fst (rewrite_group fuel is_map_group t) in
    group_bounded env.se_bound t' /\
    begin if is_map_group
    then map_group_sem env t == map_group_sem env t'
    else Spec.array_group_equiv (array_group_sem env t) (array_group_sem env t')
    end
  end

#push-options "--z3rlimit 32"

#restart-solver
let rec rewrite_typ_correct
  (env: sem_env)
  (fuel: nat)
  (t: typ)
: Lemma
  (requires (
    typ_bounded env.se_bound t
  ))
  (ensures (
    let t' = fst (rewrite_typ fuel t) in
    typ_bounded env.se_bound t' /\
    Spec.typ_equiv (typ_sem env t) (typ_sem env t')
  ))
  (decreases fuel)
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | TChoice (TChoice t1 t2) t3 ->
    rewrite_typ_correct env fuel' (TChoice t1 (TChoice t2 t3))
  | TSize t _
  | TChoice t (TElem EAlwaysFalse)
  | TChoice (TElem EAlwaysFalse) t
    -> rewrite_typ_correct env fuel' t
  | TDetCbor t1 t2
  | TChoice t1 t2 ->
    rewrite_typ_correct env fuel' t1;
    rewrite_typ_correct env fuel' t2;
    rewrite_typ_correct env fuel' (TChoice (fst (rewrite_typ fuel' t1)) (fst (rewrite_typ fuel' t2)))
  | TArray g ->
    rewrite_group_correct env fuel' false g
  | TMap g ->
    rewrite_group_correct env fuel' true g
  | _ -> ()

and rewrite_group_correct
  (env: sem_env)
  (fuel: nat)
  (is_map_group: bool)
  (t: group)
: Lemma
  (requires (
    group_bounded env.se_bound t
  ))
  (ensures (
    let t' = fst (rewrite_group fuel is_map_group t) in
    group_bounded env.se_bound t' /\
    begin if is_map_group
    then map_group_sem env t == map_group_sem env t'
    else Spec.array_group_equiv (array_group_sem env t) (array_group_sem env t')
    end
  ))
  (decreases fuel)
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | GConcat GAlwaysFalse _ -> ()
  | GConcat GNop g -> rewrite_group_correct env fuel' is_map_group g
  | GConcat g GNop -> rewrite_group_correct env fuel' is_map_group g
  | GConcat t1 t2 ->
    if is_map_group && GConcat? t2
    then begin
      let GConcat t2 t3 = t2 in
      rewrite_group_correct env fuel' is_map_group (GConcat (GConcat t1 t2) t3)
    end else if (not is_map_group) && GConcat? t1
    then begin
      let GConcat t0 t1 = t1 in
      rewrite_group_correct env fuel' is_map_group (GConcat t0 (GConcat t1 t2))
    end else
    let (t1', _) = rewrite_group fuel' is_map_group t1 in
    let (t2', _) = rewrite_group fuel' is_map_group t2 in
    rewrite_group_correct env fuel' is_map_group t1;
    rewrite_group_correct env fuel' is_map_group t2;
    rewrite_group_correct env fuel' is_map_group (GConcat t1' t2');
    if is_map_group
    then ()
    else Spec.array_group_concat_equiv (array_group_sem env t1) (array_group_sem env t1') (array_group_sem env t2) (array_group_sem env t2')
  | GChoice GAlwaysFalse g -> rewrite_group_correct env fuel' is_map_group g
  | GChoice g GAlwaysFalse -> rewrite_group_correct env fuel' is_map_group g
  | GChoice (GChoice t1 t2) t3 ->
    rewrite_group_correct env fuel' is_map_group (GChoice t1 (GChoice t2 t3))
  | GChoice t1 t2 ->
    let (t1', _) = rewrite_group fuel' is_map_group t1 in
    let (t2', _) = rewrite_group fuel' is_map_group t2 in
    rewrite_group_correct env fuel' is_map_group t1;
    rewrite_group_correct env fuel' is_map_group t2;
    rewrite_group_correct env fuel' is_map_group (GChoice t1' t2')
  | GZeroOrMore g1 ->
    assert (group_bounded env.se_bound g1);
    begin match is_map_group, g1 with
    | true, GElem cut (TElem (ELiteral key)) value ->
      Spec.map_group_zero_or_more_map_group_match_item_for cut (eval_literal key) (typ_sem env value);
      rewrite_group_correct env fuel' is_map_group (GZeroOrOne (GElem cut (TElem (ELiteral key)) value) <: group);
      assert (rewrite_group_correct_postcond env fuel true t)
    | true, GChoice (GElem cut key value) g' ->
      if RSuccess? (map_group_is_productive g')
      then begin
        map_group_is_productive_correct env g';
        Spec.map_group_zero_or_more_choice (Spec.map_group_match_item cut (typ_sem env key) (typ_sem env value)) (map_group_sem env g');
        rewrite_group_correct env fuel' is_map_group (GConcat (GZeroOrMore (GElem cut key value)) (GZeroOrMore g'));
        assert (rewrite_group_correct_postcond env fuel true t)
      end
    | _ -> ()
    end;
    rewrite_group_correct env fuel' is_map_group g1;
    let (g2, _) = rewrite_group fuel' is_map_group g1 in
    rewrite_group_correct env fuel' is_map_group (GZeroOrMore g2);
    if not is_map_group
    then Spec.array_group_zero_or_more_equiv (array_group_sem env g1) (array_group_sem env g2);
    assert (rewrite_group_correct_postcond env fuel is_map_group t)
  | GOneOrMore g1 ->
    rewrite_group_correct env fuel' is_map_group g1;
    let (g2, _) = rewrite_group fuel' is_map_group g1 in
    rewrite_group_correct env fuel' is_map_group (GOneOrMore g2);
    if not is_map_group
    then Spec.array_group_zero_or_more_equiv (array_group_sem env g1) (array_group_sem env g2);
    assert (rewrite_group_correct_postcond env fuel is_map_group t)
  | GElem cut key value ->
    rewrite_typ_correct env fuel' key;
    rewrite_typ_correct env fuel' value;
    if is_map_group
    then Spec.map_group_match_item_ext cut (typ_sem env key) (typ_sem env value) (typ_sem env (fst (rewrite_typ fuel' key))) (typ_sem env (fst (rewrite_typ fuel' value)))
    else Spec.array_group_item_equiv (typ_sem env value) (typ_sem env (fst (rewrite_typ fuel' value)))
  | GZeroOrOne g1 ->
    rewrite_group_correct env fuel' is_map_group g1
  | GAlwaysFalse
  | GNop
  | GDef _ -> ()

#pop-options

(* Disjointness *)

let destruct_group
  (g: group)
: Tot (group & group)
= match g with
  | GConcat g1 g2 -> (g1, g2)
  | _ -> (g, GNop)

let maybe_close_array_group_concat
  (close: bool)
  (a1 a2: Spec.array_group None)
: Lemma
  (Spec.array_group_equiv
    (Spec.maybe_close_array_group (Spec.array_group_concat a1 a2) close)
    (Spec.array_group_concat a1 (Spec.maybe_close_array_group a2 close))
  )
= ()

let array_group_sem_destruct_group
  (e: sem_env)
  (g: group { group_bounded e.se_bound g })
: Lemma
  (let (g1, g2) = destruct_group g in
    group_bounded e.se_bound g1 /\
    group_bounded e.se_bound g2 /\
    array_group_sem e g `Spec.array_group_equiv` (array_group_sem e g1 `Spec.array_group_concat` array_group_sem e g2)
  )
= ()

let maybe_close_array_group_sem_destruct_group
  (close: bool)
  (e: sem_env)
  (g: group { group_bounded e.se_bound g })
: Lemma
  (let (g1, g2) = destruct_group g in
    group_bounded e.se_bound g1 /\
    group_bounded e.se_bound g2 /\
    Spec.maybe_close_array_group (array_group_sem e g) close `Spec.array_group_equiv`
      (array_group_sem e g1 `Spec.array_group_concat` Spec.maybe_close_array_group (array_group_sem e g2) close)
  )
  [SMTPat (Spec.maybe_close_array_group (array_group_sem e g) close)]
= ()

#restart-solver
let array_group_concat_elem_disjoint
  (close1 close2: bool)
  (t1 t2: Spec.typ)
  (a1 a2: Spec.array_group None)
: Lemma
  (ensures (Spec.array_group_disjoint (Spec.maybe_close_array_group a1 close1) (Spec.maybe_close_array_group a2 close2) ==>
    Spec.array_group_disjoint
      (Spec.maybe_close_array_group (Spec.array_group_concat (Spec.array_group_item t1) a1) close1)
      (Spec.maybe_close_array_group (Spec.array_group_concat (Spec.array_group_item t2) a2) close2)
  ))
= maybe_close_array_group_concat close1 (Spec.array_group_item t1) a1;
  maybe_close_array_group_concat close2 (Spec.array_group_item t1) a2

[@@CMacro]
let simple_value_false : Cbor.simple_value = 20uy
[@@CMacro]
let simple_value_true : Cbor.simple_value = 21uy

let array_group_disjoint_sym #b (a1 a2: Spec.array_group b) : Lemma
  (Spec.array_group_disjoint a1 a2 <==> Spec.array_group_disjoint a2 a1)
= ()

let typ_disjoint_t =
  (e: ast_env) ->
  (t1: typ { typ_bounded e.e_sem_env.se_bound t1 }) ->
  (t2: typ { typ_bounded e.e_sem_env.se_bound t2 }) ->
  Pure (result unit) // I cannot use `squash` because of unification, yet I want to shortcut disjointness symmetry
    (requires True)
    (ensures fun r -> RSuccess? r ==> Spec.typ_disjoint (typ_sem e.e_sem_env t1) (typ_sem e.e_sem_env t2))

let array_group_disjoint_t =
  (e: ast_env) ->
  (close1: bool) ->
  (close2: bool) ->
  (a1: group { group_bounded e.e_sem_env.se_bound a1 }) ->
  (a2: group { group_bounded e.e_sem_env.se_bound a2 }) ->
  Pure (result unit)
    (requires True)
    (ensures fun r ->
      RSuccess? r ==> Spec.array_group_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close1) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close2)
    )

let rec split_interval
  (e: sem_env)
  (is_int: bool)
  (lo hi: int)
  (t: typ)
: Pure (option int)
    (requires typ_bounded e.se_bound t)
    (ensures fun res ->
      match res with
      | None -> True
      | Some mi -> (lo <= mi /\ mi < hi)
    )
= match t with
  | TChoice t1 t2 ->
    begin match split_interval e is_int lo hi t1 with
    | None -> split_interval e is_int lo hi t2
    | r -> r
    end
  | _ ->
    let aux = match t with
    | TRange _ _ _ ->
      if is_int
      then begin match extract_range_value e t with
      | Some (tlo, thi) -> Some (eval_int_value tlo, eval_int_value thi)
      | _ -> None
      end
      else None
    | TSize _ t' ->
      if is_int
      then begin match extract_int_value e t' with
      | Some ti ->
        let i = eval_int_value ti in
        if i < 0 then None else Some (0, pow2 (let open FStar.Mul in 8 * i) - 1)
      | _ -> None
      end
      else begin match extract_range_value e t' with
      | Some (rlo, rhi) ->
        let lo = eval_int_value rlo in
        let hi = eval_int_value rhi in
        if lo > hi then None else Some (lo, hi)
      | _ -> None
      end
    | _ -> None
    in
    begin match aux with
    | None -> None
    | Some (lo', hi') ->
      if lo' <= lo && lo <= hi' && hi' < hi
      then Some hi'
      else if lo < lo' && lo' <= hi && hi <= hi'
      then Some (lo' - 1)
      else None
    end

let typ_included_t =
  (e: ast_env) ->
  (t1: typ { typ_bounded e.e_sem_env.se_bound t1 }) ->
  (t2: typ { typ_bounded e.e_sem_env.se_bound t2 }) ->
  Pure (result unit) // I cannot use `squash` because of unification
    (requires True)
    (ensures fun r -> RSuccess? r ==> Spec.typ_included (typ_sem e.e_sem_env t1) (typ_sem e.e_sem_env t2))

let array_group_included_t =
  (e: ast_env) ->
  (close: bool) ->
  (a1: group { group_bounded e.e_sem_env.se_bound a1 }) ->
  (a2: group { group_bounded e.e_sem_env.se_bound a2 }) ->
  Pure (result unit)
    (requires True)
    (ensures fun r ->
      match r with
      | RSuccess _ -> Spec.array_group_included (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close)
      | _ -> True
    )


let typ_sub_underapprox_postcond
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
      Spec.typ_included (typ_sem env.e_sem_env t') (typ_sem env.e_sem_env t1 `Util.andp` Util.notp (typ_sem env.e_sem_env t2))
    | RFailure _ -> False
    | _ -> True
    end

let mk_TChoice
  (t1 t2: typ)
: Tot typ
= match t1 with
  | TElem EAlwaysFalse -> t2
  | _ ->
    begin match t2 with
    | TElem EAlwaysFalse -> t1
    | _ -> TChoice t1 t2
    end

let mk_TChoice_bounded
  (env: name_env)
  (t1 t2: typ)
: Lemma
  (requires (
    typ_bounded env t1 /\
    typ_bounded env t2
  ))
  (ensures (
    typ_bounded env (mk_TChoice t1 t2)
  ))
= ()

#push-options "--z3rlimit 16"

#restart-solver
let mk_TChoice_sem
  (env: sem_env)
  (t1 t2: typ)
: Lemma
  (requires (
    typ_bounded env.se_bound t1 /\
    typ_bounded env.se_bound t2
  ))
  (ensures (
    typ_bounded env.se_bound (mk_TChoice t1 t2) /\
    typ_sem env (mk_TChoice t1 t2) `Spec.typ_equiv` Spec.t_choice (typ_sem env t1) (typ_sem env t2)
  ))
= ()

#pop-options

let rec typ_sub_underapprox
  (typ_disjoint: typ_disjoint_t)
  (fuel: nat)
  (env: ast_env)
  (t1 t2: typ)
: Pure (result typ)
  (requires (
    typ_bounded env.e_sem_env.se_bound t1 /\
    typ_bounded env.e_sem_env.se_bound t2
  ))
  (ensures fun t' ->
    typ_sub_underapprox_postcond env t1 t2 t'
  )
  (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t1 with
  | TChoice t1l t1r ->
    begin match typ_sub_underapprox typ_disjoint fuel' env t1l t2 with
    | RSuccess t1l' ->
      begin match typ_sub_underapprox typ_disjoint fuel' env t1r t2 with
      | RSuccess t1r' -> RSuccess (mk_TChoice t1l' t1r')
      | res -> res
      end
    | res -> res
    end
  | TDef i ->
    let t1' = env.e_env i in
    typ_sub_underapprox typ_disjoint fuel' env t1' t2
  | _ ->
    begin match typ_disjoint env t1 t2 with
    | RSuccess _ -> RSuccess t1
    | RFailure _ -> RSuccess (TElem EAlwaysFalse)
    | ROutOfFuel -> ROutOfFuel
    end

let typ_with_except_union_approx
  (t1 t1'
   t1_except'
   t2 t2'
   t2_except'
   d1 d2: Spec.typ)
: Lemma
  (requires (
    Spec.typ_included t1 (t1' `Util.andp` Util.notp t1_except') /\
    Spec.typ_included t2 (t2' `Util.andp` Util.notp t2_except') /\
    Spec.typ_included d1 (t1_except' `Util.andp` Util.notp t2') /\
    Spec.typ_included d2 (t2_except' `Util.andp` Util.notp t1')
  ))
  (ensures (
    Spec.typ_included (Spec.t_choice t1 t2) (Spec.t_choice t1' t2' `Util.andp` Util.notp (Spec.t_choice d1 d2))
  ))
= ()

let typ_included_andp_notp_equiv
  (s t1 t2 t1' t2': Spec.typ)
: Lemma
  (requires (
    Spec.typ_included s (t1 `Util.andp` Util.notp t2) /\
    t1 `Spec.typ_equiv` t1' /\
    t2 `Spec.typ_equiv` t2'
  ))
  (ensures (
    Spec.typ_included s (t1' `Util.andp` Util.notp t2')
  ))
= ()

let typ_included_union
  (a1 a2 b1 b2: Spec.typ)
: Lemma
  (requires (
    Spec.typ_included a1 b1 /\
    Spec.typ_included a2 b2
  ))
  (ensures (
    Spec.typ_included (Spec.t_choice a1 a2) (Spec.t_choice b1 b2)
  ))
= ()

let rec array_group_is_nonempty
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (g: group)
: Pure (result unit)
    (requires (group_bounded env.e_sem_env.se_bound g))
    (ensures fun r -> match r with
    | RSuccess _ -> Spec.array_group_is_nonempty (array_group_sem env.e_sem_env g)
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match g with
  | GDef n -> array_group_is_nonempty fuel' env (env.e_env n)
  | GOneOrMore g' -> array_group_is_nonempty fuel' env g'
  | GZeroOrOne _ -> RFailure "array_group_is_nonempty: GZeroOrOne"
  | GZeroOrMore _ -> RFailure "array_group_is_nonempty: GZeroOrMore"
  | GNop -> RFailure "array_group_is_nonempty: GNop"
  | GConcat g1 g2 ->
    begin match array_group_is_nonempty fuel' env g1 with
    | RFailure _ -> array_group_is_nonempty fuel' env g2
    | res -> res
    end
  | GChoice g1 g2 ->
    begin match array_group_is_nonempty fuel' env g1 with
    | RSuccess _ -> array_group_is_nonempty fuel' env g2
    | res -> res
    end
  | GElem _ _ _
  | GAlwaysFalse -> RSuccess ()

#push-options "--z3rlimit 64 --split_queries always --query_stats --fuel 4 --ifuel 8"

#restart-solver
let rec array_group_concat_unique_strong
  (array_group_disjoint: array_group_disjoint_t)
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (#g1: group)
  (s1: ast0_wf_array_group g1)
  (g2: group)
: Pure (result unit)
    (requires (
      spec_wf_array_group env.e_sem_env _ s1 /\
      group_bounded env.e_sem_env.se_bound g2
    ))
    (ensures fun r -> match r with
    | RSuccess _ -> Spec.array_group_concat_unique_strong (array_group_sem env.e_sem_env g1) (array_group_sem env.e_sem_env g2)
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  let array_group_concat_unique_strong = array_group_concat_unique_strong array_group_disjoint fuel' in
  match s1 with
  | WfAChoice g1l g1r s1l s1r ->
    let res1 = array_group_concat_unique_strong env s1l g2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_strong env s1r g2 in
    if not (RSuccess? res2)
    then res2
    else let res3 = array_group_disjoint env false false g1l g1r in
    if not (RSuccess? res3)
    then res3
    else begin
      Spec.array_group_concat_unique_strong_choice_left
        (array_group_sem env.e_sem_env g1l)
        (array_group_sem env.e_sem_env g1r)
        (array_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | WfAConcat g1l g1r s1l s1r ->
    let res1 = array_group_concat_unique_strong env s1r g2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_strong env s1l (GConcat g1r g2) in
    if not (RSuccess? res2)
    then res2
    else begin
      Spec.array_group_concat_unique_strong_concat_left (array_group_sem env.e_sem_env g1l) (array_group_sem env.e_sem_env g1r) (array_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | WfAElem _ _ _ _ -> RSuccess ()
  | WfARewrite _ _ s1 ->
    array_group_concat_unique_strong env s1 g2
(*  
  | WfADef n ->
    begin match (env.e_wf n).wf_array with
      | None -> RFailure "array_group_concat_unique_strong: unfold left, not proven yet"
      | Some (| _, s |) -> array_group_concat_unique_strong env #(env.e_env n) s g2
    end
*)
  | _ ->
    begin match destruct_group g2 with
    | (GDef i, g2r) ->
      let g2' = GConcat (env.e_env i) g2r in
      Spec.array_group_concat_equiv
        (fst (Ghost.reveal (env.e_sem_env.se_env i) <: (Spec.array_group None & Spec.map_group)))
        (array_group_sem env.e_sem_env (env.e_env i))
        (array_group_sem env.e_sem_env g2r)
        (array_group_sem env.e_sem_env g2r);
      rewrite_group_correct env.e_sem_env fuel false g2';
      let (g22, res_) = rewrite_group fuel false g2' in
      Spec.array_group_concat_unique_strong_equiv
        (array_group_sem env.e_sem_env g1)
        (array_group_sem env.e_sem_env g1)
        (array_group_sem env.e_sem_env g2)
        (array_group_sem env.e_sem_env g22);
      if res_ then
      array_group_concat_unique_strong env s1 g22
      else ROutOfFuel
    | _ ->
      begin match s1 with
      | WfAZeroOrOneOrMore g' s' g1' ->
        let res1 = array_group_disjoint env false false g' g2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_strong env s' g' in
        if not (RSuccess? res2)
        then res2
        else let res3 = array_group_concat_unique_strong env s' g2 in
        if not (RSuccess? res3)
        then res3
        else begin
          match g1' with
          | GZeroOrMore _ ->
            Spec.array_group_concat_unique_strong_zero_or_more_left
              (array_group_sem env.e_sem_env g')
              (array_group_sem env.e_sem_env g2);
            RSuccess ()
          | GOneOrMore _ ->
            Spec.array_group_concat_unique_strong_one_or_more_left
              (array_group_sem env.e_sem_env g')
              (array_group_sem env.e_sem_env g2);
            RSuccess ()          
        end
      | WfAZeroOrOne g' s' ->
        let res1 = array_group_disjoint env false false g' g2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_strong env s' g2 in
        if not (RSuccess? res2)
        then res2
        else begin
          Spec.array_group_concat_unique_strong_zero_or_one_left
            (array_group_sem env.e_sem_env g')
            (array_group_sem env.e_sem_env g2);
          assert (Spec.array_group_concat_unique_strong
            (Spec.array_group_zero_or_one (array_group_sem env.e_sem_env g'))
            (array_group_sem env.e_sem_env g2)
          );
          assert (Spec.array_group_concat_unique_strong
            (array_group_sem env.e_sem_env g1)
            (array_group_sem env.e_sem_env g2)
          );
          RSuccess ()
        end
      end
    end

#restart-solver
let rec array_group_concat_unique_weak
  (array_group_disjoint: array_group_disjoint_t)
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (#g1: group)
  (s1: ast0_wf_array_group g1)
  (#g2: group)
  (s2: ast0_wf_array_group g2)
: Pure (result unit)
    (requires (
      spec_wf_array_group env.e_sem_env _ s1 /\
      spec_wf_array_group env.e_sem_env _ s2
    ))
    (ensures fun r -> match r with
    | RSuccess _ -> Spec.array_group_concat_unique_weak (array_group_sem env.e_sem_env g1) (array_group_sem env.e_sem_env g2)
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  let array_group_concat_unique_weak = array_group_concat_unique_weak array_group_disjoint fuel' in
  match s1 with
  | WfAChoice g1l g1r s1l s1r ->
    let res1 = array_group_concat_unique_weak env s1l s2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_weak env s1r s2 in
    if not (RSuccess? res2)
    then res2
    else let res3 = array_group_disjoint env false true g1l (GConcat g1r g2) in
    if not (RSuccess? res3)
    then res3
    else begin
      Spec.array_group_concat_unique_weak_choice_left
        (array_group_sem env.e_sem_env g1l)
        (array_group_sem env.e_sem_env g1r)
        (array_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | _ ->
    begin match s2 with
    | WfAChoice g2l g2r s2l s2r ->
      let res1 = array_group_concat_unique_weak env s1 s2l in
      if not (RSuccess? res1)
      then res1
      else let res2 = array_group_concat_unique_weak env s1 s2r in
      if not (RSuccess? res2)
      then res2
      else begin
        Spec.array_group_concat_unique_weak_choice_right
          (array_group_sem env.e_sem_env g1)
          (array_group_sem env.e_sem_env g2l)
          (array_group_sem env.e_sem_env g2r);
        RSuccess ()
      end
    | _ ->
      begin match s1 with
      | WfAElem _ _ _ _ -> RSuccess ()
      | WfAConcat g1l g1r s1l s1r ->
        let res1 = array_group_concat_unique_weak env s1r s2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_weak env s1l (WfAConcat g1r g2 s1r s2) in
        if not (RSuccess? res2)
        then res2
        else begin
          Spec.array_group_concat_unique_weak_concat_left
            (array_group_sem env.e_sem_env g1l)
            (array_group_sem env.e_sem_env g1r)
            (array_group_sem env.e_sem_env g2);
          RSuccess ()
        end
      | WfARewrite _ _ s1' ->
        array_group_concat_unique_weak env s1' s2
(*        
      | WfADef n ->
        begin match (env.e_wf n).wf_array with
        | None -> RFailure "array_group_concat_unique_weak: unfold left, not proven yet"
        | Some (| _, s1' |) ->
          array_group_concat_unique_weak env #(env.e_env n) s1' s2
        end
*)
      | WfAZeroOrOneOrMore g s g' ->
        let res1 = array_group_disjoint env false true g g2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_strong array_group_disjoint fuel env s g in
        if not (RSuccess? res2)
        then res2
        else let res3 = array_group_concat_unique_weak env s s2 in
        if not (RSuccess? res3)
        then res3
        else begin
          match g' with
          | GZeroOrMore _ ->
            Spec.array_group_concat_unique_weak_zero_or_more_left
              (array_group_sem env.e_sem_env g)
              (array_group_sem env.e_sem_env g2);
            RSuccess ()
          | GOneOrMore _ ->
            Spec.array_group_concat_unique_weak_one_or_more_left
              (array_group_sem env.e_sem_env g)
              (array_group_sem env.e_sem_env g2);
            RSuccess ()
        end
      | WfAZeroOrOne g s ->
        let res1 = array_group_disjoint env false true g g2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_weak env s s2 in
        if not (RSuccess? res2)
        then res2
        else begin
          Spec.array_group_concat_unique_weak_zero_or_one_left
            (array_group_sem env.e_sem_env g)
            (array_group_sem env.e_sem_env g2);
          RSuccess ()
        end
      end
    end

#pop-options

let map_group_footprint'_postcond
  (env: sem_env)
  (g: elab_map_group)
  (res: result (typ & typ))
: GTot prop
=
      begin match res with
      | RSuccess te ->
        let t = fst te in
        let t_except = snd te in
        bounded_elab_map_group env.se_bound g /\
        typ_bounded env.se_bound t /\
        typ_bounded env.se_bound t_except /\
        begin let t' = spec_map_group_footprint env g in
        Spec.typ_included t' (typ_sem env t `Util.andp` Util.notp (typ_sem env t_except))
        end
      | RFailure _ -> False
      | _ -> True
      end

let map_group_footprint'_postcond_intro_success
  (env: sem_env)
  (g: elab_map_group)
  (t: typ)
  (t_except: typ)
  (t': Ghost.erased Spec.typ)
: Lemma
  (requires (
      bounded_elab_map_group env.se_bound g /\
      typ_bounded env.se_bound t /\
      typ_bounded env.se_bound t_except /\
      spec_map_group_footprint env g == t' /\
      Spec.typ_included t' (typ_sem env t `Util.andp` Util.notp (typ_sem env t_except))
  ))
  (ensures (
    map_group_footprint'_postcond env g (RSuccess (t, t_except))
  ))
= ()

let map_group_footprint'_postcond_intro_out_of_fuel
  (env: sem_env)
  (g: elab_map_group)
  (res: result (typ & typ))
  (sq: squash (~ (RSuccess? res)))
  (sq_not_fail: squash (~ (RFailure? res)))
: Lemma
    (requires True)
  (ensures (
    map_group_footprint'_postcond env g res
  ))
= ()

#restart-solver
let spec_map_group_footprint_choice_or_concat
  (env: sem_env)
  (g1 g2 g: elab_map_group)
  (sq1: squash (bounded_elab_map_group env.se_bound g1))
  (sq2: squash (bounded_elab_map_group env.se_bound g2))
  (sq': squash (g == MGChoice g1 g2 \/ g == MGConcat g1 g2))
: Lemma
  (ensures (
    bounded_elab_map_group env.se_bound g1 /\
    bounded_elab_map_group env.se_bound g2 /\
    bounded_elab_map_group env.se_bound g /\
    spec_map_group_footprint env g == (Ghost.hide ((spec_map_group_footprint env g1) `Spec.t_choice` (spec_map_group_footprint env g2)))
  ))
= assert (
    bounded_elab_map_group env.se_bound g1 /\
    bounded_elab_map_group env.se_bound g2 /\
    bounded_elab_map_group env.se_bound (MGChoice g1 g2) /\
    spec_map_group_footprint env (MGChoice g1 g2) == (Ghost.hide ((spec_map_group_footprint env g1) `Spec.t_choice` (spec_map_group_footprint env g2)))
  );
 assert (
    bounded_elab_map_group env.se_bound g1 /\
    bounded_elab_map_group env.se_bound g2 /\
    bounded_elab_map_group env.se_bound (MGChoice g1 g2) /\
    spec_map_group_footprint env (MGConcat g1 g2) == (Ghost.hide ((spec_map_group_footprint env g1) `Spec.t_choice` (spec_map_group_footprint env g2)))
  )

#push-options "--z3rlimit 64 --ifuel 8 --fuel 2 --split_queries always --query_stats"

#restart-solver
let rec map_group_footprint'
  (typ_disjoint: typ_disjoint_t)
  (fuel: nat)
  (env: ast_env)
  (g: elab_map_group)
  (sq: squash (bounded_elab_map_group env.e_sem_env.se_bound g))
: Tot (res: result (typ & typ) & squash (map_group_footprint'_postcond env.e_sem_env g res))
  (decreases g)
= match g with
  | MGNop
  | MGAlwaysFalse ->
    let res = RSuccess (TElem EAlwaysFalse, TElem EAlwaysFalse) in
    assert (map_group_footprint'_postcond env.e_sem_env g res); (| res, () |)
  | MGMatch _ key _
    ->
    let res = RSuccess (TElem (ELiteral key), TElem EAlwaysFalse) in
    assert (map_group_footprint'_postcond env.e_sem_env g res); (| res, () |)
  | MGMatchWithCut key _
  | MGCut key
    ->
    let res = RSuccess (key, TElem EAlwaysFalse) in
    assert (map_group_footprint'_postcond env.e_sem_env g res); (| res, () |)
  | MGTable key key_except _ ->
    let res = RSuccess (key, key_except) in
    assert (map_group_footprint'_postcond env.e_sem_env g res); (| res, () |)
  | MGChoice g1 g2
  | MGConcat g1 g2 ->
    let sq1: squash (bounded_elab_map_group env.e_sem_env.se_bound g1) = () in
    let sq2: squash (bounded_elab_map_group env.e_sem_env.se_bound g2) = () in
    let (| te1, _ |) = map_group_footprint' typ_disjoint fuel env g1 sq1 in
    assert (map_group_footprint'_postcond env.e_sem_env g1 te1);
    begin match te1 with
    | RSuccess te1 ->
      let t1 = fst te1 in
      let t1_except = snd te1 in
      let (| te2, _ |) = map_group_footprint' typ_disjoint fuel env g2 sq2 in
      assert (map_group_footprint'_postcond env.e_sem_env g2 te2);
      begin match te2 with
      | RSuccess te2 ->
        let t2 = fst te2 in
        let t2_except = snd te2 in
        spec_map_group_footprint_choice_or_concat env.e_sem_env g1 g2 g sq1 sq2 ();
        let s1 = (spec_map_group_footprint env.e_sem_env g1) in
        let s2 = (spec_map_group_footprint env.e_sem_env g2) in
        let u1 = typ_sub_underapprox typ_disjoint fuel env t1_except t2 in
        begin match u1 with
        | RSuccess d1 ->
          let u2 = typ_sub_underapprox typ_disjoint fuel env t2_except t1 in
          begin match u2 with
          | RSuccess d2 ->
            typ_with_except_union_approx
              s1
              (typ_sem env.e_sem_env t1)
              (typ_sem env.e_sem_env t1_except)
              s2
              (typ_sem env.e_sem_env t2)
              (typ_sem env.e_sem_env t2_except)
              (typ_sem env.e_sem_env d1)
              (typ_sem env.e_sem_env d2);
            let t' = mk_TChoice t1 t2 in
            mk_TChoice_sem env.e_sem_env t1 t2;
            let d' = mk_TChoice d1 d2 in
            mk_TChoice_sem env.e_sem_env d1 d2;
            typ_included_andp_notp_equiv
              (Spec.t_choice s1 s2)
              (Spec.t_choice (typ_sem env.e_sem_env t1) (typ_sem env.e_sem_env t2))
              (Spec.t_choice (typ_sem env.e_sem_env d1) (typ_sem env.e_sem_env d2))
              (typ_sem env.e_sem_env t')
              (typ_sem env.e_sem_env d');
            assert (Spec.typ_included
              (Spec.t_choice s1 s2)
              (typ_sem env.e_sem_env t' `Util.andp` Util.notp (typ_sem env.e_sem_env d'))
            );
            assert (Spec.typ_included
              ((spec_map_group_footprint env.e_sem_env g))
              (typ_sem env.e_sem_env t' `Util.andp` Util.notp (typ_sem env.e_sem_env d'))
            );
            map_group_footprint'_postcond_intro_success env.e_sem_env g t' d' (Spec.t_choice s1 s2);
            (| RSuccess (t', d'),  () |)
          | res -> (| ROutOfFuel, map_group_footprint'_postcond_intro_out_of_fuel env.e_sem_env g (ROutOfFuel) () () |)
          end
        | res -> (| ROutOfFuel, map_group_footprint'_postcond_intro_out_of_fuel env.e_sem_env g (ROutOfFuel) () () |)
        end
      | res -> (| ROutOfFuel, map_group_footprint'_postcond_intro_out_of_fuel env.e_sem_env g (ROutOfFuel) () () |)
      end
    | res -> (| ROutOfFuel, map_group_footprint'_postcond_intro_out_of_fuel env.e_sem_env g (ROutOfFuel) () () |)
    end

#pop-options

let map_group_footprint_postcond
  (env: sem_env)
  (g: elab_map_group)
  (res: result (typ & typ))
: GTot prop
=
      begin match res with
      | RSuccess te ->
        let t = fst te in
        let t_except = snd te in
        bounded_elab_map_group env.se_bound g /\
        typ_bounded env.se_bound t /\
        typ_bounded env.se_bound t_except /\
        begin let t' = spec_map_group_footprint env g in
          Spec.typ_included t' (typ_sem env t `Util.andp` Util.notp (typ_sem env t_except)) /\
          Spec.map_group_footprint (elab_map_group_sem env g) t' /\
          Spec.map_group_footprint (elab_map_group_sem env g) (typ_sem env t `Util.andp` Util.notp (typ_sem env t_except))
        end
      | RFailure _ -> False
      | _ -> True
      end

let map_group_footprint
  (typ_disjoint: typ_disjoint_t)
  (fuel: nat)
  (env: ast_env)
  (g: elab_map_group)
: Pure (result (typ & typ))
    (requires (bounded_elab_map_group env.e_sem_env.se_bound g))
    (ensures fun res -> map_group_footprint_postcond env.e_sem_env g res)
= let (| res, prf |) = map_group_footprint' typ_disjoint fuel env g () in
  res

let typ_diff_disjoint_t =
  (env: ast_env) ->
  (t1: typ) ->
  (d1: typ) ->
  (t2: typ) ->
  (d2: typ) ->
  Pure (result unit)
    (requires (
      typ_bounded env.e_sem_env.se_bound t1 /\
      typ_bounded env.e_sem_env.se_bound t2 /\
      typ_bounded env.e_sem_env.se_bound d1 /\
      typ_bounded env.e_sem_env.se_bound d2
    ))
    (ensures (fun res ->
      match res with
      | RSuccess _ ->
        typ_bounded env.e_sem_env.se_bound t1 /\
        typ_bounded env.e_sem_env.se_bound t2 /\
        typ_bounded env.e_sem_env.se_bound d1 /\
        typ_bounded env.e_sem_env.se_bound d2 /\
        Spec.typ_disjoint (typ_sem env.e_sem_env t1 `Util.andp` Util.notp (typ_sem env.e_sem_env d1)) (typ_sem env.e_sem_env t2 `Util.andp` Util.notp (typ_sem env.e_sem_env d2))
      | _ -> True
    ))

let typ_disjoint_from_diff
  (typ_diff_disjoint: typ_diff_disjoint_t)
  (env: ast_env)
  (t1 t2 t3: typ)
: Pure (result unit)
    (requires (
      typ_bounded env.e_sem_env.se_bound t1 /\
      typ_bounded env.e_sem_env.se_bound t2 /\
      typ_bounded env.e_sem_env.se_bound t3
    ))
    (ensures (fun res ->
      match res with
      | RSuccess _ ->
        typ_bounded env.e_sem_env.se_bound t1 /\
        typ_bounded env.e_sem_env.se_bound t2 /\
        typ_bounded env.e_sem_env.se_bound t3 /\
        Spec.typ_disjoint (typ_sem env.e_sem_env t1) (typ_sem env.e_sem_env t2 `Util.andp` Util.notp (typ_sem env.e_sem_env t3))
      | _ -> True
    ))
= typ_diff_disjoint env t1 (TElem EAlwaysFalse) t2 t3

let map_group_choice_compatible_no_cut_t =
  (env: ast_env) ->
  (#g1: elab_map_group) ->
  (s1: ast0_wf_parse_map_group g1) ->
  (#g2: elab_map_group) ->
  (s2: ast0_wf_parse_map_group g2) ->
  Pure (result unit)
    (requires (
      spec_wf_parse_map_group env.e_sem_env _ s1 /\
      spec_wf_parse_map_group env.e_sem_env _ s2
    ))
    (ensures fun r -> match r with
    | RSuccess _ -> Spec.map_group_choice_compatible_no_cut (elab_map_group_sem env.e_sem_env g1) (elab_map_group_sem env.e_sem_env g2)
    | _ -> True
    )

let map_group_choice_compatible'_postcond
  (env: sem_env)
  (#g1: elab_map_group)
  (s1: ast0_wf_parse_map_group g1)
  (#g2: elab_map_group)
  (s2: ast0_wf_parse_map_group g2)
  (r: result unit)
: GTot prop
= 
      spec_wf_parse_map_group env _ s1 /\
      spec_wf_parse_map_group env _ s2 /\
      begin match r with
      | RSuccess _ -> Spec.map_group_choice_compatible (elab_map_group_sem env g1) (elab_map_group_sem env g2)
      | _ -> True
      end

let map_group_choice_compatible_t =
  (env: ast_env) ->
  (#g1: elab_map_group) ->
  (s1: ast0_wf_parse_map_group g1) ->
  (#g2: elab_map_group) ->
  (s2: ast0_wf_parse_map_group g2) ->
  Pure (result unit)
    (requires (
      spec_wf_parse_map_group env.e_sem_env _ s1 /\
      spec_wf_parse_map_group env.e_sem_env _ s2
    ))
    (ensures fun r -> (map_group_choice_compatible'_postcond env.e_sem_env s1 s2 r))

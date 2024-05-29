module CDDL.Interpreter.Elab
include CDDL.Interpreter.AST
module Spec = CDDL.Spec
module U64 = FStar.UInt64
module MapSpec = CDDL.Spec.MapGroupGen

noeq
type result (t: Type) =
| RSuccess of t
| RFailure of string
| ROutOfFuel

(* Rewriting *)

[@@ sem_attr]
let rec map_group_is_productive
  (g: group NMapGroup)
: Tot (result unit)
= match g with
  | GOneOrMore g' -> map_group_is_productive g'
  | GAlwaysFalse
  | GMapElem _ _ _ _ -> RSuccess ()
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

let rec map_group_is_productive_correct
  (env: sem_env)
  (g: group NMapGroup)
: Lemma
  (requires (
    group_bounded NMapGroup env.se_bound g /\
    RSuccess? (map_group_is_productive g)
  ))
  (ensures (
    MapSpec.map_group_is_productive (map_group_sem env g)
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
let rec rewrite_typ
  (fuel: nat)
  (t: typ)
: Tot typ
= if fuel = 0
  then t
  else let fuel' : nat = fuel - 1 in
  match t with
  | TChoice (TChoice t1 t2) t3 -> rewrite_typ fuel' (TChoice t1 (TChoice t2 t3))
  | TChoice t (TElem EAlwaysFalse)
  | TChoice (TElem EAlwaysFalse) t
    -> rewrite_typ fuel' t
  | TChoice t1 t2 ->
    let t' = TChoice (rewrite_typ fuel' t1) (rewrite_typ fuel' t2) in
    if t' = t
    then t'
    else rewrite_typ fuel' t'
  | TArray g -> TArray (rewrite_group fuel' NArrayGroup g)
  | TMap g -> TMap (rewrite_group fuel' NMapGroup g)
  | _ -> t

and rewrite_group
  (fuel: nat)
  (kind: name_env_elem)
  (g: group kind)
: Tot (group kind)
= if fuel = 0
  then g
  else let fuel' : nat = fuel - 1 in
  match g with
  | GConcat GAlwaysFalse _ -> GAlwaysFalse
  | GConcat GNop g -> rewrite_group fuel' kind g
  | GConcat g GNop -> rewrite_group fuel' kind g
  | GConcat (GConcat t1 t2) t3 -> rewrite_group fuel' kind (GConcat t1 (GConcat t2 t3))
  | GConcat t1 t2 ->
    let g' = GConcat (rewrite_group fuel' kind t1) (rewrite_group fuel' kind t2) in
    if g' = g
    then g'
    else rewrite_group fuel' kind g'
  | GChoice GAlwaysFalse g -> rewrite_group fuel' kind g
  | GChoice g GAlwaysFalse -> rewrite_group fuel' kind g
  | GChoice (GChoice t1 t2) t3 -> rewrite_group fuel' kind (GChoice t1 (GChoice t2 t3))
  | GChoice t1 t2 ->
    let g' = GChoice (rewrite_group fuel' kind t1) (rewrite_group fuel' kind t2) in
    if g' = g
    then g'
    else rewrite_group fuel' kind g'
  | GZeroOrMore (GMapElem sq cut (TElem (ELiteral key)) value) ->
    rewrite_group fuel' kind (GZeroOrOne (GMapElem sq cut (TElem (ELiteral key)) value))
  | GZeroOrMore (GChoice (GMapElem sq cut key value) g') ->
    if RSuccess? (map_group_is_productive g')
    then rewrite_group fuel' kind (GConcat (GZeroOrMore (GMapElem sq cut key value)) (GZeroOrMore g'))
    else g
  | GZeroOrMore g1 -> 
    let g' = GZeroOrMore (rewrite_group fuel' kind g1) in
    if g' = g
    then g'
    else rewrite_group fuel' kind g'
  | GZeroOrOne g -> GZeroOrOne (rewrite_group fuel' kind g)
  | GOneOrMore g -> GOneOrMore (rewrite_group fuel' kind g)
  | GArrayElem sq ty -> GArrayElem sq (rewrite_typ fuel' ty)
  | GMapElem sq cut key value -> GMapElem sq cut (rewrite_typ fuel' key) (rewrite_typ fuel' value)
  | GDef sq n -> GDef sq n
  | GAlwaysFalse -> GAlwaysFalse
  | GNop -> GNop

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
    let t' = rewrite_typ fuel t in
    typ_bounded env.se_bound t' /\
    Spec.typ_equiv (typ_sem env t) (typ_sem env t')
  ))
  (decreases fuel)
  [SMTPat (typ_sem env (rewrite_typ fuel t))]
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | TChoice (TChoice t1 t2) t3 ->
    rewrite_typ_correct env fuel' (TChoice t1 (TChoice t2 t3))
  | TChoice t (TElem EAlwaysFalse)
  | TChoice (TElem EAlwaysFalse) t
    -> rewrite_typ_correct env fuel' t
  | TChoice t1 t2 ->
    rewrite_typ_correct env fuel' t1;
    rewrite_typ_correct env fuel' t2;
    rewrite_typ_correct env fuel' (TChoice (rewrite_typ fuel' t1) (rewrite_typ fuel' t2))
  | TArray g ->
    rewrite_group_correct env fuel' g
  | TMap g ->
    rewrite_group_correct env fuel' g
  | _ -> ()

and rewrite_group_correct
  (env: sem_env)
  (fuel: nat)
  (#kind: name_env_elem)
  (t: group kind)
: Lemma
  (requires (
    group_bounded kind env.se_bound t
  ))
  (ensures (
    let t' = rewrite_group fuel kind t in
    group_bounded kind env.se_bound t' /\
    begin match kind with
    | NArrayGroup -> Spec.array_group3_equiv (array_group_sem env t) (array_group_sem env t')
    | NMapGroup -> map_group_sem env t == map_group_sem env t'
    | _ -> True
    end
  ))
  (decreases fuel)
  [SMTPatOr [
    [SMTPat (map_group_sem env (rewrite_group fuel kind t))];
    [SMTPat (array_group_sem env (rewrite_group fuel kind t))];
  ]]
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | GConcat GAlwaysFalse _ -> ()
  | GConcat GNop g -> rewrite_group_correct env fuel' g
  | GConcat g GNop -> rewrite_group_correct env fuel' g
  | GConcat (GConcat t1 t2) t3 ->
    rewrite_group_correct env fuel' (GConcat t1 (GConcat t2 t3))
  | GConcat t1 t2 ->
    let t1' = rewrite_group fuel' kind t1 in
    let t2' = rewrite_group fuel' kind t2 in
    rewrite_group_correct env fuel' t1;
    rewrite_group_correct env fuel' t2;
    rewrite_group_correct env fuel' (GConcat t1' t2');
    begin match kind with
    | NArrayGroup -> Spec.array_group3_concat_equiv (array_group_sem env t1) (array_group_sem env t1') (array_group_sem env t2) (array_group_sem env t2')
    | _ -> ()
    end
  | GChoice GAlwaysFalse g -> rewrite_group_correct env fuel' g
  | GChoice g GAlwaysFalse -> rewrite_group_correct env fuel' g
  | GChoice (GChoice t1 t2) t3 ->
    rewrite_group_correct env fuel' (GChoice t1 (GChoice t2 t3))
  | GChoice t1 t2 ->
    let t1' = rewrite_group fuel' kind t1 in
    let t2' = rewrite_group fuel' kind t2 in
    rewrite_group_correct env fuel' t1;
    rewrite_group_correct env fuel' t2;
    rewrite_group_correct env fuel' (GChoice t1' t2')
  | GZeroOrMore (GMapElem sq cut (TElem (ELiteral key)) value) ->
    MapSpec.map_group_zero_or_more_map_group_match_item_for cut (eval_literal key) (typ_sem env value);
    rewrite_group_correct env fuel' (GZeroOrOne (GMapElem sq cut (TElem (ELiteral key)) value))
  | GZeroOrMore (GChoice (GMapElem sq cut key value) g') ->
    if RSuccess? (map_group_is_productive g')
    then begin
      map_group_is_productive_correct env g';
      MapSpec.map_group_zero_or_more_choice (MapSpec.map_group_match_item cut (typ_sem env key) (typ_sem env value)) (map_group_sem env g');
      rewrite_group_correct env fuel' (GConcat (GZeroOrMore (GMapElem sq cut key value)) (GZeroOrMore g'))
    end
  | GZeroOrOne g1 ->
    rewrite_group_correct env fuel' g1
  | GZeroOrMore g1 ->
    rewrite_group_correct env fuel' g1;
    let g2 = rewrite_group fuel' kind g1 in
    rewrite_group_correct env fuel' (GZeroOrMore g2);
    begin match kind with
    | NArrayGroup -> Spec.array_group3_zero_or_more_equiv (array_group_sem env g1) (array_group_sem env g2)
    | _ -> ()
    end
  | GOneOrMore g1 ->
    rewrite_group_correct env fuel' g1;
    let g2 = rewrite_group fuel' kind g1 in
    rewrite_group_correct env fuel' (GOneOrMore g2);
    begin match kind with
    | NArrayGroup -> Spec.array_group3_zero_or_more_equiv (array_group_sem env g1) (array_group_sem env g2)
    | _ -> ()
    end
  | GArrayElem sq ty ->
    rewrite_typ_correct env fuel' ty;
    Spec.array_group3_item_equiv (typ_sem env ty) (typ_sem env (rewrite_typ fuel' ty))
  | GMapElem sq cut key value ->
    rewrite_typ_correct env fuel' key;
    rewrite_typ_correct env fuel' value;
    MapSpec.map_group_match_item_ext cut (typ_sem env key) (typ_sem env value) (typ_sem env (rewrite_typ fuel' key)) (typ_sem env (rewrite_typ fuel' value))
  | GAlwaysFalse
  | GNop
  | GDef _ _ -> ()

#pop-options

(* Disjointness *)

let destruct_group
  (#n: name_env_elem)
  (g: group n)
: Tot (group n & group n)
= match g with
  | GConcat g1 g2 -> (g1, g2)
  | _ -> (g, GNop)

let maybe_close_array_group_concat
  (close: bool)
  (a1 a2: Spec.array_group3 None)
: Lemma
  (Spec.array_group3_equiv
    (Spec.maybe_close_array_group (Spec.array_group3_concat a1 a2) close)
    (Spec.array_group3_concat a1 (Spec.maybe_close_array_group a2 close))
  )
= ()

let array_group_sem_destruct_group
  (e: sem_env)
  (g: group NArrayGroup { group_bounded _ e.se_bound g })
: Lemma
  (let (g1, g2) = destruct_group g in
    group_bounded _ e.se_bound g1 /\
    group_bounded _ e.se_bound g2 /\
    array_group_sem e g `Spec.array_group3_equiv` (array_group_sem e g1 `Spec.array_group3_concat` array_group_sem e g2)
  )
= ()

let maybe_close_array_group_sem_destruct_group
  (close: bool)
  (e: sem_env)
  (g: group NArrayGroup { group_bounded _ e.se_bound g })
: Lemma
  (let (g1, g2) = destruct_group g in
    group_bounded _ e.se_bound g1 /\
    group_bounded _ e.se_bound g2 /\
    Spec.maybe_close_array_group (array_group_sem e g) close `Spec.array_group3_equiv`
      (array_group_sem e g1 `Spec.array_group3_concat` Spec.maybe_close_array_group (array_group_sem e g2) close)
  )
  [SMTPat (Spec.maybe_close_array_group (array_group_sem e g) close)]
= ()

#restart-solver
let array_group_concat_elem_same_disjoint
  (close: bool)
  (t1 t2: Spec.typ)
  (a1 a2: Spec.array_group3 None)
: Lemma
  (requires
    Spec.typ_equiv t1 t2
  )
  (ensures (Spec.array_group3_disjoint (Spec.maybe_close_array_group a1 close) (Spec.maybe_close_array_group a2 close) ==>
    Spec.array_group3_disjoint
      (Spec.maybe_close_array_group (Spec.array_group3_concat (Spec.array_group3_item t1) a1) close)
      (Spec.maybe_close_array_group (Spec.array_group3_concat (Spec.array_group3_item t2) a2) close)
  ))
= maybe_close_array_group_concat close (Spec.array_group3_item t1) a1;
  maybe_close_array_group_concat close (Spec.array_group3_item t1) a2

#push-options "--admit_smt_queries true" // "--z3rlimit 128 --query_stats --split_queries always --fuel 4 --ifuel 8"

#restart-solver
[@@"opaque_to_smt"]
let rec typ_disjoint
  (e: ast_env)
  (fuel: nat)
  (t1: typ { typ_bounded e.e_sem_env.se_bound t1 })
  (t2: typ { typ_bounded e.e_sem_env.se_bound t2 })
: Pure (result unit) // I cannot use `squash` because of unification, yet I want to shortcut disjointness symmetry
    (requires True)
    (ensures fun r -> RSuccess? r ==> Spec.typ_disjoint (typ_sem e.e_sem_env t1) (typ_sem e.e_sem_env t2))
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | TElem EAlwaysFalse, _
  | _, TElem EAlwaysFalse -> RSuccess ()
  | TElem EAny, _
  | _, TElem EAny -> RFailure "typ_disjoint: EAny"
  | _ ->
    if t1 = t2
    then RFailure "typ_disjoint: irrefl"
    else begin
  match t1, t2 with
  | t2, TDef i
  | TDef i, t2 ->
    let s1 = e.e_sem_env.se_env i in
    let t1' = e.e_env i in
    typ_disjoint e fuel' t1' t2
  | TChoice t1l t1r, t2
  | t2, TChoice t1l t1r ->
    let rl = typ_disjoint e fuel' t1l t2 in
    if not (RSuccess? rl)
    then rl
    else typ_disjoint e fuel' t1r t2
  | TTagged tag1 t1', TTagged tag2 t2' ->
    if tag1 = tag2
    then typ_disjoint e fuel' t1' t2'
    else RSuccess ()
  | TTagged _ _, _
  | _, TTagged _ _ -> RSuccess ()
  | TElem EBool, TElem (ELiteral (LSimple v))
  | TElem (ELiteral (LSimple v)), TElem EBool ->
    if v = Spec.simple_value_true
    then RFailure "typ_disjoint: Bool vs. simple_value_true"
    else if v = Spec.simple_value_false
    then RFailure "typ_disjoint: Bool vs. simple_value_false"
    else RSuccess ()
  | TElem (ELiteral (LInt ty _)), TElem EUInt
  | TElem EUInt, TElem (ELiteral (LInt ty _)) ->
    if ty = CBOR.Spec.cbor_major_type_uint64
    then RFailure "typ_disjoint: uint64"
    else RSuccess ()
  | TElem (ELiteral (LInt ty _)), TElem ENInt
  | TElem ENInt, TElem (ELiteral (LInt ty _)) ->
    if ty = CBOR.Spec.cbor_major_type_neg_int64
    then RFailure "typ_disjoint: neg_int64"
    else RSuccess ()
  | TElem (ELiteral (LString ty _)), TElem EByteString
  | TElem EByteString, TElem (ELiteral (LString ty _)) ->
    if ty = CBOR.Spec.cbor_major_type_byte_string
    then RFailure "typ_disjoint: byte string"
    else RSuccess ()
  | TElem (ELiteral (LString ty _)), TElem ETextString
  | TElem ETextString, TElem (ELiteral (LString ty _)) ->
    if ty = CBOR.Spec.cbor_major_type_text_string
    then RFailure "typ_disjoint: text string"
    else RSuccess ()
  | TElem e1, TElem e2 ->
    RSuccess ()
  | TElem _, _
  | _, TElem _ -> RSuccess ()
  | TMap _, TMap _ -> RFailure "typ_disjoint: map: not supported"
  | TMap _, _
  | _, TMap _ -> RSuccess ()
  | TArray a1, TArray a2 ->
    Spec.array3_close_array_group (array_group_sem e.e_sem_env a1);
    Spec.array3_close_array_group (array_group_sem e.e_sem_env a2);
    array_group_disjoint e fuel' true a1 a2
  | TArray _, _
  | _, TArray _ -> RSuccess ()
  end

and array_group_disjoint
  (e: ast_env)
  (fuel: nat)
  (close: bool)
  (a1: group NArrayGroup { group_bounded _ e.e_sem_env.se_bound a1 })
  (a2: group NArrayGroup { group_bounded _ e.e_sem_env.se_bound a2 })
: Pure (result unit)
    (requires True)
    (ensures fun r ->
      RSuccess? r ==> Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close)
    )
    (decreases fuel)
= let a10 = a1 in
  let a20 = a2 in
  if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match (a1, destruct_group a1), (a2, destruct_group a2) with
  | (GAlwaysFalse, _), _
  | _, (GAlwaysFalse, _) -> RSuccess ()
  | _ ->
    if a1 = a2
    then RFailure "array_group_disjoint: irrefl"
    else begin
  match (a1, destruct_group a1), (a2, destruct_group a2) with
  | (GChoice a1l a1r, _), (a2, _)
  | (a2, _), (GChoice a1l a1r, _) ->
    let res1 = array_group_disjoint e fuel' close a1l a2 in
    if not (RSuccess? res1)
    then res1
    else array_group_disjoint e fuel' close a1r a2
  | (_, (GDef _ n, a1r)), (a2, _)
  | (a2, _), (_, (GDef _ n, a1r)) ->
    let a1' = GConcat (e.e_env n) a1r in
    rewrite_group_correct e.e_sem_env fuel' a1';
    array_group_disjoint e fuel' close (rewrite_group fuel' _ a1') a2
  | (a1, (GZeroOrMore g, a1r)), (a2, _)
  | (a2, _), (a1, (GZeroOrMore g, a1r)) ->
    assert (
     Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close) <==>
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close)
     );
     let res1 = array_group_disjoint e fuel' close a1r a2 in
     if not (RSuccess? res1)
     then res1
     else if RSuccess? (array_group_disjoint e fuel' false g a2) // loop-free shortcut, but will miss things like "disjoint? (a* ) (ab)"
     then RSuccess ()
     else begin
       Spec.array_group3_concat_assoc (array_group_sem e.e_sem_env g) (array_group_sem e.e_sem_env (GZeroOrMore g)) (array_group_sem e.e_sem_env a1r);
       let a1' = GConcat g a1 in
       rewrite_group_correct e.e_sem_env fuel' a1';
       array_group_disjoint e fuel' close (rewrite_group fuel' _ a1') a2 // potential source of loops
     end
   | (a1, (GOneOrMore g, a1r)), (a2, _)
   | (a2, _), (a1, (GOneOrMore g, a1r)) ->
     assert (
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close) <==>
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close)
     );
     let a1' = GConcat (GConcat g (GZeroOrMore g)) a1r in
     rewrite_group_correct e.e_sem_env fuel' a1';
     array_group_disjoint e fuel' close (rewrite_group fuel' _ a1') a2 // potential source of loops
   | (a1, (GZeroOrOne g, a1r)), (a2, _)
   | (a2, _), (a1, (GZeroOrOne g, a1r)) ->
     assert (
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close) <==>
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close)
     );
     let res = array_group_disjoint e fuel' close a1r a2 in
     if not (RSuccess? res)
     then res
     else begin
       let a1' = GConcat g a1r in
       rewrite_group_correct e.e_sem_env fuel' a1';
       array_group_disjoint e fuel' close (rewrite_group fuel' _ a1') a2
     end
   | (GNop, _), (_, (GArrayElem _ _, _))
   | (_, (GArrayElem _ _, _)), (GNop, _) ->
     if close then RSuccess () else RFailure "array_group_disjoint: empty but not close"
   | (_, (GArrayElem _ a1l, a1r)), (_, (GArrayElem _ a2l, a2r)) ->
     let res1 = typ_disjoint e fuel' a1l a2l in
     if RSuccess? res1
     then res1
     else if a1l = a2l // TODO: replace with equivalence?
     then begin
       array_group_concat_elem_same_disjoint
         close
         (typ_sem e.e_sem_env a1l)
         (typ_sem e.e_sem_env a2l)
         (array_group_sem e.e_sem_env a1r)
         (array_group_sem e.e_sem_env a2r);
       array_group_disjoint e fuel' close a1r a2r
     end
     else res1
   | (_, (GConcat a11 a12, a13)), (a2, _)
   | (a2, _), (_, (GConcat a11 a12, a13)) ->
     array_group_disjoint e fuel' close (GConcat a11 (GConcat a12 a13)) a2
   | _ -> RFailure "array_group_disjoint: array: unsupported pattern"
  end

#pop-options

#restart-solver
let rec map_group_footprint
  (g: group NMapGroup)
: Tot (result typ)
= match g with
  | GMapElem _ cut (TElem (ELiteral key)) value
  -> RSuccess (TElem (ELiteral key))
  | GZeroOrMore (GMapElem _ false key _) // TODO: extend to GOneOrMore
  -> RSuccess key
  | GZeroOrOne g -> map_group_footprint g
  | GChoice g1 g2
  | GConcat g1 g2 ->
    begin match map_group_footprint g1 with
    | RSuccess ty1 ->
      begin match map_group_footprint g2 with
      | RSuccess ty2 -> RSuccess (ty1 `TChoice` ty2)
      | res -> res
      end
    | res -> res
    end
  | GNop
  | GAlwaysFalse -> RSuccess (TElem EAlwaysFalse)
  | GMapElem _ _ _ _
  | GZeroOrMore _
  | GOneOrMore _ -> RFailure "map_group_footprint: unsupported cases. Please `rewrite` your map group before calling"

#push-options "--z3rlimit 32"

#restart-solver
let rec map_group_footprint_correct'
  (env: sem_env)
  (g: group NMapGroup)
: Lemma
  (requires (
    group_bounded _ env.se_bound g
  ))
  (ensures (
    match spec_map_group_footprint env g, map_group_footprint g with
    | Some ty, RSuccess t ->
      typ_bounded env.se_bound t /\
      ty `Spec.typ_equiv` typ_sem env t
    | _, RSuccess _ -> False
    | Some _, _ -> False
    | _ -> True
  ))
  (decreases g)
= match g with
  | GZeroOrOne g ->
    map_group_footprint_correct' env g
  | GChoice g1 g2
  | GConcat g1 g2 ->
    map_group_footprint_correct' env g1;
    map_group_footprint_correct' env g2
  | _ -> ()

let map_group_footprint_correct
  (env: sem_env)
  (g: group NMapGroup)
: Lemma
  (requires (
    group_bounded _ env.se_bound g
  ))
  (ensures (
    match spec_map_group_footprint env g, map_group_footprint g with
    | Some ty, RSuccess t ->
      typ_bounded env.se_bound t /\
      ty `Spec.typ_equiv` typ_sem env t /\
      MapSpec.map_group_footprint (map_group_sem env g) (typ_sem env t)
    | _, RSuccess _ -> False
    | Some _, _ -> False
    | _ -> True
  ))
  (decreases g)
  [SMTPat (spec_map_group_footprint env g)]
= map_group_footprint_correct' env g;
  match spec_map_group_footprint env g, map_group_footprint g with
  | Some ty, RSuccess t ->
    MapSpec.map_group_footprint_equiv (map_group_sem env g) ty (typ_sem env t)
  | _ -> ()

let coerce_failure
  (#t1 #t2: Type)
  (r: result t1 { ~ (RSuccess? r) })
: Tot (result t2)
= match r with
  | RFailure msg -> RFailure msg
  | ROutOfFuel -> ROutOfFuel

#restart-solver
let rec restrict_map_group
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (left: typ)
  (g: group NMapGroup)
: Pure (result (group NMapGroup))
    (requires (
      typ_bounded env.e_sem_env.se_bound left /\
      group_bounded _ env.e_sem_env.se_bound g
    ))
    (ensures (fun g' ->
      match g' with
      | RSuccess g' ->
        group_bounded _ env.e_sem_env.se_bound g' /\
        MapSpec.restrict_map_group
          (map_group_sem env.e_sem_env g)
          (map_group_sem env.e_sem_env g') /\
        begin match spec_map_group_footprint env.e_sem_env g, spec_map_group_footprint env.e_sem_env g' with
        | Some fp, Some fp' -> Spec.typ_included fp' fp /\
          Spec.typ_disjoint (typ_sem env.e_sem_env left) fp'
        | _ -> False
        end
      | _ -> True
    ))
  (decreases g)
= match g with
  | GChoice g1 g2 ->
    begin match restrict_map_group fuel env left g1 with
    | RSuccess g1' ->
      begin match restrict_map_group fuel env left g2 with
      | RSuccess g2' -> RSuccess (GChoice g1' g2')
      | res -> res
      end
    | res -> res
    end
  | GConcat g1 g2 ->
    begin match restrict_map_group fuel env left g1 with
    | RSuccess g1' ->
      let RSuccess fp1 = map_group_footprint g1 in
      begin match restrict_map_group fuel env (left `TChoice` fp1) g2 with
      | RSuccess g2' ->
        let f2' = Ghost.hide (Some?.v (spec_map_group_footprint env.e_sem_env g2')) in
        MapSpec.restrict_map_group_concat
          (map_group_sem env.e_sem_env g1)
          (typ_sem env.e_sem_env fp1)
          (map_group_sem env.e_sem_env g1')
          (map_group_sem env.e_sem_env g2)
          (map_group_sem env.e_sem_env g2')
          f2';
        let g' = GConcat g1' g2' in
        assert (MapSpec.restrict_map_group
          (map_group_sem env.e_sem_env g)
          (map_group_sem env.e_sem_env g')
        );
        assert (Some? (spec_map_group_footprint env.e_sem_env g));
        assert (Some? (spec_map_group_footprint env.e_sem_env g'));
        assert (
          let Some fp = spec_map_group_footprint env.e_sem_env g in
          let Some fp' = spec_map_group_footprint env.e_sem_env g' in
          Spec.typ_included fp' fp /\
          Spec.typ_disjoint (typ_sem env.e_sem_env left) fp'
        );
        RSuccess g' // (rewrite_group fuel _ g')
      | res -> res
      end
    | res -> res
    end
  | GZeroOrOne g1 ->
    begin match restrict_map_group fuel env left g1 with
    | RSuccess g1' -> RSuccess (GZeroOrOne g1')
    | res -> res
    end
  | GMapElem sq cut (TElem (ELiteral key)) value ->
    begin match typ_disjoint env fuel (TElem (ELiteral key)) left with
    | RSuccess _ ->
      MapSpec.map_group_is_det_match_item_for
        cut
        (eval_literal key)
        (typ_sem env.e_sem_env value);
      MapSpec.restrict_map_group_refl (map_group_sem env.e_sem_env g);
      RSuccess g
    | res -> coerce_failure res
    end
  | GZeroOrMore (GMapElem _ false key value) ->
    begin match typ_disjoint env fuel key left with
    | RSuccess _ ->
      MapSpec.restrict_map_group_refl (map_group_sem env.e_sem_env g);
      RSuccess g
    | ROutOfFuel -> ROutOfFuel // the restriction heuristics should not depend on the fuel
    | _ ->
      RSuccess GNop
    end
  | _ -> RFailure "restrict_map_group: unsupported cases"

#pop-options

noeq
type mk_wf_validate_map_group_t (left_elems: Spec.typ) (left_tables: Spec.typ) (g1: group NMapGroup) = {
  left_elems1: Spec.typ;
  left_tables1: Spec.typ;
  wf: ast0_wf_validate_map_group left_elems left_tables g1 left_elems1 left_tables1;
  left_elems10: typ;
  left_tables10: typ;
}

let rec array_group_is_nonempty
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (g: group NArrayGroup)
: Pure (result unit)
    (requires (group_bounded _ env.e_sem_env.se_bound g))
    (ensures fun r -> match r with
    | RSuccess _ -> Spec.array_group3_is_nonempty (array_group_sem env.e_sem_env g)
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match g with
  | GDef _ n -> array_group_is_nonempty fuel' env (env.e_env n)
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
  | GArrayElem _ _
  | GAlwaysFalse -> RSuccess ()

#push-options "--admit_smt_queries true" // "--z3rlimit 64 --split_queries always --query_stats --fuel 4 --ifuel 8"

#restart-solver
let rec array_group_concat_unique_strong
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (#g1: group NArrayGroup)
  (s1: ast0_wf_array_group g1)
  (g2: group NArrayGroup)
: Pure (result unit)
    (requires (
      spec_wf_array_group env.e_sem_env _ s1 /\
      group_bounded _ env.e_sem_env.se_bound g2
    ))
    (ensures fun r -> match r with
    | RSuccess _ -> Spec.array_group3_concat_unique_strong (array_group_sem env.e_sem_env g1) (array_group_sem env.e_sem_env g2)
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match s1 with
  | WfAChoice g1l g1r s1l s1r ->
    let res1 = array_group_concat_unique_strong fuel' env s1l g2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_strong fuel' env s1r g2 in
    if not (RSuccess? res2)
    then res2
    else begin
      Spec.array_group3_concat_unique_strong_choice_left
        (array_group_sem env.e_sem_env g1l)
        (array_group_sem env.e_sem_env g1r)
        (array_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | WfAConcat g1l g1r s1l s1r ->
    let res1 = array_group_concat_unique_strong fuel' env s1r g2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_strong fuel' env s1l (GConcat g1r g2) in
    if not (RSuccess? res2)
    then res2
    else begin
      Spec.array_group3_concat_unique_strong_concat_left (array_group_sem env.e_sem_env g1l) (array_group_sem env.e_sem_env g1r) (array_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | WfAElem _ _ -> RSuccess ()
  | WfADef n ->
    begin match env.e_wf n with
      | None -> RFailure "array_group_concat_unique_strong: unfold left, not proven yet"
      | Some s -> array_group_concat_unique_strong fuel' env #(env.e_env n) s g2
    end
  | _ ->
    begin match destruct_group g2 with
    | (GDef _ i, g2r) ->
      let g2' = GConcat (env.e_env i) g2r in
      Spec.array_group3_concat_equiv
        (env.e_sem_env.se_env i)
        (array_group_sem env.e_sem_env (env.e_env i))
        (array_group_sem env.e_sem_env g2r)
        (array_group_sem env.e_sem_env g2r);
      rewrite_group_correct env.e_sem_env fuel g2';
      let g22 = rewrite_group fuel _ g2' in
      Spec.array_group3_concat_unique_strong_equiv
        (array_group_sem env.e_sem_env g1)
        (array_group_sem env.e_sem_env g1)
        (array_group_sem env.e_sem_env g2)
        (array_group_sem env.e_sem_env g22);
      array_group_concat_unique_strong fuel' env s1 g22
    | _ ->
      begin match s1 with
      | WfAZeroOrOneOrMore g' s' g1' ->
        let res1 = array_group_disjoint env fuel false g' g2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_strong fuel' env s' g' in
        if not (RSuccess? res2)
        then res2
        else let res3 = array_group_concat_unique_strong fuel' env s' g2 in
        if not (RSuccess? res3)
        then res3
        else begin
          match g1' with
          | GZeroOrMore _ ->
            Spec.array_group3_concat_unique_strong_zero_or_more_left
              (array_group_sem env.e_sem_env g')
              (array_group_sem env.e_sem_env g2);
            RSuccess ()
          | GOneOrMore _ ->
            Spec.array_group3_concat_unique_strong_one_or_more_left
              (array_group_sem env.e_sem_env g')
              (array_group_sem env.e_sem_env g2);
            RSuccess ()          
        end
      | WfAZeroOrOne g' s' ->
        let res1 = array_group_disjoint env fuel false g' g2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_strong fuel' env s' g2 in
        if not (RSuccess? res2)
        then res2
        else begin
          Spec.array_group3_concat_unique_strong_zero_or_one_left
            (array_group_sem env.e_sem_env g')
            (array_group_sem env.e_sem_env g2);
          assert (Spec.array_group3_concat_unique_strong
            (Spec.array_group3_zero_or_one (array_group_sem env.e_sem_env g'))
            (array_group_sem env.e_sem_env g2)
          );
          assert (Spec.array_group3_concat_unique_strong
            (array_group_sem env.e_sem_env g1)
            (array_group_sem env.e_sem_env g2)
          );
          RSuccess ()
        end
      end
    end

#restart-solver
let rec array_group_concat_unique_weak
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (#g1: group NArrayGroup)
  (s1: ast0_wf_array_group g1)
  (#g2: group NArrayGroup)
  (s2: ast0_wf_array_group g2)
: Pure (result unit)
    (requires (
      spec_wf_array_group env.e_sem_env _ s1 /\
      spec_wf_array_group env.e_sem_env _ s2
    ))
    (ensures fun r -> match r with
    | RSuccess _ -> Spec.array_group3_concat_unique_weak (array_group_sem env.e_sem_env g1) (array_group_sem env.e_sem_env g2)
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match s1 with
  | WfAChoice g1l g1r s1l s1r ->
    let res1 = array_group_concat_unique_weak fuel' env s1l s2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_weak fuel' env s1r s2 in
    if not (RSuccess? res2)
    then res2
    else begin
      Spec.array_group3_concat_unique_weak_choice_left
        (array_group_sem env.e_sem_env g1l)
        (array_group_sem env.e_sem_env g1r)
        (array_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | _ ->
    begin match s2 with
    | WfAChoice g2l g2r s2l s2r ->
      let res1 = array_group_concat_unique_weak fuel' env s1 s2l in
      if not (RSuccess? res1)
      then res1
      else let res2 = array_group_concat_unique_weak fuel' env s1 s2r in
      if not (RSuccess? res2)
      then res2
      else begin
        Spec.array_group3_concat_unique_weak_choice_right
          (array_group_sem env.e_sem_env g1)
          (array_group_sem env.e_sem_env g2l)
          (array_group_sem env.e_sem_env g2r);
        RSuccess ()
      end
    | _ ->
      begin match s1 with
      | WfAElem _ _ -> RSuccess ()
      | WfAConcat g1l g1r s1l s1r ->
        let res1 = array_group_concat_unique_weak fuel' env s1r s2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_weak fuel' env s1l (WfAConcat g1r g2 s1r s2) in
        if not (RSuccess? res2)
        then res2
        else begin
          Spec.array_group_concat_unique_weak_concat_left
            (array_group_sem env.e_sem_env g1l)
            (array_group_sem env.e_sem_env g1r)
            (array_group_sem env.e_sem_env g2);
          RSuccess ()
        end
      | WfADef n ->
        begin match env.e_wf n with
        | None -> RFailure "array_group_concat_unique_weak: unfold left, not proven yet"
        | Some s1' ->
          array_group_concat_unique_weak fuel' env #(env.e_env n) s1' s2
        end
      | WfAZeroOrOneOrMore g s g' ->
        let res1 = array_group_disjoint env fuel false g g2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_strong fuel env s g in
        if not (RSuccess? res2)
        then res2
        else let res3 = array_group_concat_unique_weak fuel' env s s2 in
        if not (RSuccess? res3)
        then res3
        else begin
          match g' with
          | GZeroOrMore _ ->
            Spec.array_group3_concat_unique_weak_zero_or_more_left
              (array_group_sem env.e_sem_env g)
              (array_group_sem env.e_sem_env g2);
            RSuccess ()
          | GOneOrMore _ ->
            Spec.array_group3_concat_unique_weak_one_or_more_left
              (array_group_sem env.e_sem_env g)
              (array_group_sem env.e_sem_env g2);
            RSuccess ()
        end
      | WfAZeroOrOne g s ->
        let res1 = array_group_disjoint env fuel false g g2 in
        if not (RSuccess? res1)
        then res1
        else let res2 = array_group_concat_unique_weak fuel' env s s2 in
        if not (RSuccess? res2)
        then res2
        else begin
          Spec.array_group3_concat_unique_weak_zero_or_one_left
            (array_group_sem env.e_sem_env g)
            (array_group_sem env.e_sem_env g2);
          RSuccess ()
        end
      end
    end

#restart-solver
let rec map_group_choice_compatible_no_cut
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (#g1: group NMapGroup)
  (s1: ast0_wf_parse_map_group g1)
  (#g2: group NMapGroup)
  (s2: ast0_wf_parse_map_group g2)
: Pure (result unit)
    (requires (
      spec_wf_parse_map_group env.e_sem_env _ s1 /\
      spec_wf_parse_map_group env.e_sem_env _ s2
    ))
    (ensures fun r -> match r with
    | RSuccess _ -> MapSpec.map_group_choice_compatible_no_cut (map_group_sem env.e_sem_env g1) (map_group_sem env.e_sem_env g2)
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match s1 with
  | WfMLiteral false key value _ ->
    MapSpec.map_group_choice_compatible_no_cut_match_item_for_no_cut
      (eval_literal key)
      (typ_sem env.e_sem_env value)
      (map_group_sem env.e_sem_env g2);
    RSuccess ()
  | WfMZeroOrMore key value _ _ ->
    MapSpec.map_group_choice_compatible_no_cut_zero_or_more_match_item_left
      (typ_sem env.e_sem_env key)
      (typ_sem env.e_sem_env value)
      (map_group_sem env.e_sem_env g2);
    RSuccess ()
  | WfMChoice g1l s1l g1r s1r ->
    let res1 = map_group_choice_compatible_no_cut fuel' env s1l s2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = map_group_choice_compatible_no_cut fuel' env s1r s2 in
    if not (RSuccess? res2)
    then res2
    else begin
      MapSpec.map_group_choice_compatible_no_cut_choice_left
        (map_group_sem env.e_sem_env g1l)
        (map_group_sem env.e_sem_env g1r)
        (map_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | WfMZeroOrOne g s ->
    let res1 = map_group_choice_compatible_no_cut fuel' env s s2 in
    if not (RSuccess? res1)
    then res1
    else begin
      MapSpec.map_group_choice_compatible_no_cut_zero_or_one_left
        (map_group_sem env.e_sem_env g)
        (map_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | WfMLiteral _ key value _ ->
    map_group_footprint_correct env.e_sem_env g2;
    let RSuccess f2 = map_group_footprint g2 in
    let res1 = typ_disjoint env fuel (TElem (ELiteral key)) f2 in
    if not (RSuccess? res1)
    then res1
    else begin
      MapSpec.map_group_choice_compatible_no_cut_match_item_for_cut
        (eval_literal key)
        (typ_sem env.e_sem_env value)
        (map_group_sem env.e_sem_env g2)
        (typ_sem env.e_sem_env f2);
      RSuccess ()
    end
  | WfMConcat g1l s1l g1r s1r ->
    let res1 = map_group_choice_compatible_no_cut fuel' env s1l s2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = map_group_choice_compatible_no_cut fuel' env s1r s2 in
    if not (RSuccess? res2)
    then res2
    else begin
      MapSpec.map_group_choice_compatible_no_cut_concat_left
        (map_group_sem env.e_sem_env g1l)
        (Some?.v (spec_map_group_footprint env.e_sem_env g1l))
        (map_group_sem env.e_sem_env g1r)
        (Some?.v (spec_map_group_footprint env.e_sem_env g1r))
        (map_group_sem env.e_sem_env g2);
      RSuccess ()
    end

#restart-solver
let rec map_group_choice_compatible
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (#g1: group NMapGroup)
  (s1: ast0_wf_parse_map_group g1)
  (#g2: group NMapGroup)
  (s2: ast0_wf_parse_map_group g2)
: Pure (result unit)
    (requires (
      spec_wf_parse_map_group env.e_sem_env _ s1 /\
      spec_wf_parse_map_group env.e_sem_env _ s2
    ))
    (ensures fun r -> match r with
    | RSuccess _ -> MapSpec.map_group_choice_compatible (map_group_sem env.e_sem_env g1) (map_group_sem env.e_sem_env g2)
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match s1 with
  | WfMZeroOrMore _ _ _ _ ->
    RFailure "map_group_choice_compatible: GZeroOrMore never fails"
  | WfMZeroOrOne _ _ ->
    RFailure "map_group_choice_compatible: GZeroOrOne always succeeds or cuts, but never fails"
  | WfMChoice g1l s1l g1r s1r ->
    let res1 = map_group_choice_compatible fuel' env s1l s2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = map_group_choice_compatible fuel' env s1r s2 in
    if not (RSuccess? res2)
    then res2
    else begin
      MapSpec.map_group_choice_compatible_choice_left
        (map_group_sem env.e_sem_env g1l)
        (map_group_sem env.e_sem_env g1r)
        (map_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | _ ->
    begin match s2 with
    | WfMChoice g2l s2l g2r s2r ->
      let res1 = map_group_choice_compatible fuel' env s1 s2l in
      if not (RSuccess? res1)
      then res1
      else let res2 = map_group_choice_compatible fuel' env s1 s2r in
      if not (RSuccess? res2)
      then res2
      else begin
        MapSpec.map_group_choice_compatible_choice_right
          (map_group_sem env.e_sem_env g1)
          (map_group_sem env.e_sem_env g2l)
          (map_group_sem env.e_sem_env g2r);
        RSuccess ()
      end
    | _ ->
      begin match s1 with
      | WfMConcat g1l s1l g1r s1r ->
        begin match map_group_choice_compatible fuel' env s1l s2 with
        | RSuccess _ ->
          MapSpec.map_group_choice_compatible_concat_left
            (map_group_sem env.e_sem_env g1l)
            (Some?.v (spec_map_group_footprint env.e_sem_env g1l))
            (map_group_sem env.e_sem_env g1r)
            (Some?.v (spec_map_group_footprint env.e_sem_env g1r))
            (map_group_sem env.e_sem_env g2);
          RSuccess ()
        | ROutOfFuel -> ROutOfFuel
        | RFailure _ ->
          let res1 = map_group_choice_compatible_no_cut fuel env s1l s2 in
          if not (RSuccess? res1)
          then res1
          else let res2 = map_group_choice_compatible fuel' env s1r s2 in
          if not (RSuccess? res2)
          then res2
          else begin
            MapSpec.map_group_choice_compatible_concat_left
              (map_group_sem env.e_sem_env g1l)
              (Some?.v (spec_map_group_footprint env.e_sem_env g1l))
              (map_group_sem env.e_sem_env g1r)
              (Some?.v (spec_map_group_footprint env.e_sem_env g1r))
              (map_group_sem env.e_sem_env g2);
            RSuccess ()
          end
        end
      | WfMLiteral cut key value _ ->
        map_group_footprint_correct env.e_sem_env g2;
        let RSuccess f2 = map_group_footprint g2 in
        begin match typ_disjoint env fuel (TElem (ELiteral key)) f2 with
        | RSuccess _ ->
          MapSpec.map_group_choice_compatible_match_item_for cut (eval_literal key) (typ_sem env.e_sem_env value) (map_group_sem env.e_sem_env g2) (typ_sem env.e_sem_env f2);
          RSuccess ()
        | ROutOfFuel -> ROutOfFuel
        | RFailure _ ->
          if cut
          then RFailure "map_group_choice_compatible: GMapElem true (TElem (ELiteral key)) value, not disjoint"
          else begin match s2 with
          | WfMConcat g2l s2l g2r s2r ->
            let res1 = map_group_choice_compatible fuel' env s1 s2l in
            if not (RSuccess? res1)
            then res1
            else let res2 = map_group_choice_compatible fuel' env s1 s2r in
            if not (RSuccess? res2)
            then res2
            else begin
              MapSpec.map_group_choice_compatible_match_item_for_concat_right
                (eval_literal key)
                (typ_sem env.e_sem_env value)
                (map_group_sem env.e_sem_env g2l)
                (map_group_sem env.e_sem_env g2r)
                (Some?.v (spec_map_group_footprint env.e_sem_env g2l))
                (Some?.v (spec_map_group_footprint env.e_sem_env g2r));
              RSuccess ()
            end
          | WfMZeroOrOne g s ->
            let res1 = map_group_choice_compatible fuel' env s1 s in
            if not (RSuccess? res1)
            then res1
            else begin
              MapSpec.map_group_choice_compatible_match_item_for_zero_or_one_right cut (eval_literal key) (typ_sem env.e_sem_env value) (map_group_sem env.e_sem_env g);
              RSuccess ()
            end
          | WfMLiteral cut2 key2 value2 _ ->
            if key <> key2
            then begin // this case should already have been eliminated by the typ_disjoint test above
              MapSpec.map_group_choice_compatible_match_item_for cut (eval_literal key) (typ_sem env.e_sem_env value) (map_group_sem env.e_sem_env g2) (Spec.t_literal (eval_literal key2));
              RSuccess ()
            end else begin
              let res1 = typ_disjoint env fuel value value2 in
              if not (RSuccess? res1)
              then res1
              else begin
                MapSpec.map_group_choice_compatible_match_item_for_same
                  (eval_literal key)
                  (typ_sem env.e_sem_env value)
                  (typ_sem env.e_sem_env value2)
                  cut2;
                RSuccess ()
              end
            end
          | WfMZeroOrMore _ _ _ _ -> RFailure "map_group_choice_compatible: GZeroOrMore right, not disjoint"
          end
        end
      end
    end

#pop-options

#push-options "--admit_smt_queries true" // "--z3rlimit 128 --split_queries always --query_stats --fuel 4 --ifuel 8"

#restart-solver
let rec mk_wf_typ
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (g: typ)
: Pure (result (ast0_wf_typ g))
    (requires typ_bounded env.e_sem_env.se_bound g)
    (ensures fun r -> match r with
    | RSuccess s -> spec_wf_typ env.e_sem_env g s
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
    begin match mk_wf_validate_map_group fuel' env Spec.t_always_false Spec.t_always_false (TElem EAlwaysFalse) (TElem EAlwaysFalse) m with
    | RSuccess s1 ->
      begin match restrict_map_group fuel env (TElem EAlwaysFalse) m with
      | RSuccess m2 ->
        rewrite_group_correct env.e_sem_env fuel m2;
        let m3 = rewrite_group fuel _ m2 in
        begin match mk_wf_parse_map_group fuel' env m3 with
        | RSuccess s3 -> RSuccess (WfTMap m _ _ s1.wf m3 s3)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | TTagged tag t' ->
    begin match mk_wf_typ fuel' env t' with
    | RSuccess s' -> RSuccess (WfTTagged tag t' s')
    | res -> coerce_failure res
    end
  | TChoice t1 t2 ->
    begin match typ_disjoint env fuel t1 t2 with
    | RSuccess _ ->
      begin match mk_wf_typ fuel' env t1 with
      | RSuccess s1 ->
        begin match mk_wf_typ fuel' env t2 with
        | RSuccess s2 -> RSuccess (WfTChoice t1 t2 s1 s2)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | TDef n -> RSuccess (WfTDef n)

and mk_wf_array_group
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (g: group NArrayGroup)
: Pure (result (ast0_wf_array_group g))
    (requires group_bounded _ env.e_sem_env.se_bound g)
    (ensures fun r -> match r with
    | RSuccess s -> spec_wf_array_group env.e_sem_env g s
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match g with
  | GArrayElem _ ty ->
    begin match mk_wf_typ fuel' env ty with
    | RSuccess s -> RSuccess (WfAElem ty s)
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
        begin match array_group_concat_unique_weak fuel env s1 s2 with
        | RSuccess _ -> RSuccess (WfAConcat g1 g2 s1 s2)
        | res -> coerce_failure res
        end
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | GChoice g1 g2 ->
    begin match array_group_disjoint env fuel false g1 g2 with
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
  | GDef _ n -> RSuccess (WfADef n)
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
        begin match array_group_concat_unique_strong fuel env s' g' with
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
  (g: group NMapGroup)
: Pure (result (ast0_wf_parse_map_group g))
    (requires group_bounded _ env.e_sem_env.se_bound g)
    (ensures fun r -> match r with
    | RSuccess s -> spec_wf_parse_map_group env.e_sem_env g s
    | _ -> True
    )
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match g with
  | GChoice g1 g2 ->
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
  | GMapElem _ cut (TElem (ELiteral key)) value ->
    begin match mk_wf_typ fuel' env value with
    | RSuccess tvalue -> RSuccess (WfMLiteral cut key value tvalue)
    | res -> coerce_failure res
    end
  | GZeroOrMore (GMapElem _ false key value) ->
    begin match mk_wf_typ fuel' env key with
    | RSuccess tkey ->
      begin match mk_wf_typ fuel' env value with
      | RSuccess tvalue -> RSuccess (WfMZeroOrMore key value tkey tvalue)
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | GZeroOrOne g' ->
    begin match map_group_is_productive g' with
    | RSuccess _ ->
      map_group_is_productive_correct env.e_sem_env g';
      begin match mk_wf_parse_map_group fuel' env g' with
      | RSuccess s' -> RSuccess (WfMZeroOrOne g' s')
      | res -> coerce_failure res
      end
    | res -> coerce_failure res
    end
  | GConcat g1 g2 ->
    begin match map_group_footprint g1 with
    | RSuccess fp1 ->
      begin match map_group_footprint g2 with
      | RSuccess fp2 ->
        map_group_footprint_correct env.e_sem_env g1;
        map_group_footprint_correct env.e_sem_env g2;
        begin match typ_disjoint env fuel fp1 fp2 with
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
  | _ -> RFailure "mk_wf_parse_map_group: unsupported"

and mk_wf_validate_map_group
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (left_elems: Spec.typ)
  (left_tables: Spec.typ)
  (left_elems0: typ)
  (left_tables0: typ)
  (g: group NMapGroup)
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

#pop-options

let mk_wf_typ'
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (g: typ)
: Tot (result (ast0_wf_typ g))
= if typ_bounded env.e_sem_env.se_bound g
  then begin
    rewrite_typ_correct env.e_sem_env fuel g;
    let g' = rewrite_typ fuel g in
    match mk_wf_typ fuel env g' with
    | RSuccess s' -> RSuccess (WfTRewrite g g' s')
    | res -> coerce_failure res
  end
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
= RSuccess?._0 (mk_wf_typ' fuel e t)

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
= wf_ast_env_extend_typ_with_weak e new_name t (RSuccess?._0 (mk_wf_typ' fuel e t))

exception ExceptionOutOfFuel

let solve_mk_wf_typ_fuel_for () : FStar.Tactics.Tac unit =
  let rec aux (n: nat) : FStar.Tactics.Tac unit =
    FStar.Tactics.try_with
    (fun _ ->
      FStar.Tactics.print ("solve_mk_wf_typ_fuel_for with fuel " ^ string_of_int n ^ "\n");
      FStar.Tactics.apply (FStar.Tactics.mk_app (`mk_wf_typ_fuel_for_intro) [quote n, FStar.Tactics.Q_Explicit]);
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.try_with
        (fun _ ->
          FStar.Tactics.trefl ()
        )
        (fun e -> 
          let g = FStar.Tactics.cur_goal () in
          FStar.Tactics.print ("solve_mk_wf_typ_fuel_for Failure: " ^ FStar.Tactics.term_to_string g ^ "\n");
          let g0 = quote (squash (ROutOfFuel == RSuccess ())) in
          FStar.Tactics.print ("Comparing with " ^ FStar.Tactics.term_to_string g0 ^ "\n");
          let e' =
            if g `FStar.Tactics.term_eq` g0
            then ExceptionOutOfFuel
            else e
          in
          FStar.Tactics.raise e'
        )
      )
      (fun e ->
        match e with
        | ExceptionOutOfFuel -> aux (n + 1)
        | _ -> FStar.Tactics.raise e
      )
  in
  aux 0

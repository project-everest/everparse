module CDDL.Spec.AST.Elab.Disjoint.Array
include CDDL.Spec.AST.Elab.Base

module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

#push-options "--z3rlimit 512 --query_stats --split_queries always --fuel 4 --ifuel 8"

let array_group_disjoint
  (typ_disjoint: typ_disjoint_t)
  (array_group_disjoint: array_group_disjoint_t)
  (fuel: nat)
: Tot array_group_disjoint_t
= fun e close1 close2 a1 a2 ->
  let a10 = a1 in
  let a20 = a2 in
  let close10 = close1 in
  let close20 = close2 in
  match (a1, destruct_group a1), (a2, destruct_group a2) with
  | (GAlwaysFalse, _), _
  | _, (GAlwaysFalse, _) -> RSuccess ()
  | _ ->
    if a1 = a2
    then RFailure "array_group_disjoint: irrefl"
    else begin
  match (a1, close1, destruct_group a1), (a2, close2, destruct_group a2) with
  | (GChoice a1l a1r, close1, _), (a2, close2, _)
  | (a2, close2, _), (GChoice a1l a1r, close1, _) ->
    let res1 = array_group_disjoint e  close1 close2 a1l a2 in
    if not (RSuccess? res1)
    then res1
    else array_group_disjoint e  close1 close2 a1r a2
  | (_, close1, (GDef n, a1r)), (a2, close2, _)
  | (a2, close2, _), (_, close1, (GDef n, a1r)) ->
    let en = match e.e_sem_env.se_bound n with
    | Some NGroup -> (e.e_env n)
    | Some NType -> GElem false (TElem EAny) (e.e_env n)
    in
    let a1' = GConcat en a1r in
    rewrite_group_correct e.e_sem_env  fuel false a1';
    let (a1_, res) = rewrite_group  fuel false a1' in
    if res
    then array_group_disjoint e  close1 close2 a1_ a2
    else ROutOfFuel
  | (a1, close1, (GZeroOrMore g, a1r)), (a2, close2, _)
  | (a2, close2, _), (a1, close1, (GZeroOrMore g, a1r)) ->
    array_group_disjoint_sym (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close10) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close20);
    assert (
     Spec.array_group_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close10) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close20) <==>
       Spec.array_group_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close1) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close2)
     );
     let res1 = array_group_disjoint e  close1 close2 a1r a2 in
     if not (RSuccess? res1)
     then res1
     else if RSuccess? (array_group_disjoint e  false close2 g a2) // loop-free shortcut, but will miss things like "disjoint? (a* ) (ab)"
     then RSuccess ()
     else begin
       Spec.array_group_concat_assoc (array_group_sem e.e_sem_env g) (array_group_sem e.e_sem_env (GZeroOrMore g)) (array_group_sem e.e_sem_env a1r);
       let a1' = GConcat g a1 in
       rewrite_group_correct e.e_sem_env  fuel false a1';
       let (a1_, res) = rewrite_group  fuel false a1' in
       if res
       then array_group_disjoint e  close1 close2 (a1_) a2 // potential source of loops
       else ROutOfFuel
     end
   | (a1, close1, (GOneOrMore g, a1r)), (a2, close2, _)
   | (a2, close2, _), (a1, close1, (GOneOrMore g, a1r)) ->
     array_group_disjoint_sym (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close10) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close20);
     assert (
       Spec.array_group_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close10) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close20) <==>
       Spec.array_group_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close1) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close2)
     );
     let a1' = GConcat (GConcat g (GZeroOrMore g)) a1r in
     rewrite_group_correct e.e_sem_env  fuel false a1';
     let (a1_, res) = rewrite_group  fuel false a1' in
     if res
     then array_group_disjoint e  close1 close2 (a1_) a2 // potential source of loops
     else ROutOfFuel
   | (a1, close1, (GZeroOrOne g, a1r)), (a2, close2, _)
   | (a2, close2, _), (a1, close1, (GZeroOrOne g, a1r)) ->
     array_group_disjoint_sym (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close10) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close20);
     assert (
       Spec.array_group_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close10) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close20) <==>
       Spec.array_group_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close1) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close2)
     );
     let res = array_group_disjoint e  close1 close2 a1r a2 in
     if not (RSuccess? res)
     then res
     else begin
       let a1' = GConcat g a1r in
       rewrite_group_correct e.e_sem_env  fuel false a1';
       let (a1_, res) = rewrite_group  fuel false a1' in
       if res
       then array_group_disjoint e  close1 close2 a1_ a2
       else ROutOfFuel
     end
   | (GNop, close, _), (_, _, (GElem _ _ _, _))
   | (_, _, (GElem _ _ _, _)), (GNop, close, _) ->
     if close then RSuccess () else RFailure "array_group_disjoint: empty but not close"
   | (_, _, (GElem _ _ a1l, a1r)), (_, _, (GElem _ _ a2l, a2r)) ->
     let res1 = typ_disjoint e  a1l a2l in
     if not (RFailure? res1)
     then res1
     else begin
       array_group_concat_elem_disjoint
         close1 close2
         (typ_sem e.e_sem_env a1l)
         (typ_sem e.e_sem_env a2l)
         (array_group_sem e.e_sem_env a1r)
         (array_group_sem e.e_sem_env a2r);
       array_group_disjoint e  close1 close2 a1r a2r
     end
   | (_, close1, (GConcat a11 a12, a13)), (a2, close2, _)
   | (a2, close2, _), (_, close1, (GConcat a11 a12, a13)) ->
     array_group_disjoint e  close1 close2 (GConcat a11 (GConcat a12 a13)) a2
   | _ -> RFailure "array_group_disjoint: array: unsupported pattern"
  end

#pop-options


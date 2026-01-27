module CDDL.Spec.AST.Elab.Included.Array
include CDDL.Spec.AST.Elab.Base
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

#push-options "--z3rlimit 512 --query_stats --split_queries always --fuel 4 --ifuel 8"

let array_group_included
  (typ_included: typ_included_t)
  (array_group_included: array_group_included_t)
  (array_group_disjoint: array_group_disjoint_t)
  (fuel: nat)
: array_group_included_t
= fun e close a1 a2 ->
  let a10 = a1 in
  let a20 = a2 in
  match (a1, destruct_group a1), (a2, destruct_group a2) with
  | (_, (GAlwaysFalse, _)), _ -> RSuccess ()
  | w ->
    if a1 = a2
    then RSuccess ()
    else begin
  match w with
  | (_, (GAlwaysFalse, _)), _ -> RSuccess ()
  | (_, (GConcat _ _, _)), _
  | _, (_, (GConcat _ _, _))
    -> RFailure "array_group_included: group should have been rewritten beforehand"
  | (_, (GChoice a1l a1r, a1q)), (a2, _) ->
    let a1l' = GConcat a1l a1q in
    rewrite_group_correct e.e_sem_env fuel false a1l';
    let (a1l_, res) = rewrite_group fuel false a1l' in
    if res
    then
    let res1 = array_group_included e close (a1l_) a2 in
    if not (RSuccess? res1)
    then res1
    else begin
      let a1r' = GConcat a1r a1q in
      rewrite_group_correct e.e_sem_env fuel false a1r';
      let (a1r_, res) = rewrite_group fuel false a1r' in
      if res
      then array_group_included e close (a1r_) a2
      else ROutOfFuel
    end
    else ROutOfFuel
  | (a1, _), (_, (GChoice a2l a2r, a2q)) ->
    let a2l' = GConcat a2l a2q in
    rewrite_group_correct e.e_sem_env fuel false a2l';
    let (a2l'', res) = rewrite_group fuel false a2l' in
    if res
    then begin
      let resl = array_group_included e close a1 a2l'' in
      if RFailure? resl
      then begin
        match array_group_disjoint e false false a1 a2l with
        | RSuccess _ ->
          let a2r' = GConcat a2r a2q in
          rewrite_group_correct e.e_sem_env fuel false a2r';
          Classical.move_requires
            (Spec.array_group_included_choice_r_r
              (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close)
              (array_group_sem e.e_sem_env a2l)
              (array_group_sem e.e_sem_env a2r)
            )
            (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2q) close);
          let (a2r_, res) = rewrite_group fuel false a2r' in
          if res
          then array_group_included e close a1 (a2r_)
          else ROutOfFuel
        | res -> res
      end
      else resl
    end
    else ROutOfFuel
  | (_, (GDef n, a1r)), (a2, _) ->
    let en = match e.e_sem_env.se_bound n with
    | Some NGroup -> (e.e_env n)
    | Some NType -> GElem false (TElem EAny) (e.e_env n)
    in
    let a1' = GConcat en a1r in
    rewrite_group_correct e.e_sem_env fuel false a1';
    let (a1_, res) = rewrite_group fuel false a1' in
    if res
    then array_group_included e close (a1_) a2
    else ROutOfFuel
  | (a2, _), (_, (GDef n, a1r)) ->
    let en = match e.e_sem_env.se_bound n with
    | Some NGroup -> (e.e_env n)
    | Some NType -> GElem false (TElem EAny) (e.e_env n)
    in
    let a1' = GConcat en a1r in
    rewrite_group_correct e.e_sem_env fuel false a1';
    let (a1_, res) = rewrite_group fuel false a1' in
    if res
    then array_group_included e close a2 (a1_)
    else ROutOfFuel
  | _, (_, (GAlwaysFalse, _)) -> RFailure "array_group_included: GAlwaysFalse"
  | (GNop, _), (_, (GZeroOrOne _, a2r))
  | (GNop, _), (_, (GZeroOrMore _, a2r))
    ->
      if close
      then array_group_included e close GNop a2r
      else RFailure "array_group_included: GNop"
  | (_, (GNop, _)), _
    -> RFailure "array_group_included: GNop"
  | (_, (GOneOrMore g, a1r)), (a2, _) ->
    let a1' = GConcat (GConcat g (GZeroOrMore g)) a1r in
    rewrite_group_correct e.e_sem_env fuel false a1';
    let (a1_, res) = rewrite_group fuel false a1' in
    if res
    then array_group_included e close (a1_) a2
    else ROutOfFuel
  | (a1, _), (_, (GOneOrMore g, a2r)) ->
    let a2' = GConcat (GConcat g (GZeroOrMore g)) a2r in
    rewrite_group_correct e.e_sem_env fuel false a2';
    let (a2_, res) = rewrite_group fuel false a2' in
    if res
    then array_group_included e close a1 (a2_)
    else ROutOfFuel
  | (_, (GZeroOrOne g1, a1r)), (a2, _) ->
    let a1' = GConcat g1 a1r in
    rewrite_group_correct e.e_sem_env fuel false a1';
    let (a1_, res) = rewrite_group fuel false a1' in
    if res
    then
      let res1 = array_group_included e close (a1_) a2 in
      if RSuccess? res1
      then array_group_included e close a1r a2
      else res1
    else ROutOfFuel
  | (a1, _), (_, (GZeroOrOne g2, a2r)) ->
    let a2' = GConcat g2 a2r in
    rewrite_group_correct e.e_sem_env fuel false a2';
    let (a2_, res) = rewrite_group fuel false a2' in
    if res
    then
      let res2 = array_group_included e close a1 (a2_) in
      if RFailure? res2
      then begin
        match array_group_disjoint e false false a1 g2 with
        | RSuccess _ -> array_group_included e close a1 a2r
        | res -> res
      end
      else res2
    else ROutOfFuel
  | (_, (GZeroOrMore g1, a1r)), (a2, (GZeroOrMore g2, a2r)) ->
    let res1 = array_group_included e false g1 g2 in
    if RSuccess? res1
    then begin
      Classical.move_requires
        (Spec.array_group_included_zero_or_more_l
          (array_group_sem e.e_sem_env g1)
          (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1r) close)
          (array_group_sem e.e_sem_env g2)
        )
        (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2r) close);
      array_group_included e close a1r a2
    end
    else res1
  | (_, (GZeroOrMore _, _)), _ ->
    RFailure "array_group_included: GZeroOrMore"
  | (_, (GElem _ _ t1, a1r)), (_, (GElem _ _ t2, a2r)) ->
    let res1 = typ_included e t1 t2 in
    if RSuccess? res1
    then array_group_included e close a1r a2r
    else res1
  | (a1, _), (a2, (GZeroOrMore g2, a2r)) ->
    let a2' = GConcat g2 a2 in
    rewrite_group_correct e.e_sem_env fuel false a2';
    let (a2_, res) = rewrite_group fuel false a2' in
    if res
    then
    begin match array_group_included e close a1 (a2_) with
    | RFailure _ ->
      begin match array_group_disjoint e false false a1 g2 with
      | RSuccess _ ->
        Classical.move_requires
          (Spec.array_group_included_zero_or_more_2
            (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close)
            (array_group_sem e.e_sem_env g2)
          )
          (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2r) close);
        array_group_included e close a1 a2r
      | res -> res
      end
    | res ->
      Classical.move_requires
        (Spec.array_group_included_zero_or_more_1
          (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close)
          (array_group_sem e.e_sem_env g2)
        )
        (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2r) close);
      res
    end
    else ROutOfFuel
  | (_, (GElem _ _ _, _)), _ ->
    RFailure "array_group_included: GArrayElem"
  end

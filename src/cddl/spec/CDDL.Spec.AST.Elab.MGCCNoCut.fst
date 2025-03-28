module CDDL.Spec.AST.Elab.MGCCNoCut
include CDDL.Spec.AST.Elab.Base
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

#push-options "--z3rlimit 64 --split_queries always --query_stats --fuel 4 --ifuel 8"

#restart-solver
let map_group_choice_compatible_no_cut
  (map_group_choice_compatible_no_cut: map_group_choice_compatible_no_cut_t)
  (typ_disjoint: typ_disjoint_t)
  (typ_diff_disjoint: typ_diff_disjoint_t)
  (fuel: nat) // to unfold definitions
: map_group_choice_compatible_no_cut_t
= fun env #g1 s1 #g2 s2 ->
  match s1 with
  | WfMLiteral false key value _ ->
    Spec.map_group_choice_compatible_no_cut_match_item_for_no_cut
      (eval_literal key)
      (typ_sem env.e_sem_env value)
      (elab_map_group_sem env.e_sem_env g2);
    RSuccess ()
  | WfMZeroOrMore key key_except value _ _ _ ->
    Spec.map_group_choice_compatible_no_cut_zero_or_more_match_item_left
      (Util.andp (typ_sem env.e_sem_env key) (Util.notp (typ_sem env.e_sem_env key_except)))
      (typ_sem env.e_sem_env value)
      (elab_map_group_sem env.e_sem_env g2);
    RSuccess ()
  | WfMChoice g1l s1l g1r s1r ->
    let res1 = map_group_choice_compatible_no_cut env s1l s2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = map_group_choice_compatible_no_cut env s1r s2 in
    if not (RSuccess? res2)
    then res2
    else begin
      Spec.map_group_choice_compatible_no_cut_choice_left
        (elab_map_group_sem env.e_sem_env g1l)
        (elab_map_group_sem env.e_sem_env g1r)
        (elab_map_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | WfMZeroOrOne g s ->
    let res1 = map_group_choice_compatible_no_cut env s s2 in
    if not (RSuccess? res1)
    then res1
    else begin
      Spec.map_group_choice_compatible_no_cut_zero_or_one_left
        (elab_map_group_sem env.e_sem_env g)
        (elab_map_group_sem env.e_sem_env g2);
      RSuccess ()
    end
  | WfMLiteral _ key value _ ->
    begin match map_group_footprint typ_disjoint fuel env g2 with
    | RSuccess (t2, t_ex2) ->
      let res1 = typ_disjoint_from_diff typ_diff_disjoint env (TElem (ELiteral key)) t2 t_ex2 in
      if not (RSuccess? res1)
      then res1
      else begin
        Spec.map_group_choice_compatible_no_cut_match_item_for_cut
          (eval_literal key)
          (typ_sem env.e_sem_env value)
          (elab_map_group_sem env.e_sem_env g2)
          (typ_sem env.e_sem_env t2 `Util.andp` Util.notp (typ_sem env.e_sem_env t_ex2));
        RSuccess ()
      end
    | res -> coerce_failure res
    end
  | WfMConcat g1l s1l g1r s1r ->
    let res1 = map_group_choice_compatible_no_cut env s1l s2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = map_group_choice_compatible_no_cut env s1r s2 in
    if not (RSuccess? res2)
    then res2
    else begin
      Spec.map_group_choice_compatible_no_cut_concat_left
        (elab_map_group_sem env.e_sem_env g1l)
        ((spec_map_group_footprint env.e_sem_env g1l))
        (elab_map_group_sem env.e_sem_env g1r)
        ((spec_map_group_footprint env.e_sem_env g1r))
        (elab_map_group_sem env.e_sem_env g2);
      RSuccess ()
    end

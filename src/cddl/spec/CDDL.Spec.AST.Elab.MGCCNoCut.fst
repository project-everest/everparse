module CDDL.Spec.AST.Elab.MGCCNoCut
include CDDL.Spec.AST.Elab.Base
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

#push-options "--z3rlimit 32"

#restart-solver
[@@"opaque_to_smt"]
let map_group_choice_compatible_no_cut
  (map_group_choice_compatible_no_cut: map_group_choice_compatible_no_cut_t)
  (typ_disjoint: typ_disjoint_t)
  (typ_included: typ_included_t)
//  (typ_diff_disjoint: typ_diff_disjoint_t)
  (fuel: nat) // to unfold definitions
: map_group_choice_compatible_no_cut_t
= fun env #g1 s1 #g2 s2 ->
  match s1 with
  | WfMNop _ -> RSuccess ()
  | WfMLiteral false _ key value _ ->
    Spec.map_group_choice_compatible_no_cut_match_item_for_no_cut
      (eval_literal key)
      (typ_sem env.e_sem_env value)
      (elab_map_group_sem env.e_sem_env g2);
    RSuccess ()
  | WfMZeroOrMore key value except _ _ _ ->
    Spec.map_group_choice_compatible_no_cut_filtered_table
      (typ_sem env.e_sem_env key)
      (typ_sem env.e_sem_env value)
      (map_constraint_sem env.e_sem_env except)
      (elab_map_group_sem env.e_sem_env g2);
    RSuccess ()
  | WfMChoice g1l s1l g1r s1r ->
    assert (g1 == MGChoice g1l g1r);
    spec_wf_parse_map_group_choice env.e_sem_env g1l s1l g1r s1r;
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
  | WfMLiteral _cut _ key value _s ->
    begin match map_group_footprint typ_disjoint fuel env g2 with
    | RSuccess te2 ->
      let res1 = map_constraint_disjoint typ_disjoint typ_included env (MCKeyValue (TElem (ELiteral key)) (TElem EAny)) te2 in
      if not (RSuccess? res1)
      then res1
      else begin
        Spec.map_group_choice_compatible_no_cut_match_item_for_no_cut
          (eval_literal key)
          (typ_sem env.e_sem_env value)
          (elab_map_group_sem env.e_sem_env g2);
        Spec.map_group_choice_compatible_no_cut_match_item_for_cut
          (eval_literal key)
          (typ_sem env.e_sem_env value)
          (elab_map_group_sem env.e_sem_env g2)
          (map_constraint_sem env.e_sem_env te2);
        RSuccess ()
      end
    | res -> coerce_failure res
    end
  | WfMConcat g1l s1l g1r s1r ->
    elab_map_group_sem_concat env.e_sem_env g1l g1r;
    let res1 = map_group_choice_compatible_no_cut env s1l s2 in
    if not (RSuccess? res1)
    then res1
    else let res2 = map_group_choice_compatible_no_cut env s1r s2 in
    if not (RSuccess? res2)
    then res2
    else
    begin
      Spec.map_group_choice_compatible_no_cut_concat_left
        (elab_map_group_sem env.e_sem_env g1l)
        ((spec_map_group_footprint env.e_sem_env g1l))
        (elab_map_group_sem env.e_sem_env g1r)
        ((spec_map_group_footprint env.e_sem_env g1r))
        (elab_map_group_sem env.e_sem_env g2);
      RSuccess ()
    end

#pop-options

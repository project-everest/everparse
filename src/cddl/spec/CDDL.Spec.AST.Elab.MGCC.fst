module CDDL.Spec.AST.Elab.MGCC
include CDDL.Spec.AST.Elab.Base
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

#push-options "--z3rlimit 128 --split_queries always --query_stats --fuel 4 --ifuel 8"

#restart-solver
let rec map_group_choice_compatible'
  (map_group_choice_compatible_no_cut: map_group_choice_compatible_no_cut_t)
  (typ_disjoint: typ_disjoint_t)
  (typ_diff_disjoint: typ_diff_disjoint_t)
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (#g1: elab_map_group)
  (s1: ast0_wf_parse_map_group g1)
  (#g2: elab_map_group)
  (s2: ast0_wf_parse_map_group g2)
  (sq: squash (
    spec_wf_parse_map_group env.e_sem_env _ s1 /\
    spec_wf_parse_map_group env.e_sem_env _ s2
  ))
: Tot (r: result unit & squash (map_group_choice_compatible'_postcond env.e_sem_env s1 s2 r))
  (decreases fuel)
= if fuel = 0
  then (| ROutOfFuel, () |)
  else let fuel' : nat = fuel - 1 in
  let map_group_choice_compatible' = map_group_choice_compatible' map_group_choice_compatible_no_cut typ_disjoint typ_diff_disjoint fuel' in
  match s1 with
  | WfMZeroOrMore _ _ _ _ _ _ ->
    (| RFailure "map_group_choice_compatible: GZeroOrMore never fails", () |)
  | WfMZeroOrOne _ _ ->
    (| RFailure "map_group_choice_compatible: GZeroOrOne always succeeds or cuts, but never fails", () |)
  | WfMChoice g1l s1l g1r s1r ->
    let (| res1, _ |) = map_group_choice_compatible' env s1l s2 () in
    if not (RSuccess? res1)
    then (| res1, () |)
    else let (| res2, _ |) = map_group_choice_compatible' env s1r s2 () in
    if not (RSuccess? res2)
    then (| res2, () |)
    else begin
      Spec.map_group_choice_compatible_choice_left
        (elab_map_group_sem env.e_sem_env g1l)
        (elab_map_group_sem env.e_sem_env g1r)
        (elab_map_group_sem env.e_sem_env g2);
      (| RSuccess (), () |)
    end
  | _ ->
    begin match s2 with
    | WfMChoice g2l s2l g2r s2r ->
      let (| res1, _ |) = map_group_choice_compatible' env s1 s2l () in
      if not (RSuccess? res1)
      then (| res1, () |)
      else let (| res2, _ |) = map_group_choice_compatible' env s1 s2r () in
      if not (RSuccess? res2)
      then (| res2, () |)
      else begin
        Spec.map_group_choice_compatible_choice_right
          (elab_map_group_sem env.e_sem_env g1)
          (elab_map_group_sem env.e_sem_env g2l)
          (elab_map_group_sem env.e_sem_env g2r);
        (| RSuccess (), () |)
      end
    | _ ->
      begin match s1 with
      | WfMConcat g1l s1l g1r s1r ->
        let (| r1l, _ |) = map_group_choice_compatible' env s1l s2 () in
        begin match r1l with
        | RSuccess _ ->
          Spec.map_group_choice_compatible_concat_left
            (elab_map_group_sem env.e_sem_env g1l)
            ((spec_map_group_footprint env.e_sem_env g1l))
            (elab_map_group_sem env.e_sem_env g1r)
            ((spec_map_group_footprint env.e_sem_env g1r))
            (elab_map_group_sem env.e_sem_env g2);
          (| RSuccess (), () |)
        | ROutOfFuel -> (| ROutOfFuel, () |)
        | RFailure _ ->
          let res1 = map_group_choice_compatible_no_cut env s1l s2 in
          if not (RSuccess? res1)
          then (| res1, () |)
          else let (| res2, _ |) = map_group_choice_compatible' env s1r s2 () in
          if not (RSuccess? res2)
          then (| res2,  () |)
          else begin
            Spec.map_group_choice_compatible_concat_left
              (elab_map_group_sem env.e_sem_env g1l)
              ((spec_map_group_footprint env.e_sem_env g1l))
              (elab_map_group_sem env.e_sem_env g1r)
              ((spec_map_group_footprint env.e_sem_env g1r))
              (elab_map_group_sem env.e_sem_env g2);
            (| RSuccess (), () |)
          end
        end
      | WfMLiteral cut key value _ ->
        begin match map_group_footprint typ_disjoint fuel env g2 with
        | RSuccess (t2, t_ex2) ->
          begin match typ_disjoint_from_diff typ_diff_disjoint env (TElem (ELiteral key)) t2 t_ex2 with
          | RSuccess _ ->
            Spec.map_group_choice_compatible_match_item_for cut (eval_literal key) (typ_sem env.e_sem_env value) (elab_map_group_sem env.e_sem_env g2) (typ_sem env.e_sem_env t2 `Util.andp` Util.notp (typ_sem env.e_sem_env t_ex2));
            (| RSuccess (), () |)
          | ROutOfFuel -> (| ROutOfFuel, () |)
          | RFailure _ ->
            if cut
            then (| RFailure "map_group_choice_compatible: GMapElem true (TElem (ELiteral key)) value, not disjoint", () |)
            else begin match s2 with
            | WfMConcat g2l s2l g2r s2r ->
              let (| res1, _ |) = map_group_choice_compatible' env s1 s2l () in
              if not (RSuccess? res1)
              then (| res1, () |)
              else let (| res2, _ |) = map_group_choice_compatible' env s1 s2r () in
              if not (RSuccess? res2)
              then (| res2, () |)
              else begin
                Spec.map_group_choice_compatible_match_item_for_concat_right
                  (eval_literal key)
                  (typ_sem env.e_sem_env value)
                  (elab_map_group_sem env.e_sem_env g2l)
                  (elab_map_group_sem env.e_sem_env g2r)
                  ((spec_map_group_footprint env.e_sem_env g2l))
                  ((spec_map_group_footprint env.e_sem_env g2r));
                (| RSuccess (), () |)
              end
            | WfMZeroOrOne g s ->
              let (| res1, _ |) = map_group_choice_compatible' env s1 s () in
              if not (RSuccess? res1)
              then (| res1, () |)
              else begin
                Spec.map_group_choice_compatible_match_item_for_zero_or_one_right cut (eval_literal key) (typ_sem env.e_sem_env value) (elab_map_group_sem env.e_sem_env g);
                (| RSuccess (), () |)
              end
            | WfMLiteral cut2 key2 value2 _ ->
              if key <> key2
              then begin // this case should already have been eliminated by the typ_disjoint test above
                Classical.forall_intro_2 byte_seq_of_ascii_string_diff;
                Spec.map_group_choice_compatible_match_item_for cut (eval_literal key) (typ_sem env.e_sem_env value) (elab_map_group_sem env.e_sem_env g2) (Spec.t_literal (eval_literal key2));
                (| RSuccess (), () |)
              end else begin
                let res1 = typ_disjoint env value value2 in
                if not (RSuccess? res1)
                then (| res1, () |)
                else begin
                  Spec.map_group_choice_compatible_match_item_for_same
                    (eval_literal key)
                    (typ_sem env.e_sem_env value)
                    (typ_sem env.e_sem_env value2)
                    cut2;
                  (| RSuccess (), () |)
                end
              end
            | WfMZeroOrMore _ _ _ _ _ _ -> (| RFailure "map_group_choice_compatible: GZeroOrMore right, not disjoint", () |)
            end
          end
        | res -> (| coerce_failure res, () |)
        end
      end
    end

#pop-options

let map_group_choice_compatible
  (map_group_choice_compatible_no_cut: map_group_choice_compatible_no_cut_t)
  (typ_disjoint: typ_disjoint_t)
  (typ_diff_disjoint: typ_diff_disjoint_t)
  (fuel: nat) // to unfold definitions
  (env: ast_env)
  (#g1: elab_map_group)
  (s1: ast0_wf_parse_map_group g1)
  (#g2: elab_map_group)
  (s2: ast0_wf_parse_map_group g2)
: Pure (result unit)
    (requires (
      spec_wf_parse_map_group env.e_sem_env _ s1 /\
      spec_wf_parse_map_group env.e_sem_env _ s2
    ))
    (ensures fun r -> (map_group_choice_compatible'_postcond env.e_sem_env s1 s2 r))
= let (| res, _ |) = map_group_choice_compatible' map_group_choice_compatible_no_cut typ_disjoint typ_diff_disjoint fuel env s1 s2 () in
  res

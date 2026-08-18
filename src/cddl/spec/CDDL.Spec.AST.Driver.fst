module CDDL.Spec.AST.Driver
include CDDL.Spec.AST.Elab

let mk_GConcat (g1 g2: group) : Tot group =
  match g1 with
  | GNop -> g2
  | _ ->
    begin match g2 with
    | GNop -> g1
    | _ -> GConcat g1 g2
    end

let mk_GChoice (g1 g2: group) : Tot group =
  match g1 with
  | GAlwaysFalse -> g2
  | _ ->
    begin match g2 with
    | GAlwaysFalse -> g1
    | _ -> GChoice g1 g2
    end

unfold
let ast_env_extend_typ_with_pre
  (e: ast_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t)
: GTot prop
=
    e.e_sem_env.se_bound new_name == None /\
    typ_bounded e.e_sem_env.se_bound t /\
    bounded_wf_typ (extend_name_env e.e_sem_env.se_bound new_name NType) t t_wf /\
    spec_wf_typ (ast_env_extend_gen e new_name NType t).e_sem_env true t t_wf

let check_name (env: name_env) (name: string) (k: name_env_elem) : Tot (option name_env) =
  match env name with
  | None -> Some (extend_name_env env name k)
  | Some k' ->
    if k = k'
    then Some env
    else None

open FStar.Mul

[@@PpxDerivingShow]
type topological_sort_result =
  result program

let rec topological_sort'
  (bound: Ghost.erased pos)
  (env: ast_env)
  (res: list (string & decl))
  (accu: list (string & decl))
  (l: list (string & decl) { List.Tot.length accu + List.Tot.length l < bound })
: Tot (r: topological_sort_result { ~ (ROutOfFuel? r) })
  (decreases ((List.Tot.length l + List.Tot.length accu) * bound + List.Tot.length l))
= match l with
  | [] ->
    begin match accu with
    | [] -> RSuccess (List.Tot.rev res)
    | (new_name, _) :: _ -> RFailure ("topological_sort' : " ^ new_name ^  " contains an undefined name")
    end
  | elt :: q ->
    let (new_name, tg) = elt in
    begin match env.e_sem_env.se_bound new_name with
    | Some _ -> RFailure ("topological sort': name "^ new_name ^" already defined. Definitions already processed: " ^  CDDL.Spec.AST.Print.program_to_string res ^ ". Definitions remaining to process: " ^ CDDL.Spec.AST.Print.program_to_string (elt :: List.Tot.rev_acc accu q))
    | _ ->
      List.Tot.rev_acc_length accu q;
      begin match tg with
      | DGroup g ->
        if group_bounded (env.e_sem_env.se_bound) g
        then
          let env' = ast_env_extend_gen env new_name NGroup g in
          topological_sort' bound env' (elt :: res) [] (List.Tot.rev_acc accu q)
        else
          topological_sort' bound env res (elt :: accu) q
      | DType t ->
        if typ_bounded (env.e_sem_env.se_bound) t
        then
          let env' = ast_env_extend_gen env new_name NType t in
          topological_sort' bound env' (elt :: res) [] (List.Tot.rev_acc accu q)
        else
          topological_sort' bound env res (elt :: accu) q
      end
    end

let prelude_list = [
    ("bool", DType (TElem EBool));
    ("everparse-no-match", DType (TElem EAlwaysFalse))
  ]

let topological_sort
  (l: list (string & decl))
: topological_sort_result
= topological_sort' (List.Tot.length l + 3) empty_ast_env [] [] (List.Tot.append prelude_list l)

let topological_sort_as_option
  (l: list (string & decl))
= match topological_sort l with
  | RSuccess res -> Some res
  | _ -> None

let rec elab_list_tot
  (fuel: nat)
  (env: wf_ast_env)
  (l: list (string & decl))
: Tot (result wf_ast_env)
  (decreases l)
= match l with
  | [] ->
      RSuccess env
  | elt :: q ->
    let (new_name, tg) = elt in
    begin match env.e_sem_env.se_bound new_name with
    | Some _ ->
      RFailure (new_name ^ " already in use")
    | _ ->
      begin match tg with
      | DGroup t ->
        if group_bounded (env.e_sem_env.se_bound) t
        then begin
          group_bounded_incr (env.e_sem_env.se_bound) (extend_name_env env.e_sem_env.se_bound new_name NGroup) t;
          let env' = wf_ast_env_extend_group env new_name t () () in
          elab_list_tot fuel env' q
        end else begin
          RFailure "group not bounded, this should not happen if you use topological_sort"
        end
      | DType t ->
        if typ_bounded (env.e_sem_env.se_bound) t
        then
            let res = mk_wf_typ_bounded fuel env t in
            match res with
            | RSuccess t_wf ->
              assert (bounded_wf_typ (env.e_sem_env.se_bound) t t_wf);
              bounded_wf_typ_incr (env.e_sem_env.se_bound) (extend_name_env env.e_sem_env.se_bound new_name NType) t t_wf;
              let env' = wf_ast_env_extend_typ_with env new_name t t_wf in
              elab_list_tot fuel env' q
            | res -> coerce_failure res
        else begin
          RFailure "type not bounded, this should not happen if you use topological_sort"
        end
      end
    end

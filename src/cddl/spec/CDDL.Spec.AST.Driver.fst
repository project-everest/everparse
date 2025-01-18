module CDDL.Spec.AST.Driver
include CDDL.Spec.AST.Print

open FStar.All
open FStar.IO

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

let print_endline (s: string) : ML unit =
  print_string s;
  print_newline ()

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
    spec_wf_typ (ast_env_extend_gen e new_name NType t).e_sem_env t t_wf

[@@plugin]
type decl =
| DType of typ
| DGroup of group

let check_name (env: name_env) (name: string) (k: name_env_elem) : Tot (option name_env) =
  match env name with
  | None -> Some (extend_name_env env name k)
  | Some k' ->
    if k = k'
    then Some env
    else None

let rec elab_list'
  (fuel: nat)
  (env: ast_env)
  (accu: list (string & decl))
  (l: list (string & decl))
: ML (result ast_env)
= match l with
  | [] ->
    if Nil? accu
    then begin
      print_endline "Done, no definitions left";
      RSuccess env
    end else begin
      let msg = "Some definitions left, but none suitable to choose. They are likely all using undefined types or groups." in
      print_endline ("ERROR: " ^ msg);
      RFailure msg
    end
  | elt :: q ->
    let (new_name, tg) = elt in
    begin match env.e_sem_env.se_bound new_name with
    | Some _ ->
      print_endline "ERROR: Name already in use";
      RFailure (new_name ^ " already in use")
    | _ ->
      begin match tg with
      | DGroup t ->
        print_string "NOT elaborating group: ";
        print_endline new_name;
        print_endline (group_to_string t);
        if group_bounded (env.e_sem_env.se_bound) t
        then begin
          print_endline "Extending the environment";
          group_bounded_incr (env.e_sem_env.se_bound) (extend_name_env env.e_sem_env.se_bound new_name NGroup) t;
          let env' = ast_env_extend_gen env new_name NGroup t in
          elab_list' fuel env' [] (List.Tot.rev_acc accu q)
        end else begin
          print_endline "Group uses undefined types/groups. Choosing another one";
          elab_list' fuel env (elt :: accu) q
        end
      | DType t ->
        print_string "Elaborating type: ";
        print_endline new_name;
        print_endline (typ_to_string t);
        if typ_bounded (env.e_sem_env.se_bound) t
        then
          let rec aux (fuel': nat) : ML (result ast_env) =
            print_endline "Rewritten as:";
            print_endline (typ_to_string (fst (rewrite_typ fuel' t)));
            let res = mk_wf_typ_bounded fuel' env t in
            print_endline "Result:";
            print_endline (ast0_wf_typ_result_to_string _ res);
            match res with
            | RFailure s ->
              print_endline "Failure! Aborting";
              RFailure s
            | ROutOfFuel ->
              print_endline "Out of fuel! Trying to increase fuel";
              aux (fuel' + fuel')
            | RSuccess t_wf ->
              print_endline "Success! Extending the environment";
              assert (bounded_wf_typ (env.e_sem_env.se_bound) t t_wf);
              bounded_wf_typ_incr (env.e_sem_env.se_bound) (extend_name_env env.e_sem_env.se_bound new_name NType) t t_wf;
              assert (ast_env_extend_typ_with_pre env new_name t t_wf); // FIXME: WHY WHY WHY?
              let env' = ast_env_extend_typ_with env new_name t t_wf in
              elab_list' fuel' env' [] (List.Tot.rev_acc accu q)
          in
          aux fuel
        else begin
          print_endline "Type uses undefined types/groups. Choosing another one";
          elab_list' fuel env (elt :: accu) q
        end
      end
    end

let prelude_ast_env : ast_env =
  let env = empty_ast_env in
  let env = ast_env_extend_typ_with env "bool" (TElem EBool) (WfTElem EBool) in
  assert_norm (ast_env_extend_typ_with_pre env "everparse-no-match" (TElem EAlwaysFalse) (WfTElem EAlwaysFalse)); // FIXME: WHY WHY WHY?
  let env = ast_env_extend_typ_with env "everparse-no-match" (TElem EAlwaysFalse) (WfTElem EAlwaysFalse) in
  env

let elab_list
  (l: list (string & decl))
: ML (result ast_env)
= elab_list' 1 prelude_ast_env [] l

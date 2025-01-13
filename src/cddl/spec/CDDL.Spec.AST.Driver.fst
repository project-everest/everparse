module CDDL.Spec.AST.Driver
include CDDL.Spec.AST.Print

open FStar.All
open FStar.IO

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

let rec elab_list'
  (fuel: nat)
  (env: ast_env)
  (l: list (string & typ))
: ML (result ast_env)
= match l with
  | [] ->
    print_endline "Done, no definitions left";
    RSuccess env
  | (new_name, t) :: q ->
    print_string "Elaborating type: ";
    print_endline new_name;
    print_endline (typ_to_string t);
    begin match env.e_sem_env.se_bound new_name with
    | Some _ ->
      print_endline "ERROR: Name already in use";
      RFailure (new_name ^ " already in use")
    | _ ->
      let rec aux (fuel': nat) : ML (result ast_env) =
        let res = mk_wf_typ' fuel' env t in
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
          elab_list' fuel' env' q
      in
      aux fuel
    end

let elab_list
  (l: list (string & typ))
: ML (result ast_env)
= elab_list' 1 empty_ast_env l

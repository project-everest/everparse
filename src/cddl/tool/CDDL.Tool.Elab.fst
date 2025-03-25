module CDDL.Tool.Elab
include CDDL.Tool.Print
include CDDL.Spec.AST.Driver

open FStar.All
open FStar.IO

let print_endline (s: string) : ML unit =
  print_string s;
  print_newline ()

let rec elab_list'
  (fuel: nat)
  (env: wf_ast_env)
  (accu: list (string & decl))
  (l: list (string & decl))
: ML (result wf_ast_env)
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
          let env' = wf_ast_env_extend_group env new_name t () () in
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
          let rec aux (fuel': nat) : ML (result wf_ast_env) =
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
              let env' = wf_ast_env_extend_typ_with env new_name t t_wf in
              elab_list' fuel' env' [] (List.Tot.rev_acc accu q)
          in
          aux fuel
        else begin
          print_endline "Type uses undefined types/groups. Choosing another one";
          elab_list' fuel env (elt :: accu) q
        end
      end
    end

let elab_list
  (l: list (string & decl))
: ML (result wf_ast_env)
= elab_list' 1 empty_ast_env [] (List.Tot.append prelude_list l)

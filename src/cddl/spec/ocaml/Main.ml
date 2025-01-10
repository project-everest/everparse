type result = unit CDDL_Spec_AST_Base.ast0_wf_typ CDDL_Spec_AST_Elab.result [@@deriving show]

let fuel : Prims.nat = Prims.of_int 3000

let rec elab_list
  (env: CDDL_Spec_AST_Base.ast_env)
  (l: (string * CDDL_Spec_AST_Base.typ) list)
: CDDL_Spec_AST_Base.ast_env CDDL_Spec_AST_Elab.result
= match l with
  | [] ->
    print_endline "Done, no definitions left";
    CDDL_Spec_AST_Elab.RSuccess env
  | (new_name, t) :: q ->
    print_endline "Elaborating type: ";
    print_endline (CDDL_Spec_AST_Base.show_typ t);
    let res : result = CDDL_Spec_AST_Elab.mk_wf_typ' fuel env t in
    print_endline "Result:";
    print_endline (show_result res);
    begin match res  with
    | CDDL_Spec_AST_Elab.RFailure s ->
      print_endline "Failure, aborting";
      CDDL_Spec_AST_Elab.RFailure s
    | CDDL_Spec_AST_Elab.RSuccess t_wf ->
      print_endline "Success, extending the environment";
      let env' = CDDL_Spec_AST_Base.wf_ast_env_extend_typ_with_weak env new_name t t_wf in
      elab_list env' q
    end

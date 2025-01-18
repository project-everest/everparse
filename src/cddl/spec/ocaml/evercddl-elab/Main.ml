let elab_list = CDDL_Spec_AST_Driver.elab_list

let env : CDDL_Spec_AST_Base.name_env ref = ref CDDL_Spec_AST_Base.empty_name_env

let read_buf : (string * CDDL_Spec_AST_Driver.decl) list ref = ref []

let process_file filename =
  match ParseFromFile.parse !env filename with
  | None -> print_endline "Syntax error"; exit 1
  | Some (env', l) -> env := env'; read_buf := List.append l !read_buf

let _ =
  Arg.parse [] process_file "Usage: %0 [file1 ...]";
  begin match elab_list !read_buf with
  | CDDL_Spec_AST_Elab.RSuccess env' ->
     print_endline "Success!"
  | CDDL_Spec_AST_Elab.RFailure msg ->
     print_endline ("Failure: " ^ msg);
     exit 2
  | CDDL_Spec_AST_Elab.ROutOfFuel ->
     print_endline "Out of fuel! This should not happen";
     exit 3
  end

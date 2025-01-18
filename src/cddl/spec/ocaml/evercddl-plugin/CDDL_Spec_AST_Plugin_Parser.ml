let parse filename = match ParseFromFile.parse CDDL_Spec_AST_Base.empty_name_env filename with
  | None -> None
  | Some (_, l) -> Some l

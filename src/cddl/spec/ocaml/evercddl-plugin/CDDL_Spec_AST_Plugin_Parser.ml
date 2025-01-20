let parse_one env filename =
  try
    ParseFromFile.parse env filename
  with _ -> None

let rec parse' (env, l) = function
  | [] -> Some (env, l)
  | a :: q ->
     begin match parse_one env a with
     | Some (env', l_) ->
        parse' (env', List.append l l_) q
     | None -> None
     end

let parse l = match parse' (CDDL_Spec_AST_Base.empty_name_env, []) l with
  | None -> None
  | Some (_, res) -> Some res

let parse (env: CDDLParser.state) filename =
  let ch = open_in filename in
  let lexbuf = Lexing.from_channel ch in
  let buf : (Tokens.token, CDDLParser.state) TokenBuffer.t = TokenBuffer.create (fun _ -> CDDLLexer.token lexbuf) env in
  let p = CDDLParser.cddl () in
  let res = p buf in
  close_in ch;
  res

let parse_one env filename =
  try
    parse env filename
  with _ -> None

let rec parse' (env, l) = function
  | [] -> Some (env, l)
  | a :: q ->
     begin match parse_one env a with
     | Some (env', l_) ->
        parse' (env', List.append l l_) q
     | None -> None
     end

let parse_from_files l = match parse' (CDDL_Spec_AST_Base.empty_name_env, []) l with
  | None -> None
  | Some (_, res) -> Some res

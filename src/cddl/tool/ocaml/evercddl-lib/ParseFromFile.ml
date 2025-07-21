let parse (env: CDDLParser.state) filename =
  let ch = open_in filename in
  let lexbuf = Lexing.from_channel ch in
  let buf : (Tokens.token, CDDLParser.state) TokenBuffer.t = TokenBuffer.create (fun _ -> CDDLLexer.token lexbuf) env in
  let p = CDDLParser.cddl () in
  let res = p buf (fun x -> Some x) in
  close_in ch;
  res

let parse_one env filename =
  try
    parse env filename
  with e ->
    print_endline (Printexc.to_string e);
    None

let rec parse' env = function
  | [] -> Some env
  | a :: q ->
     begin match parse_one env a with
     | Some (env') ->
        parse' env' q
     | None -> None
     end

let empty_env = {
    CDDLParser.env = CDDL_Spec_AST_Base.empty_name_env;
    sockets = [];
    result = [];
}

let plug_empty_socket
  (st: CDDLParser.state)
  (accu: (string * CDDL_Spec_AST_Base.decl) list)
  (name: string)
= if List.mem_assoc name accu
  then accu
  else
    let def = match st.env name with
    | Some CDDL_Spec_AST_Base.NType -> CDDL_Spec_AST_Base.DType (CDDL_Spec_AST_Base.TElem CDDL_Spec_AST_Base.EAlwaysFalse)
    | Some CDDL_Spec_AST_Base.NGroup -> CDDL_Spec_AST_Base.DGroup CDDL_Spec_AST_Base.GAlwaysFalse
    | _ -> failwith "plug_empty_socket: this should not happen. Please report"
    in
    (name, def) :: accu

let plug_empty_sockets
  (st: CDDLParser.state)
  (l: (string * CDDL_Spec_AST_Base.decl) list)
= List.fold_left (plug_empty_socket st) l st.sockets

let parse_from_files l = match parse' empty_env l with
  | None -> None
  | Some env -> Some (plug_empty_sockets env env.result)

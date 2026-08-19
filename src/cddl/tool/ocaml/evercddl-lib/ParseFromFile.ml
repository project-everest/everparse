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
    CDDLParser.sockets = [];
    result = [];
}

let rec solve_names
  (solved: (string * CDDL_Spec_AST_Base.decl) list)
  (unknown: (string * CDDL_Spec_AST_Base.decl CDDLParser.thing_or_name) list)
= function
  | [] ->
    begin match unknown with
    | [] -> List.rev solved
    | (a, CDDLParser.Name b) :: _ -> failwith ("solve_names: definition `" ^ a ^ " = " ^ b ^ "` has not been solved")
    | (_, _) :: _ -> failwith ("solve_names: this should not happen")
    end
  | (a, CDDLParser.Thing d) :: q ->
     solve_names ((a, d) :: solved) [] (List.rev_append unknown q)
  | ((a, CDDLParser.Name n) as x) :: q ->
    begin match List.assoc_opt n solved with
    | Some (DType _) -> solve_names ((a, DType (TDef n)) :: solved) [] (List.rev_append unknown q)
    | Some (DGroup _) -> solve_names ((a, DGroup (GDef n)) :: solved) [] (List.rev_append unknown q)
    | None -> solve_names solved (x :: unknown) q
    end

let plug_empty_socket
  (accu: (string * CDDL_Spec_AST_Base.decl) list)
  (name: (string * CDDLParser.id_kind))
= let (n, k) = name in
  if List.mem_assoc n accu
  then accu
  else match k with
  | Regular -> accu
  | SocketType -> (n, CDDL_Spec_AST_Base.DType (CDDL_Spec_AST_Base.TElem CDDL_Spec_AST_Base.EAlwaysFalse)) :: accu
  | SocketGroup -> (n, CDDL_Spec_AST_Base.DGroup CDDL_Spec_AST_Base.GAlwaysFalse) :: accu

let plug_empty_sockets
  (st: CDDLParser.state)
  (l: (string * CDDL_Spec_AST_Base.decl) list)
= List.fold_left (plug_empty_socket) l st.sockets

let parse_from_files l = match parse' empty_env l with
  | None -> None
  | Some env -> Some (plug_empty_sockets env (solve_names [] [] env.result))

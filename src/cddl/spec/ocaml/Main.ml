let elab_list = CDDL_Spec_AST_Driver.elab_list

let parse filename =
  let ch = open_in filename in
  let lexbuf = Lexing.from_channel ch in
  let res =
    try
      Some (Parser.cddl Lexer.token lexbuf)
    with e ->
      print_endline "Syntax error";
      None
  in
  close_in ch;
  res

let process_file filename =
  match parse filename with
  | None -> ()
  | Some l -> ignore (elab_list l)

let _ =
  Arg.parse [] process_file "Usage: %0 [file1 ...]"

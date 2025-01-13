let elab_list = CDDL_Spec_AST_Driver.elab_list

let print_position filename outx lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" filename
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error filename lexbuf =
  Parser2.cddl () lexbuf

let parse filename =
  let ch = open_in filename in
  let lexbuf = Lexing.from_channel ch in
  let buf = TokenBuffer.create (fun _ -> Lexer.token lexbuf) in
  let res = parse_with_error filename buf in
  close_in ch;
  res

let process_file filename =
  match parse filename with
  | None -> print_endline "Syntax error"
  | Some l -> ignore (elab_list l)

let _ =
  Arg.parse [] process_file "Usage: %0 [file1 ...]"

let elab_list = CDDL_Spec_AST_Driver.elab_list

let print_position filename outx lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" filename
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error filename lexbuf =
  try Some (Parser.cddl Lexer.token lexbuf) with
  | Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" (print_position filename) lexbuf;
    None

let parse filename =
  let ch = open_in filename in
  let lexbuf = Lexing.from_channel ch in
  let res = parse_with_error filename lexbuf in
  close_in ch;
  res

let process_file filename =
  match parse filename with
  | None -> ()
  | Some l -> ignore (elab_list l)

let _ =
  Arg.parse [] process_file "Usage: %0 [file1 ...]"

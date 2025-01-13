let elab_list = CDDL_Spec_AST_Driver.elab_list

let print_position filename outx lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" filename
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error filename lexbuf =
  Parser.cddl () lexbuf

let parse filename =
  let ch = open_in filename in
  let lexbuf = Lexing.from_channel ch in
  let buf = TokenBuffer.create (fun _ -> Lexer.token lexbuf) in
  let res = parse_with_error filename buf in
  close_in ch;
  res

let read_buf : (string * CDDL_Spec_AST_Base.typ) list ref = ref []

let process_file filename =
  match parse filename with
  | None -> print_endline "Syntax error"; exit 1
  | Some l -> read_buf := List.append l !read_buf

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

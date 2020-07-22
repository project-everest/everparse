open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse filename =
  let p = MenhirLib.Convert.Simplified.traditional2revised Parser.prog in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- {
    pos_fname= filename;
    pos_cnum = 0;
    pos_bol = 0;
    pos_lnum = 1 };
  try
    p (fun _ -> Lexer.token lexbuf)
  with e ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit 1

let int_of_string x = Z.of_string x

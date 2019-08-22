open Lexing

let print_position filename outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d"
    filename
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse filename =
  let p = MenhirLib.Convert.Simplified.traditional2revised Parser.prog in
  let lexbuf = Lexing.from_channel (open_in filename) in
  try
    let _ = p (fun _ -> Lexer.token lexbuf) in
    Printf.printf "Parsed\n" (* (Ast.print_expr s) *)
  with e ->
    Printf.fprintf stderr "%a: syntax error\n" (print_position filename) lexbuf;
    raise e

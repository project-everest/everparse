open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let test () =
  let p = MenhirLib.Convert.Simplified.traditional2revised Parser.prog in
  let lexbuf = Lexing.from_string "#define Foo 0" in
  try
    let _ = p (fun _ -> Lexer.token lexbuf) in
    Printf.printf "Parsed\n" (* (Ast.print_expr s) *)
  with e ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    raise e
;;

test ()

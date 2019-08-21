let test () =
  let p = MenhirLib.Convert.Simplified.traditional2revised Parser.prog in
  let lexbuf = Sedlexing.Utf8.from_string "1 || 2 &&   3 = (4 && 5   || 6 && 7 = (9 = 12))" in
  try
    let s = p (fun _ -> Lexer.token lexbuf) in
    Printf.printf "Parsed: %s\n" (Ast.print_expr s)
  with e ->
    print_string "Error!";
    raise e
;;

test ()

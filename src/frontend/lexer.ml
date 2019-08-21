open Sedlexing
open Parser

let space =  [%sedlex.regexp? ' ' | '\t']
let newline =  [%sedlex.regexp? '\r' | "\r\n" | '\n']
let skip = [%sedlex.regexp? space | newline]
let digit = [%sedlex.regexp? '0'..'9']
let integer = [%sedlex.regexp? Plus digit]
(*
 let low_alpha = [%sedlex.regexp? 'a'..'z']
 let up_alpha =  [%sedlex.regexp? 'A'..'Z']
 let any = [%sedlex.regexp? up_alpha | low_alpha | '_' | digit]
let lident = [%sedlex.regexp? low_alpha, Star (any)]
let uident = [%sedlex.regexp? up_alpha, Star (any)]
*)

let locate lb tok =
(*  let s, e = Sedlexing.lexing_positions lb in *)
  tok, Lexing.dummy_pos, Lexing.dummy_pos

let keywords = [
]

let rec token lexbuf =
match%sedlex lexbuf with
| integer ->
    let l = Utf8.lexeme lexbuf in
    locate lexbuf (INT (int_of_string l))
| "=" -> locate lexbuf EQ
| "&&" -> locate lexbuf AND
| "||" -> locate lexbuf OR
| eof -> locate lexbuf EOF
| skip -> token lexbuf
| _ -> print_string "Got:"; print_string (Utf8.lexeme lexbuf); assert false

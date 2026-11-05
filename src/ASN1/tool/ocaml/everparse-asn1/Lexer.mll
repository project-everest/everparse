{
type token =
  | ID of string          (* identifiers and keywords *)
  | NUM of int
  | ASSIGN                (* ::= *)
  | LBRACE | RBRACE | LPAREN | RPAREN | LBRACKET | RBRACKET
  | COMMA | DOTDOT | ELLIPSIS | BAR | MINUS | SEMI | DOT | LT
  | EOF

exception Lex_error of string

let line = ref 1

(* The types named by `--#KEEP-BYTES T1 T2 ...` directives *)
let keep_bytes : string list ref = ref []
}

let letter = ['a'-'z' 'A'-'Z']
let alnum = ['a'-'z' 'A'-'Z' '0'-'9']
let ident = letter (alnum | '-' alnum)*

rule token = parse
  | [' ' '\t' '\r']+ { token lexbuf }
  | '\n' { incr line; token lexbuf }
  | "--#KEEP-BYTES" { keep_line lexbuf }
  | "--" { line_comment lexbuf }
  | "/*" { block_comment 1 lexbuf }
  | "::=" { ASSIGN }
  | "..." { ELLIPSIS }
  | ".." { DOTDOT }
  | '.' { DOT }
  | '{' { LBRACE } | '}' { RBRACE }
  | '(' { LPAREN } | ')' { RPAREN }
  | '[' { LBRACKET } | ']' { RBRACKET }
  | ',' { COMMA } | '|' { BAR } | '-' { MINUS } | ';' { SEMI } | '<' { LT }
  | ['0'-'9']+ as n {
      match int_of_string_opt n with
      | Some i when i < 1 lsl 61 -> NUM i
      | _ -> raise (Lex_error (Printf.sprintf "line %d: number too large: %s" !line n)) }
  | ident as s { ID s }
  | eof { EOF }
  | _ as c { raise (Lex_error (Printf.sprintf "line %d: unexpected character '%c'" !line c)) }

(* X.680 12.6.3: a comment ends at the end of the line or at the next "--" *)
and line_comment = parse
  | '\n' { incr line; token lexbuf }
  | "--" { token lexbuf }
  | eof { EOF }
  | _ { line_comment lexbuf }

(* A `--#KEEP-BYTES` directive: type names up to the end of the line *)
and keep_line = parse
  | [' ' '\t' '\r' ',']+ { keep_line lexbuf }
  | ident as s { keep_bytes := s :: !keep_bytes; keep_line lexbuf }
  | '\n' { incr line; token lexbuf }
  | "--" { token lexbuf }
  | eof { EOF }
  | _ as c { raise (Lex_error (Printf.sprintf "line %d: unexpected character '%c' in --#KEEP-BYTES" !line c)) }

and block_comment depth = parse
  | "*/" { if depth = 1 then token lexbuf else block_comment (depth - 1) lexbuf }
  | "/*" { block_comment (depth + 1) lexbuf }
  | '\n' { incr line; block_comment depth lexbuf }
  | eof { raise (Lex_error "unterminated comment") }
  | _ { block_comment depth lexbuf }

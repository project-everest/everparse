{
type token =
  | ID of string          (* identifiers and keywords *)
  | NUM of int
  | CSTRING of string     (* "text" *)
  | BSTRING of string     (* '0101'B: the digits *)
  | HSTRING of string     (* '0A'H: the digits *)
  | ASSIGN                (* ::= *)
  | LBRACE | RBRACE | LPAREN | RPAREN | LBRACKET | RBRACKET
  | COMMA | DOTDOT | ELLIPSIS | BAR | MINUS | SEMI | DOT | LT | COLON
  | AMP of string         (* &field: a field of an information object class *)
  | AT                    (* @ *)
  | CARET                 (* ^ *)
  | EOF

exception Lex_error of string

let line = ref 1

let count_lines s = String.iter (fun c -> if c = '\n' then incr line) s

(* X.680 12.10, 12.12: white space in bstring and hstring is ignored *)
let strip s =
  count_lines s;
  String.concat "" (String.split_on_char ' ' (String.map (function '\t' | '\n' | '\r' -> ' ' | c -> c) s))

(* The `--#` directive lines (line number, text), in reverse order *)
let directives : (int * string) list ref = ref []
}

let letter = ['a'-'z' 'A'-'Z']
let alnum = ['a'-'z' 'A'-'Z' '0'-'9']
let ident = letter (alnum | '-' alnum)*

rule token = parse
  | [' ' '\t' '\r']+ { token lexbuf }
  | '\n' { incr line; token lexbuf }
  | "--#" ([^ '\n']* as d) { directives := (!line, d) :: !directives; token lexbuf }
  | "--" { line_comment lexbuf }
  | "/*" { block_comment 1 lexbuf }
  | "::=" { ASSIGN }
  | '\'' ([^ '\'']* as b) "'B" {
      let b = strip b in
      if String.exists (fun c -> c <> '0' && c <> '1') b then
        raise (Lex_error (Printf.sprintf "line %d: bad bstring '%s'B" !line b));
      BSTRING b }
  | '\'' ([^ '\'']* as h) "'H" {
      let h = strip h in
      if String.exists (fun c -> not (('0' <= c && c <= '9') || ('A' <= c && c <= 'F'))) h then
        raise (Lex_error (Printf.sprintf "line %d: bad hstring '%s'H" !line h));
      HSTRING h }
  | '"' { cstring (Buffer.create 16) lexbuf }
  | "..." { ELLIPSIS }
  | ".." { DOTDOT }
  | '.' { DOT }
  | '{' { LBRACE } | '}' { RBRACE }
  | '(' { LPAREN } | ')' { RPAREN }
  | '[' { LBRACKET } | ']' { RBRACKET }
  | ':' { COLON }
  | ',' { COMMA } | '|' { BAR } | '-' { MINUS } | ';' { SEMI } | '<' { LT }
  | ['0'-'9']+ as n {
      match int_of_string_opt n with
      | Some i when i < 1 lsl 61 -> NUM i
      | _ -> raise (Lex_error (Printf.sprintf "line %d: number too large: %s" !line n)) }
  | ident as s { ID s }
  | '&' (ident as s) { AMP s }
  | '@' { AT } | '^' { CARET }
  | eof { EOF }
  | _ as c { raise (Lex_error (Printf.sprintf "line %d: unexpected character '%c'" !line c)) }

(* X.680 12.6.3: a comment ends at the end of the line or at the next "--" *)
and line_comment = parse
  | '\n' { incr line; token lexbuf }
  | "--" { token lexbuf }
  | eof { EOF }
  | _ { line_comment lexbuf }

(* X.680 12.14: a doubled quote stands for a quote, and a newline with its surrounding white space is removed *)
and cstring b = parse
  | "\"\"" { Buffer.add_char b '"'; cstring b lexbuf }
  | '"' { CSTRING (Buffer.contents b) }
  | [' ' '\t' '\r']* '\n' [' ' '\t' '\r']* { incr line; cstring b lexbuf }
  | eof { raise (Lex_error "unterminated string") }
  | _ as c { Buffer.add_char b c; cstring b lexbuf }

and block_comment depth = parse
  | "*/" { if depth = 1 then token lexbuf else block_comment (depth - 1) lexbuf }
  | "/*" { block_comment (depth + 1) lexbuf }
  | '\n' { incr line; block_comment depth lexbuf }
  | eof { raise (Lex_error "unterminated comment") }
  | _ { block_comment depth lexbuf }

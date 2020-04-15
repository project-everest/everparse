{
	open Lexing
	open Format

	open Rfc_parser

	exception SyntaxError of string
}

let ospace  = [' ' '\t']*
let space   = [' ' '\t']+
let newln   = "\r" | "\n" | "\r\n"
let int     = ['0'-'9']+
let id      = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '-' '.']*
let hexb    = ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F']
let hex     = '0' 'x' ['0'-'9' 'a'-'f' 'A'-'F']+
let attr    = "/*@" ['a'-'z' 'A'-'Z' '_']+ "*/"

rule read = parse
	| space    { read lexbuf }
	| newln    { new_line lexbuf; read lexbuf }
        | "abstract" { ABSTRACT }
	| "struct" { STRUCT }
	| "enum"   { ENUM }
	| "select" { SELECT }
	| "if"     { IF }
	| "else"   { ELSE }
	| "case"   { CASE }
	| "default" { DEFAULT }
	| ((int | hex) as i) 'u' 'y' { LITERAL (Printf.sprintf "%02x" (int_of_string i)) }
	| ((int | hex) as i) 'u' 's' { LITERAL (Printf.sprintf "%04x" (int_of_string i)) }
	| ((int | hex) as i) 'u' 'l' { LITERAL (Printf.sprintf "%08x" (int_of_string i)) }
	| int as i { INT (int_of_string i) }
	| hex as i { INT (int_of_string i) }
	| '2' '^' (int as pow) '-' (int as sub)
		{ INT (let p, m = int_of_string pow, int_of_string sub in
			    (1 lsl p) - m ) }
	| '2' '^' (int as pow) '+' (int as sub)
		{ INT (let p, m = int_of_string pow, int_of_string sub in
			    (1 lsl p) + m ) }
	| '2' '^' (int as pow) {INT (let p = int_of_string pow in 1 lsl p)}
	| id as i  { TYPE i }
	| '<'      { LT }
	| '>'      { GT }
	| '='      { EQUALS }
	| ';'      { SEMCOL }
	| ':'      { FULCOL }
	| '{'      { LBRACE }
	| '}'      { RBRACE }
	| '['      { LBRACK }
	| ']'      { RBRACK }
	| '('      { LPAREN }
	| ')'      { RPAREN }
  | attr as a{ ATTRIBUTE (String.sub a 3 (String.length a - 5)) }
	| '/' '*'  { comment_start 1 lexbuf }
	| '"'      { string_start "" lexbuf }
	| ','      { COMMA  }
	| '.' '.'  { DOTDOT }
	| eof      { EOF }
	| _        { raise (SyntaxError ("Unexpected " ^ Lexing.lexeme lexbuf)) }

and comment_start depth = parse
	| newln { new_line lexbuf; comment_start depth lexbuf }
	| "*/"  { if depth=1 then read lexbuf else comment_start (depth-1) lexbuf }
	| "/*"  { comment_start (depth+1) lexbuf } (*Nested comments*)
	| eof   { Printf.eprintf "Warning: reached EOF before comment closure\n"; EOF }
	| _     { comment_start depth lexbuf }

and string_start acc = parse
  | "\\\"" {string_start (acc^"\"") lexbuf}
	| "\"" { LITERAL acc }
        | [ ^ '"' '\\' ] as c { string_start (acc^String.make 1 c) lexbuf }

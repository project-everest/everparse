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
let hex     = '0' 'x' ['0'-'9' 'a'-'f' 'A'-'F']+
let attr    = "/*@" ['a'-'z' 'A'-'Z' '_']+ "*/"

rule read = parse
	| space    { read lexbuf }
	| newln    { new_line lexbuf; read lexbuf }
	| "struct" { STRUCT }
	| "enum"   { ENUM }
	| "select" { SELECT }
	| "case"   { CASE }
	| int as i { INT (int_of_string i) }
	| hex as i { INT (int_of_string i) }
	| id as i  { TYPE i }
	| '<'      { RANGE (range_min lexbuf) }
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
	| ','      { COMMA  }
	| '.' '.'  { DOTDOT }
	| eof      { EOF }
	| _        { raise (SyntaxError ("Unexpected " ^ Lexing.lexeme lexbuf)) }

and range_min = parse
		| space {range_min lexbuf}
	| int as min space? '.' '.' { range_max (int_of_string min) lexbuf }
	| _ { raise (SyntaxError ("Invalid range start " ^ Lexing.lexeme lexbuf)) }

and range_max min = parse
	| ospace (int as max) ospace '>' { (min, int_of_string max) }
	| '2' '^' (int as pow) '-' (int as sub) '>'
		{ (min, let p, m = int_of_string pow, int_of_string sub in (1 lsl p) - m ) }
	| _ { raise (SyntaxError ("Invalid range end " ^ Lexing.lexeme lexbuf)) }

and comment_start depth = parse
		| newln { new_line lexbuf; comment_start depth lexbuf }
		| "*/"  { if depth=1 then read lexbuf else comment_start (depth-1) lexbuf }
		| "/*"  { comment_start (depth+1) lexbuf } (*Nested comments*)
		| eof   { Printf.eprintf "Warning: reached EOF before comment closure\n"; EOF }
		| _     { comment_start depth lexbuf }

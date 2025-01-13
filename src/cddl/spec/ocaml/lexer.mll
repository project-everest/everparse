{

open Parser
open CDDL_Spec_AST_Base

}

let digit = ['0'-'9']
let digit1 = ['1'-'9']
let hexdig = digit | "A" | "B" | "C" | "D" | "E" | "F"
let bindig = ['0'-'1']
let uint = digit1 digit* | "0x" hexdig+ | "0b" bindig+ | "0"

let schar = ['\x20'-'\x21'] | ['\x23'-'\x5b'] | ['\x5d'-'\x7e']
(* TODO: Unicode *)
(* TODO: ESC *)

let alpha = ['\x41'-'\x5a'] | ['\x61'-'\x7a']
let ealpha = alpha | "@" | "_" | "$"
(* TODO: this should be:
let id = ealpha (("-" | ".")* (ealpha | digit))*
However, we want to distinguish the `$` cases
*)
let raw_id = (alpha | "@" | "_") (("-" | ".")* (ealpha | digit))*

let pchar = ['\x20'-'\xff']
(* FIXME: pchar should be Unicode *)
let crlf = ['\x0a'] | ['\x0d'] ['\x0a']
let comment = ";" pchar* crlf
let nl = comment | crlf
let sp = " "
let ws = sp | nl
let nonempty_s = ws+

rule token =
  parse
  | uint as x { (UINT (Prims.parse_int x)) }
  | ['"'] (schar* as x) ['"'] { (TEXT x) }
  | nonempty_s { NONEMPTY_S }
  | raw_id as x { (RAW_ID x) }
  | "=>" { ARROW }
  | "=" { EQ }
  | "$$" { DOLLARDOLLAR }
  | "$" { DOLLAR }
  | "//" { SLASHSLASH }
  | "/" { SLASH }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "#6" { POUND6 }
  | "." { DOT }
  | "#" { POUND }
  | "-" { MINUS }
  | "," { COMMA }
  | ":" { COLON }
  | "^" { HAT }
  | "*" { STAR }
  | "+" { PLUS }
  | "?" { QUESTION }
  | eof { EOF }

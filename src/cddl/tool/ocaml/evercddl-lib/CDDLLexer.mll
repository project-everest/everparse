{

open CDDLParser
open CDDL_Spec_AST_Base
open Tokens
open Fstar_pluginlib

let debug (x: token) =
(*
  print_endline ("Token: " ^ Tokens.show_token x);
*)
  x

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
  | uint as x { debug (UINT (Prims.parse_int x)) }
  | ['"'] (schar* as x) ['"'] { debug (TEXT x) }
  | nonempty_s { debug NONEMPTY_S }
  | raw_id as x { debug (RAW_ID x) }
  | "=>" { debug ARROW }
  | "=" { debug EQ }
  | "$$" { debug DOLLARDOLLAR }
  | "$" { debug DOLLAR }
  | "//=" { debug SLASHSLASHEQ }
  | "//" { debug SLASHSLASH }
  | "/=" { debug SLASHEQ }
  | "/" { debug SLASH }
  | "(" { debug LPAREN }
  | ")" { debug RPAREN }
  | "{" { debug LBRACE }
  | "}" { debug RBRACE }
  | "[" { debug LBRACK }
  | "]" { debug RBRACK }
  | "#0" { debug POUND0 }
  | "#1" { debug POUND1 }
  | "#2" { debug POUND2 }
  | "#3" { debug POUND3 }
  | "#6" { debug POUND6 }
  | "#7" { debug POUND7 }
  | "&"  { debug AMP }
  | "..." { debug DOTDOTDOT }
  | ".." { debug DOTDOT }
  | "." { debug DOT }
  | "#" { debug POUND }
  | "-" { debug MINUS }
  | "," { debug COMMA }
  | ":" { debug COLON }
  | "^" { debug HAT }
  | "*" { debug STAR }
  | "+" { debug PLUS }
  | "?" { debug QUESTION }
  | eof { debug EOF }

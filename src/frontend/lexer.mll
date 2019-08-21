{

open Parser
module H = BatHashtbl

let locate lb tok =
  tok,
  Lexing.lexeme_start_p lb,
  Lexing.lexeme_end_p lb

let keywords = H.create 0
let () =
  H.add keywords "sizeof" SIZEOF;
  H.add keywords "enum" ENUM;
  H.add keywords "typedef" TYPEDEF;
  H.add keywords "struct" STRUCT;
  H.add keywords "casetype" CASETYPE;
  H.add keywords "switch" SWITCH;
  H.add keywords "case" CASE;
  H.add keywords "this" THIS;
  H.add keywords "UINT32" UINT32

}

let space = " " | "\t"
let newline = "\r" | "\r\n" | "\n"
let skip = space+ | newline+

let digit = ['0'-'9']
let hex   = digit | ['A'-'F'] | ['a'-'f']
let xinteger = "0x" hex+
let integer = digit+



let low_alpha = ['a'-'z']
let up_alpha =  ['A'-'Z']
let any = up_alpha | low_alpha | "_" | digit

let lident = low_alpha any*
let uident = up_alpha any*
let ident_start = low_alpha | up_alpha | "_"
let ident = ident_start any*

let line_comment = "//" any*  newline


rule token =
  parse
  | "#define"         { locate lexbuf DEFINE }
  | ident as i        { locate lexbuf (IDENT i) }
  | line_comment as c { locate lexbuf (COMMENT c) }
  | "("            { locate lexbuf LPAREN }
  | "="            { locate lexbuf EQ }
  | "&&"           { locate lexbuf AND }
  | "||"           { locate lexbuf OR }
  | integer as i   { locate lexbuf (INT (int_of_string i) ) }
  | " "            { token lexbuf }
  | eof            { locate lexbuf EOF }
  | _              { assert false }


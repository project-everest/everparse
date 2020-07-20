{

open Parser
open Ast
module Option  = BatOption
module H = BatHashtbl

let mk_pos (l:Lexing.position) =
    let open Lexing in
      let col = (l.pos_cnum - l.pos_bol + 1) in
      {
        filename=l.pos_fname;
        line=Z.of_int l.pos_lnum;
        col=Z.of_int col;
      }

let with_range (x:'a) (l:Lexing.position) : 'a with_meta_t =
    Ast.with_range x (mk_pos l, mk_pos l)
    
let locate lb tok =
  tok,
  Lexing.lexeme_start_p lb,
  Lexing.lexeme_end_p lb

let locate_pos lb tok =
  let tok, p, q = locate lb tok in
  tok, mk_pos p, mk_pos q

let keywords = H.create 0
let () =
  H.add keywords "not" NOT;
  H.add keywords "where" WHERE;
  H.add keywords "requires" REQUIRES;    
  H.add keywords "sizeof" SIZEOF;
  H.add keywords "enum" ENUM;
  H.add keywords "typedef" TYPEDEF;
  H.add keywords "struct" STRUCT;
  H.add keywords "casetype" CASETYPE;
  H.add keywords "switch" SWITCH;
  H.add keywords "case" CASE;
  H.add keywords "this" THIS;
  H.add keywords "entrypoint" ENTRYPOINT;
  H.add keywords "if" IF; 
  H.add keywords "else" ELSE;
  H.add keywords "mutable" MUTABLE;
  H.add keywords "field_pos" FIELD_POS;
  H.add keywords "field_ptr" FIELD_PTR;
  H.add keywords "var" VAR;
  H.add keywords "abort" ABORT;
  H.add keywords "return" RETURN  

let unsigned_int_of_string s = int_of_string (String.sub s 0 (String.length s - 2))

}

let space = " " | "\t"
let newline = "\r" | "\r\n" | "\n"
let skip = space+ | newline+
let digit = ['0'-'9']
let hex   = digit | ['A'-'F'] | ['a'-'f']
let integer = digit+
let uint8 = digit+ "uy"
let uint16 = digit+ "us"
let uint32 = digit+ "ul"
let uint64 = digit+ "uL"
let xint8 = "0x" hex hex "uy"?
let xint16 = "0x" hex hex hex hex "us"?
let xint32 = "0x" hex hex hex hex hex hex hex hex "ul"?
let xint64 = "0x" hex hex hex hex hex hex hex hex hex hex hex hex hex hex hex hex "uL"?
let bool = "true" | "false"


let low_alpha = ['a'-'z']
let up_alpha =  ['A'-'Z']
let any = up_alpha | low_alpha | "_" | digit

let lident = low_alpha any*
let uident = up_alpha any*
let ident_start = low_alpha | up_alpha | "_"
let ident = ident_start any*
let reserved_prefix = "___"
let line_comment = "//" [ ^ '\r' '\n']*

rule token =
  parse
  | bool as b      { locate lexbuf (BOOL (b="true")) }
  | "#define"      { locate lexbuf DEFINE }
  | ident as i        {
      let ident = with_range i (Lexing.lexeme_start_p lexbuf) in
      check_reserved_identifier ident;
      locate lexbuf (H.find_option keywords i |> Option.default (IDENT (ident)))
    }
  | line_comment as c { Ast.comments_buffer.push (locate_pos lexbuf c); token lexbuf }
  | "/*++"         { block_comment ("", Lexing.lexeme_start_p lexbuf) lexbuf }
  | "("            { locate lexbuf LPAREN }
  | ")"            { locate lexbuf RPAREN }  
  | ">="           { locate lexbuf GEQ }
  | "<="           { locate lexbuf LEQ }
  | ">"            { locate lexbuf GREATER_THAN }
  | "<"            { locate lexbuf LESS_THAN }
  | "="            { locate lexbuf EQ }
  | "!="           { locate lexbuf NEQ }  
  | "&&"           { locate lexbuf AND }
  | "||"           { locate lexbuf OR }
  | ","            { locate lexbuf COMMA }
  | ";"            { locate lexbuf SEMICOLON }
  | ":"            { locate lexbuf COLON }
  | "{:on-success" { locate lexbuf LBRACE_ONSUCCESS }
  | "{"            { locate lexbuf LBRACE }
  | "}"            { locate lexbuf RBRACE }
  | "[="           { locate lexbuf LBRACK_EQ }    
  | "[<="          { locate lexbuf LBRACK_LEQ }  
  | "["            { locate lexbuf LBRACK }
  | "]"            { locate lexbuf RBRACK }  
  | "*"            { locate lexbuf STAR }
  | "/"            { locate lexbuf DIV }    
  | "+"            { locate lexbuf PLUS }  
  | "-"            { locate lexbuf MINUS }
  | uint8  as i    { locate lexbuf (UINT8  (unsigned_int_of_string i) ) }
  | uint16 as i    { locate lexbuf (UINT16 (unsigned_int_of_string i) ) }
  | uint32 as i    { locate lexbuf (UINT32 (unsigned_int_of_string i) ) }
  | uint64 as i    { locate lexbuf (UINT64 (unsigned_int_of_string i) ) }
  | integer as i   { locate lexbuf (INT (int_of_string i) ) }
  | xint8 as x     { locate lexbuf (XINT8 x) }
  | xint16 as x    { locate lexbuf (XINT16 x) }
  | xint32 as x    { locate lexbuf (XINT32 x) }
  | xint64 as x    { locate lexbuf (XINT64 x) }  
  | space+         { token lexbuf }
  | newline        { Lexing.new_line lexbuf; token lexbuf }
  | eof            { locate lexbuf EOF }
  | _              { assert false }

and block_comment cp = parse
 | "--*/"
    { let contents, pos = cp in
      BLOCK_COMMENT(contents), pos, Lexing.lexeme_end_p lexbuf }

 | newline as n
    { let contents, pos = cp in
      Lexing.new_line lexbuf;
      block_comment (contents^n, pos) lexbuf }

 | _ as n 
   {  let contents, pos = cp in
      let n = String.make 1 n in
      block_comment (contents^n, pos) lexbuf }





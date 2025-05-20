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

let range_of_lexbuf lb =
  mk_pos (Lexing.lexeme_start_p lb),
  mk_pos (Lexing.lexeme_end_p lb)

let to_ident' (x:string) = {modul_name=None; name=x}

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
  H.add keywords "where" WHERE;
  H.add keywords "requires" REQUIRES;
  H.add keywords "sizeof" SIZEOF;
  H.add keywords "enum" ENUM;
  H.add keywords "typedef" TYPEDEF;
  H.add keywords "struct" STRUCT;
  H.add keywords "casetype" CASETYPE;
  H.add keywords "switch" SWITCH;
  H.add keywords "case" CASE;
  H.add keywords "default" DEFAULT;
  H.add keywords "this" THIS;
  H.add keywords "entrypoint" ENTRYPOINT;
  H.add keywords "aligned" ALIGNED;
  H.add keywords "if" IF;
  H.add keywords "else" ELSE;
  H.add keywords "mutable" MUTABLE;
  H.add keywords "field_pos_64" FIELD_POS_64;
  H.add keywords "field_pos_32" FIELD_POS_32;
  H.add keywords "field_pos" FIELD_POS_32; (* TODO: change to FIELD_POS_64 once ready *)
  H.add keywords "field_ptr" FIELD_PTR;
  H.add keywords "field_ptr_after" FIELD_PTR_AFTER;
  H.add keywords "var" VAR;
  H.add keywords "abort" ABORT;
  H.add keywords "return" RETURN;
  H.add keywords "refining" REFINING;
  H.add keywords "as" AS;
  H.add keywords "module" MODULE;
  H.add keywords "export" EXPORT;
  H.add keywords "output" OUTPUT;
  H.add keywords "union" UNION;
  H.add keywords "extern" EXTERN;
  H.add keywords "probe" PROBE;
  H.add keywords "pointer" POINTER;
  H.add keywords "PURE" PURE;
  H.add keywords "specialize" SPECIALIZE

let unsigned_int_of_string s = int_of_string (String.sub s 0 (String.length s - 2))

let deprecation_warning lb t =
    Ast.warning ("This construct is deprecated; Use '" ^t^ "' instead")
                (range_of_lexbuf lb)
}

let space = " " | "\t"
let newline = "\r" | "\r\n" | "\n"
let skip = space+ | newline+
let digit = ['0'-'9']
let hex   = digit | ['A'-'F'] | ['a'-'f']
let signedness_width = "uy" | "us" | "ul" | "uL"
let integer = digit+ signedness_width?
let xinteger = "0x" hex+ signedness_width?
let bool = "true" | "false"
let string = "\""

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
      let ident = with_range (to_ident' i) (Lexing.lexeme_start_p lexbuf) in
      check_reserved_identifier ident;
      locate lexbuf (H.find_option keywords i |> Option.default (IDENT (ident)))
    }
  | line_comment as c { Ast.comments_buffer.push (locate_pos lexbuf c); token lexbuf }
  | "/*++"         { block_comment ("", Lexing.lexeme_start_p lexbuf) lexbuf }
  | "/*"           { multi_line_comment lexbuf }
  | "#if"          { locate lexbuf HASH_IF }
  | "#elif"        { locate lexbuf HASH_ELIF }  
  | "#else"        { locate lexbuf HASH_ELSE }
  | "#endif"       { locate lexbuf HASH_ENDIF }  
  | "("            { locate lexbuf LPAREN }
  | ")"            { locate lexbuf RPAREN }
  | "<<"           { locate lexbuf SHIFT_LEFT }
  | ">>"           { locate lexbuf SHIFT_RIGHT }
  | ">="           { locate lexbuf GEQ }
  | "<="           { locate lexbuf LEQ }
  | ">"            { locate lexbuf GREATER_THAN }
  | "<"            { locate lexbuf LESS_THAN }
  | "=="           { locate lexbuf DOUBLEEQ }
  | "="            { locate lexbuf EQ }
  | "!="           { locate lexbuf NEQ }
  | "!"            { locate lexbuf NOT }
  | "&&"           { locate lexbuf AND }
  | "&"            { locate lexbuf BITWISE_AND }
  | "||"           { locate lexbuf OR }
  | "|"            { locate lexbuf BITWISE_OR }
  | "^"            { locate lexbuf BITWISE_XOR }
  | "~"            { locate lexbuf BITWISE_NOT }
  | "."            { locate lexbuf DOT }
  | "->"           { locate lexbuf RARROW }
  | ","            { locate lexbuf COMMA }
  | ";"            { locate lexbuf SEMICOLON }
  | "::"           { locate lexbuf COLON_COLON }
  | ":"            { locate lexbuf COLON }
  | "?"            { locate lexbuf QUESTION }
  | "{:act"        { locate lexbuf LBRACE_ACT }
  | "{:check"      { locate lexbuf LBRACE_CHECK }
  | "{:on-success" { locate lexbuf LBRACE_ONSUCCESS }

  | "{"            { locate lexbuf LBRACE }
  | "}"            { locate lexbuf RBRACE }
  | "[:byte-size"                { locate lexbuf LBRACK_BYTESIZE }
  | "[:byte-size-single-element-array-at-most"      { locate lexbuf LBRACK_BYTESIZE_AT_MOST }
  | "[:byte-size-single-element-array"        { locate lexbuf LBRACK_SINGLE_ELEMENT_BYTESIZE }
  | "[:zeroterm"     { locate lexbuf LBRACK_STRING }
  | "[:zeroterm-byte-size-at-most"     { locate lexbuf LBRACK_STRING_AT_MOST }
  | "[:consume-all"  { locate lexbuf LBRACK_CONSUME_ALL }
  | "["                          { locate lexbuf LBRACK (* intended for use with UINT8 arrays only, interpreted as [:byte-size] *)}
  | "]"                          { locate lexbuf RBRACK }
  | "[="           { deprecation_warning lexbuf "[:byte-size-single-element-array";
                     locate lexbuf LBRACK_EQ }
  | "[<="          { deprecation_warning lexbuf "[:byte-size-single-element-array-at-most";
                     locate lexbuf LBRACK_LEQ }
  | "*"            { locate lexbuf STAR }
  | "/"            { locate lexbuf DIV }
  | "%"            { locate lexbuf REM }
  | "+"            { locate lexbuf PLUS }
  | "-"            { locate lexbuf MINUS }
  | xinteger as i  { locate lexbuf (XINT i) }
  | integer as i   { locate lexbuf (INT i) }
  | '"'            { string (Buffer.create 0) (Lexing.lexeme_start_p lexbuf) lexbuf }
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

and multi_line_comment = parse
 | "*/"
   {
      token lexbuf
   }

 | newline as n
    {
      Lexing.new_line lexbuf;
      multi_line_comment lexbuf
    }

 | _ as n
   {
      multi_line_comment lexbuf
   }

and string buffer start_pos = parse
 | '\\' newline space*
   {
      Lexing.new_line lexbuf; string buffer start_pos lexbuf
   }
 | newline
   {
      Buffer.add_string buffer (Lexing.lexeme lexbuf);
      Lexing.new_line lexbuf;
      string buffer start_pos lexbuf
   }
 | '"'
   {
    (* position info must be set since the start of the string *)
    STRING (Buffer.contents buffer),
    start_pos,
    Lexing.lexeme_end_p lexbuf
   }
 | _
   {
     Buffer.add_string buffer (Lexing.lexeme lexbuf);
     string buffer start_pos lexbuf
   }
 | eof
   {
     let r = (mk_pos start_pos) in
     error "Unterminated string" (r, r)
   }

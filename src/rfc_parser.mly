%{
open Rfc_ast

let ectr = ref 0
%}

%token SEMCOL FULCOL
%token LBRACE RBRACE
%token LBRACK RBRACK
%token LPAREN RPAREN
%token COMMA  EOF
%token EQUALS DOTDOT

%token STRUCT ENUM
%token SELECT CASE DEFAULT

%token <string>  ATTRIBUTE
%token <string>  TYPE
%token <string>  CMMNT
%token <int>     INT
%token <int*int> RANGE

%start <Rfc_ast.prog> prog
%%

prog:
	| g = list(gemstone); EOF; { g }
;

attrlist:
	| a = ATTRIBUTE; t=attrlist { a :: t }
	| {[]}
;

gemstone:
	| ENUM; a=attrlist; LBRACE; enum = separated_list(COMMA, enum_field); RBRACE; t = TYPE; SEMCOL;
		{ ectr := 0; Enum(a, enum, t) }
	| STRUCT; a = attrlist; LBRACE; fields = list(struct_field); RBRACE; t = TYPE; SEMCOL;
		{ match fields with
		  | [(al, ty, n, vec, def)] -> Typedef("inline"::al, ty, t, vec, def)
			| l -> Struct(a, fields, t) }
	| t = struct_field; { Typedef(t) }
;

vector:
	|	{ VectorNone }
	| LBRACK; l = INT; RBRACK; { VectorFixed(l) }
	| LBRACK; s = TYPE; RBRACK;	{ VectorSymbolic(s) }
	| r = RANGE; { let (min,max)=r in VectorRange(min,max) }
;

enum_field:
	| e = TYPE {let c = !ectr in incr ectr; EnumFieldSimple(e, c)}
	| e = TYPE; LPAREN; l = INT; RPAREN; { EnumFieldSimple(e, l) }
	| e = TYPE; LPAREN; a = INT; DOTDOT; b = INT; RPAREN
		{ EnumFieldRange(e, a, b) }
	| LPAREN; l = INT; RPAREN; { EnumFieldAnonymous(l) }
;

default_val:
	| { None }
	| EQUALS l = INT { Some [l] }
	| EQUALS LBRACE vl = separated_list(COMMA, INT) RBRACE { Some vl }
	| EQUALS e = TYPE; LPAREN; l = INT; RPAREN { Some  [l] }

struct_field:
	|  a=attrlist; ty = field_type; n = TYPE; v = vector; dv = default_val; SEMCOL;
	  { (a, ty, n, v, dv) }

field_type:
  | t = TYPE; { TypeSimple t }
	| SELECT; LPAREN; n = TYPE; RPAREN; LBRACE; cases = list(select_case); def = default_case; RBRACE;
	  { TypeSelect(n, cases, def) }
;

select_case:
	| CASE; e = TYPE; FULCOL; t = TYPE; SEMCOL;	{ (e,t) }
;

default_case:
  | { None }
	| DEFAULT; FULCOL; t = TYPE; SEMCOL; { Some t }
;

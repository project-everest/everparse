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
%token SELECT CASE

%token <string>  TYPE
%token <string>  CMMNT
%token <int>     INT
%token <int*int> RANGE

%start <Rfc_ast.prog> prog
%%

prog:
	| g = list(gemstone); EOF;
		{ g }
;

qualstruct:
	| STRUCT { None }
	| q = TYPE; STRUCT { Some q }
;

gemstone:
	| ENUM; LBRACE; enum = separated_list(COMMA, enum_fields); RBRACE; t = TYPE; SEMCOL;
				{ ectr := 0; Enum(enum, t) }
		| q = qualstruct; LBRACE; SELECT; LPAREN; c = TYPE; RPAREN; LBRACE; s = list(select_case); RBRACE; option(SEMCOL); RBRACE; t = TYPE; SEMCOL;
				{ SelectStruct(t, c, s) }
		| q = qualstruct; LBRACE; fields = unambiguous_fields RBRACE; t = TYPE; SEMCOL;
		{ Struct(t, q, fields) }
;

vector:
	| t = TYPE; n = TYPE;
		{ VectorSimple(t, n) }
	| t = TYPE; n = TYPE; LBRACK; l = INT; RBRACK;
		{ VectorSize(t, n, l) }
	| t = TYPE; n = TYPE; LBRACK; s = TYPE; RBRACK;
		{ VectorSymbolic(t, n, s) }
	| t = TYPE; n = TYPE; r = RANGE;
		{ VectorRange(t, n, r) }
;

enum_fields:
		| e = TYPE
				{let c = !ectr in incr ectr; EnumFieldSimple(e, c)}
	| e = TYPE; LPAREN; l = INT; RPAREN;
		{ EnumFieldSimple(e, l) }
	| e = TYPE; LPAREN; a = INT; DOTDOT; b = INT; RPAREN
		{ EnumFieldRange(e, a, b) }
	| LPAREN; l = INT; RPAREN;
		{ EnumFieldAnonymous(l) }
;

default_val:
	| { None }
	| EQUALS LBRACE vl = separated_list(COMMA, INT) RBRACE { Some vl }
	| EQUALS e = TYPE; LPAREN; l = INT; RPAREN { Some  [l] }

unambiguous_fields:
	| { [] }
		| v = vector; dv = default_val; SEMCOL; l = list(struct_fields)
				{ StructFieldSimple(v, dv) :: l }
;

struct_fields:
		| v = vector; dv = default_val; SEMCOL;
		{ StructFieldSimple(v, dv) }
		| SELECT; LPAREN; t = TYPE; RPAREN; LBRACE; sele = list(select_ty_case); RBRACE; y = TYPE; SEMCOL;
		{ StructFieldSelect(t, sele, y) }
;

select_case:
	| CASE; e = TYPE; FULCOL; fields = list(struct_fields);
				{ (e, fields) }
;

select_ty_case:
	| CASE; e = TYPE; FULCOL; t = TYPE; SEMCOL;
		{ SelectField(e, t) }
;

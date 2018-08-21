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

%token STRUCT ENUM ABSTRACT
%token SELECT CASE

%token <string>  ATTRIBUTE
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

attrlist:
	| a = ATTRIBUTE; t=attrlist { a :: t }
	| {[]}
;

gemstone:
	| ENUM; a=attrlist; LBRACE; enum = separated_list(COMMA, enum_fields); RBRACE; t = TYPE; SEMCOL;
		{ ectr := 0; Enum(enum, t, a) }
	| STRUCT; a = attrlist; LBRACE; SELECT; LPAREN; c = TYPE; RPAREN; LBRACE; s = list(select_case); RBRACE; option(SEMCOL); RBRACE; t = TYPE; SEMCOL;
		{ SelectStruct(t, c, s) }
	| STRUCT; a = attrlist; LBRACE; fields = unambiguous_fields RBRACE; t = TYPE; SEMCOL;
		{ match fields with
                  | [StructFieldSimple (v, None)] ->
                     SingleFieldStruct(t, a, v)
                  | _ -> Struct(t, a, fields) }
        | ABSTRACT; a = attrlist; t=TYPE; FULCOL; min=INT; DOTDOT; max=INT; SEMCOL;
                {
                    Abstract(t, a, min, max)    
                }
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

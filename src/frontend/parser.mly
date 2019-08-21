%{
  open Ast
%}

%token<int>     INT
%token<string>  COMMENT IDENT
%token          EQ AND OR EOF SIZEOF ENUM TYPEDEF STRUCT CASETYPE SWITCH CASE THIS UINT32
%token          DEFINE LPAREN RPAREN LBRACE RBRACE
%start <Ast.decl list> prog
%start <Ast.expr> expr_top

%nonassoc EQ
%left OR
%left AND


%%

constant:
  | i=INT { Int i }

expr:
  | l=expr EQ r=expr
    { Expr (Eq, [l;r]) }
  | l=expr AND r=expr
    { Expr (And, [l;r]) }
  | l=expr OR r=expr
    { Expr (Or, [l;r]) }
  | c=constant
    { Expr (Constant c, []) }

decl:
  | l=COMMENT { Comment l }
  | DEFINE i=IDENT c=constant { Define (i, c) }

expr_top:
  | e=expr EOF { e }

prog:
  | d=decl EOF { [d] }
  | d=decl p=prog { d :: p }

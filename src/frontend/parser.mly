%{
  open Ast
%}

%token<int>     INT
%token        EQ AND OR EOF
%start <Ast.expr> prog

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

prog:
  | e=expr EOF { e }

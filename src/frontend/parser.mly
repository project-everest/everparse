%{
  open Ast
%}

%token<int>     INT
%token<string>  COMMENT IDENT XINT
%token          EQ AND OR EOF SIZEOF ENUM TYPEDEF STRUCT CASETYPE SWITCH CASE THIS
%token          DEFINE LPAREN RPAREN LBRACE RBRACE COMMA SEMICOLON COLON
%token          STAR MINUS PLUS LBRACK RBRACK
%start <Ast.decl list> prog
%start <Ast.expr> expr_top

%nonassoc EQ
%left OR
%left AND
%left PLUS
%left MINUS


%%

right_flexible_list(SEP, X):
  |     { [] }
  | x=X { [x] }
  | x=X SEP xs=right_flexible_list(SEP, X) { x :: xs }

right_flexible_nonempty_list(SEP, X):
  | x=X { [x] }
  | x=X SEP xs=right_flexible_list(SEP, X) { x :: xs }

constant:
  | i=INT { Int i }
  | x=XINT { XInt x }

rel_op:
  | EQ { Eq }

expr:
  | i=IDENT { Identifier i }
  | THIS    { This }
  | c=constant
    { Constant c }
  | l=expr o=rel_op r=expr %prec EQ
    { App (o, [l;r]) }
  | l=expr AND r=expr
    { App (And, [l;r]) }
  | l=expr OR r=expr
    { App (Or, [l;r]) }
  | l=expr MINUS r=expr
    { App (Minus, [l;r]) }
  | l=expr PLUS r=expr
    { App (Plus, [l;r]) }
  | SIZEOF LPAREN e=expr RPAREN
    { App (SizeOf, [e]) }

arguments:
 | es=right_flexible_nonempty_list(COMMA, expr)  { es }

typ:
  | i=IDENT { Type_name i }
  | hd=IDENT LPAREN a=arguments RPAREN { Type_app(hd, a) }

constraint_opt:
  |  { None }
  | LBRACE o=rel_op e=expr RBRACE { Some (App(o, [This; e])) }

array_size_opt:
  |  { None }
  | LBRACK e=expr RBRACK { Some e }

struct_field:
  | l=COMMENT { FieldComment l }
  | t=typ fn=IDENT aopt=array_size_opt c=constraint_opt { Field {field_ident=fn; field_type=t; field_constraint=c} }


parameter:
  | t=typ i=IDENT { (t, i) }

parameters:
  |  { [] }
  | LPAREN ps=right_flexible_nonempty_list(COMMA, parameter) RPAREN { ps }

case:
  | CASE i=IDENT COLON f=struct_field { (i, f) }

cases:
  | cs=right_flexible_nonempty_list(SEMICOLON, case) { cs }

decl:
  | l=COMMENT { Comment l }
  | DEFINE i=IDENT c=constant { Define (i, c) }
  | t=IDENT ENUM i=IDENT LBRACE es=right_flexible_nonempty_list(COMMA, IDENT) RBRACE
    { Enum(t, i, es) }
  | TYPEDEF STRUCT i=IDENT ps=parameters
    LBRACE fields=right_flexible_nonempty_list(SEMICOLON, struct_field)
    RBRACE j=IDENT COMMA STAR k=IDENT SEMICOLON
    { Record(i, ps, fields, j, k) }
  | CASETYPE i=IDENT ps=parameters
    LBRACE SWITCH LPAREN e=IDENT RPAREN
           LBRACE cs=cases
           comms=list(COMMENT)
           RBRACE
    RBRACE j=IDENT COMMA STAR k=IDENT SEMICOLON
    { CaseType(i, ps, (e, cs), j, k) }

expr_top:
  | e=expr EOF { e }

prog:
  | d=decl EOF { [d] }
  | d=decl p=prog { d :: p }

%{
  open FStar_Pervasives
  open Lexing
  open Ast
  let mk_td b i j k = {
    typedef_name = i;
    typedef_abbrev = j;
    typedef_ptr_abbrev = k;
    typedef_entry_point = b
  }

  let mk_pos (l:Lexing.position) =
      let col = (l.pos_cnum - l.pos_bol + 1) in
      {
        filename=l.pos_fname;
        line=Z.of_int l.pos_lnum;
        col=Z.of_int col;
      }

  let with_range (x:'a) (l:Lexing.position) : 'a with_meta_t =
      Ast.with_range x (mk_pos l, mk_pos l)

    let pointer_name j p =
         match p with
         | None -> {j with v="P"^j.v}
         | Some k -> k
%}

%token<int>       INT
%token<string>  XINT
%token<string>  BLOCK_COMMENT
%token<bool>    BOOL
%token<Ast.ident>   IDENT
%token          EQ NEQ AND OR NOT EOF SIZEOF ENUM TYPEDEF STRUCT CASETYPE SWITCH CASE THIS ENTRYPOINT
%token          DEFINE LPAREN RPAREN LBRACE RBRACE COMMA SEMICOLON COLON
%token          STAR DIV MINUS PLUS LBRACK RBRACK LEQ LESS_THAN GEQ GREATER_THAN WHERE REQUIRES IF ELSE
%token          MUTABLE LBRACE_ONSUCCESS FIELD_POS FIELD_PTR VAR ABORT RETURN
(* LBRACE_ONERROR CHECK  *)
%start <Ast.decl list> prog
%start <Ast.expr> expr_top

%left OR
%left AND
%nonassoc EQ LEQ LESS_THAN GEQ GREATER_THAN NEQ
%left PLUS
%left MINUS
%left STAR
%left DIV


%%

option_of (X):
  |  { None }
  | x=X { Some x }

right_flexible_list(SEP, X):
  |     { [] }
  | x=X { [x] }
  | x=X SEP xs=right_flexible_list(SEP, X) { x :: xs }

right_flexible_nonempty_list(SEP, X):
  | x=X { [x] }
  | x=X SEP xs=right_flexible_list(SEP, X) { x :: xs }

constant:
  | i=INT { Int (Ast.UInt32, Z.of_int i) }
  | x=XINT { XInt x }
  | b=BOOL { Bool b }

rel_op:
  | EQ { Eq }
  | NEQ { Neq }
  | LEQ { LE }
  | LESS_THAN { LT }
  | GEQ { GE }
  | GREATER_THAN { GT }

else_opt:
  |             { None   }
  | ELSE LBRACE e=expr RBRACE { Some e }

expr_no_range:
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
  | l=expr STAR r=expr
    { App (Mul, [l;r]) }
  | l=expr DIV r=expr
    { App (Division, [l;r]) }
  | NOT LPAREN e=expr RPAREN
    { App (Not, [e]) }
  | SIZEOF LPAREN e=expr RPAREN
    { App (SizeOf, [e]) }
  | IF e=expr LBRACE e1=expr RBRACE e2=else_opt
    {
        let e2 =
            match e2 with
            | None -> with_range (Constant (Bool true)) $startpos
            | Some e2 -> e2
        in
        App(IfThenElse, [e;e1;e2])
    }

expr_opt:
  |        { None }
  | e=expr { Some e }

expr:
  | e=expr_no_range { with_range e $startpos }
  | LPAREN e=expr RPAREN eopt=expr_opt {
      match e, eopt with
      | _, None -> with_range e.v $startpos
      | {v=Identifier i}, Some e' ->
        with_range (App (Cast (None, as_integer_typ i), [e'])) $startpos(eopt)
      | _ -> error ("Expected a cast expression, got " ^ (print_expr e)) e.range
    }

arguments:
 | es=right_flexible_nonempty_list(COMMA, expr)  { es }

typ_no_range:
  | i=IDENT { Type_app(i, []) }
  | hd=IDENT LPAREN a=arguments RPAREN { Type_app(hd, a) }

typ:
  | t=typ_no_range { with_range t $startpos }

maybe_pointer_typ:
  | t=typ { t }
  | t=pointer_typ { t }

pointer_typ:
  | t=maybe_pointer_typ STAR { with_range (Pointer t) $startpos }

refinement:
  | LBRACE e=expr RBRACE { e }

array_size:
  | LBRACK e=expr RBRACK { (e, true) }
  | LBRACK LBRACE e=expr RBRACE RBRACK { (e, false) }

bitwidth:
  | COLON i=INT { Inl (with_range (Z.of_int i) $startpos(i)) }

field_action:
  | LBRACE_ONSUCCESS a=action RBRACE { a, false }

struct_field:
  | t=typ fn=IDENT bopt=option_of(bitwidth) aopt=option_of(array_size) c=option_of(refinement) a=option_of(field_action)
    {
        {
         field_dependence=false;
         field_ident=fn;
         field_type=t;
         field_array_opt=aopt;
         field_constraint=c;
         field_size=None;
         field_number=None;
         field_bitwidth=bopt;
         field_action=a
        }
    }

field:
  | f = struct_field
    {
      let comms = Ast.comments_buffer.flush () in
      let range = (mk_pos $startpos, mk_pos $startpos) in
      with_range_and_comments f range comms
    }


immutable_parameter:
  | t=typ i=IDENT { (t, i, Immutable) }

mutable_parameter:
  | MUTABLE t=pointer_typ i=IDENT { (t, i, Mutable) }

parameter:
  | i=immutable_parameter { i }
  | m=mutable_parameter { m }

parameters:
  |  { [] }
  | LPAREN ps=right_flexible_nonempty_list(COMMA, parameter) RPAREN { ps }

case:
  | CASE i=IDENT COLON f=field { (with_range (Identifier i) $startpos(i), f) }

cases:
  | cs=right_flexible_nonempty_list(SEMICOLON, case) { cs }

maybe_entry:
  |            { false }
  | ENTRYPOINT { true }

where_opt:
  |              { None }
  | WHERE e=expr { Some e }
  | REQUIRES e=expr { Some e }

atomic_action:
  | RETURN e=expr SEMICOLON { Action_return e }
  | ABORT SEMICOLON         { Action_abort }
  | FIELD_POS SEMICOLON     { Action_field_pos }
  | FIELD_PTR SEMICOLON     { Action_field_ptr }
  | STAR i=IDENT SEMICOLON  { Action_deref i }
  | STAR i=IDENT EQ e=expr SEMICOLON { Action_assignment(i, e) }
  | f=IDENT LPAREN args=arguments RPAREN SEMICOLON { Action_call(f, args) }

action_else:
  | ELSE LBRACE a=action RBRACE { a }

action_no_range:
  | a=atomic_action { Atomic_action a }
  | a1=atomic_action a=action { Action_seq (a1, a) }
  | IF e=expr LBRACE a1=action RBRACE a2=option_of(action_else) { Action_ite (e, a1, a2) }
  | VAR i=IDENT EQ a1=atomic_action a2=action               { Action_let (i, a1, a2) }

action:
  | a=action_no_range { with_range a ($startpos(a)) }

enum_case:
  | i=IDENT            { i, None }
  | i=IDENT EQ j=INT   { i, Some (Inl (Z.of_int j)) }
  | i=IDENT EQ j=IDENT { i, Some (Inr j) }

typedef_pointer_name_opt:
  |                    { None }
  | COMMA STAR k=IDENT { Some k }
decl_no_range:
  | DEFINE i=IDENT c=constant { Define (i, None, c) }
  | t=IDENT ENUM i=IDENT LBRACE es=right_flexible_nonempty_list(COMMA, enum_case) RBRACE
    { Enum(with_range (Type_app (t, [])) ($startpos(t)), i, es) }
  | b=maybe_entry TYPEDEF t=typ i=IDENT SEMICOLON
    { TypeAbbrev (t, i) }
  | b=maybe_entry TYPEDEF STRUCT i=IDENT ps=parameters w=where_opt
    LBRACE fields=right_flexible_nonempty_list(SEMICOLON, field)
    RBRACE j=IDENT p=typedef_pointer_name_opt SEMICOLON
    {  let k = pointer_name j p in
       Record(mk_td b i j k, ps, w, fields)
    }
  | b=maybe_entry CASETYPE i=IDENT ps=parameters
    LBRACE SWITCH LPAREN e=IDENT RPAREN
           LBRACE cs=cases
           RBRACE
    RBRACE j=IDENT p=typedef_pointer_name_opt SEMICOLON
    {
        let k = pointer_name j p in
        let td = mk_td b i j k in
        CaseType(td, ps, (with_range (Identifier e) ($startpos(i)), cs))
    }

block_comment_opt:
  |                 { None }
  | c=BLOCK_COMMENT { Some c }

decl:
  | c=block_comment_opt d=decl_no_range {
      let _ = Ast.comments_buffer.flush () in
      match c with
      | Some c -> with_range_and_comments d (mk_pos ($startpos(d)), mk_pos ($startpos(d))) [c]
      | None -> with_range d ($startpos(d))
    }

expr_top:
  | e=expr EOF { e }

prog:
  | d=decl EOF { [d] }
  | d=decl p=prog { d :: p }

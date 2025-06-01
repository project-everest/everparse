%{
  open FStar_Pervasives
  open Lexing
  open Ast
  let mk_td b i j k = {
    typedef_name = i;
    typedef_abbrev = j;
    typedef_ptr_abbrev = k;
    typedef_attributes = b
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

  let parse_int_and_type r (s:string) : Z.t * string * integer_type =
      let r = mk_pos r, mk_pos r in
      let s', t = parse_int_suffix s in
      let i = Z.of_string s' in
      let t' = smallest_integer_type_of r i in
      let t = match t with
              | None -> t'
              | Some t ->
                if integer_type_leq t' t
                then t
                else error ("Integer " ^s^ " is too large for the specified type") r
      in
      i, s', t

  let mk_out_expr_from_ident id r = {
    out_expr_node = with_range (OE_id id) r;
    out_expr_meta = None
  }

  
%}

%token<string>  INT XINT STRING
%token<string>  BLOCK_COMMENT
%token<bool>    BOOL
%token<Ast.ident> IDENT
%token          EQ DOUBLEEQ NEQ AND OR NOT EOF SIZEOF ENUM TYPEDEF STRUCT CASETYPE SWITCH CASE DEFAULT THIS
%token          DEFINE LPAREN RPAREN LBRACE RBRACE DOT RARROW COMMA SEMICOLON COLON_COLON COLON QUESTION
%token          STAR DIV MINUS PLUS LEQ LESS_THAN GEQ GREATER_THAN WHERE REQUIRES IF ELSE
%token          LBRACK RBRACK LBRACK_LEQ LBRACK_EQ LBRACK_BYTESIZE LBRACK_BYTESIZE_AT_MOST LBRACK_SINGLE_ELEMENT_BYTESIZE
%token          LBRACK_CONSUME_ALL
%token          LBRACK_STRING LBRACK_STRING_AT_MOST
%token          MUTABLE LBRACE_ONSUCCESS LBRACE_ACT LBRACE_CHECK FIELD_POS_64 FIELD_POS_32 FIELD_PTR FIELD_PTR_AFTER VAR ABORT RETURN
%token          REM SHIFT_LEFT SHIFT_RIGHT BITWISE_AND BITWISE_OR BITWISE_XOR BITWISE_NOT AS
%token          MODULE EXPORT OUTPUT UNION EXTERN
%token          ENTRYPOINT REFINING ALIGNED
%token          HASH_IF HASH_ELSE HASH_ENDIF HASH_ELIF
%token          PROBE POINTER PURE SPECIALIZE SKIP_READ SKIP_WRITE

(* LBRACE_ONERROR CHECK  *)
%start <Ast.prog> prog
%start <Ast.expr> expr_top

%left OR
%left AND
%left BITWISE_OR
%left BITWISE_XOR
%left DOT RARROW
%left BITWISE_AND
%nonassoc NEQ DOUBLEEQ
%nonassoc LEQ LESS_THAN GEQ GREATER_THAN
%left SHIFT_LEFT SHIFT_RIGHT
%left PLUS MINUS
%left STAR REM DIV
%nonassoc BITWISE_NOT NOT

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
  | i=INT    { let n, _, t = parse_int_and_type ($startpos(i)) i in Int(t, n) }
  | i=XINT   { let _, x, t = parse_int_and_type ($startpos(i)) i in XInt(t, x) }
  | b=BOOL   { Bool b }

rel_op:
  | DOUBLEEQ     { Eq }
  | NEQ          { Neq }
  | LEQ          { LE None }
  | LESS_THAN    { LT None }
  | GEQ          { GE None }
  | GREATER_THAN { GT None }

else_opt:
  |             { None   }
  | ELSE LBRACE e=expr RBRACE { Some e }

hash_else_opt:
  | HASH_ENDIF                  { None   }
  | HASH_ELSE e=expr HASH_ENDIF { Some e }
  | HASH_ELIF e=hash_if_body    { Some (with_range e ($startpos)) }

atomic_expr:
  | i=qident   { Identifier i }
  | THIS       { This }
  | c=constant { Constant c }

atomic_or_paren_expr:
  | e=atomic_expr  { with_range e $startpos }
  | LPAREN e=expr RPAREN { e }

castable_expr:
  |               { None }
  | e=atomic_expr { Some e }
  | LPAREN e=expr RPAREN { Some e.v }

hash_if_body:
  | e=atomic_or_paren_expr e1=expr e2=hash_else_opt
    {
        let e2 =
            match e2 with
            | None -> with_range (Constant (Bool true)) $startpos
            | Some e2 -> e2
        in
        let e = with_range (Static e) ($startpos(e)) in
        App(IfThenElse, [e;e1;e2])
    }

expr_no_range:
  | e=atomic_expr { e }
  | LPAREN e=expr RPAREN eopt=castable_expr {
      match e, eopt with
      | _, None -> e.v
      | {v=Identifier i}, Some e' ->
        let e' = with_range e' $startpos(eopt) in
        App (Cast (None, as_integer_typ i), [e'])
      | _ ->
        error ("Expected a cast expression, got " ^ (print_expr e)) e.range
    }
  | l=expr o=rel_op r=expr %prec DOUBLEEQ
    { App (o, [l;r]) }
  | l=expr AND r=expr
    { App (And, [l;r]) }
  | l=expr OR r=expr
    { App (Or, [l;r]) }
  | l=expr MINUS r=expr
    { App (Minus None, [l;r]) }
  | l=expr PLUS r=expr
    { App (Plus None, [l;r]) }
  | l=expr STAR r=expr
    { App (Mul None, [l;r]) }
  | l=expr DIV r=expr
    { App (Division None, [l;r]) }
  | l=expr REM r=expr
    { App (Remainder None, [l;r]) }
  | l=expr BITWISE_AND r=expr
    { App (BitwiseAnd None, [l;r]) }
  | l=expr BITWISE_XOR r=expr
    { App (BitwiseXor None, [l;r]) }
  | l=expr BITWISE_OR r=expr
    { App (BitwiseOr None, [l;r]) }
  | BITWISE_NOT l=expr
    { App (BitwiseNot None, [l]) }
  | l=expr SHIFT_RIGHT r=expr
    { App (ShiftRight None, [l;r]) }
  | l=expr SHIFT_LEFT r=expr
    { App (ShiftLeft None, [l;r]) }
  | NOT e=expr
    { App (Not, [e]) }
  | SIZEOF LPAREN e=expr RPAREN
    { App (SizeOf, [e]) }
  | e=atomic_or_paren_expr QUESTION e1=atomic_or_paren_expr COLON e2=atomic_or_paren_expr
    {
        App(IfThenElse, [e;e1;e2])
    }
  | IF e=expr LBRACE e1=expr RBRACE e2=else_opt
    {
        let e2 =
            match e2 with
            | None -> with_range (Constant (Bool true)) $startpos
            | Some e2 -> e2
        in
        App(IfThenElse, [e;e1;e2])
    }
  | HASH_IF e=hash_if_body
    { e }
  
  | i=IDENT LPAREN es=arguments RPAREN
    {
       App(Ext i.v.name, es)
    }

expr:
  | e=expr_no_range { with_range e $startpos }

arguments:
  | es=right_flexible_list(COMMA, expr)  { es }

typ_param:
  | e=expr  { Inl e }
  | oe=out_expr  { Inr oe }

qident:
  | i=IDENT    { i }
  | m=IDENT COLON_COLON n=IDENT    { with_range ({modul_name=Some m.v.name; name=n.v.name}) $startpos }

(*
 * NOTE that the kind is being set to KindSpec here
 *   It is set properly in the desugaring phase
 *)
typ_no_range:
  | i=qident { Type_app(i, KindSpec, [], []) }
  | hd=qident LPAREN a=right_flexible_nonempty_list(COMMA, typ_param) RPAREN 
    { Type_app(hd, KindSpec, [], a) }

typ:
  | t=typ_no_range { with_range t $startpos }

maybe_pointer_typ:
  | t=typ { t }
  | t=pointer_typ { t }

pointer_tag:
  | POINTER { false }
  | POINTER QUESTION { true } 

pointer_qual:
  | { (UInt64, false) }
  | LPAREN t=IDENT RPAREN
    { 
      match t.v.name with
      | "UINT32" -> (UInt32, true)
      | "UINT64" -> (UInt64, true)
      | _ -> error "Unexpected pointer qualifier; expected UINT32 or UINT64" t.range
    }

pointer_qualifier:
  | nullable=pointer_tag qual=pointer_qual
    { 
      let (w, d) = qual in
      PQ (w, d, nullable)
    }

pointer_typ:
  | t=maybe_pointer_typ STAR qopt=option_of(pointer_qualifier) 
    { 
      let q =
        match qopt with
        | None -> PQ(UInt64, false, false)
        | Some q -> q 
      in
      with_range (Pointer(t,q)) $startpos }


refinement:
  | LBRACE e=expr RBRACE { e }

array_size:
  | LBRACK e=expr RBRACK                         { (e, ByteArrayByteSize) }
  | LBRACK_BYTESIZE e=expr RBRACK                { (e, ArrayByteSize) }
  | LBRACK_LEQ e=expr RBRACK                     { (e, ArrayByteSizeAtMost) }
  | LBRACK_BYTESIZE_AT_MOST e=expr RBRACK        { (e, ArrayByteSizeAtMost) }
  | LBRACK_EQ e=expr RBRACK                      { (e, ArrayByteSizeSingleElementArray) }
  | LBRACK_SINGLE_ELEMENT_BYTESIZE e=expr RBRACK { (e, ArrayByteSizeSingleElementArray) }

array_annot:
  | { FieldScalar }
  | a=array_size { FieldArrayQualified a }
  | LBRACK_STRING RBRACK { FieldString None }
  | LBRACK_STRING_AT_MOST e=expr RBRACK { FieldString (Some e) }
  | LBRACK_CONSUME_ALL RBRACK { FieldConsumeAll }

bitwidth:
  | COLON i=INT { Inl (with_range (Z.of_string i) $startpos(i)) }

field_action:
  | LBRACE_ONSUCCESS a=action RBRACE { a, false }
  | LBRACE_CHECK a=action RBRACE { a, false }
  | LBRACE_ACT a=action RBRACE { with_range (Action_act a) $startpos(a), false }

probe_field:
| field_name=IDENT EQ e=expr 
  {
    match field_name.v with
    | {modul_name=None; name="length"} -> ("length", e)
    | {modul_name=None; name="destination"} -> ("destination", e)
    | _ -> error "Unexpected field name in probe" field_name.range
  }

with_probe:
| PROBE
  probe_fn_opt=option_of(i=IDENT { i })
  LPAREN fields=separated_list(COMMA, probe_field) RPAREN
  block=option_of(LBRACE a=probe_action RBRACE { a })
    {
      let p = mk_pos $startpos in
      let rng = p,p in
      match probe_fn_opt, block with
      | None, None -> 
        error "Expected either a probe function or a probe action" rng
      | Some _, Some _ ->
        error "Composite probe blocks do not have a probe function" rng
      | Some pf, None -> (
        match fields with 
        | [("length", l); ("destination", {v=Identifier d})] ->
          let p = with_range (probe_action_simple pf l) $startpos in
          { probe_block = p; probe_dest=d; probe_ptr_as_u64=None; probe_dest_sz=l; probe_init=None }
        | _ ->
          error "Expected 'length' and 'destination' fields in probe" rng
      )
      | None, Some a -> (
        match fields with
        | [("length", l); ("destination", {v=Identifier e})] ->
          { probe_dest=e; probe_block=a; probe_ptr_as_u64=None; probe_dest_sz=l; probe_init=None }
        | _ -> error "Expected 'length' and 'destination' fields in probe" rng
      )        
    }

atomic_field:
  | t=maybe_pointer_typ fn=IDENT
      bopt=option_of(bitwidth)
      aopt=array_annot
      c=option_of(refinement)
      a=option_of(field_action)
      p=option_of(with_probe)
    {
        {
         field_dependence=false;
         field_ident=fn;
         field_type=t;
         field_array_opt=aopt;
         field_constraint=c;
         field_bitwidth=bopt;
         field_action=a;
         field_probe=p
        }
    }

anonymous_struct_field:
  | STRUCT LBRACE fields=fields RBRACE fn=IDENT
    {
        RecordField(fields, fn)
    }

anonymous_casetype_field:
  | SWITCH LPAREN i=IDENT RPAREN LBRACE cs=cases RBRACE fn=IDENT
    {
        let e = with_range (Identifier i) ($startpos(i)) in
        SwitchCaseField((e, cs), fn)
    }

maybe_hash_else_fields:
  | HASH_ENDIF                          { None }
  | HASH_ELSE f_else=option_of(fields) HASH_ENDIF { f_else }
  | HASH_ELIF f=static_conditional_body { Some [with_range f ($startpos)] }

static_conditional_body:
  | e=atomic_or_paren_expr f_then=option_of(fields) f_else=maybe_hash_else_fields
    {
        let tt = with_range (Constant (Bool true)) ($startpos(e)) in
        let dummy_identifier = with_range (to_ident' "_") ($startpos(e)) in
        let as_field fopt posn =
            let unit_field = with_range (AtomicField (unit_atomic_field (mk_pos posn, mk_pos posn))) posn in
            let fields =
                match fopt with
                | None -> [unit_field]
                | Some fs -> fs
            in
            match fields with
            | [f] -> f
            | _ -> with_range (RecordField(fields, dummy_identifier)) posn
        in
        let f_then = as_field f_then ($startpos(f_then)) in
        let f_else = as_field f_else ($startpos(f_else)) in
        let case_then = Case (tt, f_then) in
        let case_else = DefaultCase f_else in
        let e = with_range (Static e) ($startpos(e)) in
        SwitchCaseField ((e, [case_then; case_else]), dummy_identifier)
    }
  
static_conditional_field:
  | HASH_IF f=static_conditional_body
    { f }
    
field:
  | f = atomic_field SEMICOLON
    {
      let comms = Ast.comments_buffer.flush () in
      let range = (mk_pos $startpos, mk_pos $startpos) in
      let af' = with_range_and_comments f range comms in
      with_range_and_comments (AtomicField af') range comms
    }
    
  | rf = anonymous_struct_field SEMICOLON
    {
      let comms = Ast.comments_buffer.flush () in
      let range = (mk_pos $startpos, mk_pos $startpos) in
      with_range_and_comments rf range comms
    }

  | cf = anonymous_casetype_field SEMICOLON
    {
      let comms = Ast.comments_buffer.flush () in
      let range = (mk_pos $startpos, mk_pos $startpos) in
      with_range_and_comments cf range comms
    }

  | cf = static_conditional_field
    {
      let comms = Ast.comments_buffer.flush () in
      let range = (mk_pos $startpos, mk_pos $startpos) in
      with_range_and_comments cf range comms
    }

fields:
  | fields=nonempty_list(field)
   { fields }

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

case_pattern:
  | i=qident   { with_range (Identifier i) $startpos(i) }
  | c=constant { with_range (Constant c) $startpos(c) }

case:
  | CASE p=case_pattern COLON f=field { Case (p, f) }
  | DEFAULT COLON f=field { DefaultCase f }

cases:
  | cs=nonempty_list(case) { cs }

attribute:
  | ENTRYPOINT { Entrypoint None }
  | ENTRYPOINT PROBE i=qident LPAREN length=IDENT EQ len=expr RPAREN {
      if length.v.name <> "length" || length.v.modul_name <> None
      then error "Expected 'length' as the first argument to 'entrypoint probe'" length.range;
      Entrypoint (Some ({
        probe_ep_fn = i;
        probe_ep_length = len;
      }))
    }
  | ALIGNED    { Aligned }

attributes:
  |            { [] }
  | a=attribute tl=attributes { a :: tl }

where_opt:
  |              { None }
  | WHERE e=expr { Some e }
  | REQUIRES e=expr { Some e }

(*
 * We are doing some dancing around here for an out expression being an ident
 * The reason is that, an ident is also an expression
 *   and a type parameter can either be an expression or output expression
 * So if an ident appears as a type parameter, we would not know if
 *   it is an expr or out_expr
 *
 * With this dancing around, idents are not out exprs and are always parsed as expressions
 *)
out_expr_no_range:
  | STAR oe=qident                          { OE_star (mk_out_expr_from_ident oe $startpos) }
  | STAR oe=out_expr                        { OE_star oe }
  | BITWISE_AND oe=qident                   { OE_addrof (mk_out_expr_from_ident oe $startpos) }
  | BITWISE_AND oe=out_expr                 { OE_addrof oe }
  | oe=qident RARROW f=qident               { OE_deref (mk_out_expr_from_ident oe $startpos, f) }
  | oe=out_expr RARROW f=qident             { OE_deref (oe, f) }
  | oe=out_expr DOT f=qident                { OE_dot (oe, f) }
  | LPAREN oe=out_expr_no_range RPAREN      { oe }

out_expr:
  | oe=out_expr_no_range    { {out_expr_node = with_range oe $startpos;
                               out_expr_meta = None} }  //metadata is set after typechecking (Binding)

atomic_action:
  | RETURN e=expr SEMICOLON { Action_return e }
  | ABORT SEMICOLON         { Action_abort }
  | FIELD_POS_64 SEMICOLON     { Action_field_pos_64 }
  | FIELD_POS_32 SEMICOLON     { Action_field_pos_32 }
  | FIELD_PTR SEMICOLON     { Action_field_ptr }
  | oe=out_expr EQ FIELD_PTR_AFTER LPAREN e=expr RPAREN SEMICOLON { Action_field_ptr_after(e, oe) }
  | STAR i=IDENT SEMICOLON  { Action_deref i }
  | oe=out_expr EQ e=expr SEMICOLON { Action_assignment(oe, e) }
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

probe_atomic_action:
  | RETURN e=expr SEMICOLON { Probe_action_return e }
  | SKIP_WRITE LPAREN e=expr RPAREN SEMICOLON { Probe_action_skip_write e }
  | SKIP_READ LPAREN e=expr RPAREN SEMICOLON { Probe_action_skip_read e }
  | f=IDENT LPAREN args=arguments RPAREN SEMICOLON { Probe_action_call(f, args) }

probe_action_no_range:
  | a=probe_atomic_action { Probe_atomic_action a }
  | a1=probe_atomic_action a=probe_action { Probe_action_seq (string_as_expr "", with_range (Probe_atomic_action a1) ($startpos(a1)), a) }
  | VAR i=IDENT EQ a1=probe_atomic_action a2=probe_action  { Probe_action_let (string_as_expr "", i, a1, a2) }

probe_action:
  | a=probe_action_no_range { with_range a ($startpos(a)) }

enum_case:
  | i=IDENT            { i, None }
  | i=IDENT EQ j=INT   { i, Some (Inl (Z.of_string j)) }
  | i=IDENT EQ j=IDENT { i, Some (Inr j) }

exported:
  |              { false }
  | EXPORT       { true }

maybe_semi:
  |           { () }
  | SEMICOLON { () }

typedef_pointer_name_opt:
  |                    { None }
  | COMMA STAR k=IDENT { Some k }

out_field_bitwidth_opt:
  | COLON i=INT  { Some (Z.of_string i) }
  |              { None   }

out_field:
  | t=maybe_pointer_typ f=IDENT bopt=out_field_bitwidth_opt  { Out_field_named (f, t, bopt) }
  | STRUCT LBRACE out_flds=right_flexible_nonempty_list(SEMICOLON, out_field) RBRACE
    { Out_field_anon (out_flds, false) }
  | UNION LBRACE out_flds=right_flexible_nonempty_list(SEMICOLON, out_field) RBRACE
    { Out_field_anon (out_flds, true) }

specialize_lhs:
  | POINTER LPAREN STAR RPAREN { () }
  | POINTER LPAREN i=IDENT RPAREN 
    {
      match i.v.name with
      | "UINT64" -> ()
      | _ -> error "Unexpected pointer qualifier; '*'" i.range
    }

decl_no_range:
  | MODULE i=IDENT EQ m=IDENT { ModuleAbbrev (i, m) }
  | DEFINE i=IDENT c=constant { Define (i, None, c) }
  | t=IDENT ENUM i=IDENT LBRACE es=right_flexible_nonempty_list(COMMA, enum_case) RBRACE maybe_semi
    { Enum(with_range (Type_app (t, KindSpec, [], [])) ($startpos(t)), i, es) }
  | b=attributes TYPEDEF t=typ i=IDENT SEMICOLON
    { TypeAbbrev ([], t, i, [], []) }
  | b=attributes TYPEDEF STRUCT i=IDENT ps=parameters w=where_opt
    LBRACE fields=fields
    RBRACE j=IDENT p=typedef_pointer_name_opt SEMICOLON
    {  
        Record(mk_td b i j p, [], ps, w, fields)
    }
  | b=attributes CASETYPE i=IDENT ps=parameters
    LBRACE SWITCH LPAREN e=IDENT RPAREN
           LBRACE cs=cases
           RBRACE
    RBRACE j=IDENT p=typedef_pointer_name_opt SEMICOLON
    {
        let td = mk_td b i j p in
        CaseType(td, [], ps, (with_range (Identifier e) ($startpos(i)), cs))
    }

  | SPECIALIZE LPAREN specialize_lhs COMMA p2=pointer_qualifier RPAREN i=IDENT j=IDENT SEMICOLON
    { let PQ(p2, _, _) = p2 in
      Specialize ([UInt64, p2], i, j) }

  | OUTPUT TYPEDEF STRUCT i=IDENT
    LBRACE out_flds=right_flexible_nonempty_list(SEMICOLON, out_field) RBRACE
    j=IDENT p=typedef_pointer_name_opt SEMICOLON
    {
       let td = mk_td [] i j p in
       OutputType ({out_typ_names=td; out_typ_fields=out_flds; out_typ_is_union=false})
    }

  | EXTERN TYPEDEF STRUCT i=IDENT j=IDENT
    {  let td = mk_td [] i j None in
       ExternType td
    }

  | EXTERN pure=option_of(PURE) ret=typ i=IDENT ps=parameters
    { ExternFn (i, ret, ps, pure <> None) }

  | EXTERN PROBE q=option_of(probe_qualifier) i=IDENT
    { let q = match q with None -> PQWithOffsets | Some q -> q in ExternProbe (i, q) }

probe_qualifier:
  | LPAREN q=IDENT 
          t=option_of(t=qident{ match maybe_as_integer_typ t with
                               | None -> error "Expected integer type" t.range
                               | Some t -> t })
    RPAREN
    {
      match q.v.name, t with
      | "INIT", None -> PQInit
      | "READ", Some t -> PQRead t
      | "WRITE", Some t -> PQWrite t
      | _ -> error "Unexpected probe qualifier" q.range
    }

block_comment_opt:
  |                 {
                      let _ = Ast.comments_buffer.flush () in
                      None
                    }
  | c=BLOCK_COMMENT {  let _ = Ast.comments_buffer.flush () in Some c }

decl:
  | c=block_comment_opt isexported=exported d=decl_no_range {
      let r = mk_pos ($startpos(d)), mk_pos ($startpos(d)) in
      match c with
      | Some c -> mk_decl d r [c] isexported
      | None -> mk_decl d r [] isexported
    }

expr_top:
  | e=expr EOF { e }

type_map:
  | i=IDENT { i, None }
  | i=IDENT AS j=IDENT { i, Some j }

type_refinement:
  | REFINING includes=right_flexible_nonempty_list(COMMA, STRING)
    LBRACE
      type_map=right_flexible_nonempty_list(COMMA, type_map)
    RBRACE
    {
          {
            includes = includes;
            type_map = type_map;
            auto_type_map = []
          }
    }


prog:
  | d=decl r=option_of(type_refinement) EOF
    { [d], r }
  | d=decl p=prog
    {
        let tl, r = p in
        (d :: tl), r
    }

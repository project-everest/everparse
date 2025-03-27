(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Target
(* The abstract syntax for the code produced by 3d *)
open FStar.All
module A = Ast
open Binding

/// The same as A.op, but with `SizeOf` removed
/// and arithmetic operators resolved to their types
noeq
type op =
  | Eq
  | Neq
  | And
  | Or
  | Not
  | Plus of A.integer_type
  | Minus of A.integer_type
  | Mul of A.integer_type
  | Division of A.integer_type
  | Remainder of A.integer_type
  | BitwiseAnd of A.integer_type
  | BitwiseXor of A.integer_type
  | BitwiseOr of A.integer_type
  | BitwiseNot of A.integer_type
  | ShiftRight of A.integer_type
  | ShiftLeft of A.integer_type
  | LT of A.integer_type
  | GT of A.integer_type
  | LE of A.integer_type
  | GE of A.integer_type
  | IfThenElse
  | BitFieldOf: size: int -> order: A.bitfield_bit_order -> op //BitFieldOf(i, from, to)
  | Cast : from:A.integer_type -> to:A.integer_type -> op
  | Ext of string
  | ProbeFunctionName of A.ident

/// Same as A.expr, but with `This` removed
///
/// Carrying around the range information from AST.expr so that we
///   can report errors in terms of their 3d file locations

noeq
type expr' =
  | Constant   : c:A.constant -> expr'
  | Identifier : i:A.ident -> expr'
  | App        : hd:op -> args:list expr -> expr'
  | Record     : type_name:A.ident -> list (A.ident * expr) -> expr'

and expr = expr' & A.range

let rec as_constant n =
  match fst n with
  | Constant (A.Int sw i) ->
    Some (A.Int sw i)
  | App (Cast _from to) [ n ] -> (
    match as_constant n with
    | Some (A.Int _ i) -> Some (A.Int to i)
    | _ -> None
  )
  | App (Plus _) [ n; m ] -> (
    match as_constant n, as_constant m with
    | Some (A.Int sw i), Some (A.Int _ j) -> Some (A.Int sw (i + j))
    | _ -> None
  )
  | App (Minus _) [ n; m ] -> (
    match as_constant n, as_constant m with
    | Some (A.Int sw i), Some (A.Int _ j) -> Some (A.Int sw (i - j))
    | _ -> None
  )
  | App (Mul _) [ n; m ] -> (
    match as_constant n, as_constant m with
    | Some (A.Int sw i), Some (A.Int _ j) -> Some (A.Int sw (i `op_Multiply` j))
    | _ -> None
  )
  | _ -> None

let subst = list (A.ident' & expr)
val subst_expr (s:subst) (e:expr) : expr
let mk_expr (e:expr') = e, A.dummy_range

type lam a = (option A.ident) & a

noeq
type atomic_action =
  | Action_return of expr
  | Action_abort
  | Action_field_pos_64
  | Action_field_pos_32
  | Action_field_ptr
  | Action_field_ptr_after: sz: expr -> write_to:A.ident -> atomic_action
  | Action_field_ptr_after_with_setter: sz: expr -> write_to_field:A.ident -> write_to_object:expr -> atomic_action
  | Action_deref of A.ident
  | Action_assignment : lhs:A.ident -> rhs:expr -> atomic_action
  | Action_call : f:A.ident -> args:list expr -> atomic_action

noeq
type action =
  | Atomic_action of atomic_action
  | Action_seq : hd:atomic_action -> tl:action -> action
  | Action_ite : hd:expr -> then_:action -> else_:action -> action
  | Action_let : i:A.ident -> a:atomic_action -> k:action -> action
  | Action_act : action -> action
  
(* A subset of F* types that the translation targets *)
noeq
type atomic_probe_action =
  | Atomic_probe_and_copy :
      bytes_to_read : expr ->
      probe_fn: A.ident ->
      atomic_probe_action
  | Atomic_probe_and_read :
      reader : A.ident ->
      atomic_probe_action
  | Atomic_probe_write_at_offset :
      v:expr ->
      writer : A.ident ->
      atomic_probe_action
  | Atomic_probe_call_pure :
      f: A.ident ->
      args: list expr ->
      atomic_probe_action
  | Atomic_probe_skip_read:
      n:expr ->
      atomic_probe_action
  | Atomic_probe_skip_write:
      n:expr ->
      atomic_probe_action
  | Atomic_probe_init:
      f:A.ident ->
      n:expr ->
      atomic_probe_action
  | Atomic_probe_return:
      v:expr ->
      atomic_probe_action
  | Atomic_probe_fail:
      atomic_probe_action

noeq
type probe_action =
  | Probe_action_atomic :
      atomic_probe_action ->
      probe_action
  | Probe_action_var :
      expr ->
      probe_action
  | Probe_action_simple:
      bytes_to_read : expr ->
      probe_fn: A.ident ->
      probe_action
  | Probe_action_seq:
      probe_action ->
      probe_action ->
      probe_action
  | Probe_action_let:
      i:A.ident ->
      m1: atomic_probe_action ->
      m2: probe_action ->
      probe_action
  | Probe_action_ite:
      cond: expr ->
      m1: probe_action ->
      m2: probe_action ->
      probe_action
  
noeq
type typ =
  | T_false    : typ
  | T_app      : hd:A.ident -> A.t_kind -> args:list index -> typ
  | T_nlist    : elt: typ -> bytesize: expr -> typ
  | T_pair     : fst: typ -> snd: typ -> typ
  | T_dep_pair : dfst:typ -> dsnd:(A.ident & typ) -> typ
  | T_refine   : base:typ -> refinement:lam expr -> typ
  | T_if_else  : e:expr -> t:typ -> f:typ -> typ
  | T_pointer  : typ -> pointer_size:A.integer_type -> typ
  | T_with_action: typ -> action -> typ
  | T_with_dep_action: typ -> a:lam action -> typ
  | T_with_comment: typ -> A.comments -> typ
  | T_with_probe: 
      content_typ:typ ->
      pointer_size:A.pointer_size_t ->
      probe_fn:probe_action ->
      dest:A.ident ->
      as_u64:A.ident ->
      init:A.ident ->
      dest_sz:expr ->
      typ
  | T_arrow : list typ -> typ -> typ

(* An index is an F* type or an expression
   -- we reuse Ast expressions for this
*)
and index = either typ expr

let field_typ = typ

type param = A.ident & typ

let mk_subst (l:list param) (args:list expr) : ML (option subst) =
  if List.Tot.length l <> List.Tot.length args
  then None
  else (
    Some (List.map2 #param (fun (i, t) e -> i.v, e) l args)
  )

noeq
type struct_field = {
  sf_dependence: bool;
  sf_ident: A.ident;
  sf_typ: field_typ
}

type field = struct_field

noeq
type typedef_body =
  | TD_abbrev : typ -> typedef_body
  | TD_struct : list field  -> typedef_body

noeq
type probe_entrypoint = {
  probe_ep_fn: A.ident;
  probe_ep_length: expr;
}

noeq
type typedef_name = {
  td_name:A.ident;
  td_params:list param;
  td_entrypoint_probes: list probe_entrypoint;
  td_entrypoint:bool;
  td_noextract:bool;
}
type typedef = typedef_name & typedef_body

////////////////////////////////////////////////////////////////////////////////

noeq
type parser_kind' =
  | PK_return
  | PK_impos
  | PK_base     : hd:A.ident -> parser_kind'
  | PK_list     : elt_kind:parser_kind -> option nat -> parser_kind'
  | PK_t_at_most: parser_kind'
  | PK_t_exact  : parser_kind'
  | PK_filter   : k:parser_kind -> parser_kind'
  | PK_and_then : k1:parser_kind -> k2:parser_kind -> parser_kind'
  | PK_glb      : k1:parser_kind -> k2:parser_kind -> parser_kind'
  | PK_string   : parser_kind'

and parser_kind = {
  pk_kind : parser_kind';
  pk_weak_kind : A.weak_kind ;
  pk_nz: bool;
}

val expr_eq (e1 e1:expr) : bool
val exprs_eq (es1 es1:list expr) : bool
val fields_eq (fs1 fs2:list (A.ident & expr)) : bool
val parser_kind_eq (k k':parser_kind) : bool

noeq
type parser' =
  | Parse_return    : v:expr -> parser'
  | Parse_app       : hd:A.ident -> args:list index -> parser'
  | Parse_nlist     : t_size_constant:bool -> n:expr -> t:parser -> parser'
  | Parse_t_at_most : n:expr -> t:parser -> parser'
  | Parse_t_exact   : n:expr -> t:parser -> parser'
  | Parse_pair      : n1: A.ident -> p_is_const: bool -> p:parser -> q_is_const: bool -> q:parser -> parser' // p_is_const, q_is_const record whether p and q are total compile-time constant size parsers
  | Parse_dep_pair  : n1: A.ident -> p:parser -> k:lam parser -> parser'
  | Parse_dep_pair_with_refinement: n1: A.ident -> dfst:parser -> refinement:lam expr -> dsnd:lam parser -> parser'
  | Parse_dep_pair_with_action: dfst:parser -> a:lam action -> dsnd:lam parser -> parser'
  | Parse_dep_pair_with_refinement_and_action: n1: A.ident -> dfst:parser -> refinement:lam expr -> a:lam action -> dsnd:lam parser -> parser'
  | Parse_map       : p:parser -> f:lam expr -> parser'
  | Parse_refinement: n:A.ident -> p:parser -> f:lam expr -> parser'
  | Parse_refinement_with_action : n:A.ident -> p:parser -> f:lam expr -> a:lam action -> parser'
  | Parse_with_dep_action : name:A.ident -> p:parser -> a:lam action -> parser'
  | Parse_with_action: name: A.ident -> p:parser -> a:action -> parser'
  | Parse_weaken_left: p:parser ->  k:parser_kind -> parser'
  | Parse_weaken_right: p:parser ->  k:parser_kind -> parser'
  | Parse_if_else   : e:expr -> parser -> parser -> parser'
  | Parse_impos     : parser'
  | Parse_with_comment: p:parser -> c:A.comments -> parser'
  | Parse_string    : p:parser -> zero:expr -> parser'
  | Parse_with_probe :
      p:parser ->
      pointer_size:A.pointer_size_t ->
      probe:probe_action ->
      dest:A.ident ->
      as_u64:A.ident ->
      probe_init:A.ident ->
      dest_sz:expr ->
      parser'
  
and parser = {
  p_kind:parser_kind;
  p_typ:typ;
  p_parser:parser';
  p_typename: A.ident;
  p_fieldname: string;
}

noeq
type reader =
  | Read_u8
  | Read_u16
  | Read_u32
  | Read_filter : r:reader -> f:lam expr -> reader
  | Read_app : hd:A.ident -> args:list index -> reader

////////////////////////////////////////////////////////////////////////////////

noeq
type type_decl = {
  decl_name: typedef_name;
  decl_typ: typedef_body;
  decl_parser: parser;
  decl_is_enum : bool
}

let definition = A.ident * list param * typ * expr

let assumption = A.ident * typ

type decl_attributes = {
  is_hoisted: bool;
  is_entrypoint: bool;
  is_exported: bool;
  is_if_def: bool;
  should_inline: bool;
  comments: list string;
}


/// Output expressions, mostly a mirror image of the AST output expressions,
///   except the types in the metadata are Target types

noeq
type output_expr' =
  | T_OE_id : A.ident -> output_expr'
  | T_OE_star : output_expr -> output_expr'
  | T_OE_addrof : output_expr -> output_expr'
  | T_OE_deref : output_expr -> A.ident -> output_expr'
  | T_OE_dot : output_expr -> A.ident -> output_expr'

and output_expr = {
  oe_expr : output_expr';
  oe_bt : typ;
  oe_t : typ;
  oe_bitwidth: option int
}

(*
 * For every output expression in the 3d program,
 *   we add a new decl to the target AST
 *
 * This decl will then be used to emit F* and C code for output types
 *)

noeq
type probe_qualifier =
  | PQSimple
  | PQWithOffsets
  | PQInit
  | PQRead of A.integer_type
  | PQWrite of A.integer_type


noeq
type decl' =
  | Assumption : assumption -> decl'
  | Definition : definition -> decl' //the bool marks it for inline_for_extraction
  | Type_decl  : type_decl -> decl'
  | Probe_function :
      A.ident ->
      params:list param ->
      probe_action ->
      decl'
  | Output_type: A.out_typ -> decl'  //output types specifications, we keep them if we need to print them to C

  | Output_type_expr : output_expr -> is_get:bool -> decl'  //is_get boolean indicates that the output expression appears in a getter position, i.e. in a type parameter, it is false when the output expression is an assignment action lhs

  | Extern_type : A.ident -> decl'
  | Extern_fn : A.ident -> typ -> list param -> pure:bool -> decl'
  | Extern_probe : A.ident -> probe_qualifier -> decl'

type decl = decl' * decl_attributes

type decls = list decl
val has_output_types (ds:list decl) : bool
val has_output_type_exprs (ds:list decl) : bool
val has_extern_types (ds:list decl) : bool
val has_extern_functions (ds:list decl) : bool
val has_extern_probes (ds:list decl) : bool
val has_external_api (ds:list decl) : bool
val error_handler_decl : decl
val maybe_mname_prefix (mname:string) (i:A.ident) : string
val print_ident (i:A.ident) : string
val print_maybe_qualified_ident (mname:string) (i:A.ident) : ML string
val print_expr (mname:string) (e:expr) : ML string
val print_typ (mname:string) (t:typ) : ML string
val print_kind (mname:string) (k:parser_kind) : Tot string
val print_params (mname:string) (ps:list param) : ML string
val print_action (mname:string) (a:action) : ML string
val print_probe_action  (mname:string) (a:probe_action) : ML string
val print_definition (mname:string) (d:decl { Definition? (fst d)} ) : ML string
val print_assumption (mname:string) (d:decl { Assumption? (fst d) } ) : ML string
val wrapper_name (modul: string) (fn: string) : ML string
val validator_name (modul: string) (fn: string) : ML string
type produce_everparse_error = | ProduceEverParseError
type opt_produce_everparse_error = option produce_everparse_error
val print_c_entry (_: opt_produce_everparse_error) (modul: string) (env: global_env) (ds:list decl)
  : ML (string & string)

(*
 * The following 3 functions are used by Translate to get action names
 *   for output expressions
 *)

val output_setter_name (lhs:output_expr) : ML string
val output_getter_name (lhs:output_expr) : ML string
val output_base_var (lhs:output_expr) : ML A.ident


(*
 * Used by Main
 *)
 
val print_external_types_fstar_interpreter (modul:string) (ds:decls) : ML string
val print_external_api_fstar_interpreter (modul:string) (ds:decls) : ML string
val print_out_exprs_c (modul:string) (ds:decls) : ML string
val print_output_types_defs (modul:string) (ds:decls) : ML string

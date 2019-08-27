module Target
open FStar.All
module A = Ast
open Binding

/// The same as A.op, but with `SizeOf` removed
type op =
  | Eq
  | And
  | Or
  | Not
  | Plus
  | Minus
  | LT
  | GT
  | LE
  | GE
  | Ext of string
/// Same as A.expr, but with `This` removed
noeq
type expr =
  | Constant   : c:A.constant -> expr
  | Identifier : i:A.ident -> expr
  | App        : hd:op -> args:list expr -> expr
  | Record     : type_name:A.ident -> list (A.ident * expr) -> expr

type lam a = A.ident & a

(* A subset of F* types that the translation targets *)
noeq
type typ =
  | T_app      : hd:A.ident -> args:list index -> typ
  | T_dep_pair : dfst:typ -> dsnd:lam typ -> typ
  | T_refine   : base:typ -> refinement:lam expr -> typ
  | T_match    : scrutinee:expr -> list case -> typ

(* One arm of a match *)
and case = {
  pattern: expr;
  branch: typ
}

(* An index is an F* type or an expression
   -- we reuse Ast expressions for this
*)
and index = either typ expr

type param = A.ident & typ
noeq
type struct_field = {
  sf_dependence: bool;
  sf_ident: A.ident;
  sf_typ: typ
}
noeq
type field =
  | Field : struct_field -> field
  | FieldComment : string -> field
type comment = string

noeq
type typedef_body =
  | TD_abbrev : typ -> typedef_body
  | TD_struct : list field  -> typedef_body

type typedef_name = A.ident & list param
type typedef = typedef_name & typedef_body

////////////////////////////////////////////////////////////////////////////////

type parser_kind = unit

noeq
type parser' =
  | Parse_app       : hd:A.ident -> args:list index -> parser'
  | Parse_return    : v:expr -> parser'
  | Parse_seq       : p:parser -> q:parser -> parser'
  | Parse_and_then  : p:parser -> k:lam parser -> parser'
  | Parse_map       : p:parser -> f:lam expr -> parser'
  | Parse_filter    : p:parser -> f:lam expr -> parser'
  | Parse_with_kind : p:parser -> k:parser_kind -> parser'
  | Parse_cases     : e:expr -> list (expr * parser) -> parser'

and parser = {
  p_kind:parser_kind;
  p_typ:typ;
  p_parser:parser'
}

noeq
type reader =
  | Read_u8
  | Read_u16
  | Read_u32
  | Read_filter : r:reader -> f:lam expr -> reader

noeq
type validator' =
  | Validate_app      : hd:A.ident -> args:list index -> validator'
  | Validate_return   : validator'
  | Validate_seq      : v1:validator -> v2:validator -> validator'
  | Validate_and_read : v:validator -> r:reader -> k:lam validator -> validator'
  | Validate_map      : p:validator -> f:lam expr -> validator'
  | Validate_filter   : v:validator -> r:reader -> f:lam expr -> validator'
  | Validate_filter_and_read : v:validator -> r:reader -> f:lam expr -> k:lam validator -> validator'
  | Validate_with_kind : v:validator -> validator'
  | Validate_cases    : e:expr -> list (expr * validator) -> validator'

and validator = {
  v_parser:parser;
  v_validator:validator'
}

////////////////////////////////////////////////////////////////////////////////

noeq
type type_decl = {
  decl_name: typedef_name;
  decl_typ: typedef_body;
  decl_parser: parser;
  decl_validator: validator
}

let definition = A.ident * A.constant

noeq
type decl =
  | Comment of string
  | Definition of definition
  | Type_decl of type_decl

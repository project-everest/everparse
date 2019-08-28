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
  | Parse_dep_pair  : p:parser -> k:lam parser -> parser'
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

////////////////////////////////////////////////////////////////////////////////

let print_ident (i:A.ident) =
  let open A in
  match String.list_of_string i.v with
  | [] -> i.v
  | c0::_ ->
    if FStar.Char.lowercase c0 = c0
    then i.v
    else "_"^i.v

//  if String.starts_with i.v
let print_op = function
  | Eq -> "="
  | And -> "&&"
  | Or -> "||"
  | Not -> "not"
  | Plus -> "+"
  | Minus -> "-"
  | LT -> "<"
  | GT -> ">"
  | LE -> "<="
  | GE -> ">="
  | Ext s -> s

let rec print_expr (e:expr) : Tot string =
  match e with
  | Constant c ->
    A.print_constant c
  | Identifier i ->
    print_ident i
  | Record nm fields ->
    Printf.sprintf "{ %s }" (String.concat "; " (print_fields fields))
  | App Eq [e1; e2] ->
    Printf.sprintf "(%s = %s)" (print_expr e1) (print_expr e2)
  | App And [e1; e2] ->
    Printf.sprintf "(%s && %s)" (print_expr e1) (print_expr e2)
  | App Or [e1; e2] ->
    Printf.sprintf "(%s || %s)" (print_expr e1) (print_expr e2)
  | App Or [e1; e2] ->
    Printf.sprintf "(%s || %s)" (print_expr e1) (print_expr e2)
  | App Not [e1] ->
    Printf.sprintf "(not %s)" (print_expr e1)
  | App Plus [e1; e2] ->
    Printf.sprintf "(%s + %s)" (print_expr e1) (print_expr e2)
  | App Minus [e1; e2] ->
    Printf.sprintf "(%s - %s)" (print_expr e1) (print_expr e2)
  | App LT [e1; e2] ->
    Printf.sprintf "(%s < %s)" (print_expr e1) (print_expr e2)
  | App GT [e1; e2] ->
    Printf.sprintf "(%s > %s)" (print_expr e1) (print_expr e2)
  | App LE [e1; e2] ->
    Printf.sprintf "(%s <= %s)" (print_expr e1) (print_expr e2)
  | App GE [e1; e2] ->
    Printf.sprintf "(%s >= %s)" (print_expr e1) (print_expr e2)
  | App op [] ->
    print_op op
  | App op es ->
    Printf.sprintf "(%s %s)" (print_op op) (String.concat " " (print_exprs es))

and print_exprs (es:list expr) : Tot (list string) =
  match es with
  | [] -> []
  | hd::tl -> print_expr hd :: print_exprs tl

and print_fields (fs:_) : Tot (list string) =
  match fs with
  | [] -> []
  | (x, e)::tl ->
    Printf.sprintf "%s = %s" (print_ident x) (print_expr e)
    :: print_fields tl

let rec print_typ (t:typ) : Tot string (decreases t) =
  match t with
  | T_app hd args ->
    Printf.sprintf "(%s %s)"
      (print_ident hd)
      (String.concat " " (print_indexes args))
  | T_dep_pair t1 (x, t2) ->
    Printf.sprintf "(%s:%s & %s)"
      (print_ident x)
      (print_typ t1)
      (print_typ t2)
  | T_refine t1 (x, e2) ->
    Printf.sprintf "(%s:%s{%s})"
      (print_ident x)
      (print_typ t1)
      (print_expr e2)
  | T_match sc cases ->
    let cases = print_cases (print_expr sc) cases in
    Printf.sprintf "(%s\nelse False)"
                   (String.concat "\nelse " cases)

and print_cases hd (cs:list case) : Tot (list string) (decreases cs) =
  match cs with
  | [] -> []
  | c::cs ->
    Printf.sprintf "if (%s = %s) then %s" hd (print_expr c.pattern) (print_typ c.branch)::print_cases hd cs

and print_indexes (is:list index) : Tot (list string) (decreases is) =
  match is with
  | [] -> []
  | Inl t::is -> print_typ t::print_indexes is
  | Inr e::is -> print_expr e::print_indexes is


let rec print_parser (p:parser) : Tot string (decreases p) =
  match p.p_parser with
  | Parse_app hd args ->
    Printf.sprintf "parse_%s %s" (print_ident hd) (String.concat " " (print_indexes args))
  | Parse_return v ->
    Printf.sprintf "parseReturn %s" (print_expr v)
  | Parse_seq p1 p2 ->
    Printf.sprintf "(%s `seq` %s)" (print_parser p1) (print_parser p2)
  | Parse_dep_pair p1 (x, p2) ->
    Printf.sprintf "(%s `dep_pair` (fun %s -> %s))" (print_parser p1) (print_ident x) (print_parser p2)
  | Parse_map p1 (x, e) ->
    Printf.sprintf "(%s `map` (fun %s -> %s))" (print_parser p1) (print_ident x) (print_expr e)
  | Parse_filter p1 (x, e) ->
    Printf.sprintf "(%s `filter` (fun %s -> %s))" (print_parser p1) (print_ident x) (print_expr e)
  | Parse_with_kind p1 k ->
    Printf.sprintf "weaken_kind %s" (print_parser p1)
  | Parse_cases e cases ->
    let e = print_expr e in
    Printf.sprintf "(%s\nelse false_elim())"
      (String.concat "\n else " (print_parser_cases e cases))

and print_parser_cases hd (cases:list (expr * parser)) : Tot (list string) (decreases cases) =
  match cases with
  | [] -> []
  | (e, p)::cases ->
    Printf.sprintf "if (%s = %s) then %s"
      hd (print_expr e) (print_parser p)
    :: print_parser_cases hd cases

let rec print_validator (v:validator) : Tot string =
  match v.v_validator with
  | Validate_app hd args ->
    Printf.sprintf "validate_%s %s" (print_ident hd) (String.concat " " (print_indexes args))
  | Validate_return ->
    Printf.sprintf "validateReturn"
  | Validate_seq p1 p2 ->
    Printf.sprintf "(%s `v_seq` %s)" (print_validator p1) (print_validator p2)
  | Validate_and_read p1 _ (x, p2) ->
    Printf.sprintf "(%s `v_and_read` (fun %s -> %s))" (print_validator p1) (print_ident x) (print_validator p2)
  | Validate_map p1 (x, e) ->
    Printf.sprintf "(%s `v_map` (fun %s -> %s))" (print_validator p1) (print_ident x) (print_expr e)
  | Validate_filter p1 _ (x, e) ->
    Printf.sprintf "(%s `v_filter` (fun %s -> %s))" (print_validator p1) (print_ident x) (print_expr e)
  | Validate_filter_and_read p1 _ (x, e) (y, v) ->
    Printf.sprintf "(v_filter_and_read %s (fun %s -> %s) (fun %s -> %s))"
      (print_validator p1)
      (print_ident x)
      (print_expr e)
      (print_ident y)
      (print_validator v)
  | Validate_with_kind p1 ->
    Printf.sprintf "v_weaken_kind %s" (print_validator p1)
  | Validate_cases e cases ->
    Printf.sprintf "(match %s with\n%s)"
      (print_expr e)
      (String.concat "\n" (print_validator_cases cases))

and print_validator_cases (cases:list (expr * validator)) : Tot (list string) =
  match cases with
  | [] -> []
  | (e, p)::cases ->
    Printf.sprintf "| %s -> %s" (print_expr e) (print_validator p)
    :: print_validator_cases cases

let print_typedef_name (tdn:typedef_name) =
  let name, params = tdn in
  Printf.sprintf "%s %s"
    (print_ident name)
    (String.concat " "
      (List.Tot.map (fun (id, t) -> Printf.sprintf "(%s:%s)" (print_ident id) (print_typ t)) params))

let print_typedef_typ (tdn:typedef_name) =
  let name, params = tdn in
  Printf.sprintf "%s %s"
    (print_ident name)
    (String.concat " "
      (List.Tot.map (fun (id, t) -> (print_ident id)) params))

let print_typedef_body (b:typedef_body) =
  match b with
  | TD_abbrev t -> print_typ t
  | TD_struct fields ->
    let print_field (f:field) : Tot string =
      match f with
      | FieldComment s -> s
      | Field sf ->
        Printf.sprintf "%s : %s%s"
          (print_ident sf.sf_ident)
          (print_typ sf.sf_typ)
          (if sf.sf_dependence then " (*dep*)" else "")
    in
    let fields = String.concat ";\n" (List.Tot.map print_field fields) in
    Printf.sprintf "{\n%s\n}" fields

let print_decl (d:decl) : Tot string =
  match d with
  | Comment c -> c
  | Definition (x, c) ->
    Printf.sprintf "let %s = %s\n" (print_ident x) (A.print_constant c)
  | Type_decl td ->
    Printf.sprintf "type %s = %s\n"
      (print_typedef_name td.decl_name)
      (print_typedef_body td.decl_typ)
    `strcat`
    Printf.sprintf "let parse_%s : parser (%s) = %s\n"
      (print_typedef_name td.decl_name)
      (print_typedef_typ td.decl_name)
      (print_parser td.decl_parser)
    // `strcat`
    // Printf.sprintf "let validate_%s : validator (parse_%s) = %s\n"
    //   (print_typedef_name td.decl_name)
    //   (print_typedef_name td.decl_name)
    //   (print_validator td.decl_validator)

let print_decls (ds:list decl) =
  Printf.sprintf
    "module Rndis\n\
     open Prelude\n\
     %s"
     (String.concat "\n" (List.Tot.map print_decl ds))

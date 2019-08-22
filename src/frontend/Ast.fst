module Ast
open FStar.All

type pos = {
  filename: string;
  line:int;
  col:int
}

let range = pos * pos

let string_of_pos p =
  Printf.sprintf "%s:(%d,%d)" p.filename p.line p.col

let dummy_pos = {
  filename="";
  line=0;
  col=0;
}

noeq
type withrange 'a = {
  v:'a;
  range:range
}

type ident' = string
let ident = withrange ident'

type constant =
  | Int of int
  | XInt of string

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
  | SizeOf

type expr' =
  | Constant of constant
  | Identifier of ident
  | This
  | App : op -> list expr -> expr'

and expr = withrange expr'

type typ' =
  | Type_app : ident -> list expr -> typ'
and typ = withrange typ'

type param = typ & ident

type struct_field = {
  field_dependence:bool;
  field_ident:ident;
  field_type:typ;
  field_constraint:option expr;
}

type field' =
 | Field of struct_field
 | FieldComment of string
and field = withrange field'
type case = expr & field
type switch_case = expr & list case

type typedef_names = {
  typedef_name: ident;
  typedef_abbrev: ident;
  typedef_ptr_abbrev: ident
}

type decl' =
  | Comment of string
  | Define: ident -> constant -> decl'
  | Enum: typ -> ident -> list ident -> decl'
  | Record: typedef_names -> list param -> list field -> decl'
  | CaseType: typedef_names -> list param -> switch_case -> decl'
and decl = withrange decl'

let rec print_expr (e:expr) : Tot string =
  match e.v with
  | Constant (Int i) ->
    Printf.sprintf "%d" i
  | Identifier i ->
    i.v
  | This ->
    "this"
  | App Eq [e1; e2] ->
    Printf.sprintf "(%s = %s)" (print_expr e1) (print_expr e2)
  | App And [e1; e2] ->
    Printf.sprintf "(%s && %s)" (print_expr e1) (print_expr e2)
  | App Or [e1; e2] ->
    Printf.sprintf "(%s || %s)" (print_expr e1) (print_expr e2)
  | _ -> "??"

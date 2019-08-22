module Ast
open FStar.All

type ident = string

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

type expr =
  | Constant of constant
  | Identifier of ident
  | This
  | App : op -> list expr -> expr

type typ =
  | Type_name of string
  | Type_app : string -> list expr -> typ

type param = typ & ident

type struct_field = {
  field_ident:string;
  field_type:typ;
  field_constraint:option expr;
}

type field =
 | Field of struct_field
 | FieldComment of string

type atomic_type = ident

type case = ident & field
type switch_case = ident & list case

type typedef_names = {
  typedef_name: ident;
  typedef_abbrev: ident;
  typedef_ptr_abbrev: ident
}

type decl =
  | Comment of string
  | Define: ident -> constant -> decl
  | Enum: atomic_type -> ident -> list ident -> decl
  | Record: typedef_names -> list param -> list field -> decl
  | CaseType: typedef_names -> list param -> switch_case -> decl

let rec print_expr (e:expr) : Tot string =
  match e with
  | Constant (Int i) ->
    Printf.sprintf "%d" i
  | Identifier i ->
    i
  | This ->
    "this"
  | App Eq [e1; e2] ->
    Printf.sprintf "(%s = %s)" (print_expr e1) (print_expr e2)
  | App And [e1; e2] ->
    Printf.sprintf "(%s && %s)" (print_expr e1) (print_expr e2)
  | App Or [e1; e2] ->
    Printf.sprintf "(%s || %s)" (print_expr e1) (print_expr e2)
  | _ -> "??"

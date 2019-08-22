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

noeq type withrange 'a = {
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

noeq
type expr' =
  | Constant of constant
  | Identifier of ident
  | This
  | App : op -> list expr -> expr'

and expr = withrange expr'

noeq
type typ' =
  | Type_app : ident -> list expr -> typ'
and typ = withrange typ'

type param = typ & ident

noeq
type struct_field = {
  field_dependence:bool;
  field_ident:ident;
  field_type:typ;
  field_constraint:option expr;
}

noeq
type field' =
 | Field of struct_field
 | FieldComment of string
and field = withrange field'
type case = expr & field
type switch_case = expr & list case

noeq
type typedef_names = {
  typedef_name: ident;
  typedef_abbrev: ident;
  typedef_ptr_abbrev: ident
}

noeq
type decl' =
  | Comment of string
  | Define: ident -> constant -> decl'
  | Enum: typ -> ident -> list ident -> decl'
  | Record: typedef_names -> list param -> list field -> decl'
  | CaseType: typedef_names -> list param -> switch_case -> decl'
and decl = withrange decl'

let rec eq_expr (e1 e2:expr) : Tot bool (decreases e1) =
  match e1.v, e2.v with
  | Constant i, Constant j -> i = j
  | Identifier i, Identifier j -> i.v = j.v
  | This, This -> true
  | App op1 es1, App op2 es2 ->
    op1 = op2
    && eq_exprs es1 es2
  | _ -> false

and eq_exprs (es1 es2:list expr) : Tot bool =
  match es1, es2 with
  | [], [] -> true
  | hd1::es1, hd2::es2 -> eq_expr hd1 hd2 && eq_exprs es1 es2
  | _ -> false

let eq_typ (t1 t2:typ) : Tot bool =
  let Type_app hd1 es1, Type_app hd2 es2 = t1.v, t2.v in
  hd1.v = hd2.v
  && eq_exprs es1 es2


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

let print_typ t : ML string =
  let Type_app i es = t.v in
  match es with
  | [] -> i.v
  | _ ->
    Printf.sprintf "%s(%s)"
      i.v
      (String.concat ", " (List.map print_expr es))

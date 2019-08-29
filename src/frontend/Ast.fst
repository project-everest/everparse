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
  | Bool of bool

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
 //OffsetOf

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

let size = int

noeq
type struct_field = {
  field_dependence:bool;
  field_size:option size;
  field_ident:ident;
  field_type:typ;
  field_array_opt:option expr;
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
  | TypeAbbrev: typ -> ident -> decl'
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

let dummy_range = dummy_pos, dummy_pos
let with_range x r = { v = x; range = r}
let with_dummy_range x = with_range x dummy_range
let tbool = with_dummy_range (Type_app (with_dummy_range "Bool") [])
let tuint32 = with_dummy_range (Type_app (with_dummy_range "UINT32") [])
let tunknown = with_dummy_range (Type_app (with_dummy_range "?") [])
let pos_of_ident i = i.range

let print_constant (c:constant) =
  match c with
  | Int i -> Printf.sprintf "%dul" i
  | XInt x -> Printf.sprintf "%s" x
  | Bool b -> Printf.sprintf "%b" b

let print_ident (i:ident) = i.v

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
  | SizeOf -> "sizeof"

let rec print_expr (e:expr) : Tot string =
  match e.v with
  | Constant c ->
    print_constant c
  | Identifier i ->
    print_ident i
  | This ->
    "this"
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
  | App SizeOf [e1] ->
    Printf.sprintf "(sizeof %s)" (print_expr e1)
  | App op es ->
    Printf.sprintf "(?? %s %s)" (print_op op) (String.concat ", " (print_exprs es))

and print_exprs (es:list expr) : Tot (list string) =
  match es with
  | [] -> []
  | hd::tl -> print_expr hd :: print_exprs tl

let print_typ t : ML string =
  let Type_app i es = t.v in
  match es with
  | [] -> i.v
  | _ ->
    Printf.sprintf "%s(%s)"
      i.v
      (String.concat ", " (List.map print_expr es))

let print_params (ps:list param) =
  match ps with
  | [] -> ""
  | _ ->
    Printf.sprintf "(%s)"
      (String.concat ", "
        (ps |> List.map
          (fun (t, p) ->
             Printf.sprintf "%s %s"
               (print_typ t)
               (print_ident p))))

let print_opt (o:option 'a) (f:'a -> string) : string =
  match o with
  | None -> ""
  | Some x -> f x

let print_field (f:field) : ML string =
  match f.v with
  | FieldComment c -> c
  | Field sf ->
    Printf.sprintf "%s%s %s%s%s;"
      (if sf.field_dependence then "dependent " else "")
      (print_typ sf.field_type)
      (print_ident sf.field_ident)
      (print_opt sf.field_array_opt (fun e -> Printf.sprintf "[%s]" (print_expr e)))
      (print_opt sf.field_constraint (fun e -> Printf.sprintf "{%s}" (print_expr e)))

let print_switch_case (s:switch_case) : ML string =
  let head, cases = s in
  let print_case (c:case) : ML string =
    Printf.sprintf "case %s: %s;"
      (print_expr (fst c))
      (print_field (snd c))
  in
  Printf.sprintf "switch (%s) {\n
                  %s\n\
                 }"
                 (print_expr head)
                 (String.concat "\n" (List.map print_case cases))

let print_decl (d:decl) : ML string =
  match d.v with
  | Comment s -> s
  | Define i c ->
    Printf.sprintf "#define %s %s;" (print_ident i) (print_constant c)
  | TypeAbbrev t i ->
    Printf.sprintf "typedef %s %s;" (print_typ t) (print_ident i)
  | Enum t i ls ->
    Printf.sprintf "%s enum %s {\n\
                       %s \n\
                   }"
                   (print_typ t)
                   i.v
                   (String.concat "\n" (List.map print_ident ls))
  | Record td params fields ->
    Printf.sprintf "typedef struct %s%s {\n\
                        %s \n\
                    } %s, *%s"
                    td.typedef_name.v
                    (print_params params)
                    (String.concat "\n" (List.map print_field fields))
                    td.typedef_abbrev.v
                    td.typedef_ptr_abbrev.v
  | CaseType td params switch_case ->
    Printf.sprintf "casetype %s%s {\n\
                        %s \n\
                    } %s, *%s"
                    td.typedef_name.v
                    (print_params params)
                    (print_switch_case switch_case)
                    td.typedef_abbrev.v
                    td.typedef_ptr_abbrev.v

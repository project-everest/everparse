type name = string

type typ =
| U32

type constant =
| Int of int

type param = name * typ

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
| This
| Constant of constant

type expr =
  | Expr of op * expr list

type field = {
  field_name:string;
  field_type:typ;
  field_constraint:expr;
}

type decl =
| Comment of string
| Define of name * constant
| Record of param list * field list

let rec print_expr e =
  let Expr (op, es) = e in
  match op, es with
  | Eq, [e1; e2] -> 
    Printf.sprintf "(%s = %s)" (print_expr e1) (print_expr e2)
  | And, [e1; e2] -> 
    Printf.sprintf "(%s && %s)" (print_expr e1) (print_expr e2)  
  | Or, [e1; e2] -> 
    Printf.sprintf "(%s || %s)" (print_expr e1) (print_expr e2)
  | Constant (Int i), [] -> 
    Printf.sprintf "%d" i
  | _ -> "??"

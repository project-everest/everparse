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
| This

type expr =
| Constant of constant
| Identifier of ident
| This
| App of op * expr list

type typ =
| Type_name of string
| Type_app of string * expr list

type param = typ * ident

type struct_field = {
  field_ident:string;
  field_type:typ;
  field_constraint:expr option;
}

type field = 
 | Field of struct_field
 | FieldComment of string

type atomic_type = ident

type case = ident * field
type switch_case = ident * case list

type decl =
| Comment of string
| Define of ident * constant
| Enum of atomic_type * ident * ident list
| Record of ident * param list * field list * ident * ident
| CaseType of ident * param list * switch_case * ident * ident

let rec print_expr e =
  match e with
  | Constant (Int i) -> 
    Printf.sprintf "%d" i
  | Identifier i -> 
    i
  | This -> 
    "this"
  | App (Eq, [e1; e2]) -> 
    Printf.sprintf "(%s = %s)" (print_expr e1) (print_expr e2)
  | App (And, [e1; e2]) -> 
    Printf.sprintf "(%s && %s)" (print_expr e1) (print_expr e2)  
  | App (Or, [e1; e2]) -> 
    Printf.sprintf "(%s || %s)" (print_expr e1) (print_expr e2)
  | _ -> "??"

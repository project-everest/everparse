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
  | T_false    : typ
  | T_app      : hd:A.ident -> args:list index -> typ
  | T_dep_pair : dfst:typ -> dsnd:lam typ -> typ
  | T_refine   : base:typ -> refinement:lam expr -> typ
  | T_if_else  : e:expr -> t:typ -> f:typ -> typ
  | T_cases    : typ -> typ

(* An index is an F* type or an expression
   -- we reuse Ast expressions for this
*)
and index = either typ expr

type param = A.ident & typ
noeq
type struct_field = {
  sf_dependence: bool;
  sf_ident: A.ident;
  sf_typ: typ;
  sf_field_number:option A.field_num
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

noeq
type typedef_name = {
  td_name:A.ident;
  td_params:list param;
  td_entrypoint:bool
}
type typedef = typedef_name & typedef_body

////////////////////////////////////////////////////////////////////////////////

noeq
type parser_kind =
  | PK_return
  | PK_base     : hd:A.ident -> parser_kind
  | PK_filter   : k:parser_kind -> parser_kind
  | PK_and_then : k1:parser_kind -> k2:parser_kind -> parser_kind
  | PK_glb      : k1:parser_kind -> k2:parser_kind -> parser_kind

let rec parser_kind_eq k k' =
  match k, k' with
  | PK_return, PK_return -> true
  | PK_base hd1, PK_base hd2 -> A.(hd1.v = hd2.v)
  | PK_filter k, PK_filter k' -> parser_kind_eq k k'
  | PK_and_then k1 k2, PK_and_then k1' k2'
  | PK_glb k1 k2, PK_glb k1' k2' ->
    parser_kind_eq k1 k1'
    && parser_kind_eq k2 k2'
  | _ -> false

noeq
type parser' =
  | Parse_return    : v:expr -> parser'
  | Parse_app       : hd:A.ident -> args:list index -> parser'
  | Parse_nlist     : n:expr -> t:parser -> parser'
  | Parse_seq       : p:parser -> q:parser -> parser'
  | Parse_dep_pair  : p:parser -> k:lam parser -> parser'
  | Parse_map       : p:parser -> f:lam expr -> parser'
  | Parse_filter    : p:parser -> f:lam expr -> parser'
  | Parse_weaken    : p:parser ->  k:parser_kind -> parser'
  | Parse_if_else   : e:expr -> parser -> parser -> parser'
  | Parse_impos     : parser'
  | Parse_with_error: f:A.field_num -> parser -> parser'

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
  | Read_app : hd:A.ident -> args:list index -> reader

noeq
type validator' =
  | Validate_return   : validator'
  | Validate_app      : hd:A.ident -> args:list index -> validator'
  | Validate_nlist    : n:expr -> v:validator -> validator'
  | Validate_seq      : v1:validator -> v2:validator -> validator'
  | Validate_and_read : v:validator -> r:reader -> k:lam validator -> validator'
  | Validate_map      : p:validator -> f:lam expr -> validator'
  | Validate_filter   : v:validator -> r:reader -> f:lam expr -> validator'
  | Validate_filter_and_read : v:validator -> r:reader -> f:lam expr -> k:lam validator -> validator'
  | Validate_weaken   : v:validator ->  k:parser_kind -> validator'
  | Validate_if_else  : e:expr -> validator -> validator -> validator'
  | Validate_impos    : validator'
  | Validate_with_error: f:A.field_num -> validator -> validator'

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
  decl_validator: validator;
  decl_reader: option reader
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
  | Plus -> "`FStar.UInt32.add`"
  | Minus -> "`FStar.UInt32.sub`"
  | LT -> "`FStar.UInt32.lt`"
  | GT -> "`FStar.UInt32.gt`"
  | LE -> "`FStar.UInt32.lte`"
  | GE -> "`FStar.UInt32.gte`"
  | Ext s -> s

let rec print_expr (e:expr) : Tot string =
  match e with
  | Constant c ->
    A.print_constant c
  | Identifier i ->
    print_ident i
  | Record nm fields ->
    Printf.sprintf "{ %s }" (String.concat "; " (print_fields fields))
  | App Eq [e1; e2]
  | App And [e1; e2]
  | App Or [e1; e2]
  | App Plus [e1; e2]
  | App Minus [e1; e2]
  | App LT [e1; e2]
  | App GT [e1; e2]
  | App LE [e1; e2]
  | App GE [e1; e2] ->
    Printf.sprintf "(%s %s %s)" (print_expr e1) (print_op (App?.hd e)) (print_expr e2)
  | App Not [e1] ->
    Printf.sprintf "(%s %s)" (print_op (App?.hd e)) (print_expr e1)
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
  | T_false -> "False"
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
  | T_if_else e t1 t2 ->
    Printf.sprintf "(if %sthen\n%s\nelse\n%s)"
      (print_expr e)
      (print_typ t1)
      (print_typ t2)
  | T_cases t -> print_typ t

and print_indexes (is:list index) : Tot (list string) (decreases is) =
  match is with
  | [] -> []
  | Inl t::is -> print_typ t::print_indexes is
  | Inr e::is -> print_expr e::print_indexes is

let rec print_kind (k:parser_kind) : Tot string =
  match k with
  | PK_base hd ->
    Printf.sprintf "kind_%s"
      (print_ident hd)
  | PK_return ->
    "ret_kind"
  | PK_and_then k1 k2 ->
    Printf.sprintf "(and_then_kind %s %s)"
      (print_kind k1)
      (print_kind k2)
  | PK_glb k1 k2 ->
    Printf.sprintf "(glb %s %s)"
      (print_kind k1)
      (print_kind k2)
  | PK_filter k ->
    Printf.sprintf "(filter_kind %s)"
      (print_kind k)

let rec print_parser (p:parser) : Tot string (decreases p) =
  match p.p_parser with
  | Parse_return v ->
    Printf.sprintf "(parse_ret %s)" (print_expr v)
  | Parse_app hd args ->
    Printf.sprintf "(parse_%s %s)" (print_ident hd) (String.concat " " (print_indexes args))
  | Parse_nlist e p ->
    Printf.sprintf "(parse_nlist %s %s)" (print_expr e) (print_parser p)
  | Parse_seq p1 p2 ->
    Printf.sprintf "(%s `parse_pair` %s)" (print_parser p1) (print_parser p2)
  | Parse_dep_pair p1 (x, p2) ->
    Printf.sprintf "(%s `parse_dep_pair` (fun %s -> %s))" (print_parser p1) (print_ident x) (print_parser p2)
  | Parse_map p1 (x, e) ->
    Printf.sprintf "(%s `parse_map` (fun %s -> %s))" (print_parser p1) (print_ident x) (print_expr e)
  | Parse_filter p1 (x, e) ->
    Printf.sprintf "(%s `parse_filter` (fun %s -> %s))" (print_parser p1) (print_ident x) (print_expr e)
  | Parse_weaken p1 k ->
    Printf.sprintf "(parse_weaken %s _)" (print_parser p1) //(print_kind k)
  | Parse_if_else e p1 p2 ->
    Printf.sprintf "(parse_ite %s (fun _ -> %s) (fun _ -> %s))"
      (print_expr e)
      (print_parser p1)
      (print_parser p2)
  | Parse_impos -> "(parse_impos())"
  | Parse_with_error _ p -> print_parser p

let rec print_reader (r:reader) : Tot string =
  match r with
  | Read_u8 -> "read_u8"
  | Read_u16 -> "read_u16"
  | Read_u32 -> "read__UINT32"
  | Read_app hd args ->
    Printf.sprintf "(read_%s %s)" (print_ident hd) (String.concat " " (print_indexes args))
  | Read_filter r (x, f) ->
    Printf.sprintf "(read_filter %s (fun %s -> %s))"
      (print_reader r)
      (print_ident x)
      (print_expr f)

let rec print_validator (v:validator) : Tot string (decreases v) =
  match v.v_validator with
  | Validate_return ->
    Printf.sprintf "validate_ret"
  | Validate_app hd args ->
    Printf.sprintf "(validate_%s %s)" (print_ident hd) (String.concat " " (print_indexes args))
  | Validate_nlist e p ->
    Printf.sprintf "(validate_nlist %s %s)" (print_expr e) (print_validator p)
  | Validate_seq p1 p2 ->
    Printf.sprintf "(%s `validate_pair` %s)" (print_validator p1) (print_validator p2)
  | Validate_and_read p1 r (x, p2) ->
    Printf.sprintf "(validate_dep_pair %s %s (fun %s -> %s))"
      (print_validator p1)
      (print_reader r)
      (print_ident x)
      (print_validator p2)
  | Validate_map p1 (x, e) ->
    Printf.sprintf "(%s `validate_map` (fun %s -> %s))" (print_validator p1) (print_ident x) (print_expr e)
  | Validate_filter p1 r (x, e) ->
    Printf.sprintf "(validate_filter %s %s (fun %s -> %s))"
      (print_validator p1)
      (print_reader r)
      (print_ident x)
      (print_expr e)
  | Validate_filter_and_read p1 _ (x, e) (y, v) ->
    Printf.sprintf "(v_filter_and_read %s (fun %s -> %s) (fun %s -> %s))"
      (print_validator p1)
      (print_ident x)
      (print_expr e)
      (print_ident y)
      (print_validator v)
  | Validate_weaken p1 k ->
    Printf.sprintf "(validate_weaken %s _)" (print_validator p1) // (print_kind k)
  | Validate_if_else e v1 v2 ->
    Printf.sprintf "(validate_ite %s (fun _ -> %s) (fun _ -> %s) (fun _ -> %s) (fun _ -> %s))"
      (print_expr e)
      (print_parser v1.v_parser)
      (print_validator v1)
      (print_parser v2.v_parser)
      (print_validator v2)
  | Validate_impos -> "(validate_impos())"
  | Validate_with_error f v ->
    Printf.sprintf "(validate_with_error %duL %s)" f (print_validator v)

let print_typedef_name (tdn:typedef_name) =
  Printf.sprintf "%s %s"
    (print_ident tdn.td_name)
    (String.concat " "
      (List.Tot.map (fun (id, t) -> Printf.sprintf "(%s:%s)" (print_ident id) (print_typ t)) tdn.td_params))

let print_typedef_typ (tdn:typedef_name) =
  Printf.sprintf "%s %s"
    (print_ident tdn.td_name)
    (String.concat " "
      (List.Tot.map (fun (id, t) -> (print_ident id)) tdn.td_params))

let print_typedef_body (b:typedef_body) =
  match b with
  | TD_abbrev t -> print_typ t
  | TD_struct fields ->
    let print_field (f:field) : Tot string =
      match f with
      | FieldComment s -> s
      | Field sf ->
        Printf.sprintf "%s : %s%s%s"
          (print_ident sf.sf_ident)
          (print_typ sf.sf_typ)
          (if sf.sf_dependence then " (*dep*)" else "")
          (match sf.sf_field_number with | None -> "" | Some n -> Printf.sprintf "(* %d *)" n)
    in
    let fields = String.concat ";\n" (List.Tot.map print_field fields) in
    Printf.sprintf "{\n%s\n}" fields

let print_decl (d:decl) : Tot string =
  match d with
  | Comment c -> c
  | Definition (x, c) ->
    Printf.sprintf "[@CMacro]\nlet %s = %s\n" (print_ident x) (A.print_constant c)
  | Type_decl td ->
    Printf.sprintf "noextract\ntype %s = %s\n"
      (print_typedef_name td.decl_name)
      (print_typedef_body td.decl_typ)
    `strcat`
    Printf.sprintf "noextract\nlet kind_%s : parser_kind = %s\n"
      (print_ident td.decl_name.td_name)
      (print_kind td.decl_parser.p_kind)
    `strcat`
    Printf.sprintf "noextract\nlet parse_%s : parser (kind_%s) (%s) = %s\n"
      (print_typedef_name td.decl_name)
      (print_ident td.decl_name.td_name)
      (print_typedef_typ td.decl_name)
      (print_parser td.decl_parser)
    `strcat`
    Printf.sprintf "%sinline_for_extraction\nlet validate_%s : validator (parse_%s) = %s\n"
      (if td.decl_name.td_entrypoint then "" else "noextract\n")
      (print_typedef_name td.decl_name)
      (print_typedef_typ td.decl_name)
      (print_validator td.decl_validator)
    `strcat`
    (match td.decl_reader with
     | None -> ""
     | Some r ->
       Printf.sprintf "%sinline_for_extraction\nlet read_%s : reader (parse_%s) = %s\n"
         (if td.decl_name.td_entrypoint then "" else "noextract\n")
         (print_typedef_name td.decl_name)
         (print_typedef_name td.decl_name)
         (print_reader r))

let print_decls (ds:list decl) =
  Printf.sprintf
    "module Rndis\n\
     open Prelude\n\
     %s"
     (String.concat "\n" (List.Tot.map print_decl ds))

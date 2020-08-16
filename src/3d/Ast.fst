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
module Ast
(* The source abstract syntax for the 3d frontend to EverParse *)

open FStar.All

let reserved_prefix = "___"


/// pos: Source locations
type pos = {
  filename: string;
  line:int;
  col:int
}

noeq
type comments_buffer_t = {
  push: string & pos & pos -> ML unit;
  flush: unit -> ML (list string);
  flush_until: pos -> ML (list string);
}

#push-options "--warn_error -272" //top-level effect; ok
let comments_buffer : comments_buffer_t =
  let buffer : ref (list (string & pos & pos)) = FStar.ST.alloc [] in
  let buffer_comment (c, s, p) =
    let c = String.substring c 2 (String.length c - 2) in
    buffer := (c, s, p) :: !buffer
  in
  let flush_comments () =
    let cs = !buffer in
    buffer := [];
    (List.rev cs) |> List.map (fun (c, _, _) -> c)
  in
  let flush_until pos : ML (list string) =
    let cs = !buffer in
    let preceding, following =
      List.partition (fun (c, _, end_pos) ->
        Options.debug_print_string
          (Printf.sprintf "Requesting comments until line %d,\nAt line %d we have comment (*%s*)\n"
            pos.line
            end_pos.line
            c);
          end_pos.line <= pos.line) cs
    in
    buffer := following;
    preceding |> List.map (fun (c, _, _) -> c)
  in
  {
    push = buffer_comment;
    flush = flush_comments;
    flush_until = flush_until
  }
#pop-options

let string_of_pos p =
  Printf.sprintf "%s:(%d,%d)" p.filename p.line p.col

/// range: A source extent
let range = pos * pos

/// comment: A list of line comments, i.e., a list of strings
let comments = list string

let string_of_range r =
  let p, q = r in
  if p.filename = q.filename
  then Printf.sprintf "%s:(%d,%d--%d,%d)"
              p.filename p.line p.col q.line q.col
  else Printf.sprintf "%s -- %s"
              (string_of_pos p)
              (string_of_pos q)

let dummy_pos = {
  filename="";
  line=0;
  col=0;
}

noeq
type with_meta_t 'a = {
  v:'a;
  range:range;
  comments: comments
}

let with_range_and_comments (x:'a) r c : with_meta_t 'a = {
  v = x;
  range = r;
  comments = c
}
let with_range (x:'a) (r:range) : with_meta_t 'a = with_range_and_comments x r []

let ident' = string
let ident = with_meta_t ident'

exception Error of string

let error #a msg (r:range) : ML a =
  raise (Error (Printf.sprintf "%s: (Error) %s\n" (string_of_pos (fst r)) msg))

let warning msg (r:range) : ML unit =
  FStar.IO.print_string (Printf.sprintf "%s: (Warning) %s\n" (string_of_pos (fst r)) msg)

let check_reserved_identifier (i:ident) =
  let open FStar.String in
  let s = i.v in
  if length s >= 3
  && sub s 0 3 = reserved_prefix
  then error "Identifiers cannot begin with \"___\"" i.range

type integer_type =
  | UInt8
  | UInt16
  | UInt32
  | UInt64

let parse_int_suffix (i:string) : string * option integer_type =
    let l = String.length i in
    if l >= 2
    then let suffix = String.sub i (l - 2) 2 in
         let prefix = String.sub i 0 (l - 2) in
         match suffix with
         | "uy" -> prefix, Some UInt8
         | "us" -> prefix, Some UInt16
         | "ul" -> prefix, Some UInt32
         | "uL" -> prefix, Some UInt64
         | _ -> i, None
    else i, None

let smallest_integer_type_of r (i:int) : ML integer_type =
  if FStar.UInt.fits i 8 then UInt8
  else if FStar.UInt.fits i 16 then UInt16
  else if FStar.UInt.fits i 32 then UInt32
  else if FStar.UInt.fits i 64 then UInt64
  else error (Printf.sprintf
                 "Integer %d is too large for all supported fixed-width types"
                 i)
             r

let integer_type_lub (t1 t2: integer_type) : Tot integer_type =
  match t1, t2 with
  | UInt64, _
  | _, UInt64 -> UInt64
  | _, UInt32
  | UInt32, _ -> UInt32
  | _, UInt16
  | UInt16, _ -> UInt16
  | UInt8, UInt8 -> UInt8

let integer_type_leq (t1 t2: integer_type) : bool =
  integer_type_lub t1 t2 = t2

let as_integer_typ (i:ident) : ML integer_type =
  match i.v with
  | "UINT8" -> UInt8
  | "UINT16" -> UInt16
  | "UINT32" -> UInt32
  | "UINT64" -> UInt64
  | _ -> error ("Unknown integer type: " ^ i.v) i.range

/// Integer, hex and boolean constants
type constant =
  | Unit
  | Int : integer_type -> int -> constant
  | XInt: integer_type -> string -> constant   //hexadecimal constants
  | Bool of bool

/// Operators supported in refinement expressions
type op =
  | Eq
  | Neq
  | And
  | Or
  | Not
  | Plus of option integer_type
  | Minus of option integer_type
  | Mul of option integer_type
  | Division of option integer_type
  | Remainder of option integer_type
  | BitwiseAnd of option integer_type
  | BitwiseXor of option integer_type
  | BitwiseOr of option integer_type
  | BitwiseNot of option integer_type
  | ShiftRight of option integer_type
  | ShiftLeft of option integer_type
  | LT of option integer_type
  | GT of option integer_type
  | LE of option integer_type
  | GE of option integer_type
  | IfThenElse
  | BitFieldOf of int //BitFieldOf_n(i, from, to); the integer is the size of i in bits
  | SizeOf
  | Cast : from:option integer_type -> to:integer_type -> op
  | Ext of string
  //OffsetOf ?

/// Expressions used in refinements
///   Expressions have no binding structure
///   Names are represented using concrete identifiers, i.e., strings
///   We enforce that all names are unique in a scope, i.e., no shadowing allowed
noeq
type expr' =
  | Constant of constant
  | Identifier of ident
  | This
  | App : op -> list expr -> expr'

and expr = with_meta_t expr'

/// Types: all types are named and fully instantiated to expressions only
///   i.e., no type-parameterized types
noeq
type typ' =
  | Type_app : ident -> list expr -> typ'
  | Pointer : typ -> typ'
and typ = with_meta_t typ'

let field_typ = t:typ { Type_app? t.v }

noeq
type atomic_action =
  | Action_return of expr
  | Action_abort
  | Action_field_pos
  | Action_field_ptr
  | Action_deref of ident
  | Action_assignment : lhs:ident -> rhs:expr -> atomic_action
  | Action_call : f:ident -> args:list expr -> atomic_action

noeq
type action' =
  | Atomic_action of atomic_action
  | Action_seq : hd:atomic_action -> tl:action -> action'
  | Action_ite : hd:expr -> then_:action -> else_:option action -> action'
  | Action_let : i:ident -> a:atomic_action -> k:action -> action'
and action = with_meta_t action'


type qualifier =
  | Immutable
  | Mutable

/// Parameters: Type definitions can be parameterized by values
///   Parameters have a name and are always annoted with their type
type param =  typ & ident & qualifier

/// The size of a type is its the number of bytes used in its representation
let size = int

/// field_num: Every field in a struct is assigned a unique identifier
///   which is then reported in case validation fails. The identifier
///   has to be suitably small, so that it fits in the 32 bits that
///   LowParse reserves for both field identifiers and error codes.
///
///   We pick this to be 2^16 now. Which is to say that a single en
let field_num = n:nat{ 0 < n /\ n < pow2 16 }

noeq
type bitfield_attr' = {
  bitfield_width : int;
  bitfield_identifier : int;
  bitfield_type : typ;
  bitfield_from : int;
  bitfield_to: int
}
and bitfield_attr = with_meta_t bitfield_attr'

let field_bitwidth_t = either (with_meta_t int) bitfield_attr

type array_qualifier =
  | VariableSizeEq              //[Size]
  | VariableSizeLeq             //[<= Size]
  | SingleElementVariableSizeEq //[= Size]
  | ConstantSize                //[N]

noeq
type struct_field = {
  field_dependence:bool;   //computed; whether or not the rest of the struct depends on this field
  field_size:option size;  //computed; the size in bytes occupied by this field
  field_ident:ident;       //name of the field
  field_type:typ;          //type of the field
  field_array_opt:option (expr * array_qualifier);  //array size in bytes, the qualifier indicates whether this is a variable-length suffix or not
  field_constraint:option expr; //refinement constraint
  field_number:option field_num; //computed; field identifiers, used for error reporting
  field_bitwidth:option field_bitwidth_t;  //bits used for the field; elaborate from Inl to Inr
  field_action:option (action & bool); //boo indicates if the action depends on the field value
}

let field = with_meta_t struct_field

noeq
type case =
  | Case : expr -> field -> case
  | DefaultCase : field -> case

type switch_case = expr & list case

noeq
type attribute =
  | Entrypoint

/// Typedefs are given 2 names by convention and can be tagged as an
/// "entrypoint" for the validator
///
///   E.g.,
///    typedef [entrypoint] struct _T { ... } T, *PTR_T;
noeq
type typedef_names = {
  typedef_name: ident;
  typedef_abbrev: ident;
  typedef_ptr_abbrev: ident;
  typedef_attributes: list attribute
}

let enum_case = ident & option (either int ident)

/// A 3d specification a list of declarations
///   - Define: macro definitions for constants
///   - TypeAbbrev: macro definition of types
///   - Enum: enumerated type using existing constants or newly defined constants
///   - Record: a struct with refinements
///   - CaseType: an untagged union
noeq
type decl' =
  | Define: ident -> option typ -> constant -> decl'
  | TypeAbbrev: typ -> ident -> decl'
  | Enum: typ -> ident -> list enum_case -> decl'
  | Record: names:typedef_names -> params:list param -> where:option expr -> fields:list field -> decl'
  | CaseType: typedef_names -> list param -> switch_case -> decl'
and decl = with_meta_t decl'

noeq
type type_refinement = {
  includes:list string;
  type_map:list (ident * option ident)
}

let prog = list decl & option type_refinement

////////////////////////////////////////////////////////////////////////////////
// Utilities
////////////////////////////////////////////////////////////////////////////////

(** Equality on expressions and types **)

/// eq_expr partially decides equality on expressions, by requiring
/// syntactic equality
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

/// eq_typ: syntactic equalty of types
let rec eq_typ (t1 t2:typ) : Tot bool =
  match t1.v, t2.v with
  | Type_app hd1 es1, Type_app hd2 es2 ->
    hd1.v = hd2.v
    && eq_exprs es1 es2
  | Pointer t1, Pointer t2 ->
    eq_typ t1 t2
  | _ -> false

(** Common AST constants and builders **)
let dummy_range = dummy_pos, dummy_pos
let with_dummy_range x = with_range x dummy_range
let tbool = with_dummy_range (Type_app (with_dummy_range "Bool") [])
let tunit = with_dummy_range (Type_app (with_dummy_range "unit") [])
let tuint8 = with_dummy_range (Type_app (with_dummy_range "UINT8") [])
let tuint16 = with_dummy_range (Type_app (with_dummy_range "UINT16") [])
let tuint32 = with_dummy_range (Type_app (with_dummy_range "UINT32") [])
let tuint64 = with_dummy_range (Type_app (with_dummy_range "UINT64") [])
let tunknown = with_dummy_range (Type_app (with_dummy_range "?") [])
let tfield_id = with_dummy_range (Type_app (with_dummy_range "field_id") [])

let map_opt (f:'a -> ML 'b) (o:option 'a) : ML (option 'b) =
  match o with
  | None -> None
  | Some x -> Some (f x)

////////////////////////////////////////////////////////////////////////////////
// Substitutions
////////////////////////////////////////////////////////////////////////////////
module H = Hashtable
let subst = H.t ident' expr
let mk_subst (s:list (ident * expr)) : ML subst =
  let h = H.create 10 in
  List.iter (fun (i, e) -> H.insert h i.v e) s;
  h
let apply (s:subst) (id:ident) : ML expr =
  match H.try_find s id.v with
  | None -> with_range (Identifier id) id.range
  | Some e -> e
let rec subst_expr (s:subst) (e:expr) : ML expr =
  match e.v with
  | Constant _
  | This -> e
  | Identifier i -> apply s i
  | App op es -> {e with v = App op (List.map (subst_expr s) es)}
let rec subst_typ (s:subst) (t:typ) : ML typ =
  match t.v with
  | Type_app hd es -> { t with v = Type_app hd (List.map (subst_expr s) es) }
  | Pointer t -> {t with v = Pointer (subst_typ s t) }
let subst_field (s:subst) (f:field) : ML field =
  let sf = f.v in
  let sf = {
      sf with
      field_type = subst_typ s sf.field_type;
      field_array_opt = map_opt (fun (e, b) -> subst_expr s e, b) sf.field_array_opt;
      field_constraint = map_opt (subst_expr s) sf.field_constraint
  } in
  { f with v = sf }
let subst_case (s:subst) (c:case) : ML case =
  match c with
  | Case e f -> Case (subst_expr s e) (subst_field s f)
  | DefaultCase f -> DefaultCase (subst_field s f)
let subst_switch_case (s:subst) (sc:switch_case) : ML switch_case =
  subst_expr s (fst sc), List.map (subst_case s) (snd sc)
let subst_params (s:subst) (p:list param) : ML (list param) =
  List.map (fun (t, i, q) -> subst_typ s t, i, q) p
let subst_decl (s:subst) (d:decl) : ML decl =
  match d.v with
  | Define i None _ -> d
  | Define i (Some t) c -> {d with v = Define i (Some (subst_typ s t)) c}
  | TypeAbbrev t i -> { d with v = TypeAbbrev (subst_typ s t) i }
  | Enum t i is -> { d with v = Enum (subst_typ s t) i is }
  | Record names params where fields ->
    { d with v = Record names (subst_params s params) (map_opt (subst_expr s) where) (List.map (subst_field s) fields) }
  | CaseType names params cases ->
    { d with v = CaseType names (subst_params s params) (subst_switch_case s cases) }

(*** Printing the source AST; for debugging only **)
let print_constant (c:constant) =
  let print_tag = function
    | UInt8 -> "uy"
    | UInt16 -> "us"
    | UInt32 -> "ul"
    | UInt64 -> "uL"
  in
  match c with
  | Unit -> "()"
  | Int tag i  -> Printf.sprintf "%d%s" i (print_tag tag)
  | XInt tag x ->
    let tag = print_tag tag in
    if String.length x >= 2
    && String.sub x (String.length x - 2) 2 = tag
    then x
    else Printf.sprintf "%s%s" x tag
  | Bool b -> Printf.sprintf "%b" b

let print_ident (i:ident) = i.v

let print_integer_type = function
  | UInt8 -> "UINT8"
  | UInt16 -> "UINT16"
  | UInt32 -> "UINT32"
  | UInt64 -> "UINT64"

let print_op = function
  | Eq -> "="
  | Neq -> "!="
  | And -> "&&"
  | Or -> "||"
  | Not -> "!"
  | Plus _ -> "+"
  | Minus _ -> "-"
  | Mul _ -> "*"
  | Division _ -> "/"
  | Remainder _ -> "%"
  | BitwiseAnd _ -> "&"
  | BitwiseOr _ -> "|"
  | BitwiseXor _ -> "^"
  | BitwiseNot _ -> "~"
  | ShiftLeft _ -> "<<"
  | ShiftRight _ -> ">>"
  | LT _ -> "<"
  | GT _ -> ">"
  | LE _ -> "<="
  | GE _ -> ">="
  | IfThenElse -> "ifthenelse"
  | BitFieldOf i -> Printf.sprintf "bitfield_of(%d)" i
  | SizeOf -> "sizeof"
  | Cast _ t -> "(" ^ print_integer_type t ^ ")"
  | Ext s -> s

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
  | App Not [e1] ->
    Printf.sprintf "(! %s)" (print_expr e1)
  | App (BitwiseNot _) [e1] ->
    Printf.sprintf "(~ %s)" (print_expr e1)
  | App (Plus _) [e1; e2]
  | App (Minus _) [e1; e2]
  | App (Mul _) [e1; e2]
  | App (Division _) [e1; e2]
  | App (Remainder _) [e1; e2]
  | App (BitwiseAnd _) [e1; e2]
  | App (BitwiseOr _) [e1; e2]
  | App (BitwiseXor _) [e1; e2]
  | App (ShiftLeft _) [e1; e2]
  | App (ShiftRight _) [e1; e2]
  | App (LT _) [e1; e2]
  | App (GT _) [e1; e2]
  | App (LE _) [e1; e2]
  | App (GE _) [e1; e2] ->
    let op = App?._0 e.v in
    Printf.sprintf "(%s %s %s)" (print_expr e1) (print_op op) (print_expr e2)
  | App SizeOf [e1] ->
    Printf.sprintf "(sizeof %s)" (print_expr e1)
  | App (Cast i j) [e] ->
    Printf.sprintf "%s %s" (print_op (Cast i j)) (print_expr e)
  | App (Ext s) es ->
    Printf.sprintf "%s(%s)" (print_op (Ext s)) (String.concat ", " (print_exprs es))
  | App op es ->
    Printf.sprintf "(?? %s %s)" (print_op op) (String.concat ", " (print_exprs es))

and print_exprs (es:list expr) : Tot (list string) =
  match es with
  | [] -> []
  | hd::tl -> print_expr hd :: print_exprs tl

let rec print_typ t : ML string =
  match t.v with
  | Type_app i es ->
    begin
    match es with
    | [] -> i.v
    | _ ->
      Printf.sprintf "%s(%s)"
        i.v
        (String.concat ", " (List.map print_expr es))
    end
  | Pointer t ->
     Printf.sprintf "(pointer %s)"
       (print_typ t)

let typ_as_integer_type (t:typ) : ML integer_type =
  match t.v with
  | Type_app i [] -> as_integer_typ i
  | _ -> error ("Expected an integer type; got: " ^ (print_typ t)) t.range

let print_qual = function
  | Mutable -> "mutable"
  | Immutable -> ""

let print_params (ps:list param) =
  match ps with
  | [] -> ""
  | _ ->
    Printf.sprintf "(%s)"
      (String.concat ", "
        (ps |> List.map
          (fun (t, p, q) ->
             Printf.sprintf "%s%s %s"
               (print_qual q)
               (print_typ t)
               (print_ident p))))

let print_opt (o:option 'a) (f:'a -> string) : string =
  match o with
  | None -> ""
  | Some x -> f x

let print_bitfield (bf:option field_bitwidth_t) =
  match bf with
  | None -> ""
  | Some (Inl x) -> Printf.sprintf ": %d " x.v
  | Some (Inr {v=a}) ->
    Printf.sprintf ": (|width=%d, id=%d, type=%s, from=%d, to=%d|) "
     a.bitfield_width a.bitfield_identifier
     (print_typ a.bitfield_type)
     a.bitfield_from a.bitfield_to

let print_field (f:field) : ML string =
  let print_array eq : Tot string =
    let e, q = eq in
    match q with
    | VariableSizeEq -> Printf.sprintf "[%s]" (print_expr e)
    | VariableSizeLeq -> Printf.sprintf "[<= %s]" (print_expr e)
    | SingleElementVariableSizeEq -> Printf.sprintf "[= %s]" (print_expr e)
    | ConstantSize -> Printf.sprintf "[{ %s }]" (print_expr e)
  in
  let sf = f.v in
    Printf.sprintf "%s%s %s%s%s%s; (* size = %s *)"
      (if sf.field_dependence then "dependent " else "")
      (print_typ sf.field_type)
      (print_ident sf.field_ident)
      (print_bitfield sf.field_bitwidth)
      (print_opt sf.field_array_opt print_array)
      (print_opt sf.field_constraint (fun e -> Printf.sprintf "{%s}" (print_expr e)))
      (print_opt sf.field_size string_of_int)

let print_switch_case (s:switch_case) : ML string =
  let head, cases = s in
  let print_case (c:case) : ML string =
    match c with
    | Case e f ->
      Printf.sprintf "case %s: %s;"
        (print_expr e)
        (print_field f)
    | DefaultCase f ->
      Printf.sprintf "default: %s;"
        (print_field f)
  in
  Printf.sprintf "switch (%s) {\n
                  %s\n\
                 }"
                 (print_expr head)
                 (String.concat "\n" (List.map print_case cases))

let print_decl' (d:decl') : ML string =
  match d with
  | Define i None c ->
    Printf.sprintf "#define %s %s;" (print_ident i) (print_constant c)
  | Define i (Some t) c ->
    Printf.sprintf "#define %s : %s %s;" (print_ident i) (print_typ t) (print_constant c)
  | TypeAbbrev t i ->
    Printf.sprintf "typedef %s %s;" (print_typ t) (print_ident i)
  | Enum t i ls ->
    let print_enum_case (i, jopt) =
      match jopt with
      | None -> print_ident i
      | Some (Inl j) -> Printf.sprintf "%s = %d" (print_ident i) j
      | Some (Inr j) -> Printf.sprintf "%s = %s" (print_ident i) (print_ident j)
    in
    Printf.sprintf "%s enum %s {\n\
                       %s \n\
                   }"
                   (print_typ t)
                   i.v
                   (String.concat ",\n" (List.map print_enum_case ls))
  | Record td params wopt fields ->
    Printf.sprintf "typedef struct %s%s%s {\n\
                        %s \n\
                    } %s, *%s"
                    td.typedef_name.v
                    (print_params params)
                    (match wopt with | None -> "" | Some e -> " where " ^ print_expr e)
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

let print_decl (d:decl) : ML string =
  match d.comments with
  | [] -> print_decl' d.v
  | cs -> Printf.sprintf "/* %s */\n%s"
          (String.concat "\n" cs)
          (print_decl' d.v)

let print_decls (ds:list decl) : ML string =
  List.map print_decl ds
  |> String.concat "\n"

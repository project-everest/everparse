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

//redefining either because we need to serialize to Json
[@@ PpxDerivingYoJson ]
type either a b =
  | Inl of a
  | Inr of b

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
(* Override the json serializers for with_meta_t to
   avoid polluting the generated JSON with ranges everywhere *)
let with_meta_t_of_yojson (#a #b #c:Type) (f:(a -> b)) (x:a)
  : ML c
  = failwith "No reading yojson"
let with_meta_t_to_yojson (f:('a -> 'b)) (x:with_meta_t 'a)
  : 'b
  = f x.v
let with_range_and_comments (x:'a) r c : with_meta_t 'a = {
  v = x;
  range = r;
  comments = c
}
let with_range (x:'a) (r:range) : with_meta_t 'a = with_range_and_comments x r []

[@@ PpxDerivingYoJson ]
type ident' = {
  modul_name : option string;
  name : string
}
[@@ PpxDerivingYoJson ]
let ident = with_meta_t ident'

let ident_to_string i = Printf.sprintf "%s%s"
  (match i.v.modul_name with
   | None -> ""
   | Some m -> m ^ ".")
  i.v.name

let ident_name i = i.v.name

exception Error of string

let error #a msg (r:range) : ML a =
  raise (Error (Printf.sprintf "%s: (Error) %s\n" (string_of_pos (fst r)) msg))

let warning msg (r:range) : ML unit =
  FStar.IO.print_string (Printf.sprintf "%s: (Warning) %s\n" (string_of_pos (fst r)) msg)

let check_reserved_identifier (i:ident) =
  let open FStar.String in
  let s = i.v.name in
  if length s >= 3
  && sub s 0 3 = reserved_prefix
  then error "Identifiers cannot begin with \"___\"" i.range

[@@ PpxDerivingYoJson ]
type integer_type =
  | UInt8
  | UInt16
  | UInt32
  | UInt64

[@@ PpxDerivingYoJson ]
let pointer_size_t = i:integer_type { i == UInt32 \/ i == UInt64 }

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

let maybe_as_integer_typ (i:ident) : Tot (option integer_type) =
  if i.v.modul_name <> None
  then None
  else
    match i.v.name with
    | "UINT8" -> Some UInt8
    | "UINT16" -> Some UInt16
    | "UINT32" -> Some UInt32
    | "UINT64" -> Some UInt64
    | "UINT8BE" -> Some UInt8
    | "UINT16BE" -> Some UInt16
    | "UINT32BE" -> Some UInt32
    | "UINT64BE" -> Some UInt64
    | _ -> None

let as_integer_typ (i:ident) : ML integer_type =
  match maybe_as_integer_typ i with
  | None -> failwith ("Unknown integer type: " ^ ident_to_string i) //i.range
  | Some t -> t

/// Bit order for bitfields
[@@ PpxDerivingYoJson ]
type bitfield_bit_order =
  | LSBFirst (* Least-significant bit first (MSVC default) *)
  | MSBFirst (* Most-significant bit first (necessary for many IETF protocols) *)

let maybe_bit_order_of (i:ident) : Pure (option bitfield_bit_order)
  (requires True)
  (ensures (fun y ->
    Some? y == Some? (maybe_as_integer_typ i)
  ))
= if i.v.modul_name <> None
  then None
  else
    match i.v.name with
    | "UINT8" -> Some LSBFirst
    | "UINT16" -> Some LSBFirst
    | "UINT32" -> Some LSBFirst
    | "UINT64" -> Some LSBFirst
    | "UINT8BE" -> Some MSBFirst
    | "UINT16BE" -> Some MSBFirst
    | "UINT32BE" -> Some MSBFirst
    | "UINT64BE" -> Some MSBFirst
    | _ -> None

let bit_order_of (i:ident) : ML bitfield_bit_order =
  match maybe_bit_order_of i with
  | None -> error ("Unknown integer type: " ^ ident_to_string i) i.range
  | Some t -> t

/// Integer, hex and boolean constants
[@@ PpxDerivingYoJson ]
type constant =
  | Unit
  | Int : integer_type -> int -> constant
  | XInt: integer_type -> string -> constant   //hexadecimal constants
  | Bool of bool

/// Operators supported in refinement expressions
[@@ PpxDerivingYoJson ]
noeq
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
  | BitFieldOf: sz: int -> order: bitfield_bit_order -> op //BitFieldOf_n(i, from, to); the integer is the size of i in bits
  | SizeOf
  | Cast : from:option integer_type -> to:integer_type -> op
  | Ext of string
  | ProbeFunctionName of ident
  //OffsetOf ?

/// Expressions used in refinements
///   Expressions have no binding structure
///   Names are represented using concrete identifiers, i.e., strings
///   We enforce that all names are unique in a scope, i.e., no shadowing allowed
[@@ PpxDerivingYoJson ]
noeq
type expr' =
  | Constant of constant
  | Identifier of ident
  | Static of expr //the guard of a #if; must be made from compile-time constants only
  | This
  | App : op -> list expr -> expr'

and expr = with_meta_t expr'

/// A non-pointer type in the AST (see typ below) may be
///   - A spec type, i.e. a type that has an interpretation in 3d, that 3d understands
///   - An output type, may be used as the type of the parse tree constructed as part of actions
///     This includes structs and unions, and actions support assignment to fields of output types
///   - An extern type, an abstract, uninterpreted type

[@@ PpxDerivingYoJson ]
type t_kind =
  | KindSpec
  | KindOutput
  | KindExtern

/// Syntax for output expressions
///
/// Output expressions may appear as type parameters or as lhs of assignment actions

[@@ PpxDerivingYoJson ]
noeq
type out_expr' =
  | OE_id     : ident -> out_expr'
  | OE_star   : out_expr -> out_expr'
  | OE_addrof : out_expr -> out_expr'
  | OE_deref  : out_expr -> ident -> out_expr'  //deref a field
  | OE_dot    : out_expr -> ident -> out_expr'  //read a field

/// Output expressions maintain metadata
///   (base type, type of the expr and its bitwidth, in case the expression is of a bitfield type)
///
/// where base type is the type of the base identifier,
///       and type of the output expression
///
/// The metadata is initially None after parsing,
///   and is populated after typechecking (in Binding.fst)
///
/// It is used during emitting F* and C code
/// For each output expression, we emit an action (external function call)
///   whose signature requires all this
///
/// TODO: could we also store the source string for pretty printing?

and out_expr_meta_t = {
  out_expr_base_t : typ;
  out_expr_t : typ;
  out_expr_bit_width : option int;
}

and out_expr = { out_expr_node: with_meta_t out_expr';
                 out_expr_meta: option out_expr_meta_t }


/// A type parameter is either an expression or an output expression

and typ_param = either expr out_expr

and generic_inst = expr
/// Types: all types are named and fully instantiated to expressions only
///   i.e., no type-parameterized types
///
/// The t_kind field maintains the kind
///
/// It is set during the desugaring phase, the parser always sets it to KindSpec
///   We could move it to the parser itself
///
/// Keeping this makes it easy to check whether a type is an output type or an extern type
///   Alternatively we would have to carry some environment along


and typ' =
  | Type_app : ident -> t_kind -> list generic_inst -> list typ_param -> typ'
  | Pointer : typ -> pointer_qualifier -> typ'
  | Type_arrow : args:list typ { Cons? args } -> typ -> typ'

and pointer_qualifier =
  | PQ of pointer_size_t

and typ = with_meta_t typ'

let field_typ = t:typ { Type_app? t.v }

[@@ PpxDerivingYoJson ]
noeq
type atomic_action =
  | Action_return of expr
  | Action_abort
  | Action_field_pos_64
  | Action_field_pos_32
  | Action_field_ptr
  | Action_field_ptr_after: sz:expr -> write_to:out_expr -> atomic_action
  | Action_deref of ident
  | Action_assignment : lhs:out_expr -> rhs:expr -> atomic_action
  | Action_call : f:ident -> args:list expr -> atomic_action

noeq
[@@ PpxDerivingYoJson ]
type action' =
  | Atomic_action of atomic_action
  | Action_seq : hd:atomic_action -> tl:action -> action'
  | Action_ite : hd:expr -> then_:action -> else_:option action -> action'
  | Action_let : i:ident -> a:atomic_action -> k:action -> action'
  | Action_act : action -> action'
and action = with_meta_t action'
open FStar.List.Tot

let sequence_non_failing_actions (a0:action{Action_act? a0.v}) (a1:action {Action_act? a1.v})
  : a:action{Action_act? a.v}
  = let rec seq (a0:action) = 
      let w a = 
          with_range_and_comments a 
            a1.range
            (a0.comments @ a1.comments)
      in
      let Action_act a1 = a1.v in
      match a0.v with
      | Atomic_action a -> 
        w (Action_seq a a1)
  
      | Action_seq a0 tl ->
        w (Action_seq a0 (seq tl))
  
      | Action_ite hd th el ->
        let th = seq th in
        let el = 
          match el with
          | None -> Some a1
          | Some el -> Some (seq el)
        in
        w (Action_ite hd th el)
  
      | Action_let i a k ->
        w (Action_let i a (seq k))
  
      | Action_act a ->
        seq a
    in
    let res = seq a0 in
    with_range_and_comments (Action_act res)
      res.range
      res.comments
            

[@@ PpxDerivingYoJson ]
type qualifier =
  | Immutable
  | Mutable

/// Parameters: Type definitions can be parameterized by values
///   Parameters have a name and are always annoted with their type
[@@ PpxDerivingYoJson ]
type param =  typ & ident & qualifier

[@@ PpxDerivingYoJson ]
noeq
type bitfield_attr' = {
  bitfield_width : int;
  bitfield_identifier : int;
  bitfield_type : typ;
  bitfield_from : int;
  bitfield_to: int
}
and bitfield_attr = with_meta_t bitfield_attr'

[@@ PpxDerivingYoJson ]
let field_bitwidth_t = either (with_meta_t int) bitfield_attr

[@@ PpxDerivingYoJson ]
type array_qualifier =
  | ByteArrayByteSize  //[
  | ArrayByteSize      //[:byte-size
  | ArrayByteSizeAtMost //[:byte-size-single-element-array-at-most
  | ArrayByteSizeSingleElementArray //[:byte-size-single-element-array

[@@ PpxDerivingYoJson ]
noeq
type field_array_t =
  | FieldScalar
  | FieldArrayQualified of (expr & array_qualifier) //array size in bytes, the qualifier indicates whether this is a variable-length suffix or not
  | FieldString of (option expr)
  | FieldConsumeAll // [:consume-all]

[@@ PpxDerivingYoJson ]
noeq
type probe_field =
  | ProbeLength of expr
  | ProbeDest of expr

[@@ PpxDerivingYoJson ]
noeq
type probe_atomic_action =
  | Probe_action_return of expr
  | Probe_action_call : f:ident -> args:list expr -> probe_atomic_action
  | Probe_action_read : f:ident -> probe_atomic_action
  | Probe_action_write : f:ident -> value:expr -> probe_atomic_action
  | Probe_action_copy : f:ident -> len:expr -> probe_atomic_action
  | Probe_action_skip : len:expr -> probe_atomic_action
  | Probe_action_fail : probe_atomic_action
noeq
[@@ PpxDerivingYoJson ]
type probe_action' =
  | Probe_atomic_action of probe_atomic_action
  | Probe_action_var of expr
  | Probe_action_simple : 
    probe_fn: option ident ->
    bytes_to_read : expr -> 
    probe_action'
  | Probe_action_seq :
    hd:probe_action ->
    tl:probe_action ->
    probe_action'
  | Probe_action_let :
    i:ident ->
    a:probe_atomic_action ->
    k:probe_action ->
    probe_action'
  | Probe_action_ite :
    hd:expr ->
    then_:probe_action ->
    else_:probe_action ->
    probe_action'
and probe_action = with_meta_t probe_action'

open FStar.List.Tot

[@@ PpxDerivingYoJson ]
noeq
type probe_call = {
  probe_dest:ident;
  probe_block:probe_action;
  probe_ptr_as_u64: option ident
}

[@@ PpxDerivingYoJson ]
noeq
type atomic_field' = {
  field_dependence:bool;   //computed; whether or not the rest of the struct depends on this field
  field_ident:ident;       //name of the field
  field_type:typ;          //type of the field
  field_array_opt: field_array_t;
  field_constraint:option expr; //refinement constraint
  field_bitwidth:option field_bitwidth_t;  //bits used for the field; elaborate from Inl to Inr
  field_action:option (action & bool); //bool indicates if the action depends on the field value
  field_probe:option probe_call; //set in case this field has to be probed then validated
}

and atomic_field = with_meta_t atomic_field'

and field' =
  | AtomicField of atomic_field
  | RecordField : record -> ident -> field'
  | SwitchCaseField : switch_case -> ident -> field'

and field = with_meta_t field'

and record = list field

and case =
  | Case : expr -> field -> case
  | DefaultCase : field -> case

and switch_case = expr & list case


[@@ PpxDerivingYoJson ]
noeq
type probe_entrypoint = {
  probe_ep_fn: ident;
  probe_ep_length:expr;
}

[@@ PpxDerivingYoJson ]
noeq
type attribute =
  | Entrypoint: (probe: option probe_entrypoint) -> attribute
  | Aligned
  | Noextract

/// Typedefs are given 2 names by convention and can be tagged as an
/// "entrypoint" for the validator
///
///   E.g.,
///    typedef [entrypoint] struct _T { ... } T, *PTR_T;
[@@ PpxDerivingYoJson ]
noeq
type typedef_names = {
  typedef_name: ident;
  typedef_abbrev: ident;
  typedef_ptr_abbrev: option ident;
  typedef_attributes: list attribute
}

[@@ PpxDerivingYoJson ]
let enum_case = ident & option (either int ident)

/// Specification of output types
///
/// Output types contain atomic fields with optional bitwidths for bitfield types,
///   but they may also contain anonymous structs and unions

[@@ PpxDerivingYoJson ]
noeq
type out_field =
  | Out_field_named: ident -> typ -> bit_width:option int -> out_field
  | Out_field_anon : list out_field -> is_union:bool -> out_field

[@@ PpxDerivingYoJson ]
noeq
type out_typ = {
  out_typ_names    : typedef_names;
  out_typ_fields   : list out_field;
  out_typ_is_union : bool;  //TODO: unclear if this field is needed
}

[@@ PpxDerivingYoJson ]
type probe_qualifier =
  | PQWithOffsets
  | PQRead of integer_type
  | PQWrite of integer_type

[@@ PpxDerivingYoJson ]
noeq
type generic_param =
  | GenericProbeFunction : param_name:ident -> k:typ -> probe_for_type:ident -> generic_param

[@@ PpxDerivingYoJson ]
noeq
type probe_function_type =
  | SimpleProbeFunction of ident
  | CoerceProbeFunction of ident & ident

/// A 3d specification a list of declarations
///   - Define: macro definitions for constants
///   - TypeAbbrev: macro definition of types
///   - Enum: enumerated type using existing constants or newly defined constants
///   - Record: a struct with refinements
///   - CaseType: an untagged union
///
///   - OutputType: an output type definition
///       no validators are generated for these types,
///       they are used only in the parse trees construction in the actions
///   - ExternType: An abstract type declaration
///   - ExternFn: An abstract function declaration, may be used in the actions

[@@ PpxDerivingYoJson ]
noeq
type decl' =
  | ModuleAbbrev:
      ident ->
      ident ->
      decl'
  
  | Define:
      ident ->
      option typ ->
      constant ->
      decl'

  | TypeAbbrev:
      list attribute ->
      typ ->
      ident ->
      list generic_param ->
      list param ->
      decl'

  | Enum:
      typ ->
      ident ->
      list enum_case ->
      decl'

  | Record:
      names:typedef_names ->
      generics:list generic_param ->
      params:list param ->
      where:option expr ->
      fields:record -> decl'
  
  | CaseType:
      names:typedef_names ->
      generics:list generic_param ->
      params:list param ->
      switch_case -> decl'

  | ProbeFunction:
      ident ->
      list param ->
      probe_action ->
      probe_function_type ->
      decl'

  | Specialize :
      list (integer_type & integer_type) ->
      ident ->
      ident ->
      decl' 
      
  | CoerceProbeFunctionStub:
      ident ->
      list param ->
      p:probe_function_type { CoerceProbeFunction? p } ->
      decl'

  | OutputType:
      out_typ ->
      decl'

  | ExternType :
      typedef_names ->
      decl'

  | ExternFn   :
      ident ->
      typ ->
      list param ->
      pure:bool ->
      decl'

  | ExternProbe :
      ident ->
      option probe_qualifier ->
      decl'

[@@ PpxDerivingYoJson ]
noeq
type decl = {
  d_decl : with_meta_t decl';
  d_exported : bool
}

let mk_decl (d:decl') r c (is_exported:bool) : decl =
  { d_decl = with_range_and_comments d r c;
    d_exported = is_exported }

let decl_with_v (d:decl) (v:decl') : decl =
  { d with d_decl = { d.d_decl with v = v } }

[@@ PpxDerivingYoJson ]
noeq
type type_refinement = {
  includes:list string;
  type_map:list (ident * option ident)
}

[@@ PpxDerivingYoJson ]
let prog = list decl & option type_refinement

let mk_arrow (xs:list typ) (ty:typ) : typ =
  match xs with
  | [] -> ty
  | _ -> with_range (Type_arrow xs ty) ty.range

let mk_arrow_ps (xs:list param) (ty:typ) : typ =
  mk_arrow (List.Tot.map (fun (x, _, _) -> x) xs) ty

let destruct_arrow (t:typ) : Tot (list typ & typ) =
  match t.v with
  | Type_arrow xs ty -> xs, ty
  | _ -> [], t
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

let print_ident (i:ident) = ident_to_string i

let print_integer_type = function
  | UInt8 -> "UINT8"
  | UInt16 -> "UINT16"
  | UInt32 -> "UINT32"
  | UInt64 -> "UINT64"

let print_bitfield_bit_order = function
  | LSBFirst -> "LSBFirst"
  | MSBFirst -> "MSBFirst"

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
  | BitFieldOf i o -> Printf.sprintf "bitfield_of(%d, %s)" i (print_bitfield_bit_order o)
  | SizeOf -> "sizeof"
  | Cast _ t -> "(" ^ print_integer_type t ^ ")"
  | Ext s -> s
  | ProbeFunctionName s -> print_ident s

let rec print_expr (e:expr) : Tot string =
  match e.v with
  | Constant c ->
    print_constant c
  | Identifier i ->
    print_ident i
  | This ->
    "this"
  | Static e -> 
    Printf.sprintf "static(%s)" (print_expr e)
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
  | App (ProbeFunctionName f) es ->
    Printf.sprintf "(probe-fun %s %s)" (print_ident f) (String.concat ", " (print_exprs es))
  | App op es ->
    Printf.sprintf "(?? %s %s)" (print_op op) (String.concat ", " (print_exprs es))

and print_exprs (es:list expr) : Tot (list string) =
  match es with
  | [] -> []
  | hd::tl -> print_expr hd :: print_exprs tl

let rec print_out_expr o : ML string =
  match o.out_expr_node.v with
  | OE_id i -> ident_to_string i
  | OE_star o -> Printf.sprintf "*(%s)" (print_out_expr o)
  | OE_addrof o -> Printf.sprintf "&(%s)" (print_out_expr o)
  | OE_deref o i -> Printf.sprintf "(%s)->(%s)" (print_out_expr o) (ident_to_string i)
  | OE_dot o i -> Printf.sprintf "(%s).(%s)" (print_out_expr o) (ident_to_string i)

let print_typ_param p : ML string =
  match p with
  | Inl e -> print_expr e
  | Inr o -> print_out_expr o

let print_generic_inst = print_expr
let print_generic_insts = function
  | [] -> ""
  | gs -> Printf.sprintf "<%s>" (String.concat ", " (List.map print_generic_inst gs))
let rec print_typ t : ML string =
  match t.v with
  | Type_app i _k gs ps ->
    begin
    match ps with
    | [] -> ident_to_string i
    | _ ->
      Printf.sprintf "%s%s(%s)"
        (ident_to_string i)
        (print_generic_insts gs)
        (String.concat ", " (List.map print_typ_param ps))
    end
  | Pointer t (PQ q) ->
     Printf.sprintf "(pointer %s (%s))"
       (print_typ t)
       (print_integer_type q)
  | Type_arrow ts t ->
    Printf.sprintf "%s -> %s"
      (String.concat " -> " (List.map print_typ ts))
      (print_typ t)

let typ_as_integer_type (t:typ) : ML integer_type =
  match t.v with
  | Type_app i _k [] [] -> as_integer_typ i
  | Pointer _ (PQ i) -> i
  | _ -> error ("Expected an integer type; got: " ^ (print_typ t)) t.range

let bit_order_of_typ (t:typ) : ML bitfield_bit_order =
  match t.v with
  | Type_app i _k [] [] -> bit_order_of i
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

let print_opt (o:option 'a) (f:'a -> ML string) : ML string =
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

let rec print_field' (f:field) (with_comments:bool) : ML string =
  let field = 
    match f.v with
    | AtomicField f -> print_atomic_field f
    | RecordField f i -> Printf.sprintf "%s %s" (print_record f) i.v.name
    | SwitchCaseField f i -> Printf.sprintf "%s %s" (print_switch_case f) i.v. name
  in
  if with_comments then 
    match f.comments with 
    | [] -> field
    | comms -> Printf.sprintf "//%s\n%s" (String.concat "; " comms) field
  else field

and print_field f : ML string = print_field' f true 

and print_record (f:record) : ML string = 
  List.map print_field f |>
  String.concat ";\n"

and print_atomic_field (f:atomic_field) : ML string =
  let print_array eq : Tot string =
    match eq with
    | FieldScalar -> ""
    | FieldArrayQualified (e, q) ->
      begin match q with
      | ByteArrayByteSize -> Printf.sprintf "[%s]" (print_expr e)
      | ArrayByteSize -> Printf.sprintf "[:byte-size %s]" (print_expr e)
      | ArrayByteSizeAtMost -> Printf.sprintf "[:byte-size-single-element-array-at-most %s]" (print_expr e)
      | ArrayByteSizeSingleElementArray -> Printf.sprintf "[:byte-size-single-element-array %s]" (print_expr e)
      end
    | FieldString None -> Printf.sprintf "[::zeroterm]"
    | FieldString (Some sz) -> Printf.sprintf "[:zeroterm-byte-size-at-most %s]" (print_expr sz)
    | FieldConsumeAll -> Printf.sprintf "[:consume-all]"
  in
  let print_probe_field = function
    | ProbeLength e -> Printf.sprintf "length=%s" (print_expr e)
    | ProbeDest e -> Printf.sprintf "destination=%s" (print_expr e)
  in
  let sf = f.v in
    Printf.sprintf "%s%s %s%s%s%s%s;"
      (if sf.field_dependence then "dependent " else "")
      (print_typ sf.field_type)
      (print_ident sf.field_ident)
      (print_bitfield sf.field_bitwidth)
      (print_array sf.field_array_opt)
      (print_opt sf.field_constraint (fun e -> Printf.sprintf "{%s}" (print_expr e)))
      (print_opt sf.field_probe
        (fun p -> Printf.sprintf " probe %s" (print_probe_call p)))

and print_probe_action (p:probe_action) : ML string =
  match p.v with
  | Probe_atomic_action a ->
    print_probe_atomic_action a
  | Probe_action_var i ->
    Printf.sprintf "(Probe_action_var %s)" (print_expr i)
  | Probe_action_simple f n ->
    Printf.sprintf "(Probe_action_simple %s (%s))"
      (print_opt f print_ident)
      (print_expr n)
  | Probe_action_seq hd tl ->
    Printf.sprintf "%s; %s" 
      (print_probe_action hd)
      (print_probe_action tl)
  | Probe_action_let i hd tl ->
    Printf.sprintf "var %s = %s; %s"
      (print_ident i)
      (print_probe_atomic_action hd)
      (print_probe_action tl)
  | Probe_action_ite hd then_ else_ ->
    Printf.sprintf "if (%s) { %s } else { %s }"
      (print_expr hd)
      (print_probe_action then_)
      (print_probe_action else_)

and print_probe_atomic_action (p:probe_atomic_action)
: ML string
= match p with
  | Probe_action_return e -> Printf.sprintf "return %s;" (print_expr e)
  | Probe_action_call f args -> Printf.sprintf "(Probe_action_call %s(%s));" (print_ident f) (String.concat ", " (List.map print_expr args))
  | Probe_action_read f -> Printf.sprintf "(Probe_action_read %s);" (print_ident f)
  | Probe_action_write f v ->Printf.sprintf "(Probe_action_write %s(%s));" (print_ident f) (print_expr v)
  | Probe_action_copy f v -> Printf.sprintf "(Probe_action_copy %s(%s));" (print_ident f) (print_expr v)
  | Probe_action_skip n -> Printf.sprintf "(Probe_action_skip %s);" (print_expr n)
  | Probe_action_fail -> "(Probe_action_fail);"

and print_probe_call (p:probe_call) : ML string =
  match p with
  | { probe_dest; probe_block } ->
    Printf.sprintf "(destination=%s) { %s }"
          (print_ident probe_dest)
          (print_probe_action probe_block)

and print_action (a:action) : ML string =
  let print_atomic_action (a:atomic_action) : ML string =
    match a with
    | Action_return e -> Printf.sprintf "return %s;" (print_expr e)
    | Action_abort ->  "abort;" 
    | Action_field_pos_64 -> "field_pos_64;"
    | Action_field_pos_32 -> "field_pos_32;"
    | Action_field_ptr -> "field_ptr;"
    | Action_field_ptr_after sz write_to -> Printf.sprintf "field_ptr_after(%s, %s);" (print_expr sz) (print_out_expr write_to)
    | Action_deref i -> Printf.sprintf "deref %s;" (print_ident i)
    | Action_assignment lhs rhs -> Printf.sprintf "%s = %s;" (print_out_expr lhs) (print_expr rhs)
    | Action_call f args -> Printf.sprintf "%s(%s);" (print_ident f) (String.concat ", " (List.map print_expr args))
  in
  match a.v with
  | Atomic_action a -> print_atomic_action a
  | Action_seq hd tl -> Printf.sprintf "%s\n%s" (print_atomic_action hd) (print_action tl)
  | Action_ite hd then_ (Some else_) -> Printf.sprintf "if (%s) {\n%s\n} else {\n%s\n}" (print_expr hd) (print_action then_) (print_action else_)
  | Action_ite hd then_ None -> Printf.sprintf "if (%s) {\n%s\n}" (print_expr hd) (print_action then_)
  | Action_let i a k -> Printf.sprintf "let %s = %s in\n%s" (print_ident i) (print_atomic_action a) (print_action k)
  | Action_act a -> Printf.sprintf "{\n%s\n}" (print_action a)

and print_switch_case (s:switch_case) : ML string =
  let head, cases = s in
  Printf.sprintf "switch (%s) {\n
                  %s\n\
                 }"
                 (print_expr head)
                 (String.concat "\n" (List.map print_case cases))

and print_case (c:case) : ML string =
    match c with
    | Case e f ->
      Printf.sprintf "case %s: %s;"
        (print_expr e)
        (print_field f)
    | DefaultCase f ->
      Printf.sprintf "default: %s;"
        (print_field f)

let option_to_string (f:'a -> ML string) (x:option 'a) : ML string = print_opt x f

let print_generic_param (g:generic_param)
: ML string
= match g with
  | GenericProbeFunction i tt t ->
    Printf.sprintf "(%s : (%s) probe for %s)" (print_ident i) (print_typ tt) (print_ident t)
let print_generics generics =
  match generics with
  | [] -> ""
  | _ -> 
    Printf.sprintf "<%s>" (String.concat ", " (List.map print_generic_param generics))

let print_attribute (a:attribute) : ML string =
  match a with
  | Entrypoint None -> "entrypoint"
  | Entrypoint (Some p) -> Printf.sprintf "entrypoint(probe(%s, length=%s)" (print_ident p.probe_ep_fn) (print_expr p.probe_ep_length)
  | Aligned -> "aligned"
  | Noextract -> "noextract"
let print_attributes (a:list attribute) : ML string =
  match a with
  | [] -> ""
  | _ -> Printf.sprintf "[%s]" (String.concat ", " (List.map print_attribute a)) ^ " "
let print_probe_function_type = function
  | SimpleProbeFunction i -> print_ident i
  | CoerceProbeFunction (i,j) -> Printf.sprintf "%s -> %s" (print_ident i) (print_ident j)
let print_decl' (d:decl') : ML string =
  match d with
  | ModuleAbbrev i m -> Printf.sprintf "module %s = %s" (print_ident i) (print_ident m)
  | Define i None c ->
    Printf.sprintf "#define %s %s;" (print_ident i) (print_constant c)
  | Define i (Some t) c ->
    Printf.sprintf "#define %s : %s %s;" (print_ident i) (print_typ t) (print_constant c)
  | TypeAbbrev attrs t i generics params ->
    Printf.sprintf "%stypedef %s %s%s%s;" 
      (print_attributes attrs)
      (print_typ t)
      (print_ident i)
      (print_generics generics)
      (print_params params)
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
                   (ident_to_string i)
                   (String.concat ",\n" (List.map print_enum_case ls))
  | Record td generics params wopt fields ->
    Printf.sprintf "%stypedef struct %s%s%s%s {\n\
                        %s \n\
                    } %s, *%s"
                    (print_attributes td.typedef_attributes)
                    (ident_to_string td.typedef_name)
                    (print_generics generics)
                    (print_params params)
                    (match wopt with | None -> "" | Some e -> " where " ^ print_expr e)
                    (String.concat "\n" (List.map print_field fields))
                    (ident_to_string td.typedef_abbrev)
                    (option_to_string ident_to_string td.typedef_ptr_abbrev)
  | CaseType td generics params switch_case ->
    Printf.sprintf "%scasetype %s%s%s {\n\
                        %s \n\
                    } %s, *%s"
                    (print_attributes td.typedef_attributes)
                    (ident_to_string td.typedef_name)
                    (print_generics generics)
                    (print_params params)
                    (print_switch_case switch_case)
                    (ident_to_string td.typedef_abbrev)
                    (option_to_string ident_to_string td.typedef_ptr_abbrev)
  | ProbeFunction i params a tn ->
    Printf.sprintf "probe %s(%s) (for %s) {\n\
                        %s \n\
                    }"
                    (print_ident i)
                    (print_params params)
                    (print_probe_function_type tn)
                    (print_probe_action a)
  | CoerceProbeFunctionStub i params j ->
    Printf.sprintf "stub probe %s(%s) (for %s)" 
      (print_ident i)
      (print_params params)
      (print_probe_function_type j)
  | Specialize pqs i j ->
    let print_pointer_qual i = Printf.sprintf "pointer(%s)" (print_integer_type i) in
    Printf.sprintf "specialize (%s) %s %s"
      (String.concat ", " (List.map (fun (q1, q2) -> print_pointer_qual q1 ^ ", " ^ print_pointer_qual q2) pqs))
      (print_ident i)
      (print_ident j)
  | OutputType out_t -> "Printing for output types is TBD"
  | ExternType _ -> "Printing for extern types is TBD"
  | ExternFn _ _ _ _
  | ExternProbe _ _ -> "Printing for extern functions is TBD"

let print_decl (d:decl) : ML string =
  match d.d_decl.comments with
  | [] -> print_decl' d.d_decl.v
  | cs -> Printf.sprintf "/* %s */\n%s"
          (String.concat "\n" cs)
          (print_decl' d.d_decl.v)

let print_decls (ds:list decl) : ML string =
  List.map print_decl ds
  |> String.concat "\n/*------------------------------------*/\n"

////////////////////////////////////////////////////////////////////////////////
// Utilities
////////////////////////////////////////////////////////////////////////////////

(** Entrypoint and export definitions *)

let has_entrypoint (l:list attribute) : Tot bool =
  List.Tot.existsb Entrypoint? l

let rec get_entrypoint_probes' (l: list attribute) (accu: list probe_entrypoint) : Tot (list probe_entrypoint) =
  match l with
  | [] -> List.Tot.rev accu
  | Entrypoint (Some probe) :: q -> get_entrypoint_probes' q (probe :: accu)
  | _ :: q -> get_entrypoint_probes' q accu

let get_entrypoint_probes (l: list attribute) : Tot (list probe_entrypoint) =
  get_entrypoint_probes' l []

let is_entrypoint_or_export d = match d.d_decl.v with
  | Record names _ _ _ _
  | CaseType names _ _ _ ->
    if has_entrypoint (names.typedef_attributes)
    then true
    else d.d_exported
  | _ -> d.d_exported

let is_entrypoint d = match d.d_decl.v with
  | Record names _ _ _ _
  | CaseType names _ _ _ ->
    has_entrypoint (names.typedef_attributes)
  | _ -> false

let attribs_of_decl d = match d.d_decl.v with
  | Record names _ _ _ _
  | CaseType names _ _ _ -> names.typedef_attributes
  | TypeAbbrev attribs _ _ _ _ -> attribs
  | _ -> []

let is_noextract d = List.existsb Noextract? (attribs_of_decl d)

(** Determine if there are output type expressions: which cases in
   TranslateForInterpreter introduce the Output_type_expr constructor?
   *)

/// Matches translate_action_assignment, translate_action_field_ptr_after
let out_expr_is_out_type_expr (lhs: out_expr) : Tot bool =
  match lhs.out_expr_node.v with
  | OE_star ({out_expr_node = {v=OE_id i}}) -> false
  | _ -> true

/// Matches translate_atomic_action
let atomic_action_has_out_expr (a: atomic_action) : Tot bool =
  match a with
  | Action_field_ptr_after _ write_to
  | Action_assignment write_to _
    -> out_expr_is_out_type_expr write_to
  | _ -> false

/// Matches translate_action
let rec action_has_out_expr (a: action) : Tot bool =
  match a.v with
  | Atomic_action a -> atomic_action_has_out_expr a
  | Action_seq hd tl ->
    if atomic_action_has_out_expr hd
    then true
    else action_has_out_expr tl
  | Action_ite _ then_ (Some else_) ->
    if action_has_out_expr then_
    then true
    else action_has_out_expr else_
  | Action_ite _ then_ None ->
    action_has_out_expr then_
  | Action_let _ a k ->
    if atomic_action_has_out_expr a
    then true
    else action_has_out_expr k
  | Action_act a ->
    action_has_out_expr a

let field_action_has_out_expr 
  (f: option (action & bool))
: Tot bool
= match f with
  | None -> false
  | Some (a, _) -> action_has_out_expr a

/// Matches translate_atomic_field
let atomic_field_has_out_expr (f: atomic_field) : Tot bool =
  let sf = f.v in
  field_action_has_out_expr sf.field_action

/// Matches field_as_grouped_fields
let rec field_has_out_expr (f: field) : Tot bool =
  match f.v with
  | AtomicField af ->
    atomic_field_has_out_expr af
  | RecordField fs _ ->
    record_has_out_expr fs
  | SwitchCaseField sw _ ->
    switch_case_has_out_expr sw

and record_has_out_expr (fs: record) : Tot bool =
  match fs with
  | [] -> false
  | f :: fs' ->
    if field_has_out_expr f
    then true
    else record_has_out_expr fs'

and switch_case_has_out_expr (sw: switch_case) : Tot bool =
  let (_, c) = sw in
  cases_have_out_expr c

and cases_have_out_expr (cs: list case) : Tot bool =
  match cs with
  | [] -> false
  | c :: cs ->
    if case_has_out_expr c
    then true
    else cases_have_out_expr cs

and case_has_out_expr (c: case) : Tot bool =
  match c with
  | Case _ f
  | DefaultCase f
    ->
    field_has_out_expr f

/// Matches parse_field
let decl_has_out_expr (d: decl) : Tot bool =
  match d.d_decl.v with
  | Record _ _ _ _ ast_fields ->
    record_has_out_expr ast_fields
  | CaseType _ _ _ switch_case ->
    switch_case_has_out_expr switch_case
  | _ -> false

(** Equality on expressions and types **)

/// eq_expr partially decides equality on expressions, by requiring
/// syntactic equality

let eq_idents (i1 i2:ident) : Tot bool =
  i1.v.modul_name = i2.v.modul_name && i1.v.name = i2.v.name


let eq_op (o1 o2:op) : bool =
  match o1, o2 with
  | Eq, Eq
  | Neq, Neq
  | And, And
  | Or, Or
  | Not, Not
  | SizeOf, SizeOf
  | IfThenElse, IfThenElse -> true
  | BitFieldOf sz0 o0, BitFieldOf sz1 o1 -> sz0 = sz1 && o0 = o1
  | Plus i, Plus j
  | Minus i, Minus j 
  | Mul i, Mul j
  | Division i, Division j
  | Remainder i, Remainder j
  | BitwiseAnd i, BitwiseAnd j
  | BitwiseOr i, BitwiseOr j
  | BitwiseXor i, BitwiseXor j
  | BitwiseNot i, BitwiseNot j
  | ShiftLeft i, ShiftLeft j
  | ShiftRight i, ShiftRight j
  | LT i, LT j
  | GT i, GT j
  | LE i, LE j
  | GE i, GE j
    -> i = j
  | Cast i1 t1, Cast i2 t2 -> i1 = i2 && t1 = t2
  | Ext s1, Ext s2 -> s1 = s2
  | ProbeFunctionName i1, ProbeFunctionName i2 -> eq_idents i1 i2
  | _ -> false

let rec eq_expr (e1 e2:expr) : Tot bool (decreases e1) =
  match e1.v, e2.v with
  | Constant i, Constant j -> i = j
  | Identifier i, Identifier j -> i.v = j.v
  | This, This -> true
  | App op1 es1, App op2 es2 ->
    eq_op op1 op2
    && eq_exprs es1 es2
  | _ -> false

and eq_exprs (es1 es2:list expr) : Tot bool =
  match es1, es2 with
  | [], [] -> true
  | hd1::es1, hd2::es2 -> eq_expr hd1 hd2 && eq_exprs es1 es2
  | _ -> false

/// eq_typ: syntactic equalty of types

let rec eq_out_expr (o1 o2:out_expr) : bool =
  match o1.out_expr_node.v, o2.out_expr_node.v with
  | OE_id i1, OE_id i2 -> eq_idents i1 i2
  | OE_star o1, OE_star o2
  | OE_addrof o1, OE_addrof o2 -> eq_out_expr o1 o2
  | OE_deref o1 i1, OE_deref o2 i2
  | OE_dot o1 i1, OE_dot o2 i2 -> eq_idents i1 i2 && eq_out_expr o1 o2
  | _ -> false

let eq_typ_param (p1 p2:typ_param) : bool =
  match p1, p2 with
  | Inl e1, Inl e2 -> eq_expr e1 e2
  | Inr o1, Inr o2 -> eq_out_expr o1 o2
  | _ -> false

let rec eq_typ_params (ps1 ps2:list typ_param) : bool =
  match ps1, ps2 with
  | [], [] -> true
  | p1::ps1, p2::ps2 -> eq_typ_param p1 p2 && eq_typ_params ps1 ps2
  | _ -> false

let eq_opt (f:'a -> 'a -> bool) (x y:option 'a) =
  match x, y with
  | None, None -> true
  | Some x, Some y -> f x y
  | _ -> false

let eq_pointer_qualifier (q1 q2:pointer_qualifier) =
  let PQ a1, PQ a2 = q1, q2 in
  a1=a2

let rec eq_typ (t1 t2:typ) : Tot bool =
  match t1.v, t2.v with
  | Type_app hd1 k1 gs1 ps1, Type_app hd2 k2 gs2 ps2 ->
    eq_idents hd1 hd2
    && k1 = k2
    && eq_exprs gs1 gs2
    && eq_typ_params ps1 ps2
  | Pointer t1 q1, Pointer t2 q2 ->
    eq_typ t1 t2
    && eq_pointer_qualifier q1 q2
  | Type_arrow ts1 t1, Type_arrow ts2 t2 ->
    eq_typs ts1 ts2
    && eq_typ t1 t2
  | _ -> false
and eq_typs (ts1 ts2:list typ) : Tot bool =
  match ts1, ts2 with
  | [], [] -> true
  | t1::ts1, t2::ts2 -> eq_typ t1 t2 && eq_typs ts1 ts2
  | _ -> false

(** Common AST constants and builders **)
let dummy_range = dummy_pos, dummy_pos
let with_dummy_range x = with_range x dummy_range
let to_ident' x = {modul_name=None;name=x}
let mk_prim_t x = with_dummy_range (Type_app (with_dummy_range (to_ident' x)) KindSpec [] [])
let tbool = mk_prim_t "Bool"
let tunit = mk_prim_t "unit"
let tuint8 = mk_prim_t "UINT8"
let tuint8be = mk_prim_t "UINT8BE"
let puint8 = mk_prim_t "PUINT8"
let tuint16 = mk_prim_t "UINT16"
let tuint32 = mk_prim_t "UINT32"
let tuint64 = mk_prim_t "UINT64"
let type_of_integer_type = function
  | UInt8  -> tuint8
  | UInt16 -> tuint16
  | UInt32 -> tuint32
  | UInt64 -> tuint64
let tcopybuffer = mk_prim_t "EVERPARSE_COPY_BUFFER_T"
let as_u64_identity = with_dummy_range <| to_ident' "as_u64_identity"
let probe_m_t = mk_prim_t "probe_m_unit"
let tunknown = mk_prim_t "?"
let unit_atomic_field rng = 
    let dummy_identifier = with_range (to_ident' "_empty_") rng in
    let f = {
         field_dependence=false;
         field_ident=dummy_identifier;
         field_type=tunit;
         field_array_opt=FieldScalar;
         field_constraint=None;
         field_bitwidth=None;
         field_action=None;
         field_probe=None
        } in
    with_range f rng

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
  | Static e -> { e with v = Static (subst_expr s e) }
  | App op es -> {e with v = App op (List.map (subst_expr s) es)}
let subst_atomic_action (s:subst) (aa:atomic_action) : ML atomic_action =
  match aa with
  | Action_return e -> Action_return (subst_expr s e)
  | Action_assignment lhs rhs -> Action_assignment lhs (subst_expr s rhs)
  | Action_call f args -> Action_call f (List.map (subst_expr s) args)
  | _ -> aa //action mutable identifiers are not subject to substitution
let rec subst_action (s:subst) (a:action) : ML action =
  match a.v with
  | Atomic_action aa -> {a with v = Atomic_action (subst_atomic_action s aa)}
  | Action_seq hd tl -> {a with v = Action_seq (subst_atomic_action s hd) (subst_action s tl) }
  | Action_ite hd then_ else_ -> {a with v = Action_ite (subst_expr s hd) (subst_action s then_) (subst_action_opt s else_) }
  | Action_let i aa k -> {a with v = Action_let i (subst_atomic_action s aa) (subst_action s k) }
  | Action_act a -> {a with v = Action_act (subst_action s a) }
and subst_action_opt (s:subst) (a:option action) : ML (option action) =
  match a with
  | None -> None
  | Some a -> Some (subst_action s a)
let subst_probe_atomic_action (s:subst) (aa:probe_atomic_action) : ML probe_atomic_action =
  match aa with
  | Probe_action_return e -> Probe_action_return (subst_expr s e)
  | Probe_action_call f args -> Probe_action_call f (List.map (subst_expr s) args)
  | Probe_action_read f -> Probe_action_read f
  | Probe_action_write f value -> Probe_action_write f (subst_expr s value)
  | Probe_action_copy f len -> Probe_action_copy f (subst_expr s len)
  | Probe_action_skip len -> Probe_action_skip (subst_expr s len)
  | Probe_action_fail -> Probe_action_fail

let rec subst_probe_action (s:subst) (a:probe_action) : ML probe_action =
  match a.v with
  | Probe_atomic_action aa ->
    {a with v = Probe_atomic_action (subst_probe_atomic_action s aa)}
  | Probe_action_var i ->
    { a with v = Probe_action_var (subst_expr s i) }
  | Probe_action_simple f n -> 
    {a with v = Probe_action_simple f (subst_expr s n) }
  | Probe_action_seq hd tl ->
    {a with v = Probe_action_seq (subst_probe_action s hd) (subst_probe_action s tl) }
  | Probe_action_let i aa k ->
    {a with v = Probe_action_let i (subst_probe_atomic_action s aa) (subst_probe_action s k) }
  | Probe_action_ite hd then_ else_ ->
    {a with v = Probe_action_ite (subst_expr s hd) (subst_probe_action s then_) (subst_probe_action s else_) }
//No need to substitute in output expressions
let subst_out_expr (s:subst) (o:out_expr) : out_expr = o
let subst_typ_param (s:subst) (p:typ_param) : ML typ_param =
  match p with
  | Inl e -> Inl (subst_expr s e)
  | Inr oe -> Inr (subst_out_expr s oe)
let rec subst_typ (s:subst) (t:typ) : ML typ =
  match t.v with
  | Type_app hd k gs ps -> { t with v = Type_app hd k (List.map (subst_expr s) gs)  (List.map (subst_typ_param s) ps) }
  | Pointer t q -> {t with v = Pointer (subst_typ s t) q }
  | Type_arrow ts t -> mk_arrow (List.map (subst_typ s) ts) (subst_typ s t)

let subst_field_array (s:subst) (f:field_array_t) : ML field_array_t =
  match f with
  | FieldScalar -> f
  | FieldArrayQualified (e, q) -> FieldArrayQualified (subst_expr s e, q)
  | FieldString sz -> FieldString (map_opt (subst_expr s) sz)
  | FieldConsumeAll -> f
let rec subst_field (s:subst) (ff:field) : ML field =
  match ff.v with
  | AtomicField f -> {ff with v = AtomicField (subst_atomic_field s f)}
  | RecordField f i -> {ff with v = RecordField (subst_record s f) i}
  | SwitchCaseField f i -> {ff with v = SwitchCaseField (subst_switch_case s f) i}
and subst_atomic_field (s:subst) (f:atomic_field) : ML atomic_field =
  let sf = f.v in
  let a =
    match sf.field_action with
    | None -> None
    | Some (a, b) -> Some (subst_action s a, b)
  in
  let pa =
    match sf.field_probe with
    | None -> None
    | Some { probe_dest; probe_block; probe_ptr_as_u64 } ->
      Some {
        probe_dest;
        probe_block=subst_probe_action s probe_block; 
        probe_ptr_as_u64
      }
  in
  let sf = {
      sf with
      field_type = subst_typ s sf.field_type;
      field_array_opt = subst_field_array s sf.field_array_opt;
      field_constraint = map_opt (subst_expr s) sf.field_constraint;
      field_action = a;
      field_probe = pa
  } in
  { f with v = sf }  
and subst_record (s:subst) (f:record) : ML record   
  = List.map (subst_field s) f
and subst_case (s:subst) (c:case) : ML case =
  match c with
  | Case e f -> Case (subst_expr s e) (subst_field s f)
  | DefaultCase f -> DefaultCase (subst_field s f)
and subst_switch_case (s:subst) (sc:switch_case) : ML switch_case =
  subst_expr s (fst sc), List.map (subst_case s) (snd sc)
let subst_params (s:subst) (p:list param) : ML (list param) =
  List.map (fun (t, i, q) -> subst_typ s t, i, q) p
let subst_decl' (s:subst) (d:decl') : ML decl' =
  match d with
  | ModuleAbbrev _ _ -> d
  | Define i None _ -> d
  | Define i (Some t) c -> Define i (Some (subst_typ s t)) c
  | TypeAbbrev attrs t i generics params ->
    TypeAbbrev attrs (subst_typ s t) i generics (subst_params s params)
  | Enum t i is -> Enum (subst_typ s t) i is
  | Record names generics params where fields ->
    Record names generics (subst_params s params) (map_opt (subst_expr s) where) (List.map (subst_field s) fields)
  | CaseType names generics params cases ->
    CaseType names generics (subst_params s params) (subst_switch_case s cases)
  | ProbeFunction i params a tn -> ProbeFunction i (subst_params s params) (subst_probe_action s a) tn
  | CoerceProbeFunctionStub i params tn -> 
    CoerceProbeFunctionStub i (subst_params s params) tn
  | Specialize _ _ _
  | OutputType _
  | ExternType _
  | ExternFn _ _ _ _
  | ExternProbe _ _ -> d
  
let subst_decl (s:subst) (d:decl) : ML decl = decl_with_v d (subst_decl' s d.d_decl.v)

type weak_kind =
  | WeakKindWeak
  | WeakKindStrongPrefix
  | WeakKindConsumesAll

let print_weak_kind (k: weak_kind) : Tot string =
  match k with
  | WeakKindConsumesAll -> "WeakKindConsumesAll"
  | WeakKindStrongPrefix -> "WeakKindStrongPrefix"
  | WeakKindWeak -> "WeakKindWeak"

let weak_kind_glb (w1 w2: weak_kind) : Tot weak_kind =
  if w1 = w2
  then w1
  else WeakKindWeak


let field_tag_equal (f0 f1:field) = 
  match f0.v, f1.v with
  | AtomicField _, AtomicField _
  | RecordField _ _, RecordField _ _
  | SwitchCaseField _ _, SwitchCaseField _ _ -> true
  | _ -> false

let extend_substitute (s:list (ident & expr)) 
                      (g:list generic_inst & list generic_param)
                      (p:list typ_param & list param)
: ML subst
= let (gs, gs') = g in
  let (ps, ps') = p in
  if List.existsb Inr? ps //it contains out-exprs
  then failwith "Type abbreviations instantiated with out-exprs are not supported";
  let ps = List.collect (function Inl v -> [v] | _ -> [] ) ps in
  if List.length gs <> List.length gs' || List.length ps <> List.length ps'
  then failwith "Substitution lists must have the same length";
  s @
  List.map2 (fun g (GenericProbeFunction x _ _) -> (x, g)) gs gs' @
  List.map2 (fun p (_, x, _) -> (x, p)) ps ps' |>
  mk_subst

let substitute = extend_substitute []

let idents_of_decl (d:decl) =
  match d.d_decl.v with
  | ModuleAbbrev i _
  | Define i _ _ 
  | TypeAbbrev _ _ i _ _
  | Enum _ i _
  | ExternFn i _ _ _
  | ExternProbe i _
  | ProbeFunction i _ _ _
  | CoerceProbeFunctionStub i _ _
  | Specialize _ _ i -> [i]
  | Record names _ _ _ _
  | CaseType names _ _ _
  | OutputType { out_typ_names = names } 
  | ExternType names -> [names.typedef_name; names.typedef_abbrev]
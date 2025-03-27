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
module Target
(* The abstract syntax for the code produced by 3d *)
#set-options "--warn_error -290"
open FStar.All
module A = Ast
open Binding
open FStar.List.Tot
let lookup (s:subst) (i:A.ident) : option expr =
  List.Tot.assoc i.v s

let rec subst_expr (s:subst) (e:expr)
: expr
= match fst e with
  | Constant _ -> e
  | Identifier i -> (
    match lookup s i with
    | Some e' -> e'
    | None -> e
  )
  | App hd args -> (
    App hd (subst_exprs s args), snd e
  )
  | Record tn fields -> (
    Record tn (subst_fields s fields), snd e
  )
and subst_exprs s es =
  match es with
  | [] -> []
  | e::es -> subst_expr s e :: subst_exprs s es
and subst_fields s fs =
  match fs with
  | [] -> []
  | (i, e)::fs -> (i, subst_expr s e)::subst_fields s fs

let eq_op (o1 o2:op) : bool =
match o1, o2 with
| Eq, Eq -> true
| Neq, Neq -> true
| And, And -> true
| Or, Or -> true
| Not, Not -> true
| Plus t1, Plus t2
| Minus t1, Minus t2
| Mul t1, Mul t2
| Division t1, Division t2
| Remainder t1, Remainder t2
| BitwiseAnd t1, BitwiseAnd t2
| BitwiseXor t1, BitwiseXor t2
| BitwiseOr t1, BitwiseOr t2
| BitwiseNot t1, BitwiseNot t2
| ShiftRight t1, ShiftRight t2
| ShiftLeft t1, ShiftLeft t2
| LT t1, LT t2
| GT t1, GT t2
| LE t1, LE t2
| GE t1, GE t2 -> t1 = t2
| IfThenElse, IfThenElse -> true
| BitFieldOf s1 o1, BitFieldOf s2 o2 -> s1 = s2 && o1 = o2
| Cast f1 t1, Cast f2 t2 -> f1 = f2 && t1 = t2
| Ext s1, Ext s2 -> s1 = s2
| ProbeFunctionName i1, ProbeFunctionName i2 -> A.(eq_idents i1 i2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match fst e1, fst e2 with
  | Constant c1, Constant c2 -> c1=c2
  | Identifier i1, Identifier i2 -> A.(i1.v = i2.v)
  | App hd1 args1, App hd2 args2 -> eq_op hd1 hd2 && exprs_eq args1 args2
  | Record t1 fields1, Record t2 fields2 -> A.(t1.v = t2.v) && fields_eq fields1 fields2
  | _ -> false
and exprs_eq es1 es2 =
  match es1, es2 with
  | [], [] -> true
  | e1::es1, e2::es2 -> expr_eq e1 e2 && exprs_eq es1 es2
  | _ -> false
and fields_eq fs1 fs2 =
  match fs1, fs2 with
  | [], [] -> true
  | (i1, e1)::fs1, (i2, e2)::fs2 ->
    A.(i1.v = i2.v)
    && fields_eq fs1 fs2
  | _ -> false
let rec parser_kind_eq k k' =
  match k.pk_kind, k'.pk_kind with
  | PK_return, PK_return -> true
  | PK_impos, PK_impos -> true
  | PK_list k0 n0,  PK_list k1 n1 -> parser_kind_eq k0 k1 && n0=n1
  | PK_t_at_most,  PK_t_at_most -> true
  | PK_t_exact,  PK_t_exact -> true
  | PK_base hd1, PK_base hd2 -> A.(hd1.v = hd2.v)
  | PK_filter k, PK_filter k' -> parser_kind_eq k k'
  | PK_and_then k1 k2, PK_and_then k1' k2'
  | PK_glb k1 k2, PK_glb k1' k2' ->
    parser_kind_eq k1 k1'
    && parser_kind_eq k2 k2'
  | _ -> false

let has_output_types (ds:list decl) : bool =
  List.Tot.existsb (fun (d, _) -> Output_type? d) ds

let has_output_type_exprs (ds:list decl) : bool =
  List.Tot.existsb (fun (d, _) -> Output_type_expr? d) ds

let has_extern_types (ds:list decl) : bool =
  List.Tot.existsb (fun (d, _) -> Extern_type? d) ds

let has_extern_functions (ds:list decl) : bool =
  List.Tot.existsb (fun (d, _) -> Extern_fn? d) ds

let has_extern_probes (ds:list decl) : bool =
  List.Tot.existsb (fun (d, _) -> Extern_probe? d) ds

let has_external_api (ds:list decl) : bool =
  has_output_type_exprs ds
  || has_extern_types ds
  || has_extern_functions ds
  || has_extern_probes ds
// Some constants

let default_attrs = {
    is_hoisted = false;
    is_entrypoint = false;
    is_if_def = false;
    is_exported = false;
    should_inline = false;
    comments = []
}

let error_handler_name =
  let open A in
  let id' = {
    modul_name = None;
    name = "handle_error";
  } in
  let id = with_range id' dummy_range in
  id
  
let error_handler_decl =
  let open A in
  let error_handler_id' = {
    modul_name = Some "EverParse3d.Actions.Base";
    name = "error_handler"
  } in
  let error_handler_id = with_range error_handler_id' dummy_range in
  let typ = T_app error_handler_id KindSpec [] in
  let a = Assumption (error_handler_name, typ) in
  a, default_attrs

////////////////////////////////////////////////////////////////////////////////
// Printing the target AST in F* concrete syntax
////////////////////////////////////////////////////////////////////////////////

let maybe_mname_prefix (mname:string) (i:A.ident) =
  let open A in
  match i.v.modul_name with
  | None -> ""
  | Some s -> if s = mname then "" else Printf.sprintf "%s." s

let print_ident (i:A.ident) =
  let open A in
  match String.list_of_string i.v.name with
  | [] -> i.v.name
  | c0::_ ->
    if FStar.Char.lowercase c0 = c0
    then i.v.name
    else Ast.reserved_prefix^i.v.name

let print_maybe_qualified_ident (mname:string) (i:A.ident) =
  Printf.sprintf "%s%s" (maybe_mname_prefix mname i) (print_ident i)

let print_field_id_name (i:A.ident) =
  let open A in
  match i.v.modul_name with
  | None -> failwith "Unexpected: module name missing from the field id"
  | Some m -> Printf.sprintf "%s_%s" (String.lowercase m) i.v.name

let print_integer_type =
  let open A in
  function
   | UInt8 -> "uint8"
   | UInt16 -> "uint16"
   | UInt32 -> "uint32"
   | UInt64 -> "uint64"

let namespace_of_integer_type =
  let open A in
  function
   | UInt8 -> "UInt8"
   | UInt16 -> "UInt16"
   | UInt32 -> "UInt32"
   | UInt64 -> "UInt64"

let print_range (r:A.range) : string =
  let open A in
  Printf.sprintf "(FStar.Range.mk_range \"%s\" %d %d %d %d)"
    (fst r).filename
    (fst r).line
    (fst r).col
    (snd r).line
    (snd r).col

let arith_op (o:op) =
  match o with
  | Plus _
  | Minus _
  | Mul _
  | Division _
  | Remainder _
  | ShiftLeft _
  | ShiftRight _
  | BitwiseAnd _
  | BitwiseOr _
  | BitwiseXor _
  | BitwiseNot _ -> true
  | _ -> false

let integer_type_of_arith_op (o:op{arith_op o}) =
  match o with
  | Plus t
  | Minus t
  | Mul t
  | Division t
  | Remainder t
  | ShiftLeft t
  | ShiftRight t
  | BitwiseAnd t
  | BitwiseOr t
  | BitwiseXor t
  | BitwiseNot t -> t

let print_arith_op_range () : ML bool =
  List.length (Options.get_equate_types_list ()) = 0

let print_arith_op
  (o:op{arith_op o})
  (r:option A.range) : ML string
  = let fn =
      match o with
      | Plus _ -> "add"
      | Minus _ -> "sub"
      | Mul _ -> "mul"
      | Division _ -> "div"
      | Remainder _ -> "rem"
      | ShiftLeft _ -> "shift_left"
      | ShiftRight _ -> "shift_right"
      | BitwiseAnd _ -> "logand"
      | BitwiseOr _ -> "logor"
      | BitwiseXor _ -> "logxor"
      | BitwiseNot _ -> "lognot"
    in

    if print_arith_op_range ()
    then
      let t =
        match integer_type_of_arith_op o with
        | A.UInt8 -> "u8"
        | A.UInt16 -> "u16"
        | A.UInt32 -> "u32"
        | A.UInt64 -> "u64"
      in
      let r = match r with | Some r -> r | None -> A.dummy_range in
      Printf.sprintf "EverParse3d.Prelude.%s_%s %s"
        t fn (print_range r)
    else
      let m =
        match integer_type_of_arith_op o with
        | A.UInt8 -> "FStar.UInt8"
        | A.UInt16 -> "FStar.UInt16"
        | A.UInt32 -> "FStar.UInt32"
        | A.UInt64 -> "FStar.UInt64"
      in
      Printf.sprintf "%s.%s" m fn

let is_infix =
  function
  | Eq
  | Neq
  | And
  | Or -> true
  | _ -> false

// Bitfield operators from EverParse3d.Prelude.StaticHeader are least
// significant bit first by default, following MSVC
// (https://learn.microsoft.com/en-us/cpp/c-language/c-bit-fields)
let print_bitfield_bit_order = function
  | A.LSBFirst -> ""
  | A.MSBFirst -> "_msb_first"

let print_op_with_range ropt o =
  match o with
  | Eq -> "="
  | Neq -> "<>"
  | And -> "&&"
  | Or -> "||"
  | Not -> "not"
  | Plus _
  | Minus _
  | Mul _
  | Division _
  | Remainder _
  | ShiftLeft _
  | ShiftRight _
  | BitwiseAnd _
  | BitwiseOr _
  | BitwiseXor _
  | BitwiseNot _ -> print_arith_op o ropt
  | LT t -> Printf.sprintf "FStar.%s.lt" (namespace_of_integer_type t)
  | GT t -> Printf.sprintf "FStar.%s.gt" (namespace_of_integer_type t)
  | LE t -> Printf.sprintf "FStar.%s.lte" (namespace_of_integer_type t)
  | GE t -> Printf.sprintf "FStar.%s.gte" (namespace_of_integer_type t)
  | IfThenElse -> "ite"
  | BitFieldOf i order -> Printf.sprintf "get_bitfield%d%s" i (print_bitfield_bit_order order)
  | Cast from to ->
    let tfrom = print_integer_type from in
    let tto = print_integer_type to in
    if tfrom = tto
    then "EverParse3d.Prelude.id"
    else Printf.sprintf "EverParse3d.Prelude.%s_to_%s" tfrom tto
  | Ext s -> s
  | ProbeFunctionName i -> print_ident i

let print_op = print_op_with_range None

let rec print_expr (mname:string) (e:expr) : ML string =
  match fst e with
  | Constant c ->
    A.print_constant c
  | Identifier i -> print_maybe_qualified_ident mname i
  | Record nm fields ->
    Printf.sprintf "{ %s }" (String.concat "; " (print_fields mname fields))
  | App op [e1;e2] ->
    if is_infix op
    then
      Printf.sprintf "(%s %s %s)"
                   (print_expr mname e1)
                   (print_op_with_range (Some (snd e)) (App?.hd (fst e)))
                   (print_expr mname e2)
    else
      Printf.sprintf "(%s %s %s)"
                   (print_op_with_range (Some (snd e)) (App?.hd (fst e)))
                   (print_expr mname e1)
                   (print_expr mname e2)
  | App Not [e1]
  | App (BitwiseNot _) [e1] ->
    Printf.sprintf "(%s %s)" (print_op (App?.hd (fst e))) (print_expr mname e1)
  | App IfThenElse [e1;e2;e3] ->
    Printf.sprintf
      "(if %s then %s else %s)"
      (print_expr mname e1) (print_expr mname e2) (print_expr mname e3)
  | App (BitFieldOf i order) [e1;e2;e3] ->
    Printf.sprintf
      "(%s %s %s %s)"
      (print_op (BitFieldOf i order))
      (print_expr mname e1) (print_expr mname e2) (print_expr mname e3)
  | App op [] ->
    print_op op
  | App op es ->
    Printf.sprintf "(%s %s)" (print_op op) (String.concat " " (print_exprs mname es))

and print_exprs (mname:string) (es:list expr) : ML (list string) =
  match es with
  | [] -> []
  | hd::tl -> print_expr mname hd :: print_exprs mname tl

and print_fields (mname:string) (fs:_) : ML (list string) =
  match fs with
  | [] -> []
  | (x, e)::tl ->
    Printf.sprintf "%s = %s" (print_ident x) (print_expr mname e)
    :: print_fields mname tl

let print_lam (#a:Type) (f:a -> ML string) (x:lam a) : ML string =
  match x with
  | Some x, y ->
    Printf.sprintf ("(fun %s -> %s)")
      (print_ident x)
      (f y)
  | None, y -> f y

let print_expr_lam (mname:string) (x:lam expr) : ML string =
  print_lam (print_expr mname) x

let rec is_output_type (t:typ) : bool =
  match t with
  | T_app _ A.KindOutput [] -> true
  | T_pointer t A.UInt64 -> is_output_type t
  | _ -> false

let rec is_extern_type (t:typ) : bool =
  match t with
  | T_app _ A.KindExtern [] -> true
  | T_pointer t A.UInt64 -> is_extern_type t
  | _ -> false

(*
 * An output type is printed as the ident, or p_<ident>
 *
 * They are abstract types in the emitted F* code
 *)
let print_output_type (qual:bool) (t:typ) : ML string =
  let rec aux (t:typ)
    : ML (option string & string)
    = match t with
      | T_app id _ _ ->
        id.v.modul_name, print_ident id
      | T_pointer t A.UInt64 ->
        let m, i = aux t in
        m, Printf.sprintf "p_%s" i
      | _ -> failwith "Print: not an output type"
  in
  let mopt, i = aux t in
  if qual 
  then match mopt with
       | None -> i
       | Some m -> Printf.sprintf "%s.ExternalTypes.%s" m i
  else i

let rec print_typ (mname:string) (t:typ) : ML string = //(decreases t) =
  if is_output_type t
  then print_output_type true t
  else
  match t with
  | T_false -> "False"
  | T_app hd _ args ->  //output types are already handled at the beginning of print_typ
    let hd' =
      if hd.v = Ast.to_ident' "void"
      then "unit"
      else print_maybe_qualified_ident mname hd
    in
    Printf.sprintf "(%s %s)"
      hd'
      (String.concat " " (print_indexes mname args))
  | T_nlist elt n ->
    Printf.sprintf "(nlist %s %s)"
      (print_expr mname n)
      (print_typ mname elt)
  | T_pair t1 t2 ->
    Printf.sprintf "(%s & %s)"
      (print_typ mname t1)
      (print_typ mname t2)
  | T_dep_pair t1 (x, t2) ->
    Printf.sprintf "(%s:%s & %s)"
      (print_ident x)
      (print_typ mname t1)
      (print_typ mname t2)
  | T_refine t e ->
    Printf.sprintf "(refine %s %s)"
      (print_typ mname t)
      (print_expr_lam mname e)
  | T_if_else e t1 t2 ->
    Printf.sprintf "(t_ite %s (fun _ -> %s) (fun _ -> %s))"
      (print_expr mname e)
      (print_typ mname t1)
      (print_typ mname t2)
  | T_pointer t i -> Printf.sprintf "bpointer (%s)" (print_typ mname t)
  | T_with_action t _
  | T_with_dep_action t _
  | T_with_comment t _ -> print_typ mname t
  | T_with_probe t _ _ _ _ _ _ -> Printf.sprintf "%s probe" (print_typ mname t)
  | T_arrow [] t -> print_typ mname t
  | T_arrow ts t ->
    Printf.sprintf "(%s -> %s)"
      (String.concat " -> " (List.map (print_typ mname) ts))
      (print_typ mname t)
and print_indexes (mname:string) (is:list index) : ML (list string) = //(decreases is) =
  match is with
  | [] -> []
  | Inl t::is -> print_typ mname t::print_indexes mname is
  | Inr e::is -> print_expr mname e::print_indexes mname is

let rec print_kind (mname:string) (k:parser_kind) : Tot string =
  match k.pk_kind with
  | PK_base hd ->
    Printf.sprintf "%skind_%s"
      (maybe_mname_prefix mname hd)
      (print_ident hd)
  | PK_list k0 n ->
    Printf.sprintf "(kind_nlist %s %s)"
      (print_kind mname k0)
      (match n with
       | None -> "None"
       | Some n -> Printf.sprintf "(Some %d)" n)
  | PK_t_at_most ->
    "kind_t_at_most"
  | PK_t_exact ->
    "kind_t_exact"
  | PK_return ->
    "ret_kind"
  | PK_impos ->
    "impos_kind"
  | PK_and_then k1 k2 ->
    Printf.sprintf "(and_then_kind %s %s)"
      (print_kind mname k1)
      (print_kind mname k2)
  | PK_glb k1 k2 ->
    Printf.sprintf "(glb %s %s)"
      (print_kind mname k1)
      (print_kind mname k2)
  | PK_filter k ->
    Printf.sprintf "(filter_kind %s)"
      (print_kind mname k)
  | PK_string ->
    "parse_string_kind"

let print_params (mname:string) (params:list param) : ML string =
  String.concat " " <|
  List.map 
    (fun (id, t) -> 
      Printf.sprintf "(%s:%s)"
                    (print_ident id)
                    (print_typ mname t))
    params

let print_typedef_name (mname:string) (tdn:typedef_name) : ML string =
  Printf.sprintf "%s %s"
                 (print_ident tdn.td_name)
                 (print_params mname tdn.td_params)


let rec print_action (mname:string) (a:action) : ML string =
  let print_atomic_action (a:atomic_action)
    : ML string
    = match a with
      | Action_return e ->
        Printf.sprintf "(action_return %s)" (print_expr mname e)
      | Action_abort -> "(action_abort())"
      | Action_field_pos_64 -> "(action_field_pos_64())"
      | Action_field_pos_32 -> "(action_field_pos_32 EverParse3d.Actions.BackendFlagValue.backend_flag_value)"
      | Action_field_ptr -> "(action_field_ptr EverParse3d.Actions.BackendFlagValue.backend_flag_value)"
      | Action_field_ptr_after sz write_to ->
        Printf.sprintf "(action_field_ptr_after EverParse3d.Actions.BackendFlagValue.backend_flag_value %s %s)" (print_expr mname sz) (print_ident write_to)
      | Action_field_ptr_after_with_setter sz write_to_field write_to_obj ->
        Printf.sprintf "(action_field_ptr_after_with_setter EverParse3d.Actions.BackendFlagValue.backend_flag_value %s (%s %s))"
          (print_expr mname sz)
          (print_ident write_to_field)
          (print_expr mname write_to_obj)
      | Action_deref i ->
        Printf.sprintf "(action_deref %s)" (print_ident i)
      | Action_assignment lhs rhs ->
        Printf.sprintf "(action_assignment %s %s)" (print_ident lhs) (print_expr mname rhs)
      | Action_call f args ->
        Printf.sprintf "(mk_extern_action (%s %s))" (print_ident f) (String.concat " " (List.map (print_expr mname) args))
  in
  match a with
  | Atomic_action a ->
    print_atomic_action a
  | Action_seq hd tl ->
    Printf.sprintf "(action_seq %s %s)"
                    (print_atomic_action hd)
                    (print_action mname tl)
  | Action_ite hd then_ else_ ->
    Printf.sprintf "(action_ite %s (fun _ -> %s) (fun _ -> %s))"
      (print_expr mname hd)
      (print_action mname then_)
      (print_action mname else_)
  | Action_let i a k ->
    Printf.sprintf "(action_bind \"%s\" %s (fun %s -> %s))"
                   (print_ident i)
                   (print_atomic_action a)
                   (print_ident i)
                   (print_action mname k)
  | Action_act a -> 
    Printf.sprintf "(action_act %s)" 
      (print_action mname a)
      
let rec print_probe_action (mname:string) (p:probe_action) : ML string =
  let print_atomic_probe_action (p:atomic_probe_action) : ML string =
    match p with
    | Atomic_probe_and_copy bytes_to_read probe_fn ->
      Printf.sprintf "(Atomic_probe_and_copy %s %s)"
      (print_expr mname bytes_to_read)
      (print_ident probe_fn)
    | Atomic_probe_and_read reader ->
      Printf.sprintf "(Atomic_probe_and_read %s)"
      (print_ident reader)
    | Atomic_probe_write_at_offset v writer ->
      Printf.sprintf "(Atomic_probe_write_at_offset %s %s)"
      (print_expr mname v)
      (print_ident writer)
    | Atomic_probe_call_pure f args ->
      Printf.sprintf "(Atomic_probe_call_pure (%s %s))"
      (print_ident f)
      (String.concat " " (List.map (print_expr mname) args))
    | Atomic_probe_skip_read n ->
      Printf.sprintf "(Atomic_probe_skip_read %s)"
      (print_expr mname n)
    | Atomic_probe_skip_write n ->
      Printf.sprintf "(Atomic_probe_skip_write %s)"
      (print_expr mname n)
    | Atomic_probe_init f n ->
      Printf.sprintf "(Atomic_probe_init %s %s)"
      (print_ident f)
      (print_expr mname n)
    | Atomic_probe_return v ->
      Printf.sprintf "(Atomic_probe_return %s)"
      (print_expr mname v)
    | Atomic_probe_fail ->
      "(Atomic_probe_fail)"
  in
  match p with
  | Probe_action_atomic a ->
    Printf.sprintf "(Probe_action_atomic %s)" (print_atomic_probe_action a)
  | Probe_action_var e ->
    Printf.sprintf "(Probe_action_var %s)" (print_expr mname e)
  | Probe_action_simple bytes_to_read probe_fn ->
    Printf.sprintf "(Probe_action_simple %s %s)" (print_expr mname bytes_to_read) (print_ident probe_fn)
  | Probe_action_seq p1 p2 ->
    Printf.sprintf "(Probe_action_seq %s %s)" (print_probe_action mname p1) (print_probe_action mname p2)
  | Probe_action_let i m1 m2 ->
    Printf.sprintf "(Probe_action_let %s (fun %s -> %s))" (print_atomic_probe_action m1) (print_ident i) (print_probe_action mname m2)
  | Probe_action_ite cond m1 m2 ->
    Printf.sprintf "(Probe_action_ite %s %s %s)" (print_expr mname cond) (print_probe_action mname m1) (print_probe_action mname m2)


let print_typedef_typ (tdn:typedef_name) : ML string =
  Printf.sprintf "%s %s"
    (print_ident tdn.td_name)
    (String.concat " "
      (List.map (fun (id, t) -> (print_ident id)) tdn.td_params))

let print_typedef_body (mname:string) (b:typedef_body) : ML string =
  match b with
  | TD_abbrev t -> print_typ mname t
  | TD_struct fields ->
    let print_field (sf:field) : ML string =
        Printf.sprintf "%s : %s%s"
          (print_ident sf.sf_ident)
          (print_typ mname sf.sf_typ)
          (if sf.sf_dependence then " (*dep*)" else "")
    in
    let fields = String.concat ";\n" (List.map print_field fields) in
    Printf.sprintf "{\n%s\n}" fields

let print_typedef_actions_inv_and_fp (td:type_decl) =
    //we need to add output loc to the modifies locs
    //if there is an output type type parameter
    let should_add_output_loc =
      List.Tot.existsb (fun (_, t) -> is_output_type t || is_extern_type t) td.decl_name.td_params in
    let pointers =  //get only non output type pointers
      List.Tot.filter (fun (x, t) -> T_pointer? t && not (is_output_type t || is_extern_type t)) td.decl_name.td_params
    in
    let inv =
      List.Tot.fold_right
        (fun (x, t) out ->
          Printf.sprintf "((ptr_inv %s) `conj_inv` %s)"
                         (print_ident x)
                         out)
        pointers
        "true_inv"
    in
    let fp =
      List.Tot.fold_right
        (fun (x, t) out ->
          Printf.sprintf "(eloc_union (ptr_loc %s) %s)"
                         (print_ident x)
                         out)
        pointers
        (if should_add_output_loc then "output_loc" else "eloc_none")
    in
    inv, fp

let print_comments (cs:list string) : string =
  match cs with
  | [] -> ""
  | _ ->
    let c = String.concat "\\n\\\n" cs in
    Printf.sprintf " (Comment \"%s\")" c

let print_attributes (entrypoint:bool) (attrs:decl_attributes) : string =
  match attrs.comments with
  | [] ->
    if entrypoint || attrs.is_exported
    then ""
    else if attrs.should_inline
    then "inline_for_extraction noextract\n"
    else "[@ (CInline)]\n"
  | cs ->
    Printf.sprintf "[@ %s %s]\n%s"
      (print_comments cs)
      (if not entrypoint &&
          not attrs.is_exported &&
          not attrs.should_inline 
       then "(CInline)" else "")
      (if attrs.should_inline then "inline_for_extraction\n" else "")


/// Printing a decl for M.Types.fst
///
/// Print all the definitions, and for a Type_decl, only the type definition

let maybe_print_type_equality (mname:string) (td:type_decl) : ML string =
  if td.decl_name.td_entrypoint
  then
    let equate_types_list = Options.get_equate_types_list () in
    (match (List.tryFind (fun (_, m) -> m = mname) equate_types_list) with
     | Some (a, _) ->
       let typname = A.ident_name td.decl_name.td_name in
       Printf.sprintf "\n\nlet _ = assert (%s.Types.%s == %s) by (FStar.Tactics.trefl ())\n\n"
         a typname typname         
     | None -> "")
  else ""

let print_definition (mname:string) (d:decl { Definition? (fst d)} ) : ML string =
  match fst d with
  | Definition (x, [], T_app ({Ast.v={Ast.name="field_id"}}) _ _, (Constant c, _)) ->
    Printf.sprintf "[@(CMacro)%s]\nlet %s = %s <: Tot field_id by (FStar.Tactics.trivial())\n\n"
     (print_comments (snd d).comments)
     (print_field_id_name x)
     (A.print_constant c)

  | Definition (x, [], t, (Constant c, _)) ->
    Printf.sprintf "[@(CMacro)%s]\nlet %s = %s <: Tot %s\n\n"
      (print_comments (snd d).comments)
      (print_ident x)
      (A.print_constant c)
      (print_typ mname t) 
  
  | Definition (x, params, typ, expr) ->
    let x_ps = {
      td_name = x;
      td_params = params;
      td_entrypoint_probes = [];
      td_entrypoint = false;
      td_noextract = false;
    } in
    Printf.sprintf "%slet %s : %s = %s\n\n"
      (print_attributes false (snd d))
      (print_typedef_name mname x_ps)
      (print_typ mname typ)
      (print_expr mname expr)

let print_assumption (mname:string) (d:decl { Assumption? (fst d) } ) : ML string =
  match fst d with
  | Assumption (x, t) ->
    Printf.sprintf "%sassume\nval %s : %s\n\n"
      (if (snd d).is_if_def then "[@@ CIfDef ]\n" else "")
      (print_ident x)      
      (print_typ mname t) 

/// Print a decl for M.fst
///
/// No need to print Definition(s), they are `include`d from M.Types.fst
///
/// For a Type_decl, if it is an entry point, we need to emit a definition since
///   there is a corresponding declaration in the .fsti
///   We make the definition as simply the definition in M.Types.fst

let is_type_abbreviation (td:type_decl) : bool =
  match td.decl_typ with
  | TD_abbrev _ -> true
  | TD_struct _ -> false


let external_api_include (modul:string) (ds:list decl) : string =
  if has_external_api ds
  then Printf.sprintf "open %s.ExternalAPI\n\n" modul
  else ""

#push-options "--z3rlimit_factor 4"
let pascal_case name : ML string =
  let chars = String.list_of_string name in
  let has_underscore = List.mem '_' chars in
  let keep, up, low = 0, 1, 2 in
  if has_underscore then
    let what_next : ref int = alloc up in
    let rewrite_char c : ML (list FStar.Char.char) =
      match c with
      | '_' ->
        what_next := up;
        []
      | c ->
        let c_next =
          let n = !what_next in
          if n = keep then c
          else if n = up then FStar.Char.uppercase c
          else FStar.Char.lowercase c
        in
        let _ =
          if Char.uppercase c = c
          then what_next := low
          else if Char.lowercase c = c
          then what_next := keep
        in
        [c_next]
    in
    let chars = List.collect rewrite_char (String.list_of_string name) in
    String.string_of_list chars
  else if String.length name = 0
  then name
  else String.uppercase (String.sub name 0 1) ^ String.sub name 1 (String.length name - 1)

let uppercase (name:string) : string = String.uppercase name

let rec print_as_c_type (t:typ) : ML string =
    let open Ast in
    match t with
    | T_pointer t A.UInt64 ->
          Printf.sprintf "%s*" (print_as_c_type t)
    | T_app {v={name="Bool"}} _ [] ->
          "BOOLEAN"
    | T_app {v={name="UINT8"}} _ [] ->
          "uint8_t"
    | T_app {v={name="UINT16"}} _ [] ->
          "uint16_t"
    | T_app {v={name="UINT32"}} _ [] ->
          "uint32_t"
    | T_app {v={name="UINT64"}} _ [] ->
          "uint64_t"
    | T_app {v={name="PUINT8"}} _ [] ->
          "uint8_t*"
    | T_app {v={name=x}} KindSpec [] ->
          x
    | T_app {v={name=x}} _ [] ->
          uppercase x
    | _ ->
         "__UNKNOWN__"

let error_code_macros = 
   //To be kept consistent with EverParse3d.ErrorCode.error_reason_of_result
   "#define EVERPARSE_ERROR_GENERIC 1uL\n\
    #define EVERPARSE_ERROR_NOT_ENOUGH_DATA 2uL\n\
    #define EVERPARSE_ERROR_IMPOSSIBLE 3uL\n\
    #define EVERPARSE_ERROR_LIST_SIZE_NOT_MULTIPLE 4uL\n\
    #define EVERPARSE_ERROR_ACTION_FAILED 5uL\n\
    #define EVERPARSE_ERROR_CONSTRAINT_FAILED 6uL\n\
    #define EVERPARSE_ERROR_UNEXPECTED_PADDING 7uL\n"

let rec get_output_typ_dep (modul:string) (t:typ) : ML (option string) =
  match t with
  | T_app {v={modul_name=None}} _ _ -> None
  | T_app {v={modul_name=Some m}} _ _ ->
    if m = modul then None
    else Some m
  | T_pointer t _ -> get_output_typ_dep modul t
  | _ -> failwith "get_typ_deps: unexpected output type"

let wrapper_name
  (modul: string)
  (fn: string)
: ML string
= Printf.sprintf "%s_check_%s"
    modul
    fn
  |> pascal_case

let probe_wrapper_name
  (modul: string)
  (probe_fn: string)
  (fn: string)
: ML string
= Printf.sprintf "%s_%s_check_%s" modul probe_fn fn
    |> pascal_case

let validator_name
  (modul: string)
  (fn: string)
: ML string
= Printf.sprintf "%s_validate_%s"
    modul
    fn
  |> pascal_case

let define_ident_to_c
  (i: A.ident)
: Tot string
= Printf.sprintf "%s__%s"
    (match i.v.modul_name with
      | None -> ""
      | Some m -> uppercase m ^ "__")
    (uppercase i.v.name)

let expr_to_c
  (e: expr)
: ML string
= match fst e with
  | Constant (A.Int _ i) -> Printf.sprintf "%dU" i
  | Constant (A.XInt tag x) ->
    let print_tag = function
      | A.UInt8 -> "uy"
      | A.UInt16 -> "us"
      | A.UInt32 -> "ul"
      | A.UInt64 -> "uL"
    in
    let tag = print_tag tag in
    let x =
      if String.length x >= 2
      && String.sub x (String.length x - 2) 2 = tag
      then String.sub x 0 (String.length x - 2)
      else x
    in
    Printf.sprintf "%sU" x
  | Identifier i -> define_ident_to_c i
  | _ -> A.error "expr_to_c: this case should have been removed by Binding" (snd e)

let probe_fn_to_c (i: A.ident) : Tot string =
  i.v.name

let print_c_entry
                  (produce_everparse_error: opt_produce_everparse_error)
                  (modul: string)
                  (env: global_env)
                  (ds:list decl)
    : ML (string & string)
    =  let default_error_handler =
         "static\n\
          void DefaultErrorHandler(\n\t\
                              const char *typename_s,\n\t\
                              const char *fieldname,\n\t\
                              const char *reason,\n\t\
                              uint64_t error_code,\n\t\
                              uint8_t *context,\n\t\
                              EVERPARSE_INPUT_BUFFER input,\n\t\
                              uint64_t start_pos)\n\
          {\n\t\
            EVERPARSE_ERROR_FRAME *frame = (EVERPARSE_ERROR_FRAME*)context;\n\t\
            EverParseDefaultErrorHandler(\n\t\t\
              typename_s,\n\t\t\
              fieldname,\n\t\t\
              reason,\n\t\t\
              error_code,\n\t\t\
              frame,\n\t\t\
              input,\n\t\t\
              start_pos\n\t\
            );\n\
          }" 
   in
   let input_stream_binding = Options.get_input_stream_binding () in
   let is_input_stream_buffer = HashingOptions.InputStreamBuffer? input_stream_binding in
   let wrapped_call_buffer name params =
     Printf.sprintf
       "EVERPARSE_ERROR_FRAME frame;\n\t\
       frame.filled = FALSE;\n\t\
       %s\
       uint64_t result = %s(%s (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);\n\t\
       if (EverParseIsError(result))\n\t\
       {\n\t\t\
         if (frame.filled)\n\t\t\
         {\n\t\t\t\
           %sEverParseError(frame.typename_s, frame.fieldname, frame.reason);\n\t\t\
         }\n\t\t\
         return FALSE;\n\t\
       }\n\t\
       return TRUE;"
       (if is_input_stream_buffer then ""
         else "EVERPARSE_INPUT_BUFFER input = EverParseMakeInputBuffer(base);\n\t")
        name
        params
        modul
   in
   let wrapped_call_probe_buffer wrappedName params (probe: probe_entrypoint) : ML string =
     let len = expr_to_c probe.probe_ep_length in
     Printf.sprintf
      "if (%s(probeAddr, %s, probeDest)) {
         uint8_t * base = EverParseStreamOf(probeDest);
         return %s(%s base, %s);
       } else {
         // FIXME: we currently assume that the probe function handles its own error
         return FALSE;
       }"
       (probe_fn_to_c probe.probe_ep_fn)
       len
       wrappedName
       params
       len
   in
   let wrapped_call_stream name params =
     Printf.sprintf
       "EVERPARSE_ERROR_FRAME frame =\n\t\
             { .filled = FALSE,\n\t\
               .typename_s = \"UNKNOWN\",\n\t\
               .fieldname =  \"UNKNOWN\",\n\t\
               .reason =   \"UNKNOWN\",\n\t\
               .error_code = 0uL\n\
             };\n\
       EVERPARSE_INPUT_BUFFER input = EverParseMakeInputBuffer(base);\n\t\
       uint64_t result = %s(%s (uint8_t*)&frame, &DefaultErrorHandler, input, 0);\n\t\
       uint64_t parsedSize = EverParseGetValidatorErrorPos(result);\n\
       if (EverParseIsError(result))\n\t\
       {\n\t\t\
           EverParseHandleError(_extra, parsedSize, frame.typename_s, frame.fieldname, frame.reason, frame.error_code);\n\t\t\
       }\n\t\
       EverParseRetreat(_extra, base, parsedSize);\n\
       return parsedSize;"
       name
       params
   in
   let wrapped_call_probe_stream wrappedName params (probe: probe_entrypoint) : ML string =
     let len = print_expr modul probe.probe_ep_length in
     Printf.sprintf
      "if (%s(probeAddr, %s, probeDest)) {
         EVERPARSE_INPUT_STREAM_BASE * base = EverParseStreamOf(probeDest);
         return %s(%s base);
       } else {
         // FIXME: we currently assume that the probe function handles its own error
         return 0;
       }"
       (probe_fn_to_c probe.probe_ep_fn)
       len
       wrappedName
       params
   in
   let mk_param (name: string) (typ: string) : Tot param =
     (A.with_range (A.to_ident' name) A.dummy_range, T_app (A.with_range (A.to_ident' typ) A.dummy_range) A.KindSpec [])
   in
   let print_validators_for_one_decl (d:type_decl) : ML (list (string & string)) =
    let params = 
      d.decl_name.td_params @
      (if is_input_stream_buffer then [] else [mk_param "_extra" "EVERPARSE_EXTRA_T"])
    in
    let print_params (ps:list param) : ML string =
      let params =
        String.concat
          ", "
          (List.map
            (fun (id, t) -> Printf.sprintf "%s %s" (print_as_c_type t) (print_ident id))
            ps)
       in
       match ps with
       | [] -> params
       | _ -> params ^ ", "
    in
    let print_arguments (ps:list param) : Tot string =
      let params =
        String.concat
          ", "
          (List.Tot.map
            (fun (id, t) ->
             if is_output_type t  //output type pointers are uint8_t* in the F* generated code
             then (print_ident id)
             else print_ident id)
            ps)
       in
       match ps with
       | [] -> params
       | _ -> params ^ ", "
    in
    let wrapper_name = wrapper_name modul d.decl_name.td_name.A.v.A.name in
    let impl signature body =
      Printf.sprintf "%s {\n\t%s\n}" 
        signature body
    in
    let constr_wrapper signature body =
      (signature ^ ";", impl signature body)
    in
    (* Main wrapper *)
    let pparams = print_params params in
    let pargs = print_arguments params in
    let signature =
      if is_input_stream_buffer 
      then Printf.sprintf
            "BOOLEAN %s(%suint8_t *base, uint32_t len)"
             wrapper_name
             pparams
      else Printf.sprintf
            "uint64_t %s(%sEVERPARSE_INPUT_STREAM_BASE base)"
             wrapper_name
             pparams
    in
    let validator_name = validator_name modul d.decl_name.td_name.A.v.A.name in
    let body = 
      if is_input_stream_buffer
      then wrapped_call_buffer validator_name pargs
      else wrapped_call_stream validator_name pargs
    in
    (* Probe wrapper *)
    let probe_wrapper_signature probe : ML _ =
      let return_type =
        if is_input_stream_buffer 
        then "BOOLEAN"
        else "uint64_t"
      in
      let probe_fn = probe_fn_to_c probe.probe_ep_fn in
      let probe_wrapper_name = probe_wrapper_name modul probe_fn d.decl_name.td_name.A.v.A.name in
      Printf.sprintf
            "%s %s(%sEVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr)"
             return_type
             probe_wrapper_name
             pparams
    in
    let probe_wrapper (probe: probe_entrypoint) : ML _ =
      constr_wrapper
        (probe_wrapper_signature probe)
        (if is_input_stream_buffer
          then wrapped_call_probe_buffer wrapper_name pargs probe
          else wrapped_call_probe_stream wrapper_name pargs probe
        )
    in
    (* Collecting everything together *)
    constr_wrapper signature body :: List.map probe_wrapper d.decl_name.td_entrypoint_probes
  in

  let signatures_output_typ_deps =
    List.fold_left (fun deps (d, _) ->
      match d with
      | Type_decl d ->
        if d.decl_name.td_entrypoint
        then let params = d.decl_name.td_params in
             List.fold_left (fun deps (_, t) ->
               match get_output_typ_dep modul t with
               | Some dep -> if List.mem dep deps then deps else deps@[dep]
               | _ -> deps) deps params
        else deps
      | _ -> deps) [] ds in
               
  let signatures, impls =
    List.split
      (List.collect
        (fun d ->
          match fst d with
          | Type_decl d ->
            if d.decl_name.td_entrypoint
            then print_validators_for_one_decl d
            else []
          | _ -> [])
        ds)
  in

  let external_defs_includes =
    if not (Options.get_emit_output_types_defs ()) then "" else
    let deps =
      if List.length signatures_output_typ_deps = 0
      then ""
      else
        String.concat
          ""
          (List.map
             (fun dep -> Printf.sprintf "#include \"%s_ExternalTypedefs.h\"\n\n" dep)
             signatures_output_typ_deps) in
    let self =
      if has_output_types ds || has_extern_types ds
      then Printf.sprintf "#include \"%s_ExternalTypedefs.h\"\n" modul
      else "" in
    Printf.sprintf "%s\n%s\n\n" deps self in

  let header =
    Printf.sprintf
      "#include \"EverParseEndianness.h\"\n\
       %s\n\
       %s\
       #ifdef __cplusplus\n\
       extern \"C\" {\n\
       #endif\n\
       %s\n\
       #ifdef __cplusplus\n\
       }\n\
       #endif\n"
      error_code_macros
      external_defs_includes
      (signatures |> String.concat "\n\n")
  in
  let input_stream_include = HashingOptions.input_stream_include input_stream_binding in
  let header =
    if input_stream_include = ""
    then header
    else Printf.sprintf
      "#include \"%s\"\n\
      %s"
      input_stream_include
      header
  in
  let add_includes = Options.make_includes () in
  let header = Printf.sprintf "%s%s" add_includes header in
  let error_callback_proto =
    if HashingOptions.InputStreamBuffer? input_stream_binding
    then Printf.sprintf 
          "void %sEverParseError(const char *StructName, const char *FieldName, const char *Reason)%s"
              modul
               (if produce_everparse_error = Some ProduceEverParseError
                then "{(void) StructName; (void) FieldName; (void) Reason;}"
                else ";")
    else ""
  in
  let external_api_from_decl (accu: list string) (d: decl) : Tot (list string) =
    match fst d with
      | Type_decl d ->
        let probe_modules = List.Tot.map (fun ep -> match ep.probe_ep_fn.v.modul_name with Some s -> s | _ -> "") d.decl_name.td_entrypoint_probes in
        List.Tot.filter (fun x -> x <> "" && not (List.Tot.mem x accu)) probe_modules `List.Tot.append` accu
      | _ -> accu
  in
  let include_external_api_from_module (accu: string) (modu: string) : Tot string =
    Printf.sprintf "%s#include \"%s_ExternalAPI.h\"\n" accu modu
  in
  let include_external_api =
    ds
    |> List.Tot.fold_left external_api_from_decl []
    |> List.Tot.fold_left include_external_api_from_module ""
  in
  let impl =
    Printf.sprintf
      "#include \"%sWrapper.h\"\n\
       #include \"EverParse.h\"\n\
       #include \"%s.h\"\n\
       %s\
       %s\n\n\
       %s\n\n\
       %s\n"
      modul
      modul
      include_external_api
      error_callback_proto
      default_error_handler
      (impls |> String.concat "\n\n")
  in
  let impl =
    if input_stream_include = ""
    then impl
    else
      Printf.sprintf
        "#include \"%s\"\n\
        %s"
        input_stream_include
        impl
  in
  let impl = Printf.sprintf "%s%s" add_includes impl in
  header,
  impl


/// Functions for printing setters and getters for output expressions

let rec out_bt_name (t:typ) : ML string =
  match t with
  | T_app i _ _ -> A.ident_name i
  | T_pointer t A.UInt64 -> out_bt_name t
  | _ -> failwith "Impossible, out_bt_name received a non output type!"

let out_expr_bt_name (oe:output_expr) : ML string = out_bt_name oe.oe_bt

(*
 * Walks over the output expressions AST and constructs a string
 *)
let rec out_fn_name (oe:output_expr) : ML string =
  match oe.oe_expr with
  | T_OE_id _ -> out_expr_bt_name oe
  | T_OE_star oe -> Printf.sprintf "%s_star" (out_fn_name oe)
  | T_OE_addrof oe -> Printf.sprintf "%s_addrof" (out_fn_name oe)
  | T_OE_deref oe f -> Printf.sprintf "%s_deref_%s" (out_fn_name oe) (A.ident_name f)
  | T_OE_dot oe f -> Printf.sprintf "%s_dot_%s" (out_fn_name oe) (A.ident_name f)

module H = Hashtable
type set = H.t string unit

(*
 * In the printing functions, a hashtable tracks that we print a defn. only once
 *
 * E.g. multiple output expressions may require a val decl. for types,
 *   we need to print them only once each
 *)

let rec base_output_type (t:typ) : ML A.ident =
  match t with
  | T_app id A.KindOutput [] -> id
  | T_pointer t A.UInt64 -> base_output_type t
  | _ -> failwith "Target.base_output_type called with a non-output type"
#push-options "--fuel 1"
let rec print_output_type_val (tbl:set) (t:typ) : ML string =
  let open A in
  if is_output_type t
  then let s = print_output_type false t in
       if H.try_find tbl s <> None then ""
       else let _ = H.insert tbl s () in
            assert (is_output_type t);
            match t with
            | T_app id KindOutput [] ->
              Printf.sprintf "\n\nval %s : Type0\n\n" s
            | T_pointer bt A.UInt64 ->
              let bs = print_output_type_val tbl bt in
              bs ^ (Printf.sprintf "\n\ninline_for_extraction noextract type %s = bpointer %s\n\n" s (print_output_type false bt))
  else ""
#pop-options

let rec print_out_expr' (oe:output_expr') : ML string =
  match oe with
  | T_OE_id id -> A.ident_to_string id
  | T_OE_star o -> Printf.sprintf "*(%s)" (print_out_expr' o.oe_expr)
  | T_OE_addrof o -> Printf.sprintf "&(%s)" (print_out_expr' o.oe_expr)
  | T_OE_deref o i -> Printf.sprintf "(%s)->%s" (print_out_expr' o.oe_expr) (A.ident_to_string i)
  | T_OE_dot o i -> Printf.sprintf "(%s).%s" (print_out_expr' o.oe_expr) (A.ident_to_string i)


(*
 * F* val for the setter for the output expression
 *)

let print_out_expr_set_fstar (tbl:set) (mname:string) (oe:output_expr) : ML string =
  let fn_name = Printf.sprintf "set_%s" (out_fn_name oe) in
  match H.try_find tbl fn_name with
  | Some _ -> ""
  | _ ->
    H.insert tbl fn_name ();
    //TODO: module name?
    let fn_arg1_t = print_typ mname oe.oe_bt in
    let fn_arg2_t =
      (*
       * If bitwidth is not None,
       *   then output the size restriction in the refinement
       * Is there a better way to output it?
       *)
      if oe.oe_bitwidth = None
      then print_typ mname oe.oe_t
      else begin
        Printf.sprintf "(i:%s{FStar.UInt.size (FStar.Integers.v i) %d})"
          (print_typ mname oe.oe_t)
          (Some?.v oe.oe_bitwidth)
      end in
    Printf.sprintf
        "\n\nval %s (_:%s) (_:%s) : extern_action unit (NonTrivial output_loc)\n\n"
        fn_name
        fn_arg1_t
        fn_arg2_t

let rec base_id_of_output_expr (oe:output_expr) : A.ident =
  match oe.oe_expr with
  | T_OE_id id -> id
  | T_OE_star oe
  | T_OE_addrof oe
  | T_OE_deref oe _
  | T_OE_dot oe _ -> base_id_of_output_expr oe

(*
 * C defn. for the setter for the output expression
 *)

let print_out_expr_set (tbl:set) (oe:output_expr) : ML string =
  let fn_name = pascal_case (Printf.sprintf "set_%s" (out_fn_name oe)) in
  match H.try_find tbl fn_name with
  | Some _ -> ""
  | _ ->
    H.insert tbl fn_name ();
    let fn_arg1_t = print_as_c_type oe.oe_bt in
    let fn_arg1_name = base_id_of_output_expr oe in
    let fn_arg2_t = print_as_c_type oe.oe_t in
    let fn_arg2_name = "__v" in
    let fn_body = Printf.sprintf
      "%s = %s;"
      (print_out_expr' oe.oe_expr)
      fn_arg2_name in
    let fn = Printf.sprintf
      "void %s (%s %s, %s %s){\n    %s;\n}\n"
      fn_name
      fn_arg1_t
      (A.ident_name fn_arg1_name)
      fn_arg2_t
      fn_arg2_name
      fn_body in
    Printf.sprintf "\n\n%s\n\n" fn

(*
 * F* val for the getter for the output expression
 *)

let print_out_expr_get_fstar (tbl:set) (mname:string) (oe:output_expr) : ML string =
  let fn_name = Printf.sprintf "get_%s" (out_fn_name oe) in
  match H.try_find tbl fn_name with
  | Some _ -> ""
  | _ ->
    H.insert tbl fn_name ();
    let fn_arg1_t = print_typ mname oe.oe_bt in
    let fn_res = print_typ mname oe.oe_t in  //No bitfields, we could enforce?
    Printf.sprintf "\n\nval %s : %s -> %s\n\n" fn_name fn_arg1_t fn_res

(*
 * C defn. for the getter for the output expression
 *)

let print_out_expr_get(tbl:set) (oe:output_expr) : ML string =
  let fn_name = pascal_case (Printf.sprintf "get_%s" (out_fn_name oe)) in
  match H.try_find tbl fn_name with
  | Some _ -> ""
  | _ ->
    H.insert tbl fn_name ();
    let fn_arg1_t = print_as_c_type oe.oe_bt in
    let fn_arg1_name = base_id_of_output_expr oe in
    let fn_res = print_as_c_type oe.oe_t in
    let fn_body = Printf.sprintf "return %s;" (print_out_expr' oe.oe_expr) in
    let fn = Printf.sprintf "%s %s (%s %s){\n    %s;\n}\n"
      fn_res
      fn_name
      fn_arg1_t
      (A.ident_name fn_arg1_name)
      fn_body in
    Printf.sprintf "\n\n%s\n\n" fn

let output_setter_name lhs = Printf.sprintf "set_%s" (out_fn_name lhs)
let output_getter_name lhs = Printf.sprintf "get_%s" (out_fn_name lhs)
let output_base_var lhs = base_id_of_output_expr lhs

let print_external_types_fstar_interpreter (modul:string) (ds:decls) : ML string =
  let tbl = H.create 10 in
  let s = String.concat "" (ds |> List.map (fun d ->
    match fst d with
    | Output_type ot ->
      let t = T_app ot.out_typ_names.typedef_abbrev A.KindOutput [] in
      Printf.sprintf "%s%s"
        (print_output_type_val tbl t)
        (print_output_type_val tbl (T_pointer t A.UInt64))
    | Extern_type i ->
      Printf.sprintf "\n\nval %s : Type0\n\n" (print_ident i)
    | _ -> "")) in
   Printf.sprintf
    "module %s.ExternalTypes\n\n\
     open EverParse3d.Prelude\n\
     open EverParse3d.Actions.All\n\n%s"
     modul
    s

let print_external_api_fstar_interpreter (modul:string) (ds:decls) : ML string =
  let tbl = H.create 10 in
  let s = String.concat "" (ds |> List.map (fun d ->
    match fst d with
    // | Output_type ot ->
    //   let t = T_app ot.out_typ_names.typedef_name A.KindOutput [] in
    //   Printf.sprintf "%s%s"
    //     (print_output_type_val tbl t)
    //     (print_output_type_val tbl (T_pointer t))
    | Output_type_expr oe is_get ->
      Printf.sprintf "%s"
        // (print_output_type_val tbl oe.oe_bt)
        // (print_output_type_val tbl oe.oe_t)
        (if not is_get then print_out_expr_set_fstar tbl modul oe
         else print_out_expr_get_fstar tbl modul oe)
    | Extern_type i ->
      Printf.sprintf "\n\nval %s : Type0\n\n" (print_ident i)
    | Extern_fn f ret params false ->
      Printf.sprintf "\n\nval %s %s : extern_action %s (NonTrivial output_loc)\n"
        (print_ident f)
        (String.concat " " (params |> List.map (fun (i, t) -> Printf.sprintf "(%s:%s)"
          (print_ident i)
          (print_typ modul t))))
        (print_typ modul ret)
    | Extern_fn f ret params true ->
      Printf.sprintf "\n\nval %s %s : EverParse3d.ProbeActions.pure_external_action %s\n"
        (print_ident f)
        (String.concat " " (params |> List.map (fun (i, t) -> Printf.sprintf "(%s:%s)"
          (print_ident i)
          (print_typ modul t))))
        (print_typ modul ret)
    | Extern_probe f PQSimple ->
      Printf.sprintf "\n\nval %s : EverParse3d.ProbeActions.probe_fn\n\n" (print_ident f)
    | Extern_probe f PQWithOffsets ->
      Printf.sprintf "\n\nval %s : EverParse3d.ProbeActions.probe_fn_incremental\n\n" (print_ident f)
    | Extern_probe f (PQRead t) ->
      Printf.sprintf "\n\nval %s : EverParse3d.ProbeActions.probe_and_read_at_offset_%s \n\n" 
              (print_ident f)
              (print_integer_type t)
    | Extern_probe f (PQWrite t) ->
      Printf.sprintf "\n\nval %s : EverParse3d.ProbeActions.write_at_offset_%s \n\n" 
              (print_ident f)
              (print_integer_type t)
    | Extern_probe f PQInit ->
      Printf.sprintf "\n\nval %s : EverParse3d.ProbeActions.init_probe_dest_t \n\n" 
              (print_ident f)
    | _ -> "")) in

   let external_types_include =
     if has_output_types ds || has_extern_types ds
     then Printf.sprintf "include %s.ExternalTypes\n\n" modul
     else "" in

   Printf.sprintf
    "module %s.ExternalAPI\n\n\
     open EverParse3d.Prelude\n\
     open EverParse3d.Actions.All\n\
     open EverParse3d.Interpreter\n\
     %s\n\
     noextract val output_loc : eloc\n\n%s"
    modul
    external_types_include
    s

//
// When printing output expressions in C,
//   the output types may be coming from some other module
// This function gets all the dependencies from output expressions
//   so that they can be added in the M_OutputTypes.c file
//
let get_out_exprs_deps (modul:string) (ds:decls) : ML (list string) =
  let maybe_add_dep (deps:list string) (s:option string) : list string =
    match s with
    | None -> deps
    | Some s -> if List.mem s deps then deps else deps@[s] in

  List.fold_left (fun deps (d, _) ->
    match d with
    | Output_type_expr oe _ ->
      maybe_add_dep (maybe_add_dep deps (get_output_typ_dep modul oe.oe_bt))
                    (get_output_typ_dep modul oe.oe_t)
    | _ -> deps) [] ds

let print_out_exprs_c modul (ds:decls) : ML string =
  let tbl = H.create 10 in
  let deps = get_out_exprs_deps modul ds in
  let emit_output_types_defs = Options.get_emit_output_types_defs () in
  let dep_includes =
    if List.length deps = 0 || not emit_output_types_defs
    then ""
    else
      String.concat ""
        (List.map (fun s -> FStar.Printf.sprintf "#include \"%s_ExternalTypedefs.h\"\n\n" s) deps) in

  let self_external_typedef_include =
    if has_output_types ds && emit_output_types_defs
    then Printf.sprintf "#include \"%s_ExternalTypedefs.h\"\n\n" modul
    else "" in


  (Printf.sprintf
     "%s#include<stdint.h>\n\n\
      %s\
      %s\
      #if defined(__cplusplus)\n\
      extern \"C\" {\n\
      #endif\n\n"
     (Options.make_includes ())
     dep_includes
     self_external_typedef_include)
  ^
  (String.concat "" (ds |> List.map (fun d ->
     match fst d with
     | Output_type_expr oe is_get ->
       if not is_get then print_out_expr_set tbl oe
       else print_out_expr_get tbl oe
    | _ -> "")))
  ^
  ("#if defined(__cplusplus)\n\
    }\n\
   #endif\n\n")

let rec atyp_to_ttyp (t:A.typ) : ML typ =
  match t.v with
  | A.Pointer t pq ->
    let t = atyp_to_ttyp t in    
    T_pointer t A.UInt64

  | A.Type_app hd _b _gs _args ->
    T_app hd _b []
  
  | A.Type_arrow ts t ->
    let ts = List.map atyp_to_ttyp ts in
    let t = atyp_to_ttyp t in
    T_arrow ts t

let rec print_output_types_fields (flds:list A.out_field) : ML string =
  List.fold_left (fun s fld ->
    let fld_s =
      match fld with
      | A.Out_field_named id t bopt ->
        Printf.sprintf "%s    %s%s;\n"
          (print_as_c_type (atyp_to_ttyp t))
          (A.ident_name id)
          (match bopt with
           | None -> ""
           | Some n -> ":" ^ (string_of_int n))
      | A.Out_field_anon flds is_union ->
        Printf.sprintf "%s  {\n %s };\n"
          (if is_union then "union" else "struct")
          (print_output_types_fields flds) in
    s ^ fld_s) "" flds

let print_out_typ (ot:A.out_typ) : ML string =
  let open A in
  Printf.sprintf
    "\ntypedef %s %s {\n%s\n} %s;\n"
    (if ot.out_typ_is_union then "union" else "struct")
    (uppercase (A.ident_name ot.out_typ_names.typedef_name))
    (print_output_types_fields ot.out_typ_fields)
    (uppercase (A.ident_name ot.out_typ_names.typedef_abbrev))

let print_output_types_defs (modul:string) (ds:decls) : ML string =
  let defs =
    String.concat "\n\n" (List.map (fun (d, _) ->
      match d with
      | Output_type ot -> print_out_typ ot
      | _ -> "") ds) in

  Printf.sprintf
    "#ifndef __%s_OutputTypesDefs_H\n\
     #define __%s_OutputTypesDefs_H\n\n\
     #if defined(__cplusplus)\n\
     extern \"C\" {\n\
     #endif\n\n\n\
     %s%s\n\n\n\
     #if defined(__cplusplus)\n\
     }\n\
     #endif\n\n\
     #define __%s_OutputTypes_H_DEFINED\n\
     #endif\n"

    modul
    modul
    (Options.make_includes ())
    defs
    modul

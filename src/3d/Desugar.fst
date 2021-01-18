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
module Desugar
open FStar.Mul
open Ast
open FStar.All
module H = Hashtable

(* This module implements a pass over the source AST, 
   implementing various simple desugarings

   * Desugar enums with newly defined idents and explicit constant
     assignments to enums where all the tags are previously defined
     constants.
*)

let check_desugared_enum_cases (cases:list enum_case) : ML (list ident) =
    List.map
      (function
        | (i, None) -> i
        | (i, _) -> failwith "Enum should already have been desugared")
     cases

let desugar_enum_cases (ityp:integer_type) (cases:list enum_case)
  : ML (list enum_case & list decl) =
  let find_definition (i:ident) (d:decl) =
    match d.v with
    | Define j _ (Int _ _) -> 
      i.v = j.v
    | _ -> 
      false
  in
  let _, cases_rev, ds_rev =
    List.fold_left
      (fun (next, cases_rev, ds_rev) (i, jopt) ->
        let next =
          match jopt with
          | Some (Inl j) -> j
          | Some (Inr j) -> 
            begin
            match List.Tot.find (find_definition j) ds_rev with
            | Some ({v=Define _ _ (Int _ k)}) -> k
            | _ -> error (Printf.sprintf "Enum identifier %s not found" (print_ident j)) j.range
            end
          | None -> next
        in
        let case = (i, None) in
        let d = with_range_and_comments 
                   (Define i None (Int ityp next))
                   i.range
                   ["Enum constant"]
        in
        (next + 1,
         case :: cases_rev,
         d :: ds_rev))
     (0, [], [])
     cases
  in
  List.rev cases_rev,
  List.rev ds_rev

let desugar_one_enum (d:decl) : ML (list decl) =
  match d.v with
  | Enum t i cases -> 
    if List.for_all (fun (_, jopt) -> None? jopt) cases
    then [d] //no enum value assignments; no desugaring to do
    else //if we have any assignments at all, then we treat all the
         //tags as fresh constants and assign them values in sequence
         //with respect to the assigned values of preceding tags
         let cases, ds = desugar_enum_cases (typ_as_integer_type t) cases in
         let enum = { d with v = Enum t i cases } in
         ds@[enum]
  | _ -> [d]

(* This code is currently not used
   It desugars an Enum to a record with a single refined field *)
let eliminate_enum (d:decl) : ML decl =
  match d.v with 
  | Enum t i cases -> 
    let names = {
      typedef_name = { i with v = { i.v with name=Ast.reserved_prefix ^ Ast.reserved_prefix ^ i.v.name }};
      typedef_abbrev = i;
      typedef_ptr_abbrev = { i with v = {i.v with
                                         name = Ast.reserved_prefix ^ Ast.reserved_prefix ^ "P" ^ i.v.name }};
      typedef_attributes = [];
    } in
    let params = [] in
    let where = None in
    let field_ident = with_dummy_range (to_ident' (Ast.reserved_prefix ^ "enum_field")) in
    let field_ident_expr = with_dummy_range (Identifier field_ident) in
    let field_constraint = 
      List.fold_right 
        (fun (case, _) out ->
          let eq = with_range (App Eq [field_ident_expr; with_range (Identifier case) case.range]) case.range in
          with_dummy_range (App Or [eq; out]))
        cases
        (with_dummy_range (Constant (Bool false)))
    in
    let field = {
       field_dependence = false;
       field_ident = field_ident;
       field_type = t;
       field_array_opt = FieldScalar;
       field_constraint = Some field_constraint;
       field_number = None;
       field_bitwidth = None;
       field_action = None
    } in
    let d' = Record names params where [with_dummy_range field] in
    {d with v = d'}
    
  | _ -> d


type qenv = {
  mname : string;
  local_names : list string
}

let push_name (env:qenv) (name:string) : qenv =
  { env with local_names = name::env.local_names }

let prim_consts = [
  "unit"; "Bool"; "UINT8"; "UINT16"; "UINT32"; "UINT64";
  "field_id"; "PUINT8";
  "is_range_okay" ]

let maybe_qualify_ident (env:qenv) (i:ident) : ML ident =
  if List.mem i.v.name prim_consts     ||
     List.mem i.v.name env.local_names ||
     Some? i.v.modul_name then i
  else { i with v = { i.v with modul_name = Some env.mname } }

let rec qualify_expr' (env:qenv) (e:expr') : ML expr' =
  match e with
  | Constant _ -> e
  | Identifier i -> Identifier (maybe_qualify_ident env i)
  | This -> e
  | App op args -> App op (List.map (qualify_expr env) args)

and qualify_expr (env:qenv) (e:expr) : ML expr = { e with v = qualify_expr' env e.v }

let rec qualify_typ' (env:qenv) (t:typ') : ML typ' =
  match t with
  | Type_app hd args ->
    Type_app (maybe_qualify_ident env hd) (List.map (qualify_expr env) args)
  | Pointer t -> Pointer (qualify_typ env t)

and qualify_typ (env:qenv) (t:typ) : ML typ = { t with v = qualify_typ' env t.v }

let qualify_atomic_action (env:qenv) (ac:atomic_action) : ML atomic_action =
  match ac with
  | Action_return e -> Action_return (qualify_expr env e)
  | Action_abort
  | Action_field_pos
  | Action_field_ptr -> ac
  | Action_deref i -> Action_deref i  //most certainly a type parameter
  | Action_assignment lhs rhs ->
    Action_assignment lhs (qualify_expr env rhs)  //lhs is an action-local variable
  | Action_call f args ->
    Action_call (maybe_qualify_ident env f) (List.map (qualify_expr env) args)

let rec qualify_action' (env:qenv) (act:action') : ML action' =
  match act with
  | Atomic_action ac -> Atomic_action (qualify_atomic_action env ac)
  | Action_seq hd tl ->
    Action_seq (qualify_atomic_action env hd) (qualify_action env tl)
  | Action_ite hd then_ else_ ->
    Action_ite (qualify_expr env hd) (qualify_action env then_) (map_opt (qualify_action env) else_)
  | Action_let i a k ->
    Action_let i (qualify_atomic_action env a) (qualify_action (push_name env i.v.name) k)

and qualify_action (env:qenv) (act:action) : ML action =
  { act with v = qualify_action' env act.v }

let qualify_param (env:qenv) (p:param) : ML param =
  let t, i, q = p in
  qualify_typ env t, i, q

let qualify_field_bitwidth_t (env:qenv) (fb:field_bitwidth_t) : ML field_bitwidth_t =
  let qualify_bitfield_attr' (env:qenv) (b:bitfield_attr') : ML bitfield_attr' =
    { b with bitfield_type = qualify_typ env b.bitfield_type } in

  let qualify_bitfield_attr (env:qenv) (b:bitfield_attr) : ML bitfield_attr =
    { b with v = qualify_bitfield_attr' env b.v } in

  match fb with
  | Inl _ -> fb
  | Inr b -> Inr (qualify_bitfield_attr env b)

let qualify_field_array_t (env:qenv) (farr:field_array_t) : ML field_array_t =
  match farr with
  | FieldScalar -> farr
  | FieldArrayQualified (e, aq) ->
    FieldArrayQualified (qualify_expr env e, aq)
  | FieldString None -> farr
  | FieldString (Some e) -> FieldString (Some (qualify_expr env e))

let qualify_field (env:qenv) (f:field) : ML field =
  let qualify_struct_field (env:qenv) (sf:struct_field) : ML struct_field =
    { sf with
      field_type = qualify_typ env sf.field_type;
      field_array_opt = qualify_field_array_t env sf.field_array_opt;
      field_constraint = map_opt (qualify_expr env) sf.field_constraint;
      field_bitwidth = map_opt (qualify_field_bitwidth_t env) sf.field_bitwidth;
      field_action = map_opt (fun (a, b) -> qualify_action env a, b) sf.field_action } in

  { f with v = qualify_struct_field env f.v }

let qualify_switch_case (env:qenv) (sc:switch_case) : ML switch_case =
  let qualify_case (env:qenv) (c:case) : ML case =
    match c with
    | Case e f -> Case (qualify_expr env e) (qualify_field env f)
    | DefaultCase f -> DefaultCase (qualify_field env f) in

  let e, l = sc in
  qualify_expr env e, List.map (qualify_case env) l

let qualify_typedef_names (env:qenv) (td_names:typedef_names) : ML typedef_names =
  { td_names with
    typedef_name = maybe_qualify_ident env td_names.typedef_name;
    typedef_abbrev = maybe_qualify_ident env td_names.typedef_abbrev;
    typedef_ptr_abbrev = maybe_qualify_ident env td_names.typedef_ptr_abbrev }

let qualify_enum_case (env:qenv) (ec:enum_case) : ML enum_case =
  match ec with
  | i, None -> maybe_qualify_ident env i, None
  | _ -> error "Unexpected enum_case in qualify_enum_case" (fst ec).range

let qualify_decl' (env:qenv) (d:decl') : ML decl' =
  match d with
  | ModuleAbbrev _ _ -> d
  | Define i topt c ->
    Define (maybe_qualify_ident env i) (map_opt (qualify_typ env) topt) c
  | TypeAbbrev t i ->
    TypeAbbrev (qualify_typ env t) (maybe_qualify_ident env i)
  | Enum t i ecs ->
    Enum (qualify_typ env t) (maybe_qualify_ident env i) (List.map (qualify_enum_case env) ecs)
  | Record td_names params where flds ->
    let td_names = qualify_typedef_names env td_names in
    let params = List.map (qualify_param env) params in
    let env = List.fold_left (fun env (_, t, _) -> push_name env t.v.name) env params in
    let where = map_opt (qualify_expr env) where in
    let _, flds = List.fold_left (fun (env, flds) f ->
      let f = qualify_field env f in
      push_name env f.v.field_ident.v.name, flds@[f]) (env, []) flds in
    Record td_names params where flds
  | CaseType td_names params sc ->
    let td_names = qualify_typedef_names env td_names in
    let params = List.map (qualify_param env) params in
    let sc = qualify_switch_case env sc in
    CaseType td_names params sc

let qualify_decl (env:qenv) (d:decl) : ML decl = { d with v = qualify_decl' env d.v }

let desugar (mname:string) (ds:list decl) : ML (list decl) =
  let ds = List.collect desugar_one_enum ds in
  List.map (qualify_decl ({mname=mname; local_names=[]})) ds

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


noeq
type qenv = {
  mname : string;
  module_abbrevs : H.t string string;
  local_names : list string
}

let push_module_abbrev (env:qenv) (i m:string) : ML unit =
  H.insert env.module_abbrevs i m

let push_name (env:qenv) (name:string) : qenv =
  { env with local_names = name::env.local_names }

let prim_consts = [
  "unit"; "Bool"; "UINT8"; "UINT16"; "UINT32"; "UINT64";
  "field_id"; "PUINT8";
  "is_range_okay" ]

let resolve_ident (env:qenv) (i:ident) : ML ident =
  if List.mem i.v.name prim_consts  //it's a primitive constant, e.g. UINT8, leave as is
  then i
  else if List.mem i.v.name env.local_names  //it's a local name (e.g. a parameter name)
       then (if Some? i.v.modul_name  //must have module name set to None
             then error (Printf.sprintf 
                          "Ident %s is a local name but has a qualifying modul %s"
                          i.v.name
                          (Some?.v i.v.modul_name))
                        i.range
             else i)  //return the local name as is
       else (match i.v.modul_name with  //it's a top-level name
             | None -> { i with v = { i.v with modul_name = Some env.mname } }  //if unqualified, add current module
             | Some m ->  //if already qualified, check if it is an abbreviation
               (match H.try_find env.module_abbrevs m with
                | None -> i
                | Some m -> { i with v = { i.v with modul_name = Some m } }))


let rec resolve_expr' (env:qenv) (e:expr') : ML expr' =
  match e with
  | Constant _ -> e
  | Identifier i -> Identifier (resolve_ident env i)
  | This -> e
  | App op args -> App op (List.map (resolve_expr env) args)

and resolve_expr (env:qenv) (e:expr) : ML expr = { e with v = resolve_expr' env e.v }

let rec resolve_typ' (env:qenv) (t:typ') : ML typ' =
  match t with
  | Type_app hd args ->
    Type_app (resolve_ident env hd) (List.map (resolve_expr env) args)
  | Pointer t -> Pointer (resolve_typ env t)

and resolve_typ (env:qenv) (t:typ) : ML typ = { t with v = resolve_typ' env t.v }

let resolve_atomic_action (env:qenv) (ac:atomic_action) : ML atomic_action =
  match ac with
  | Action_return e -> Action_return (resolve_expr env e)
  | Action_abort
  | Action_field_pos
  | Action_field_ptr -> ac
  | Action_deref i -> Action_deref i  //most certainly a type parameter
  | Action_assignment lhs rhs ->
    Action_assignment lhs (resolve_expr env rhs)  //lhs is an action-local variable
  | Action_call f args ->
    Action_call (resolve_ident env f) (List.map (resolve_expr env) args)

let rec resolve_action' (env:qenv) (act:action') : ML action' =
  match act with
  | Atomic_action ac -> Atomic_action (resolve_atomic_action env ac)
  | Action_seq hd tl ->
    Action_seq (resolve_atomic_action env hd) (resolve_action env tl)
  | Action_ite hd then_ else_ ->
    Action_ite (resolve_expr env hd) (resolve_action env then_) (map_opt (resolve_action env) else_)
  | Action_let i a k ->
    Action_let i (resolve_atomic_action env a) (resolve_action (push_name env i.v.name) k)

and resolve_action (env:qenv) (act:action) : ML action =
  { act with v = resolve_action' env act.v }

let resolve_param (env:qenv) (p:param) : ML param =
  let t, i, q = p in
  resolve_typ env t, i, q

let resolve_field_bitwidth_t (env:qenv) (fb:field_bitwidth_t) : ML field_bitwidth_t =
  let resolve_bitfield_attr' (env:qenv) (b:bitfield_attr') : ML bitfield_attr' =
    { b with bitfield_type = resolve_typ env b.bitfield_type } in

  let resolve_bitfield_attr (env:qenv) (b:bitfield_attr) : ML bitfield_attr =
    { b with v = resolve_bitfield_attr' env b.v } in

  match fb with
  | Inl _ -> fb
  | Inr b -> Inr (resolve_bitfield_attr env b)

let resolve_field_array_t (env:qenv) (farr:field_array_t) : ML field_array_t =
  match farr with
  | FieldScalar -> farr
  | FieldArrayQualified (e, aq) ->
    FieldArrayQualified (resolve_expr env e, aq)
  | FieldString None -> farr
  | FieldString (Some e) -> FieldString (Some (resolve_expr env e))

let resolve_field (env:qenv) (f:field) : ML field =
  let resolve_struct_field (env:qenv) (sf:struct_field) : ML struct_field =
    { sf with
      field_type = resolve_typ env sf.field_type;
      field_array_opt = resolve_field_array_t env sf.field_array_opt;
      field_constraint = map_opt (resolve_expr env) sf.field_constraint;
      field_bitwidth = map_opt (resolve_field_bitwidth_t env) sf.field_bitwidth;
      field_action = map_opt (fun (a, b) -> resolve_action env a, b) sf.field_action } in

  { f with v = resolve_struct_field env f.v }

let resolve_switch_case (env:qenv) (sc:switch_case) : ML switch_case =
  let resolve_case (env:qenv) (c:case) : ML case =
    match c with
    | Case e f -> Case (resolve_expr env e) (resolve_field env f)
    | DefaultCase f -> DefaultCase (resolve_field env f) in

  let e, l = sc in
  resolve_expr env e, List.map (resolve_case env) l

let resolve_typedef_names (env:qenv) (td_names:typedef_names) : ML typedef_names =
  { td_names with
    typedef_name = resolve_ident env td_names.typedef_name;
    typedef_abbrev = resolve_ident env td_names.typedef_abbrev;
    typedef_ptr_abbrev = resolve_ident env td_names.typedef_ptr_abbrev }

let resolve_enum_case (env:qenv) (ec:enum_case) : ML enum_case =
  match ec with
  | i, None -> resolve_ident env i, None
  | _ -> error "Unexpected enum_case in resolve_enum_case" (fst ec).range

let resolve_decl' (env:qenv) (d:decl') : ML decl' =
  match d with
  | ModuleAbbrev i m -> push_module_abbrev env i.v.name m.v.name; d
  | Define i topt c ->
    Define (resolve_ident env i) (map_opt (resolve_typ env) topt) c
  | TypeAbbrev t i ->
    TypeAbbrev (resolve_typ env t) (resolve_ident env i)
  | Enum t i ecs ->
    Enum (resolve_typ env t) (resolve_ident env i) (List.map (resolve_enum_case env) ecs)
  | Record td_names params where flds ->
    let td_names = resolve_typedef_names env td_names in
    let params = List.map (resolve_param env) params in
    let env = List.fold_left (fun env (_, t, _) -> push_name env t.v.name) env params in
    let where = map_opt (resolve_expr env) where in
    let _, flds = List.fold_left (fun (env, flds) f ->
      let env = push_name env f.v.field_ident.v.name in
      let f = resolve_field env f in
      env, flds@[f]) (env, []) flds in
    Record td_names params where flds
  | CaseType td_names params sc ->
    let td_names = resolve_typedef_names env td_names in
    let params = List.map (resolve_param env) params in
    let sc = resolve_switch_case env sc in
    CaseType td_names params sc

let resolve_decl (env:qenv) (d:decl) : ML decl = { d with v = resolve_decl' env d.v }

let desugar (mname:string) (ds:list decl) : ML (list decl) =
  let ds = List.collect desugar_one_enum ds in
  List.map (resolve_decl ({mname=mname; module_abbrevs=H.create 10; local_names=[]})) ds

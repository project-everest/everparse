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
module InlineSingletonRecords
open Ast
open FStar.All
module H = Hashtable
type singleton_record = list param & field
let env = H.t ident' singleton_record

(*
  This module implements a pass over the source AST
  
    1. Inlining records that contain only a single field
    2. Inlining enumerated types that have dependences

  Both of these are necessary to avoid double fetches
*)
    
  
let choose_one (a b:option 'a) : ML (option 'a) = 
  match a, b with
  | Some fc, _
  | _, Some fc -> Some fc
  | _ -> None
                 
let simplify_field (env:env) (f:field)
  : ML field
  = let field = f.v in
    let field = 
      match field.field_type.v with
      | Pointer _ -> failwith "Impossible: field types cannot be pointers"
      | Type_app hd args ->
        begin
        match H.try_find env hd.v with
        | None -> //not a singleton record
          field
        | Some (params, inlined_field) ->
          let subst = 
               List.map2 
               (fun (_t, x, _q) e -> (x, e))
               params args
          in
          let subst = (inlined_field.v.field_ident, with_dummy_range (Identifier field.field_ident)) :: subst in
          let inlined_field = subst_field (mk_subst subst) inlined_field in
          match field, inlined_field.v with
          | { field_constraint = Some _ }, { field_constraint = Some _ } ->
            failwith "Singleton field cannot be inlined because of duplicated refinements"
            
          | { field_action = Some _ }, { field_action = Some _ } ->
            failwith "Singleton field cannot be inlined because of duplicated actions"
  
          | { field_constraint = Some _ }, { field_action = Some _ } ->
            failwith "Singleton field cannot be inlined because it would alter order of evaluation of refinement and action"
  
          | { field_array_opt = Some _ }, _        
          | _, { field_array_opt = Some _ } ->
            failwith "Singleton field cannot be inlined because it contains an array"

          | { field_bitwidth = Some _ }, _        
          | _, { field_bitwidth = Some _ } ->
            failwith "Singleton field cannot be inlined because it contains a bitfield"
          
          | _, _ ->
            { field with 
              field_type = inlined_field.v.field_type;
              field_constraint = choose_one field.field_constraint inlined_field.v.field_constraint;
              field_action = choose_one field.field_action inlined_field.v.field_action }
        end
    in
    { f with v = field }

let simplify_decl (env:env) (d:decl) : ML decl =
  match d.v with
  | Define _ _ _ ->
    d

  | TypeAbbrev t i ->
    d

  | Enum t i cases ->
    d
    
  | Record tdnames params None [field] -> //singleton
    begin
    match field.v with
    | { field_array_opt = Some _ }
    | { field_bitwidth = Some _ } ->
       d
    | _ -> 
      let field = simplify_field env field in
      H.insert env tdnames.typedef_name.v (params, field);
      {d with v = Record tdnames params None [field]}
    end
  
  | Record tdnames params wopt fields ->
    let fields = List.map (simplify_field env) fields in
    { d with v = Record tdnames params wopt fields }

  | CaseType tdnames params switch ->
    let hd, cases = switch in
    let cases = List.map (fun (e, f) -> e, simplify_field env f) cases in
    { d with v=CaseType tdnames params (hd, cases) }

let simplify_prog (p:list decl) =
  let env = H.create 10 in
  List.map (simplify_decl env) p

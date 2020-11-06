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
      typedef_name = { i with v = Ast.reserved_prefix ^ Ast.reserved_prefix ^ i.v };
      typedef_abbrev = i;
      typedef_ptr_abbrev = { i with v = Ast.reserved_prefix ^ Ast.reserved_prefix ^ "P" ^ i.v };
      typedef_attributes = [];
    } in
    let params = [] in
    let where = None in
    let field_ident = with_dummy_range (Ast.reserved_prefix ^ "enum_field") in
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
  
  
let desugar (ds:list decl) : ML (list decl) =
  List.collect desugar_one_enum ds


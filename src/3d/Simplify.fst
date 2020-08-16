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
module Simplify
open Ast
open FStar.All
module B = Binding
module T = TypeSizes

(*
  This module implements a pass over the source AST
  
    1. Simplifying refinement expressions, in particular reducing
       sizeof expressions to constants

    2. Reducing typedef abbreviations
*)

let rec simplify_expr (env:T.env_t) (e:expr)
  : ML expr
  = match e.v with
    | This -> failwith "Impossible: should have been eliminated already"
    | App SizeOf _ ->
      begin
      match T.value_of_const_expr env e with
      | Some (Inr (t, n)) -> with_range (Constant (Int t n)) e.range
      | _ -> error "Could not evaluate sizeof to a compile-time constant" e.range
      end
    | App op es ->
      let es = List.map (simplify_expr env) es in
      { e with v = App op es }

    | _ -> e
    
let rec simplify_typ (env:T.env_t) (t:typ)
  : ML typ
  = match t.v with
    | Pointer t -> {t with v=Pointer (simplify_typ env t)}
    | Type_app s es ->
      let es = List.map (simplify_expr env) es in
      let s = B.resolve_typedef_abbrev (fst env) s in
      { t with v = Type_app s es }

let simplify_field (env:T.env_t) (f:field)
  : ML field
  = let sf = f.v in
    let ft = simplify_typ env sf.field_type in
    let fa = sf.field_array_opt |> B.map_opt (fun (e, b) -> simplify_expr env e, b) in
    let fc = sf.field_constraint |> B.map_opt (simplify_expr env) in
    let sf = { sf with field_type = ft;
                       field_array_opt = fa; 
                       field_constraint = fc } in
    { f with v = sf }

let simplify_decl (env:T.env_t) (d:decl) : ML decl =
  match d.v with
  | Define i None c -> d
  | Define i (Some t) c -> { d with v = Define i (Some (simplify_typ env t)) c }

  | TypeAbbrev t i ->
    { d with v = TypeAbbrev (simplify_typ env t) i }

  | Enum t i cases ->
    let t = simplify_typ env t in
    { d with v = Enum t i cases }

  | Record tdnames params wopt fields ->
    let params = List.map (fun (t, i, q) -> simplify_typ env t, i, q) params in
    let fields = List.map (simplify_field env) fields in
    let wopt = match wopt with | None -> None | Some w -> Some (simplify_expr env w) in
    { d with v = Record tdnames params wopt fields }

  | CaseType tdnames params switch ->
    let params = List.map (fun (t, i, q) -> simplify_typ env t, i, q) params in 
    let hd, cases = switch in
    let hd = simplify_expr env hd in
    let cases = List.map (function Case e f -> Case (simplify_expr env e) (simplify_field env f)
                                 | DefaultCase f -> DefaultCase (simplify_field env f)) 
                         cases in
    { d with v=CaseType tdnames params (hd, cases) }

let simplify_prog (env:T.env_t) (p:list decl) =
  List.map (simplify_decl env) p

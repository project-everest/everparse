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
      | _ -> error (Printf.sprintf "Could not evaluate %s to a compile-time constant" (print_expr e)) e.range
      end
    | App op es ->
      let es = List.map (simplify_expr env) es in
      { e with v = App op es }

    | _ -> e

(*
 * Simplify output expressions, mainly their metadata to resolve
 *   abbrevs in the types that appear in the metadata
 *)
let rec simplify_typ_param (env:T.env_t) (p:typ_param) : ML typ_param =
  match p with
  | Inl e -> simplify_expr env e |> Inl
  | Inr oe -> simplify_out_expr env oe |> Inr

and simplify_typ (env:T.env_t) (t:typ)
  : ML typ
  = match t.v with
    | Pointer t -> {t with v=Pointer (simplify_typ env t)}
    | Type_app s b ps ->
      let ps = List.map (simplify_typ_param env) ps in
      let s = B.resolve_record_case_outputtype_name (fst env) s in
      let t = { t with v = Type_app s b ps } in
      if Options.get_interpret()
      then B.unfold_typ_abbrev_only (fst env) t
      else t

and simplify_out_expr_node (env:T.env_t) (oe:with_meta_t out_expr')
  : ML (with_meta_t out_expr')
  = oe

and simplify_out_expr_meta (env:T.env_t) (mopt:option (typ & typ))
  : ML (option (typ & typ))
  = match mopt with
    | None -> None
    | Some (bt, t) ->
      Some (simplify_typ env bt, simplify_typ env t)

and simplify_out_expr (env:T.env_t) (oe:out_expr) : ML out_expr =
  {oe with
   out_expr_node = simplify_out_expr_node env oe.out_expr_node;
   out_expr_meta = simplify_out_expr_meta env oe.out_expr_meta}

let simplify_atomic_action (env:T.env_t) (a:atomic_action)
  : ML atomic_action
  = match a with
    | Action_return e -> Action_return (simplify_expr env e)
    | Action_assignment lhs rhs ->
      Action_assignment (simplify_out_expr env lhs) (simplify_expr env rhs)
    | Action_call f args -> Action_call f (List.map (simplify_expr env) args)
    | _ -> a //action mutable identifiers are not subject to substitution
let rec simplify_action (env:T.env_t) (a:action) : ML action =
  match a.v with
  | Atomic_action aa -> {a with v = Atomic_action (simplify_atomic_action env aa)}
  | Action_seq hd tl -> {a with v = Action_seq (simplify_atomic_action env hd) (simplify_action env tl) }
  | Action_ite hd then_ else_ -> {a with v = Action_ite (simplify_expr env hd) (simplify_action env then_) (simplify_action_opt env else_) }
  | Action_let i aa k -> {a with v = Action_let i (simplify_atomic_action env aa) (simplify_action env k) }
  | Action_act a -> { a with v = Action_act (simplify_action env a) }
and simplify_action_opt (env:T.env_t) (a:option action) : ML (option action) =
  match a with
  | None -> None
  | Some a -> Some (simplify_action env a)


let simplify_field_array (env:T.env_t) (f:field_array_t) : ML field_array_t =
  match f with
  | FieldScalar -> FieldScalar
  | FieldArrayQualified (e, b) -> FieldArrayQualified (simplify_expr env e, b)
  | FieldString sz -> FieldString (map_opt (simplify_expr env) sz)

let simplify_field (env:T.env_t) (f:field)
  : ML field
  = let sf = f.v in
    let ft = simplify_typ env sf.field_type in
    let fa = simplify_field_array env sf.field_array_opt in
    let fc = sf.field_constraint |> map_opt (simplify_expr env) in
    let fact =
      match sf.field_action with
      | None -> None
      | Some (a, b) -> Some (simplify_action env a, b)
    in
    let sf = { sf with field_type = ft;
                       field_array_opt = fa; 
                       field_constraint = fc;
                       field_action = fact } in
    { f with v = sf }

let rec simplify_out_fields (env:T.env_t) (flds:list out_field) : ML (list out_field) =
  List.map (fun fld -> match fld with
    | Out_field_named id t -> Out_field_named id (simplify_typ env t)
    | Out_field_anon flds is_union ->
      Out_field_anon (simplify_out_fields env flds) is_union) flds

let simplify_decl (env:T.env_t) (d:decl) : ML decl =
  match d.d_decl.v with
  | ModuleAbbrev _ _ -> d
  | Define i None c -> d
  | Define i (Some t) c -> decl_with_v d (Define i (Some (simplify_typ env t)) c)

  | TypeAbbrev t i ->
    let t' = simplify_typ env t in
    if Options.get_interpret() 
    then B.update_typ_abbrev (fst env) i t';
    decl_with_v d (TypeAbbrev t' i)

  | Enum t i cases ->
    let t = simplify_typ env t in
    decl_with_v d (Enum t i cases)

  | Record tdnames params wopt fields ->
    let params = List.map (fun (t, i, q) -> simplify_typ env t, i, q) params in
    let fields = List.map (simplify_field env) fields in
    let wopt = match wopt with | None -> None | Some w -> Some (simplify_expr env w) in
    decl_with_v d (Record tdnames params wopt fields)

  | CaseType tdnames params switch ->
    let params = List.map (fun (t, i, q) -> simplify_typ env t, i, q) params in 
    let hd, cases = switch in
    let hd = simplify_expr env hd in
    let cases = List.map (function Case e f -> Case (simplify_expr env e) (simplify_field env f)
                                 | DefaultCase f -> DefaultCase (simplify_field env f)) 
                         cases in
    decl_with_v d (CaseType tdnames params (hd, cases))

  | OutputType out_t ->
    decl_with_v d (OutputType ({out_t with out_typ_fields=simplify_out_fields env out_t.out_typ_fields}))

let simplify_prog benv senv (p:list decl) =
  List.map (simplify_decl (B.mk_env benv, senv)) p

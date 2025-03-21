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
    | Pointer t q -> {t with v=Pointer (simplify_typ env t) q}
    | Type_app s b gs ps ->
      let gs = List.map (simplify_expr env) gs in
      let ps = List.map (simplify_typ_param env) ps in
      let s = B.resolve_record_case_output_extern_type_name (fst env) s in
      let t = { t with v = Type_app s b gs ps } in
      B.unfold_typ_abbrev_only (fst env) t
    | Type_arrow ts t1 ->
      let ts = List.map (simplify_typ env) ts in
      let t1 = simplify_typ env t1 in
      { t with v = (mk_arrow ts t1).v }

and simplify_out_expr_node (env:T.env_t) (oe:with_meta_t out_expr')
  : ML (with_meta_t out_expr')
  = oe

and simplify_out_expr_meta (env:T.env_t) (mopt:option out_expr_meta_t)
  : ML (option out_expr_meta_t)
  = match mopt with
    | None -> None
    | Some ({ out_expr_base_t = bt;
              out_expr_t = t;
              out_expr_bit_width = n }) ->
      Some ({ out_expr_base_t = simplify_typ env bt;
              out_expr_t = simplify_typ env t;
              out_expr_bit_width = n })

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
    | Action_field_ptr_after sz write_to ->
      Action_field_ptr_after (simplify_expr env sz) (simplify_out_expr env write_to)
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

let simplify_probe_atomic_action (env:T.env_t) (a:probe_atomic_action)
  : ML probe_atomic_action
  = match a with
    | Probe_action_return e ->
      Probe_action_return (simplify_expr env e)
    | Probe_action_call f args ->
      Probe_action_call f (List.map (simplify_expr env) args)
    | Probe_action_read f ->
      Probe_action_read f
    | Probe_action_write f v ->
      Probe_action_write f (simplify_expr env v)
    | Probe_action_copy f v ->
      Probe_action_copy f (simplify_expr env v)
    | Probe_action_skip e ->
      Probe_action_skip (simplify_expr env e)
    | Probe_action_fail ->
      Probe_action_fail
    
let rec simplify_probe_action (env:T.env_t) (a:probe_action) : ML probe_action =
  match a.v with
  | Probe_action_var i -> a
  | Probe_action_simple f l -> 
    {a with v = Probe_action_simple f (simplify_expr env l) }
  | Probe_atomic_action aa ->
    {a with v = Probe_atomic_action (simplify_probe_atomic_action env aa)}
  | Probe_action_seq hd tl ->
    {a with v = Probe_action_seq (simplify_probe_action env hd) (simplify_probe_action env tl) }
  | Probe_action_let i aa k ->
    {a with v = Probe_action_let i (simplify_probe_atomic_action env aa) (simplify_probe_action env k) }
  | Probe_action_ite hd then_ else_ ->
    {a with v = Probe_action_ite (simplify_expr env hd) (simplify_probe_action env then_)
                                 (simplify_probe_action env else_) }
 
let simplify_field_array (env:T.env_t) (f:field_array_t) : ML field_array_t =
  match f with
  | FieldScalar -> FieldScalar
  | FieldArrayQualified (e, b) -> FieldArrayQualified (simplify_expr env e, b)
  | FieldString sz -> FieldString (map_opt (simplify_expr env) sz)
  | FieldConsumeAll -> FieldConsumeAll

let simplify_probe (env:T.env_t) (p:probe_call) : ML probe_call =
  match p with
  | { probe_dest; probe_block; probe_ptr_as_u64 } ->
    let probe_block = simplify_probe_action env probe_block in
    { probe_dest; probe_block; probe_ptr_as_u64 }

let simplify_atomic_field (env:T.env_t) (f:atomic_field)
  : ML atomic_field
  = let sf = f.v in
    let ft = simplify_typ env sf.field_type in
    let fa = simplify_field_array env sf.field_array_opt in
    let fc = sf.field_constraint |> map_opt (simplify_expr env) in
    let fp = sf.field_probe |> map_opt (simplify_probe env) in
    let fact =
      match sf.field_action with
      | None -> None
      | Some (a, b) -> Some (simplify_action env a, b)
    in
    let sf = { sf with field_type = ft;
                       field_array_opt = fa; 
                       field_constraint = fc;
                       field_action = fact;
                       field_probe = fp } in
    { f with v = sf }

let rec simplify_field (env:T.env_t) (f:field)
  : ML field
  = match f.v with
    | AtomicField af -> { f with v = AtomicField (simplify_atomic_field env af) }
    | RecordField fs i -> { f with v = RecordField (List.map (simplify_field env) fs) i }
    | SwitchCaseField swc i -> { f with v = SwitchCaseField (simplify_switch_case env swc) i }

and simplify_switch_case (env:T.env_t) (c:switch_case)
  : ML switch_case = 
  let (e, cases) = c in
  let e = simplify_expr env e in
  let cases =
    List.map 
      (function Case e f -> Case (simplify_expr env e) (simplify_field env f)
              | DefaultCase f -> DefaultCase (simplify_field env f))
      cases
  in
  e, cases
  
   
let rec simplify_out_fields (env:T.env_t) (flds:list out_field) : ML (list out_field) =
  List.map (fun fld -> match fld with
    | Out_field_named id t n -> Out_field_named id (simplify_typ env t) n
    | Out_field_anon flds is_union ->
      Out_field_anon (simplify_out_fields env flds) is_union) flds

let check_probe_size_range (e: expr) : ML unit =
  match e.v with
  | Constant (Int t n) ->
    if integer_type_leq t UInt32
    then ()
    else
      error
        (Printf.sprintf "entrypoint probe: computed sizeof(%s) == %d, exceeds unsigned 32-bit integer range"
          (print_expr e)
          n
        )
      e.range
  | App SizeOf _ -> error "check_probe_size_range: sizeof should have been eliminated already" e.range
  | _ -> ()

let simplify_attribute (env: T.env_t) (attr: attribute) : ML attribute =
  match attr with
  | Entrypoint (Some p) ->
    let e' = simplify_expr env p.probe_ep_length in
    check_probe_size_range e';
    Entrypoint (Some ({
      p with
        probe_ep_length = e';
    }))
  | _ -> attr

let simplify_typedef_names (env: T.env_t) (tdnames: typedef_names) : ML typedef_names =
  { tdnames with
      typedef_attributes = List.map (simplify_attribute env) tdnames.typedef_attributes;
  }

let simplify_params (env: T.env_t) (params: list param)
: ML (list param)
= List.map (fun (t, i, q) -> simplify_typ env t, i, q) params

let simplify_generic (env: T.env_t) (g: generic_param)
: ML generic_param
= let GenericProbeFunction p k i = g in
  let k = simplify_typ env k in
  GenericProbeFunction p k i

let simplify_decl (env:T.env_t) (d:decl) : ML decl =
  match d.d_decl.v with
  | ModuleAbbrev _ _ -> d
  | Define i None c -> d
  | Define i (Some t) c -> decl_with_v d (Define i (Some (simplify_typ env t)) c)

  | TypeAbbrev attrs t i gs ps ->
    let attrs = List.map (simplify_attribute env) attrs in
    let ps = simplify_params env ps in
    let t' = simplify_typ env t in
    B.update_typ_abbrev (fst env) i t';
    decl_with_v d (TypeAbbrev attrs t' i gs ps)

  | Enum t i cases ->
    let t = simplify_typ env t in
    decl_with_v d (Enum t i cases)

  | Record tdnames generics params wopt fields ->
    let generics = List.map (simplify_generic env) generics in
    let tdnames = simplify_typedef_names env tdnames in
    let params = simplify_params env params in
    let fields = List.map (simplify_field env) fields in
    let wopt = match wopt with | None -> None | Some w -> Some (simplify_expr env w) in
    decl_with_v d (Record tdnames generics params wopt fields)

  | CaseType tdnames generics params switch ->
    let generics = List.map (simplify_generic env) generics in
    let tdnames = simplify_typedef_names env tdnames in
    let params = List.map (fun (t, i, q) -> simplify_typ env t, i, q) params in 
    let switch = simplify_switch_case env switch in
    decl_with_v d (CaseType tdnames generics params switch)

  | ProbeFunction id ps b tn ->
    let ps = simplify_params env ps in
    let b = simplify_probe_action env b in
    decl_with_v d (ProbeFunction id ps b tn)
    
  | CoerceProbeFunctionStub id ps tn ->
    let ps = simplify_params env ps in
    decl_with_v d (CoerceProbeFunctionStub id ps tn)

  | Specialize qs t0 t1 ->
    decl_with_v d (Specialize qs t0 t1)

  | OutputType out_t ->
    decl_with_v d (OutputType ({out_t with out_typ_fields=simplify_out_fields env out_t.out_typ_fields}))

  | ExternType tdnames -> d

  | ExternFn f ret params pure ->
    let ret = simplify_typ env ret in
    let params = List.map (fun (t, i, q) -> simplify_typ env t, i, q) params in
    decl_with_v d (ExternFn f ret params pure)

  | ExternProbe _ _ -> d
  

let simplify_prog benv senv (p:list decl) =
  List.map (simplify_decl (B.mk_env benv, senv)) p

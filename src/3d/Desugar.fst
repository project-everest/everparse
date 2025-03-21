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
open FStar.List.Tot
open FStar.Mul
open Ast
open FStar.All
module H = Hashtable

(* This module implements a pass over the source AST, 
   implementing various simple desugarings

   * Desugar enums with newly defined idents and explicit constant
     assignments to enums where all the tags are previously defined
     constants.

   * Resolve module-qualified names, including the use of module 
     abbreviations

   * Set the kind (Spec/Output/Extern) in the type nodes

   * Finds variables in Static expressions and hoists them as assumptions
     and removes the Static
*)

let check_desugared_enum_cases (cases:list enum_case) : ML (list ident) =
    List.map
      (function
        | (i, None) -> i
        | (i, _) -> failwith "Enum should already have been desugared")
     cases

let desugar_enum_cases (ityp:integer_type) (cases:list enum_case) (export:bool)
  : ML (list enum_case & list decl) =
  let find_definition (i:ident) (d:decl) =
    match d.d_decl.v with
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
            | Some ({d_decl={v=Define _ _ (Int _ k)}}) -> k
            | _ -> error (Printf.sprintf "Enum identifier %s not found" (print_ident j)) j.range
            end
          | None -> next
        in
        let case = (i, None) in
        let d = mk_decl
                   (Define i None (Int ityp next))
                   i.range
                   ["Enum constant"]
                   export
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
  match d.d_decl.v with
  | Enum t i cases -> 
    if List.for_all (fun (_, jopt) -> None? jopt) cases
    then [d] //no enum value assignments; no desugaring to do
    else     //if we have any assignments at all, then we treat all the
             //tags as fresh constants and assign them values in sequence
             //with respect to the assigned values of preceding tags
         let cases, ds = desugar_enum_cases (typ_as_integer_type t) cases d.d_exported in
         let enum = decl_with_v d (Enum t i cases) in
         ds@[enum]
  | _ -> [d]

(* This code is currently not used
   It desugars an Enum to a record with a single refined field *)
// let eliminate_enum (d:decl) : ML decl =
//   match d.v with 
//   | Enum t i cases -> 
//     let names = {
//       typedef_name = { i with v = { i.v with name=Ast.reserved_prefix ^ Ast.reserved_prefix ^ i.v.name }};
//       typedef_abbrev = i;
//       typedef_ptr_abbrev = { i with v = {i.v with
//                                          name = Ast.reserved_prefix ^ Ast.reserved_prefix ^ "P" ^ i.v.name }};
//       typedef_attributes = [];
//     } in
//     let params = [] in
//     let where = None in
//     let field_ident = with_dummy_range (to_ident' (Ast.reserved_prefix ^ "enum_field")) in
//     let field_ident_expr = with_dummy_range (Identifier field_ident) in
//     let field_constraint = 
//       List.fold_right 
//         (fun (case, _) out ->
//           let eq = with_range (App Eq [field_ident_expr; with_range (Identifier case) case.range]) case.range in
//           with_dummy_range (App Or [eq; out]))
//         cases
//         (with_dummy_range (Constant (Bool false)))
//     in
//     let field = {
//        field_dependence = false;
//        field_ident = field_ident;
//        field_type = t;
//        field_array_opt = FieldScalar;
//        field_constraint = Some field_constraint;
//        field_number = None;
//        field_bitwidth = None;
//        field_action = None
//     } in
//     let d' = Record names params where [with_dummy_range field] in
//     {d with v = d'}
    
//   | _ -> d


(*
 * output_types and extern_types tables to set the kind in the Typ_app nodes
 *)

noeq
type qenv = {
  mname : string;
  module_abbrevs : H.t string string;
  output_types : H.t ident' unit;
  extern_types : H.t ident' unit;
  local_names : list string;
  generic_names : list string;
  global_env: GlobalEnv.global_env;
}

let push_module_abbrev (env:qenv) (i m:string) : ML unit =
  H.insert env.module_abbrevs i m

let push_output_type (env:qenv) (out_t:out_typ) : ML unit =
  H.insert env.output_types out_t.out_typ_names.typedef_name.v ();
  H.insert env.output_types out_t.out_typ_names.typedef_abbrev.v ()

let push_extern_type (env:qenv) (td:typedef_names) : ML unit =
  H.insert env.extern_types td.typedef_name.v ();
  H.insert env.extern_types td.typedef_abbrev.v ()

let push_name (env:qenv) (name:string) : qenv =
  { env with local_names = name::env.local_names }

let push_generic (env:qenv) (g:generic_param)
: ML qenv
= let GenericProbeFunction p _ _ = g in
  if List.mem p.v.name env.generic_names
  then error (Printf.sprintf "Generic name %s already in scope" p.v.name) p.range
  else { env with generic_names = p.v.name::env.generic_names }

let push_generics (env:qenv) (g:list generic_param) : ML qenv =
  List.fold_left push_generic env g


let prim_consts = [
  "unit"; "Bool"; "UINT8"; "UINT16"; "UINT32"; "UINT64";
  "UINT8BE"; "UINT16BE"; "UINT32BE"; "UINT64BE";
  "field_id"; "PUINT8"; "EVERPARSE_COPY_BUFFER_T";
  "all_bytes"; "all_zeros";
  "is_range_okay";
  "void" ]

let resolve_generic (env:qenv) (i:ident) : ML ident =
  if List.mem i.v.name env.generic_names
  then i
  else error (Printf.sprintf "Generic name %s not in scope" i.v.name) i.range

let resolve_ident (env:qenv) (i:ident) : ML ident =
  let resolve_to_current_module i =
    { i with v = { i.v with modul_name = Some env.mname } }
  in
  let maybe_resolve_as_ifdef (i:ident) 
    : ML ident
    = match env.global_env.ge_cfg with
      | None -> resolve_to_current_module i
      | Some (cfg, cfg_module_name) ->
        if List.mem i.v.name cfg.compile_time_flags.flags
        then { i with v = { i.v with modul_name = Some cfg_module_name } }
        else resolve_to_current_module i
  in
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
             | None -> maybe_resolve_as_ifdef i
             | Some m ->  //if already qualified, check if it is an abbreviation
               (match H.try_find env.module_abbrevs m with
                | None -> i
                | Some m -> { i with v = { i.v with modul_name = Some m } }))


let rec collect_ifdef_guards (env:qenv) (e:expr) 
  : ML unit
  = let check_resolved_to_ifdef i =
      match env.global_env.ge_cfg with
      | None -> false
      | Some (cfg, cfg_module_name) ->
        List.mem i.v.name cfg.compile_time_flags.flags
        && i.v.modul_name = Some cfg_module_name
    in
    match e.v with
    | This -> error "'this' is not allowed in the guard of an #if" e.range
    | Static _ -> failwith "static should have been eliminated already"
    | Constant _ -> ()
    | Identifier i ->
      if not (check_resolved_to_ifdef i)
      then error (Printf.sprintf "Identifier %s is not a compile-time macro but is used in a #if" i.v.name) e.range
    | App op args ->
      begin 
      match op with
      | And
      | Or
      | Not -> List.iter (collect_ifdef_guards env) args
      | _ -> error "Only boolean expressions over identifiers are supported in #if guards" e.range
      end

let rec resolve_expr' (env:qenv) (e:expr') r : ML expr' =
  match e with
  | Constant _ -> e
  | Identifier i -> Identifier (resolve_ident env i)
  | This -> e
  | Static e' ->
    let e' = resolve_expr env e' in
    collect_ifdef_guards env e';//mark any variables as top-level IfDef symbols
    e'.v
  
  | App op args -> 
    let args = List.map (resolve_expr env) args in
    App op args    

and resolve_expr (env:qenv) (e:expr) : ML expr = { e with v = resolve_expr' env e.v e.range }

let resolve_typ_param (env:qenv) (p:typ_param) : ML typ_param =
  match p with
  | Inl e -> resolve_expr env e |> Inl
  | _ -> p  //Currently not going inside output expressions, should we?


let kind_of_ident (env:qenv) (i:ident)
  : ML t_kind
  = let _or_ (b0 b1:bool) = b0 || b1 in
    if  Some? (H.try_find env.output_types i.v) `_or_`
        Some? (H.try_find env.global_env.ge_out_t i.v)
    then KindOutput
    else if
        Some? (H.try_find env.extern_types i.v) `_or_`
        Some? (H.try_find env.global_env.ge_extern_t i.v)    
    then KindExtern
    else KindSpec
    
let rec resolve_typ' (env:qenv) (t:typ') : ML typ' =
  match t with
  | Type_app hd _ gs args ->
    let hd = resolve_ident env hd in
    let gs = List.map (resolve_expr env) gs in
    //Set is_out argument to the Type_app appropriately
    let k = kind_of_ident env hd in
    Type_app hd k gs (List.map (resolve_typ_param env) args)
  | Pointer t q -> Pointer (resolve_typ env t) q
  | Type_arrow ts t -> (mk_arrow (List.map (resolve_typ env) ts) (resolve_typ env t)).v

and resolve_typ (env:qenv) (t:typ) : ML typ = { t with v = resolve_typ' env t.v }

let resolve_atomic_action (env:qenv) (ac:atomic_action) : ML atomic_action =
  match ac with
  | Action_return e -> Action_return (resolve_expr env e)
  | Action_abort
  | Action_field_pos_64
  | Action_field_pos_32
  | Action_field_ptr -> ac
  | Action_field_ptr_after e write_to -> Action_field_ptr_after (resolve_expr env e) write_to
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
  | Action_act a ->
    Action_act (resolve_action env a)

and resolve_action (env:qenv) (act:action) : ML action =
  { act with v = resolve_action' env act.v }

let resolve_probe_atomic_action (env:qenv) (ac:probe_atomic_action) : ML probe_atomic_action =
  match ac with
  | Probe_action_return e -> Probe_action_return (resolve_expr env e)
  | Probe_action_call f args ->
    Probe_action_call (resolve_ident env f) (List.map (resolve_expr env) args)
  | Probe_action_read f -> Probe_action_read (resolve_ident env f)
  | Probe_action_write f v -> Probe_action_write (resolve_ident env f) (resolve_expr env v)
  | Probe_action_copy f v -> Probe_action_copy (resolve_ident env f) (resolve_expr env v)
  | Probe_action_skip n -> Probe_action_skip (resolve_expr env n)
  | Probe_action_fail -> Probe_action_fail

let rec resolve_probe_action' (env:qenv) (act:probe_action') : ML probe_action' =
  match act with
  | Probe_atomic_action ac -> Probe_atomic_action (resolve_probe_atomic_action env ac)
  | Probe_action_var i -> Probe_action_var (resolve_expr env i)
  | Probe_action_simple f n ->
    Probe_action_simple (map_opt (resolve_ident env) f) (resolve_expr env n)
  | Probe_action_seq hd tl ->
    Probe_action_seq (resolve_probe_action env hd) (resolve_probe_action env tl)
  | Probe_action_let i a k ->
    Probe_action_let i (resolve_probe_atomic_action env a) (resolve_probe_action (push_name env i.v.name) k)
  | Probe_action_ite hd then_ else_ ->
    Probe_action_ite (resolve_expr env hd) (resolve_probe_action env then_) (resolve_probe_action env else_)
and resolve_probe_action (env:qenv) (act:probe_action) : ML probe_action =
  { act with v = resolve_probe_action' env act.v }

let resolve_param (env:qenv) (p:param) : ML (param & qenv) =
  let t, i, q = p in
  (resolve_typ env t, i, q),
  push_name env i.v.name

let resolve_params (env:qenv) (params:list param) : ML (list param & qenv) =
  List.fold_left (fun (params, env) p ->
    let p, env = resolve_param env p in
    params@[p], env) ([], env) params

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
  | FieldConsumeAll -> farr

let resolve_probe_field env = function
  | ProbeLength e -> ProbeLength (resolve_expr env e)
  | ProbeDest e -> ProbeDest (resolve_expr env e)

let resolve_probe_call env pc =
  let { probe_dest; probe_block; probe_ptr_as_u64 } = pc in
  {
    probe_dest = resolve_ident env probe_dest;
    probe_block = resolve_probe_action env probe_block;
    probe_ptr_as_u64 = map_opt (resolve_ident env) probe_ptr_as_u64;
  }

let rec resolve_field (env:qenv) (ff:field) : ML (field & qenv) =
  match ff.v with
  | AtomicField f -> let f, e = resolve_atomic_field env f in {ff with v = AtomicField f}, e
  | RecordField f i -> let fs, _ = resolve_fields env f in  {ff with v = RecordField fs i}, env //record fields are not in scope outside the record
  | SwitchCaseField f i -> let f = resolve_switch_case env f in {ff with v = SwitchCaseField f i}, env

and resolve_atomic_field (env:qenv) (f:atomic_field) : ML (atomic_field & qenv) =
  let resolve_atomic_field' (env:qenv) (sf:atomic_field') : ML atomic_field' =
    let is_non_scalar = not (FieldScalar? sf.field_array_opt) in
    if is_non_scalar && (Some? sf.field_constraint)
    then error (Printf.sprintf "Non-scalar field '%s' cannot be refined with constraints" sf.field_ident.v.name) f.range
    else if is_non_scalar && (Some? sf.field_bitwidth)
    then error (Printf.sprintf "Non-scalar field '%s' cannot have a bit width" sf.field_ident.v.name) f.range
    else (
        { sf with
          field_type = resolve_typ env sf.field_type;
          field_array_opt = resolve_field_array_t env sf.field_array_opt;
          field_constraint = map_opt (resolve_expr env) sf.field_constraint;
          field_bitwidth = map_opt (resolve_field_bitwidth_t env) sf.field_bitwidth;
          field_action = map_opt (fun (a, b) -> resolve_action env a, b) sf.field_action;
          field_probe = map_opt (resolve_probe_call env) sf.field_probe }
    )
  in
  let env = push_name env f.v.field_ident.v.name in
  { f with v = resolve_atomic_field' env f.v }, env

and resolve_fields (env:qenv) (flds:list field) : ML (list field & qenv) =
  List.fold_left (fun (flds, env) f ->
    let f, env = resolve_field env f in
    flds@[f], env) ([], env) flds

and resolve_switch_case (env:qenv) (sc:switch_case) : ML switch_case = //case fields do not escape their scope
  let resolve_case (env:qenv) (c:case) : ML case =
    match c with
    | Case e f -> Case (resolve_expr env e) (fst (resolve_field env f))
    | DefaultCase f -> DefaultCase (fst (resolve_field env f)) in

  let e, l = sc in
  resolve_expr env e, List.map (resolve_case env) l

let resolve_typedef_attribute (env: qenv) (a: attribute) : ML attribute =
  match a with
  | Entrypoint (Some p) ->
    Entrypoint (Some ({
      probe_ep_fn = resolve_ident env p.probe_ep_fn;
      probe_ep_length = resolve_expr env p.probe_ep_length;
    }))
  | _ -> a

let resolve_typedef_names (env:qenv) (td_names:typedef_names) : ML typedef_names =
  {
    typedef_name = resolve_ident env td_names.typedef_name;
    typedef_abbrev = resolve_ident env td_names.typedef_abbrev;
    typedef_ptr_abbrev = map_opt (resolve_ident env) td_names.typedef_ptr_abbrev;
    typedef_attributes = List.map (resolve_typedef_attribute env) td_names.typedef_attributes;
  }

let resolve_enum_case (env:qenv) (ec:enum_case) : ML enum_case =
  match ec with
  | i, None -> resolve_ident env i, None
  | _ -> error "Unexpected enum_case in resolve_enum_case" (fst ec).range

let rec resolve_out_field (env:qenv) (fld:out_field) : ML out_field =
  match fld with
  | Out_field_named i t n -> Out_field_named i (resolve_typ env t) n
  | Out_field_anon l u -> Out_field_anon (resolve_out_fields env l) u

and resolve_out_fields (env:qenv) (flds:list out_field) : ML (list out_field) =
  List.map (resolve_out_field env) flds

let resolve_out_type (env:qenv) (out_t:out_typ) : ML out_typ =
  { out_t with
    out_typ_names = resolve_typedef_names env out_t.out_typ_names;
    out_typ_fields = List.map (resolve_out_field env) out_t.out_typ_fields }

let resolve_probe_function_type env = function
    | SimpleProbeFunction id -> SimpleProbeFunction (resolve_ident env id)
    | CoerceProbeFunction (x, y) -> CoerceProbeFunction (resolve_ident env x, resolve_ident env y)
  
let resolve_decl' (env:qenv) (d:decl') : ML decl' =
  match d with
  | ModuleAbbrev i m -> push_module_abbrev env i.v.name m.v.name; d
  | Define i topt c ->
    Define (resolve_ident env i) (map_opt (resolve_typ env) topt) c
  | TypeAbbrev attrs t i gs ps ->
    let attrs = List.map (resolve_typedef_attribute env) attrs in
    let env = push_generics env gs in    
    let params, env = resolve_params env ps in
    TypeAbbrev attrs (resolve_typ env t) (resolve_ident env i) gs ps
  | Enum t i ecs ->
    Enum (resolve_typ env t) (resolve_ident env i) (List.map (resolve_enum_case env) ecs)
  | Record td_names generics params where flds ->
    let td_names = resolve_typedef_names env td_names in
    let env = push_generics env generics in
    let params, env = resolve_params env params in
    let where = map_opt (resolve_expr env) where in
    let flds, _ = resolve_fields env flds in
    Record td_names generics params where flds
  | CaseType td_names generics params sc ->
    let td_names = resolve_typedef_names env td_names in
    let env = push_generics env generics in
    let params, env = resolve_params env params in
    let sc = resolve_switch_case env sc in
    CaseType td_names generics params sc
  | ProbeFunction f params act tn ->
    let tn = resolve_probe_function_type env tn in
    let params, env = resolve_params env params in
    let act = resolve_probe_action env act in
    ProbeFunction f params act tn
  | CoerceProbeFunctionStub id params tn ->
    let tn = resolve_probe_function_type env tn in
    let params, env = resolve_params env params in
    CoerceProbeFunctionStub id params tn
  | Specialize qs t0 t1 ->
    Specialize qs (resolve_ident env t0) (resolve_ident env t1)
  | OutputType out_t ->
    let out_t = resolve_out_type env out_t in
    push_output_type env out_t;
    OutputType out_t
  | ExternType td_names ->
    let td_names = resolve_typedef_names env td_names in
    push_extern_type env td_names;
    ExternType td_names
  | ExternFn id ret params pure ->
    let id = resolve_ident env id in
    let ret = resolve_typ env ret in
    let params, _ = resolve_params env params in
    ExternFn id ret params pure
  | ExternProbe id q ->
    let id = resolve_ident env id in
    ExternProbe id q

let resolve_decl (env:qenv) (d:decl) : ML decl = decl_with_v d (resolve_decl' env d.d_decl.v)

let desugar (genv:GlobalEnv.global_env) (mname:string) (p:prog) : ML prog =
  let decls, refinement = p in
  let decls = List.collect desugar_one_enum decls in
  let env = {
    mname=mname;
    module_abbrevs=H.create 10;
    output_types=H.create 10;
    extern_types=H.create 10;
    local_names=[];
    generic_names=[];
    global_env=genv
  } in
  H.insert env.extern_types (Ast.to_ident' "void") ();
  let decls = List.map (resolve_decl env) decls in
  decls,
  (match refinement with
   | None -> None
   | Some tr ->
     Some ({ tr with
             type_map =
               tr.type_map
               |> List.map (fun (i, jopt) -> match jopt with
                                         | None -> i, Some (resolve_ident env i)
                                         | Some j -> i, Some (resolve_ident env j))}))

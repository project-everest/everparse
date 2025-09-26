(*
   Copyright 2025 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain as copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module GeneralizeProbes
(*
  This module implements a pass over the source AST, run after the name resolution pass
  of Desugar.

  It generalizes types that contain probes, allowing those probes to be
  instantiated in different ways, preparing for a subsequent specialization of
  probed types to 32- or 64-bit layouts

*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
module H = Hashtable
module B = Binding
open GlobalEnv

let generalized_signature = list (ident & typ)

let print_probe_qualifier = function
  | PQWithOffsets -> "WithOffsets"
  | PQRead i -> Printf.sprintf "Read %s" (print_integer_type i)
  | PQWrite i -> Printf.sprintf "Write %s" (print_integer_type i)
  | PQInit -> "Init"

noeq
type env = {
  benv:Binding.env;
  needs_probe:list ident';
  should_generalize:H.t ident' (option generalized_signature)
}

let simple_probe_function_for_type (type_name:ident) : ident =
  let name = reserved_prefix ^ "probe_" ^ type_name.v.name in
  let id = { type_name with v = { type_name.v with name } } in
  id

let simple_probe_name_for_type (e:env) (type_name:ident)
: option ident
= if List.Tot.mem type_name.v e.needs_probe
  then Some (simple_probe_function_for_type type_name)
  else None

let find_probe_fn (e:B.env) (q:probe_qualifier) r
: ML ident
= match GlobalEnv.extern_probe_fn_qual (B.global_env_of_env e) r q with
  | None ->
    error (Printf.sprintf "Cannot find probe function for %s" (print_probe_qualifier q))
          r
  | Some id ->
    id
  
let find_extern_coercion (e:B.env) (t0:typ) (t1:typ) r
: ML ident
= match GlobalEnv.resolve_extern_coercion (B.global_env_of_env e) r t0 t1 with
  | None ->
    error (Printf.sprintf "Cannot find coercion for %s to %s" (print_typ t0) (print_typ t1))
          r
  | Some id ->
    id

let should_generate_probe (e:env) (n:typedef_names) = List.mem n.typedef_abbrev.v e.needs_probe
let should_generalize_ident (e:env) (id:ident) =
  Some? <| H.try_find e.should_generalize id.v
let should_generalize (e:env) (n:typedef_names) = should_generalize_ident e n.typedef_abbrev
let gen_signature (e:env) (id:ident) : ML generalized_signature = 
  match H.try_find e.should_generalize id.v with
  | None -> failwith (Printf.sprintf "No generalization signature for this type <None>: %s" (print_ident id))
  | Some None -> failwith (Printf.sprintf "No generalization signature for this type <Some None>: %s" (print_ident id))
  | Some (Some sig) -> sig

let mark_for_probe (e:env) (id:ident) 
: ML (env & bool) 
= if List.mem id.v e.needs_probe
  then e, false
  else { e with needs_probe = id.v :: e.needs_probe }, true

let mark_for_generalize (e:env) (id:ident)
: ML (env & bool)
= if should_generalize_ident e id
  then e, false
  else (
    H.insert e.should_generalize id.v None;
    e, true
  )

let clear_generalization (e:env) (n:typedef_names)
: ML unit
= H.remove e.should_generalize n.typedef_abbrev.v

let set_generalization_signature (e:env) (id:ident) (sig:generalized_signature)
: ML env
= if should_generalize_ident e id
  then (
    H.remove e.should_generalize id.v;
    H.insert e.should_generalize id.v (Some sig);
    e
  )
  else (
    error
     (Printf.sprintf 
      "Cannot set generalization signature for a type %s that is not marked for generalization"
      (print_ident id))
     id.range
  )

let rec head_type (e:env) (t:typ) : ML (ident & list typ_param) =
  match (Binding.unfold_typ_abbrev_only e.benv t).v with
  | Type_app hd _ _ params -> hd, params
  | Pointer t _ -> head_type e t
  | _ -> failwith "head_type: unexpected arrow type"

let has_simple_probe (fp:probe_call) : option expr =
  match fp with
  | { probe_block={ v = Probe_atomic_action (Probe_action_copy _ len) }} -> Some len
  | _ -> None

let atomic_field_has_simple_probe_aux (e:env) head_type (f:atomic_field)
: ML (bool & option ident)
= match f.v.field_probe with
  | Some fp -> (
    match has_simple_probe fp with
    | Some l -> true, Some head_type
    | _ ->
      Options.debug_print_string <|
        Printf.sprintf "Expected a simple probe, got %s\n"
          (print_probe_call fp);
      false, None
  )
  | _ -> false, None

let atomic_field_has_simple_probe (e:env) head_type (f:atomic_field)
: ML bool
= let b, _ = atomic_field_has_simple_probe_aux e head_type f in b

let fold_left_changed (#a #b:Type) (f: a -> b -> ML (a & bool)) (x:a) (l:list b) 
: ML (a & bool)
= List.fold_left (fun (a, changed) b -> let a', changed' = f a b in a', changed || changed') (x, false) l

let rec needs_probe_field (maybe_gen:bool) (enclosing_type:typedef_names) (e:env) (f:field)
: ML (env & bool)
= let maybe_generalize e t = if maybe_gen then mark_for_generalize e t.typedef_abbrev else e, false in
  match f.v with
  | AtomicField f ->
    let head_type, _ = head_type e f.v.field_type in
    let has_simple_probe = atomic_field_has_simple_probe e head_type f in
    if has_simple_probe
    then (
      let e, changed = mark_for_probe e head_type  in
      let e, changed' = maybe_generalize e enclosing_type in
      e, changed || changed'
    )
    else (
      // match field_type_ident with
      // | Some x ->
      //   error 
      //     (Printf.sprintf 
      //       "Expected a probe with sizeof(%s) but found a probe with sizeof(%s)"
      //       (print_ident head_type)
      //       (print_ident x))
      //     f.range
      // | None -> 
      let e, changed = 
        if should_generate_probe e enclosing_type
        then mark_for_probe e head_type // struct A { B b; } should probe B if A is probed
        else e, false
      in
      if should_generalize_ident e head_type 
      then let e, changed' = maybe_generalize e enclosing_type in // struct A { B <...> b; } should generalize A if B is generalized
            e, changed || changed'
      else e, changed
    )
  | RecordField r _ ->
    fold_left_changed (needs_probe_field maybe_gen enclosing_type) e r
  | SwitchCaseField sw _ ->
    fold_left_changed (needs_probe_case maybe_gen enclosing_type) e (snd sw)

and needs_probe_case (maybe_generalize:bool) (enclosing_type:typedef_names) (e:env) (c:case)
: ML (env & bool)
= match c with
  | Case _ f -> needs_probe_field maybe_generalize enclosing_type e f
  | DefaultCase f -> needs_probe_field maybe_generalize enclosing_type e f

let needs_probe_decl (e:env) (d:decl) 
: ML (env & bool)
= let maybe_generalize = not (is_entrypoint d) in
  let should_descend n : ML bool =
    should_generalize_ident e n.typedef_abbrev `_or_`
    should_generate_probe e n
  in
  match d.d_decl.v with
  | Record names _ _ _ fields ->
    if should_descend names
    then fold_left_changed (needs_probe_field maybe_generalize names) e fields
    else e, false
  | CaseType names _ _ sw ->
    if should_descend names
    then fold_left_changed (needs_probe_case maybe_generalize names) e (snd sw)
    else e, false
  | Specialize _ t _ -> (
    mark_for_generalize e t
  )
  | _ -> e, false

let needs_probe_decls (e:env) (ds:list decl)
: ML (env & bool)
= let any_change : ref bool = alloc false in
  let rec aux (e:env) (ds:list decl) : ML (env & bool) = 
    let e, changed = fold_left_changed needs_probe_decl e ds in
    if changed 
    then (
      any_change := true;
      aux e ds
    )
    else (e, !any_change)
  in
  aux e ds

let should_retain_param_for_probe (e:B.env) (p:param)
: bool
= let t, _, q = p in
  not (eq_typ t tcopybuffer || q = Mutable)
  

let rec generic_instantiations_for_type (e:B.env) (tt:typ)
: ML (list expr & typ)
= match tt.v with
  | Pointer t _ -> generic_instantiations_for_type e t
  | Type_app hd _ _ args ->
    let _, params = B.params_of_decl (fst <| B.lookup_type_decl e hd) in
    let args, params =
      List.map2
        (fun a p -> 
          match a with
          | Inr _ -> []
          | Inl x ->
            if should_retain_param_for_probe e p
            then [x,p]
            else []) args params
      |> List.flatten
      |> List.split
    in
    args, mk_arrow_ps params probe_m_t
  | _ -> failwith "Impossible: field type is an arrow"

let simple_probe_for (e:env) (tid:ident) params
: ML decl
= let simple_probe_name = simple_probe_function_for_type tid in
  let probe_size =
    with_range (
        App SizeOf [with_range (Identifier tid) tid.range]
      ) tid.range
  in
  let probe_and_copy_n = find_probe_fn e.benv PQWithOffsets tid.range in
  let simple_probe =
      with_range
      (Probe_atomic_action (
        Probe_action_copy probe_and_copy_n probe_size
      ))
      tid.range
  in
  let params = List.Tot.filter (should_retain_param_for_probe e.benv) params in
  let d' = 
    mk_decl         
    //  (ProbeFunction simple_probe_name params simple_probe 
    //     (SimpleProbeFunction names.typedef_abbrev))
      (CoerceProbeFunctionStub 
        (Ast.name32 simple_probe_name)
        params
        (CoerceProbeFunctionPlaceholder tid))
      dummy_range
      []
      false
  in
  d'
  
let generate_probe_function_stubs_for_one_decl (e:env) (seen_probe_primitive:bool) (d:decl)
: ML (list decl)
= let simple_probe name params = simple_probe_for e name params in
  match d.d_decl.v with
  | Record names gs params w fields -> (
    if not <| should_generate_probe e names
    then [d]
    else (
      let d' = simple_probe names.typedef_abbrev params in
      [d;d']
    )
  )
  | CaseType names gs params sw -> (
    if not <| should_generate_probe e names
    then [d]
    else (
      let d' = simple_probe names.typedef_abbrev params in
      [d;d']
    )
  )
  | TypeAbbrev _attrs ty name gs params -> (
    if not <| List.mem name.v e.needs_probe
    then [d]
    else (
      let d' = simple_probe name params in
      [d;d']
    )
  )
  | _ -> [d]

let generate_primitive_probe_function_stubs (e:env) (ids:list ident')
: ML (list decl)
= let generate_probe_for (id:ident')
  : ML (list decl)
  = let id = with_dummy_range id in
    let ty = with_dummy_range <| Type_app id KindSpec [] [] in
    if Binding.typ_is_integral e.benv ty
    then [simple_probe_for e id []]
    else []
  in
  List.collect generate_probe_for ids

let generate_probe_function_stubs (e:env) (ds:list decl)
: ML (list decl)
= let aux seen_probe_primitive (d:decl) 
  : ML (list decl & bool)
  = match d.d_decl.v with
    | ExternProbe _ PQWithOffsets ->
      [d], true
    | _ ->
      generate_probe_function_stubs_for_one_decl e seen_probe_primitive d, seen_probe_primitive
  in
  let ds, _ =
    List.fold_left
    (fun (ds, seen_probe_primitive) d ->
      let ds', seen_probe_primitive = aux seen_probe_primitive d in
      ds'::ds, seen_probe_primitive)
    ([], false) ds
  in
  List.rev ds |> List.flatten
  


let generalized_name (e:env) (head_name:ident) : ident = head_name

let generalized_record_name (e:env) (n:typedef_names)
: ML typedef_names
= let name = generalized_name e n.typedef_name in
  let abbrev = generalized_name e n.typedef_abbrev in
  { typedef_name = name;
    typedef_abbrev = abbrev;
    typedef_ptr_abbrev = None;
    typedef_attributes = List.filter Aligned? n.typedef_attributes }

let generalize_atomic_field (e:env) (path_prefix:string) (af:atomic_field)
: ML (atomic_field & list generic_param & generalized_signature)
= let head_type, params = head_type e af.v.field_type in
  if not <| should_generalize_ident e head_type
  then af, [], []
  else (
    let sig = gen_signature e head_type in
    let gen_name = generalized_name e head_type in
    let generic_name i = 
        with_range (
          to_ident' <|
          Printf.sprintf "%sprobe_%s_%s_%d"
            reserved_prefix
            path_prefix
            head_type.v.name
            i
        ) af.range
    in
    let generic_params = List.mapi (fun i t -> generic_name i, t) sig in
    let generic_insts = List.map (fun (i, _) -> with_range (Identifier i) af.range) generic_params in
    let rec field_type ft : ML typ =
      match ft.v with
      | Type_app id k [] args ->
        { ft with v = Type_app gen_name k generic_insts args }
      | Pointer t pq ->
        { ft with v = Pointer (field_type t) pq }
      | _ -> failwith "field_type: already partially generalized!"
    in
    let af = { af with v = { af.v with field_type = field_type af.v.field_type } } in
    af,
    List.map (fun (i,(h,t)) -> GenericProbeFunction i t h) generic_params,
    sig
  )

let rec generalize_probe_field (e:env) (path_prefix:string) (f:field) 
: ML (field & list generic_param & generalized_signature)
= match f.v with
  | AtomicField af -> (
    let head_type, params = head_type e af.v.field_type in
    let params = List.collect (function Inl t -> [t] | _ -> []) params in
    let af, gs0, sig0 = generalize_atomic_field e path_prefix af in
    let f = { f with v = AtomicField af } in
    if not <| atomic_field_has_simple_probe e head_type af
    then f, gs0, sig0
    else (
      match af.v.field_probe with
      | None -> failwith "Impossible"
      | Some probe_call ->
        let generic_name = 
          with_range (
            to_ident' <|
            reserved_prefix ^ "probe_" ^ path_prefix ^ print_ident af.v.field_ident
          ) f.range
        in
        let probe_inst, probe_sig = generic_instantiations_for_type e.benv af.v.field_type in
        let probe =
          match probe_inst with
          | [] -> with_range (Identifier generic_name) f.range
          | _ -> with_range (App (ProbeFunctionName generic_name) probe_inst) f.range
        in
        let probe = with_range (Probe_action_var probe) f.range in
        let probe_call = { probe_call with probe_block = probe } in
        let af = { af with v = { af.v with field_probe = Some probe_call } } in
        let f = { f with v = AtomicField af } in
        f,
        gs0@[GenericProbeFunction generic_name probe_sig head_type],
        sig0@[head_type, probe_sig]
    )
  )
  | RecordField r i ->
    let path_prefix = path_prefix ^ print_ident i in
    let r, gs, insts = generalize_probe_fields e path_prefix r in
    { f with v = RecordField r i }, gs, insts
  | SwitchCaseField sw i ->
    let path_prefix = path_prefix ^ print_ident i in
    let cs, gs, insts = generalize_probe_cases e path_prefix (snd sw) in
    { f with v = SwitchCaseField (fst sw, cs) i }, gs, insts
  
and generalize_probe_case (e:env) (path_prefix:string) (c:case)
: ML (case & list generic_param & generalized_signature)
= match c with
  | Case ex f ->
    let f, gs, insts = generalize_probe_field e path_prefix f in
    Case ex f, gs, insts
  | DefaultCase f ->
    let f, gs, insts = generalize_probe_field e path_prefix f in
    DefaultCase f, gs, insts

and generalize_probe_fields (e:env) (path_prefix:string) (fs:list field) 
: ML (list field & list generic_param & generalized_signature)
= List.fold_right 
    (fun f (fs, gs, is) -> 
       let f, gs', is' = generalize_probe_field e path_prefix f in
       f::fs, gs'@gs, is'@is)
    fs ([], [], [])

and generalize_probe_cases (e:env) (path_prefix:string) (cs:list case)
: ML (list case & list generic_param & generalized_signature)
= List.fold_right 
    (fun f (fs, gs, is) -> 
       let f, gs', is' = generalize_probe_case e path_prefix f in
       f::fs, gs'@gs, is'@is)
    cs ([], [], [])

let default_instantiation_subst
      (e:env)
      (r:range)
      (enclosing_type:typedef_names)
      (gs:list generic_param)
      (sig:generalized_signature)
: ML (list decl & subst)
= match GlobalEnv.extern_probe_fn_qual (B.global_env_of_env e.benv) r PQWithOffsets with
  | None ->
    error (Printf.sprintf "No extern probe function found for %s" (print_ident enclosing_type.typedef_abbrev))
          r
  | Some probe_and_copy_n ->
    let default_instantiation_body = 
      with_range (Probe_action_copy_init_sz probe_and_copy_n) r
    in
    let default_name_for param_name type_name =
      let name =
        Printf.sprintf "%s_%s_%s" 
          enclosing_type.typedef_abbrev.v.name
          param_name.v.name
          type_name.v.name in
      { param_name with v = { param_name.v with name } }
    in
    let formals_of_type (t:typ) : ML (list param) =
      match t.v with
      | Type_arrow args _ ->
        List.mapi (fun i t -> 
          let name = Printf.sprintf "%s_arg%d" reserved_prefix i in
          t, mk_ident name, Immutable) args
      | _ -> []
    in
    let default_instatiation_for (g:generic_param)
    : ML (decl & (ident & expr)) 
    = let GenericProbeFunction param_name typ type_name = g in
      let name = default_name_for param_name type_name in
      let params = formals_of_type typ in
      let decl = 
        mk_decl
          (ProbeFunction
            name
            params
            default_instantiation_body (SimpleProbeFunction type_name))
          dummy_range
          []
          false
      in
      decl, (param_name, with_range (Identifier name) r)
    in
    let decls, subst =
      List.map (fun g -> default_instatiation_for g) gs
      |> List.unzip
    in
    Options.debug_print_string <|
      (Printf.sprintf
        "Generated substitution: {%s}\n"
          (String.concat "; "
            (List.map (fun (i, e) -> Printf.sprintf "[%s -> %s]" (print_ident i) (print_expr e)) subst)));
    decls, mk_subst subst

let do_generalization (e:env) (d:decl)
: ML (list decl)
= let generalize_type names gs (params:list param) sig : ML _ =
    if not <| should_generalize e names
    then (
      error 
        (Printf.sprintf "Type %s should not be generalized" (print_ident names.typedef_abbrev))
        d.d_decl.range
    );
    let _ = set_generalization_signature e names.typedef_abbrev sig in
    let gen_name = generalized_record_name e names in
    let gen_name = { 
        gen_name with 
        typedef_attributes = gen_name.typedef_attributes
    } in
    gen_name
  in
  let id_of_decl d =
    match idents_of_decl d with
    | [i] -> i
    | _::j::_ -> j
  in
  Options.debug_print_string
    (Printf.sprintf "Generalize_probe_decls for %s\n"
      (print_ident <| id_of_decl d));
  match d.d_decl.v with
  | Record names gs params w fields -> (
    let fields, gs', sig = generalize_probe_fields e "" fields in
    match gs' with
    | [] -> (
      [d]
    )
    | _ -> (
      Options.debug_print_string
        (Printf.sprintf "**************************For type %s\nInstantiations with signature %s for fields: %s\n"
              (print_ident names.typedef_abbrev)
              (print_generics gs')
              (String.concat "; " <| List.map print_field fields));
      if not <| should_generalize e names
      then (
        let ds, s = default_instantiation_subst e d.d_decl.range names gs' sig in
        let fields = List.map (subst_field s) fields in
        let d = { d with 
                d_decl = { d.d_decl with 
                v=Record names gs params w fields }} in
        Options.debug_print_string
          (Printf.sprintf
            "<After substitution>:\n%s\n</After substitution>"
            (print_decl d));
        ds@[ d ]
      )
      else (
        let gen_name = generalize_type names gs params sig in
        let generalized_record =
          { d with 
            d_decl = { d.d_decl with 
            v=Record gen_name (gs'@gs) params w fields }}
        in
        [generalized_record]
      )
    )
  )
  | CaseType names gs params (v, cases) -> (
    let cases, gs', sig = generalize_probe_cases e "" cases in
    match gs' with
    | [] -> (
      [d]
    )
    | _ -> (
      Options.debug_print_string
        (Printf.sprintf "**************************For type %s\nInstantiations with signature %s for fields: %s\n"
              (print_ident names.typedef_abbrev)
              (print_generics gs')
              (String.concat "; " <| List.map print_case cases));
      if not <| should_generalize e names
      then (
        let ds, s = default_instantiation_subst e d.d_decl.range names gs' sig in
        let cases' = List.map (subst_case s) cases in
        let d = { d with 
            d_decl = { d.d_decl with 
            v=CaseType names gs params (v, cases') }} in
        Options.debug_print_string
          (Printf.sprintf
            "<After substitution>:\n%s\n</After substitution>"
            (print_decl d));
        ds@[ d ]
      )
      else (
        let gen_name = generalize_type names gs params sig in
        let generalized_c =
          { d with 
            d_decl = { d.d_decl with 
            v=CaseType gen_name (gs'@gs) params (v, cases) }}
        in
        [generalized_c]
      )
    )
  )
  | _ -> (
    [d]
  )

let generalize_probe_decls (e:GlobalEnv.global_env) (ds:list decl)
: ML (list decl)
= let e = { benv = Binding.mk_env e; needs_probe = []; should_generalize = H.create 10 } in
  let e, any_change = needs_probe_decls e ds in
  let print_ident (i:ident') = i.name in
  let _ = 
    List.iter
      (fun d ->
        match d.d_decl.v with
        | Specialize _ t _ ->
          if None? (H.try_find e.should_generalize t.v)
          then error (Printf.sprintf "Type %s was marked for specialization, but nothing was found to be specialized"        
                              (print_ident t.v))
                      d.d_decl.range
        | _ -> ())
        ds
  in
  Options.debug_print_string
    (Printf.sprintf "Probes needed for: %s\nShould generalize: %s\n" 
      (String.concat ", " (List.map print_ident e.needs_probe))
      (String.concat ", " (H.fold (fun k _ out -> print_ident k::out) e.should_generalize [])));
  if not any_change then ds
  else (
    let ds = generate_probe_function_stubs e ds in
    Options.debug_print_string "=============After generate probe functions=============\n";
    Options.debug_print_string (print_decls ds);
    Options.debug_print_string "\n";
    List.collect (do_generalization e) ds
  )
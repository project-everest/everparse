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

let generalized_signature = list ident

noeq
type env = {
  benv:Binding.env;
  needs_probe:list ident';
  should_generalize:H.t ident' (option (list ident))
}

let simple_probe_function_for_type (type_name:ident) : ML ident =
  let name = reserved_prefix ^ "probe_" ^ type_name.v.name in
  let id = { type_name with v = { type_name.v with name } } in
  id

let simple_probe_name_for_type (e:env) (type_name:ident)
: ML (option ident)
= if List.mem type_name.v e.needs_probe
  then Some (simple_probe_function_for_type type_name)
  else None

let should_generate_probe (e:env) (n:typedef_names) = List.mem n.typedef_abbrev.v e.needs_probe
let should_generalize_ident (e:env) (id:ident) =
  Some? <| H.try_find e.should_generalize id.v
let should_generalize (e:env) (n:typedef_names) = should_generalize_ident e n.typedef_abbrev
let gen_signature (e:env) (id:ident) : ML generalized_signature = 
  match H.try_find e.should_generalize id.v with
  | None -> failwith "No generalization signature for this type"
  | Some None -> failwith "No generalization signature for this type"
  | Some (Some sig) -> sig

let mark_for_probe (e:env) (id:ident) 
: ML env 
= { e with needs_probe = id.v :: e.needs_probe }

let mark_for_generalize (e:env) (id:ident)
: ML env
= if should_generalize_ident e id
  then e
  else (
    H.insert e.should_generalize id.v None;
    e
  )

let set_generalization_signature (e:env) (id:ident) (sig:generalized_signature)
: ML env
= if should_generalize_ident e id
  then (
    FStar.IO.print_string
      (Printf.sprintf "Setting generalization signature for %s to %s\n"
        (print_ident id)
        (String.concat ", " (List.map print_ident sig)));
    H.remove e.should_generalize id.v;
    H.insert e.should_generalize id.v (Some sig);
    e
  )
  else (
    failwith
     (Printf.sprintf 
      "Cannot set generalization signature for a type %s that is not marked for generalization"
      (print_ident id))
  )

let rec head_type (e:env) (t:typ) : ML ident =
  match (Binding.unfold_typ_abbrev_only e.benv t).v with
  | Type_app hd _ _ _ -> hd
  | Pointer t _ -> head_type e t
  | _ -> failwith 
          (Printf.sprintf "head_type: not a type application; got %s" (print_typ t))

let atomic_field_has_simple_probe (e:env) (f:atomic_field)
: ML bool
= match f.v.field_probe with
  | Some fp -> (
    FStar.IO.print_string
      (Printf.sprintf "Field %s has a probe %s\n"
         (print_ident f.v.field_ident)
         (print_probe_call fp)
      );
    match fp with 
    | { probe_block = { v = Probe_action_simple _ l } } -> (
        match l.v with
        | App (Cast _ _) [{ v = App SizeOf _ }]
        | App SizeOf [_] -> true
        | _ -> 
          FStar.IO.print_string
            (Printf.sprintf "But not a sizeof probe\n");
          false
      )
    | _ -> 
      FStar.IO.print_string
        (Printf.sprintf "But not a simple probe\n");
      false
  )
  | _ -> false

let rec needs_probe_field (enclosing_type:ident) (e:env) (f:field)
: ML env
= match f.v with
  | AtomicField f -> 
    if atomic_field_has_simple_probe e f
    then (let e = mark_for_probe e (head_type e f.v.field_type) in
          mark_for_generalize e enclosing_type)
    else (
      let ht = head_type e f.v.field_type in
      if should_generalize_ident e ht
      then mark_for_generalize e enclosing_type
      else e
    )
  | RecordField r _ -> List.fold_left (needs_probe_field enclosing_type) e r
  | SwitchCaseField sw _ -> List.fold_left (needs_probe_case enclosing_type) e (snd sw)

and needs_probe_case (enclosing_type:ident) (e:env) (c:case)
: ML env
= match c with
  | Case _ f -> needs_probe_field enclosing_type e f
  | DefaultCase f -> needs_probe_field enclosing_type e f

let need_probe_decl (e:env) (d:decl) 
: ML env
= match d.d_decl.v with
  | Record names _ _ _ fields ->
    List.fold_left (needs_probe_field names.typedef_abbrev) e fields
  | CaseType names _ _ sw ->
    if is_entrypoint d
    then e
    else List.fold_left (needs_probe_case names.typedef_abbrev) e (snd sw)
  | _ -> e

let need_probe_decls (e:env) (ds:list decl) = List.fold_left need_probe_decl e ds


let generate_probe_functions (e:env) (d:decl)
: ML (list decl)
= match d.d_decl.v with
  | Record names gs params w fields -> (
    if not <| should_generate_probe e names
    then [d]
    else (
      match simple_probe_name_for_type e names.typedef_abbrev with
      | None -> failwith "Impossible"
      | Some simple_probe_name ->
        let probe_size =
          with_range (
            App SizeOf [with_range (Identifier names.typedef_abbrev) names.typedef_name.range]
          ) d.d_decl.range
        in
        let simple_probe =
          with_range (
            Probe_action_simple None probe_size
          ) d.d_decl.range
        in
        let d' = 
          mk_decl 
            (ProbeFunction simple_probe_name [] simple_probe 
              (SimpleProbeFunction names.typedef_abbrev))
            dummy_range
            []
            false
        in
        [d;d']
    )
  )
  | CaseType names gs params sw -> (
    if should_generalize e names
    then failwith "Cannot automatically generate a probe function for a case type"
    else [d]
  )
  | _ -> [d]

let generalized_name (e:env) (head_name:ident) : ident = head_name
  // let gen = reserved_prefix ^ "generalized_" ^ head_name.v.name in
  // {head_name with v = { head_name.v with name = gen }}

let starts_with (long:string) (short:string) 
: option string
= let long_len = String.length long in
  let short_len = String.length short in
  if long_len < short_len
  then None
  else if String.sub long 0 short_len = short
  then Some (String.sub long short_len (long_len - short_len))
  else None

let ungeneralize_name (n:ident) : ident = n
  // let gen = reserved_prefix ^ "generalized_" in
  // match starts_with n.v.name gen with
  // | None -> n
  // | Some x ->  {n with v = { n.v with name=x }}

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
= let head_type = head_type e af.v.field_type in
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
    List.map (fun (i,t) -> GenericProbeFunction i t) generic_params,
    sig
  )

let rec generalize_probe_field (e:env) (path_prefix:string) (f:field) 
: ML (field & list generic_param & generalized_signature)
= match f.v with
  | AtomicField af -> (
    let head_type = head_type e af.v.field_type in
    let af, gs0, sig0 = generalize_atomic_field e path_prefix af in
    let f = { f with v = AtomicField af } in
    if not <| atomic_field_has_simple_probe e af
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
        let probe = with_range (Probe_action_var generic_name) f.range in
        let probe_call = { probe_call with probe_block = probe } in
        let af = { af with v = { af.v with field_probe = Some probe_call } } in
        let f = { f with v = AtomicField af } in
        f,
        gs0@[GenericProbeFunction generic_name head_type],
        sig0@[head_type]
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

let default_instantiation (e:env) (r:range) (head_type:ident)
: ML expr 
= match simple_probe_name_for_type e head_type with
  | None ->
    failwith (Printf.sprintf "Could not find probe instantiation for %s\n"
                (print_ident head_type))
  | Some probe_inst ->
    with_range (Identifier probe_inst) r

let default_instantiation_subst (e:env) (r:range) (gs:list generic_param) (sig:generalized_signature)
: ML subst
= let insts = 
    List.map2 
      (fun (GenericProbeFunction id _) s -> id, default_instantiation e r s)
      gs sig
  in
  mk_subst insts

let generalize_probes_decl (e:env) (d:decl)
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
        typedef_attributes = Noextract :: gen_name.typedef_attributes
    } in
    let instantiated_type =
      let head = gen_name.typedef_abbrev in
      let insts = List.map (default_instantiation e d.d_decl.range) sig in
      let instantiations =
        insts @
        List.map
          (function GenericProbeFunction i _ ->
            with_range (Identifier i) i.range)
          gs
      in
      let params =
        List.map (fun (_, i, _) -> Inl <| with_range (Identifier i) i.range) params
      in
      with_range (Type_app head KindSpec instantiations params)
                  d.d_decl.range
    in
    let inst_attrs = List.filter (fun a -> not (Aligned? a)) names.typedef_attributes in
    gen_name, instantiated_type, inst_attrs
  in
  match d.d_decl.v with
  | Record names gs params w fields -> (
    let fields, gs', sig = generalize_probe_fields e "" fields in
    match gs' with
    | [] -> [d]
    | _ -> (
      if is_entrypoint d
      then (
        let s = default_instantiation_subst e d.d_decl.range gs' sig in
        let fields = List.map (subst_field s) fields in
        [ { d with 
            d_decl = { d.d_decl with 
            v=Record names gs params w fields }} ]
      )
      else (
        let gen_name, instantiated_type, inst_attrs = generalize_type names gs params sig in
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
    | [] -> [d]
    | _ -> (
      if is_entrypoint d
      then (
        let s = default_instantiation_subst e d.d_decl.range gs' sig in
        let cases = List.map (subst_case s) cases in
        [ { d with 
            d_decl = { d.d_decl with 
            v=CaseType names gs params (v, cases) }} ]
      )
      else (
        let gen_name, instantiated_type, inst_attrs = generalize_type names gs params sig in
        let generalized_c =
          { d with 
            d_decl = { d.d_decl with 
            v=CaseType gen_name (gs'@gs) params (v, cases) }}
        in
        [generalized_c]
      )
    )
  )
  | _ -> [d]

let generalize_probe_decls (e:GlobalEnv.global_env) (ds:list decl)
: ML (list decl)
= let e = { benv = Binding.mk_env e; needs_probe = []; should_generalize = H.create 10 } in
  let e = need_probe_decls e ds in
  let print_ident (i:ident') = i.name in
  FStar.IO.print_string 
    (Printf.sprintf "Probes needed for: %s\nShould generalize: %s\n" 
      (String.concat ", " (List.map print_ident e.needs_probe))
      (String.concat ", " (H.fold (fun k _ out -> print_ident k::out) e.should_generalize [])));
  let ds = List.collect (generate_probe_functions e) ds in
  List.collect (generalize_probes_decl e) ds
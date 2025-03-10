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

type env = Binding.env & list ident'
let simple_probe_name_for_type (e:env) (type_name:ident)
: option ident
= if List.mem type_name.v (snd e)
  then (
    let name = reserved_prefix ^ "probe_" ^ type_name.v.name in
    let id = { type_name with v = { type_name.v with name } } in
    Some id
  )
  else None
let mark_for_probe (e:env) (id:ident) : ML env = fst e, id.v :: snd e
let rec head_type (e:env) (t:typ) : ML ident =
  match (Binding.unfold_typ_abbrev_only (fst e) t).v with
  | Type_app hd _ _ _ -> hd
  | Pointer t _ -> head_type e t
  | _ -> failwith 
          (Printf.sprintf "head_type: not a type application; got %s" (print_typ t))

let atomic_field_has_simple_probe (e:env) (f:atomic_field)
: bool
= match f.v.field_probe with
  | Some { probe_block = { v = Probe_action_simple _ l } } -> (
    match l.v with
    | App SizeOf [_] -> true
    | _ -> false
  )
  | _ -> false

let rec needs_probe_field (e:env) (f:field)
: ML env
= match f.v with
  | AtomicField f -> 
    if atomic_field_has_simple_probe e f
    then mark_for_probe e (head_type e f.v.field_type)
    else e
  | RecordField r _ -> List.fold_left needs_probe_field e r
  | SwitchCaseField sw _ -> List.fold_left needs_probe_case e (snd sw)

and needs_probe_case (e:env) (c:case)
: ML env
= match c with
  | Case _ f -> needs_probe_field e f
  | DefaultCase f -> needs_probe_field e f

let need_probe_decl (e:env) (d:decl) 
: ML env
= match d.d_decl.v with
  | Record _ _ _ _ fields -> List.fold_left needs_probe_field e fields
  | CaseType _ _ _ sw -> List.fold_left needs_probe_case e (snd sw)
  | _ -> e

let need_probe_decls (e:env) (ds:list decl) = List.fold_left need_probe_decl e ds

let should_generalize (e:env) (n:typedef_names) = List.mem n.typedef_abbrev.v (snd e)

let generate_probe_functions (e:env) (d:decl)
: ML (list decl)
= match d.d_decl.v with
  | Record names gs params w fields -> (
    if not <| should_generalize e names
    then [d]
    else (
      let Some simple_probe_name = simple_probe_name_for_type e names.typedef_abbrev in 
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
          (ProbeFunction simple_probe_name [] simple_probe)
          dummy_range
          []
          false
      in
      [d;d']
    )
  )
  | CaseType names gs params sw -> (
    if not <| should_generalize e names
    then failwith "Cannot automatically generate a probe function for a case type"
    else (
      [d]
    )
  )
  | _ -> [d]

let generalized_record_name (e:env) (n:typedef_names)
: ML typedef_names
= let name = reserved_prefix ^ "generalized_" ^ n.typedef_name.v.name in
  let name = { n.typedef_name with v = { n.typedef_name.v with name } } in
  let abbrev = reserved_prefix ^ "generalized_" ^ n.typedef_abbrev.v.name in
  let abbrev = { n.typedef_abbrev with v = { n.typedef_abbrev.v with name = abbrev } } in
  { typedef_name = name;
    typedef_abbrev = abbrev;
    typedef_ptr_abbrev = None;
    typedef_attributes = List.filter Aligned? n.typedef_attributes }

let rec generalize_probe_field (e:env) (path_prefix:string) (f:field) 
: ML (field & list generic_param & list generic_inst)
= match f.v with
  | AtomicField af -> (
    if not <| atomic_field_has_simple_probe e af
    then f, [], []
    else (
      let Some probe_call = af.v.field_probe in
      let generic_name = 
        with_range (
          to_ident' <|
          reserved_prefix ^ "probe_" ^ path_prefix ^ print_ident af.v.field_ident
        ) f.range
      in
      let probe = with_range (Probe_action_var generic_name) f.range in
      let head_type = head_type e af.v.field_type in
      match simple_probe_name_for_type e head_type with
      | None -> f, [], []
      | Some probe_inst ->
        let probe_inst = with_range (Identifier probe_inst) f.range in
        let probe_call = { probe_call with probe_block = probe } in
        let af = { af with v = { af.v with field_probe = Some probe_call } } in
        let f = { f with v = AtomicField af } in
        f, [GenericProbeFunction generic_name], [ probe_inst]
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
: ML (case & list generic_param & list generic_inst)
= match c with
  | Case ex f ->
    let f, gs, insts = generalize_probe_field e path_prefix f in
    Case ex f, gs, insts
  | DefaultCase f ->
    let f, gs, insts = generalize_probe_field e path_prefix f in
    DefaultCase f, gs, insts

and generalize_probe_fields (e:env) (path_prefix:string) (fs:list field) 
: ML (list field & list generic_param & list generic_inst)
= List.fold_right 
    (fun f (fs, gs, is) -> 
       let f, gs', is' = generalize_probe_field e path_prefix f in
       f::fs, gs'@gs, is'@is)
    fs ([], [], [])

and generalize_probe_cases (e:env) (path_prefix:string) (cs:list case)
: ML (list case & list generic_param & list generic_inst)
= List.fold_right 
    (fun f (fs, gs, is) -> 
       let f, gs', is' = generalize_probe_case e path_prefix f in
       f::fs, gs'@gs, is'@is)
    cs ([], [], [])

let generalize_probes_decl (e:env) (d:decl)
: ML (list decl)
= match d.d_decl.v with
  | Record names gs params w fields -> (
    let fields, gs', insts = generalize_probe_fields e "" fields in
    match gs' with
    | [] -> [d]
    | _ -> (
      let gen_name = generalized_record_name e names in
      let generalized_record =
        { d with 
          d_decl = { d.d_decl with 
          v=Record gen_name (gs'@gs) params w fields }}
      in
      let instantiated_type =
        let head = gen_name.typedef_abbrev in
        let instantiations =
          insts @
          List.map
            (function GenericProbeFunction i ->
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
      let instantiated_record =
        { d with 
          d_decl = { d.d_decl with 
          v=TypeAbbrev inst_attrs instantiated_type names.typedef_abbrev gs params }}
      in
      [generalized_record; instantiated_record]
    )
  )
  | CaseType _ _ _ _ -> generate_probe_functions e d
  | _ -> [d]

let generalize_probe_decls (e:GlobalEnv.global_env) (ds:list decl)
: ML (list decl)
= let e = Binding.mk_env e, [] in
  let e = need_probe_decls e ds in
  let print_ident (i:ident') = i.name in
  FStar.IO.print_string 
    (Printf.sprintf "Probes needed for: %s\n" 
      (String.concat ", " (List.map print_ident (snd e))));
  let ds = List.collect (generate_probe_functions e) ds in
  FStar.IO.print_string
    (Printf.sprintf "Generated probe functions\n%s\n" (print_decls ds));
  List.collect (generalize_probes_decl e) ds
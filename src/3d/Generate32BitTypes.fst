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
module Generate32BitTypes
(*
  This module implements a pass over the source AST,
  to add 32-bit variants of types that have probe functions
*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
module H = Hashtable
module B = Binding
open GlobalEnv

type env_t = B.env & list ident 
let should_specialize (e:env_t) (id:ident) : ML bool = 
  List.existsb (fun id' -> eq_idents id id') (snd e)
let name32 (head_name:ident) : ident =
  let gen = reserved_prefix ^ "specialized32_" ^ head_name.v.name in
  {head_name with v = { head_name.v with name = gen }}

let coercion_for_type (t:ident) : ML ident =
  name32 (GeneralizeProbes.simple_probe_function_for_type t)

let gen_name_32 (n:typedef_names) 
: ML typedef_names
= let name = name32 n.typedef_name in
  let abbrev = name32 n.typedef_abbrev in
  { typedef_name = name;
    typedef_abbrev = abbrev;
    typedef_ptr_abbrev = None;
    typedef_attributes = Noextract :: List.filter Aligned? n.typedef_attributes }

//only specializing pointer types to 32 bit
let maybe_specialize_32 (e:env_t) (t:typ)
: ML (option typ)
= match t.v with
  | Pointer _ (PQ UInt64 false _) -> //implicit U64 pointer
    Some tuint32

  | Pointer _ pq ->
    None

  | Type_app id ts gs ps -> (
    let t = B.unfold_typ_abbrev_and_enum (fst e) t in
    if B.typ_is_integral (fst e) t
    then None
    else if should_specialize e id
    then (
      Some { t with v = Type_app (name32 id) ts gs ps }
    )
    else None
  )
  | _ -> None

let maybe_gen_l 
      (gen_a: ('a -> ML (bool & 'a)))
      (l: list 'a)
: ML (bool & list 'a)
= let changed, l' =
    List.fold_right
      (fun field (b, fields) ->
        let b', field' = gen_a field in
        b || b', field' :: fields)
      l
      (false, [])
  in
  if changed
  then true, l'
  else false, l
  

let rec gen_field (e:env_t) (f:field) 
: ML (bool & field)
= match f.v with
  | AtomicField af -> (
    match maybe_specialize_32 e af.v.field_type with
    | None -> false, f
    | Some t32 ->
      let af32 = { af with v = { af.v with field_type = t32; field_probe=None } } in
      true, { f with v=AtomicField af32 }
  )
  | RecordField r i -> (
    let changed, r' = maybe_gen_l (gen_field e) r in
    if changed
    then true, { f with v=RecordField r' i }
    else false, f
  )
  | SwitchCaseField sw i -> (
    let changed, cases = maybe_gen_l (gen_case e) (snd sw) in
    let sw = (fst sw, cases) in
    if changed
    then true, { f with v=SwitchCaseField sw i }
    else false, f
  )

and gen_case (env:env_t) (c:case)
: ML (bool & case)
= match c with
  | Case e f -> (
    let b, f' = gen_field env f in
    if b
    then b, Case e f'
    else false, c
  )
  | DefaultCase f -> (
    let b, f' = gen_field env f in
    if b
    then b, DefaultCase f'
    else false, c
  )

let rec gen_decl (env:env_t) (d:decl) : ML (option decl) =
  match d.d_decl.v with
  | Record names gs params w fields ->
    let changed, fields32 = maybe_gen_l (gen_field env) fields in
    if changed
    then (
      let names_32 = gen_name_32 names in
      let d32 = Record names_32 gs params w fields32 in
      Some (mk_decl d32 d.d_decl.range [] false)
    )
    else None

  | CaseType names gs params (e, cases) -> (
    let changed, cases = maybe_gen_l (gen_case env) cases in
    if changed
    then (
      let names_32 = gen_name_32 names in
      let d32 = CaseType names_32 gs params (e, cases) in
      Some (mk_decl d32 d.d_decl.range [] false)
    )
    else None
  ) 

  | TypeAbbrev attrs t i gs ps -> (
    match t.v with
    | Type_app id _ _ _ -> (
      let decl, _ = Binding.lookup_type_decl (fst env) id in
      gen_decl env decl
      ) 
    | _ -> None
  )

  | _ -> None

let gen_decls (e:env_t) (d: decl)
: ML (list decl & env_t)
= match d.d_decl.v with
  | ProbeFunction id ps v (SimpleProbeFunction tn) -> (
    
    let decl, _ = Binding.lookup_type_decl (fst e) tn in
    match gen_decl e decl with
    | None -> 
      let c = ProbeFunction (name32 id) ps v (SimpleProbeFunction tn) in
      let c = mk_decl c d.d_decl.range [] false in
      [d;c], e
    | Some d' ->
      let src =
        match idents_of_decl d' with
        | [id] -> id
        | [_; id] -> id
        | _ -> failwith "Unexpected number of names"
      in
      let name = name32 id in
      let c =
        mk_decl 
          (CoerceProbeFunctionStub (name32 id) ps (CoerceProbeFunction (src, tn)))
          d.d_decl.range 
          [] 
          false
      in
      [d'; d; c], (fst e, tn :: snd e)
  )
  | _ ->
    [d], e

let has_32bit_coercion (e:B.env) (t32 t:typ) : ML (option ident) =
  let t32 = B.unfold_typ_abbrev_only e t32 in
  let t = B.unfold_typ_abbrev_only e t in
  match t.v, t32.v with
  | Type_app id _ _ _, Type_app id32 _ _ _ -> 
    Options.debug_print_string <|
      Printf.sprintf "Checking for coercion from %s to %s\n" (print_ident id32) (print_ident id);
    GlobalEnv.find_probe_fn (B.global_env_of_env e) (CoerceProbeFunction (id32, id))
  | _ ->
    None

let generate_32_bit_types (e:GlobalEnv.global_env) (d: list decl)
: ML (list decl)
= let env : env_t = B.mk_env e, [] in
  let env, ds =
    List.fold_left 
      (fun (env, out) d ->
        let d, env = gen_decls env d in
        (env, List.rev d @ out))
      (env, [])
      d
  in
  List.rev ds
 
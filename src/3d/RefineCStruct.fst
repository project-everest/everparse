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
module RefineCStruct
(*
  This module generate C types for all aligned record types, 
  and generates refining blocks to relate the C types to the
  original record types. 
*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
module H = Hashtable
module B = Binding
open GlobalEnv
module TS = TypeSizes
let env_t = TS.env_t

noeq
type ctype = 
| Ty of typ
| Struct of cfields
| Union of cfields
and cfield = ctype & ident & option int
and cfields = list cfield

noeq
type ctype_decl =
| CStruct : ident -> ident -> cfields -> ctype_decl
| CUnion : ident -> ident -> cfields -> ctype_decl

let no_module (i:ident) : ML ident = { i with v = { i.v with modul_name = None } }
let cname_of_names (names:typedef_names)
: ML (ident & ident)
= names.typedef_name, names.typedef_abbrev

let ctype_of_typ (e:env_t) (t:typ)
: ML (option ctype)
= match t.v with
  | Pointer _ (PQ UInt32 _) -> Some <| Ty tuint32
  | Pointer _ (PQ UInt64 _) -> Some <| Ty tuint64
  | Type_arrow _ _ -> None // no Ctype analog for function types
  | _ ->
    let t = Binding.unfold_typ_abbrev_and_enum (fst e) t in
    Some <| Ty t

let rec cfield_of_field (e:env_t) (f:field)
: ML (list cfield)
= match f.v with
  | AtomicField f ->
    if TS.is_alignment_field f.v.field_ident then []
    else (
      match f.v.field_array_opt with
      | FieldScalar -> (
        match ctype_of_typ e f.v.field_type with
        | Some ct -> [ct, f.v.field_ident, None]
        | _ -> []
      )
      | FieldArrayQualified ({v=Constant (Int _ n)}, ByteArrayByteSize) ->
        [Ty tuint8, f.v.field_ident, Some n]
      | FieldArrayQualified _
      | FieldString _
      | FieldConsumeAll -> [] // no Ctype analog for these fields
    )
  | RecordField fields i ->
    let cfields = List.collect (cfield_of_field e) fields in
    [Struct cfields, i, None]
  | SwitchCaseField sw i ->
    let cfields = cfields_of_switch_case e sw in
    [Union cfields, i, None]

and cfields_of_switch_case (e:env_t) (sw:switch_case)
: ML (list cfield)
= let fields = List.map (function Case _ f -> f | DefaultCase f -> f) (snd sw) in 
  let cfields = List.collect (cfield_of_field e) fields in
  cfields

let ctype_of_decl (e:env_t) (d:decl)
: ML (list ctype_decl)
= match d.d_decl.v with
  | Record names _gs _ps _w fields ->
    if List.existsb Aligned? names.typedef_attributes
    then (
      let cfields = List.collect (cfield_of_field e) fields in
      let name, abbr = cname_of_names names in
      [CStruct name abbr cfields]
    )
    else []

  | CaseType names _ _ sw ->
    if List.existsb Aligned? names.typedef_attributes
    then (
      let cfields = cfields_of_switch_case e sw in
      let name, abbr = cname_of_names names in
      [CUnion name abbr cfields]
    )
    else []

  | _ -> []

let refine_records (e:GlobalEnv.global_env) (t:TS.size_env) (p:prog)
: ML (list ctype_decl & prog)
= let e = B.mk_env e, t in
  let decls, type_refinements = p in
  let ctypes = List.collect (ctype_of_decl e) decls in
  let ref =
    List.collect
      (function (CStruct _ abbr _) -> [no_module abbr, Some abbr] | _ -> [])
      ctypes
  in
  let type_refinements = 
    match type_refinements, ref with
    | None, [] -> None
    | None, _ -> Some { includes = []; type_map = ref }
    | Some r, _ -> Some { r with type_map = r.type_map @ ref }
  in
  ctypes, (decls, type_refinements)

let print_indent (n:nat)
: ML string
= String.make (2 * n) ' '

let rec print_typ (t:typ)
: ML string
= match t.v with
  | Type_app i _ _ _ -> i.v.name
  | Pointer t0 _ -> Printf.sprintf "%s*" (print_typ t0)
  | _ -> failwith "print_typ: unsupported type"

let rec print_ctyp (indent:nat) (ct:ctype)
: ML string
= match ct with
  | Ty t -> print_typ t
  | Struct fs -> 
    Printf.sprintf "struct { %s }" (print_cfields (indent + 1) fs)
  | Union fs -> 
    Printf.sprintf "union { %s }" (print_cfields (indent + 1) fs)

and print_cfield indent (c:cfield)
: ML string
= let ct, i, arr = c in
  match arr with
  | None -> Printf.sprintf "%s %s;" (print_ctyp indent ct) i.v.name
  | Some n -> Printf.sprintf "%s %s[%d];" (print_ctyp indent ct) i.v.name n

and print_cfields (indent:nat) (c:list cfield)
: ML string
= String.concat ("\n" ^ print_indent indent) <| List.map (print_cfield indent) c

let print_ctype_decl ct
: ML string
= let label, name, abbr, fields =
    match ct with 
    | CStruct name abbr fields -> "struct", name, abbr, fields
    | CUnion name abbr fields -> "union", name, abbr, fields
  in
  Printf.sprintf "typedef %s %s\n{\n%s%s\n} %s;" label name.v.name (print_indent 1) (print_cfields 1 fields) abbr.v.name

let print_ctypes (ctypes:list ctype_decl)
: ML string
= List.map print_ctype_decl ctypes |> String.concat "\n\n"
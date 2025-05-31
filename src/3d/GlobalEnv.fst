(*
   Copyright 2019 Microsoft Research

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
module GlobalEnv

(*
  This module implements a pass over the source AST
     -- checking that all names are properly bound
     -- well-typed
     -- computing the size of types
     -- computing which fields are dependent on others
*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
module H = Hashtable

/// Computed attributes for a decl:
///    -- its size in bytes
///    -- whether or not it ends with a variable-length field (suffix)
///    -- whether or not its validator may fail
///    -- whether the type is an integral type, i.e., can it be decomposed into bitfields
type decl_attributes = {
  may_fail:bool;
  integral:option integer_type;
  bit_order: (bit_order: option bitfield_bit_order { Some? bit_order ==> Some? integral });
  has_reader:bool;
  parser_weak_kind:weak_kind;
  parser_kind_nz:option bool
}

noeq
type macro_signature = {
  macro_arguments_t: list typ;
  macro_result_t: typ;
  macro_defn_t:option expr
}

let nullary_macro t d = {
  macro_arguments_t = [];
  macro_result_t = t;
  macro_defn_t = d
}

(* Type-checking environments *)

/// global_env ge_h field is a hash (hence `_h`) table that:
///  -- maps top-level identifiers to their corresponding declaration
///  -- maps type identifiers to decl_attributes
///  -- maps macro names to their types
///
/// global_env ge_fd field maps a unique numerical identifier to each
/// "struct identifier - field (hence `_fd`) name" pair. It is part of
/// the global environment so that numerical field identifiers are
/// proper to the current module, and not shared across different .3d
/// files given on the command line

type global_hash_t = H.t ident' (decl & either decl_attributes macro_signature)

noeq
type global_env = {
  mname: string;
  ge_h: global_hash_t;
  ge_out_t: H.t ident' decl;  //a table for output types declarations
  ge_extern_t: H.t ident' decl;  //a table for extern type declarations
  ge_extern_fn: H.t ident' decl;  //a table for extern function declarations
  ge_probe_fn: H.t ident' decl;  //a table for probe function declarations
  ge_cfg: option (Config.config & string)
}

let copy_hash_table #k #v (h:H.t k v) : ML (H.t k v) =
  let h' = H.create 100 in
  let f k v = H.insert h' k v in
  H.iter f h;
  h'

let copy_global_env (g:global_env) : ML global_env =
  let h = copy_hash_table g.ge_h in
  let out_t = copy_hash_table g.ge_out_t in
  let extern_t = copy_hash_table g.ge_extern_t in
  let extern_fn = copy_hash_table g.ge_extern_fn in
  let probe_fn = copy_hash_table g.ge_probe_fn in
  let cfg = g.ge_cfg in
  { 
    mname=g.mname;
    ge_h=h;
    ge_out_t=out_t; 
    ge_extern_t=extern_t;
    ge_extern_fn=extern_fn;
    ge_probe_fn=probe_fn;
    ge_cfg=cfg
  }
  
let module_name_matches (g:global_env) (id:ident) : ML bool =
  match id.v.modul_name with
  | None -> true
  | Some m -> m = g.mname

let _and_ (x:bool) (y:bool) : ML bool = x && y

let check_unique (msg:unit -> ML string) (r:range) (l:list ident)
: ML (option ident)
= match l with
  | [] -> None
  | [x] -> Some x
  | _ ->
    error (Printf.sprintf "%s: %s" (msg()) (String.concat ", " (List.map print_ident l))) r

let extern_probe_fn_qual (g:global_env) (r:range) (pq:probe_qualifier)
: ML (option ident)
= let finder k v out : ML _ =
      match v.d_decl.v with
      | ExternProbe id pq' ->
        if (pq=pq') `_and_` module_name_matches g id then id::out else out
      | _ -> out
  in
  check_unique (fun _ -> "Found multiple probe functions") r (H.fold finder g.ge_probe_fn [])

let default_probe_fn (g:global_env) (r:range)
: ML (option ident)
= extern_probe_fn_qual g r PQWithOffsets

let resolve_probe_fn_any (g:global_env) (id:ident)
  : ML (option (ident & either typ probe_qualifier))
  = match H.try_find g.ge_probe_fn id.v with
    | Some {d_decl={v=ExternProbe id pq}} ->
      Some (id, Inr pq)
    | Some {d_decl={v=ProbeFunction id ps pq _}} ->
      Some (id, Inl (mk_arrow_ps ps probe_m_t))
    | Some {d_decl={v=CoerceProbeFunctionStub id ps _}} ->
      Some (id, Inl (mk_arrow_ps ps probe_m_t) )
    | _ -> None

let resolve_probe_fn (g:global_env) (id:ident) (pq:probe_qualifier)
  : ML (option ident)
  = match resolve_probe_fn_any g id with
    | Some (id, Inr pq') -> if pq=pq' then Some id else None
    | _ -> None

let eq_probe_function_type pq0 pq1 : ML bool =
  match pq0, pq1 with
  | SimpleProbeFunction t0, SimpleProbeFunction t1 -> eq_idents t0 t1
  | CoerceProbeFunctionPlaceholder t0, CoerceProbeFunctionPlaceholder t1 -> eq_idents t0 t1
  | CoerceProbeFunction (t0, t1), CoerceProbeFunction (t0', t1') ->
    Options.debug_print_string <|
      Printf.sprintf "Comparing %s to %s\n" (print_probe_function_type pq0) (print_probe_function_type pq1);
    eq_idents t0 t0' && eq_idents t1 t1'
  | HelperProbeFunction, HelperProbeFunction -> true
  | _, _ -> false

let find_probe_fn (g:global_env) r (pq:probe_function_type)
: ML (option ident)
= let finder k v out : ML (list ident) =
      match v.d_decl.v with
      | ProbeFunction id _ _ pq' 
      | CoerceProbeFunctionStub id _ pq' ->
        if eq_probe_function_type pq pq' `_and_` module_name_matches g id then id::out else out
      | _ -> out
  in
  check_unique (fun _ -> "Found multiple probe functions") r (H.fold finder g.ge_probe_fn [])

let fields_of_type (g:global_env) (typename:ident)
: ML (option (list field))
= match H.try_find g.ge_h typename.v with
  | Some ({d_decl={v=Record _ _ _ _ fields}}, _) -> Some fields
  | _ -> None

let resolve_extern_coercion (g:global_env) (r:range) (t0 t1:typ)
: ML (option ident)
= let finder k v out : ML _ =
    match v.d_decl.v with
    | ExternFn id t1' [(t0', _, _)] true ->
      if eq_typ t0 t0' `_and_` eq_typ t1 t1'
      `_and_` module_name_matches g id 
      then id::out
      else out
      
    | _ -> out
  in
  check_unique
    (fun _ -> 
      Printf.sprintf "Multiple extern coercions found for %s -> %s"
        (print_typ t0) (print_typ t1))
    r
    (H.fold finder g.ge_extern_fn [])

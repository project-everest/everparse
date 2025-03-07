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
  ge_h: global_hash_t;
  ge_out_t: H.t ident' decl;  //a table for output types declarations
  ge_extern_t: H.t ident' decl;  //a table for extern type declarations
  ge_extern_fn: H.t ident' decl;  //a table for extern function declarations
  ge_probe_fn: H.t ident' decl;  //a table for probe function declarations
  ge_cfg: option (Config.config & string)
}

let default_probe_fn (g:global_env)
  : ML (option ident)
  = if H.length g.ge_probe_fn <> 1
    then None 
    else (
      match H.fold (fun k v _ -> Some v) g.ge_probe_fn (None #decl) with
      | Some {d_decl={v=ExternProbe id None}} -> Some id
      | _ -> None
    )

let resolve_probe_fn_any (g:global_env) (id:ident)
  : ML (option (ident & option probe_qualifier))
  = match H.try_find g.ge_probe_fn id.v with
    | Some {d_decl={v=ExternProbe id pq}} ->
      Some (id, pq)
    | _ -> None

let resolve_probe_fn (g:global_env) (id:ident) (pq:option probe_qualifier)
  : ML (option ident)
  = match resolve_probe_fn_any g id with
    | None -> None
    | Some (id, pq') -> if pq=pq' then Some id else None

let fields_of_type (g:global_env) (typename:ident)
: ML (option (list field))
= match H.try_find g.ge_h typename.v with
  | Some ({d_decl={v=Record _ _ _ _ fields}}, _) -> Some fields
  | _ -> None
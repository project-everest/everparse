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
module Binding
open FStar.All
open Ast
include GlobalEnv

val env : Type0
val mk_env (g:global_env) : ML env
val global_env_of_env (e:env) : ML global_env

val resolve_record_case_output_extern_type_name (_:env) (_:ident): ML ident
val lookup_type_decl (_:env) (_:ident) : ML (decl & decl_attributes)
val resolve_record_type (_:env) (_:ident) 
: ML (res:(decl & decl_attributes) { Record? (fst res).d_decl.v })
val params_of_decl (d:decl) : list generic_param & list param
val lookup_expr_name (_:env) (_:ident) : ML typ
val lookup_macro_definition (_:env) (_:ident) : ML (option expr)
val typ_is_integral (_:env) (_:typ) : ML bool
val has_reader (_:global_env) (_:ident) : ML bool
val parser_kind_nz (env:global_env) (id:ident) : ML (option bool)
val parser_weak_kind  (env:global_env) (id:ident) : ML (option weak_kind)
val unfold_typ_abbrev_only (_:env) (t:typ) : ML typ
val unfold_typ_abbrev_and_enum (env:env) (t:typ) : ML typ
val update_typ_abbrev (_:env) (id:ident) (t:typ) : ML unit
val size_of_integral_typ (_:env) (_:typ) (_:range) : ML int
val bit_order_of_integral_typ (_:env) (_:typ) (_:range) : ML bitfield_bit_order
val bind_decls (g:global_env) (p:list decl) : ML (list decl & global_env)
//val add_field_error_code_decls (ge: env) : ML (list decl)

val initial_global_env (mname:string) : ML global_env
// DOES NOT return exported output types/extern types/extern functions
val get_exported_decls (ge:global_env) (mname:string) : ML (list ident' & list ident')  //exported, private
val finish_module (ge:global_env) (mname:string)
  : ML global_env

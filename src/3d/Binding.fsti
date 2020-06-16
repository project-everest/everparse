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

val global_env : Type0

val all_nums (ge: global_env)
  : ML (list (field_num & option ident & string)) //retrieve a table of identifier/field-name mappings

(* retrieve the name of the field code variable *)
val lookup_field_num : global_env -> field_num -> ML (option ident)

val env : Type0
val mk_env (g:global_env) : ML env

val resolve_typedef_abbrev (_:env) (_:ident): ML ident
val lookup_expr_name (_:env) (_:ident) : ML typ
val size_of_typ (_:env) (_:typ) : ML size
val has_reader (_:global_env) (_:ident) : ML bool
val parser_kind_nz (env:global_env) (id:ident) : ML (option bool)
val has_suffix (env:global_env) (id:ident) : ML bool
val value_of_const_expr (env:env) (e:expr) : ML (option (either bool (integer_type & int)))
val map_opt (f:'a -> ML 'b) (o:option 'a) : ML (option 'b)



let prog = list decl

val bind_prog (p:prog) : ML (prog & global_env)

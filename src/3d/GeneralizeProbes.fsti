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
open FStar.All
open Ast
val simple_probe_function_for_type (t:ident) : ident 

val generic_instantiations_for_type (e:Binding.env) (tt:typ)
: ML (list expr & typ)

val generalize_probe_decls (e:GlobalEnv.global_env) (ds:list decl)
: ML (list decl)
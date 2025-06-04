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
  This module implements a pass over the source AS11T,
  to add 32-bit variants of types that have probe functions
*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
module B = Binding

val coercion_for_type (t:ident)
: ML ident

val has_32bit_coercion (e:B.env) (t32 t:typ) : ML (option ident)

val generate_32_bit_types (e:GlobalEnv.global_env) (d: list decl)
: ML (list decl)

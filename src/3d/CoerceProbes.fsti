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
module CoerceProbes
(*
  This module implements a pass over the source AST,
  elaborating CoerceProbeFunctionStubs into ProbeFunctions, 
  by coercing a 32-bit layout type into a 64-bit layout type 
*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
open GlobalEnv

val replace_stubs (e:global_env) (ds:list decl)
: ML (list decl)
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
module Simplify
open Ast
open FStar.All
module B = Binding

(*
  This module implements a pass over the source AST

    1. Simplifying refinement expressions, in particular reducing
       sizeof expressions to constants
*)

val simplify_prog (benv:B.global_env) (senv:TypeSizes.size_env) (p:list decl) : ML (list decl)

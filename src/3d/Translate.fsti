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
module Translate
(* This module translates type definitions from the source Ast
   to types, parsers and validators in the Target language *)
module A = Ast
module B = Binding
module T = Target
open FStar.All

val translate_decls (env:B.global_env) (d:list A.decl) : ML (list T.decl)

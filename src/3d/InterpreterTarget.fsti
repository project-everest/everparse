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
module InterpreterTarget
(* The abstract syntax for the code produced by 3d, targeting prelude/Interpreter.fst *)
open FStar.All
module A = Ast
module T = Target
open Binding

val type_decl : Type0

val translate_decls (ds:T.decls)
  : ML (list type_decl)

val print_type_decls (mname:string) (ds:list type_decl)
  : ML string

val print_validators (mname:string) (ds:list type_decl)
  : ML string

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
let expr = T.expr
let action = T.action
let lam a = A.ident & a
type itype =
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | UInt8BE
  | UInt16BE
  | UInt32BE
  | UInt64BE
  | Unit
  | AllBytes
  | AllZeros

noeq
type dtyp : Type =
  | DT_IType:
      i:itype -> dtyp

  | DT_App:
      hd:A.ident ->
      args:list expr ->
      dtyp

let non_empty_string = s:string { s <> "" }

let nes (s:string)
  : non_empty_string
  = if s = "" then "missing" else s

noeq
type typ : Type =
  | T_false:
      fn:non_empty_string ->
      typ

  | T_denoted:
      fn:non_empty_string ->
      d:dtyp ->
      typ

  | T_pair:
      fn:non_empty_string ->
      t1:typ ->
      t2:typ ->
      typ

  | T_dep_pair:
      fn:non_empty_string ->
      t1:dtyp ->
      t2:lam typ ->
      typ

  | T_refine:
      fn:non_empty_string ->
      base:dtyp ->
      refinement:lam expr ->
      typ

  | T_refine_with_action:
      fn:non_empty_string ->
      base:dtyp ->
      refinement:lam expr ->
      a:lam action ->
      typ

  | T_dep_pair_with_refinement:
      fn:non_empty_string ->
      base:dtyp ->
      refinement:lam expr ->
      k:lam typ ->
      typ

  | T_dep_pair_with_action:
      fn:non_empty_string ->
      base:dtyp ->
      k:lam typ ->
      a:lam action ->
      typ

  | T_dep_pair_with_refinement_and_action:
      fn:non_empty_string ->
      base:dtyp ->
      refinement:lam expr ->
      k:lam typ ->
      a:lam action ->
      typ

  | T_if_else:
      b:expr ->
      t1:typ ->
      t2:typ ->
      typ

  | T_with_action:
      fn:non_empty_string ->
      base:typ ->
      act:action ->
      typ

  | T_with_dep_action:
      fn:non_empty_string ->
      head:dtyp ->
      act:lam action ->
      typ

  | T_with_comment:
      fn:non_empty_string ->
      t:typ ->
      c:string ->
      typ

  | T_nlist:
      fn:non_empty_string ->
      n:expr ->
      t:typ ->
      typ

  | T_at_most:
      fn:non_empty_string ->
      n:expr ->
      t:typ ->
      typ

  | T_exact:
      fn:non_empty_string ->
      n:expr ->
      t:typ ->
      typ

  | T_string:
      fn:non_empty_string ->
      element_type:dtyp ->
      terminator:expr ->
      typ

val decl : Type0
val env : Type0

val create_env (_:unit) : ML env

val translate_decls (e:env) (ds:T.decls)
  : ML (list decl)

val print_decls (e:env) (mname:string) (ds:list decl)
  : ML (string & string)

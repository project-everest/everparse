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

let allow_reader_of_itype (i:itype)
  : bool
  = match i with
    | AllBytes
    | AllZeros -> false
    | _ -> true

let readable_itype = (i: itype { allow_reader_of_itype i == true })

noeq
type dtyp : Type =
  | DT_IType:
      i:itype -> dtyp

  | DT_App:
      has_action:bool ->
      readable: bool ->
      hd:A.ident ->
      args:list expr ->
      dtyp

let allow_reader_of_dtyp (d: dtyp) : Tot bool =
  match d with
  | DT_IType i -> allow_reader_of_itype i
  | DT_App _ readable _ _ -> readable

let has_action_of_dtyp d : Tot bool =
  match d with
  | DT_IType _ -> false
  | DT_App has_action _ _ _ -> has_action
  
let readable_dtyp = (d: dtyp { allow_reader_of_dtyp d == true })

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
      k1_const: bool -> // whether t1 is a total compile-time constant size type without actions
      t1:typ ->
      k2_const: bool ->
      t2:typ ->
      typ

  | T_dep_pair:
      fn:non_empty_string ->
      t1:readable_dtyp ->
      t2:lam typ ->
      typ

  | T_refine:
      fn:non_empty_string ->
      base:readable_dtyp ->
      refinement:lam expr ->
      typ

  | T_refine_with_action:
      fn:non_empty_string ->
      base:readable_dtyp ->
      refinement:lam expr ->
      a:lam action ->
      typ

  | T_dep_pair_with_refinement:
      fn:non_empty_string ->
      base:readable_dtyp ->
      refinement:lam expr ->
      k:lam typ ->
      typ

  | T_dep_pair_with_action:
      fn:non_empty_string ->
      base:readable_dtyp ->
      k:lam typ ->
      a:lam action ->
      typ

  | T_dep_pair_with_refinement_and_action:
      fn:non_empty_string ->
      base:readable_dtyp ->
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
      head:readable_dtyp ->
      act:lam action ->
      typ

  | T_drop:
      t:typ ->
      typ

  | T_with_comment:
      fn:non_empty_string ->
      t:typ ->
      c:string ->
      typ

  | T_nlist:
      fn:non_empty_string ->
      fixed_size_t:bool -> //does t have a fixed size?
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
      element_type:readable_dtyp ->
      terminator:expr ->
      typ

  | T_probe_then_validate:
      fn:non_empty_string ->
      t:dtyp ->
      sz:A.pointer_size_t ->
      probe:T.probe_action ->
      dest:A.ident ->
      as_u64:A.ident ->
      typ

val typ_indexes : Type0
noeq
type type_decl = {
  name : T.typedef_name;
  typ : typ;
  kind : T.parser_kind;
  typ_indexes : typ_indexes;
  has_action: bool;
  allow_reading: bool;
  attrs : (attrs: T.decl_attributes { attrs.is_entrypoint ==> ~ allow_reading });
  enum_typ: option (t:T.typ {T.T_refine? t })
}
let not_type_decl = (d: T.decl { ~ (T.Type_decl? (fst d)) })
let decl : Type0 = either not_type_decl type_decl
val env : Type0

val create_env (_:unit) : ML env

val translate_decls (e:env) (ds:T.decls)
  : ML (list decl)

val print_decls (e:env) (mname:string) (ds:list decl)
  : ML (string & string)

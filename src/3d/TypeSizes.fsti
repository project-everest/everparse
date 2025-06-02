(*
   Copyright 2019 Microsoft Research

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
module TypeSizes
open FStar.All
open Ast
open FStar.Mul
module H = Hashtable
module B = Binding

let alignment = option (x:int{x == 1 \/ x == 2 \/ x == 4 \/ x == 8})

type size =
  | Fixed of int
  | WithVariableSuffix of int
  | Variable

val size_env : Type0

val initial_senv (_:unit) : ML size_env

let env_t = B.env & size_env

val size_of_typename (env:env_t) (i:ident)
  : ML size

val size_of_typ (env:env_t) (t:typ)
  : ML size

val value_of_const_expr (env:env_t) (e:expr)
  : ML (option (either bool (integer_type & int)))

val field_size_and_alignment (env:env_t) (enclosing_typ:ident) (field_name:ident)
  : ML (option (size & alignment))

val field_offsets_of_type (env:env_t) (typ:ident)
: ML (either (list (ident & int)) string)

val is_alignment_field (fieldname:ident)
: bool

val size_of_decls (env:B.global_env) (senv:size_env) (d:list decl)
  : ML (list decl)

val finish_module (en:size_env) (mname:string) (e_and_p:list ident' & list ident')
  : ML unit

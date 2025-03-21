module Specialize
(*
  This module implements a pass over the source AST,
  elaborating the `specialize` declaration
*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
module B = Binding

val specialize (e:GlobalEnv.global_env) (d: list decl)
: ML (list decl)

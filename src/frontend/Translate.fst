module Translate
open Ast
module A = Ast
module T = Target
open FStar.All

let translate_decl (d:A.decl) : ML T.decl =
  match d.v with
  | Comment _ -> None

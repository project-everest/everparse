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

noeq
type dtyp : Type =
  | DT_IType:
      i:itype -> dtyp

  | DT_App:
      hd:A.ident ->
      args:list expr ->
      dtyp

noeq
type typ : Type =
  | T_false:
      typ

  | T_denoted:
      d:dtyp ->
      typ

  | T_pair:
      t1:typ ->
      t2:typ ->
      typ

  | T_dep_pair:
      t1:dtyp ->
      t2:lam typ ->
      typ

  | T_refine:
      base:dtyp ->
      refinement:lam expr ->
      typ

  | T_dep_pair_with_refinement:
      base:dtyp ->
      refinement:lam expr ->
      k:lam typ ->
      typ

  | T_dep_pair_with_refinement_and_action:
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
      base:typ ->
      act:action ->
      typ

  | T_with_dep_action:
      head:dtyp ->
      act:lam action ->
      typ

  | T_with_comment:
      t:typ ->
      c:A.comments ->
      typ

  | T_nlist:
      n:expr ->
      t:typ ->
      typ

  | T_at_most:
      n:expr ->
      t:typ ->
      typ

  | T_exact:
      n:expr ->
      t:typ ->
      typ

  | T_string:
      element_type:dtyp ->
      terminator:expr ->
      typ

let type_decl = T.typedef_name & typ
let decl = either T.decl type_decl

let dtyp_of_app (hd:A.ident) (args:list T.index)
  : ML dtyp
  = match hd.v.name, args with
    | "UINT8", [] ->
      DT_IType UInt8

    | "UINT16", [] ->
      DT_IType UInt16

    | "UINT32", [] ->
      DT_IType UInt32

    | "UINT64", [] ->
      DT_IType UInt64

    | _ ->
      DT_App hd
        (List.map
          (function Inl _ -> failwith "Unexpected type application"
                  | Inr e -> e)
          args)

let tag_of_parser p
  = let open T in
    match p.p_parser with
    | Parse_return _ -> "Parse_return"
    | Parse_app _ _ -> "Parse_app"
    | Parse_nlist _ _ -> "Parse_nlist"
    | Parse_t_at_most _ _ -> "Parse_t_at_most"
    | Parse_t_exact _ _ -> "Parse_t_exact"
    | Parse_pair _ _ _ -> "Parse_pair"
    | Parse_dep_pair _ _ _ -> "Parse_dep_pair"
    | Parse_dep_pair_with_refinement _ _ _ _ -> "Parse_dep_pair_with_refinement"
    | Parse_dep_pair_with_action _ _ _ -> "Parse_dep_pair_with_action"
    | Parse_dep_pair_with_refinement_and_action _ _ _ _ _ -> "Parse_dep_pair_with_refinement_and_action"
    | Parse_map _ _ -> "Parse_map"
    | Parse_refinement _ _ _ -> "Parse_refinement"
    | Parse_refinement_with_action _ _ _ _ -> "Parse_refinement_with_action"
    | Parse_with_dep_action _ _ _ -> "Parse_with_dep_action"
    | Parse_with_action _ _ _ -> "Parse_with_action"
    | Parse_weaken_left _ _ -> "Parse_weaken_left"
    | Parse_weaken_right _ _ -> "Parse_weaken_right"
    | Parse_if_else _ _ _ -> "Parse_if_else"
    | Parse_impos -> "Parse_impos"
    | Parse_with_comment _ _ -> "Parse_with_comment"
    | Parse_string _ _ -> "Parse_string"

let as_lam (x:T.lam 'a)
  : lam 'a
  = let i =
      match fst x with
      | None -> A.(with_dummy_range (to_ident' "_"))
      | Some i -> i
    in
    i, snd x

let rec typ_of_parser (p:T.parser)
  : ML typ
  = let rec dtyp_of_parser (p:T.parser)
      : ML dtyp
      = match p.p_parser with
        | T.Parse_app hd args ->
          dtyp_of_app hd args

        | T.Parse_weaken_left p _
        | T.Parse_weaken_right p _
        | T.Parse_with_comment p _ ->
          dtyp_of_parser p

        | _ ->
          failwith
            (Printf.sprintf "Expected a named type, got %s"
              (T.print_parser "" p))
    in
    match p.p_parser with
    | T.Parse_impos ->
      T_false

    | T.Parse_app _ _ ->
      T_denoted (dtyp_of_parser p)

    | T.Parse_pair _ p q ->
      T_pair (typ_of_parser p) (typ_of_parser q)

    | T.Parse_with_comment p c ->
      T_with_comment (typ_of_parser p) c

    | T.Parse_nlist n p ->
      T_nlist n (typ_of_parser p)

    | T.Parse_t_at_most n p ->
      T_at_most n (typ_of_parser p)

    | T.Parse_t_exact n p ->
      T_exact n (typ_of_parser p)

    | T.Parse_if_else e p1 p2 ->
      T_if_else e (typ_of_parser p1) (typ_of_parser p2)

    | T.Parse_dep_pair _ p k ->
      let i, k = as_lam k in
      T_dep_pair (dtyp_of_parser p)
                 (i, typ_of_parser k)

    | T.Parse_dep_pair_with_refinement _ p r k ->
      let i, r = as_lam r in
      let j, k = as_lam k in
      T_dep_pair_with_refinement (dtyp_of_parser p) (i, r) (j, typ_of_parser k)

    | T.Parse_dep_pair_with_action p a k ->
      let a = as_lam a in
      let (i, k) = as_lam k in
      let r = as_lam (None, T.mk_expr (T.Constant (A.Bool true))) in
      T_dep_pair_with_refinement_and_action (dtyp_of_parser p) r (i, typ_of_parser k) a

    | T.Parse_dep_pair_with_refinement_and_action _ p r a k ->
      let a = as_lam a in
      let (i, k) = as_lam k in
      let r = as_lam r in
      T_dep_pair_with_refinement_and_action (dtyp_of_parser p) r (i, typ_of_parser k) a

    | T.Parse_with_action _ p a ->
      T_with_action (typ_of_parser p) a

    | T.Parse_with_dep_action _ p a ->
      let a = as_lam a in
      T_with_dep_action (dtyp_of_parser p) a

    | T.Parse_string p z ->
      T_string (dtyp_of_parser p) z

    | T.Parse_refinement _ p f ->
      T_refine (dtyp_of_parser p) (as_lam f)

    | T.Parse_refinement_with_action _ _ _ _ ->
      failwith "Not yet implemented"

    | T.Parse_weaken_left p _
    | T.Parse_weaken_right p _ ->
      typ_of_parser p

    | T.Parse_map _ _
    | T.Parse_return _ -> failwith "Unnecessary"

let translate_decls (ds:T.decls)
  : ML (list decl)
  = List.map
      (function
        | (T.Type_decl td, _) ->
          Inr (td.decl_name, typ_of_parser td.decl_parser)

        | d ->
          Inl d)
      ds

let print_ityp (i:itype) =
  match i with
  | UInt8 -> "UInt8"
  | UInt16 -> "UInt16"
  | UInt32 -> "UInt32"
  | UInt64 -> "UInt64"

let print_ident (mname:string) (i:A.ident) =
  T.print_maybe_qualified_ident mname i

let print_dtyp (mname:string) (dt:dtyp) =
  match dt with
  | DT_IType i ->
    Printf.sprintf "(DT_IType %s)" (print_ityp i)

  | DT_App hd args ->
    Printf.sprintf "(DT_App %s %s)"
      (print_ident mname hd)
      (List.map (T.print_expr mname) args |> String.concat " ")

let print_lam (p:'a -> ML string) (x:lam 'a) =
  Printf.sprintf "(fun %s -> %s)"
    (fst x).v.name
    (p (snd x))

let rec print_typ (mname:string) (t:typ)
  : ML string
  = match t with
    | T_false ->
      "T_false"

    | T_denoted dt ->
      print_dtyp mname dt

    | T_pair t1 t2 ->
      Printf.sprintf "(T_pair %s %s)"
                     (print_typ mname t1)
                     (print_typ mname t2)

    | T_dep_pair t k ->
      Printf.sprintf "(T_dep_pair %s %s)"
                     (print_dtyp mname t)
                     (print_lam (print_typ mname) k)

    | T_refine d r ->
      Printf.sprintf "(T_refine %s %s)"
                     (print_dtyp mname d)
                     (print_lam (T.print_expr mname) r)


    | T_dep_pair_with_refinement d r k ->
      Printf.sprintf "(T_dep_pair_with_refinement %s %s %s)"
                     (print_dtyp mname d)
                     (print_lam (T.print_expr mname) r)
                     (print_lam (print_typ mname) k)

    | T_dep_pair_with_refinement_and_action d r k a ->
      Printf.sprintf "(T_dep_pair_with_refinement_and_action %s %s %s %s)"
                     (print_dtyp mname d)
                     (print_lam (T.print_expr mname) r)
                     (print_lam (print_typ mname) k)
                     (print_lam (T.print_action mname) a)

    | T_if_else e t1 t2 ->
      Printf.sprintf "(T_if_else %s %s %s)"
                     (T.print_expr mname e)
                     (print_typ mname t1)
                     (print_typ mname t2)

    | T_with_action p a ->
      Printf.sprintf "(T_with_action %s %s)"
                     (print_typ mname p)
                     (T.print_action mname a)

    | T_with_dep_action d a ->
      Printf.sprintf "(T_with_dep_action %s %s)"
                     (print_dtyp mname d)
                     (print_lam (T.print_action mname) a)

    | T_with_comment t c ->
      Printf.sprintf "(T_with_comment %s [%s])"
                     (print_typ mname t)
                     (List.map (Printf.sprintf "\"%s\"") c |> String.concat "; ")

    | T_nlist n t ->
      Printf.sprintf "(T_nlist %s %s)"
                     (T.print_expr mname n)
                     (print_typ mname t)

    | T_at_most n t ->
      Printf.sprintf "(T_at_most %s %s)"
                     (T.print_expr mname n)
                     (print_typ mname t)

    | T_exact n t ->
      Printf.sprintf "(T_exact %s %s)"
                     (T.print_expr mname n)
                     (print_typ mname t)

    | T_string d z ->
      Printf.sprintf "(T_string %s %s)"
                     (print_dtyp mname d)
                     (T.print_expr mname z)

let print_param mname (p:T.param) =
  Printf.sprintf "(%s:%s)"
    (fst p).v.name
    (T.print_typ mname (snd p))

let print_typedef_name mname (n:T.typedef_name) =
  Printf.sprintf "%s %s"
    (n.td_name.v.name)
    (List.map (print_param mname) n.td_params |> String.concat " ")

let print_type_decl mname (td:type_decl) =
  FStar.Printf.sprintf
    "[@@specialize]\n\
     let %s = %s\n"
      (print_typedef_name mname (fst td))
      (print_typ mname (snd td))

let print_decl mname d =
  match d with
  | Inl d -> T.print_decls mname [d]
  | Inr td -> print_type_decl mname td

let print_decls mname tds =
  List.map (print_decl mname) tds |>
  String.concat "\n\n"

let print_validator (td:type_decl) =
  FStar.Printf.sprintf
    "[@@T.postprocess_for_extraction_with specialize_tac]\n\
     let validate_%s = as_validator %s\n"
      (fst td).td_name.v.name
      (fst td).td_name.v.name

let print_validators mname tds =
  List.collect (function Inl _ -> [] | Inr x -> [print_validator x]) tds |>
  String.concat "\n\n"

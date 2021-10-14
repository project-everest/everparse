(*
   Copyright 2021 Microsoft Research

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
open FStar.List.Tot
module A = Ast
module T = Target
module H = Hashtable

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

noeq
type inv =
  | Inv_true : inv
  | Inv_conj : inv -> inv -> inv
  | Inv_ptr  : A.ident -> inv
  | Inv_name : A.ident -> list expr -> inv

noeq
type eloc =
  | Eloc_none  : eloc
  | Eloc_union : eloc -> eloc -> eloc
  | Eloc_ptr   : A.ident -> eloc
  | Eloc_name  : A.ident -> list expr -> eloc

noeq
type on_success =
  | On_success : bool -> on_success
  | On_success_named : A.ident -> list expr -> on_success
  | On_success_union : on_success -> on_success -> on_success

let inv_eloc = inv & eloc & on_success
let inv_eloc_nil = Inv_true, Eloc_none, On_success false
let inv_eloc_union (i, e, b) (i', e', b') = Inv_conj i i', Eloc_union e e', On_success_union b b'
let inv_eloc_name hd args = Inv_name hd args, Eloc_name hd args, On_success_named hd args

noeq
type type_decl = {
  name : T.typedef_name;
  typ : typ;
  kind : T.parser_kind;
  inv_eloc : inv_eloc;
  allow_reading: bool
}
let decl = either T.decl type_decl
let env = H.t A.ident' type_decl
let create_env (_:unit) : ML env = H.create 100

let rec free_vars_of_expr (e:T.expr)
  : ML (list A.ident)
  = let open T in
    match fst e with
    | Constant _ -> []
    | Identifier i -> [i]
    | App _ args -> List.collect free_vars_of_expr args
    | Record _ args -> List.collect (fun (_, e) -> free_vars_of_expr e) args

let rec free_vars_of_inv (i:inv)
  : ML (list A.ident)
  = match i with
    | Inv_true -> []
    | Inv_conj i j -> free_vars_of_inv i @ free_vars_of_inv j
    | Inv_ptr x -> [x]
    | Inv_name _ args -> List.collect free_vars_of_expr args

let rec free_vars_of_eloc (e:eloc)
  : ML (list A.ident)
  = match e with
    | Eloc_none -> []
    | Eloc_union i j -> free_vars_of_eloc i @ free_vars_of_eloc j
    | Eloc_ptr x -> [x]
    | Eloc_name _ args -> List.collect free_vars_of_expr args

let free_vars_of_inv_eloc (i:inv_eloc) =
  let i, j, _ = i in
  free_vars_of_inv i @ free_vars_of_eloc j

let filter_args_for_inv (args:list expr)
                        (td:type_decl)
  : ML (list expr)
  = let fvs = free_vars_of_inv_eloc td.inv_eloc in
    let args =
      List.map2
        (fun (b, _) a ->
          if Some? (List.tryFind (fun j -> A.ident_name b = A.ident_name j) fvs)
          then [a]
          else [])
        td.name.td_params
        args
    in
    List.flatten args



let itype_of_ident (hd:A.ident)
  : option itype
  = match hd.v.name with
    | "UINT8" -> Some UInt8
    | "UINT16" -> Some UInt16
    | "UINT32" -> Some UInt32
    | "UINT64" -> Some UInt64
    | _ -> None

let dtyp_of_app (hd:A.ident) (args:list T.index)
  : ML dtyp
  = match itype_of_ident hd, args with
    | Some i, [] ->
      DT_IType i

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

let rec inv_eloc_of_action (a:T.action)
  : ML inv_eloc
  = let open T in
    let of_atomic_action (a:T.atomic_action)
      : ML inv_eloc
      = match a with
        | Action_return _
        | Action_abort
        | Action_field_pos -> inv_eloc_nil
        | Action_field_ptr -> Inv_true, Eloc_none, On_success true
        | Action_deref x -> Inv_ptr x, Eloc_none, On_success false
        | Action_assignment x _ -> Inv_ptr x, Eloc_ptr x, On_success false
        | Action_call _ _ -> failwith "Not yet handled (Action_call)"
    in
    match a with
    | Atomic_action aa -> of_atomic_action aa
    | Action_seq hd tl
    | Action_let _ hd tl ->
      inv_eloc_union (of_atomic_action hd) (inv_eloc_of_action tl)
    | Action_ite _ a0 a1 ->
      inv_eloc_union (inv_eloc_of_action a0) (inv_eloc_of_action a1)

let rec inv_eloc_of_parser (en:env) (p:T.parser)
  : ML inv_eloc
  = let inv_eloc_of_parser = inv_eloc_of_parser en in
    match p.p_parser with
    | T.Parse_impos ->
      inv_eloc_nil

    | T.Parse_app hd args ->
      let dt = dtyp_of_app hd args in
      begin
      match dt with
      | DT_IType _ ->
        inv_eloc_nil
      | DT_App hd args ->
        let td =
          match H.try_find en hd.v with
          | Some td -> td
          | _ -> failwith (Printf.sprintf "Type decl not found for %s" (A.ident_to_string hd))
        in
        inv_eloc_name hd (filter_args_for_inv args td)
      end

    | T.Parse_if_else _ p q
    | T.Parse_pair _ p q
    | T.Parse_dep_pair _ p (_, q)
    | T.Parse_dep_pair_with_refinement _ p _ (_, q) ->
      inv_eloc_union (inv_eloc_of_parser p) (inv_eloc_of_parser q)

    | T.Parse_weaken_left p _
    | T.Parse_weaken_right p _
    | T.Parse_refinement _ p _
    | T.Parse_with_comment p _
    | T.Parse_nlist _ p
    | T.Parse_t_at_most _ p
    | T.Parse_t_exact _ p ->
      inv_eloc_of_parser p

    | T.Parse_dep_pair_with_action p (_, a) (_, q)
    | T.Parse_dep_pair_with_refinement_and_action _ p _ (_, a) (_, q) ->
      inv_eloc_union (inv_eloc_of_parser p)
                     (inv_eloc_union (inv_eloc_of_action a) (inv_eloc_of_parser q))

    | T.Parse_with_action _ p a
    | T.Parse_with_dep_action _ p (_, a) ->
      inv_eloc_union (inv_eloc_of_parser p) (inv_eloc_of_action a)

    | T.Parse_string p _ ->
      inv_eloc_nil

    | T.Parse_refinement_with_action _ _ _ _ ->
      failwith "Not yet implemented"

    | T.Parse_map _ _
    | T.Parse_return _ -> failwith "Unnecessary"

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

let rec allow_reading_of_typ (en:env) (t:typ)
  : ML bool
  =
  match t with
  | T_with_comment t _ ->
    allow_reading_of_typ en t

  | T_denoted dt ->
    begin
    match dt with
    | DT_IType _ -> true
    | DT_App hd _ ->
      match H.try_find en hd.v with
      | None -> failwith "type not found"
      | Some td -> td.allow_reading
    end

  | _ -> false

let translate_decls (en:env) (ds:T.decls)
  : ML (list decl)
  = List.map
        (fun d ->
          match d with
          | (T.Type_decl td, _) ->
            let t = typ_of_parser td.decl_parser in
            let ar = allow_reading_of_typ en t in
            let td =
              { name = td.decl_name;
                typ = typ_of_parser td.decl_parser;
                kind = td.decl_parser.p_kind;
                inv_eloc = inv_eloc_of_parser en td.decl_parser;
                allow_reading = ar
                }
            in
            H.insert en td.name.td_name.v td;
            Inr td
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
    Printf.sprintf "(dtyp_%s %s)"
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
      Printf.sprintf "(T_denoted %s)"
                     (print_dtyp mname dt)

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
    "[@@specialize; noextract_to \"Kremlin\"]\n\
     noextract\n\
     let def_%s = %s\n"
      (print_typedef_name mname td.name)
      (print_typ mname td.typ)

let print_args mname (es:list expr) =
    List.map (T.print_expr mname) es |> String.concat " "

let rec print_inv mname (i:inv)
  : ML string
  = match i with
    | Inv_true -> "A.true_inv"
    | Inv_conj i j -> Printf.sprintf "(A.conj_inv %s %s)" (print_inv mname i) (print_inv mname j)
    | Inv_ptr x -> Printf.sprintf "(A.ptr_inv %s)" (print_ident mname x)
    | Inv_name hd args -> Printf.sprintf "(inv_%s %s)" (print_ident mname hd) (print_args mname args)

let rec print_eloc mname (e:eloc)
  : ML string
  = match e with
    | Eloc_none -> "A.eloc_none"
    | Eloc_union i j -> Printf.sprintf "(A.eloc_union %s %s)" (print_eloc mname i) (print_eloc mname j)
    | Eloc_ptr x -> Printf.sprintf "(A.ptr_loc %s)" (print_ident mname x)
    | Eloc_name hd args -> Printf.sprintf "(eloc_%s %s)" (print_ident mname hd) (print_args mname args)

let rec print_on_sucess mname (b:on_success)
  : ML string
  = match b with
    | On_success b -> Printf.sprintf "%b" b
    | On_success_union b0 b1 -> Printf.sprintf "(%s || %s)" (print_on_sucess mname b0) (print_on_sucess mname b1)
    | On_success_named hd args -> Printf.sprintf "(on_success_%s %s)" (print_ident mname hd) (print_args mname args)

let rec print_param_type mname (t:T.typ)
  : ML string
  = let open T in
    match t with
    | T_app hd false [] ->
      (match itype_of_ident hd with
       | Some i ->
         Printf.sprintf "(PT_Base %s)"
                        (print_ityp i)
       | None ->
         Printf.sprintf "(PT_Typedef %s)"
                        (print_ident mname hd))
    | T_pointer t ->
      Printf.sprintf "(PT_Pointer %s)"
                     (print_param_type mname t)
    | _ ->
      failwith (Printf.sprintf "Unexpected param type: %s" (T.print_typ mname t))

let print_binding mname (td:type_decl)
  : ML string
  = let tdn = td.name in
    let typ = td.typ in
    let k = td.kind in
    let root_name = print_ident mname tdn.td_name in
    let param_types_literal =
         List.map (fun (_, t) -> print_param_type mname t) tdn.td_params |>
         String.concat "; "
    in
    let param_types =
        Printf.sprintf "[@@specialize; noextract_to \"Kremlin\"]\nnoextract\nlet param_types_%s = [%s]\n"
          root_name
          param_types_literal
    in
    let print_binders binders =
        List.map (print_param mname) binders |>
        String.concat " "
    in
    let print_args binders =
        List.map (fun (i, _) -> print_ident mname i) binders |>
        String.concat " "
    in
    let binders = print_binders tdn.td_params in
    let args = print_args tdn.td_params in
    let arg_tuple =
        List.fold_right
          (fun (x, _) out -> Printf.sprintf "(%s, %s)" (print_ident mname x) out)
          tdn.td_params
          "()"
    in
    let validate_binding =
        FStar.Printf.sprintf "[@@T.postprocess_with specialize_tac]\n\
                             let validate_%s %s = as_validator (def_%s %s)\n"
                             root_name
                             binders
                             root_name
                             args
    in
    let type_of_binding =
        let f =
          match tdn.td_params with
          | [] ->
            Printf.sprintf "(as_type def_%s)" root_name
          | _ ->
            Printf.sprintf "(fun %s -> as_type (def_%s %s))"
                           binders
                           root_name
                           args
        in
        Printf.sprintf "[@@noextract_to \"Kremlin\"]\nnoextract\nlet type_%s : arrow param_types_%s Type = coerce (_ by (T.trefl())) %s\n"
                       root_name
                       root_name
                       f
   in
   let pk_of_binding =
     Printf.sprintf "[@@noextract_to \"Kremlin\"]inline_for_extraction noextract\nlet kind_%s = %s\n"
       root_name
       (T.print_kind mname k)
   in
   let parser_of_binding =
       let f =
          match tdn.td_params with
          | [] ->
            Printf.sprintf "(as_parser def_%s)" root_name
          | _ ->
            Printf.sprintf "(fun %s -> as_parser (def_%s %s))"
                           binders
                           root_name
                           args
       in
       Printf.sprintf "[@@noextract_to \"Kremlin\"]noextract let parser_%s : dep_arrow param_types_%s (fun args -> P.parser kind_%s (apply_arrow type_%s args))\n\
                          = coerce (_ by (T.trefl())) %s\n"
                        root_name
                        root_name
                        root_name
                        root_name
                        f
   in
   let print_inv_or_eloc tag ty defn fvs
     : ML (string & string)
     =
     let fv_binders =
         List.filter
           (fun (i, _) ->
             Some? (List.tryFind (fun j -> A.ident_name i = A.ident_name j) fvs))
           tdn.td_params
     in
     let fv_binders_string = print_binders fv_binders in
     let fv_args_string = print_args fv_binders in
     let f =
         match fv_binders with
          | [] ->
            defn
          | _ ->
            Printf.sprintf "(fun %s -> %s)"
                           fv_binders_string
                           defn
     in
     let s0 = Printf.sprintf "[@@noextract_to \"Kremlin\"]noextract let %s_%s = %s\n" tag root_name f in
     let body =
       let body =
         Printf.sprintf "%s_%s %s" tag root_name fv_args_string
       in
       match tdn.td_params with
       | [] -> body
       | _ -> Printf.sprintf "(fun %s -> %s)" binders body
     in
     let s1 = Printf.sprintf "[@@noextract_to \"Kremlin\"]noextract let %s_arrow_%s : arrow param_types_%s %s = coerce (_ by (T.trefl())) %s\n"
                    tag
                    root_name
                    root_name
                    ty
                    body
     in
     s0 ^ s1, fv_args_string
   in
   let inv_eloc_of_binding, fv_args =
     let inv, eloc, _ = td.inv_eloc in
     let fvs1 = free_vars_of_inv inv in
     let fvs2 = free_vars_of_eloc eloc in
     let s0, _ = print_inv_or_eloc "inv" "A.slice_inv" (print_inv mname inv) (fvs1@fvs2) in
     let s1, fv_args = print_inv_or_eloc "eloc" "A.eloc" (print_eloc mname eloc) (fvs1@fvs2) in
     s0 ^ s1, fv_args
   in
   let coerce_tac =
     let steps =
       let s =
         ["param_types";
         "kind";
         "type";
         "parser";
         "inv";
         "inv_arrow";
         "eloc";
         "eloc_arrow"]
       in
       let steps =
         List.map (fun s -> Printf.sprintf "`%%%s_%s" s root_name) s |>
         String.concat "; "
       in
       steps
     in
     Printf.sprintf "(coerce_tac [%s])" steps
   in
   let validator_of_binding =
       Printf.sprintf "[@@specialize; noextract_to \"Kremlin\"]\nnoextract\nlet validator_%s \n\
                         : dep_arrow param_types_%s\n\
                             (fun args ->\n\
                               A.validate_with_action_t \n\
                                 (apply_dep_arrow _ _ parser_%s args)\n\
                                 (apply_arrow inv_arrow_%s args)\n\
                                 (apply_arrow eloc_arrow_%s args)\n\
                                 %b)\n\
                          = coerce (_ by %s) validate_%s\n"
                        root_name
                        root_name
                        root_name
                        root_name
                        root_name
                        td.allow_reading
                        coerce_tac
                        root_name
   in
   let binding =
     Printf.sprintf "[@@specialize; noextract_to \"Kremlin\"]\nnoextract\nlet binding_%s \n\
                      : global_binding \n\
                      = mk_global_binding\n\
                           param_types_%s\n\
                           inv_arrow_%s\n\
                           eloc_arrow_%s\n\
                           validator_%s\n\
                           None"
                      root_name
                      root_name
                      root_name
                      root_name
                      root_name
   in
   let dtyp_of_binding =
     Printf.sprintf "[@@specialize; noextract_to \"Kremlin\"]\n\
                     noextract\n\
                     let dtyp_%s %s\n\
                       : dtyp kind_%s false (inv_%s %s) (eloc_%s %s) %b\n\
                       = coerce (_ by (T.trefl())) (DT_App \"%s\" binding_%s (coerce (_ by %s) %s))\n"
                     root_name
                     binders
                     root_name
                     root_name
                     fv_args
                     root_name
                     fv_args
                     td.allow_reading
                     root_name
                     root_name
                     coerce_tac
                     arg_tuple
   in
   String.concat "\n"
     [validate_binding;
      param_types;
      type_of_binding;
      pk_of_binding;
      parser_of_binding;
      inv_eloc_of_binding;
      validator_of_binding;
      binding;
      dtyp_of_binding]

let print_decl mname (d:decl) =
  match d with
  | Inl d ->
    begin
    match fst d with
    | T.Assumption _ -> T.print_assumption mname d
    | T.Definition _ -> T.print_definition mname d
    | _ -> ""
    end
  | Inr td ->
    Printf.sprintf "%s\n%s\n"
      (print_type_decl mname td)
      (print_binding mname td)

let print_decls en mname tds =
  List.map (print_decl mname) tds |>
  String.concat "\n\n"

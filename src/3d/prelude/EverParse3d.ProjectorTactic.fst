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

   Author: G. Martinez
   Modified by: N. Swamy
*)
module EverParse3d.ProjectorTactic

open FStar.List.Tot
open FStar.Tactics

let mkproj (unf:list string) (np:nat) (i:nat) : Tac unit =
  let _ = ignore (repeatn (np+1) intro) in
  let b = nth_binder (-1) in
  let r = t_destruct b in
  // dump "GGG";
  // FIXME: if this is just t_destrcut (nth_binder (-1)), this tactic
  // fails when loaded from another file... ????
  match r with
  | [(cons, arity)] -> begin
    if (i >= arity) then
      fail "bad index";
    let bs = repeatn (arity+1) (fun () -> intro ()) in
    // dump "1";
    rewrite (nth_binder (-1));
    // dump "2";
    norm [iota; delta_only unf];
    // dump "3";
    match List.Tot.nth bs i with
    | None -> fail "impossible, but I should be able to prove it"
    | Some b -> exact b
    end
  | _ ->
    fail "no"

exception NotFound

let subst_map (ss : list (bv * fv)) (r:term) (t : term) : Tac term =
  // dump ("before = " ^ term_to_string t);
  let t = fold_left (fun t (x, fv) -> subst x (mk_e_app (Tv_FVar fv) [r]) t) t ss in
  // dump ("after  = " ^ term_to_string t);
  t

let rec embed_list_string (e : list string) : Tac term =
  match e with
  | [] -> `Nil
  | s::ss ->
    (`(`#(Tv_Const (C_String s))) :: (`#(embed_list_string ss)))

let mk_proj_decl proj_name (tyqn:name) ctorname univs indices (params:list binder) (idx:nat) (fieldty : typ)
                 (unfold_names : list string)
                 (smap : list (bv & fv))
: Tac (sigelt & fv)
=
  let np = List.Tot.length params in
  let ni = List.Tot.length indices in
  let tyfv = pack_fv tyqn in
  let fv = pack_fv (cur_module () @ [proj_name]) in
  let rty : binder = fresh_binder (mk_e_app (pack (Tv_FVar tyfv))
                                   (map binder_to_term (params @ indices)))
  in
  let projty = mk_tot_arr (List.Tot.map (binder_set_qual Q_Implicit) params
                           @ List.Tot.map (binder_set_qual Q_Implicit) indices
                           @ [rty])
                          (subst_map smap (binder_to_term rty) fieldty)
  in
  let lbdef =
    (`(_ by (mkproj (`#(embed_list_string unfold_names))
                        (`#(Tv_Const (C_Int (np+ni))))
                        (`#(Tv_Const (C_Int idx))))))
  in
  let lb = pack_lb ({ lb_fv = fv; lb_us= univs; lb_typ=projty; lb_def = lbdef}) in
  let sv
    : sigelt_view
    = Sg_Let false [lb]
  in
  // dump ("returning : " ^ term_to_string (quote sv));
  (pack_sigelt sv, fv)

#push-options "--fuel 2"
let rec zip #a #b (x:list a) (y:list b { length x == length y })
  : list (a & b)
  = match x, y with
    | [], [] -> []
    | x::xs, y::ys -> (x,y) :: zip xs ys

let mk_projs (tyname:string) (proj_names:list string) : Tac decls =
  let tyqn = explode_qn tyname in
  match lookup_typ (top_env ()) tyqn with
  | None ->
    raise NotFound
  | Some se ->
    match inspect_sigelt se with
    | Sg_Inductive ctorname univs params typ ctors ->
      if (List.Tot.length ctors <> 1) then
        fail "expected a record";
      let indices = fst (collect_arr_bs typ) in
      let [ctor] = ctors in
      let (fields, _) = collect_arr_bs (snd ctor) in
      if (List.Tot.length proj_names <> List.Tot.length fields)
      then fail "Not enough record names";
      let field_projectors = zip fields proj_names in
      let (decls, _, _, _) =
        fold_left (fun (decls, smap, unfold_names, idx) (field, proj_name) ->
                     let (d, fv) = mk_proj_decl proj_name tyqn ctorname univs indices params idx (type_of_binder field) unfold_names smap in
                     (d::decls,
                      (bv_of_binder field,fv)::smap,
                      (implode_qn (inspect_fv fv))::unfold_names,
                      idx+1))
                  ([], [], [], 0)
                  field_projectors
      in
      List.Tot.rev decls
    | _ ->
      fail "not an inductive"
#pop-options

// #set-options "--__temp_no_proj Proj"

// noeq
// type monad (rr : Type) (m:Type0 -> Type0) : Type = {
//   ret    : #a:_ -> a -> m a;
//   bind   : #a:_ -> #b:_ -> m a -> (a -> m b) -> m b;
//   assoc  : #a:_ -> #b:_ -> #c:_ -> x:m a -> f:(a -> m b) -> g:(b -> m c) ->
//                          squash (bind (bind x f) g == bind x (fun y -> bind (f y) g));
//   id1    : #a:_ -> #b:_ -> x:a -> f:(a -> m b) ->
//            squash (bind (ret x) f == f x);
//   id2    : #a:_ -> c:m a ->
//            squash (bind c ret == c);
// }

// #set-options (* Look mom, *)"--no_smt" (* ! *)

// %splice[proj_0; proj_1; proj_2; proj_3; proj_4] (mk_projs (`%monad))

// #set-options "--print_bound_var_types --print_implicits"

// type test : int -> Type =
//  | MakeThisGuy :
//   i:int ->
//   x:int ->
//   test i

// %splice[] (mk_projs (`%test))

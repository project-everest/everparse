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

   Authors: N. Swamy, ...
*)
module EverParse3d.Interpreter
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module A = EverParse3d.Actions.All
module P = EverParse3d.Prelude
module T = FStar.Tactics
module CP = EverParse3d.CopyBuffer
open FStar.List.Tot

(* This module defines a strongly typed abstract syntax for an
   intermediate representation of 3D programs. This is the type `typ`.

   The main idea of this module is to give `typ`s a threefold
   denotation:

     1. Type denotation: `as_type` interprets a `typ` as an F* type

     2. Parser denotation: `as_parser` interprets a `t:typ` as a parser
        of values of the type denotation of `t`.

     3. Validate-with-action denotation: `as_validator` inteprets a
        `t:typ` as a low-level validator corresponding to the parser
        denotation of `t`.

   The 3rd denotation, validate-with-action, is the main operational
   denotation. That is, given a 3D program `t:typ` we can interpret it
   as validator to check that an input array of bytes conforms to the
   format specified by `t`. But, what we want ultimately is a C
   program for a `t`-validator.

   To achieve this, for any given concrete `t`, we partially evaluate
   this interpreter to get an EverParse validator specialized to `t`
   which can be extracted by F*/KaRaMeL as usual---this partial
   evaluation of an interpreter to a compiler producing a C program
   for t-validator is an instance of the 1st Futamura projection.
 *)

(** You can see the basic idea of the whole stack working at first on
    a very simple class of types---just the primitive types *)

(* Our first order of business to scale this up to 3D is to set up
   definitions for type contexts.

   A 3D program is a sequence of top-level definitions, where a given
   definition may reference terms defined previously. To model this,
   we'll given a denotation of programs in a _context_, where the
   context provides denotations for all the names defined previously
   which are in scope.
*)

(* Now, we can define the type of an environment *)
module T = FStar.Tactics

let dtyp_as_eqtype_lemma #nz #wk (#pk:P.parser_kind nz wk) #i #disj #l
                         (d:dtyp pk true i disj l)
  : Lemma
    (ensures hasEq (dtyp_as_type d))
    [SMTPat (hasEq (dtyp_as_type d))]
  = match d with
    | DT_IType i -> 
      ()

    | DT_App _ _ _ _ _ b _ ->
      let (| _, _ |) = get_leaf_reader b in ()

  
let dtyp_as_parser #nz #wk (#pk:P.parser_kind nz wk) #hr #i #disj #l
                   (d:dtyp pk hr i disj l)
  : P.parser pk (dtyp_as_type d)
  = match d returns Tot (P.parser pk (dtyp_as_type d)) with
    | DT_IType i -> 
      itype_as_parser i

    | DT_App _ _ _ _ _ b _ ->
      parser_of_binding b
 
let dtyp_as_serializer #nz #wk (#pk:P.parser_kind nz wk) #hr #i #disj #l
                   (d:dtyp pk hr i disj l)
  : P.serializer (dtyp_as_parser d)
  = match d returns Tot (P.serializer (dtyp_as_parser d)) with
    | DT_IType i -> 
      itype_as_serializer i

    | DT_App _ _ _ _ _ b _ ->
      serializer_of_binding b

[@@specialize]
let dtyp_as_validator #nz #wk (#pk:P.parser_kind nz wk)
                      (#hr:_)
                      (#[@@@erasable] i:inv_index)
                      (#[@@@erasable] disj:disj_index)
                      (#[@@@erasable] l:loc_index)
                      (d:dtyp pk hr i disj l)
  : A.validate_with_action_t #nz #wk #pk #(dtyp_as_type d)
        (dtyp_as_parser d)
        (interp_inv i)
        (interp_disj disj)
        (interp_loc l)
        hr
  = match d 
    returns 
      A.validate_with_action_t #nz #wk #pk #(dtyp_as_type d)
            (dtyp_as_parser d)
            (interp_inv i)
            (interp_disj disj)
            (interp_loc l)
            hr 
    with
    | DT_IType i -> 
      itype_as_validator i

    | DT_App _ _ _ _ _ b _ ->
      // assert_norm (dtyp_as_type (DT_App_Alt ps b args) == (type_of_binding_alt (apply_arrow b args)));
      // assert_norm (dtyp_as_parser (DT_App_Alt ps b args) == parser_of_binding_alt (apply_arrow b args));
      validator_of_binding b


[@@specialize]
let dtyp_as_leaf_reader #nz (#pk:P.parser_kind nz P.WeakKindStrongPrefix)
                        (#[@@@erasable] i:inv_index)
                        (#[@@@erasable] disj:disj_index)
                        (#[@@@erasable] l:loc_index)
                        (d:dtyp pk true i disj l)
  : A.leaf_reader (dtyp_as_parser d)
  = match d with
    | DT_IType i -> 
      itype_as_leaf_reader i

    | DT_App _ _ _ _ _ b _ -> 
      let (| _, lr |) = get_leaf_reader b in
      lr

(** Actions *)

(* Denotation of atomic_actions as A.action *)
[@@specialize]
let atomic_action_as_action
   (#i #d #l #b #t:_)
   (a:atomic_action i d l b t)
  : Tot (A.action (interp_inv i) (interp_disj d) (interp_loc l) b t)
  = match a with
    | Action_return x ->
      A.action_return x
    | Action_abort ->
      A.action_abort
    | Action_field_pos_64 ->
      A.action_field_pos_64
    | Action_field_pos_32 sq  ->
      A.action_field_pos_32 sq
    | Action_field_ptr sq ->
      A.action_field_ptr sq
    | Action_field_ptr_after sq sz write_to ->
      A.action_field_ptr_after sq sz write_to
    | Action_field_ptr_after_with_setter sq sz write_to ->
      A.action_field_ptr_after_with_setter sq sz write_to
    | Action_deref x ->
      A.action_deref x
    | Action_assignment x rhs ->
      A.action_assignment x rhs
    | Action_call c ->
      c
    | Action_probe_then_validate #nz #wk #k #_hr #inv #l dt src len dest probe ->
      A.index_equations();
      let v = dtyp_as_validator dt in
      A.probe_then_validate v src len dest probe

(* Denotation of action as A.action *)
[@@specialize]
let rec action_as_action
   (#i #d #l #b #t:_)
   (a:action i d l b t)
  : Tot (A.action (interp_inv i) (interp_disj d) (interp_loc l) b t)
    (decreases a)
  = A.index_equations();
    match a with
    | Atomic_action a ->
      atomic_action_as_action a

    | Action_seq hd tl ->
      let a1 = atomic_action_as_action hd in
      let tl = action_as_action tl in
      A.action_seq a1 tl

    | Action_ite hd t e ->
      let then_ (x:squash hd) = action_as_action (t x) in
      let else_ (x:squash (not hd)) = action_as_action (e x) in
      A.action_ite hd then_ else_

    | Action_let hd k ->
      let head = atomic_action_as_action hd in
      let k x = action_as_action (k x) in
      A.action_bind "hd" head k

    | Action_act #i0 #l0 #b0 a ->
      A.action_weaken (A.action_seq (action_as_action a) (A.action_return true))
                      #(interp_inv i0) 
                      #_ 
                      #(interp_loc l0)

[@@specialize]
let t_probe_then_validate
      (fieldname:string)
      (probe:CP.probe_fn)
      (len:U64.t)
      (dest:CP.copy_buffer_t)
      (#nz #wk:_) (#pk:P.parser_kind nz wk)
      (#has_reader #i #disj:_)
      (#l:_)
      (td:dtyp pk has_reader i disj l)
 : typ (parser_kind_of_itype UInt64)
       (join_inv i (NonTrivial (A.copy_buffer_inv dest)))
       (join_disj disj (disjoint (NonTrivial (A.copy_buffer_loc dest)) l))
       (join_loc l (NonTrivial (A.copy_buffer_loc dest)))
       false
 = T_with_dep_action fieldname
     (DT_IType UInt64)
     (fun src ->
        Atomic_action (Action_probe_then_validate td src len dest probe))
    
(* Type, parser and serializer denotation of `typ` *)
let rec denote
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #d #b
          (t:typ pk l i d b)
  : Tot (t:Type0 & p:P.parser pk t & P.serializer p)
        (decreases t)
  = match t returns Tot (t:Type0 & p:P.parser pk t & P.serializer p) with
    | T_false _ ->
      //assert_norm (as_type g T_false == False);
      (| False, P.parse_impos(), P.serialize_impos() |)

    | T_denoted _ d ->
      (| dtyp_as_type d, dtyp_as_parser d, dtyp_as_serializer d |)

    | T_pair _ t1 t2 ->
      //assert_norm (as_type g (T_pair t1 t2) == as_type g t1 * as_type g t2);
      (| (denote t1)._1 & (denote t2)._1,
         P.parse_pair (denote t1)._2 (denote t2)._2,
         P.serialize_pair _ _ (denote t1)._3 (denote t2)._3 |)

    | T_dep_pair _ i t
    | T_dep_pair_with_action _ i t _ ->
      //assert_norm (as_type g (T_dep_pair i t) == x:itype_as_type i & as_type g (t x));
      let pi = dtyp_as_parser i in
      (| x:dtyp_as_type i & (denote (t x))._1,
         P.parse_dep_pair pi (fun (x:dtyp_as_type i) -> (denote (t x))._2),
         P.serialize_dep_pair _ _ (dtyp_as_serializer i) (fun x -> (denote (t x))._3) |)

    | T_refine _ base refinement
    | T_refine_with_action _ base refinement _ ->
      //assert_norm (as_type g (T_refine base refinement) == P.refine (itype_as_type base) refinement);
      (| P.refine (dtyp_as_type base) refinement,
         P.parse_filter (dtyp_as_parser base) refinement,
         P.serialize_filter _ _ (dtyp_as_serializer base) |)

    | T_dep_pair_with_refinement _ base refinement k ->
      (| x:P.refine (dtyp_as_type base) refinement & (denote (k x))._1,
        P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> (denote (k x))._2)),
         P.serialize_dep_pair _ _ (P.serialize_filter _ _ (dtyp_as_serializer base)) (fun x -> (denote (k x))._3) |)

    | T_dep_pair_with_refinement_and_action _ base refinement k _ ->
      (| x:P.refine (dtyp_as_type base) refinement & (denote (k x))._1,
         P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> (denote (k x))._2)),
         P.serialize_dep_pair _ _ (P.serialize_filter _ _ (dtyp_as_serializer base)) (fun x -> (denote (k x))._3) |)

    | T_if_else #nz1 #wk1 #pk1 #l1 #i1 #d1 #b1 #nz2 #wk2 #pk2 b t0 t1 ->
      let p0 (_:squash b) = P.parse_weaken_right (denote (t0 ()))._2 pk2 in
      let p1 (_:squash (not b)) = P.parse_weaken_left (denote (t1 ()))._2 pk1 in
      let s0 (_:squash b) : P.serializer (p0 ()) = P.serialize_weaken_right (denote (t0 ()))._2 pk2 (denote (t0 ()))._3 in
      let s1 (_:squash (not b)) : P.serializer (p1 ()) = P.serialize_weaken_left (denote (t1 ()))._2 pk1 (denote (t1 ()))._3 in
      (| (if b then (denote (t0 ()))._1 else (denote (t1 ()))._1),
         P.parse_ite b p0 p1, P.serialize_ite b p0 p1 s0 s1 |)

    | T_cases b t0 t1 ->
      //assert_norm (as_type g (T_if_else b t0 t1) == P.t_ite b (as_type g t0) (as_type g t1));
      let p0 (_:squash b) = P.parse_weaken_right (denote t0)._2 _ in
      let p1 (_:squash (not b)) = P.parse_weaken_left (denote t1)._2 _ in
      let s0 (_:squash b) : P.serializer (p0 ()) = P.serialize_weaken_right _ _ (denote t0)._3 in
      let s1 (_:squash (not b)) : P.serializer (p1 ()) = P.serialize_weaken_left _ _ (denote t1)._3 in
      (| (if b then (denote t0)._1 else (denote t1)._1), P.parse_ite b p0 p1, P.serialize_ite b p0 p1 s0 s1 |)

    | T_with_action _ t a ->
      //assert_norm (as_type g (T_with_action t a) == as_type g t);
      denote t

    | T_with_dep_action _ i a ->
      //assert_norm (as_type g (T_with_dep_action i a) == itype_as_type i);
      (| dtyp_as_type i, dtyp_as_parser i, dtyp_as_serializer i |)

    | T_with_comment _ t c ->
      //assert_norm (as_type g (T_with_comment t c) == as_type g t);
      denote t

    | T_nlist _ n t ->
      (| P.nlist n (denote t)._1 (denote t)._3, P.parse_nlist n (denote t)._3, P.serialize_nlist n (denote t)._3 |)

    | T_at_most _ n t ->
      (| P.t_at_most n _ (denote t)._3, P.parse_t_at_most n (denote t)._3, P.serialize_t_at_most n (denote t)._3 |)

    | T_exact _ n t ->
      (| P.t_exact n _ (denote t)._3, P.parse_t_exact n (denote t)._3, P.serialize_t_exact n (denote t)._3 |)

    | T_string _ elt_t terminator ->
      (| P.cstring (dtyp_as_type elt_t) terminator, P.parse_string (dtyp_as_parser elt_t) terminator, P.serialize_string (dtyp_as_serializer elt_t) terminator |)

(* Type denotation of `typ` *)
let as_type
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #d #b
          (t:typ pk l i d b)
  : Tot Type0 =
  (denote t)._1

(* Parser denotation of `typ` *)
let as_parser
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #d #b
          (t:typ pk l i d b)
  : P.parser pk (as_type t) =
  (denote t)._2

(* Serializer denotation of `typ` *)
let as_serializer
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #d #b
          (t:typ pk l i d b)
  : Tot (P.serializer (as_parser t)) =
  (denote t)._3

[@@specialize]
let rec as_reader #nz (#pk:P.parser_kind nz P.WeakKindStrongPrefix)
                  (#[@@@erasable] inv:inv_index)
                  (#[@@@erasable] d:disj_index)
                  (#[@@@erasable] loc:loc_index)
                  (t:typ pk inv d loc true)
  : leaf_reader (as_parser t)
  = match t with
    | T_denoted _n dt ->
      assert_norm (as_type (T_denoted _n dt) == dtyp_as_type dt);
      assert_norm (as_parser (T_denoted _n dt) == dtyp_as_parser dt);
      (| (), dtyp_as_leaf_reader dt |)
    | T_with_comment _n t _c ->
      assert_norm (as_type (T_with_comment _n t _c) == as_type t);    
      assert_norm (as_parser (T_with_comment _n t _c) == as_parser t);    
      as_reader t
    | T_false _n ->
      assert_norm (as_type (T_false _n) == False);
      assert_norm (as_parser (T_false _n) == P.parse_impos());
      (| (), A.read_impos |)

(* The main result:
   A validator denotation of `typ`
     related by construction to the parser
     and type denotations
*)
#push-options "--split_queries no --z3rlimit_factor 4 --z3cliopt 'smt.qi.eager_threshold=100'"
#restart-solver
let rec as_validator
          (typename:string)
          #nz #wk (#pk:P.parser_kind nz wk)
          (#[@@@erasable] inv:inv_index)
          (#[@@@erasable] disj:disj_index)
          (#[@@@erasable] loc:loc_index)
          #b
          (t:typ pk inv disj loc b)
  : Tot (A.validate_with_action_t #nz #wk #pk #(as_type t)
            (as_parser t)
            (interp_inv inv)
            (interp_disj disj)
            (interp_loc loc)
            b)
        (decreases t)
  = A.index_equations();
    match t
    returns Tot (
      A.validate_with_action_t #nz #wk #pk #(as_type t)
            (as_parser t)
            (interp_inv inv)
            (interp_disj disj)
            (interp_loc loc)
            b
    )
    with
    | T_false fn ->
      A.validate_with_error_handler typename fn (A.validate_impos())

    | T_denoted fn td ->
      assert_norm (as_type (T_denoted fn td) == dtyp_as_type td);
      assert_norm (as_parser (T_denoted fn td) == dtyp_as_parser td);
      A.validate_with_error_handler typename fn (A.validate_eta (dtyp_as_validator td))

    | T_pair fn t1 t2 ->
      assert_norm (as_type (T_pair fn t1 t2) == as_type t1 * as_type t2);
      assert_norm (as_parser (T_pair fn t1 t2) == P.parse_pair (as_parser t1) (as_parser t2));
      A.validate_pair fn
          (as_validator typename t1)
          (as_validator typename t2)
    
    | T_dep_pair fn i t ->
      assert_norm (as_type (T_dep_pair fn i t) == x:dtyp_as_type i & as_type (t x));
      assert_norm (as_parser (T_dep_pair fn i t) ==
                   P.parse_dep_pair (dtyp_as_parser i) (fun (x:dtyp_as_type i) -> as_parser (t x)));
      A.validate_weaken_inv_loc (interp_inv inv) _ (interp_loc loc)
          (A.validate_dep_pair fn
              (A.validate_with_error_handler typename fn (dtyp_as_validator i))
              (dtyp_as_leaf_reader i)
              (fun x -> as_validator typename (t x)))

    | T_refine fn t f ->
      assert_norm (as_type (T_refine fn t f) == P.refine (dtyp_as_type t) f);
      assert_norm (as_parser (T_refine fn t f) == P.parse_filter (dtyp_as_parser t) f);
      A.validate_with_error_handler typename fn      
        (A.validate_filter fn
          (dtyp_as_validator t)
          (dtyp_as_leaf_reader t)
          f "reading field_value" "checking constraint")

    | T_refine_with_action fn t f a ->
      assert_norm (as_type (T_refine_with_action fn t f a) == P.refine (dtyp_as_type t) f);
      assert_norm (as_parser (T_refine_with_action fn t f a) == P.parse_filter (dtyp_as_parser t) f);
      assert_norm (as_parser (T_refine fn t f) == P.parse_filter (dtyp_as_parser t) f);      
      A.validate_with_error_handler typename fn            
        (A.validate_filter_with_action fn
          (dtyp_as_validator t)
          (dtyp_as_leaf_reader t)
          f "reading field_value" "checking constraint"
          (fun x -> action_as_action (a x)))

    | T_dep_pair_with_refinement fn base refinement k ->
      assert_norm (as_type (T_dep_pair_with_refinement fn base refinement k) ==
                        x:P.refine (dtyp_as_type base) refinement & as_type (k x));
      assert_norm (as_parser (T_dep_pair_with_refinement fn base refinement k) ==
                        P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x))));
      A.validate_with_error_handler typename fn                              
        (A.validate_weaken_inv_loc _ _ _ (
          A.validate_dep_pair_with_refinement false fn
            (dtyp_as_validator base)
            (dtyp_as_leaf_reader base)
            refinement
            (fun x -> as_validator typename (k x))))

    | T_dep_pair_with_action fn base t act ->
      assert_norm (as_type (T_dep_pair_with_action fn base t act) ==
                        x:dtyp_as_type base & as_type (t x));
      assert_norm (as_parser (T_dep_pair_with_action fn base t act) ==
                        P.(dtyp_as_parser base `parse_dep_pair` (fun x -> as_parser (t x))));
      A.validate_with_error_handler typename fn                              
        (A.validate_weaken_inv_loc _ _ _ (
          A.validate_dep_pair_with_action 
            (dtyp_as_validator base)
            (dtyp_as_leaf_reader base)
            (fun x -> action_as_action (act x))
            (fun x -> as_validator typename (t x))))

    | T_dep_pair_with_refinement_and_action fn base refinement k act ->
      assert_norm (as_type (T_dep_pair_with_refinement_and_action fn base refinement k act) ==
                        x:P.refine (dtyp_as_type base) refinement & as_type (k x));
      assert_norm (as_parser (T_dep_pair_with_refinement_and_action fn base refinement k act) ==
                        P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x))));
      A.validate_weaken_inv_loc _ _ _ (
          A.validate_dep_pair_with_refinement_and_action false fn
            (A.validate_with_error_handler typename fn                              
              (dtyp_as_validator base))
            (dtyp_as_leaf_reader base)
            refinement
            (fun x -> action_as_action (act x))
            (fun x -> as_validator typename (k x)))


    | T_if_else #nz1 #wk1 #pk1 #l1 #i1 #d1 #b1 #nz2 #wk2 #pk2 #l2 #i2 #d2 #b2 b t0 t1 ->
      assert_norm (as_type (T_if_else b t0 t1) == (if b then as_type (t0()) else as_type (t1 ())));
      let p0 (_:squash b) = P.parse_weaken_right (as_parser (t0())) pk2 in
      let p1 (_:squash (not b)) = P.parse_weaken_left (as_parser (t1())) pk1 in
      assert_norm (as_parser (T_if_else b t0 t1) == P.parse_ite b p0 p1);
      let v0 (_:squash b) = 
        A.validate_weaken_right (as_validator typename (t0())) pk2
      in
      let v1 (_:squash (not b)) =
        A.validate_weaken_left (as_validator typename (t1())) pk1
      in
      coerce () (A.validate_ite b p0 v0 p1 v1)

    | T_cases #nz1 #wk1 #pk1 #l1 #i1 #d1 #b1 #nz2 #wk2 #pk2 #l2 #i2 #d2 #b2 b t0 t1 ->
      assert_norm (as_type (T_cases b t0 t1) == P.t_ite b (fun _ -> as_type t0) (fun _ -> as_type t1));
      let p0 (_:squash b) = P.parse_weaken_right (as_parser t0) pk2 in
      let p1 (_:squash (not b)) = P.parse_weaken_left (as_parser t1) pk1 in
      assert_norm (as_parser (T_cases b t0 t1) == P.parse_ite b p0 p1);
      let v0 (_:squash b) = 
        A.validate_weaken_right (as_validator typename t0) pk2
      in
      let v1 (_:squash (not b)) =
        A.validate_weaken_left (as_validator typename t1) pk1
      in
      coerce () (A.validate_ite b p0 v0 p1 v1)
 
    | T_with_action fn t a ->
      assert_norm (as_type (T_with_action fn t a) == as_type t);
      assert_norm (as_parser (T_with_action fn t a) == as_parser t);
      A.validate_with_error_handler typename fn 
        (A.validate_with_success_action fn
          (as_validator typename t)
          (action_as_action a))

    | T_with_dep_action fn i a ->
      assert_norm (as_type (T_with_dep_action fn i a) == dtyp_as_type i);
      assert_norm (as_parser (T_with_dep_action fn i a) == dtyp_as_parser i);
      A.validate_with_error_handler typename fn 
        (A.validate_weaken_inv_loc _ _ _ (
          A.validate_with_dep_action fn
            (dtyp_as_validator i)
            (dtyp_as_leaf_reader i)
            (fun x -> action_as_action (a x))))


    | T_with_comment fn t c ->
      assert_norm (as_type (T_with_comment fn t c) == as_type t);
      assert_norm (as_parser (T_with_comment fn t c) == as_parser t);
      A.validate_with_comment c (as_validator typename t)

    | T_nlist fn n t ->
      assert_norm (as_type (T_nlist fn n t) == P.nlist n (as_type t) (as_serializer t));
      assert_norm (as_parser (T_nlist fn n t) == P.parse_nlist n (as_serializer t));
      A.validate_with_error_handler typename fn 
        (A.validate_nlist n (as_serializer t) (as_validator typename t))

    | T_at_most fn n t ->
      assert_norm (as_type (T_at_most fn n t) == P.t_at_most n (as_type t) (as_serializer t));
      assert_norm (as_parser (T_at_most fn n t) == P.parse_t_at_most n (as_serializer t));
      A.validate_with_error_handler typename fn 
        (A.validate_t_at_most n (as_serializer t) (as_validator typename t))

    | T_exact fn n t ->
      assert_norm (as_type (T_exact fn n t) == P.t_exact n (as_type t) (as_serializer t));
      assert_norm (as_parser (T_exact fn n t) == P.parse_t_exact n (as_serializer t));
      A.validate_with_error_handler typename fn 
        (A.validate_t_exact n (as_serializer t) (as_validator typename t))

    | T_string fn elt_t terminator ->
      assert_norm (as_type (T_string fn elt_t terminator) == P.cstring (dtyp_as_type elt_t) terminator);
      assert_norm (as_parser (T_string fn elt_t terminator) == P.parse_string (dtyp_as_parser elt_t) terminator);
      A.validate_with_error_handler typename fn 
        (A.validate_string (dtyp_as_validator elt_t)
                           (dtyp_as_leaf_reader elt_t)
                           terminator)
#pop-options 

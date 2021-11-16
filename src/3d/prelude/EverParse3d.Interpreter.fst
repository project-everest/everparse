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
module ProjTac = EverParse3d.ProjectorTactic
#push-options "--__temp_no_proj EverParse3d.Interpreter" //we'll generate the projectors we need with a tactic

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
   which can be extracted by F*/Kremlin as usual---this partial
   evaluation of an interpreter to a compiler producing a C program
   for t-validator is an instance of the 1st Futamura projection.
 *)

(* An attribute to control partial evaluation *)
let specialize = ()

(** You can see the basic idea of the whole stack working at first on
    a very simple class of types---just the primitive types *)

(* Primitive types *)
type itype =
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | UInt16BE
  | UInt32BE
  | UInt64BE
  | Unit
  | AllBytes
  | AllZeros

(* Interpretation of itype as an F* type *)
[@@specialize]
let itype_as_type (i:itype)
  : Type
  = match i with
    | UInt8 -> P.___UINT8
    | UInt16 -> P.___UINT16
    | UInt32 -> P.___UINT32
    | UInt64 -> P.___UINT64
    | UInt16BE -> P.___UINT16BE
    | UInt32BE -> P.___UINT32BE
    | UInt64BE -> P.___UINT64BE
    | Unit -> unit
    | AllBytes -> P.all_bytes
    | AllZeros -> P.all_zeros

[@@specialize]
let parser_kind_nz_of_itype (i:itype)
  : bool
  = match i with
    | Unit
    | AllBytes
    | AllZeros -> false
    | _ -> true

[@@specialize]
let parser_weak_kind_of_itype (i:itype)
  : P.weak_kind
  = match i with
    | AllBytes
    | AllZeros -> P.WeakKindConsumesAll
    | _ -> P.WeakKindStrongPrefix

(* Interpretation of itype as a parser kind *)
[@@specialize]
let parser_kind_of_itype (i:itype)
  : P.parser_kind (parser_kind_nz_of_itype i)
                  (parser_weak_kind_of_itype i)
  = match i with
    | UInt8 -> P.kind____UINT8
    | UInt16 -> P.kind____UINT16
    | UInt32 -> P.kind____UINT32
    | UInt64 -> P.kind____UINT64
    | UInt16BE -> P.kind____UINT16BE
    | UInt32BE -> P.kind____UINT32BE
    | UInt64BE -> P.kind____UINT64BE
    | Unit -> P.kind_unit
    | AllBytes -> P.kind_all_bytes
    | AllZeros -> P.kind_all_zeros

(* Interpretation of an itype as a parser *)
let itype_as_parser (i:itype)
  : P.parser (parser_kind_of_itype i) (itype_as_type i)
  = match i with
    | UInt8 -> P.parse____UINT8
    | UInt16 -> P.parse____UINT16
    | UInt32 -> P.parse____UINT32
    | UInt64 -> P.parse____UINT64
    | UInt16BE -> P.parse____UINT16BE
    | UInt32BE -> P.parse____UINT32BE
    | UInt64BE -> P.parse____UINT64BE
    | Unit -> P.parse_unit
    | AllBytes -> P.parse_all_bytes
    | AllZeros -> P.parse_all_zeros

[@@specialize]
let allow_reader_of_itype (i:itype)
  : bool
  = match i with
    | AllBytes
    | AllZeros -> false
    | _ -> true

(* Interpretation of an itype as a leaf reader *)
[@@specialize]
let itype_as_leaf_reader (i:itype { allow_reader_of_itype i })
  : A.leaf_reader (itype_as_parser i)
  = match i with
    | UInt8 -> A.read____UINT8
    | UInt16 -> A.read____UINT16
    | UInt32 -> A.read____UINT32
    | UInt64 -> A.read____UINT64
    | UInt16BE -> A.read____UINT16BE
    | UInt32BE -> A.read____UINT32BE
    | UInt64BE -> A.read____UINT64BE
    | Unit -> A.read_unit
    
(* Interpretation of an itype as a validator
   -- Notice that the type shows that it is related to the parser *)
[@@specialize]
let itype_as_validator (i:itype)
  : A.validate_with_action_t (itype_as_parser i) A.true_inv A.eloc_none (allow_reader_of_itype i)
  = match i with
    | UInt8 -> A.validate____UINT8
    | UInt16 -> A.validate____UINT16
    | UInt32 -> A.validate____UINT32
    | UInt64 -> A.validate____UINT64
    | UInt16BE -> A.validate____UINT16BE
    | UInt32BE -> A.validate____UINT32BE
    | UInt64BE -> A.validate____UINT64BE
    | Unit -> A.validate_unit
    | AllBytes -> A.validate_all_bytes
    | AllZeros -> A.validate_all_zeros


(* Our first order of business to scale this up to 3D is to set up
   definitions for type contexts.

   A 3D program is a sequence of top-level definitions, where a given
   definition may reference terms defined previously. To model this,
   we'll given a denotation of programs in a _context_, where the
   context provides denotations for all the names defined previously
   which are in scope.
*)

let leaf_reader #nz #wk (#k: P.parser_kind nz wk) #t (p:P.parser k t)
  = _:squash (wk == P.WeakKindStrongPrefix /\ hasEq t) &
    A.leaf_reader p

(* Now, we can define the type of an environment *)
module T = FStar.Tactics

(* global_binding: 

   Represents the lifting of a fully applied a shallow F*
   quadruple of {type, parser, validator, opt reader} 
*)
noeq
type global_binding = {
  //Parser metadata
  parser_kind_nz:bool; // Does it consume non-zero bytes?
  parser_weak_kind: P.weak_kind;
  parser_kind: P.parser_kind parser_kind_nz parser_weak_kind;
  //Memory invariant of any actions it contains
  inv:A.slice_inv;
  //Write footprint of any of its actions
  loc:A.eloc;
  //Its type denotation
  p_t : Type0;
  //Its parser denotation
  p_p : P.parser parser_kind p_t;
  //Whether the type can be read -- to avoid double fetches
  p_reader: option (leaf_reader p_p);
  //Its validate-with-action denotationa
  p_v : A.validate_with_action_t p_p inv loc (Some? p_reader);
}

//Generate projectors with a tactic, because the default
//projectors are not SMT-typeable
%splice[nz_of_binding;
        wk_of_binding;
        pk_of_binding;
        inv_of_binding;
        loc_of_binding;
        type_of_binding;
        parser_of_binding;
        leaf_reader_of_binding;
        validator_of_binding]
       (ProjTac.mk_projs (`%global_binding)
                         ["nz_of_binding";
                          "wk_of_binding";
                          "pk_of_binding";
                          "inv_of_binding";
                          "loc_of_binding";
                          "type_of_binding";
                          "parser_of_binding";
                          "leaf_reader_of_binding";
                          "validator_of_binding"])

let has_reader (g:global_binding) = 
  match leaf_reader_of_binding g with
  | Some _ -> true
  | _ -> false

let reader_binding = g:global_binding { has_reader g }

[@@specialize]
let get_leaf_reader (r:reader_binding)
  : leaf_reader (parser_of_binding r)
  = Some?.v (leaf_reader_of_binding r)

(** Now we define the AST of 3D programs *)

let action_binding
      (inv:A.slice_inv)
      (l:A.eloc)
      (on_success:bool)
      (a:Type)
  : Type u#1 //in Universe 1 because it is polymorphic in t
  = (#nz:bool) ->
    (#wk:P.weak_kind) ->
    (#k:P.parser_kind nz wk) ->
    (#t:Type u#0) ->
    (p:P.parser k t) ->
    A.action p inv l on_success a

[@@specialize]
let mk_action_binding
    (#l:A.eloc)
    ($f: A.external_action l)
  : action_binding A.true_inv l false unit
  = fun (#nz:_) (#wk:_) (#k:P.parser_kind nz wk) (#t:Type u#0) (p:P.parser k t) ->
      A.mk_external_action f

(* The type of atomic actions.

   `atomic_action l i b t`: is an atomic action that
     - may modify locations `l`
     - relies on a memory invariant `i`
     - b, when set, indicates that the action can only run in a success handler
     - t, is the result type of the action

   In comparison with with the 3D front-end's internal representation
   of actions, some notable differences

     - The indexing structure tell us exactly the type to which these
       will translate. It's also worth comparing these types to the
       types of the action primitives in Actions.fsti---the indexing
       structure is the same

     - The type is already partially interpreted, e.g., rather than
       relying on an explicit representation of names (e.g., in
       Action_deref), this representation directly uses a pointer
       value.
*)
noeq
type atomic_action
  : A.slice_inv -> A.eloc -> bool -> Type0 -> Type u#1 =
  | Action_return:
      #a:Type0 ->
      x:a ->
      atomic_action A.true_inv A.eloc_none false a

  | Action_abort:
      atomic_action A.true_inv A.eloc_none false bool

  | Action_field_pos_64:
      atomic_action A.true_inv A.eloc_none false U64.t

  | Action_field_pos_32:
      squash (EverParse3d.Actions.BackendFlag.backend_flag == A.BackendFlagBuffer) ->
      atomic_action A.true_inv A.eloc_none false U32.t

  | Action_field_ptr:
      squash (EverParse3d.Actions.BackendFlag.backend_flag == A.BackendFlagBuffer) ->
      atomic_action A.true_inv A.eloc_none true A.___PUINT8

  | Action_deref:
      #a:Type0 ->
      x:A.bpointer a ->
      atomic_action (A.ptr_inv x) A.eloc_none false a

  | Action_assignment:
      #a:Type0 ->
      x:A.bpointer a ->
      rhs:a ->
      atomic_action (A.ptr_inv x) (A.ptr_loc x) false unit

  | Action_call:
      #inv:A.slice_inv ->
      #loc:A.eloc ->
      #b:bool ->
      #t:Type0 ->
      action_binding inv loc b t ->
      atomic_action inv loc b t

(* Denotation of atomic_actions as A.action *)
[@@specialize]
let atomic_action_as_action
   (#nz #wk:_)
   (#pk:P.parser_kind nz wk) (#pt:Type)
   (#i #l #b #t:_)
   (p:P.parser pk pt)
   (a:atomic_action i l b t)
  : Tot (A.action p i l b t)
  = match a with
    | Action_return x ->
      A.action_return x
    | Action_abort ->
      A.action_abort
    | Action_field_pos_64 ->
      A.action_field_pos_64 ()
    | Action_field_pos_32 sq ->
      A.action_field_pos_32 sq
    | Action_field_ptr sq ->
      A.action_field_ptr sq
    | Action_deref x ->
      A.action_deref x
    | Action_assignment x rhs ->
      A.action_assignment x rhs
    | Action_call c ->
      c p

(* A sub-language of monadic actions.

   The indexing structure mirrors the indexes of the combinators in
   Actions.fst
*)
noeq
type action
  : A.slice_inv -> A.eloc -> bool -> Type0 -> Type u#1 =
  | Atomic_action:
      #i:_ -> #l:_ -> #b:_ -> #t:_ ->
      atomic_action i l b t ->
      action i l b t

  | Action_seq:
      #i0:_ -> #l0:_ -> #b0:_ -> hd:atomic_action i0 l0 b0 unit ->
      #i1:_ -> #l1:_ -> #b1:_ -> #t:_ -> tl:action i1 l1 b1 t ->
      action (A.conj_inv i0 i1) (A.eloc_union l0 l1) (b0 || b1) t

  | Action_ite :
      hd:bool ->
      #i0:_ -> #l0:_ -> #b0:_ -> #t:_ -> then_:(_:squash hd -> action i0 l0 b0 t) ->
      #i1:_ -> #l1:_ -> #b1:_ -> else_:(_:squash (not hd) -> action i1 l1 b1 t) ->
      action (A.conj_inv i0 i1) (A.eloc_union l0 l1) (b0 || b1) t

  | Action_let:
      #i0:_ -> #l0:_ -> #b0:_ -> #t0:_ -> head:atomic_action i0 l0 b0 t0 ->
      #i1:_ -> #l1:_ -> #b1:_ -> #t1:_ -> k:(t0 -> action i1 l1 b1 t1) ->
      action (A.conj_inv i0 i1) (A.eloc_union l0 l1) (b0 || b1) t1

  | Action_act:
      #i0:_ -> #l0:_ -> #b0:_ -> act:action i0 l0 b0 unit ->
      action i0 l0 b0 bool

let _inv_implies_refl (inv: A.slice_inv) : Lemma
  (inv `A.inv_implies` inv)
  [SMTPat (inv `A.inv_implies` inv)]
= A.inv_implies_refl inv

let _inv_implies_true (inv0: A.slice_inv) : Lemma
  (inv0 `A.inv_implies` A.true_inv)
  [SMTPat (inv0 `A.inv_implies` A.true_inv)]
= A.inv_implies_true inv0

let _inv_implies_conj (inv0 inv1 inv2: A.slice_inv) : Lemma
  (requires (
    inv0 `A.inv_implies` inv1 /\
    inv0 `A.inv_implies` inv2
  ))
  (ensures (
    inv0 `A.inv_implies` (inv1 `A.conj_inv` inv2)
  ))
  [SMTPat (inv0 `A.inv_implies` (inv1 `A.conj_inv` inv2))]
= A.inv_implies_conj inv0 inv1 inv2 () ()

let _eloc_includes_none (l1:A.eloc) : Lemma
  (l1 `A.eloc_includes` A.eloc_none)
  [SMTPat (l1 `A.eloc_includes` A.eloc_none)]
= A.eloc_includes_none l1

let _eloc_includes_union (l0: A.eloc) (l1 l2: A.eloc) : Lemma
  (requires (
    l0 `A.eloc_includes` l1 /\
    l0 `A.eloc_includes` l2
  ))
  (ensures (
    l0 `A.eloc_includes` (l1 `A.eloc_union` l2)
  ))
  [SMTPat (l0 `A.eloc_includes` (l1 `A.eloc_union` l2))]
= A.eloc_includes_union l0 l1 l2 () ()

let _eloc_includes_refl (l: A.eloc) : Lemma
  (l `A.eloc_includes` l)
  [SMTPat (l `A.eloc_includes` l)]
= A.eloc_includes_refl l

(* Denotation of action as A.action *)
[@@specialize]
let rec action_as_action
   (#nz #wk:_)
   (#pk:P.parser_kind nz wk) (#pt:_)
   (#i #l #b #t:_)
   (p:P.parser pk pt)
   (a:action i l b t)
  : Tot (A.action p i l b t)
    (decreases a)
  = match a with
    | Atomic_action a ->
      atomic_action_as_action p a

    | Action_seq hd tl ->
      let a1 = atomic_action_as_action p hd in
      let tl = action_as_action p tl in
      A.action_seq a1 tl

    | Action_ite hd t e ->
      let then_ (x:squash hd) = action_as_action p (t x) in
      let else_ (x:squash (not hd)) = action_as_action p (e x) in
      A.action_ite hd then_ else_

    | Action_let hd k ->
      let head = atomic_action_as_action p hd in
      let k x = action_as_action p (k x) in
      A.action_bind "hd" head k

    | Action_act #i0 #l0 #b0 a ->
      A.action_weaken (A.action_seq (action_as_action p a) (A.action_return true)) #i0 #l0

(* Some AST nodes contain source comments that we propagate to the output *)
let comments = string

(* The main type of 3D types. Some points to note:

   - The indexing structure determines the types of the
     parser/validator etc. of its denotation

   - All top-level names mentioned in a typ must be bound in the
     context.

   - Constructs that bind local names are represented using F*
     functions that abstract over denotations of the underlying types.

   - Some elements of the source programs are "pre-denoted". Notably,
     every refinement formula is represented in this AST already as a
     boolean function, rather than in some embedded language of
     expressions. This is because expressions are not necessarily
     well-formed by syntax alone---they may give rise to verification
     conditions when using bounded arithmetic functions. So, it's the
     obligation of the `typ` generator (i.e., the 3D frontend) to
     produce boolean functions for those expressions that can be
     verified natively by F* for type correctness.
*)

noeq
type dtyp
  : #nz:bool -> #wk:P.weak_kind ->
    P.parser_kind nz wk ->
    has_reader:bool ->
    A.slice_inv ->
    A.eloc ->
    Type =
  | DT_IType:
      i:itype ->
      dtyp (parser_kind_of_itype i)
           (allow_reader_of_itype i)
           A.true_inv
           A.eloc_none

  | DT_App:
    (* We give explicit names to the indices rather than
       projecting them as a small optimization for the reduction
       machinery ... it's no longer clear that the speedup is significant *)
      #nz:bool ->
      #wk:P.weak_kind ->
      pk:P.parser_kind nz wk ->
      hr:bool ->
      inv:A.slice_inv ->
      loc:A.eloc ->
      x:global_binding ->
      _:squash (nz == nz_of_binding x /\
                wk == wk_of_binding x /\
                pk == pk_of_binding x /\
                hr == has_reader x /\
                inv == inv_of_binding x /\
                loc == loc_of_binding x) ->
      dtyp #nz #wk pk hr inv loc
           
[@@specialize]
let dtyp_as_type #nz #wk (#pk:P.parser_kind nz wk) #hr #i #l
                 (d:dtyp pk hr i l)
  : Type
  = match d with
    | DT_IType i -> 
      itype_as_type i

    | DT_App _ _ _ _ b _ ->
      type_of_binding b
      
let dtyp_as_eqtype_lemma #nz #wk (#pk:P.parser_kind nz wk) #i #l
                         (d:dtyp pk true i l)
  : Lemma
    (ensures hasEq (dtyp_as_type d))
    [SMTPat (hasEq (dtyp_as_type d))]
  = match d with
    | DT_IType i -> 
      ()

    | DT_App _ _ _ _ b _ ->
      let (| _, _ |) = get_leaf_reader b in ()

  
let dtyp_as_parser #nz #wk (#pk:P.parser_kind nz wk) #hr #i #l
                   (d:dtyp pk hr i l)
  : P.parser pk (dtyp_as_type d)
  = match d returns Tot (P.parser pk (dtyp_as_type d)) with
    | DT_IType i -> 
      itype_as_parser i

    | DT_App _ _ _ _ b _ ->
      parser_of_binding b

[@@specialize]
let dtyp_as_validator #nz #wk (#pk:P.parser_kind nz wk)
                      (#hr:_)
                      (#[@@@erasable] i:A.slice_inv)
                      (#[@@@erasable] l:A.eloc)
                      (d:dtyp pk hr i l)
  : A.validate_with_action_t #nz #wk #pk #(dtyp_as_type d) (dtyp_as_parser d) i l hr
  = match d 
    returns A.validate_with_action_t #nz #wk #pk #(dtyp_as_type d) (dtyp_as_parser d) i l hr
    with
    | DT_IType i -> 
      itype_as_validator i

    | DT_App _ _ _ _ b _ ->
      // assert_norm (dtyp_as_type (DT_App_Alt ps b args) == (type_of_binding_alt (apply_arrow b args)));
      // assert_norm (dtyp_as_parser (DT_App_Alt ps b args) == parser_of_binding_alt (apply_arrow b args));
      validator_of_binding b


[@@specialize]
let dtyp_as_leaf_reader #nz (#pk:P.parser_kind nz P.WeakKindStrongPrefix)
                        (#[@@@erasable] i:A.slice_inv)
                        (#[@@@erasable] l:A.eloc)
                        (d:dtyp pk true i l)
  : A.leaf_reader (dtyp_as_parser d)
  = match d with
    | DT_IType i -> 
      itype_as_leaf_reader i

    | DT_App _ _ _ _ b _ -> 
      let (| _, lr |) = get_leaf_reader b in
      lr

noeq
type typ
  : #nz:bool -> #wk:P.weak_kind ->
    P.parser_kind nz wk ->
    A.slice_inv ->
    A.eloc ->
    bool ->
    Type =
  | T_false:
      fieldname:string ->      
      typ P.impos_kind A.true_inv A.eloc_none true

  | T_denoted :
      fieldname:string ->       
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #has_reader:_ -> #i:_ -> #l:_ ->
      td:dtyp pk has_reader i l ->
      typ pk i l has_reader

  | T_pair:
      first_fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #l1:_ -> #b1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #l2:_ -> #b2:_ ->
      t1:typ pk1 i1 l1 b1 ->
      t2:typ pk2 i2 l2 b2 ->
      typ (P.and_then_kind pk1 pk2) (A.conj_inv i1 i2) (A.eloc_union l1 l2) false

  | T_dep_pair:
      first_fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #l1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #l2:_ -> #b2:bool ->
      //the first component is a pre-denoted type with a reader
      t1:dtyp pk1 true i1 l1 ->
      //the second component is a function from denotations of t1
      //that's why it's a small type, so that we can speak about its
      //denotation here
      t2:(dtyp_as_type t1 -> typ pk2 i2 l2 b2) ->
      typ (P.and_then_kind pk1 pk2) (A.conj_inv i1 i2) (A.eloc_union l1 l2) false

  | T_refine:
      fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #l1:_ ->
      //the first component is a pre-denoted type with a reader
      base:dtyp pk1 true i1 l1 ->
      //the second component is a function from denotations of base
      //but notice that its codomain is bool, rather than expr
      //That's to ensure that the refinement is already well-typed
      refinement:(dtyp_as_type base -> bool) ->
      typ (P.filter_kind pk1) i1 l1 false

  | T_refine_with_action:
      fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #l1:_ ->
      #i2:_ -> #l2:_ -> #b2:_ ->
      base:dtyp pk1 true i1 l1 ->
      refinement:(dtyp_as_type base -> bool) ->
      act:(dtyp_as_type base -> action i2 l2 b2 bool) ->
      typ (P.filter_kind pk1) (A.conj_inv i1 i2) (A.eloc_union l1 l2) false
  
  | T_dep_pair_with_refinement:
      //This construct serves two purposes
      // 1. To avoid double fetches, we fold the refinement
      //    and dependent pair into a single form
      // 2. This allows the well-typedness of the continuation k
      //    to depend on the refinement of the first field
      first_fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #l1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #l2:_ -> #b2:_ ->
      //the first component is a pre-denoted type with a reader
      base:dtyp pk1 true i1 l1 ->
      //the second component is a function from denotations of base
      refinement:(dtyp_as_type base -> bool) ->
      k:(x:dtyp_as_type base { refinement x } -> typ pk2 i2 l2 b2) ->
      typ (P.and_then_kind (P.filter_kind pk1) pk2)
          (A.conj_inv i1 i2)
          (A.eloc_union l1 l2)
          false

  | T_dep_pair_with_action:
      fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #l1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #l2:_ -> #b2:_ ->
      #i3:_ -> #l3:_ -> #b3:_ ->      
      base:dtyp pk1 true i1 l1 ->
      k:(x:dtyp_as_type base -> typ pk2 i2 l2 b2) ->
      act:(dtyp_as_type base -> action i3 l3 b3 bool) ->
      typ (P.and_then_kind pk1 pk2)
          (A.conj_inv i1 (A.conj_inv i3 i2))
          (A.eloc_union l1 (A.eloc_union l3 l2))
          false

  | T_dep_pair_with_refinement_and_action:
      //This construct serves two purposes
      // 1. To avoid double fetches, we fold the refinement
      //    and dependent pair and action into a single form
      // 2. This allows the well-typedness of the continuation k
      //    to depend on the refinement of the first field
      first_fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #l1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #l2:_ -> #b2:_ ->
      #i3:_ -> #l3:_ -> #b3:_ ->      
      //the first component is a pre-denoted type with a reader
      base:dtyp pk1 true i1 l1 ->
      //the second component is a function from denotations of base
      refinement:(dtyp_as_type base -> bool) ->
      k:(x:dtyp_as_type base { refinement x } -> typ pk2 i2 l2 b2) ->
      act:(dtyp_as_type base -> action i3 l3 b3 bool) ->
      typ (P.and_then_kind (P.filter_kind pk1) pk2)
          (A.conj_inv i1 (A.conj_inv i3 i2))
          (A.eloc_union l1 (A.eloc_union l3 l2))
          false

  | T_if_else:
      #nz1:_ -> #wk1:_ -> #pk1:P.parser_kind nz1 wk1 ->
      #l1:_ -> #i1:_ -> #b1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->      
      #l2:_ -> #i2:_ -> #b2:_ ->
      b:bool -> //A bool, rather than an expression
      t1:(squash b -> typ pk1 i1 l1 b1) ->
      t2:(squash (not b) -> typ pk2 i2 l2 b2) ->
      typ (P.glb pk1 pk2) (A.conj_inv i1 i2) (A.eloc_union l1 l2) false

  | T_cases:
      #nz1:_ -> #wk1:_ -> #pk1:P.parser_kind nz1 wk1 ->
      #l1:_ -> #i1:_ -> #b1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->      
      #l2:_ -> #i2:_ -> #b2:_ ->
      b:bool -> //A bool, rather than an expression
      t1:typ pk1 i1 l1 b1 ->
      t2:typ pk2 i2 l2 b2 ->
      typ (P.glb pk1 pk2) (A.conj_inv i1 i2) (A.eloc_union l1 l2) false

  | T_with_action:
      fieldname:string ->       
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #l1:_ -> #i1:_ -> #b1:_ ->
      #l2:_ -> #i2:_ -> #b2:_ ->
      base:typ pk i1 l1 b1 ->
      act:action i2 l2 b2 bool ->
      typ pk (A.conj_inv i1 i2) (A.eloc_union l1 l2) false

  | T_with_dep_action:
      fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #l1:_ ->
      #i2:_ -> #l2:_ -> #b2:_ ->
      head:dtyp pk1 true i1 l1 ->
      act:(dtyp_as_type head -> action i2 l2 b2 bool) ->
      typ pk1 (A.conj_inv i1 i2) (A.eloc_union l1 l2) false

  | T_with_comment:
      fieldname:string ->       
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #l:_ -> #i:_ -> #b:_ ->
      t:typ pk i l b ->
      c:comments ->
      typ pk i l b

  | T_nlist:
      fieldname:string ->       
      #wk:_ -> #pk:P.parser_kind true wk ->
      #i:_ -> #l:_ -> #b:_ ->
      n:U32.t ->
      t:typ pk i l b ->
      typ P.kind_nlist i l false

  | T_at_most:
      fieldname:string ->       
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #i:_ -> #l:_ -> #b:_ ->
      n:U32.t ->
      t:typ pk i l b ->
      typ P.kind_t_at_most i l false

  | T_exact:
      fieldname:string ->       
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #i:_ -> #l:_ -> #b:_ ->
      n:U32.t ->
      t:typ pk i l b ->
      typ P.kind_t_exact i l false

  | T_string:
      fieldname:string ->       
      #pk1:P.parser_kind true P.WeakKindStrongPrefix ->
      element_type:dtyp pk1 true A.true_inv A.eloc_none ->
      terminator:dtyp_as_type element_type ->
      typ P.parse_string_kind A.true_inv A.eloc_none false


(* Type denotation of `typ` *)
let rec as_type
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #b
          (t:typ pk l i b)
  : Tot Type0
    (decreases t)
  = match t with
    | T_false _ -> False

    | T_denoted _ td -> 
      dtyp_as_type td

    | T_pair _ t1 t2 ->
      as_type t1 & as_type t2

    | T_dep_pair _ i t
    | T_dep_pair_with_action _ i t _ ->
      x:dtyp_as_type i & as_type (t x)

    | T_refine _ base refinement ->
      P.refine (dtyp_as_type base) refinement

    | T_refine_with_action _ base refinement _ ->
      P.refine (dtyp_as_type base) refinement

    | T_dep_pair_with_refinement _ base refinement t ->
      x:P.refine (dtyp_as_type base) refinement & as_type (t x)

    | T_dep_pair_with_refinement_and_action _ base refinement t _ ->
      x:P.refine (dtyp_as_type base) refinement & as_type (t x)

    | T_if_else b t0 t1 ->
      P.t_ite b (fun _ -> as_type (t0()))
                      (fun _ -> as_type (t1()))

    | T_cases b t0 t1 ->
      P.t_ite b (fun _ -> as_type t0) (fun _ -> as_type t1)

    | T_with_action _ t _
    | T_with_comment _ t _ ->
      as_type t

    | T_with_dep_action _ i _ ->
      dtyp_as_type i

    | T_nlist _ n t ->
      P.nlist n (as_type t)

    | T_at_most _ n t ->
      P.t_at_most n (as_type t)

    | T_exact _ n t ->
      P.t_exact n (as_type t)

    | T_string _ elt_t terminator ->
      P.cstring (dtyp_as_type elt_t) terminator

(* Parser denotation of `typ` *)
let rec as_parser
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #b
          (t:typ pk l i b)
  : Tot (P.parser pk (as_type t))
        (decreases t)
  = match t returns Tot (P.parser pk (as_type t)) with
    | T_false _ ->
      //assert_norm (as_type g T_false == False);
      P.parse_impos()

    | T_denoted _ d ->
      dtyp_as_parser d

    | T_pair _ t1 t2 ->
      //assert_norm (as_type g (T_pair t1 t2) == as_type g t1 * as_type g t2);
      let p1 = as_parser t1 in
      let p2 = as_parser t2 in
      P.parse_pair p1 p2

    | T_dep_pair _ i t
    | T_dep_pair_with_action _ i t _ ->
      //assert_norm (as_type g (T_dep_pair i t) == x:itype_as_type i & as_type g (t x));
      let pi = dtyp_as_parser i in
      P.parse_dep_pair pi (fun (x:dtyp_as_type i) -> as_parser (t x))

    | T_refine _ base refinement
    | T_refine_with_action _ base refinement _ ->
      //assert_norm (as_type g (T_refine base refinement) == P.refine (itype_as_type base) refinement);
      let pi = dtyp_as_parser base in
      P.parse_filter pi refinement

    | T_dep_pair_with_refinement _ base refinement k ->
      P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x)))


    | T_dep_pair_with_refinement_and_action _ base refinement k _ ->
      P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x)))

    | T_if_else b t0 t1 ->
      //assert_norm (as_type g (T_if_else b t0 t1) == P.t_ite b (as_type g t0) (as_type g t1));
      let p0 (_:squash b) = 
        P.parse_weaken_right (as_parser (t0())) _
      in
      let p1 (_:squash (not b)) = 
        P.parse_weaken_left (as_parser (t1())) _
      in
      P.parse_ite b p0 p1

    | T_cases b t0 t1 ->
      //assert_norm (as_type g (T_if_else b t0 t1) == P.t_ite b (as_type g t0) (as_type g t1));
      let p0 (_:squash b) = 
        P.parse_weaken_right (as_parser t0) _
      in
      let p1 (_:squash (not b)) = 
        P.parse_weaken_left (as_parser t1) _
      in
      P.parse_ite b p0 p1

    | T_with_action _ t a ->
      //assert_norm (as_type g (T_with_action t a) == as_type g t);
      as_parser t

    | T_with_dep_action _ i a ->
      //assert_norm (as_type g (T_with_dep_action i a) == itype_as_type i);
      dtyp_as_parser i

    | T_with_comment _ t c ->
      //assert_norm (as_type g (T_with_comment t c) == as_type g t);
      as_parser t

    | T_nlist _ n t ->
      P.parse_nlist n (as_parser t)

    | T_at_most _ n t ->
      P.parse_t_at_most n (as_parser t)

    | T_exact _ n t ->
      P.parse_t_exact n (as_parser t)

    | T_string _ elt_t terminator ->
      P.parse_string (dtyp_as_parser elt_t) terminator

[@@specialize]
let rec as_reader #nz (#pk:P.parser_kind nz P.WeakKindStrongPrefix)
                  (#[@@@erasable] inv:A.slice_inv)
                  (#[@@@erasable] loc:A.eloc)
                  (t:typ pk inv loc true)
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
let rec as_validator
          (typename:string)
          #nz #wk (#pk:P.parser_kind nz wk)
          (#[@@@erasable] inv:A.slice_inv)
          (#[@@@erasable] loc:A.eloc)
          #b
          (t:typ pk inv loc b)
  : Tot (A.validate_with_action_t #nz #wk #pk #(as_type t) (as_parser t) inv loc b)
        (decreases t)
  = match t
    returns Tot (A.validate_with_action_t (as_parser t) inv loc b)
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
      A.validate_weaken_inv_loc inv loc
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
          (fun x -> action_as_action (as_parser (T_refine fn t f)) (a x)))

    | T_dep_pair_with_refinement fn base refinement k ->
      assert_norm (as_type (T_dep_pair_with_refinement fn base refinement k) ==
                        x:P.refine (dtyp_as_type base) refinement & as_type (k x));
      assert_norm (as_parser (T_dep_pair_with_refinement fn base refinement k) ==
                        P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x))));
      A.validate_with_error_handler typename fn                              
        (A.validate_weaken_inv_loc inv loc (
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
        (A.validate_weaken_inv_loc inv loc (
          A.validate_dep_pair_with_action 
            (dtyp_as_validator base)
            (dtyp_as_leaf_reader base)
            (fun x -> action_as_action (dtyp_as_parser base) (act x))
            (fun x -> as_validator typename (t x))))

    | T_dep_pair_with_refinement_and_action fn base refinement k act ->
      assert_norm (as_type (T_dep_pair_with_refinement_and_action fn base refinement k act) ==
                        x:P.refine (dtyp_as_type base) refinement & as_type (k x));
      assert_norm (as_parser (T_dep_pair_with_refinement_and_action fn base refinement k act) ==
                        P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x))));
      A.validate_weaken_inv_loc inv loc (
          A.validate_dep_pair_with_refinement_and_action false fn
            (A.validate_with_error_handler typename fn                              
              (dtyp_as_validator base))
            (dtyp_as_leaf_reader base)
            refinement
            (fun x -> action_as_action (dtyp_as_parser base) (act x))
            (fun x -> as_validator typename (k x)))

    | T_if_else b t0 t1 ->
      assert_norm (as_type (T_if_else b t0 t1) == P.t_ite b (fun _ -> as_type (t0())) (fun _ -> as_type (t1 ())));
      let p0 (_:squash b) = P.parse_weaken_right (as_parser (t0())) _ in
      let p1 (_:squash (not b)) = P.parse_weaken_left (as_parser (t1())) _ in
      assert_norm (as_parser (T_if_else b t0 t1) == P.parse_ite b p0 p1);
      let v0 (_:squash b) = 
        A.validate_weaken_right (as_validator typename (t0())) _
      in
      let v1 (_:squash (not b)) =
        A.validate_weaken_left (as_validator typename (t1())) _
      in
      A.validate_ite b p0 v0 p1 v1

    | T_cases b t0 t1 ->
      assert_norm (as_type (T_cases b t0 t1) == P.t_ite b (fun _ -> as_type t0) (fun _ -> as_type t1));
      let p0 (_:squash b) = P.parse_weaken_right (as_parser t0) _ in
      let p1 (_:squash (not b)) = P.parse_weaken_left (as_parser t1) _ in
      assert_norm (as_parser (T_cases b t0 t1) == P.parse_ite b p0 p1);
      let v0 (_:squash b) = 
        A.validate_weaken_right (as_validator typename t0) _
      in
      let v1 (_:squash (not b)) =
        A.validate_weaken_left (as_validator typename t1) _
      in
      A.validate_ite b p0 v0 p1 v1

    | T_with_action fn t a ->
      assert_norm (as_type (T_with_action fn t a) == as_type t);
      assert_norm (as_parser (T_with_action fn t a) == as_parser t);
      A.validate_with_error_handler typename fn 
        (A.validate_with_success_action fn
          (as_validator typename t)
          (action_as_action (as_parser t) a))

    | T_with_dep_action fn i a ->
      assert_norm (as_type (T_with_dep_action fn i a) == dtyp_as_type i);
      assert_norm (as_parser (T_with_dep_action fn i a) == dtyp_as_parser i);
      A.validate_with_error_handler typename fn 
        (A.validate_weaken_inv_loc inv loc (
          A.validate_with_dep_action fn
            (dtyp_as_validator i)
            (dtyp_as_leaf_reader i)
            (fun x -> action_as_action (dtyp_as_parser i) (a x))))

    | T_with_comment fn t c ->
      assert_norm (as_type (T_with_comment fn t c) == as_type t);
      assert_norm (as_parser (T_with_comment fn t c) == as_parser t);
      A.validate_with_comment c (as_validator typename t)

    | T_nlist fn n t ->
      assert_norm (as_type (T_nlist fn n t) == P.nlist n (as_type t));
      assert_norm (as_parser (T_nlist fn n t) == P.parse_nlist n (as_parser t));
      A.validate_with_error_handler typename fn 
        (A.validate_nlist n (as_validator typename t))

    | T_at_most fn n t ->
      assert_norm (as_type (T_at_most fn n t) == P.t_at_most n (as_type t));
      assert_norm (as_parser (T_at_most fn n t) == P.parse_t_at_most n (as_parser t));
      A.validate_with_error_handler typename fn 
        (A.validate_t_at_most n (as_validator typename t))

    | T_exact fn n t ->
      assert_norm (as_type (T_exact fn n t) == P.t_exact n (as_type t));
      assert_norm (as_parser (T_exact fn n t) == P.parse_t_exact n (as_parser t));
      A.validate_with_error_handler typename fn 
        (A.validate_t_exact n (as_validator typename t))

    | T_string fn elt_t terminator ->
      assert_norm (as_type (T_string fn elt_t terminator) == P.cstring (dtyp_as_type elt_t) terminator);
      assert_norm (as_parser (T_string fn elt_t terminator) == P.parse_string (dtyp_as_parser elt_t) terminator);
      A.validate_with_error_handler typename fn 
        (A.validate_string (dtyp_as_validator elt_t)
                           (dtyp_as_leaf_reader elt_t)
                           terminator)

[@@noextract_to "Kremlin"; specialize]
inline_for_extraction noextract 
let validator_of #nz #wk (#k:P.parser_kind nz wk) #i #l #b (t:typ k i l b) = 
  A.validate_with_action_t (as_parser t) i l b

[@@noextract_to "Kremlin"; specialize]  
inline_for_extraction noextract   
let dtyp_of #nz #wk (#k:P.parser_kind nz wk) #i #l #b (t:typ k i l b) = 
  dtyp k b i l

let specialization_steps =
  [nbe;
   zeta;
   primops;
   iota;
   delta_attr [`%specialize];
   delta_only [`%Some?;
               `%Some?.v;
               `%as_validator;
               `%nz_of_binding;
               `%wk_of_binding;
               `%pk_of_binding;
               `%inv_of_binding;
               `%loc_of_binding;
               `%type_of_binding;
               `%parser_of_binding;
               `%validator_of_binding;
               `%leaf_reader_of_binding;
               `%fst;
               `%snd;
               `%Mktuple2?._1;
               `%Mktuple2?._2]]

let specialize_tac steps (_:unit)
  : T.Tac unit
  = let open FStar.List.Tot in
    T.norm (steps@specialization_steps);
    T.trefl()

[@@specialize]
let mk_global_binding #nz #wk 
                      (pk:P.parser_kind nz wk)
                      ([@@@erasable] inv:A.slice_inv)
                      ([@@@erasable] loc:A.eloc)
                      ([@@@erasable] p_t : Type0)
                      ([@@@erasable] p_p : P.parser pk p_t)
                      (p_reader: option (leaf_reader p_p))
                      (b:bool)
                      (p_v : A.validate_with_action_t p_p inv loc b)
                      ([@@@erasable] pf:squash (b == Some? p_reader))
   : global_binding
   = {
       parser_kind_nz = nz;
       parser_weak_kind = wk;
       parser_kind = pk;
       inv = inv;
       loc = loc;
       p_t = p_t;
       p_p = p_p;
       p_reader = p_reader;
       p_v = p_v
     }

[@@specialize]
inline_for_extraction
let coerce (#[@@@erasable]a:Type)
           (#[@@@erasable]b:Type)
           ( [@@@erasable]pf:squash (a == b))
           (x:a) 
  : b 
  = x

[@@specialize]
let mk_dt_app #nz #wk (pk:P.parser_kind nz wk) (b:bool)
              ([@@@erasable] inv:A.slice_inv)
              ([@@@erasable] loc:A.eloc)
              (x:global_binding)
              ([@@@erasable] pf:squash (nz == nz_of_binding x /\
                                        wk == wk_of_binding x /\
                                        pk == pk_of_binding x /\
                                        b == has_reader x /\
                                        inv == inv_of_binding x /\
                                        loc == loc_of_binding x))
    : dtyp #nz #wk pk b inv loc
    = DT_App pk b inv loc x pf


[@@specialize]
let mk_dtyp_app #nz #wk 
                (pk:P.parser_kind nz wk)
                ([@@@erasable] inv:A.slice_inv)
                ([@@@erasable] loc:A.eloc)
                ([@@@erasable] p_t : Type0)
                ([@@@erasable] p_p : P.parser pk p_t)
                (p_reader: option (leaf_reader p_p))
                (b:bool)
                (p_v : A.validate_with_action_t p_p inv loc b)
                ([@@@erasable] pf:squash (b == Some? p_reader))
   : dtyp #nz #wk pk b inv loc
   = let gb = {
       parser_kind_nz = nz;
       parser_weak_kind = wk;
       parser_kind = pk;
       inv = inv;
       loc = loc;
       p_t = p_t;
       p_p = p_p;
       p_reader = p_reader;
       p_v = p_v
     } in
     DT_App pk b inv loc gb ()

let coerce_validator steps : T.Tac unit =
  let open FStar.List.Tot in
  T.norm [delta_only (steps @ [`%parser_kind_of_itype;
                               `%parser_kind_nz_of_itype;
                               `%fst;
                               `%snd;
                               `%Mktuple2?._1;
                               `%Mktuple2?._2;
                               `%coerce;
                               `%validator_of;
                               `%dtyp_of;
                              ]);
           zeta;
           iota;
           primops];
  T.trefl()


let coerce_dt_app (steps:_) : T.Tac unit =
  let open FStar.List.Tot in
  T.norm [delta_only (steps@[`%nz_of_binding;
                        `%wk_of_binding;
                        `%pk_of_binding;
                        `%has_reader;
                        `%leaf_reader_of_binding;                                 
                        `%inv_of_binding;
                        `%loc_of_binding;
                        `%mk_global_binding]);
          zeta; 
          iota;
          simplify];
  T.trivial()

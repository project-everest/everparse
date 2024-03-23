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

inline_for_extraction
noextract
let ___EVERPARSE_COPY_BUFFER_T = CP.copy_buffer_t

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
  | UInt8BE
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
    | UInt8BE -> P.___UINT8BE
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
    | UInt8BE -> P.kind____UINT8BE
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
    | UInt8BE -> P.parse____UINT8BE
    | UInt16BE -> P.parse____UINT16BE
    | UInt32BE -> P.parse____UINT32BE
    | UInt64BE -> P.parse____UINT64BE
    | Unit -> P.parse_unit
    | AllBytes -> P.parse_all_bytes
    | AllZeros -> P.parse_all_zeros

(* Interpretation of an itype as a serializer *)
let itype_as_serializer (i:itype)
  : P.serializer (itype_as_parser i)
  = match i with
    | UInt8 -> P.serialize____UINT8
    | UInt16 -> P.serialize____UINT16
    | UInt32 -> P.serialize____UINT32
    | UInt64 -> P.serialize____UINT64
    | UInt8BE -> P.serialize____UINT8BE
    | UInt16BE -> P.serialize____UINT16BE
    | UInt32BE -> P.serialize____UINT32BE
    | UInt64BE -> P.serialize____UINT64BE
    | Unit -> P.serialize_unit
    | AllBytes -> P.serialize_all_bytes
    | AllZeros -> P.serialize_all_zeros

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
    | UInt8BE -> A.read____UINT8BE
    | UInt16BE -> A.read____UINT16BE
    | UInt32BE -> A.read____UINT32BE
    | UInt64BE -> A.read____UINT64BE
    | Unit -> A.read_unit
    
(* Interpretation of an itype as a validator
   -- Notice that the type shows that it is related to the parser *)
[@@specialize]
let itype_as_validator (i:itype)
  : A.validate_with_action_t
      (itype_as_parser i)
      A.true_inv
      A.disjointness_trivial
      A.eloc_none
      (allow_reader_of_itype i)
  = match i with
    | UInt8 -> A.validate____UINT8
    | UInt16 -> A.validate____UINT16
    | UInt32 -> A.validate____UINT32
    | UInt64 -> A.validate____UINT64
    | UInt8BE -> A.validate____UINT8BE
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

[@@erasable]
noeq
type index (a:Type) =
  | Trivial : index a
  | NonTrivial : a -> index a

[@@specialize]
let join_index  (j:'a -> 'a -> 'a) (i0 i1:index 'a)
: index 'a
= match i0 with
  | Trivial -> i1
  | _ -> (
    match i1 with
    | Trivial -> i0
    | NonTrivial i1 -> 
      let NonTrivial i0 = i0 in
      NonTrivial (j i0 i1)
  )
[@@specialize]
let interp_index (triv:'a) (i:index 'a)
: GTot 'a
= match i with
  | Trivial -> triv
  | NonTrivial i -> i


let inv_index = index A.slice_inv
[@@specialize]
let inv_none : inv_index = Trivial
[@@specialize]
let join_inv = join_index A.conj_inv
[@@specialize]
let interp_inv = interp_index A.true_inv

let loc_index = index A.eloc
[@@specialize]
let loc_none : loc_index = Trivial
[@@specialize]
let join_loc = join_index A.eloc_union
[@@specialize]
let interp_loc = interp_index A.eloc_none

let disj_index = index A.disjointness_pre
[@@specialize]
let disj_none : disj_index = Trivial
[@@specialize]
let join_disj = join_index A.conj_disjointness
[@@specialize]
let interp_disj = interp_index A.disjointness_trivial
[@@specialize]
let disjoint (e1 e2:loc_index)
  : disj_index
  = match e1, e2 with
    | Trivial, _
    | _, Trivial -> disj_none
    | NonTrivial e1, NonTrivial e2 -> NonTrivial (A.disjoint e1 e2)


(* A context is a list of bindings, where each binding is a pair of a
   name and a denotation of the name. *)
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
  inv:inv_index;
  //Disjointness precondition
  disj:disj_index;
  //Write footprint of any of its actions
  loc:loc_index;
  //Its type denotation
  p_t : Type0;
  //Its parser denotation
  p_p : P.parser parser_kind p_t;
  //Its serializer denotation
  p_s : P.serializer p_p;
  //Whether the type can be read -- to avoid double fetches
  p_reader: option (leaf_reader p_p);
  //Its validate-with-action denotationa
  p_v : A.validate_with_action_t
          p_p
          (interp_inv inv)
          (interp_disj disj)
          (interp_loc loc)
          (Some? p_reader);
}

let projector_names : list string = [
  `%Mkglobal_binding?.parser_kind_nz;
  `%Mkglobal_binding?.parser_weak_kind;
  `%Mkglobal_binding?.parser_kind;
  `%Mkglobal_binding?.inv;
  `%Mkglobal_binding?.disj;
  `%Mkglobal_binding?.loc;
  `%Mkglobal_binding?.p_t;
  `%Mkglobal_binding?.p_p;
  `%Mkglobal_binding?.p_s;
  `%Mkglobal_binding?.p_reader;
  `%Mkglobal_binding?.p_v;
]

let nz_of_binding = Mkglobal_binding?.parser_kind_nz
let wk_of_binding = Mkglobal_binding?.parser_weak_kind
let pk_of_binding = Mkglobal_binding?.parser_kind
let inv_of_binding = Mkglobal_binding?.inv
let disj_of_bindng = Mkglobal_binding?.disj
let loc_of_binding = Mkglobal_binding?.loc
let type_of_binding = Mkglobal_binding?.p_t
let parser_of_binding = Mkglobal_binding?.p_p
let serializer_of_binding = Mkglobal_binding?.p_s
let leaf_reader_of_binding = Mkglobal_binding?.p_reader
let validator_of_binding = Mkglobal_binding?.p_v

let has_reader (g:global_binding) = 
  match leaf_reader_of_binding g with
  | Some _ -> true
  | _ -> false

let reader_binding = g:global_binding { has_reader g }

[@@specialize]
let get_leaf_reader (r:reader_binding)
  : leaf_reader (parser_of_binding r)
  = Some?.v (leaf_reader_of_binding r)


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
    inv_index ->
    disj_index ->
    loc_index ->
    Type =
  | DT_IType:
      i:itype ->
      dtyp (parser_kind_of_itype i)
           (allow_reader_of_itype i)
           inv_none disj_none loc_none

  | DT_App:
    (* We give explicit names to the indices rather than
       projecting them as a small optimization for the reduction
       machinery ... it's no longer clear that the speedup is significant *)
      #nz:bool ->
      #wk:P.weak_kind ->
      pk:P.parser_kind nz wk ->
      hr:bool ->
      inv:inv_index ->
      disj:disj_index ->
      loc:loc_index ->
      x:global_binding ->
      _:squash (nz == nz_of_binding x /\
                wk == wk_of_binding x /\
                pk == pk_of_binding x /\
                hr == has_reader x /\
                inv == inv_of_binding x /\
                disj == disj_of_bindng x /\
                loc == loc_of_binding x) ->
      dtyp #nz #wk pk hr inv disj loc

[@@specialize]
let dtyp_as_type #nz #wk (#pk:P.parser_kind nz wk) #hr #i #disj #l
                 (d:dtyp pk hr i disj l)
  : Type
  = match d with
    | DT_IType i -> 
      itype_as_type i

    | DT_App _ _ _ _ _ b _ ->
      type_of_binding b
      
val dtyp_as_eqtype_lemma #nz #wk (#pk:P.parser_kind nz wk) #i #disj #l
                         (d:dtyp pk true i disj l)
  : Lemma
    (ensures hasEq (dtyp_as_type d))
    [SMTPat (hasEq (dtyp_as_type d))]

  
val dtyp_as_parser #nz #wk (#pk:P.parser_kind nz wk) #hr #i #disj #l
                   (d:dtyp pk hr i disj l)
  : P.parser pk (dtyp_as_type d)
 
val dtyp_as_serializer #nz #wk (#pk:P.parser_kind nz wk) #hr #i #disj #l
                   (d:dtyp pk hr i disj l)
  : P.serializer (dtyp_as_parser d)

[@@specialize]
val dtyp_as_validator #nz #wk (#pk:P.parser_kind nz wk)
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

[@@specialize]
val dtyp_as_leaf_reader #nz (#pk:P.parser_kind nz P.WeakKindStrongPrefix)
                        (#[@@@erasable] i:inv_index)
                        (#[@@@erasable] disj:disj_index)
                        (#[@@@erasable] l:loc_index)
                        (d:dtyp pk true i disj l)
  : A.leaf_reader (dtyp_as_parser d)

(** Actions *)

let action_binding
      (inv:inv_index)
      (l:loc_index)
      (on_success:bool)
      (a:Type)
  : Type u#0
  = A.action (interp_inv inv) A.disjointness_trivial (interp_loc l) on_success a

inline_for_extraction
let extern_action (l:loc_index) = A.external_action (interp_loc l)

inline_for_extraction
let mk_extern_action (#l:loc_index) ($f:extern_action l)
  = A.mk_external_action f

[@@specialize]
let mk_action_binding
    (#l:loc_index)
    ($f:extern_action l)
  : action_binding inv_none l false unit
  = mk_extern_action f

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
  : inv_index -> disj_index -> loc_index -> bool -> Type0 -> Type u#1 =
  | Action_return:
      #a:Type0 ->
      x:a ->
      atomic_action inv_none disj_none loc_none false a

  | Action_abort:
      atomic_action inv_none disj_none loc_none false bool

  | Action_field_pos_64:
      atomic_action inv_none disj_none loc_none false U64.t

  | Action_field_pos_32:
      squash (EverParse3d.Actions.BackendFlag.backend_flag == A.BackendFlagBuffer) ->
      atomic_action inv_none disj_none loc_none false U32.t

  | Action_field_ptr:
      squash (EverParse3d.Actions.BackendFlag.backend_flag == A.BackendFlagBuffer) ->
      atomic_action inv_none disj_none loc_none true A.___PUINT8

  | Action_field_ptr_after:
      squash (EverParse3d.Actions.BackendFlag.backend_flag == A.BackendFlagExtern) ->
      (sz: FStar.UInt64.t) ->
      write_to: A.bpointer A.___PUINT8 ->
      atomic_action (NonTrivial (A.ptr_inv write_to)) disj_none (NonTrivial (A.ptr_loc write_to)) false bool
 
  | Action_field_ptr_after_with_setter:
      squash (EverParse3d.Actions.BackendFlag.backend_flag == A.BackendFlagExtern) ->
      sz: FStar.UInt64.t ->
      #out_loc:loc_index ->
      write_to: (A.___PUINT8 -> Tot (extern_action out_loc)) ->
      atomic_action inv_none disj_none out_loc false bool

  | Action_deref:
      #a:Type0 ->
      x:A.bpointer a ->
      atomic_action (NonTrivial (A.ptr_inv x)) disj_none loc_none false a

  | Action_assignment:
      #a:Type0 ->
      x:A.bpointer a ->
      rhs:a ->
      atomic_action (NonTrivial (A.ptr_inv x)) disj_none (NonTrivial (A.ptr_loc x)) false unit

  | Action_call:
      #inv:inv_index ->
      #loc:loc_index ->
      #b:bool ->
      #t:Type0 ->
      action_binding inv loc b t ->
      atomic_action inv disj_none loc b t
  
  | Action_probe_then_validate:
      #nz:bool -> 
      #wk:_ ->
      #k:P.parser_kind nz wk ->
      #has_reader:bool ->
      #inv:inv_index ->
      #disj:disj_index ->
      #l:loc_index ->
      dt:dtyp k has_reader inv disj l ->
      src:U64.t ->
      len:U64.t ->
      dest:CP.copy_buffer_t ->
      probe:CP.probe_fn ->
      atomic_action (join_inv inv (NonTrivial (A.copy_buffer_inv dest)))
                    (join_disj disj (disjoint (NonTrivial (A.copy_buffer_loc dest)) l))
                    (join_loc l (NonTrivial (A.copy_buffer_loc dest)))
                    true bool


(* Denotation of atomic_actions as A.action *)
[@@specialize]
val atomic_action_as_action
   (#i #d #l #b #t:_)
   (a:atomic_action i d l b t)
  : Tot (A.action (interp_inv i) (interp_disj d) (interp_loc l) b t)

(* A sub-language of monadic actions.

   The indexing structure mirrors the indexes of the combinators in
   Actions.fst
*)
noeq
type action
  : inv_index -> disj_index -> loc_index -> bool -> Type0 -> Type u#1 =
  | Atomic_action:
      #i:_ -> #d:_ -> #l:_ -> #b:_ -> #t:_ ->
      atomic_action i d l b t ->
      action i d l b t

  | Action_seq:
      #i0:_ -> #l0:_ -> #b0:_ -> hd:atomic_action i0 disj_none l0 b0 unit ->
      #i1:_ -> #l1:_ -> #b1:_ -> #t:_ -> tl:action i1 disj_none l1 b1 t ->
      action (join_inv i0 i1) disj_none (join_loc l0 l1) (b0 || b1) t

  | Action_ite :
      hd:bool ->
      #i0:_ -> #l0:_ -> #b0:_ -> #t:_ -> then_:(_:squash hd -> action i0 disj_none l0 b0 t) ->
      #i1:_ -> #l1:_ -> #b1:_ -> else_:(_:squash (not hd) -> action i1 disj_none l1 b1 t) ->
      action (join_inv i0 i1) disj_none (join_loc l0 l1) (b0 || b1) t

  | Action_let:
      #i0:_ -> #l0:_ -> #b0:_ -> #t0:_ -> head:atomic_action i0 disj_none l0 b0 t0 ->
      #i1:_ -> #l1:_ -> #b1:_ -> #t1:_ -> k:(t0 -> action i1 disj_none l1 b1 t1) ->
      action (join_inv i0 i1) disj_none (join_loc l0 l1) (b0 || b1) t1

  | Action_act:
      #i0:_ -> #l0:_ -> #b0:_ -> act:action i0 disj_none l0 b0 unit ->
      action i0 disj_none l0 b0 bool


(* Denotation of action as A.action *)
[@@specialize]
val action_as_action
   (#i #d #l #b #t:_)
   (a:action i d l b t)
  : Tot (A.action (interp_inv i) (interp_disj d) (interp_loc l) b t)

(* Some AST nodes contain source comments that we propagate to the output *)
let comments = string

[@@ no_auto_projectors]
noeq
type typ
  : #nz:bool -> #wk:P.weak_kind ->
    P.parser_kind nz wk ->
    inv_index ->
    disj_index ->
    loc_index ->
    bool ->
    Type =
  | T_false:
      fieldname:string ->      
      typ P.impos_kind inv_none disj_none loc_none true

  | T_denoted :
      fieldname:string ->       
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #has_reader:_ -> #i:_ -> #disj:_ -> #l:_ ->
      td:dtyp pk has_reader i disj l ->
      typ pk i disj l has_reader

  | T_pair:
      first_fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #d1:_ -> #l1:_ -> #b1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #d2:_ -> #l2:_ -> #b2:_ ->
      t1:typ pk1 i1 d1 l1 b1 ->
      t2:typ pk2 i2 d2 l2 b2 ->
      typ (P.and_then_kind pk1 pk2) 
          (join_inv i1 i2)
          (join_disj d1 d2)
          (join_loc l1 l2)
          false

  | T_dep_pair:
      first_fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #d1:_ -> #l1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #d2:_ -> #l2:_ -> #b2:bool ->
      //the first component is a pre-denoted type with a reader
      t1:dtyp pk1 true i1 d1 l1 ->
      //the second component is a function from denotations of t1
      //that's why it's a small type, so that we can speak about its
      //denotation here
      t2:(dtyp_as_type t1 -> typ pk2 i2 d2 l2 b2) ->
      typ (P.and_then_kind pk1 pk2)
          (join_inv i1 i2)
          (join_disj d1 d2)
          (join_loc l1 l2)
          false

  | T_refine:
      fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #d1:_ -> #l1:_ ->
      //the first component is a pre-denoted type with a reader
      base:dtyp pk1 true i1 d1 l1 ->
      //the second component is a function from denotations of base
      //but notice that its codomain is bool, rather than expr
      //That's to ensure that the refinement is already well-typed
      refinement:(dtyp_as_type base -> bool) ->
      typ (P.filter_kind pk1) i1 d1 l1 false

  | T_refine_with_action:
      fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #d1:_ -> #l1:_ ->
      #i2:_ -> #d2:_ -> #l2:_ -> #b2:_ ->
      base:dtyp pk1 true i1 d1 l1 ->
      refinement:(dtyp_as_type base -> bool) ->
      act:(dtyp_as_type base -> action i2 d2 l2 b2 bool) ->
      typ (P.filter_kind pk1)
          (join_inv i1 i2)
          (join_disj d1 d2)
          (join_loc l1 l2)
          false
  
  | T_dep_pair_with_refinement:
      //This construct serves two purposes
      // 1. To avoid double fetches, we fold the refinement
      //    and dependent pair into a single form
      // 2. This allows the well-typedness of the continuation k
      //    to depend on the refinement of the first field
      first_fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #d1:_ -> #l1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #d2:_ -> #l2:_ -> #b2:_ ->
      //the first component is a pre-denoted type with a reader
      base:dtyp pk1 true i1 d1 l1 ->
      //the second component is a function from denotations of base
      refinement:(dtyp_as_type base -> bool) ->
      k:(x:dtyp_as_type base { refinement x } -> typ pk2 i2 d2 l2 b2) ->
      typ (P.and_then_kind (P.filter_kind pk1) pk2)
          (join_inv i1 i2)
          (join_disj d1 d2)
          (join_loc l1 l2)
          false

  | T_dep_pair_with_action:
      fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #d1:_ -> #l1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #d2:_ -> #l2:_ -> #b2:_ ->
      #i3:_ -> #d3:_ -> #l3:_ -> #b3:_ ->      
      base:dtyp pk1 true i1 d1 l1 ->
      k:(x:dtyp_as_type base -> typ pk2 i2 d2 l2 b2) ->
      act:(dtyp_as_type base -> action i3 d3 l3 b3 bool) ->
      typ (P.and_then_kind pk1 pk2)
          (join_inv i1 (join_inv i3 i2))
          (join_disj d1 (join_disj d3 d2))
          (join_loc l1 (join_loc l3 l2))
          false

  | T_dep_pair_with_refinement_and_action:
      //This construct serves two purposes
      // 1. To avoid double fetches, we fold the refinement
      //    and dependent pair and action into a single form
      // 2. This allows the well-typedness of the continuation k
      //    to depend on the refinement of the first field
      first_fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #d1:_ -> #l1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #d2:_ -> #l2:_ -> #b2:_ ->
      #i3:_ -> #d3:_ -> #l3:_ -> #b3:_ ->      
      //the first component is a pre-denoted type with a reader
      base:dtyp pk1 true i1 d1 l1 ->
      //the second component is a function from denotations of base
      refinement:(dtyp_as_type base -> bool) ->
      k:(x:dtyp_as_type base { refinement x } -> typ pk2 i2 d2 l2 b2) ->
      act:(dtyp_as_type base -> action i3 d3 l3 b3 bool) ->
      typ (P.and_then_kind (P.filter_kind pk1) pk2)
          (join_inv i1 (join_inv i3 i2))
          (join_disj d1 (join_disj d3 d2))
          (join_loc l1 (join_loc l3 l2))
          false

  | T_if_else:
      #nz1:_ -> #wk1:_ -> #pk1:P.parser_kind nz1 wk1 ->
      #l1:_ -> #i1:_ -> #d1:_ -> #b1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->      
      #l2:_ -> #i2:_ -> #d2:_ -> #b2:_ ->
      b:bool -> //A bool, rather than an expression
      t1:(squash b -> typ pk1 i1 d1 l1 b1) ->
      t2:(squash (not b) -> typ pk2 i2 d2 l2 b2) ->
      typ (P.glb pk1 pk2)
          (join_inv i1 i2)
          (join_disj d1 d2)
          (join_loc l1 l2) false

  | T_cases:
      #nz1:_ -> #wk1:_ -> #pk1:P.parser_kind nz1 wk1 ->
      #l1:_ -> #i1:_ -> #d1:_ -> #b1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->      
      #l2:_ -> #i2:_ -> #d2:_ -> #b2:_ ->
      b:bool -> //A bool, rather than an expression
      t1:typ pk1 i1 d1 l1 b1 ->
      t2:typ pk2 i2 d2 l2 b2 ->
      typ (P.glb pk1 pk2)
          (join_inv i1 i2)
          (join_disj d1 d2)
          (join_loc l1 l2)
          false

  | T_with_action:
      fieldname:string ->       
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #l1:_ -> #i1:_ -> #d1:_ -> #b1:_ ->
      #l2:_ -> #i2:_ -> #d2:_ -> #b2:_ ->
      base:typ pk i1 d1 l1 b1 ->
      act:action i2 d2 l2 b2 bool ->
      typ pk (join_inv i1 i2) (join_disj d1 d2) (join_loc l1 l2) false

  | T_with_dep_action:
      fieldname:string ->       
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #d1: _ -> #l1:_ ->
      #i2:_ -> #d2:_ -> #l2:_ -> #b2:_ ->
      head:dtyp pk1 true i1 d1 l1 ->
      act:(dtyp_as_type head -> action i2 d2 l2 b2 bool) ->
      typ pk1 (join_inv i1 i2) (join_disj d1 d2) (join_loc l1 l2) false

  | T_with_comment:
      fieldname:string ->       
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #l:_ -> #i:_ -> #d:_ -> #b:_ ->
      t:typ pk i d l b ->
      c:comments ->
      typ pk i d l b

  | T_nlist:
      fieldname:string ->       
      #pk:P.parser_kind true P.WeakKindStrongPrefix ->
      #i:_ -> #l:_ -> #d:_ -> #b:_ ->
      n:U32.t ->
      t:typ pk i d l b ->
      typ P.kind_nlist i d l false

  | T_at_most:
      fieldname:string ->       
      #nz:_ -> #pk:P.parser_kind nz P.WeakKindStrongPrefix ->
      #i:_ -> #d:_ -> #l:_ -> #b:_ ->
      n:U32.t ->
      t:typ pk i d l b ->
      typ P.kind_t_at_most i d l false

  | T_exact:
      fieldname:string ->       
      #nz:_ -> #pk:P.parser_kind nz P.WeakKindStrongPrefix ->
      #i:_ -> #d:_ -> #l:_ -> #b:_ ->
      n:U32.t ->
      t:typ pk i d l b ->
      typ P.kind_t_exact i d l false

  | T_string:
      fieldname:string ->       
      #pk1:P.parser_kind true P.WeakKindStrongPrefix ->
      element_type:dtyp pk1 true inv_none disj_none loc_none ->
      terminator:dtyp_as_type element_type ->
      typ P.parse_string_kind inv_none disj_none loc_none false


[@@specialize]
inline_for_extraction
let coerce (#[@@@erasable]a:Type)
           (#[@@@erasable]b:Type)
           ( [@@@erasable]pf:squash (a == b))
           (x:a) 
  : b 
  = x

[@@specialize]
val t_probe_then_validate
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

(* Type denotation of `typ` *)
val as_type
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #d #b
          (t:typ pk l i d b)
  : Tot Type0

(* Parser denotation of `typ` *)
val as_parser
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #d #b
          (t:typ pk l i d b)
  : P.parser pk (as_type t)

(* Serializer denotation of `typ` *)
val as_serializer
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #d #b
          (t:typ pk l i d b)
  : Tot (P.serializer (as_parser t))

[@@specialize]
val as_reader #nz (#pk:P.parser_kind nz P.WeakKindStrongPrefix)
                  (#[@@@erasable] inv:inv_index)
                  (#[@@@erasable] d:disj_index)
                  (#[@@@erasable] loc:loc_index)
                  (t:typ pk inv d loc true)
  : leaf_reader (as_parser t)

(* The main result:
   A validator denotation of `typ`
     related by construction to the parser
     and type denotations
*)
inline_for_extraction noextract 
val as_validator
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

[@@noextract_to "krml"; specialize]
inline_for_extraction noextract 
let validator_of #allow_reading #nz #wk (#k:P.parser_kind nz wk)
                 (#[@@@erasable] i:inv_index)
                 (#[@@@erasable] d:disj_index)
                 (#[@@@erasable] l:loc_index)
                 (t:typ k i d l allow_reading) = 
  A.validate_with_action_t
      (as_parser t) 
      (interp_inv i)
      (interp_disj d)
      (interp_loc l)
      allow_reading

[@@noextract_to "krml"; specialize]  
inline_for_extraction noextract   
let dtyp_of #nz #wk (#k:P.parser_kind nz wk)
            (#[@@@erasable] i:inv_index)
            (#[@@@erasable] d:disj_index)
            (#[@@@erasable] l:loc_index)
            #b (t:typ k i d l b) = 
  dtyp k b i d l

let specialization_steps =
  [nbe;
   zeta;
   primops;
   iota;
   delta_attr [`%specialize];
   delta_only ([`%Some?;
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
                `%Mktuple2?._2]@projector_names)]

let specialize_tac steps (_:unit)
  : T.Tac unit
  = let open FStar.List.Tot in
    T.norm (steps@specialization_steps);
    T.trefl()

[@@specialize]
let mk_global_binding #nz #wk 
                      (pk:P.parser_kind nz wk)
                      ([@@@erasable] inv:inv_index)
                      ([@@@erasable] disj:disj_index)
                      ([@@@erasable] loc:loc_index)
                      ([@@@erasable] p_t : Type0)
                      ([@@@erasable] p_p : P.parser pk p_t)
                      ((*[@@@erasable]*) p_s : P.serializer p_p)
                      (p_reader: option (leaf_reader p_p))
                      (b:bool)
                      (p_v : A.validate_with_action_t p_p 
                              (interp_inv inv)
                              (interp_disj disj)
                              (interp_loc loc) b)
                      ([@@@erasable] pf:squash (b == Some? p_reader))
   : global_binding
   = {
       parser_kind_nz = nz;
       parser_weak_kind = wk;
       parser_kind = pk;
       inv = inv;
       disj;
       loc = loc;
       p_t = p_t;
       p_p = p_p;
       p_s = p_s;
       p_reader = p_reader;
       p_v = p_v
     }

[@@specialize]
let mk_dt_app #nz #wk (pk:P.parser_kind nz wk) (b:bool)
              ([@@@erasable] inv:inv_index)
              ([@@@erasable] disj:disj_index)
              ([@@@erasable] loc:loc_index)
              (x:global_binding)
              ([@@@erasable] pf:squash (nz == nz_of_binding x /\
                                        wk == wk_of_binding x /\
                                        pk == pk_of_binding x /\
                                        b == has_reader x /\
                                        inv == inv_of_binding x /\
                                        disj == disj_of_bindng x /\
                                        loc == loc_of_binding x))
    : dtyp #nz #wk pk b inv disj loc
    = DT_App pk b inv disj loc x pf


[@@specialize]
let mk_dtyp_app #nz #wk 
                (pk:P.parser_kind nz wk)
                ([@@@erasable] inv:inv_index)
                ([@@@erasable] disj:disj_index)
                ([@@@erasable] loc:loc_index)
                ([@@@erasable] p_t : Type0)
                ([@@@erasable] p_p : P.parser pk p_t)
                ((*[@@@erasable]*) p_s : P.serializer p_p)
                (p_reader: option (leaf_reader p_p))
                (b:bool)
                (p_v : A.validate_with_action_t p_p 
                        (interp_inv inv)
                        (interp_disj disj)
                        (interp_loc loc)
                        b)
                ([@@@erasable] pf:squash (b == Some? p_reader))
   : dtyp #nz #wk pk b inv disj loc
   = let gb = {
       parser_kind_nz = nz;
       parser_weak_kind = wk;
       parser_kind = pk;
       inv = inv;
       disj;
       loc = loc;
       p_t = p_t;
       p_p = p_p;
       p_s = p_s;
       p_reader = p_reader;
       p_v = p_v
     } in
     DT_App pk b inv disj loc gb ()

//attribute to tag disjointness indexes of type definitions
let specialize_disjointness = ()
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
                               `%join_disj;
                              ]);
           delta_attr [`%specialize_disjointness];                  
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
                        `%mk_global_binding]@projector_names);
          zeta; 
          iota;
          simplify];
  T.trivial()

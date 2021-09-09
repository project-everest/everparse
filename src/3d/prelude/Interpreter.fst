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
module Interpreter
module U32 = FStar.UInt32
module LPL = EverParse3d.InputBuffer
module B = LowStar.Buffer
module A = Actions
module P = Prelude

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
    a very simple class of types---just the primitive integer types *)
    
(* Primitive integer types *)
type itype =
  | UInt8
  | UInt16
  | UInt32
  | UInt64

(* Interpretation of itype as an F* type *)
let itype_as_type (i:itype) 
  : Type 
  = match i with
    | UInt8 -> P.___UINT8
    | UInt16 -> P.___UINT16
    | UInt32 -> P.___UINT32
    | UInt64 -> P.___UINT64

(* Interpretation of itype as a parser kind *)
let parser_kind_of_itype (i:itype) 
  : P.parser_kind true P.WeakKindStrongPrefix
  = match i with
    | UInt8 -> P.kind____UINT8
    | UInt16 -> P.kind____UINT16
    | UInt32 -> P.kind____UINT32
    | UInt64 -> P.kind____UINT64

(* Interpretation of an itype as a parser *)
let itype_as_parser (i:itype) 
  : P.parser (parser_kind_of_itype i) (itype_as_type i)
  = match i with
    | UInt8 -> P.parse____UINT8
    | UInt16 -> P.parse____UINT16
    | UInt32 -> P.parse____UINT32
    | UInt64 -> P.parse____UINT64

(* Interpretation of an itype as a leaf reader *)
[@@specialize]
let itype_as_leaf_reader (i:itype)
  : A.leaf_reader (itype_as_parser i)
  = match i with
    | UInt8 -> A.read____UINT8
    | UInt16 -> A.read____UINT16
    | UInt32 -> A.read____UINT32
    | UInt64 -> A.read____UINT64

(* Interpretation of an itype as a validator
   -- Notice that the type shows that it is related to the parser *)
[@@specialize]
let itype_as_validator (i:itype)
  : A.validate_with_action_t (itype_as_parser i) A.true_inv A.eloc_none true
  = match i with
    | UInt8 -> A.validate____UINT8
    | UInt16 -> A.validate____UINT16
    | UInt32 -> A.validate____UINT32
    | UInt64 -> A.validate____UINT64


(* Our first order of business to scale this up to 3D is to set up
   definitions for type contexts.

   A 3D program is a sequence of top-level definitions, where a given
   definition may reference terms defined previously. To model this,
   we'll given a denotation of programs in a _context_, where the
   context provides denotations for all the names defined previously
   which are in scope.

   One interesting wrinkle is that type definitions in 3D are
   parameterized by an arbitrary number of parameters. So, each name
   in the context can have a denotation of a different arity---we'll
   model that with a bit of generic programming.

   Limitation: For now, we restrict the type of parameters to be
   primitive integer types or pointers to parameter types.

   TODO: We should lift this restriction to allow typedefs on
   parameter types, and eventually to also support output types.
*)

(* A parameter type is either an primitive integer
   or a pointer to a parameter type *)
type param_type = 
  | IT_Base of itype
  | IT_Pointer of param_type

(* Denotation of a param_type *)
let rec param_type_as_type (i:param_type) 
  : Type0
  = match i with
    | IT_Base i -> itype_as_type i
    | IT_Pointer t -> B.pointer (param_type_as_type t)

(* `args_of ps` is a nested pair, each of whose elements
   has a type corresponding to the denotation of the
   the ith parameter type in ps *)
let rec args_of (ps:list param_type) = 
  match ps with
  | [] -> unit
  | i::ps -> param_type_as_type i & args_of ps

(* `arrow ps res` is a non-dependent curried arrow from
   each of the parameters in ps to res *)
let rec arrow (is:list param_type) (res:Type u#a)
  : Type u#a
  = match is with
    | [] -> res
    | i::is -> param_type_as_type i -> arrow is res

(* Just an example to show the `arrow` type at work *)
let _illustrate_int_to_int = arrow [IT_Base UInt8] P.___UINT8
let _illustrate_int_to_int_inhabitant 
  : _illustrate_int_to_int 
  = fun (x:P.___UINT8) -> x

(* Coercion for nullary arrows --- useful in some proofs *)
[@@specialize]
let nullary_arrow (#res:Type u#a) (f:arrow [] res)
  : res
  = f

(* Eliminating a single arrow by applying it
   --- useful in some proofs, rather than just writing `f x` *)
[@@specialize]
let apply (#i:param_type)
          (#is:list param_type)
          (#res:Type u#a)
          (f:arrow (i::is) res)
          (x:param_type_as_type i)
    : arrow is res
    = f x

(* Eliminating an arrow entirely by applying 
   it to arguments for all its parameters *)
[@@specialize]
let rec apply_arrow (#is:list param_type)
                    (#k:Type)
                    (f: arrow is k)
                    (args: args_of is)
  : k
  = match is with
    | [] -> nullary_arrow f
    | i::is -> apply_arrow (apply f (fst (args <: args_of (i::is)))) (snd (args <: args_of (i::is)))

(* `dep_arrow ps f` is a dependent, curried arrow from each of the
   parameters in `ps` to to `f args` where `args : args_of ps`
   collects the bound variables of each dependent arrow *)
let rec dep_arrow (is:list param_type) (f:args_of is -> Type)
  = match is with 
    | [] -> 
      assert_norm (args_of is == unit);
      f ()
    | i::is ->
      assert_norm (args_of (i::is) == (param_type_as_type i & args_of is));
      x:param_type_as_type i ->
      dep_arrow is (fun xs -> f (x, xs))

(* Again, some examples to illustrate. A little harder to work with, but not impossible *)
let _illustrate_eq_fun_t = x:P.___UINT8 -> y:P.___UINT8 { y == x }
let _illustrate_eq_fun_t_inhabitant : _illustrate_eq_fun_t = fun x -> x
let _illustrate_dep_int_to_int = dep_arrow [IT_Base UInt8] (fun x -> y:P.___UINT8{y == fst x})
let _coerce_eq (a b:Type) (_:squash (a == b)) (x:a) : b = x
let _illustrate_dep_int_to_int_inhabitant 
  : _illustrate_dep_int_to_int
  = assert_norm (_illustrate_dep_int_to_int == _illustrate_eq_fun_t); 
    _coerce_eq _ _ () _illustrate_eq_fun_t_inhabitant    
    

(* Eliminate a single dep_arrow into a native dependent -> *) 
[@@specialize]
let apply_dep_arrow_cons (i:_) (is:_)
                         (k: args_of (i::is) -> Type)
                         (f: dep_arrow (i::is) k)
   : x:param_type_as_type i -> dep_arrow is (fun (xs:args_of is) -> k (x, xs))
   = f

(* Eliminate a dep_arrow completely by applying to 
   all its arguments *)
[@@specialize]
let rec apply_dep_arrow (param_types:list param_type)
                        (k: args_of param_types -> Type)
                        (f: dep_arrow param_types k)
                        (args: args_of param_types)
  : k args
  = match param_types with
    | [] -> 
      assert_norm (args_of [] == unit);
      (f <: dep_arrow [] k)
    | i::is ->
      assert_norm (args_of (i::is) == param_type_as_type i & args_of is);
      let f : dep_arrow (i::is) k = f in
      let args : args_of (i::is) = args in
      apply_dep_arrow
        is 
        (fun xs -> k (fst args, xs))
        (apply_dep_arrow_cons _ _ _ f (fst args))
        (snd args)

(* Identifiers of top-level terms in 3D.
   TODO: should be qualified by a module name *)
let ident = string

(* Now, we can define the type of an environment *)

#push-options "--__temp_no_proj Interpreter"
(* global_binding: A single entry in the environment *)
noeq
type global_binding = {
  // The name being bound
  name : ident; 
  //Its parameter types  
  param_types: list param_type;
  //Parser metadata
  parser_kind_nz:bool; // Does it consume non-zero bytes?
  parser_weak_kind: P.weak_kind;
  parser_kind: P.parser_kind parser_kind_nz parser_weak_kind;
  //Memory invariant of any actions it contains
  inv:arrow param_types A.slice_inv;
  //Write footprint of any of its actions
  loc:arrow param_types A.eloc;
  //Whether the type can be read -- to avoid double fetches
  allow_reading:bool;
  //Its type denotation
  p_t : arrow param_types Type0;
  //Its parser denotation
  p_p : dep_arrow param_types
          (fun (args:args_of param_types) ->
            P.parser parser_kind (apply_arrow p_t args));
  //Its validate-with-action denotationa          
  p_v : dep_arrow param_types 
          (fun args ->
            A.validate_with_action_t (apply_dep_arrow _ _ p_p args)
                                     (apply_arrow inv args)
                                     (apply_arrow loc args)
                                     allow_reading)
}
#pop-options

let globals = list global_binding

[@@specialize]
let lookup (env:globals) (name:ident) 
  : option global_binding
  = List.Tot.tryFind (fun b -> b.name = name) env

(** Now we define the AST of 3D programs *)

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
  : A.slice_inv -> A.eloc -> bool -> Type0 -> Type =
  | Action_return:
      #a:Type0 ->
      x:a ->
      atomic_action A.true_inv A.eloc_none false a

  | Action_abort:
      atomic_action A.true_inv A.eloc_none false bool
  
  | Action_field_pos:
      atomic_action A.true_inv A.eloc_none false U32.t
      
  | Action_field_ptr: 
      atomic_action A.true_inv A.eloc_none true LPL.puint8
      
  | Action_deref:
      #a:Type0 ->
      x:B.pointer a ->
      atomic_action (A.ptr_inv x) A.eloc_none false a
      
  | Action_assignment:
      #a:Type0 ->
      x:B.pointer a ->
      rhs:a ->
      atomic_action (A.ptr_inv x) (A.ptr_loc x) false unit

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
    | Action_field_pos ->
      A.action_field_pos ()
    | Action_field_ptr ->
      A.action_field_ptr ()
    | Action_deref x ->
      A.action_deref x
    | Action_assignment x rhs -> 
      A.action_assignment x rhs

(* A sub-language of monadic actions. 

   The indexing structure mirrors the indexes of the combinators in
   Actions.fst 
*)
noeq
type action 
  : A.slice_inv -> A.eloc -> bool -> Type0 -> Type =
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
      #i0:_ -> #l0:_ -> #b0:_ -> #t:_ -> then_:action i0 l0 b0 t ->
      #i1:_ -> #l1:_ -> #b1:_ -> else_:action i1 l1 b1 t ->
      action (A.conj_inv i0 i1) (A.eloc_union l0 l1) (b0 || b1) t
      
  | Action_let: 
      #i0:_ -> #l0:_ -> #b0:_ -> #t0:_ -> head:atomic_action i0 l0 b0 t0 ->
      #i1:_ -> #l1:_ -> #b1:_ -> #t1:_ -> k:(t0 -> action i1 l1 b1 t1) ->
      action (A.conj_inv i0 i1) (A.eloc_union l0 l1) (b0 || b1) t1

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
      let then_ (_:squash hd) = action_as_action p t in
      let else_ (_:squash (not hd)) = action_as_action p e in
      A.action_ite hd then_ else_
      
    | Action_let hd k ->
      let head = atomic_action_as_action p hd in
      let k x = action_as_action p (k x) in
      A.action_bind "" head k

(* Some AST nodes contain source comments that we propagate to the output *)
let comments = list string

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
type typ (env:globals) 
  : #nz:bool -> #wk:P.weak_kind ->
    P.parser_kind nz wk ->
    A.slice_inv ->
    A.eloc ->
    bool ->
    Type =
  | T_false:
      typ env P.impos_kind
              A.true_inv
              A.eloc_none
              true
  
  | T_pair:
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #i1:_ -> #l1:_ -> #b1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #i2:_ -> #l2:_ -> #b2:_ ->
      t1:typ env pk1 i1 l1 b1 ->
      t2:typ env pk2 i2 l2 b2 ->
      typ env (P.and_then_kind pk1 pk2)
              (A.conj_inv i1 i2)
              (A.eloc_union l1 l2)
              false
                 
  | T_app:
      hd:ident { Some? (lookup env hd) } -> //The name must be bound in env
      args:args_of (Some?.v (lookup env hd)).param_types ->
      typ env (Some?.v (lookup env hd)).parser_kind
              (apply_arrow (Some?.v (lookup env hd)).inv args)                     
              (apply_arrow (Some?.v (lookup env hd)).loc args)
              (Some?.v (lookup env hd)).allow_reading
                     
  | T_dep_pair:
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #l1:_ -> #i1:_ -> #b2:_ -> 
      //the first component is a small type      
      t1:itype ->
      //the second component is a function from denotations of t1
      //that's why it's a small type, so that we can speak about its
      //denotation here
      t2:(itype_as_type t1 -> typ env pk2 i1 l1 b2) ->
      typ env (P.and_then_kind (parser_kind_of_itype t1) pk2)
              i1
              l1 
              false
               
  | T_refine:
      //the first component is a small type  
      base:itype ->
      //the second component is a function from denotations of t1
      //but notice that its codomain is bool, rather than expr
      //That's to ensure that the refinement is already well-typed
      refinement:(itype_as_type base -> bool) ->
      typ env (P.filter_kind (parser_kind_of_itype base))
              A.true_inv
              A.eloc_none
              false
               
  | T_if_else:
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #l1:_ -> #i1:_ -> #b1:_ ->
      #l2:_ -> #i2:_ -> #b2:_ ->
      b:bool -> //A bool, rather than an expression
      t1:typ env pk i1 l1 b1 ->
      t2:typ env pk i2 l2 b2 ->      
      typ env pk 
              (A.conj_inv i1 i2)
              (A.eloc_union l1 l2)
              false
               
  | T_with_action:
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #l1:_ -> #i1:_ -> #b1:_ ->
      #l2:_ -> #i2:_ -> #b2:_ ->
      base:typ env pk i1 l1 b1 ->
      act:action i2 l2 b2 bool ->
      typ env pk 
              (A.conj_inv i1 i2)
              (A.eloc_union l1 l2)
              false
                 
  | T_with_dep_action:
      #l:_ -> #i:_ -> #b:_ ->
      head:itype -> //dependent actoin, again head is a small type
      act:(itype_as_type head -> action i l b bool) ->
      typ env (parser_kind_of_itype head)
              i
              l
              false
                     
  | T_with_comment:
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #l:_ -> #i:_ -> #b:_ ->
      t:typ env pk i l b ->
      c:comments ->
      typ env pk i l b

(* Type denotation of `typ` *)
let rec as_type 
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #b #g
          (t:typ g pk l i b)
  : Tot Type0
    (decreases t)
  = match t with
    | T_false -> False

    | T_pair t1 t2 ->
      as_type t1 & as_type t2

    | T_dep_pair i t -> 
      x:itype_as_type i & as_type (t x)
      
    | T_refine base refinement -> 
      Prelude.refine (itype_as_type base) refinement

    | T_if_else b t0 t1 -> 
      Prelude.t_ite b (as_type t0) (as_type t1)

    | T_with_action t _
    | T_with_comment t _ -> 
      as_type t

    | T_with_dep_action i _ ->
      itype_as_type i

    | T_app hd args -> 
      apply_arrow (Some?.v (lookup g hd)).p_t args

module T = FStar.Tactics

(* Parser denotation of `typ` *)
let rec as_parser 
          #nz #wk (#pk:P.parser_kind nz wk)
          #l #i #b #g
          (t:typ g pk l i b)
  : Tot (P.parser pk (as_type t))
        (decreases t)
  = match t returns Tot (P.parser pk (as_type t)) with
    | T_false -> 
      //assert_norm (as_type g T_false == False);
      P.parse_impos()

    | T_pair t1 t2 -> 
      //assert_norm (as_type g (T_pair t1 t2) == as_type g t1 * as_type g t2);
      let p1 = as_parser t1 in
      let p2 = as_parser t2 in
      P.parse_pair p1 p2

    | T_dep_pair i t ->
      //assert_norm (as_type g (T_dep_pair i t) == x:itype_as_type i & as_type g (t x));      
      let pi = itype_as_parser i in
      P.parse_dep_pair pi (fun (x:itype_as_type i) -> as_parser (t x))

    | T_refine base refinement ->
      //assert_norm (as_type g (T_refine base refinement) == Prelude.refine (itype_as_type base) refinement);
      let pi = itype_as_parser base in
      P.parse_filter pi refinement

    | T_if_else b t0 t1 -> 
      //assert_norm (as_type g (T_if_else b t0 t1) == Prelude.t_ite b (as_type g t0) (as_type g t1));
      let p0 (_:squash b) = as_parser t0 in
      let p1 (_:squash (not b)) = as_parser t1 in
      P.parse_ite b p0 p1

    | T_with_action t a ->
      //assert_norm (as_type g (T_with_action t a) == as_type g t);
      as_parser t
      
    | T_with_dep_action i a ->
      //assert_norm (as_type g (T_with_dep_action i a) == itype_as_type i);
      itype_as_parser i
      
    | T_with_comment t c -> 
      //assert_norm (as_type g (T_with_comment t c) == as_type g t);      
      as_parser t

    | T_app hd args ->
      //assert_norm (as_type g (T_app hd args) == apply_arrow (Some?.v (lookup g hd)).p_t args);
      apply_dep_arrow _ _ (Some?.v (lookup g hd)).p_p args


(* The main result: 
   A validator denotation of `typ`
     related by construction to the parser
     and type denotations
*)
[@@specialize]
let rec as_validator
          #nz #wk (#pk:P.parser_kind nz wk)
          #loc #inv #b (#g:globals)
          (t:typ g pk inv loc b)
  : Tot (A.validate_with_action_t #nz #wk #pk #(as_type t) (as_parser t) inv loc b)
        (decreases t)
  = match t
    returns Tot (A.validate_with_action_t (as_parser t) inv loc b)
    with
    | T_false -> 
      A.validate_impos()

    | T_pair t1 t2 -> 
      assert_norm (as_type (T_pair t1 t2) == as_type t1 * as_type t2);
      assert_norm (as_parser (T_pair t1 t2) == P.parse_pair (as_parser t1) (as_parser t2));
      A.validate_pair ""
        (as_validator t1)
        (as_validator t2)

    | T_dep_pair i t ->
      assert_norm (as_type (T_dep_pair i t) == x:itype_as_type i & as_type (t x));
      assert_norm (as_parser (T_dep_pair i t) == 
                   P.parse_dep_pair (itype_as_parser i) (fun (x:itype_as_type i) -> as_parser (t x)));
      A.validate_weaken_inv_loc inv loc
      (A.validate_dep_pair ""
        (itype_as_validator i)
        (itype_as_leaf_reader i)
        (fun x -> as_validator (t x)))

    | T_refine t f -> 
      A.validate_filter "" 
        (itype_as_validator t)
        (itype_as_leaf_reader t)
        f "" ""

    | T_if_else b t0 t1 -> 
      assert_norm (as_type (T_if_else b t0 t1) == Prelude.t_ite b (as_type t0) (as_type t1));
      let p0 (_:squash b) = as_parser t0 in
      let p1 (_:squash (not b)) = as_parser t1 in
      assert_norm (as_parser (T_if_else b t0 t1) == P.parse_ite b p0 p1);
      let v0 (_:squash b) = as_validator t0 in
      let v1 (_:squash (not b)) = as_validator t1 in      
      A.validate_ite b p0 v0 p1 v1
        
    | T_with_action t a ->
      assert_norm (as_type (T_with_action t a) == as_type t);
      assert_norm (as_parser (T_with_action t a) == as_parser t);      
      A.validate_with_success_action ""
        (as_validator t)
        (action_as_action (as_parser t) a)

    | T_with_dep_action i a ->
      assert_norm (as_type (T_with_dep_action i a <: typ g _ _ _ _) == itype_as_type i);
      assert_norm (as_parser (T_with_dep_action i a <: typ g _ _ _ _) == itype_as_parser i);      
      A.validate_weaken_inv_loc inv loc (
       A.validate_with_dep_action ""
        (itype_as_validator i)
        (itype_as_leaf_reader i)
        (fun x -> action_as_action (itype_as_parser i) (a x)))

    | T_with_comment t c ->
      assert_norm (as_type (T_with_comment t c) == as_type t);
      assert_norm (as_parser (T_with_comment t c) == as_parser t);      
      A.validate_with_comment "" (as_validator t)
      
    | T_app hd args ->
      // assert_norm (as_type (T_app hd args) == apply_arrow (Some?.v (lookup hd)).p_t args);
      // assert_norm (as_parser (T_app hd args) == apply_dep_arrow_uncurred _ _ (Some?.v (lookup hd)).p_p args);
      apply_dep_arrow _ _ (Some?.v (lookup g hd)).p_v args

let specialize_tac ()
  : T.Tac unit
  = T.norm [zeta; iota; delta_attr [`%specialize]; delta_only [`%List.Tot.tryFind]];
    T.trefl()

[@@specialize]
let emp : globals = []

[@@specialize]
let u8_pair
  : typ emp _ _ _ _
  = T_pair (T_refine UInt8 (fun _ -> true))
           (T_refine UInt8 (fun _ -> true))

[@@T.postprocess_with specialize_tac]
let validate_u8_pair
  = as_validator u8_pair

(* In emacs, C-c C-s C-p shows the definition of validate_u8_pair as:

Actions.validate_pair ""
    (Actions.validate_filter "" Actions.validate____UINT8 Actions.read____UINT8 (fun _ -> true) "" "")
    (Actions.validate_filter "" Actions.validate____UINT8 Actions.read____UINT8 (fun _ -> true) "" "")
*)

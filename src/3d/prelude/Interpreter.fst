module Interpreter
module A = Actions

type integer_type =
  | UInt8
  | UInt16
  | UInt32
  | UInt64

/// The same as A.op, but with `SizeOf` removed
/// and arithmetic operators resolved to their types
type op =
  | Eq
  | Neq
  | And
  | Or
  | Not
  | Plus of integer_type
  | Minus of integer_type
  | Mul of integer_type
  | Division of integer_type
  | Remainder of integer_type
  | BitwiseAnd of integer_type
  | BitwiseXor of integer_type
  | BitwiseOr of integer_type
  | BitwiseNot of integer_type
  | ShiftRight of integer_type
  | ShiftLeft of integer_type
  | LT of integer_type
  | GT of integer_type
  | LE of integer_type
  | GE of integer_type
  | IfThenElse
  | BitFieldOf of int //BitFieldOf(i, from, to)
  | Cast : from:integer_type -> to:integer_type -> op
  | Ext of string

type itype = integer_type

let itype_as_type (i:itype) : Type = int

type constant : Type -> Type =
  | Unit : constant unit
  | Int  : i:itype -> int -> constant (itype_as_type i)
  | XInt : i:itype -> string -> constant (itype_as_type i)   //hexadecimal constants
  | Bool : bool -> constant bool

/// Same as A.expr, but with `This` removed
///
/// Carrying around the range information from AST.expr so that we
///   can report errors in terms of their 3d file locations

let ident = string

assume
val expr : Type0

type lam a = option ident & a
module U32 = FStar.UInt32
module LPL = EverParse3d.InputBuffer
module B = LowStar.Buffer
noeq
type atomic_action : A.eloc -> A.slice_inv -> bool -> Type0 -> Type =
  | Action_return    : a:Type0 -> x:a -> atomic_action A.eloc_none A.true_inv false a
  | Action_abort     : atomic_action A.eloc_none A.true_inv false unit
  | Action_field_pos : atomic_action A.eloc_none A.true_inv false U32.t
  | Action_field_ptr : atomic_action A.eloc_none A.true_inv true LPL.puint8
  | Action_deref     : a:Type0 -> x:B.pointer a -> atomic_action A.eloc_none (A.ptr_inv x) false a
  | Action_assignment : a:Type0 -> x:B.pointer a -> rhs:a -> atomic_action (A.ptr_loc x) (A.ptr_inv x) false unit

noeq
type action : A.eloc -> A.slice_inv -> bool -> Type0 -> Type =
  | Atomic_action : l:_ -> i:_ -> b:_ -> t:_ -> atomic_action l i b t -> action l i b t
  | Action_seq : l0:_ -> i0:_ -> b0:_ -> hd:atomic_action l0 i0 b0 unit
               -> l1:_ -> i1:_ -> b1:_ -> t:_ -> tl:action l1 i1 b1 t 
               -> action (A.eloc_union l0 l1) 
                        (A.conj_inv i0 i1)
                        (b0 || b1)
                        t
  | Action_ite : hd:bool 
               -> l0:_ -> i0:_ -> b0:_ -> t:_ -> then_:action l0 i0 b0 t
               -> l1:_ -> i1:_ -> b1:_ -> else_:action l1 i1 b1 t
               -> action (A.eloc_union l0 l1) 
                        (A.conj_inv i0 i1)
                        (b0 || b1)
                        t
  | Action_let: l0:_ -> i0:_ -> b0:_ -> t0:_ -> head:atomic_action l0 i0 b0 t0
              -> l1:_ -> i1:_ -> b1:_ -> t1:_ -> k:(t0 -> action l1 i1 b1 t1)
              -> action (A.eloc_union l0 l1) 
                       (A.conj_inv i0 i1)
                       (b0 || b1)
                       t1

let comments = list string


type index_type = 
  | IT_Base of integer_type
  | IT_Pointer of index_type

let index_typ_as_type (i:index_type) 
  : Type0
  = match i with
    | IT_Base _ -> int
    | _ -> False

let rec args_of (is:list index_type) = 
  match is with
  | [] -> unit
  | i::is -> index_typ_as_type i & args_of is


let rec arrow (is:list index_type) (res:Type u#a)
  : Type u#a
  = match is with
    | [] -> res
    | i::is -> index_typ_as_type i -> arrow is res


let rec dep_arrow_uncurried (is:list index_type) (f:args_of is -> Type)
  = match is with 
    | [] -> 
      assert_norm (args_of is == unit);
      f ()
    | i::is ->
      assert_norm (args_of (i::is) == (index_typ_as_type i & args_of is));
      x:index_typ_as_type i ->
      dep_arrow_uncurried is (fun xs -> f (x, xs))
    
let int_to_int = arrow [IT_Base UInt8] int
let test : int_to_int = (fun (x:int) -> x)

let nullary_arrow (#res:Type u#a) (f:arrow [] res)
  : res
  = f
  
let apply (#i:index_type)
          (#is:list index_type)
          (#res:Type u#a)
          (f:arrow (i::is) res)
          (x:index_typ_as_type i)
    : arrow is res
    = f x
    
let rec dep_arrow (is:list index_type)
                  (res: arrow u#(a + 1) is (Type u#a))
  : Type u#a
  = match is with
    | [] -> nullary_arrow res
    | i::is -> x:index_typ_as_type i -> (dep_arrow is (apply res x))


let rec apply_arrow (#is:list index_type)
                    (#k:Type)
                    (f: arrow is k)
                    (args: args_of is)
  = match is with
    | [] -> nullary_arrow f
    | i::is -> apply_arrow (apply f (fst (args <: args_of (i::is)))) (snd (args <: args_of (i::is)))


let apply_dep_arrow_uncurried_cons (i:_) (is:_)
                                   (k: args_of (i::is) -> Type)
                                   (f: dep_arrow_uncurried (i::is) k)
   : x:index_typ_as_type i -> dep_arrow_uncurried is (fun (xs:args_of is) -> k (x, xs))
   = f

let rec apply_dep_arrow_uncurred (param_types:list index_type)
                                 (k: args_of param_types -> Type)
                                 (f: dep_arrow_uncurried param_types k)
                                 (args: args_of param_types)
  : k args
  = match param_types with
    | [] -> 
      assert_norm (args_of [] == unit);
      (f <: dep_arrow_uncurried [] k)
    | i::is ->
      assert_norm (args_of (i::is) == index_typ_as_type i & args_of is);
      let f : dep_arrow_uncurried (i::is) k = f in
      let args : args_of (i::is) = args in
      apply_dep_arrow_uncurred 
        is 
        (fun xs -> k (fst args, xs))
        (apply_dep_arrow_uncurried_cons _ _ _ f (fst args))
        (snd args)

module P = Prelude

#push-options "--__temp_no_proj Interpreter"
noeq
type global_binding = {
  name : ident;
  param_types: list index_type;
  parser_kind_nz:bool;
  parser_weak_kind: P.weak_kind;
  parser_kind: P.parser_kind parser_kind_nz parser_weak_kind;
  inv:arrow param_types A.slice_inv;
  loc:arrow param_types A.eloc;
  allow_reading:bool;
  p_t : arrow param_types Type0;
  p_p : dep_arrow_uncurried 
          param_types
          (fun (args:args_of param_types) -> P.parser parser_kind (apply_arrow p_t args));
  p_v : dep_arrow_uncurried
          param_types 
          (fun args -> A.validate_with_action_t (apply_dep_arrow_uncurred _ _ p_p args) (apply_arrow inv args) (apply_arrow loc args) allow_reading)
}
#pop-options

let globals = list global_binding

assume
val lookup (env:globals) (name:ident) 
  : option global_binding

assume
val parser_kind_of_itype (i:itype) : P.parser_kind true P.WeakKindStrongPrefix

(* A subset of F* types that the translation targets *)
noeq
type typ (env:globals) 
  : #nz:bool -> #wk:P.weak_kind -> P.parser_kind nz wk
  -> A.eloc -> A.slice_inv -> bool -> Type =
  | T_false    : typ env P.impos_kind A.eloc_none A.true_inv true
  
  | T_pair     : #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix 
               -> #l1:_ ->#i1:_ -> #b1:_ -> typ env pk1 l1 i1 b1
               -> #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 
               -> #l2:_ ->#i2:_ -> #b2:_ -> typ env pk2 l2 i2 b2
               -> typ env (P.and_then_kind pk1 pk2)
                         (A.eloc_union l1 l2)
                         (A.conj_inv i1 i2)
                         false
                 
  | T_app      : hd:ident { Some? (lookup env hd) }
               -> args:args_of (Some?.v (lookup env hd)).param_types 
               -> typ env 
                     (Some?.v (lookup env hd)).parser_kind
                     (apply_arrow (Some?.v (lookup env hd)).loc args)
                     (apply_arrow (Some?.v (lookup env hd)).inv args)                     
                     (Some?.v (lookup env hd)).allow_reading
                     
  | T_dep_pair : dfst:itype
               -> #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2
               -> #l1:_ -> #i1:_ -> #b2:_ -> dsnd:(itype_as_type dfst -> typ env pk2 l1 i1 b2) 
               -> typ env (P.and_then_kind (parser_kind_of_itype dfst) pk2)
                         l1 i1 false
               
  | T_refine   : base:itype
               -> refinement:(itype_as_type base -> bool)
               -> typ env (P.filter_kind (parser_kind_of_itype base)) A.eloc_none A.true_inv false
               
  | T_if_else  : b:bool 
               -> #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk
               -> #l1:_ -> #i1:_ -> #b1:_ -> t1:typ env pk l1 i1 b1
               -> #l2:_ -> #i2:_ -> #b2:_ -> t2:typ env pk l2 i2 b2
               -> typ env pk (A.eloc_union l1 l2) (A.conj_inv i1 i2) false
               
  | T_pointer  : typ env P.impos_kind A.eloc_none A.true_inv false
               -> typ env P.impos_kind A.eloc_none A.true_inv false
  
  | T_with_action: #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk
                 -> #l1:_ -> #i1:_ -> #b1:_ -> typ env pk l1 i1 b1
                 -> #l2:_ -> #i2:_ -> #b2:_ -> action l2 i2 b2 bool
                 -> typ env pk (A.eloc_union l1 l2) (A.conj_inv i1 i2) false
                 
  | T_with_dep_action: head:itype 
                   -> #l:_ -> #i:_ -> #b:_ -> (itype_as_type head -> action l i b bool)
                   -> typ env (parser_kind_of_itype head) l i false
                     
  | T_with_comment: #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk 
                  -> #l:_ -> #i:_ -> #b:_ -> typ env pk l i b
                  -> comments
                  -> typ env pk l i b


let rec as_type #nz #wk (#pk:P.parser_kind nz wk) #l #i #b (g:globals) (t:typ g pk l i b)
  : Tot Type0
    (decreases t)
  = match t with
    | T_false -> False

    | T_pair t1 t2 ->
      as_type g t1 & as_type g t2

    | T_dep_pair i t -> 
      x:itype_as_type i & as_type g (t x)
      
    | T_refine base refinement -> 
      Prelude.refine (itype_as_type base) refinement

    | T_if_else b t0 t1 -> 
      Prelude.t_ite b (as_type g t0) (as_type g t1)

    | T_pointer t -> 
      B.pointer (as_type g t)

    | T_with_action t _
    | T_with_comment t _ -> 
      as_type g t

    | T_with_dep_action i _ ->
      itype_as_type i

    | T_app hd args -> 
      let Some binding = lookup g hd in
      apply_arrow binding.p_t args

assume
val itype_as_parser (i:itype) 
  : P.parser (parser_kind_of_itype i) (itype_as_type i)
module T = FStar.Tactics

let rec as_parser #nz #wk (#pk:P.parser_kind nz wk) #l #i #b (g:globals) (t:typ g pk l i b)
  : Tot (P.parser pk (as_type g t))
        (decreases t)
  = match t returns Tot (P.parser pk (as_type g t)) with
    | T_false -> 
      assert_norm (as_type g T_false == False);
      P.parse_impos()

    | T_pair t1 t2 -> 
      assert_norm (as_type g (T_pair t1 t2) == as_type g t1 * as_type g t2);
      let p1 = as_parser g t1 in
      let p2 = as_parser g t2 in
      P.parse_pair p1 p2

    | T_dep_pair i t ->
      assert_norm (as_type g (T_dep_pair i t) == x:itype_as_type i & as_type g (t x));      
      let pi = itype_as_parser i in
      P.parse_dep_pair pi (fun (x:itype_as_type i) -> as_parser g (t x))

    | T_refine base refinement ->
      assert_norm (as_type g (T_refine base refinement) == Prelude.refine (itype_as_type base) refinement);
      let pi = itype_as_parser base in
      P.parse_filter pi refinement

    | T_if_else b t0 t1 -> 
      assert_norm (as_type g (T_if_else b t0 t1) == Prelude.t_ite b (as_type g t0) (as_type g t1));
      let p0 (_:squash b) = as_parser g t0 in
      let p1 (_:squash (not b)) = as_parser g t1 in
      P.parse_ite b p0 p1

    | T_with_action t a ->
      assert_norm (as_type g (T_with_action t a) == as_type g t);
      as_parser g t
      
    | T_with_dep_action i a ->
      assert_norm (as_type g (T_with_dep_action i a) == itype_as_type i);
      itype_as_parser i
      
    | T_with_comment t c -> 
      assert_norm (as_type g (T_with_comment t c) == as_type g t);      
      as_parser g t

    | T_app hd args ->
      assert (as_type g (T_app hd args) == apply_arrow (Some?.v (lookup g hd)).p_t args)
         by (T.norm [delta_only [`%as_type]; zeta; iota];
             T.smt());
      apply_dep_arrow_uncurred _ _ (Some?.v (lookup g hd)).p_p args

    | T_pointer t ->
      admit()

assume
val itype_as_validator (i:itype)
  : A.validate_with_action_t (itype_as_parser i) A.true_inv A.eloc_none true

assume 
val itype_as_leaf_reader (i:itype)
  : A.leaf_reader (itype_as_parser i)

assume
val action_as_action 
   (#nz #wk:_)
   (#pk:P.parser_kind nz wk)
   (#lt #it #bt:_) (g:globals) (p:typ g pk lt it bt)
   (#l #i #b #t:_) (a:action l i b t) 
  : A.action (as_parser g p) i l b t

assume
val iaction_as_action 
   (g:globals) (p:itype)
   (#l #i #b #t:_) (a:action l i b t) 
  : A.action (itype_as_parser p) i l b t

let rec as_validator #nz #wk (#pk:P.parser_kind nz wk) #loc #inv #b (g:globals) (t:typ g pk loc inv b)
  : Tot (A.validate_with_action_t #nz #wk #pk #(as_type g t) (as_parser g t) inv loc b)
        (decreases t)
  = match t returns Tot (A.validate_with_action_t #nz #wk #pk #(as_type g t) (as_parser g t) inv loc b) with
    | T_false -> 
      A.validate_impos()

    | T_pair t1 t2 -> 
      assert_norm (as_type g (T_pair t1 t2) == as_type g t1 * as_type g t2);
      assert_norm (as_parser g (T_pair t1 t2) == P.parse_pair (as_parser g t1) (as_parser g t2));
      A.validate_pair ""
        (as_validator g t1)
        (as_validator g t2)

    | T_dep_pair i t ->
      assert_norm (as_type g (T_dep_pair i t) == x:itype_as_type i & as_type g (t x));
      assert_norm (as_parser g (T_dep_pair i t) == 
                   P.parse_dep_pair (itype_as_parser i) (fun (x:itype_as_type i) -> as_parser g (t x)));
      A.validate_weaken_inv_loc inv loc
      (A.validate_dep_pair ""
        (itype_as_validator i)
        (itype_as_leaf_reader i)
        (fun x -> as_validator g (t x)))

    | T_refine t f -> 
      A.validate_filter "" 
        (itype_as_validator t)
        (itype_as_leaf_reader t)
        f "" ""

    | T_if_else b t0 t1 -> 
      assert_norm (as_type g (T_if_else b t0 t1) == Prelude.t_ite b (as_type g t0) (as_type g t1));
      let p0 (_:squash b) = as_parser g t0 in
      let p1 (_:squash (not b)) = as_parser g t1 in
      assert_norm (as_parser g (T_if_else b t0 t1) == P.parse_ite b p0 p1);
      let v0 (_:squash b) = as_validator g t0 in
      let v1 (_:squash (not b)) = as_validator g t1 in      
      A.validate_ite b p0 v0 p1 v1
        
    | T_with_action t a ->
      assert_norm (as_type g (T_with_action t a) == as_type g t);
      assert_norm (as_parser g (T_with_action t a) == as_parser g t);      
      A.validate_with_success_action ""
        (as_validator g t)
        (action_as_action g t a)

    | T_with_dep_action i a ->
      assert_norm (as_type g (T_with_dep_action i a) == itype_as_type i);
      assert_norm (as_parser g (T_with_dep_action i a) == itype_as_parser i);      
      A.validate_weaken_inv_loc inv loc (
       A.validate_with_dep_action ""
        (itype_as_validator i)
        (itype_as_leaf_reader i)
        (fun x -> iaction_as_action g i (a x)))

    | T_with_comment t c ->
      assert_norm (as_type g (T_with_comment t c) == as_type g t);
      assert_norm (as_parser g (T_with_comment t c) == as_parser g t);      
      A.validate_with_comment "" (as_validator g t)
      
    | T_app hd args ->
      assert (as_type g (T_app hd args) == apply_arrow (Some?.v (lookup g hd)).p_t args)
         by (T.norm [delta_only [`%as_type]; zeta; iota];
             T.smt());
      assert (as_parser g (T_app hd args) == apply_dep_arrow_uncurred _ _ (Some?.v (lookup g hd)).p_p args)
         by (T.trefl());
      apply_dep_arrow_uncurred _ _ (Some?.v (lookup g hd)).p_v args
      
    | _ -> admit()
    
// and as_expr (g:env) (e:expr)
//   : option typed_term
//   = None
  
// assume
// val parser_kind_nz (t:typ) : bool

// assume
// val parser_weak_kind (t:typ) : P.weak_kind

// assume
// val as_kind (t:typ) : P.parser_kind (parser_kind_nz t) (parser_weak_kind t)

// assume
// val as_parser (t:typ) : P.parser (as_kind t) (as_type t)



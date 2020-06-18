module EverParse3d.LayeredActions
module A = Actions
open Actions
open Prelude

let va_repr (t : Type u#a)
            (nz:bool)
            (k:parser_kind nz)
            (p:parser k t)
            (inv:slice_inv)
            (l:eloc)
            (allow_reading:bool)
  : Type u#0
  = validate_with_action_t #nz #k #t p inv l allow_reading

val va_return (a:Type) (x:a)
  : va_repr a false ret_kind (parse_ret x) true_inv eloc_none true

val parse_bind (nz1:_) (k1:parser_kind nz1) (t1: Type u#a) (p1: parser k1 t1)
               (nz2:_) (k2:parser_kind nz2) (t2: Type u#b) (p2: (x: t1) -> parser k2 t2)
  : Tot (parser (and_then_kind k1 k2) t2)

val va_bind
      (a:Type u#a) (b:Type u#b)
      (nz1:_) (k1:parser_kind nz1) (p1:parser k1 a)
      (inv1:_) (l1:_)
//      (r1: leaf_reader p1) //<-- How to resolve this argument?
      (nz2:_) (k2:parser_kind nz2) (p2:(x:a -> parser k2 b))
      (inv2:_) (l2:_) (allow_reading2:bool)
      (v1:va_repr a nz1 k1 p1 inv1 l1 true)
      (v2:(x:a -> va_repr b nz2 k2 (p2 x) inv2 l2 allow_reading2))
  : va_repr b (nz1 || nz2) (and_then_kind k1 k2)
            (parse_bind _ _ _ p1 _ _ _ p2)
            (conj_inv inv1 inv2)
            (l1 `eloc_union` l2)
            false

val subcomp (t1:Type)
            (nz1:_)
            (k1:parser_kind nz1)
            (p1:parser k1 t1)
            (inv1:_)
            (l1:_)
            (allow_reading:bool)
            (inv2:_)
            (l2:_)
            (v1:va_repr t1 nz1 k1 p1 inv1 l1 allow_reading)
  : Pure (va_repr t1 nz1 k1 p1 inv2 l2 allow_reading)
         (requires inv2 `inv_implies` inv1 /\
                   l2 `eloc_includes` l1)
         (ensures fun _ -> True)

let if_then_else (t1:Type)
                 (nz1:bool)
                 (k1:parser_kind nz1)
                 (p1:parser k1 t1)
                 (inv1:_)
                 (l1:_)
                 (allow_reading:bool)
                 (v1:va_repr t1 nz1 k1 p1 inv1 l1 allow_reading)
                 (v2:va_repr t1 nz1 k1 p1 inv1 l1 allow_reading)
                 (p:Type0)
  : Type
  = va_repr t1 nz1 k1 p1 inv1 l1 allow_reading

//#push-options "--debug EverParse3D.LayeredActions --debug_level LayeredEffectsTc"
reifiable reflectable
layered_effect {
  VA_ : t : Type
     -> nz:bool
     -> k:parser_kind nz
     -> p:parser k t
     -> inv:slice_inv
     -> l:eloc
     -> allow_reading:bool
     -> Effect
  with
  repr = va_repr;
  return = va_return;
  bind = va_bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}


// sub_effect PURE ~> RSTATE = lift_pure_rst

effect VA (t:Type) (#nz:bool) (#k:parser_kind nz) (p:parser k t) (inv:slice_inv) (l:eloc) (allow_reading:bool) =
  VA_ t nz k p inv l allow_reading


let lift_pure (a:Type) (f:unit -> Tot a)
  : Tot (va_repr a false ret_kind (parse_ret (f())) true_inv eloc_none true)
  = va_return a (f())

sub_effect PURE ~> VA_ = lift_pure


val va_ret (#a:Type) (x:a) : VA a (parse_ret x) true_inv eloc_none false

val va_u16 (_:unit) : VA ___UINT16 parse____UINT16 true_inv eloc_none true

let parse_pair (#nz1:_) (#k1:parser_kind nz1) (#t1:_) (p1:parser k1 t1)
               (#nz2:_) (#k2:parser_kind nz2) (#t2:_) (p2:parser k2 t2)
  : Tot (parser (and_then_kind k1 (and_then_kind k2 ret_kind)) (t1 * t2))
  = parse_bind _ _ _ p1 _ _ _ (fun x1 ->
    parse_bind _ _ _ p2 _ _ _ (fun x2 ->
    parse_ret (x1, x2)))

let test (_:unit) : VA (___UINT16 * ___UINT16)
                       (parse_pair parse____UINT16 parse____UINT16)
                       (conj_inv true_inv (conj_inv true_inv true_inv))
                       (eloc_union eloc_none (eloc_union eloc_none eloc_none))
                       false
  = let x1 = va_u16 () in
    let x2 = va_u16 () in
    va_ret (x1, x2)

let test2 (_:unit) : VA (___UINT16 * ___UINT16)
                       (parse_pair parse____UINT16 parse____UINT16)
                       true_inv
                       eloc_none
                       false
  = let x1 = va_u16 () in
    let x2 = va_u16 () in
    va_ret (x1, x2)

let parse_dep_pair (#nz1:_) (#k1:parser_kind nz1) (#t1:_) (p1:parser k1 t1)
                   (#nz2:_) (#k2:parser_kind nz2) (#t2:t1 -> Type) (p2:(x:t1 -> parser k2 (t2 x)))
  : Tot (parser (and_then_kind k1 (and_then_kind k2 ret_kind)) (x:t1 & t2 x))
  = parse_bind _ _ _ p1 _ _ (dtuple2 t1 t2) (fun x1 ->
    parse_bind _ _ _ (p2 x1) _ _ (dtuple2 t1 t2) (fun x2 ->
    parse_ret (| x1, x2 |)))

inline_for_extraction noextract
val va_filter (#nz:_) (#k:parser_kind nz) (#t:_) (#p:parser k t)
              (#inv:_) (#l:_) (v:unit -> VA t p inv l true)
              // (r:leaf_reader p)
    (f:t -> bool)
  : VA_ (refine t f) nz (filter_kind k) (p `parse_filter` f) inv l false

val gt (x:int) (y:___UINT16) : bool

#push-options "--print_implicits --print_universes --print_effect_args"
let test3 (_:unit) : VA ___UINT16
                       parse____UINT16
                       true_inv
                       eloc_none
                       true
  = va_u16 ()

// let test4 (_:unit) : VA_ (refine ___UINT16 (gt 0))
//                          true
//                          (filter_kind kind____UINT16)
//                          (parse____UINT16 `parse_filter` gt 0)
//                          true_inv
//                          eloc_none
//                          false
//   = va_filter #true #kind____UINT16 #___UINT16 #parse____UINT16 #true_inv #eloc_none va_u16 (gt 0)

open Prims
type ('a, 'b) rel =
  | R of 'a * 'b 
let uu___is_R (projectee : ('a, 'b) rel) : Prims.bool= true
let __proj__R__item__l (projectee : ('a, 'b) rel) : 'a=
  match projectee with | R (l, r) -> l
let __proj__R__item__r (projectee : ('a, 'b) rel) : 'b=
  match projectee with | R (l, r) -> r
type 't double = ('t, 't) rel
type 't eq = 't double
let twice (x : 'uuuuu) : ('uuuuu, 'uuuuu) rel= R (x, x)
let tu : (unit, unit) rel= twice ()
let rel_map1T (f : 'a -> 'b) (uu___ : 'a double) : 'b double=
  match uu___ with | R (x1, x2) -> R ((f x1), (f x2))
let rel_map2Teq (f : 'a -> 'b -> 'c) (uu___ : 'a double) (uu___1 : 'b double)
  : 'c double=
  match (uu___, uu___1) with
  | (R (x1, x2), R (y1, y2)) -> R ((f x1 y1), (f x2 y2))
let rel_map2T (f : 'a -> 'b -> 'c) (uu___ : 'a double) (uu___1 : 'b double) :
  'c double=
  match (uu___, uu___1) with
  | (R (x1, x2), R (y1, y2)) -> R ((f x1 y1), (f x2 y2))
let rel_map3T (f : 'a -> 'b -> 'c -> 'd) (uu___ : 'a double)
  (uu___1 : 'b double) (uu___2 : 'c double) : 'd double=
  match (uu___, uu___1, uu___2) with
  | (R (x1, x2), R (y1, y2), R (z1, z2)) -> R ((f x1 y1 z1), (f x2 y2 z2))
let op_Hat_Plus : Prims.int double -> Prims.int double -> Prims.int double=
  rel_map2T (fun x y -> x + y)
let op_Hat_Minus : Prims.int double -> Prims.int double -> Prims.int double=
  rel_map2T (fun x y -> x - y)
let op_Hat_Star : Prims.int double -> Prims.int double -> Prims.int double=
  rel_map2T (fun x y -> x * y)
let op_Hat_Slash :
  Prims.int double -> Prims.nonzero double -> Prims.int double=
  rel_map2T (fun x y -> x / y)
let tl_rel (uu___ : 'a Prims.list double) : 'a Prims.list double=
  match uu___ with | R (uu___1::xs, uu___2::ys) -> R (xs, ys)
let cons_rel (uu___ : ('uuuuu, 'uuuuu1) rel)
  (uu___1 : ('uuuuu Prims.list, 'uuuuu1 Prims.list) rel) :
  ('uuuuu Prims.list, 'uuuuu1 Prims.list) rel=
  match (uu___, uu___1) with
  | (R (x, y), R (xs, ys)) -> R ((x :: xs), (y :: ys))
let pair_rel (uu___ : ('uuuuu, 'uuuuu1) rel)
  (uu___1 : ('uuuuu2, 'uuuuu3) rel) :
  (('uuuuu * 'uuuuu2), ('uuuuu1 * 'uuuuu3)) rel=
  match (uu___, uu___1) with | (R (a, b), R (c, d)) -> R ((a, c), (b, d))
let triple_rel (uu___ : ('uuuuu, 'uuuuu1) rel)
  (uu___1 : ('uuuuu2, 'uuuuu3) rel) (uu___2 : ('uuuuu4, 'uuuuu5) rel) :
  (('uuuuu * 'uuuuu2 * 'uuuuu4), ('uuuuu1 * 'uuuuu3 * 'uuuuu5)) rel=
  match (uu___, uu___1, uu___2) with
  | (R (a, b), R (c, d), R (e, f)) -> R ((a, c, e), (b, d, f))
let fst_rel (uu___ : unit) : ('uuuuu * 'uuuuu1) double -> 'uuuuu double=
  rel_map1T FStar_Pervasives_Native.fst
let snd_rel (uu___ : unit) : ('uuuuu * 'uuuuu1) double -> 'uuuuu1 double=
  rel_map1T FStar_Pervasives_Native.snd
let and_rel : Prims.bool double -> Prims.bool double -> Prims.bool double=
  rel_map2T (fun x y -> x && y)
let or_rel : Prims.bool double -> Prims.bool double -> Prims.bool double=
  rel_map2T (fun x y -> x || y)
let eq_rel : Prims.bool double -> Prims.bool double -> Prims.bool double=
  rel_map2Teq (fun x y -> x = y)
let and_irel (uu___ : (Prims.bool, Prims.bool) rel) : Prims.bool=
  match uu___ with | R (a, b) -> a && b
let or_irel (uu___ : (Prims.bool, Prims.bool) rel) : Prims.bool=
  match uu___ with | R (a, b) -> a || b
let eq_irel (x : ('t, 't) rel) : Prims.bool= match x with | R (a, b) -> a = b

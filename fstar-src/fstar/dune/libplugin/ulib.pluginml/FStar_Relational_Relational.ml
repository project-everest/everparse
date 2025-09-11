open Fstarcompiler
open Prims
type ('a, 'b) rel =
  | R of 'a * 'b 
let uu___is_R : 'a 'b . ('a, 'b) rel -> Prims.bool = fun projectee -> true
let __proj__R__item__l : 'a 'b . ('a, 'b) rel -> 'a =
  fun projectee -> match projectee with | R (l, r) -> l
let __proj__R__item__r : 'a 'b . ('a, 'b) rel -> 'b =
  fun projectee -> match projectee with | R (l, r) -> r
type 't double = ('t, 't) rel
type 't eq = 't double
let twice : 'uuuuu . 'uuuuu -> ('uuuuu, 'uuuuu) rel = fun x -> R (x, x)
let (tu : (unit, unit) rel) = twice ()
let rel_map1T : 'a 'b . ('a -> 'b) -> 'a double -> 'b double =
  fun f -> fun uu___ -> match uu___ with | R (x1, x2) -> R ((f x1), (f x2))
let rel_map2Teq :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a double -> 'b double -> 'c double =
  fun f ->
    fun uu___ ->
      fun uu___1 ->
        match (uu___, uu___1) with
        | (R (x1, x2), R (y1, y2)) -> R ((f x1 y1), (f x2 y2))
let rel_map2T :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a double -> 'b double -> 'c double =
  fun f ->
    fun uu___ ->
      fun uu___1 ->
        match (uu___, uu___1) with
        | (R (x1, x2), R (y1, y2)) -> R ((f x1 y1), (f x2 y2))
let rel_map3T :
  'a 'b 'c 'd .
    ('a -> 'b -> 'c -> 'd) ->
      'a double -> 'b double -> 'c double -> 'd double
  =
  fun f ->
    fun uu___ ->
      fun uu___1 ->
        fun uu___2 ->
          match (uu___, uu___1, uu___2) with
          | (R (x1, x2), R (y1, y2), R (z1, z2)) ->
              R ((f x1 y1 z1), (f x2 y2 z2))
let (op_Hat_Plus : Prims.int double -> Prims.int double -> Prims.int double)
  = rel_map2T (fun x -> fun y -> x + y)
let (op_Hat_Minus : Prims.int double -> Prims.int double -> Prims.int double)
  = rel_map2T (fun x -> fun y -> x - y)
let (op_Hat_Star : Prims.int double -> Prims.int double -> Prims.int double)
  = rel_map2T (fun x -> fun y -> x * y)
let (op_Hat_Slash :
  Prims.int double -> Prims.nonzero double -> Prims.int double) =
  rel_map2T (fun x -> fun y -> x / y)
let tl_rel : 'a . 'a Prims.list double -> 'a Prims.list double =
  fun uu___ -> match uu___ with | R (uu___1::xs, uu___2::ys) -> R (xs, ys)
let cons_rel :
  'uuuuu 'uuuuu1 .
    ('uuuuu, 'uuuuu1) rel ->
      ('uuuuu Prims.list, 'uuuuu1 Prims.list) rel ->
        ('uuuuu Prims.list, 'uuuuu1 Prims.list) rel
  =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | (R (x, y), R (xs, ys)) -> R ((x :: xs), (y :: ys))
let pair_rel :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    ('uuuuu, 'uuuuu1) rel ->
      ('uuuuu2, 'uuuuu3) rel -> (('uuuuu * 'uuuuu2), ('uuuuu1 * 'uuuuu3)) rel
  =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with | (R (a, b), R (c, d)) -> R ((a, c), (b, d))
let triple_rel :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 'uuuuu5 .
    ('uuuuu, 'uuuuu1) rel ->
      ('uuuuu2, 'uuuuu3) rel ->
        ('uuuuu4, 'uuuuu5) rel ->
          (('uuuuu * 'uuuuu2 * 'uuuuu4), ('uuuuu1 * 'uuuuu3 * 'uuuuu5)) rel
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        match (uu___, uu___1, uu___2) with
        | (R (a, b), R (c, d), R (e, f)) -> R ((a, c, e), (b, d, f))
let fst_rel :
  'uuuuu 'uuuuu1 . unit -> ('uuuuu * 'uuuuu1) double -> 'uuuuu double =
  fun uu___ -> rel_map1T FStar_Pervasives_Native.fst
let snd_rel :
  'uuuuu 'uuuuu1 . unit -> ('uuuuu * 'uuuuu1) double -> 'uuuuu1 double =
  fun uu___ -> rel_map1T FStar_Pervasives_Native.snd
let (and_rel : Prims.bool double -> Prims.bool double -> Prims.bool double) =
  rel_map2T (fun x -> fun y -> x && y)
let (or_rel : Prims.bool double -> Prims.bool double -> Prims.bool double) =
  rel_map2T (fun x -> fun y -> x || y)
let (eq_rel : Prims.bool double -> Prims.bool double -> Prims.bool double) =
  rel_map2Teq (fun x -> fun y -> x = y)
let (and_irel : (Prims.bool, Prims.bool) rel -> Prims.bool) =
  fun uu___ -> match uu___ with | R (a, b) -> a && b
let (or_irel : (Prims.bool, Prims.bool) rel -> Prims.bool) =
  fun uu___ -> match uu___ with | R (a, b) -> a || b
let eq_irel : 't . ('t, 't) rel -> Prims.bool =
  fun x -> match x with | R (a, b) -> a = b

open Prims
type heap2 = FStar_Monotonic_Heap.heap FStar_Relational_Relational.double
type st2_Pre = unit
type ('a, 'pre) st2_Post' = unit
type 'a st2_Post = unit
type 'a st2_WP = unit
type ('a, 'b, 'wp0, 'wp1, 'p, 'h2) comp = 'wp0
let compose2 :
  'a0 'b0 'wp0 'a1 'b1 'wp1 .
    ('a0 -> 'b0) ->
      ('a1 -> 'b1) ->
        ('a0, 'a1) FStar_Relational_Relational.rel ->
          ('b0, 'b1) FStar_Relational_Relational.rel
  =
  fun c0 ->
    fun c1 ->
      fun x -> failwith "Not yet implemented: FStar.Relational.Comp.compose2"
let compose2_self :
  'a 'b 'wp .
    ('a -> 'b) ->
      'a FStar_Relational_Relational.double ->
        'b FStar_Relational_Relational.double
  = fun f -> fun x -> compose2 f f x
let cross :
  'a 'b 'c 'd 'p 'pu 'q 'qu .
    (unit FStar_Relational_Relational.double ->
       ('a, 'b) FStar_Relational_Relational.rel)
      ->
      (unit FStar_Relational_Relational.double ->
         ('c, 'd) FStar_Relational_Relational.rel)
        -> ('a, 'd) FStar_Relational_Relational.rel
  =
  fun c1 ->
    fun c2 -> failwith "Not yet implemented: FStar.Relational.Comp.cross"
type ('a0, 'a1, 'b0, 'b1, 'al, 'wp, 'p, 'hl) decomp_l = unit
type ('a0, 'a1, 'b0, 'b1, 'ar, 'wp, 'p, 'hr) decomp_r = unit
let project_l :
  'a0 'b0 'a1 'b1 'wp .
    (('a0, 'a1) FStar_Relational_Relational.rel ->
       ('b0, 'b1) FStar_Relational_Relational.rel)
      -> 'a0 -> 'b0
  =
  fun c ->
    fun x -> failwith "Not yet implemented: FStar.Relational.Comp.project_l"
let project_r :
  'a0 'b0 'a1 'b1 'wp .
    (('a0, 'a1) FStar_Relational_Relational.rel ->
       ('b0, 'b1) FStar_Relational_Relational.rel)
      -> 'a1 -> 'b1
  =
  fun c ->
    fun x -> failwith "Not yet implemented: FStar.Relational.Comp.project_r"

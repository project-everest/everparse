open Prims
type heap2 = FStar_Monotonic_Heap.heap FStar_Relational_Relational.double
type st2_Pre = unit
type ('a, 'pre) st2_Post' = unit
type 'a st2_Post = unit
type 'a st2_WP = unit
type ('a, 'b, 'wp0, 'wp1, 'p, 'h2) comp = 'wp0
let compose2 (c0 : 'a0 -> 'b0) (c1 : 'a1 -> 'b1)
  (x : ('a0, 'a1) FStar_Relational_Relational.rel) :
  ('b0, 'b1) FStar_Relational_Relational.rel=
  failwith "Not yet implemented: FStar.Relational.Comp.compose2"
let compose2_self (f : 'a -> 'b) (x : 'a FStar_Relational_Relational.double)
  : 'b FStar_Relational_Relational.double= compose2 f f x
let cross
  (c1 :
    unit FStar_Relational_Relational.double ->
      ('a, 'b) FStar_Relational_Relational.rel)
  (c2 :
    unit FStar_Relational_Relational.double ->
      ('c, 'd) FStar_Relational_Relational.rel)
  : ('a, 'd) FStar_Relational_Relational.rel=
  failwith "Not yet implemented: FStar.Relational.Comp.cross"
type ('a0, 'a1, 'b0, 'b1, 'al, 'wp, 'p, 'hl) decomp_l = unit
type ('a0, 'a1, 'b0, 'b1, 'ar, 'wp, 'p, 'hr) decomp_r = unit
let project_l
  (c :
    ('a0, 'a1) FStar_Relational_Relational.rel ->
      ('b0, 'b1) FStar_Relational_Relational.rel)
  (x : 'a0) : 'b0=
  failwith "Not yet implemented: FStar.Relational.Comp.project_l"
let project_r
  (c :
    ('a0, 'a1) FStar_Relational_Relational.rel ->
      ('b0, 'b1) FStar_Relational_Relational.rel)
  (x : 'a1) : 'b1=
  failwith "Not yet implemented: FStar.Relational.Comp.project_r"

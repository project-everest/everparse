open Fstarcompiler
open Prims
type ('a, 'h, 'r) contains = ('a, unit, 'h, 'r) FStar_Monotonic_Heap.contains
type ('a, 'r, 'h) unused_in =
  ('a, unit, 'r, 'h) FStar_Monotonic_Heap.unused_in
type ('a, 'r, 'h0, 'h1) fresh = unit
let recall (r : 'uuuuu FStar_ST.ref) : unit= FStar_ST.recall r
let alloc (init : 'uuuuu) : 'uuuuu FStar_ST.ref= FStar_ST.alloc init
let read (r : 'uuuuu FStar_ST.ref) : 'uuuuu= FStar_ST.read r
let write (r : 'uuuuu FStar_ST.ref) (v : 'uuuuu) : unit= FStar_ST.write r v
let op_Bang (r : 'uuuuu FStar_ST.ref) : 'uuuuu= read r
let op_Colon_Equals (r : 'uuuuu FStar_ST.ref) (v : 'uuuuu) : unit= write r v

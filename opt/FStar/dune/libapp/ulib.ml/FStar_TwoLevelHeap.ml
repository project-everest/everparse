open Prims
type rid = Prims.int
type t = (rid, FStar_Monotonic_Heap.heap) FStar_Map.t
type st_pre = unit
type ('a, 'pre) st_post' = unit
type 'a st_post = unit
type 'a st_wp = unit
type ('id, 'a) rref = 'a FStar_Heap.ref
let as_ref : 'a . rid -> (Obj.t, 'a) rref -> 'a FStar_Heap.ref =
  fun id -> fun r -> r
let ref_as_rref : 'a . rid -> 'a FStar_Heap.ref -> (Obj.t, 'a) rref =
  fun i -> fun r -> r
let (new_region : unit -> rid) =
  fun uu___ -> failwith "Not yet implemented: FStar.TwoLevelHeap.new_region"
let ralloc : 'a . rid -> 'a -> (Obj.t, 'a) rref =
  fun i ->
    fun init -> failwith "Not yet implemented: FStar.TwoLevelHeap.ralloc"
let op_Colon_Equals : 'a . rid -> (Obj.t, 'a) rref -> 'a -> unit =
  fun i ->
    fun r ->
      fun v ->
        failwith "Not yet implemented: FStar.TwoLevelHeap.op_Colon_Equals"
let op_Bang : 'a . rid -> (Obj.t, 'a) rref -> 'a =
  fun i ->
    fun r -> failwith "Not yet implemented: FStar.TwoLevelHeap.op_Bang"
let (get : unit -> t) =
  fun uu___ -> failwith "Not yet implemented: FStar.TwoLevelHeap.get"
type ('s, 'm0, 'm1) modifies =
  (rid, FStar_Monotonic_Heap.heap, 'm1, Obj.t) FStar_Map.equal
type ('i, 'm0, 'm1) fresh_region = unit
type ('a, 'i, 'r, 'm) contains_ref = unit
type ('a, 'i, 'r, 'm0, 'm1) fresh_rref = unit

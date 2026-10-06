open Fstarcompiler
open Prims
type rid = Prims.int
type t = (rid, FStar_Monotonic_Heap.heap) FStar_Map.t
type st_pre = unit
type ('a, 'pre) st_post' = unit
type 'a st_post = unit
type 'a st_wp = unit
type ('id, 'a) rref = 'a FStar_Heap.ref
let as_ref (id : rid) (r : (Obj.t, 'a) rref) : 'a FStar_Heap.ref= r
let ref_as_rref (i : rid) (r : 'a FStar_Heap.ref) : (Obj.t, 'a) rref= r
let new_region (uu___ : unit) : rid=
  failwith "Not yet implemented: FStar.TwoLevelHeap.new_region"
let ralloc (i : rid) (init : 'a) : (Obj.t, 'a) rref=
  failwith "Not yet implemented: FStar.TwoLevelHeap.ralloc"
let op_Colon_Equals (i : rid) (r : (Obj.t, 'a) rref) (v : 'a) : unit=
  failwith "Not yet implemented: FStar.TwoLevelHeap.op_Colon_Equals"
let op_Bang (i : rid) (r : (Obj.t, 'a) rref) : 'a=
  failwith "Not yet implemented: FStar.TwoLevelHeap.op_Bang"
let get (uu___ : unit) : t=
  failwith "Not yet implemented: FStar.TwoLevelHeap.get"
type ('s, 'm0, 'm1) modifies =
  (rid, FStar_Monotonic_Heap.heap, 'm1, Obj.t) FStar_Map.equal
type ('i, 'm0, 'm1) fresh_region = unit
type ('a, 'i, 'r, 'm) contains_ref = unit
type ('a, 'i, 'r, 'm0, 'm1) fresh_rref = unit

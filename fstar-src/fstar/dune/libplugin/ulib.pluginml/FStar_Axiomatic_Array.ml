open Fstarcompiler
open Prims
type 'uuuuu seq = unit
let index : 'a . 'a seq -> Prims.int -> 'a =
  fun uu___ ->
    fun uu___1 -> failwith "Not yet implemented: FStar.Axiomatic.Array.index"
let update : 'a . 'a seq -> Prims.int -> 'a -> 'a seq =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        failwith "Not yet implemented: FStar.Axiomatic.Array.update"
let emp : 'a . unit -> 'a seq =
  fun uu___ -> failwith "Not yet implemented: FStar.Axiomatic.Array.emp"
let create : 'a . Prims.int -> 'a -> 'a seq =
  fun uu___ ->
    fun uu___1 ->
      failwith "Not yet implemented: FStar.Axiomatic.Array.create"
let length : 'a . 'a seq -> Prims.nat =
  fun uu___ -> failwith "Not yet implemented: FStar.Axiomatic.Array.length"
let slice : 'a . 'a seq -> Prims.int -> Prims.int -> 'a seq =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        failwith "Not yet implemented: FStar.Axiomatic.Array.slice"
let append : 'a . 'a seq -> 'a seq -> 'a seq =
  fun uu___ ->
    fun uu___1 ->
      failwith "Not yet implemented: FStar.Axiomatic.Array.append"
let proj_some : 'a . 'a FStar_Pervasives_Native.option seq -> 'a seq =
  fun uu___ ->
    failwith "Not yet implemented: FStar.Axiomatic.Array.proj_some"
type ('a, 'uuuuu, 'uuuuu1) equal = unit
type 'a array = 'a seq FStar_Heap.ref
type ('a, 's) is_Some_All = unit
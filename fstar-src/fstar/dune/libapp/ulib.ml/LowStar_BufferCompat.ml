open Prims
type ('a, 'r, 'len, 'b, 'h0, 'h1, 's) rcreate_post_mem_common = unit
let rfree : 'a . 'a LowStar_Buffer.buffer -> unit =
  fun b -> LowStar_Monotonic_Buffer.free b
let rcreate : 'a . unit -> 'a -> FStar_UInt32.t -> 'a LowStar_Buffer.buffer =
  fun r ->
    fun init ->
      fun len -> let b = LowStar_Monotonic_Buffer.mgcmalloc () init len in b
let rcreate_mm :
  'a . unit -> 'a -> FStar_UInt32.t -> 'a LowStar_Buffer.buffer =
  fun r ->
    fun init -> fun len -> LowStar_Monotonic_Buffer.mmalloc () init len
let create : 'a . 'a -> FStar_UInt32.t -> 'a LowStar_Buffer.buffer =
  fun init -> fun len -> LowStar_Monotonic_Buffer.malloca init len
type ('a, 'init) createL_pre = unit
let createL : 'a . 'a Prims.list -> 'a LowStar_Buffer.buffer =
  fun init -> LowStar_Monotonic_Buffer.malloca_of_list init
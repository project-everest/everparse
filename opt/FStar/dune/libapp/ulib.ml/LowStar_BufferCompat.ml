open Prims
type ('a, 'r, 'len, 'b, 'h0, 'h1, 's) rcreate_post_mem_common = unit
let rfree (b : 'a LowStar_Buffer.buffer) : unit=
  LowStar_Monotonic_Buffer.free b
let rcreate (r : unit) (init : 'a) (len : FStar_UInt32.t) :
  'a LowStar_Buffer.buffer=
  let b = LowStar_Monotonic_Buffer.mgcmalloc () init len in b
let rcreate_mm (r : unit) (init : 'a) (len : FStar_UInt32.t) :
  'a LowStar_Buffer.buffer= LowStar_Monotonic_Buffer.mmalloc () init len
let create (init : 'a) (len : FStar_UInt32.t) : 'a LowStar_Buffer.buffer=
  LowStar_Monotonic_Buffer.malloca init len
type ('a, 'init) createL_pre = unit
let createL (init : 'a Prims.list) : 'a LowStar_Buffer.buffer=
  LowStar_Monotonic_Buffer.malloca_of_list init

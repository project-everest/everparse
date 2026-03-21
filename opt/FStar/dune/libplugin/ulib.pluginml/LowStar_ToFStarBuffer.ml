open Fstarcompiler
open Prims
let new_to_old_st (b : 't LowStar_Buffer.buffer) : 't FStar_Buffer.buffer=
  failwith "Not yet implemented: LowStar.ToFStarBuffer.new_to_old_st"
let old_to_new_st (b : 't FStar_Buffer.buffer) : 't LowStar_Buffer.buffer=
  failwith "Not yet implemented: LowStar.ToFStarBuffer.old_to_new_st"
let coerce (uu___ : 't1) : 't2= (fun x -> Obj.magic x) uu___
let ex1 (b : Prims.nat LowStar_Buffer.buffer) (b1 : 'a LowStar_Buffer.buffer)
  : unit=
  let old = new_to_old_st b in
  FStar_Buffer.upd old Stdint.Uint32.zero Prims.int_zero
let new_eqb (b1 : 'a LowStar_Buffer.buffer) (b2 : 'a LowStar_Buffer.buffer)
  (len : FStar_UInt32.t) : Prims.bool=
  let b1' = new_to_old_st b1 in
  let b2' = new_to_old_st b2 in FStar_Buffer.eqb b1' b2' len
let new_blit (src : 't LowStar_Buffer.buffer) (idx_src : FStar_UInt32.t)
  (dst : 't LowStar_Buffer.buffer) (idx_dst : FStar_UInt32.t)
  (len : FStar_UInt32.t) : unit=
  let src' = new_to_old_st src in
  let dst' = new_to_old_st dst in
  FStar_Buffer.blit src' idx_src dst' idx_dst len
let new_fill (b : 't LowStar_Buffer.buffer) (z : 't) (len : FStar_UInt32.t) :
  unit= let b' = new_to_old_st b in FStar_Buffer.fill b' z len
let ex1' (b : Prims.nat FStar_Buffer.buffer) (b1 : 'a FStar_Buffer.buffer) :
  unit=
  let ne = old_to_new_st b in
  let h = FStar_HyperStack_ST.get () in
  LowStar_Monotonic_Buffer.upd' ne Stdint.Uint32.zero Prims.int_zero
let ex1'' (b : Prims.nat LowStar_Buffer.buffer)
  (b1 : 'a LowStar_Buffer.buffer) : unit=
  let old = new_to_old_st b in let old1 = new_to_old_st b1 in ex1' old old1

open Fstarcompiler
open Prims
let new_to_old_st : 't . 't LowStar_Buffer.buffer -> 't FStar_Buffer.buffer =
  fun b ->
    failwith "Not yet implemented: LowStar.ToFStarBuffer.new_to_old_st"
let old_to_new_st : 't . 't FStar_Buffer.buffer -> 't LowStar_Buffer.buffer =
  fun b ->
    failwith "Not yet implemented: LowStar.ToFStarBuffer.old_to_new_st"
let coerce : 't2 't1 . 't1 -> 't2 = fun uu___ -> (fun x -> Obj.magic x) uu___
let ex1 :
  'a . Prims.nat LowStar_Buffer.buffer -> 'a LowStar_Buffer.buffer -> unit =
  fun b ->
    fun b1 ->
      let old = new_to_old_st b in
      FStar_Buffer.upd old Stdint.Uint32.zero Prims.int_zero
let new_eqb :
  'a .
    'a LowStar_Buffer.buffer ->
      'a LowStar_Buffer.buffer -> FStar_UInt32.t -> Prims.bool
  =
  fun b1 ->
    fun b2 ->
      fun len ->
        let b1' = new_to_old_st b1 in
        let b2' = new_to_old_st b2 in FStar_Buffer.eqb b1' b2' len
let new_blit :
  't .
    't LowStar_Buffer.buffer ->
      FStar_UInt32.t ->
        't LowStar_Buffer.buffer -> FStar_UInt32.t -> FStar_UInt32.t -> unit
  =
  fun src ->
    fun idx_src ->
      fun dst ->
        fun idx_dst ->
          fun len ->
            let src' = new_to_old_st src in
            let dst' = new_to_old_st dst in
            FStar_Buffer.blit src' idx_src dst' idx_dst len
let new_fill : 't . 't LowStar_Buffer.buffer -> 't -> FStar_UInt32.t -> unit
  =
  fun b ->
    fun z ->
      fun len -> let b' = new_to_old_st b in FStar_Buffer.fill b' z len
let ex1' :
  'a . Prims.nat FStar_Buffer.buffer -> 'a FStar_Buffer.buffer -> unit =
  fun b ->
    fun b1 ->
      let ne = old_to_new_st b in
      let h = FStar_HyperStack_ST.get () in
      LowStar_Monotonic_Buffer.upd' ne Stdint.Uint32.zero Prims.int_zero
let ex1'' :
  'a . Prims.nat LowStar_Buffer.buffer -> 'a LowStar_Buffer.buffer -> unit =
  fun b ->
    fun b1 ->
      let old = new_to_old_st b in
      let old1 = new_to_old_st b1 in ex1' old old1

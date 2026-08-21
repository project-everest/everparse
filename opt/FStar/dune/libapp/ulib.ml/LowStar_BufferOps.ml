open Prims
let op_Array_Access (uu___ : unit) :
  ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer -> FStar_UInt32.t -> 'a=
  LowStar_Monotonic_Buffer.index
let op_Array_Assignment
  (b : ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (v : 'a) : unit=
  let h = FStar_HyperStack_ST.get () in LowStar_Monotonic_Buffer.upd' b i v
let op_Bang_Star (p : ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer) :
  'a= LowStar_Monotonic_Buffer.index p Stdint.Uint32.zero
let op_Star_Equals (p : ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (v : 'a) : unit=
  let h = FStar_HyperStack_ST.get () in
  LowStar_Monotonic_Buffer.upd' p Stdint.Uint32.zero v
let blit (uu___ : unit) :
  ('a, 'rrel1, 'rrel2) LowStar_Monotonic_Buffer.mbuffer ->
    FStar_UInt32.t ->
      ('a, 'rel1, 'rel2) LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t -> FStar_UInt32.t -> unit=
  LowStar_Monotonic_Buffer.blit

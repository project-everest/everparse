open Prims
type ('q, 'a) qbuf_cases = Obj.t
type ('q, 'a) q_preorder = Obj.t
type 'a qbuf = (unit, Obj.t) Prims.dtuple2
type ('a, 'c, 'uuuuu, 'uuuuu1) qbuf_pre = Obj.t
let qbuf_mbuf (uu___ : 'a qbuf) :
  ('a, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer=
  (fun c -> Obj.magic (FStar_Pervasives.dsnd c)) uu___
type 'a const_buffer = 'a qbuf
let as_qbuf (c : 'a const_buffer) : 'a qbuf= c
type ('a, 'h, 'c) live =
  ('a, Obj.t, Obj.t, 'h, Obj.t) LowStar_Monotonic_Buffer.live
let of_buffer (b : 'a LowStar_Buffer.buffer) : 'a const_buffer=
  Prims.Mkdtuple2 ((), (Obj.magic b))
let of_ibuffer (b : 'a LowStar_ImmutableBuffer.ibuffer) : 'a const_buffer=
  Prims.Mkdtuple2 ((), (Obj.magic b))
let of_qbuf (q : unit)
  (b : ('uuuuu, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer) :
  'uuuuu const_buffer= Prims.Mkdtuple2 ((), (Obj.magic b))
let null (uu___ : unit) : 'a const_buffer=
  of_buffer (LowStar_Monotonic_Buffer.mnull ())
let is_null (c : 'a const_buffer) : Prims.bool=
  let x = qbuf_mbuf c in LowStar_Monotonic_Buffer.is_null x
let index (c : 'a const_buffer) (i : FStar_UInt32.t) : 'a=
  let x = qbuf_mbuf c in LowStar_Monotonic_Buffer.index x i
type ('a, 'i, 'len, 'csub, 'c) const_sub_buffer = unit
let sub (c : 'a const_buffer) (i : FStar_UInt32.t) (len : unit) :
  'a const_buffer=
  let uu___ = c in
  match uu___ with
  | Prims.Mkdtuple2 (q, x) ->
      let x1 = Obj.magic x in
      let y = LowStar_Monotonic_Buffer.msub x1 i () in
      Prims.Mkdtuple2 ((), (Obj.magic y))
let cast (c : 'a const_buffer) :
  ('a, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer= qbuf_mbuf c
let to_buffer (uu___ : 'a const_buffer) : 'a LowStar_Buffer.buffer=
  (fun c -> Obj.magic (qbuf_mbuf c)) uu___
let to_ibuffer (uu___ : 'a const_buffer) :
  'a LowStar_ImmutableBuffer.ibuffer=
  (fun c -> Obj.magic (qbuf_mbuf c)) uu___
let test (x : FStar_UInt32.t LowStar_Buffer.buffer)
  (y : FStar_UInt32.t LowStar_ImmutableBuffer.ibuffer) : FStar_UInt32.t=
  let c1 = of_buffer x in
  let c2 = of_ibuffer y in
  (let h = FStar_HyperStack_ST.get () in
   LowStar_Monotonic_Buffer.upd' x Stdint.Uint32.zero Stdint.Uint32.one);
  (let a = index c1 Stdint.Uint32.zero in
   let a' = index c2 Stdint.Uint32.zero in
   let c3 = sub c2 Stdint.Uint32.one () in
   let a'' = index c3 Stdint.Uint32.zero in
   FStar_UInt32.add (FStar_UInt32.add a a') a'')

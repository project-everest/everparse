open Fstarcompiler
open Prims
let buffer_dummy (uu___ : unit) : 'uuuuu LowStar_Buffer.buffer=
  LowStar_Monotonic_Buffer.mnull ()
type nonzero = FStar_UInt32.t
type ('a, 'len, 'h, 'v) buffer_r_inv = unit
type ('a, 'len) buffer_repr = 'a FStar_Seq_Base.seq
type ('a, 'v) buffer_r_alloc_p = unit
let buffer_r_alloc (uu___ : unit) (uu___1 : ('a * nonzero)) (r : unit) :
  'a LowStar_Buffer.buffer=
  match uu___1 with | (ia, len) -> LowStar_Monotonic_Buffer.mmalloc () ia len
let buffer_r_free (uu___ : unit) (len : ('a * nonzero))
  (v : 'a LowStar_Buffer.buffer) : unit= LowStar_Monotonic_Buffer.free v
let buffer_copy (uu___ : unit) (uu___1 : ('a * nonzero))
  (src : 'a LowStar_Buffer.buffer) (dst : 'a LowStar_Buffer.buffer) : 
  unit=
  match uu___1 with
  | (ia, len) ->
      LowStar_Monotonic_Buffer.blit src Stdint.Uint32.zero dst
        Stdint.Uint32.zero len
let buffer_regional (ia : 'a) (len : nonzero) :
  (('a * nonzero), 'a LowStar_Buffer.buffer) LowStar_Regional.regional=
  LowStar_Regional.Rgl
    ((ia, len), (), (), (buffer_dummy ()), (), (), (), (), (), (), (),
      (buffer_r_alloc ()), (buffer_r_free ()))
let buffer_copyable (ia : 'a) (len : nonzero) :
  (('a * nonzero), 'a LowStar_Buffer.buffer, Obj.t) LowStar_RVector.copyable=
  LowStar_RVector.Cpy (buffer_copy ())
let vector_dummy (uu___ : unit) :
  ('a, 'uuuuu, Obj.t) LowStar_RVector.rvector=
  LowStar_Vector.Vec
    (Stdint.Uint32.zero, Stdint.Uint32.zero,
      (LowStar_Monotonic_Buffer.mnull ()))
type ('a, 'rst, 'rg, 'h, 'v) vector_r_inv = unit
type ('a, 'rst, 'rg) vector_repr = Obj.t FStar_Seq_Base.seq
type ('a, 'rst, 'rg, 'v) vector_r_alloc_p = unit
let vector_r_alloc (rg : ('rst, 'a) LowStar_Regional.regional) (r : unit) :
  ('a, 'rst, Obj.t) LowStar_RVector.rvector=
  FStar_HyperStack_ST.new_region ();
  LowStar_Vector.alloc_reserve Stdint.Uint32.one
    (LowStar_Regional.__proj__Rgl__item__dummy rg) ()
let vector_r_free (uu___ : unit)
  (uu___1 : ('uuuuu1, 'uuuuu) LowStar_Regional.regional)
  (v : ('uuuuu, 'uuuuu1, Obj.t) LowStar_RVector.rvector) : unit=
  LowStar_Vector.free v
let vector_regional (rg : ('rst, 'a) LowStar_Regional.regional) :
  (('rst, 'a) LowStar_Regional.regional,
    ('a, 'rst, Obj.t) LowStar_RVector.rvector) LowStar_Regional.regional=
  LowStar_Regional.Rgl
    (rg, (), (), (vector_dummy ()), (), (), (), (), (), (), (),
      vector_r_alloc, (vector_r_free ()))

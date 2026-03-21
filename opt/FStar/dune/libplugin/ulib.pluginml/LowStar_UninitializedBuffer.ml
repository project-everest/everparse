open Fstarcompiler
open Prims
type ('a, 's1, 's2) initialization_preorder = unit
type 'a ubuffer =
  ('a FStar_Pervasives_Native.option, unit, unit)
    LowStar_Monotonic_Buffer.mbuffer
let unull (uu___ : unit) : 'a ubuffer= LowStar_Monotonic_Buffer.mnull ()
type 'a pointer = 'a ubuffer
type 'a pointer_or_null = 'a ubuffer
let usub (uu___ : unit) :
  ('a FStar_Pervasives_Native.option,
    ('a, unit, unit) initialization_preorder,
    ('a, unit, unit) initialization_preorder)
    LowStar_Monotonic_Buffer.mbuffer ->
    FStar_UInt32.t ->
      unit ->
        ('a FStar_Pervasives_Native.option,
          ('a, unit, unit) initialization_preorder,
          ('a, unit, unit) initialization_preorder)
          LowStar_Monotonic_Buffer.mbuffer=
  LowStar_Monotonic_Buffer.msub
let uoffset (uu___ : unit) :
  ('a FStar_Pervasives_Native.option,
    ('a, unit, unit) initialization_preorder,
    ('a, unit, unit) initialization_preorder)
    LowStar_Monotonic_Buffer.mbuffer ->
    FStar_UInt32.t ->
      ('a FStar_Pervasives_Native.option,
        ('a, unit, unit) initialization_preorder,
        ('a, unit, unit) initialization_preorder)
        LowStar_Monotonic_Buffer.mbuffer=
  LowStar_Monotonic_Buffer.moffset
type ('a, 'i, 's) ipred = unit
type ('a, 'b, 'i) initialized_at =
  ('a FStar_Pervasives_Native.option, unit, unit, 'b, unit)
    LowStar_Monotonic_Buffer.witnessed
let uindex (b : 'a ubuffer) (i : FStar_UInt32.t) : 'a=
  let y_opt = LowStar_Monotonic_Buffer.index b i in
  LowStar_Monotonic_Buffer.recall_p b ();
  FStar_Pervasives_Native.__proj__Some__item__v y_opt
let uupd (b : 'a ubuffer) (i : FStar_UInt32.t) (v : 'a) : unit=
  (let h = FStar_HyperStack_ST.get () in
   LowStar_Monotonic_Buffer.upd' b i (FStar_Pervasives_Native.Some v));
  LowStar_Monotonic_Buffer.witness_p b ()
type ('a, 'len) lubuffer = 'a ubuffer
type ('a, 'len, 'r) lubuffer_or_null = 'a ubuffer
let ugcmalloc (r : unit) (len : FStar_UInt32.t) : 'a ubuffer=
  LowStar_Monotonic_Buffer.mgcmalloc () FStar_Pervasives_Native.None len
let ugcmalloc_partial (r : unit) (len : FStar_UInt32.t) : 'a ubuffer=
  LowStar_Monotonic_Buffer.mgcmalloc () FStar_Pervasives_Native.None len
let umalloc (r : unit) (len : FStar_UInt32.t) : 'a ubuffer=
  LowStar_Monotonic_Buffer.mmalloc () FStar_Pervasives_Native.None len
let umalloc_partial (r : unit) (len : FStar_UInt32.t) : 'a ubuffer=
  LowStar_Monotonic_Buffer.mmalloc () FStar_Pervasives_Native.None len
let ualloca (len : FStar_UInt32.t) : 'a ubuffer=
  LowStar_Monotonic_Buffer.malloca FStar_Pervasives_Native.None len
type ('a, 'rrel, 'rel, 'src, 'idxusrc, 'dst, 'idxudst, 'j) valid_j_for_blit =
  unit
type ('a, 'rrel, 'rel, 'src, 'idxusrc, 'dst, 'idxudst, 'j, 'h0,
  'h1) ublit_post_j = unit
let ublit (src : ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (idx_src : FStar_UInt32.t) (dst : 'a ubuffer) (idx_dst : FStar_UInt32.t)
  (len : FStar_UInt32.t) : unit=
  let rec aux j =
    if j = len
    then ()
    else
      if FStar_UInt32.lt j len
      then
        ((let uu___2 =
            LowStar_Monotonic_Buffer.index src (FStar_UInt32.add idx_src j) in
          uupd dst (FStar_UInt32.add idx_dst j) uu___2);
         aux (FStar_UInt32.add j Stdint.Uint32.one))
      else () in
  aux Stdint.Uint32.zero
let witness_initialized (b : 'a ubuffer) (i : Prims.nat) : unit=
  LowStar_Monotonic_Buffer.witness_p b ()
let recall_initialized (b : 'a ubuffer) (i : Prims.nat) : unit=
  LowStar_Monotonic_Buffer.recall_p b ()

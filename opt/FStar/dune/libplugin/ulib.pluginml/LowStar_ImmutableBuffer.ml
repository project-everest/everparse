open Fstarcompiler
open Prims
type ('a, 's1, 's2) immutable_preorder = ('a, 's1, 's2) FStar_Seq_Base.equal
type 'a ibuffer =
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer
let inull (uu___ : unit) : 'a ibuffer= LowStar_Monotonic_Buffer.mnull ()
type 'a ipointer = 'a ibuffer
type 'a ipointer_or_null = 'a ibuffer
let isub (uu___ : unit) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer ->
    FStar_UInt32.t ->
      unit ->
        ('a, ('a, unit, unit) immutable_preorder,
          ('a, unit, unit) immutable_preorder)
          LowStar_Monotonic_Buffer.mbuffer=
  LowStar_Monotonic_Buffer.msub
let ioffset (uu___ : unit) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer ->
    FStar_UInt32.t ->
      ('a, ('a, unit, unit) immutable_preorder,
        ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  LowStar_Monotonic_Buffer.moffset
type ('a, 's, 's1) cpred = ('a, 's, 's1) FStar_Seq_Base.equal
type ('a, 's, 'su) seq_eq = ('a, 'su, Obj.t) FStar_Seq_Base.equal
type ('a, 'b, 's) value_is =
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder, 'b, ('a, 's, unit) seq_eq)
    LowStar_Monotonic_Buffer.witnessed
type ('a, 'len, 's) libuffer =
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer
type ('a, 'len, 'r, 's) libuffer_or_null =
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer
let igcmalloc (r : unit) (init : 'a) (len : FStar_UInt32.t) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  let b = LowStar_Monotonic_Buffer.mgcmalloc () init len in
  LowStar_Monotonic_Buffer.witness_p b (); b
let igcmalloc_and_blit (r : unit) (rrel1 : unit) (rel1 : unit)
  (src : ('a, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer)
  (id_src : FStar_UInt32.t) (len : FStar_UInt32.t) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  let b = LowStar_Monotonic_Buffer.mgcmalloc_and_blit () () () src id_src len in
  let h0 = FStar_HyperStack_ST.get () in
  LowStar_Monotonic_Buffer.witness_p b (); b
let igcmalloc_partial (r : unit) (init : 'a) (len : FStar_UInt32.t) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  igcmalloc () init len
let imalloc (r : unit) (init : 'a) (len : FStar_UInt32.t) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  let b = LowStar_Monotonic_Buffer.mmalloc () init len in
  LowStar_Monotonic_Buffer.witness_p b (); b
let imalloc_and_blit (r : unit) (rrel1 : unit) (rel1 : unit)
  (src : ('a, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer)
  (id_src : FStar_UInt32.t) (len : FStar_UInt32.t) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  let b = LowStar_Monotonic_Buffer.mmalloc_and_blit () () () src id_src len in
  let h0 = FStar_HyperStack_ST.get () in
  LowStar_Monotonic_Buffer.witness_p b (); b
let imalloc_partial (r : unit) (init : 'a) (len : FStar_UInt32.t) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  imalloc () init len
let ialloca (init : 'a) (len : FStar_UInt32.t) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  let b = LowStar_Monotonic_Buffer.malloca init len in
  LowStar_Monotonic_Buffer.witness_p b (); b
let ialloca_and_blit
  (src : ('a, 'rrel1, 'rel1) LowStar_Monotonic_Buffer.mbuffer)
  (id_src : FStar_UInt32.t) (len : FStar_UInt32.t) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  let b = LowStar_Monotonic_Buffer.malloca_and_blit src id_src len in
  let h0 = FStar_HyperStack_ST.get () in
  LowStar_Monotonic_Buffer.witness_p b (); b
let ialloca_of_list (init : 'a Prims.list) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  let b = LowStar_Monotonic_Buffer.malloca_of_list init in
  LowStar_Monotonic_Buffer.witness_p b (); b
let igcmalloc_of_list (r : unit) (init : 'a Prims.list) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  let b = LowStar_Monotonic_Buffer.mgcmalloc_of_list () init in
  LowStar_Monotonic_Buffer.witness_p b (); b
let igcmalloc_of_list_partial (r : unit) (init : 'a Prims.list) :
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer=
  igcmalloc_of_list () init
let witness_contents (b : 'a ibuffer) (s : 'a FStar_Seq_Base.seq) : unit=
  LowStar_Monotonic_Buffer.witness_p b ()
let recall_contents (b : 'a ibuffer) (s : 'a FStar_Seq_Base.seq) : unit=
  LowStar_Monotonic_Buffer.recall_p b ()
let witness_value (b : 'a ibuffer) : unit=
  let h = FStar_HyperStack_ST.get () in
  LowStar_Monotonic_Buffer.witness_p b ()
let recall_value (b : 'a ibuffer) (s : unit) : unit=
  LowStar_Monotonic_Buffer.recall_p b ()

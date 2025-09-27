open Fstarcompiler
open Prims
type ('a, 'b, 'f, 'g) inverses = unit
type ('a, 'b) view =
  | View of Prims.pos * unit * unit 
let uu___is_View : 'a 'b . ('a, 'b) view -> Prims.bool =
  fun projectee -> true
let __proj__View__item__n : 'a 'b . ('a, 'b) view -> Prims.pos =
  fun projectee -> match projectee with | View (n, get, put) -> n
type ('src, 'rrel, 'rel, 'dest) buffer_view =
  | BufferView of ('src, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer *
  ('src, 'dest) view 
let uu___is_BufferView :
  'src 'rrel 'rel 'dest .
    ('src, 'rrel, 'rel, 'dest) buffer_view -> Prims.bool
  = fun projectee -> true
let __proj__BufferView__item__buf :
  'src 'rrel 'rel 'dest .
    ('src, 'rrel, 'rel, 'dest) buffer_view ->
      ('src, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer
  = fun projectee -> match projectee with | BufferView (buf, v) -> buf
let __proj__BufferView__item__v :
  'src 'rrel 'rel 'dest .
    ('src, 'rrel, 'rel, 'dest) buffer_view -> ('src, 'dest) view
  = fun projectee -> match projectee with | BufferView (buf, v) -> v
type 'dest buffer =
  (unit, unit, unit, (Obj.t, Obj.t, Obj.t, 'dest) buffer_view)
    FStar_Pervasives.dtuple4
type ('dest, 'b) as_buffer_t =
  (Obj.t, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
let as_buffer : 'b . 'b buffer -> ('b, Obj.t) as_buffer_t =
  fun v ->
    let uu___ = v in
    match uu___ with
    | FStar_Pervasives.Mkdtuple4
        (uu___1, uu___2, uu___3, BufferView (b1, uu___4)) -> b1
let get_view : 'b . 'b buffer -> (Obj.t, 'b) view =
  fun bv ->
    let uu___ = bv in
    match uu___ with
    | FStar_Pervasives.Mkdtuple4
        (uu___1, uu___2, uu___3, BufferView (uu___4, v)) -> v
type ('b, 'h, 'vb) live =
  (Obj.t, Obj.t, Obj.t, 'h, Obj.t) LowStar_Monotonic_Buffer.live
type ('b, 'vb, 'h, 'hu) mods =
  (Obj.t, 'h, 'hu) LowStar_Monotonic_Buffer.modifies
type ('b, 'vb, 'h, 'hu) modifies =
  (Obj.t, 'h, 'hu) LowStar_Monotonic_Buffer.modifies

open Fstarcompiler
open Prims
type ('a, 'b, 'f, 'g) inverses = unit
type ('a, 'b) view =
  | View of Prims.pos * unit * unit 
let uu___is_View : 'a 'b . ('a, 'b) view -> Prims.bool =
  fun projectee -> true
let __proj__View__item__n : 'a 'b . ('a, 'b) view -> Prims.pos =
  fun projectee -> match projectee with | View (n, get, put) -> n
type ('a, 'rrel, 'rel, 'b) buffer_view =
  | BufferView of ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer * (
  'a, 'b) view 
let uu___is_BufferView :
  'a 'rrel 'rel 'b . ('a, 'rrel, 'rel, 'b) buffer_view -> Prims.bool =
  fun projectee -> true
let __proj__BufferView__item__buf :
  'a 'rrel 'rel 'b .
    ('a, 'rrel, 'rel, 'b) buffer_view ->
      ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer
  = fun projectee -> match projectee with | BufferView (buf, v) -> buf
let __proj__BufferView__item__v :
  'a 'rrel 'rel 'b . ('a, 'rrel, 'rel, 'b) buffer_view -> ('a, 'b) view =
  fun projectee -> match projectee with | BufferView (buf, v) -> v
type 'dest buffer =
  (unit, unit, unit, (Obj.t, Obj.t, Obj.t, 'dest) buffer_view)
    FStar_Pervasives.dtuple4
type ('dest, 'b) as_buffer_t =
  (Obj.t, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
let as_buffer : 'b . 'b buffer -> ('b, Obj.t) as_buffer_t =
  fun v ->
    __proj__BufferView__item__buf
      (FStar_Pervasives.__proj__Mkdtuple4__item___4 v)
let get_view : 'b . 'b buffer -> (Obj.t, 'b) view =
  fun v ->
    __proj__BufferView__item__v
      (FStar_Pervasives.__proj__Mkdtuple4__item___4 v)
type ('b, 'h, 'vb) live =
  (Obj.t, Obj.t, Obj.t, 'h, Obj.t) LowStar_Monotonic_Buffer.live
type ('b, 'vb, 'h, 'hu) modifies =
  (Obj.t, 'h, 'hu) LowStar_Monotonic_Buffer.modifies

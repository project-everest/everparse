open Prims
type ('uuuuu, 'uuuuu1, 'f, 'g) inverses = unit
type ('a, 'b) view =
  | View of Prims.pos * unit * unit 
let uu___is_View : 'a 'b . ('a, 'b) view -> Prims.bool =
  fun projectee -> true
let __proj__View__item__n : 'a 'b . ('a, 'b) view -> Prims.pos =
  fun projectee -> match projectee with | View (n, get, put) -> n
type 'dest buffer =
  | Buffer of unit * Obj.t LowStar_BufferView_Down.buffer * (Obj.t, 'dest)
  view 
let uu___is_Buffer : 'dest . 'dest buffer -> Prims.bool =
  fun projectee -> true
let __proj__Buffer__item__down_buf :
  'dest . 'dest buffer -> Obj.t LowStar_BufferView_Down.buffer =
  fun projectee ->
    match projectee with | Buffer (src, down_buf, v) -> down_buf
let __proj__Buffer__item__v : 'dest . 'dest buffer -> (Obj.t, 'dest) view =
  fun projectee -> match projectee with | Buffer (src, down_buf, v) -> v
type ('b, 'bv) buffer_src = Obj.t
let as_down_buffer : 'b . 'b buffer -> Obj.t LowStar_BufferView_Down.buffer =
  fun bv -> __proj__Buffer__item__down_buf bv
let get_view : 'b . 'b buffer -> (Obj.t, 'b) view =
  fun v -> __proj__Buffer__item__v v
type ('b, 'h, 'vb) live =
  (Obj.t, Obj.t, Obj.t, 'h, Obj.t) LowStar_Monotonic_Buffer.live
type ('b, 'vb, 'h, 'hu) modifies =
  (Obj.t, 'h, 'hu) LowStar_Monotonic_Buffer.modifies

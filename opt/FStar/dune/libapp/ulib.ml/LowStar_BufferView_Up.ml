open Prims
type ('uuuuu, 'uuuuu1, 'f, 'g) inverses = unit
type ('a, 'b) view =
  | View of Prims.pos * unit * unit 
let uu___is_View (projectee : ('a, 'b) view) : Prims.bool= true
let __proj__View__item__n (projectee : ('a, 'b) view) : Prims.pos=
  match projectee with | View (n, get, put) -> n
type 'dest buffer =
  | Buffer of unit * Obj.t LowStar_BufferView_Down.buffer * (Obj.t, 'dest)
  view 
let uu___is_Buffer (projectee : 'dest buffer) : Prims.bool= true
let __proj__Buffer__item__down_buf (projectee : 'dest buffer) :
  Obj.t LowStar_BufferView_Down.buffer=
  match projectee with | Buffer (src, down_buf, v) -> down_buf
let __proj__Buffer__item__v (projectee : 'dest buffer) : (Obj.t, 'dest) view=
  match projectee with | Buffer (src, down_buf, v) -> v
type ('b, 'bv) buffer_src = Obj.t
let as_down_buffer (bv : 'b buffer) : Obj.t LowStar_BufferView_Down.buffer=
  __proj__Buffer__item__down_buf bv
let get_view (v : 'b buffer) : (Obj.t, 'b) view= __proj__Buffer__item__v v
type ('b, 'h, 'vb) live =
  (Obj.t, Obj.t, Obj.t, 'h, Obj.t) LowStar_Monotonic_Buffer.live
type ('b, 'vb, 'h, 'hu) modifies =
  (Obj.t, 'h, 'hu) LowStar_Monotonic_Buffer.modifies

open Prims
type ('a, 'b, 'rua, 'rub, 'dummyV0, 'dummyV1) lex_t =
  | Left_lex of 'a * 'a * 'b * 'b * 'rua 
  | Right_lex of 'a * 'b * 'b * 'rub 
let uu___is_Left_lex (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : Prims.bool=
  match projectee with
  | Left_lex (x1, x2, y1, y2, _4) -> true
  | uu___2 -> false
let __proj__Left_lex__item__x1 (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : 'a=
  match projectee with | Left_lex (x1, x2, y1, y2, _4) -> x1
let __proj__Left_lex__item__x2 (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : 'a=
  match projectee with | Left_lex (x1, x2, y1, y2, _4) -> x2
let __proj__Left_lex__item__y1 (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : 'b=
  match projectee with | Left_lex (x1, x2, y1, y2, _4) -> y1
let __proj__Left_lex__item__y2 (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : 'b=
  match projectee with | Left_lex (x1, x2, y1, y2, _4) -> y2
let __proj__Left_lex__item___4 (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : 'rua=
  match projectee with | Left_lex (x1, x2, y1, y2, _4) -> _4
let uu___is_Right_lex (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : Prims.bool=
  match projectee with | Right_lex (x, y1, y2, _3) -> true | uu___2 -> false
let __proj__Right_lex__item__x (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : 'a=
  match projectee with | Right_lex (x, y1, y2, _3) -> x
let __proj__Right_lex__item__y1 (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : 'b=
  match projectee with | Right_lex (x, y1, y2, _3) -> y1
let __proj__Right_lex__item__y2 (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : 'b=
  match projectee with | Right_lex (x, y1, y2, _3) -> y2
let __proj__Right_lex__item___3 (uu___ : ('a, 'b) Prims.dtuple2)
  (uu___1 : ('a, 'b) Prims.dtuple2)
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t) : 'rub=
  match projectee with | Right_lex (x, y1, y2, _3) -> _3

type ('a, 'b, 'rua, 'rub, 'uuuuu, 'uuuuu1) lex_aux = Obj.t
type ('a, 'b, 'rua, 'rub, 'wfua, 'wfub, 'uuuuu, 'uuuuu1) lex = Obj.t
let tuple_to_dep_tuple (x : ('a * 'b)) : ('a, 'b) Prims.dtuple2=
  Prims.Mkdtuple2
    ((FStar_Pervasives_Native.fst x), (FStar_Pervasives_Native.snd x))
type ('a, 'b, 'rua, 'rub, 'x, 'y) lex_t_non_dep =
  ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t

type ('a, 'b, 'rua, 'rub, 'dummyV0, 'dummyV1) sym =
  | Left_sym of 'a * 'a * 'b * 'rua 
  | Right_sym of 'a * 'b * 'b * 'rub 
let uu___is_Left_sym (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : Prims.bool=
  match projectee with | Left_sym (x1, x2, y, _3) -> true | uu___2 -> false
let __proj__Left_sym__item__x1 (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : 'a=
  match projectee with | Left_sym (x1, x2, y, _3) -> x1
let __proj__Left_sym__item__x2 (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : 'a=
  match projectee with | Left_sym (x1, x2, y, _3) -> x2
let __proj__Left_sym__item__y (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : 'b=
  match projectee with | Left_sym (x1, x2, y, _3) -> y
let __proj__Left_sym__item___3 (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : 'rua=
  match projectee with | Left_sym (x1, x2, y, _3) -> _3
let uu___is_Right_sym (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : Prims.bool=
  match projectee with | Right_sym (x, y1, y2, _3) -> true | uu___2 -> false
let __proj__Right_sym__item__x (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : 'a=
  match projectee with | Right_sym (x, y1, y2, _3) -> x
let __proj__Right_sym__item__y1 (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : 'b=
  match projectee with | Right_sym (x, y1, y2, _3) -> y1
let __proj__Right_sym__item__y2 (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : 'b=
  match projectee with | Right_sym (x, y1, y2, _3) -> y2
let __proj__Right_sym__item___3 (uu___ : ('a * 'b)) (uu___1 : ('a * 'b))
  (projectee : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) : 'rub=
  match projectee with | Right_sym (x, y1, y2, _3) -> _3
let sym_sub_lex (t1 : ('a * 'b)) (t2 : ('a * 'b))
  (p : ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) sym) :
  ('a, 'b, 'rua, 'rub, Obj.t, Obj.t) lex_t_non_dep=
  match p with
  | Left_sym (x1, x2, y, p1) -> Left_lex (x1, x2, y, y, p1)
  | Right_sym (x, y1, y2, p1) -> Right_lex (x, y1, y2, p1)


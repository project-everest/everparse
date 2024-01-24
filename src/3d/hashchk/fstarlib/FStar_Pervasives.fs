#light "off"
module FStar_Pervasives
open Prims

type pattern =
unit








type eqtype_u =
unit


type 'p spinoff =
'p


let id = (fun ( x  :  'a ) -> x)


type trivial_pure_post =
unit


type ambient =
unit


let normalize_term = (fun ( x  :  'uuuuu ) -> x)


type 'a normalize =
'a

type norm_step =
| Simpl
| Weak
| HNF
| Primops
| Delta
| Zeta
| ZetaFull
| Iota
| NBE
| Reify
| NormDebug
| UnfoldOnly of Prims.string Prims.list
| UnfoldFully of Prims.string Prims.list
| UnfoldAttr of Prims.string Prims.list
| UnfoldQual of Prims.string Prims.list
| UnfoldNamespace of Prims.string Prims.list
| Unmeta
| Unascribe


let uu___is_Simpl : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| Simpl -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Weak : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| Weak -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_HNF : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| HNF -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Primops : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| Primops -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Delta : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| Delta -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Zeta : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| Zeta -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_ZetaFull : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| ZetaFull -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Iota : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| Iota -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_NBE : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| NBE -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Reify : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| Reify -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_NormDebug : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| NormDebug -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_UnfoldOnly : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__UnfoldOnly__item___0 : norm_step  ->  Prims.string Prims.list = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let uu___is_UnfoldFully : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldFully (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__UnfoldFully__item___0 : norm_step  ->  Prims.string Prims.list = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldFully (_0) -> begin
_0
end))


let uu___is_UnfoldAttr : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldAttr (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__UnfoldAttr__item___0 : norm_step  ->  Prims.string Prims.list = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldAttr (_0) -> begin
_0
end))


let uu___is_UnfoldQual : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldQual (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__UnfoldQual__item___0 : norm_step  ->  Prims.string Prims.list = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldQual (_0) -> begin
_0
end))


let uu___is_UnfoldNamespace : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldNamespace (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__UnfoldNamespace__item___0 : norm_step  ->  Prims.string Prims.list = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| UnfoldNamespace (_0) -> begin
_0
end))


let uu___is_Unmeta : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| Unmeta -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Unascribe : norm_step  ->  Prims.bool = (fun ( projectee  :  norm_step ) -> (match (projectee) with
| Unascribe -> begin
true
end
| uu___ -> begin
false
end))


let simplify : norm_step = Simpl


let weak : norm_step = Weak


let hnf : norm_step = HNF


let primops : norm_step = Primops


let delta : norm_step = Delta


let norm_debug : norm_step = NormDebug


let zeta : norm_step = Zeta


let zeta_full : norm_step = ZetaFull


let iota : norm_step = Iota


let nbe : norm_step = NBE


let reify_ : norm_step = Reify


let delta_only : Prims.string Prims.list  ->  norm_step = (fun ( s  :  Prims.string Prims.list ) -> UnfoldOnly (s))


let delta_fully : Prims.string Prims.list  ->  norm_step = (fun ( s  :  Prims.string Prims.list ) -> UnfoldFully (s))


let delta_attr : Prims.string Prims.list  ->  norm_step = (fun ( s  :  Prims.string Prims.list ) -> UnfoldAttr (s))


let delta_qualifier : Prims.string Prims.list  ->  norm_step = (fun ( s  :  Prims.string Prims.list ) -> UnfoldAttr (s))


let delta_namespace : Prims.string Prims.list  ->  norm_step = (fun ( s  :  Prims.string Prims.list ) -> UnfoldNamespace (s))


let unmeta : norm_step = Unmeta


let unascribe : norm_step = Unascribe


let norm : norm_step Prims.list  ->  unit  ->  obj  ->  obj = (fun ( uu___  :  norm_step Prims.list ) ( uu___1  :  unit ) ( x  :  obj ) -> x)


type pure_return =
unit


type 'wp1 pure_bind_wp =
'wp1


type pure_if_then_else =
unit


type pure_ite_wp =
unit


type pure_close_wp =
unit


type pure_null_wp =
unit


type pure_assert_wp =
unit


type pure_assume_wp =
unit


type div_hoare_to_wp =
unit


type st_pre_h =
unit


type st_post_h' =
unit


type st_post_h =
unit


type st_wp_h =
unit


type 'p st_return =
'p


type 'wp1 st_bind_wp =
'wp1


type st_if_then_else =
unit


type st_ite_wp =
unit


type st_stronger =
unit


type st_close_wp =
unit


type st_trivial =
unit

type 'a result =
| V of 'a
| E of Prims.exn
| Err of Prims.string


let uu___is_V = (fun ( projectee  :  'a result ) -> (match (projectee) with
| V (v) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__V__item__v = (fun ( projectee  :  'a result ) -> (match (projectee) with
| V (v) -> begin
v
end))


let uu___is_E = (fun ( projectee  :  'a result ) -> (match (projectee) with
| E (e) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__E__item__e = (fun ( projectee  :  'a result ) -> (match (projectee) with
| E (e) -> begin
e
end))


let uu___is_Err = (fun ( projectee  :  'a result ) -> (match (projectee) with
| Err (msg) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__Err__item__msg = (fun ( projectee  :  'a result ) -> (match (projectee) with
| Err (msg) -> begin
msg
end))


type ex_pre =
unit


type ex_post' =
unit


type ex_post =
unit


type ex_wp =
unit


type 'p ex_return =
'p


type ex_bind_wp =
unit


type ex_if_then_else =
unit


type ex_ite_wp =
unit


type ex_stronger =
unit


type ex_close_wp =
unit


type 'wp ex_trivial =
'wp


type 'wp lift_div_exn =
'wp


type all_pre_h =
unit


type all_post_h' =
unit


type all_post_h =
unit


type all_wp_h =
unit


type 'p all_return =
'p


type 'wp1 all_bind_wp =
'wp1


type all_if_then_else =
unit


type all_ite_wp =
unit


type all_stronger =
unit


type all_close_wp =
unit


type all_trivial =
unit


type inversion =
unit

type ('a, 'b) either =
| Inl of 'a
| Inr of 'b


let uu___is_Inl = (fun ( projectee  :  ('a, 'b) either ) -> (match (projectee) with
| Inl (v) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__Inl__item__v = (fun ( projectee  :  ('a, 'b) either ) -> (match (projectee) with
| Inl (v) -> begin
v
end))


let uu___is_Inr = (fun ( projectee  :  ('a, 'b) either ) -> (match (projectee) with
| Inr (v) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__Inr__item__v = (fun ( projectee  :  ('a, 'b) either ) -> (match (projectee) with
| Inr (v) -> begin
v
end))


let dfst = (fun ( t  :  ('a, 'b) Prims.dtuple2 ) -> (Prims.__proj__Mkdtuple2__item___1 t))


let dsnd = (fun ( t  :  ('a, 'b) Prims.dtuple2 ) -> (Prims.__proj__Mkdtuple2__item___2 t))

type ('a, 'b, 'c) dtuple3 =
| Mkdtuple3 of 'a * 'b * 'c


let uu___is_Mkdtuple3 = (fun ( projectee  :  ('a, 'b, 'c) dtuple3 ) -> true)


let __proj__Mkdtuple3__item___1 = (fun ( projectee  :  ('a, 'b, 'c) dtuple3 ) -> (match (projectee) with
| Mkdtuple3 (_1, _2, _3) -> begin
_1
end))


let __proj__Mkdtuple3__item___2 = (fun ( projectee  :  ('a, 'b, 'c) dtuple3 ) -> (match (projectee) with
| Mkdtuple3 (_1, _2, _3) -> begin
_2
end))


let __proj__Mkdtuple3__item___3 = (fun ( projectee  :  ('a, 'b, 'c) dtuple3 ) -> (match (projectee) with
| Mkdtuple3 (_1, _2, _3) -> begin
_3
end))

type ('a, 'b, 'c, 'd) dtuple4 =
| Mkdtuple4 of 'a * 'b * 'c * 'd


let uu___is_Mkdtuple4 = (fun ( projectee  :  ('a, 'b, 'c, 'd) dtuple4 ) -> true)


let __proj__Mkdtuple4__item___1 = (fun ( projectee  :  ('a, 'b, 'c, 'd) dtuple4 ) -> (match (projectee) with
| Mkdtuple4 (_1, _2, _3, _4) -> begin
_1
end))


let __proj__Mkdtuple4__item___2 = (fun ( projectee  :  ('a, 'b, 'c, 'd) dtuple4 ) -> (match (projectee) with
| Mkdtuple4 (_1, _2, _3, _4) -> begin
_2
end))


let __proj__Mkdtuple4__item___3 = (fun ( projectee  :  ('a, 'b, 'c, 'd) dtuple4 ) -> (match (projectee) with
| Mkdtuple4 (_1, _2, _3, _4) -> begin
_3
end))


let __proj__Mkdtuple4__item___4 = (fun ( projectee  :  ('a, 'b, 'c, 'd) dtuple4 ) -> (match (projectee) with
| Mkdtuple4 (_1, _2, _3, _4) -> begin
_4
end))

type ('a, 'b, 'c, 'd, 'e) dtuple5 =
| Mkdtuple5 of 'a * 'b * 'c * 'd * 'e


let uu___is_Mkdtuple5 = (fun ( projectee  :  ('a, 'b, 'c, 'd, 'e) dtuple5 ) -> true)


let __proj__Mkdtuple5__item___1 = (fun ( projectee  :  ('a, 'b, 'c, 'd, 'e) dtuple5 ) -> (match (projectee) with
| Mkdtuple5 (_1, _2, _3, _4, _5) -> begin
_1
end))


let __proj__Mkdtuple5__item___2 = (fun ( projectee  :  ('a, 'b, 'c, 'd, 'e) dtuple5 ) -> (match (projectee) with
| Mkdtuple5 (_1, _2, _3, _4, _5) -> begin
_2
end))


let __proj__Mkdtuple5__item___3 = (fun ( projectee  :  ('a, 'b, 'c, 'd, 'e) dtuple5 ) -> (match (projectee) with
| Mkdtuple5 (_1, _2, _3, _4, _5) -> begin
_3
end))


let __proj__Mkdtuple5__item___4 = (fun ( projectee  :  ('a, 'b, 'c, 'd, 'e) dtuple5 ) -> (match (projectee) with
| Mkdtuple5 (_1, _2, _3, _4, _5) -> begin
_4
end))


let __proj__Mkdtuple5__item___5 = (fun ( projectee  :  ('a, 'b, 'c, 'd, 'e) dtuple5 ) -> (match (projectee) with
| Mkdtuple5 (_1, _2, _3, _4, _5) -> begin
_5
end))


let rec false_elim = (fun ( uu___  :  unit ) -> (false_elim ()))

type __internal_ocaml_attributes =
| PpxDerivingShow
| PpxDerivingShowConstant of Prims.string
| PpxDerivingYoJson
| CInline
| Substitute
| Gc
| Comment of Prims.string
| CPrologue of Prims.string
| CEpilogue of Prims.string
| CConst of Prims.string
| CCConv of Prims.string
| CAbstractStruct
| CIfDef
| CMacro
| CNoInline


let uu___is_PpxDerivingShow : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| PpxDerivingShow -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_PpxDerivingShowConstant : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__PpxDerivingShowConstant__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
_0
end))


let uu___is_PpxDerivingYoJson : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| PpxDerivingYoJson -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_CInline : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CInline -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Substitute : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| Substitute -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Gc : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| Gc -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Comment : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__Comment__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| Comment (_0) -> begin
_0
end))


let uu___is_CPrologue : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CPrologue (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__CPrologue__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CPrologue (_0) -> begin
_0
end))


let uu___is_CEpilogue : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CEpilogue (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__CEpilogue__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CEpilogue (_0) -> begin
_0
end))


let uu___is_CConst : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CConst (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__CConst__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CConst (_0) -> begin
_0
end))


let uu___is_CCConv : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CCConv (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__CCConv__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CCConv (_0) -> begin
_0
end))


let uu___is_CAbstractStruct : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CAbstractStruct -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_CIfDef : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CIfDef -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_CMacro : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CMacro -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_CNoInline : __internal_ocaml_attributes  ->  Prims.bool = (fun ( projectee  :  __internal_ocaml_attributes ) -> (match (projectee) with
| CNoInline -> begin
true
end
| uu___ -> begin
false
end))


let singleton = (fun ( x  :  'uuuuu ) -> x)


type 'a eqtype_as_type =
'a


let coerce_eq = (fun ( uu___1  :  unit ) ( uu___  :  'a ) -> ((fun ( uu___  :  unit ) ( x  :  'a ) -> (Prims.unsafe_coerce x)) uu___1 uu___))





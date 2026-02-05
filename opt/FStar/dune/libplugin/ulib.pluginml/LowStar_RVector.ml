open Fstarcompiler
open Prims
type ('rst, 'a, 'rg) copyable =
  | Cpy of ('rst -> 'a -> 'a -> unit) 
let uu___is_Cpy (rg : ('rst, 'a) LowStar_Regional.regional)
  (projectee : ('rst, 'a, Obj.t) copyable) : Prims.bool= true
let __proj__Cpy__item__copy (rg : ('rst, 'a) LowStar_Regional.regional)
  (projectee : ('rst, 'a, Obj.t) copyable) : 'rst -> 'a -> 'a -> unit=
  match projectee with | Cpy copy -> copy
type ('a, 'rst, 'rg) rvector = 'a LowStar_Vector.vector
type ('a, 'rst, 'rg, 'h, 'rs, 'i, 'j) rs_elems_inv = unit
type ('a, 'rst, 'rg, 'h, 'rv, 'i, 'j) rv_elems_inv = unit
type ('a, 'rst, 'rg, 'h, 'rv) elems_inv = unit
type ('a, 'rst, 'rg, 'rs, 'prid, 'i, 'j) rs_elems_reg = unit
type ('a, 'rst, 'rg, 'h, 'rv, 'i, 'j) rv_elems_reg = unit
type ('a, 'rst, 'rg, 'h, 'rv) elems_reg = unit
type ('a, 'rst, 'rg, 'h, 'rv) rv_itself_inv = unit
type ('a, 'rst, 'rg, 'h, 'rv) rv_inv = unit
let alloc_empty (rg : ('rst, 'a) LowStar_Regional.regional) :
  ('a, 'rst, Obj.t) rvector=
  LowStar_Vector.Vec
    (Stdint.Uint32.zero, Stdint.Uint32.zero,
      (LowStar_Monotonic_Buffer.mnull ()))
let rec alloc_ :
  'a 'rst .
    ('rst, 'a) LowStar_Regional.regional ->
      ('a, 'rst, Obj.t) rvector -> LowStar_Vector.uint32_t -> unit
  =
  fun rg rv cidx ->
    let hh0 = FStar_HyperStack_ST.get () in
    if cidx = Stdint.Uint32.zero
    then ()
    else
      (FStar_HyperStack_ST.new_region ();
       (let v =
          LowStar_Regional.__proj__Rgl__item__r_alloc rg
            (LowStar_Regional.__proj__Rgl__item__state rg) () in
        let hh1 = FStar_HyperStack_ST.get () in
        LowStar_Vector.assign rv (FStar_UInt32.sub cidx Stdint.Uint32.one) v;
        (let hh2 = FStar_HyperStack_ST.get () in
         alloc_ rg rv (FStar_UInt32.sub cidx Stdint.Uint32.one);
         (let hh3 = FStar_HyperStack_ST.get () in ()))))
let alloc_rid (rg : ('rst, 'a) LowStar_Regional.regional)
  (len : LowStar_Vector.uint32_t) (rid : unit) : ('a, 'rst, Obj.t) rvector=
  let vec =
    LowStar_Vector.alloc_rid len
      (LowStar_Regional.__proj__Rgl__item__dummy rg) () in
  alloc_ rg vec len; vec
let alloc_reserve (rg : ('rst, 'a) LowStar_Regional.regional)
  (len : LowStar_Vector.uint32_t) (rid : unit) : ('a, 'rst, Obj.t) rvector=
  LowStar_Vector.alloc_reserve len
    (LowStar_Regional.__proj__Rgl__item__dummy rg) ()
let alloc (rg : ('rst, 'a) LowStar_Regional.regional)
  (len : LowStar_Vector.uint32_t) : ('a, 'rst, Obj.t) rvector=
  FStar_HyperStack_ST.new_region (); alloc_rid rg len ()
let insert (rg : ('rst, 'a) LowStar_Regional.regional)
  (rv : ('a, 'rst, Obj.t) rvector) (v : 'a) : ('a, 'rst, Obj.t) rvector=
  let hh0 = FStar_HyperStack_ST.get () in
  let irv = LowStar_Vector.insert rv v in
  let hh1 = FStar_HyperStack_ST.get () in irv
let insert_copy (rg : ('rst, 'a) LowStar_Regional.regional)
  (cp : ('rst, 'a, Obj.t) copyable) (rv : ('a, 'rst, Obj.t) rvector) 
  (v : 'a) : ('a, 'rst, Obj.t) rvector=
  let hh0 = FStar_HyperStack_ST.get () in
  FStar_HyperStack_ST.new_region ();
  (let nv =
     LowStar_Regional.__proj__Rgl__item__r_alloc rg
       (LowStar_Regional.__proj__Rgl__item__state rg) () in
   let hh1 = FStar_HyperStack_ST.get () in
   ((match cp with | Cpy copy -> copy))
     (LowStar_Regional.__proj__Rgl__item__state rg) v nv;
   (let hh2 = FStar_HyperStack_ST.get () in insert rg rv nv))
let assign (rg : ('rst, 'a) LowStar_Regional.regional)
  (rv : ('a, 'rst, Obj.t) rvector) (i : LowStar_Vector.uint32_t) (v : 'a) :
  unit=
  let hh0 = FStar_HyperStack_ST.get () in
  LowStar_Vector.assign rv i v; (let hh1 = FStar_HyperStack_ST.get () in ())
let assign_copy (rg : ('rst, 'a) LowStar_Regional.regional)
  (cp : ('rst, 'a, Obj.t) copyable) (rv : ('a, 'rst, Obj.t) rvector)
  (i : LowStar_Vector.uint32_t) (v : 'a) : unit=
  let hh0 = FStar_HyperStack_ST.get () in
  (let uu___1 = LowStar_Vector.index rv i in
   (match cp with | Cpy copy -> copy)
     (LowStar_Regional.__proj__Rgl__item__state rg) v uu___1);
  (let hh1 = FStar_HyperStack_ST.get () in ())
let rec free_elems :
  'a 'rst .
    ('rst, 'a) LowStar_Regional.regional ->
      ('a, 'rst, Obj.t) rvector -> LowStar_Vector.uint32_t -> unit
  =
  fun rg rv idx ->
    let hh0 = FStar_HyperStack_ST.get () in
    (let uu___1 = LowStar_Vector.index rv idx in
     LowStar_Regional.__proj__Rgl__item__r_free rg
       (LowStar_Regional.__proj__Rgl__item__state rg) uu___1);
    (let hh1 = FStar_HyperStack_ST.get () in
     if idx <> Stdint.Uint32.zero
     then free_elems rg rv (FStar_UInt32.sub idx Stdint.Uint32.one)
     else ())
let flush (rg : ('rst, 'a) LowStar_Regional.regional)
  (rv : ('a, 'rst, Obj.t) rvector) (i : LowStar_Vector.uint32_t) :
  ('a, 'rst, Obj.t) rvector=
  let hh0 = FStar_HyperStack_ST.get () in
  if i = Stdint.Uint32.zero
  then ()
  else free_elems rg rv (FStar_UInt32.sub i Stdint.Uint32.one);
  (let hh1 = FStar_HyperStack_ST.get () in
   let frv =
     LowStar_Vector.flush rv (LowStar_Regional.__proj__Rgl__item__dummy rg) i in
   let hh2 = FStar_HyperStack_ST.get () in frv)
let rec free_elems_from :
  'a 'rst .
    ('rst, 'a) LowStar_Regional.regional ->
      ('a, 'rst, Obj.t) rvector -> LowStar_Vector.uint32_t -> unit
  =
  fun rg rv idx ->
    let hh0 = FStar_HyperStack_ST.get () in
    (let uu___1 = LowStar_Vector.index rv idx in
     LowStar_Regional.__proj__Rgl__item__r_free rg
       (LowStar_Regional.__proj__Rgl__item__state rg) uu___1);
    (let hh1 = FStar_HyperStack_ST.get () in
     if
       FStar_UInt32.lt (FStar_UInt32.add idx Stdint.Uint32.one)
         (match rv with | LowStar_Vector.Vec (sz, cap, vs) -> sz)
     then free_elems_from rg rv (FStar_UInt32.add idx Stdint.Uint32.one)
     else ())
let shrink (rg : ('rst, 'a) LowStar_Regional.regional)
  (rv : ('a, 'rst, Obj.t) rvector) (new_size : LowStar_Vector.uint32_t) :
  ('a, 'rst, Obj.t) rvector=
  let size = match rv with | LowStar_Vector.Vec (sz, cap, vs) -> sz in
  let hh0 = FStar_HyperStack_ST.get () in
  if FStar_UInt32.gte new_size size
  then rv
  else
    (free_elems_from rg rv new_size;
     (let hh1 = FStar_HyperStack_ST.get () in
      let frv = LowStar_Vector.shrink rv new_size in
      let hh2 = FStar_HyperStack_ST.get () in frv))
let free (rg : ('rst, 'a) LowStar_Regional.regional)
  (rv : ('a, 'rst, Obj.t) rvector) : unit=
  let hh0 = FStar_HyperStack_ST.get () in
  if
    (match rv with | LowStar_Vector.Vec (sz, cap, vs) -> sz) =
      Stdint.Uint32.zero
  then ()
  else
    free_elems rg rv
      (FStar_UInt32.sub
         (match rv with | LowStar_Vector.Vec (sz, cap, vs) -> sz)
         Stdint.Uint32.one);
  (let hh1 = FStar_HyperStack_ST.get () in LowStar_Vector.free rv)

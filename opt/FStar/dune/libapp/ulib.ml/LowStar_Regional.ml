open Prims
type ('st, 'a) regional =
  | Rgl of 'st * unit * unit * 'a * unit * unit * unit * unit * unit * unit *
  unit * ('st -> unit -> 'a) * ('st -> 'a -> unit) 
let uu___is_Rgl (projectee : ('st, 'a) regional) : Prims.bool= true
let __proj__Rgl__item__state (projectee : ('st, 'a) regional) : 'st=
  match projectee with
  | Rgl
      (state, region_of, loc_of, dummy, r_inv, r_inv_reg, repr, r_repr,
       r_sep, irepr, r_alloc_p, r_alloc, r_free)
      -> state
let __proj__Rgl__item__dummy (projectee : ('st, 'a) regional) : 'a=
  match projectee with
  | Rgl
      (state, region_of, loc_of, dummy, r_inv, r_inv_reg, repr, r_repr,
       r_sep, irepr, r_alloc_p, r_alloc, r_free)
      -> dummy
let __proj__Rgl__item__r_alloc (projectee : ('st, 'a) regional) :
  'st -> unit -> 'a=
  match projectee with
  | Rgl
      (state, region_of, loc_of, dummy, r_inv, r_inv_reg, repr, r_repr,
       r_sep, irepr, r_alloc_p, r_alloc, r_free)
      -> r_alloc
let __proj__Rgl__item__r_free (projectee : ('st, 'a) regional) :
  'st -> 'a -> unit=
  match projectee with
  | Rgl
      (state, region_of, loc_of, dummy, r_inv, r_inv_reg, repr, r_repr,
       r_sep, irepr, r_alloc_p, r_alloc, r_free)
      -> r_free
type ('a, 'rst, 'rg, 'uuuuu, 'uuuuu1) rg_inv = Obj.t
let rg_dummy (rg : ('rst, 'a) regional) : 'a= __proj__Rgl__item__dummy rg
let rg_alloc (rg : ('rst, 'a) regional) (r : unit) : 'a=
  __proj__Rgl__item__r_alloc rg (__proj__Rgl__item__state rg) ()
let rg_free (rg : ('rst, 'a) regional) (v : 'a) : unit=
  __proj__Rgl__item__r_free rg (__proj__Rgl__item__state rg) v

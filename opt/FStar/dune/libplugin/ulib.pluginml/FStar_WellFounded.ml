open Fstarcompiler
open Prims
type 'a binrel = unit
type ('a, 'r) well_founded = unit
let rec fix_F :
  'aa 'r 'p . ('aa -> ('aa -> 'r -> 'p) -> 'p) -> 'aa -> unit -> 'p =
  fun f x a -> f x (fun y h -> fix_F f y ())
let fix (rwf : unit) (p : unit) (f : 'aa -> ('aa -> 'r -> Obj.t) -> Obj.t)
  (x : 'aa) : Obj.t= fix_F f x ()
type ('a, 'rel) is_well_founded = unit
type 'a well_founded_relation = unit
type ('a, 'rel, 'f, 'uuuuu, 'uuuuu1) as_well_founded = 'rel

type ('a, 'r, 'subur, 'subuw, 'ruwf, 'uuuuu, 'uuuuu1) subrelation_as_wf =
  'subur
type ('a, 'b, 'rub, 'f, 'x, 'y) inverse_image = 'rub


open Fstarcompiler
open Prims
let bool_of_or (t : ('p, 'q) Prims.sum) : Prims.bool=
  match t with | Prims.Left uu___ -> true | Prims.Right uu___ -> false
type 'p pow = unit
type ('a, 'b) retract =
  | MkR of unit * unit * unit 
let uu___is_MkR (projectee : ('a, 'b) retract) : Prims.bool= true
type ('a, 'b) retract_cond =
  | MkC of unit * unit * unit 
let uu___is_MkC (projectee : ('a, 'b) retract_cond) : Prims.bool= true
let false_elim (uu___ : unit) : 'a=
  (fun f -> Obj.magic (failwith "unreachable")) uu___
type u = unit

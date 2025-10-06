open Prims
type 'k less_than = Prims.int
type 'k greater_than = Prims.int
type 'x not_less_than = Obj.t greater_than
type 'x not_greater_than = Obj.t less_than
let (coerce_to_less_than :
  Prims.int -> Obj.t not_greater_than -> Obj.t less_than) =
  fun n -> fun x -> x
let (coerce_to_not_less_than :
  Prims.int -> Obj.t greater_than -> Obj.t not_less_than) =
  fun n -> fun x -> x
let (interval_condition : Prims.int -> Prims.int -> Prims.int -> Prims.bool)
  = fun x -> fun y -> fun t -> (x <= t) && (t < y)
type ('x, 'y) interval_type = unit
type ('x, 'y) interval = Prims.int
type ('x, 'y) efrom_eto = (Obj.t, 'y) interval
type ('x, 'y) efrom_ito = (Obj.t, Obj.t) interval
type ('x, 'y) ifrom_eto = ('x, 'y) interval
type ('x, 'y) ifrom_ito = ('x, Obj.t) interval
type 'k under = (Obj.t, 'k) interval
let (interval_size : Prims.int -> Prims.int -> unit -> Prims.nat) =
  fun x -> fun y -> fun interval1 -> if y >= x then y - x else Prims.int_zero
type ('x, 'y, 'interval1) counter_for = Obj.t under
let (closed_interval_size : Prims.int -> Prims.int -> Prims.nat) =
  fun x -> fun y -> interval_size x (y + Prims.int_one) ()
let (indices_seq : Prims.nat -> Obj.t under FStar_Seq_Base.seq) =
  fun n -> FStar_Seq_Base.init n (fun x -> x)

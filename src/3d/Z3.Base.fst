module Z3.Base
open FStar.All

noeq
type z3 = {
  from_z3: unit -> ML string;
  to_z3: string -> ML unit;
}

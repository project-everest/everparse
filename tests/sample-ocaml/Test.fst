module Test
open FStar.HyperStack.ST

module B = LowStar.Buffer
module LP = LowParse.Spec.Base
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module Cast = FStar.Int.Cast

let employee_test
  (b: LP.bytes)
: Tot U16.t
= match LP.parse Employee.employee_parser b with
  | None -> 0us
  | Some (emp, _) ->
    emp.Employee.salary

let main
  ()
: ST C.exit_code
    (requires (fun h -> True))
    (ensures (fun _ _ _ -> True))
= C.EXIT_SUCCESS

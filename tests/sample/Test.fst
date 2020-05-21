module Test
open FStar.HyperStack.ST

module B = LowStar.Buffer
module LP = LowParse.Low.Int
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module Cast = FStar.Int.Cast

let employee_test
  (b: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (pos: U32.t { U32.v pos <= U32.v b.LP.len })
: Stack U16.t
  (requires (fun mem ->
    B.live mem b.LP.base
  ))
  (ensures (fun _ _ _ -> True))
= let sz = Employee.employee_validator b (Cast.uint32_to_uint64 pos) in
  if LP.is_error sz
  then 0us
  else
    let pos1 = Employee.accessor_employee_salary b pos in
    LP.read_u16 b pos1

let main
  (argc: Int32.t)
  (argv: LowStar.Buffer.buffer C.String.t)
: ST C.exit_code
    (requires (fun h -> True))
    (ensures (fun _ _ _ -> True))
= C.EXIT_SUCCESS

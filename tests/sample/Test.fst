module Test
open FStar.HyperStack.ST

module B = LowStar.Buffer
module LP = LowParse.Low.Int
module U32 = FStar.UInt32
module U16 = FStar.UInt16

let employee_test
  (b: LP.slice (B.trivial_preorder _) (B.trivial_preorder _) { U32.v b.LP.len <= U32.v LP.validator_max_length })
  (pos: U32.t { U32.v pos <= U32.v b.LP.len })
: Stack U16.t
  (requires (fun mem ->
    B.live mem b.LP.base
  ))
  (ensures (fun _ _ _ -> True))
= let sz = Employee.employee_validator b pos in
  if U32.lt LP.validator_max_length sz
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

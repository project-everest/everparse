module Test
open FStar.HyperStack.ST

let main
  (argc: Int32.t)
  (argv: LowStar.Buffer.buffer C.String.t)
: ST C.exit_code
    (requires (fun h -> True))
    (ensures (fun _ _ _ -> True))
= C.EXIT_SUCCESS

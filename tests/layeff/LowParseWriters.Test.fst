module LowParseWriters.Test
open LowParseWriters

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

let test_read
  (inv: memory_invariant)
  ()
: HST.Stack (result bool)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read bool True (fun _ -> True) (fun _ -> False) inv (fun _ -> test_read3 inv (fun () -> false))

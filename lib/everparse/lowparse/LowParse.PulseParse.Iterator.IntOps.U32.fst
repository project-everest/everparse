module LowParse.PulseParse.Iterator.IntOps.U32

(* [int_ops] instance for [U32.t] counts/offsets (e.g. ASN.1 SEQUENCE OF
   element counts). Kept in its own module so that the rescued
   [LowParse.PulseParse.Iterator.IntOps] stays verbatim. *)

open LowParse.PulseParse.Iterator.IntOps

module SZ = FStar.SizeT
module U32 = FStar.UInt32

inline_for_extraction
let u32_ops : int_ops U32.t = {
  fits = (fun (n: nat) -> (n < pow2 32 <: prop));
  v    = (fun x -> U32.v x);
  zero = 0ul;
  one  = 1ul;
  add  = (fun x y -> U32.add x y);
  sub  = (fun x y -> U32.sub x y);
  eq   = (fun x y -> x = y);
  lt   = (fun x y -> U32.lt x y);
  lte  = (fun x y -> U32.lte x y);
  gt   = (fun x y -> U32.gt x y);
  gte  = (fun x y -> U32.gte x y);
  to_sizet = (fun x -> SZ.uint32_to_sizet x);   // pre SZ.fits (U32.v x) => fits disjunct
  of_sizet = (fun s -> SZ.sizet_to_uint32 s);   // pre SZ.v s < 2^32, so no truncation
}

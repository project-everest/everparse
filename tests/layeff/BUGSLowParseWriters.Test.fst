module BUGSLowParseWriters.Test
open LowParseWriters.Parsers

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module LPI = LowParse.Low.Int
module HS = FStar.HyperStack
module U32 = FStar.UInt32

(* These do not extract *)

inline_for_extraction
noextract
let write_two_ints_ifthenelse
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit parse_empty (parse_u32 `parse_pair` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == (if U32.v x < U32.v y then x else y)) l
= if x `U32.lt` y
  then begin
    start parse_u32 LPI.write_u32 x;
    append parse_u32 LPI.write_u32 x
  end else begin
    start parse_u32 LPI.write_u32 x;
    append parse_u32 LPI.write_u32 y
  end

let extract_write_two_ints_ifthenelse
  (l: memory_invariant)
  (x y: U32.t)
=
  extract _ (write_two_ints_ifthenelse l x y)

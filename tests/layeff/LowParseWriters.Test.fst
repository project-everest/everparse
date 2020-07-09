module LowParseWriters.Test
open LowParseWriters.Parsers

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module LPI = LowParse.Low.Int
module HS = FStar.HyperStack

let test_read
  (inv: memory_invariant)
  ()
: HST.Stack (result bool)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read _ _ _ _ _ (fun _ -> test_read3 inv (fun () -> false) <: Read bool True (fun _ -> True) inv)

let test_read_if_1
  (inv: memory_invariant)
  ()
: HST.Stack (result bool)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read _ _ _ _ _ (fun _ -> test_read_if inv (fun () -> false) <: Read bool True (fun _ -> True) inv)

inline_for_extraction
noextract
let parse_u32
: parser
= make_parser
    LPI.parse_u32
    LPI.serialize_u32
    LPI.jump_u32

module U32 = FStar.UInt32

inline_for_extraction
noextract
let test_read_from_ptr'
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  ()
: Read FStar.UInt32.t True (fun _ -> True) inv
= deref LPI.read_u32 b

let test_read_from_ptr
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  ()
: HST.Stack (result U32.t)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read U32.t True (fun _ -> True) (fun _ -> False) inv (test_read_from_ptr' inv b)


inline_for_extraction
noextract
let test_read_if_nontrivial'
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  ()
: Read FStar.UInt32.t True (fun _ -> True) inv
= let x = deref LPI.read_u32 b in
  if x = 18ul
  then 42ul
  else 1729ul

let test_read_if_nontrivial
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  ()
: HST.Stack (result U32.t)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read U32.t True (fun _ -> True) (fun _ -> False) inv (test_read_if_nontrivial' inv b)

inline_for_extraction
noextract
let test_read_if_really_nontrivial'
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  (c: ptr parse_u32 inv)
  ()
: Read FStar.UInt32.t True (fun _ -> True) inv
= let x = deref LPI.read_u32 b in
  if x = 18ul
  then deref LPI.read_u32 c
  else 1729ul

let test_read_if_really_nontrivial
  (inv: memory_invariant)
  (b: ptr parse_u32 inv)
  (c: ptr parse_u32 inv)
  ()
: HST.Stack (result U32.t)
  (requires (fun h ->
    B.modifies B.loc_none inv.h0 h /\
    HS.get_tip inv.h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun h _ h' ->
    True
  ))
=
  reify_read U32.t True (fun _ -> True) (fun _ -> False) inv (test_read_if_really_nontrivial' inv b c)

let write_two_ints
  (l: memory_invariant)
  (x y: U32.t)
: Write unit parse_empty (parse_u32 `parse_pair` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == y) l
= start parse_u32 LPI.write_u32 x;
  append parse_u32 LPI.write_u32 y

let write_two_ints_2
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit parse_empty (parse_u32 `parse_pair` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l
= start parse_u32 LPI.write_u32 x;
  append parse_u32 LPI.write_u32 y

let write_two_ints_ifthenelse
  (l: memory_invariant)
  (x y: U32.t)
: Write unit parse_empty (parse_u32 `parse_pair` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == (if U32.v x < U32.v y then x else y)) l
= if x `U32.lt` y
  then begin
    start parse_u32 LPI.write_u32 x;
    append parse_u32 LPI.write_u32 x
  end else begin
    start parse_u32 LPI.write_u32 x;
    append parse_u32 LPI.write_u32 y
  end

let write_two_ints_ifthenelse_2_aux
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit parse_empty (parse_u32 `parse_pair` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l
= start parse_u32 LPI.write_u32 x;
  if x `U32.lt` y
  then
    append parse_u32 LPI.write_u32 x
  else
    append parse_u32 LPI.write_u32 y

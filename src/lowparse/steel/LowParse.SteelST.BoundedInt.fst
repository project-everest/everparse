module LowParse.SteelST.BoundedInt
include LowParse.Spec.BoundedInt
include LowParse.SteelST.Validate
include LowParse.SteelST.Access

module U32 = FStar.UInt32
module SZ = FStar.SizeT
module E = LowParse.SteelST.Endianness
module EI = LowParse.Spec.Endianness.Instances
module AP = LowParse.SteelST.ArrayPtr

open Steel.ST.GenElim

inline_for_extraction
noextract
let validate_bounded_integer
  (i: integer_size) // must be a constant
: Tot (validator (parse_bounded_integer i))
= [@inline_let] let _ = SZ.uint16_to_sizet (FStar.UInt16.uint_to_t i) in // proof that i fits
  validate_total_constant_size (parse_bounded_integer i) (SZ.uint_to_t i)

inline_for_extraction
let validate_bounded_integer'
  (i: U32.t { 1 <= U32.v i /\ U32.v i <= 4 })
: Tot (validator (parse_bounded_integer (U32.v i)))
= validate_total_constant_size (parse_bounded_integer (U32.v i)) (SZ.uint16_to_sizet (FStar.Int.Cast.uint32_to_uint16 i))

inline_for_extraction
noextract
let jump_bounded_integer
  (i: integer_size) // must be a constant
: Tot (jumper (parse_bounded_integer i))
= [@inline_let] let _ = SZ.uint16_to_sizet (FStar.UInt16.uint_to_t i) in // proof that i fits
  jump_constant_size (parse_bounded_integer i) (SZ.uint_to_t i)

inline_for_extraction
let jump_bounded_integer'
  (i: U32.t { 1 <= U32.v i /\ U32.v i <= 4 })
: Tot (jumper (parse_bounded_integer (U32.v i)))
= jump_constant_size (parse_bounded_integer (U32.v i)) (SZ.uint16_to_sizet (FStar.Int.Cast.uint32_to_uint16 i))

inline_for_extraction
noextract
let be_to_n_1 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint32 1)

inline_for_extraction
let read_bounded_integer_1 (_: unit)
: Tot (leaf_reader (parse_bounded_integer 1))
= fun #va a ->
  let va' = elim_aparse (parse_bounded_integer 1) a in
  parse_bounded_integer_spec 1 (AP.contents_of va');
  let res = be_to_n_1 a 1sz in
  let _ = intro_aparse (parse_bounded_integer 1) a in
  rewrite (aparse (parse_bounded_integer 1) a _) (aparse (parse_bounded_integer 1) a va);
  return res

inline_for_extraction
noextract
let be_to_n_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint32 2)

inline_for_extraction
let read_bounded_integer_2 (_: unit)
: Tot (leaf_reader (parse_bounded_integer 2))
= fun #va a ->
  let va' = elim_aparse (parse_bounded_integer 2) a in
  parse_bounded_integer_spec 2 (AP.contents_of va');
  let res = be_to_n_2 a 2sz in
  let _ = intro_aparse (parse_bounded_integer 2) a in
  rewrite (aparse (parse_bounded_integer 2) a _) (aparse (parse_bounded_integer 2) a va);
  return res

inline_for_extraction
noextract
let be_to_n_3 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint32 3)

inline_for_extraction
let read_bounded_integer_3 (_: unit)
: Tot (leaf_reader (parse_bounded_integer 3))
= fun #va a ->
  let va' = elim_aparse (parse_bounded_integer 3) a in
  parse_bounded_integer_spec 3 (AP.contents_of va');
  let res = be_to_n_3 a 3sz in
  let _ = intro_aparse (parse_bounded_integer 3) a in
  rewrite (aparse (parse_bounded_integer 3) a _) (aparse (parse_bounded_integer 3) a va);
  return res

inline_for_extraction
noextract
let be_to_n_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint32 4)

inline_for_extraction
let read_bounded_integer_4 (_: unit)
: Tot (leaf_reader (parse_bounded_integer 4))
= fun #va a ->
  let va' = elim_aparse (parse_bounded_integer 4) a in
  parse_bounded_integer_spec 4 (AP.contents_of va');
  let res = be_to_n_4 a 4sz in
  let _ = intro_aparse (parse_bounded_integer 4) a in
  rewrite (aparse (parse_bounded_integer 4) a _) (aparse (parse_bounded_integer 4) a va);
  return res

inline_for_extraction
noextract
let read_bounded_integer
  (i: integer_size)
: Tot (leaf_reader (parse_bounded_integer i))
= [@inline_let]
  let _ = integer_size_values i in
  match i returns (leaf_reader (parse_bounded_integer i)) with
  | 1 -> read_bounded_integer_1 ()
  | 2 -> read_bounded_integer_2 ()
  | 3 -> read_bounded_integer_3 ()
  | 4 -> read_bounded_integer_4 ()

inline_for_extraction
let read_bounded_integer'
  (i: U32.t { 1 <= U32.v i /\ U32.v i <= 4 })
: Tot (leaf_reader (parse_bounded_integer (U32.v i)))
= fun #va a ->
  if i = 1ul
  then begin
    let _ = rewrite_aparse a (parse_bounded_integer 1) in
    let res = read_bounded_integer_1 () a in
    let _ = rewrite_aparse a (parse_bounded_integer (U32.v i)) in
    rewrite (aparse (parse_bounded_integer (U32.v i)) a _) (aparse (parse_bounded_integer (U32.v i)) a va);
    return res
  end
  else if i = 2ul
  then begin
    let _ = rewrite_aparse a (parse_bounded_integer 2) in
    let res = read_bounded_integer_2 () a in
    let _ = rewrite_aparse a (parse_bounded_integer (U32.v i)) in
    rewrite (aparse (parse_bounded_integer (U32.v i)) a _) (aparse (parse_bounded_integer (U32.v i)) a va);
    return res
  end
  else if i = 3ul
  then begin
    let _ = rewrite_aparse a (parse_bounded_integer 3) in
    let res = read_bounded_integer_3 () a in
    let _ = rewrite_aparse a (parse_bounded_integer (U32.v i)) in
    rewrite (aparse (parse_bounded_integer (U32.v i)) a _) (aparse (parse_bounded_integer (U32.v i)) a va);
    return res
  end
  else begin
    let _ = rewrite_aparse a (parse_bounded_integer 4) in
    let res = read_bounded_integer_4 () a in
    let _ = rewrite_aparse a (parse_bounded_integer (U32.v i)) in
    rewrite (aparse (parse_bounded_integer (U32.v i)) a _) (aparse (parse_bounded_integer (U32.v i)) a va);
    return res
  end


module LowParse.SteelST.Int
include LowParse.Spec.Int
include LowParse.SteelST.Validate
include LowParse.SteelST.Access
include LowParse.SteelST.Write
open Steel.ST.GenElim

module E = LowParse.SteelST.Endianness
module EI = LowParse.Spec.Endianness.Instances
module SZ = FStar.SizeT
module AP = LowParse.SteelST.ArrayPtr

inline_for_extraction
let validate_u8 : validator parse_u8 =
  validate_total_constant_size parse_u8 1sz

inline_for_extraction
let jump_u8 : jumper parse_u8 =
  jump_constant_size parse_u8 1sz

inline_for_extraction
noextract
let be_to_n_1 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint8 1)

inline_for_extraction
let read_u8 : leaf_reader parse_u8 =
  fun #va a ->
  let va' = elim_aparse parse_u8 a in
  parse_u8_spec (AP.contents_of va');
  let res = be_to_n_1 a 1sz in
  let _ = intro_aparse parse_u8 a in
  rewrite (aparse parse_u8 a _) (aparse parse_u8 a va);
  return res

inline_for_extraction
noextract
let n_to_be_1 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be EI.uint8 1)

inline_for_extraction
let write_u8 : exact_writer serialize_u8 =
  fun x a ->
    let va1 = n_to_be_1 x a 1sz in
    parser_kind_prop_equiv parse_u8_kind parse_u8;
    parse_u8_spec (AP.contents_of' va1);
    let va2 = intro_aparse parse_u8 a in
    return va2

inline_for_extraction
let validate_u16 : validator parse_u16 =
  validate_total_constant_size parse_u16 2sz

inline_for_extraction
let jump_u16 : jumper parse_u16 =
  jump_constant_size parse_u16 2sz

inline_for_extraction
noextract
let be_to_n_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint16 2)

inline_for_extraction
let read_u16 : leaf_reader parse_u16 =
  fun #va a ->
  let va' = elim_aparse parse_u16 a in
  parse_u16_spec (AP.contents_of va');
  let res = be_to_n_2 a 2sz in
  let _ = intro_aparse parse_u16 a in
  rewrite (aparse parse_u16 a _) (aparse parse_u16 a va);
  return res

inline_for_extraction
noextract
let n_to_be_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be EI.uint16 2)

inline_for_extraction
let write_u16 : exact_writer serialize_u16 =
  fun x a ->
    let va1 = n_to_be_2 x a 2sz in
    parser_kind_prop_equiv parse_u16_kind parse_u16;
    parse_u16_spec (AP.contents_of' va1);
    let va2 = intro_aparse parse_u16 a in
    return va2

inline_for_extraction
let validate_u32 : validator parse_u32 =
  validate_total_constant_size parse_u32 4sz

inline_for_extraction
let jump_u32 : jumper parse_u32 =
  jump_constant_size parse_u32 4sz

inline_for_extraction
noextract
let be_to_n_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint32 4)

inline_for_extraction
let read_u32 : leaf_reader parse_u32 =
  fun #va a ->
  let va' = elim_aparse parse_u32 a in
  parse_u32_spec (AP.contents_of va');
  let res = be_to_n_4 a 4sz in
  let _ = intro_aparse parse_u32 a in
  rewrite (aparse parse_u32 a _) (aparse parse_u32 a va);
  return res

inline_for_extraction
noextract
let n_to_be_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be EI.uint32 4)

inline_for_extraction
let write_u32 : exact_writer serialize_u32 =
  fun x a ->
    let va1 = n_to_be_4 x a 4sz in
    parser_kind_prop_equiv parse_u32_kind parse_u32;
    parse_u32_spec (AP.contents_of' va1);
    let va2 = intro_aparse parse_u32 a in
    return va2

inline_for_extraction
let validate_u64 : validator parse_u64 =
  validate_total_constant_size parse_u64 8sz

inline_for_extraction
let jump_u64 : jumper parse_u64 =
  jump_constant_size parse_u64 8sz

inline_for_extraction
noextract
let be_to_n_8 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint64 8)

inline_for_extraction
let read_u64 : leaf_reader parse_u64 =
  fun #va a ->
  let va' = elim_aparse parse_u64 a in
  parse_u64_spec (AP.contents_of va');
  let res = be_to_n_8 a 8sz in
  let _ = intro_aparse parse_u64 a in
  rewrite (aparse parse_u64 a _) (aparse parse_u64 a va);
  return res

inline_for_extraction
noextract
let n_to_be_8 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be EI.uint64 8)

inline_for_extraction
let write_u64 : exact_writer serialize_u64 =
  fun x a ->
    let va1 = n_to_be_8 x a 8sz in
    parser_kind_prop_equiv parse_u64_kind parse_u64;
    parse_u64_spec (AP.contents_of' va1);
    let va2 = intro_aparse parse_u64 a in
    return va2

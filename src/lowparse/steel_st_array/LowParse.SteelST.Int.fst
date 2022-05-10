module LowParse.SteelST.Int
include LowParse.Spec.Int
include LowParse.SteelST.Validate
include LowParse.SteelST.Access
open Steel.ST.Util

module E = LowParse.SteelST.Endianness
module EI = LowParse.Spec.Endianness.Instances
module SZ = LowParse.Steel.StdInt
module AP = LowParse.SteelST.ArrayPtr

inline_for_extraction
let validate_u8 : validator parse_u8 =
  validate_total_constant_size parse_u8 (SZ.mk_size_t 1ul)

inline_for_extraction
let jump_u8 : jumper parse_u8 =
  jump_constant_size parse_u8 (SZ.mk_size_t 1ul)

inline_for_extraction
noextract
let be_to_n_1 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint8 1)

inline_for_extraction
let read_u8 : leaf_reader parse_u8 =
  fun #va a ->
  let va' = elim_aparse parse_u8 a in
  parse_u8_spec (AP.contents_of va');
  let res = be_to_n_1 a SZ.one_size in
  let _ = intro_aparse parse_u8 a in
  rewrite (aparse parse_u8 a _) (aparse parse_u8 a va);
  return res

inline_for_extraction
let validate_u16 : validator parse_u16 =
  validate_total_constant_size parse_u16 (SZ.mk_size_t 2ul)

inline_for_extraction
let jump_u16 : jumper parse_u16 =
  jump_constant_size parse_u16 (SZ.mk_size_t 2ul)

inline_for_extraction
noextract
let be_to_n_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint16 2)

inline_for_extraction
let read_u16 : leaf_reader parse_u16 =
  fun #va a ->
  let va' = elim_aparse parse_u16 a in
  parse_u16_spec (AP.contents_of va');
  let res = be_to_n_2 a (SZ.mk_size_t 2ul) in
  let _ = intro_aparse parse_u16 a in
  rewrite (aparse parse_u16 a _) (aparse parse_u16 a va);
  return res

inline_for_extraction
let validate_u32 : validator parse_u32 =
  validate_total_constant_size parse_u32 (SZ.mk_size_t 4ul)

inline_for_extraction
let jump_u32 : jumper parse_u32 =
  jump_constant_size parse_u32 (SZ.mk_size_t 4ul)

inline_for_extraction
noextract
let be_to_n_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint32 4)

inline_for_extraction
let read_u32 : leaf_reader parse_u32 =
  fun #va a ->
  let va' = elim_aparse parse_u32 a in
  parse_u32_spec (AP.contents_of va');
  let res = be_to_n_4 a (SZ.mk_size_t 4ul) in
  let _ = intro_aparse parse_u32 a in
  rewrite (aparse parse_u32 a _) (aparse parse_u32 a va);
  return res

inline_for_extraction
let validate_u64 : validator parse_u64 =
  validate_total_constant_size parse_u64 (SZ.mk_size_t 8ul)

inline_for_extraction
let jump_u64 : jumper parse_u64 =
  jump_constant_size parse_u64 (SZ.mk_size_t 8ul)

inline_for_extraction
noextract
let be_to_n_8 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint64 8)

inline_for_extraction
let read_u64 : leaf_reader parse_u64 =
  fun #va a ->
  let va' = elim_aparse parse_u64 a in
  parse_u64_spec (AP.contents_of va');
  let res = be_to_n_8 a (SZ.mk_size_t 8ul) in
  let _ = intro_aparse parse_u64 a in
  rewrite (aparse parse_u64 a _) (aparse parse_u64 a va);
  return res

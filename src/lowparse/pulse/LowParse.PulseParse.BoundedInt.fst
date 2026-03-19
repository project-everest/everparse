module LowParse.PulseParse.BoundedInt
#lang-pulse
include LowParse.Spec.BoundedInt
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module R = Pulse.Lib.Reference

(* Simple constant-size validators *)

inline_for_extraction noextract
let validate_bounded_integer (i: integer_size)
: Tot (LPS.validator (parse_bounded_integer i))
= LPS.validate_total_constant_size (parse_bounded_integer i) (SZ.uint_to_t i)

inline_for_extraction
let validate_bounded_integer' (i: U32.t { 1 <= U32.v i /\ U32.v i <= 4 })
  (_: squash (FStar.SizeT.fits_u64))
: Tot (LPS.validator (parse_bounded_integer (U32.v i)))
= FStar.SizeT.fits_u64_implies_fits_32 ();
  LPS.validate_total_constant_size (parse_bounded_integer (U32.v i)) (FStar.SizeT.uint32_to_sizet i)

inline_for_extraction noextract
let validate_bounded_integer_le (i: integer_size)
: Tot (LPS.validator (parse_bounded_integer_le i))
= LPS.validate_total_constant_size (parse_bounded_integer_le i) (SZ.uint_to_t i)

inline_for_extraction
let validate_u16_le
: LPS.validator parse_u16_le
= LPS.validate_total_constant_size parse_u16_le 2sz

inline_for_extraction
let validate_u32_le
: LPS.validator parse_u32_le
= LPS.validate_total_constant_size parse_u32_le 4sz

(* Bounded int32 validators require equational lemmas that relate
   parse_bounded_int32 to parse_bounded_integer + filter.
   The Spec module does not expose these equations, and the definitions
   are opaque due to caching (--already_cached). These validators
   would need parse_bounded_int32_eq to be added to the Spec.BoundedInt
   interface. *)

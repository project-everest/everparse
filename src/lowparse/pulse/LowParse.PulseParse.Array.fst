module LowParse.PulseParse.Array
#lang-pulse
include LowParse.Spec.Array
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPC = LowParse.PulseParse.Combinators
module LPC = LowParse.Pulse.Combinators
module PPCF = LowParse.PulseParse.FLData
module LPC = LowParse.Pulse.Combinators
module PPCL = LowParse.PulseParse.List
module LPC = LowParse.Pulse.Combinators
module PPCV = LowParse.PulseParse.VLData
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base

inline_for_extraction
let validate_array'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (array_byte_size: nat)
  (array_byte_size_sz: SZ.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond k array_byte_size elem_count == true /\
    SZ.v array_byte_size_sz == array_byte_size
  })
: LPS.validator (parse_array' s array_byte_size elem_count)
= fldata_to_array_inj s array_byte_size elem_count ();
  LPC.validate_synth
    (PPCF.validate_fldata_strong (serialize_list _ s) (PPCL.validate_list v ()) array_byte_size_sz)
    (fldata_to_array s array_byte_size elem_count ())

inline_for_extraction
let validate_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (array_byte_size: nat)
  (array_byte_size_sz: SZ.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond k array_byte_size elem_count == true /\
    SZ.v array_byte_size_sz == array_byte_size
  })
: LPS.validator (parse_array s array_byte_size elem_count)
= if k.parser_kind_metadata = Some ParserKindMetadataTotal
  then LPS.validate_total_constant_size (parse_array s array_byte_size elem_count) array_byte_size_sz
  else LPS.validate_ext (validate_array' s v array_byte_size array_byte_size_sz elem_count u) (parse_array s array_byte_size elem_count)

inline_for_extraction
let validate_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' array_byte_size_max)))
  (_: squash (FStar.SizeT.fits_u64 /\ array_byte_size_max < 4294967296))
: LPS.validator (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  LPC.validate_synth
    (PPCV.validate_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s) (PPCL.validate_list v ()) lr ())
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())


inline_for_extraction
let jump_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (array_byte_size_sz: SZ.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond k array_byte_size elem_count == true /\
    SZ.v array_byte_size_sz == array_byte_size
  })
: LPS.jumper (parse_array s array_byte_size elem_count)
= LPS.jump_constant_size (parse_array s array_byte_size elem_count) array_byte_size_sz

inline_for_extraction
let jump_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (lr: LPS.leaf_reader (serialize_bounded_integer (log256' array_byte_size_max)))
  (_: squash (FStar.SizeT.fits_u64 /\ array_byte_size_max < 4294967296))
: LPS.jumper (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  LPC.jump_synth
    (PPCV.jump_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s) lr ())
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())

module LowParseExampleDepLen
#lang-pulse
(* Ported from dependent length test.
   Original used parse_deplen with bounded_int32 headers.
   We keep spec parts (type definitions, parser, serializer).
   NOTE: Pulse validator for deplen requires leaf_reader for
   serialize_nondep_then, which needs bounded_int32 readers not yet available. *)

include LowParse.Spec.DepLen
include LowParse.Spec.Bytes
include LowParse.Spec.Int
include LowParse.Spec.Combinators
include LowParse.Spec.BoundedInt
open Pulse.Lib.Pervasives
open LowParse.Spec.Base

module B32 = FStar.Bytes
module U32 = FStar.UInt32
module I32 = FStar.Int32

(* data type definition *)

let unit_test_header_type = ((bounded_int32 0 100) & (bounded_int32 0 100))

let unit_test_payload_type = B32.bytes

let unit_test_payload_serializer = serialize_all_bytes

noextract
let unit_test_min = 0

noextract
let unit_test_max = 4200000000

(* dependent length function *)

let unit_test_deplen_func
  (h : unit_test_header_type)
: Tot (bounded_int32 0 100)
= fst h

let unit_test_data_type = unit_test_header_type & unit_test_payload_type

let unit_test_data_type_strong = parse_deplen_data_t unit_test_min unit_test_max unit_test_deplen_func unit_test_payload_serializer

type unit_test_struct_type = 
  | MkUnit_test_struct_type : len: bounded_int32 0 100 -> foo: bounded_int32 0 100 -> payload: B32.bytes {U32.v (unit_test_deplen_func (len, foo)) == Seq.length (unit_test_payload_serializer payload)} -> unit_test_struct_type

let unit_test_synth_struct
  (x: unit_test_data_type_strong)
: Tot (unit_test_struct_type)
= MkUnit_test_struct_type (fst (fst x)) (snd (fst x)) (snd x)

(* parser specification *)

let unit_test_header_parser = nondep_then (parse_bounded_int32 0 100) (parse_bounded_int32 0 100)

let unit_test_data_parser = parse_deplen unit_test_min unit_test_max unit_test_header_parser unit_test_deplen_func unit_test_payload_serializer

let unit_test_struct_parser = unit_test_data_parser `parse_synth` unit_test_synth_struct

(* parser lemmas *)

let unit_test_struct_parser_unfold
  (input : bytes)
: Lemma
  (parse unit_test_struct_parser input == (
    let res = parse unit_test_data_parser input in
      match res with
      | None -> None
      | Some (x, consumed) -> Some (MkUnit_test_struct_type (fst (fst x)) (snd (fst x)) (snd x), consumed)
      )
  )
= parse_synth_eq
    unit_test_data_parser
    unit_test_synth_struct
    input

let unit_test_lemma1_aux1
  (input : bytes)
: Lemma
  (parse unit_test_header_parser input == (
   let res_len = parse (parse_bounded_int32 0 100) input in
     match res_len with
     | None -> None
     | Some (len, consumed) ->
       let input' = Seq.slice input consumed (Seq.length input) in
       let res_foo = parse (parse_bounded_int32 0 100) input' in
       match res_foo with
       | None -> None
       | Some (foo, consumed') -> Some ((len, foo), consumed + consumed'))
  )
= nondep_then_eq (parse_bounded_int32 0 100) (parse_bounded_int32 0 100) input

#push-options "--z3rlimit 16"

let unit_test_lemma1
  (input : bytes)
: Lemma 
  (parse unit_test_struct_parser input ==
   (let res_len = parse (parse_bounded_int32 0 100) input in
      match res_len with
      | None -> None
      | Some (len, consumed) ->
        let input' = Seq.slice input consumed (Seq.length input) in
        let res_foo = parse (parse_bounded_int32 0 100) input' in
        match res_foo with
        | None -> None
        | Some (foo, consumed') ->
          let sz = U32.v (unit_test_deplen_func (len, foo)) in
          if (sz + (consumed' + consumed) > Seq.length input) then
            None
          else
            let input'' = Seq.slice input (consumed + consumed') (consumed + consumed' + sz) in
            let res_payload = parse parse_all_bytes input'' in
            match res_payload with
            | None -> None
            | Some (payload, consumed'') -> 
              if consumed'' = sz && Seq.length (serialize serialize_all_bytes payload) = consumed'' then
                Some (MkUnit_test_struct_type len foo payload, consumed + consumed' + consumed'')
              else
                None)
  )
= unit_test_struct_parser_unfold input;
  parse_deplen_unfold2 unit_test_min unit_test_max unit_test_header_parser unit_test_deplen_func unit_test_payload_serializer input;
  unit_test_lemma1_aux1 input;
  let res_len = parse (parse_bounded_int32 0 100) input in
  match res_len with
  | None -> ()
  | Some (len, consumed) ->
    let input' = Seq.slice input consumed (Seq.length input) in
    let res_foo = parse (parse_bounded_int32 0 100) input' in
    match res_foo with
    | None -> ()
    | Some (foo, consumed') ->
      let sz = U32.v (unit_test_deplen_func (len, foo)) in
      if (sz + (consumed + consumed') > Seq.length input) then
        ()
      else
        let input'' = Seq.slice input (consumed + consumed') (Seq.length input) in
        parse_deplen_payload_unfold unit_test_min unit_test_max unit_test_deplen_func unit_test_payload_serializer (len, foo) input'';
        ()

#pop-options

(* serializer specification *)

let unit_test_header_serializer = serialize_nondep_then (serialize_bounded_int32 0 100) (serialize_bounded_int32 0 100)

let unit_test_data_serializer : serializer unit_test_data_parser = serialize_deplen unit_test_min unit_test_max unit_test_header_serializer unit_test_deplen_func unit_test_payload_serializer

let unit_test_synth_struct_recip
  (x: unit_test_struct_type)
: Tot (unit_test_data_type_strong)
= ((x.len, x.foo), x.payload) 

let unit_test_struct_serializer : serializer unit_test_struct_parser = 
  serialize_synth
    unit_test_data_parser
    unit_test_synth_struct
    unit_test_data_serializer
    unit_test_synth_struct_recip
    ()

(* Pulse validators, jumper, and deplen_func_calc *)

open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module LPI = LowParse.Pulse.Int
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module PPBI = LowParse.PulseParse.BoundedInt
module PPBY = LowParse.PulseParse.Bytes
module PPDL = LowParse.PulseParse.DepLen
module Trade = Pulse.Lib.Trade.Util
module Cast = FStar.Int.Cast

let fits_u64_squash (_: unit) : Lemma (FStar.SizeT.fits_u64) = assume (FStar.SizeT.fits_u64)

inline_for_extraction noextract
let leaf_read_bi1 : PPB.leaf_reader (parse_bounded_integer 1) =
  fits_u64_squash ();
  PPBI.leaf_read_bounded_integer_1 ()

(* leaf_reader for parse_bounded_int32: read via parse_bounded_integer + bounds check.
   The value is the same U32.t, just refined. *)
#push-options "--z3rlimit 32"

inline_for_extraction
fn leaf_read_bounded_int32_0_100
  (input: S.slice byte) (#pm: perm) (#v: Ghost.erased (bounded_int32 0 100))
  requires PPB.pts_to_parsed (parse_bounded_int32 0 100) input #pm v
  returns res: bounded_int32 0 100
  ensures PPB.pts_to_parsed (parse_bounded_int32 0 100) input #pm v ** pure (res == Ghost.reveal v)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_bounded_int32_eq 0 100 w;
  parser_kind_prop_equiv (parse_bounded_integer_kind 1) (parse_bounded_integer 1);
  S.pts_to_len input;
  let b0 = input.(0sz);
  FStar.Endianness.reveal_be_to_n (Seq.slice w 0 1);
  FStar.Endianness.reveal_be_to_n (Seq.slice (Seq.slice w 0 1) 0 0);
  Seq.lemma_index_slice w 0 1 0;
  parse_bounded_integer_spec 1 w;
  let res = Cast.uint8_to_uint32 b0;
  (* Restore: pts_to input #pm w → pts_to_parsed parse_bounded_int32 *)
  Trade.elim (S.pts_to input #pm w) (PPB.pts_to_parsed (parse_bounded_int32 0 100) input #pm v);
  res
}
#pop-options

inline_for_extraction noextract
let leaf_read_bi2 : PPB.leaf_reader (parse_bounded_integer 2) =
  fits_u64_squash ();
  PPBI.leaf_read_bounded_integer_2 ()

inline_for_extraction noextract
let leaf_read_bi3 : PPB.leaf_reader (parse_bounded_integer 3) =
  fits_u64_squash ();
  PPBI.leaf_read_bounded_integer_3 ()

inline_for_extraction noextract
let leaf_read_bi4 : PPB.leaf_reader (parse_bounded_integer 4) =
  fits_u64_squash ();
  PPBI.leaf_read_bounded_integer_4 ()

inline_for_extraction
let unit_test_header_validator : LPS.validator unit_test_header_parser =
  PPC.validate_nondep_then
    (PPBI.validate_bounded_int32 0ul 100ul leaf_read_bi1 leaf_read_bi2 leaf_read_bi3 leaf_read_bi4)
    (PPBI.validate_bounded_int32 0ul 100ul leaf_read_bi1 leaf_read_bi2 leaf_read_bi3 leaf_read_bi4)

inline_for_extraction noextract
let jump_bi32 : LPS.jumper (parse_bounded_int32 0 100) =
  PPBI.jump_bounded_int32_1 0ul 100ul

inline_for_extraction noextract
let leaf_read_header : PPB.leaf_reader unit_test_header_parser =
  PPC.leaf_read_nondep_then
    leaf_read_bounded_int32_0_100
    jump_bi32
    leaf_read_bounded_int32_0_100
    ()

inline_for_extraction
let unit_test_data_validator : LPS.validator unit_test_data_parser =
  fits_u64_squash ();
  PPDL.validate_deplen unit_test_min unit_test_max
    unit_test_header_validator
    leaf_read_header
    unit_test_deplen_func
    unit_test_payload_serializer
    (PPBY.validate_all_bytes ())
    ()

inline_for_extraction
let unit_test_struct_validator : LPS.validator unit_test_struct_parser =
  LPC.validate_synth unit_test_data_validator unit_test_synth_struct

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }

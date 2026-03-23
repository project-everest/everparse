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

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }

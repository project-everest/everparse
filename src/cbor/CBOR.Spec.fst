module CBOR.Spec
open LowParse.Spec
open LowParse.Spec.BitSum
open LowParse.Spec.Fuel
open LowParse.Spec.SeqBytes

(* RFC 8949

   NOTE: we are only supporting Deterministically Encoded CBOR (Section 4.2),
   which is a requirement of COSE anyway (RFC 8152, Section 14)
*)

(* Section 3: initial byte *)

[@filter_bitsum'_t_attr]
let initial_byte_desc : bitsum' uint8 8 =
  BitField 3 (BitField 5 (BitStop ()))

inline_for_extraction
let destr_initial_byte : destr_bitsum'_t initial_byte_desc =
  norm [delta_attr [`%filter_bitsum'_t_attr]; iota; zeta; primops]
    (mk_destr_bitsum'_t initial_byte_desc)

module U8 = FStar.UInt8

inline_for_extraction
let initial_byte_wf (b: bitsum'_type initial_byte_desc) : Tot bool =
  match b with
  | (major_type, (additional_info, _)) ->
    (if major_type = 7uy then additional_info `U8.lt` 25uy else true) && // TODO: support floating-point numbers
    additional_info `U8.lt` 28uy
    // we disallow value 31 because we do not support indefinite lengths (section 4.2.1)

inline_for_extraction
let mk_initial_byte_wf
  (x: U8.t)
: Pure bool
  (requires True)
  (ensures (fun y -> y == initial_byte_wf (synth_bitsum' initial_byte_desc x)))
= destr_initial_byte
    (fun b -> (y: bool { y == initial_byte_wf b }))
    (fun _ cond sv_true sv_false -> if cond then sv_true () else sv_false ())
    (fun b -> initial_byte_wf b)
    x

let initial_byte = parse_filter_refine initial_byte_wf

module SZ = FStar.SizeT

inline_for_extraction
let argument_size
  (b: initial_byte)
: Tot SZ.t
= match b with
  | (major_type, (additional_info, _)) ->
    if additional_info = 24uy
    then 1sz
    else if additional_info = 25uy
    then 2sz
    else if additional_info = 26uy
    then 3sz
    else if additional_info = 27uy
    then 4sz
    else 0sz

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

inline_for_extraction
let uint8_wf
  (x: U8.t)
: Tot bool
= 24uy `U8.lte` x

inline_for_extraction
let uint16_wf
  (x: U16.t)
: Tot bool
= 256us `U16.lte` x

inline_for_extraction
let uint32_wf
  (x: U32.t)
: Tot bool
= 65536ul `U32.lte` x

inline_for_extraction
let uint64_wf
  (x: U64.t)
: Tot bool
= 4294967296uL `U64.lte` x

let simple_value_long_argument_wf // 3.3: "an encoder MUST NOT issue two-byte sequences that start with 0xf8 and continue with a byte less than 0x20"
  (x: U8.t)
: Tot bool
= 32uy `U8.lte` x

let long_argument
  (b: initial_byte)
: Tot Type
= match b with
  | (major_type, (additional_info, _)) ->
    if additional_info = 24uy
    then
      if major_type = 7uy
      then parse_filter_refine simple_value_long_argument_wf
      else parse_filter_refine uint8_wf
    else if additional_info = 25uy
    then parse_filter_refine uint16_wf
    else if additional_info = 26uy
    then parse_filter_refine uint32_wf
    else if additional_info = 27uy
    then parse_filter_refine uint64_wf
    else unit

noextract
let header = dtuple2 initial_byte long_argument

module Cast = FStar.Int.Cast

let argument_as_uint64
  (b: initial_byte)
  (x: long_argument b)
: Tot U64.t
= match b with
  | (major_type, (additional_info, _)) ->
    if additional_info `U8.lt` 24uy
    then Cast.uint8_to_uint64 additional_info
    else if additional_info = 24uy
    then Cast.uint8_to_uint64 x
    else if additional_info = 25uy
    then Cast.uint16_to_uint64 x
    else if additional_info = 26uy
    then Cast.uint32_to_uint64 x
    else begin
      assert (additional_info = 27uy);
      x
    end

let simple_value_wf
  (x: U8.t)
: Tot bool
= x `U8.lt` 24uy || 32uy `U8.lte` x

let simple_value = parse_filter_refine simple_value_wf

let argument_as_simple_value
  (b: initial_byte)
  (x: long_argument b)
: Pure simple_value
    (requires (let (major_type, (additional_info, _)) = b in major_type = 7uy /\ additional_info `U8.lte` 24uy))
    (ensures (fun _ -> True))
= match b with
  | (major_type, (additional_info, _)) ->
    if additional_info `U8.lt` 24uy
    then additional_info
    else x

(* Raw data items, disregarding ordering of map entries *)

noeq
type raw_data_item
= | Simple: (v: simple_value) -> raw_data_item
  | UInt64: (v: U64.t) -> raw_data_item
  | NegInt64: (minus_one_minus_v: U64.t) -> raw_data_item
  | ByteString: (v: Seq.seq byte) -> raw_data_item
  | TextString: (v: Seq.seq byte) -> raw_data_item // Setion 3.1: "a string containing an invalid UTF-8 sequence is well-formed but invalid", so we don't care about UTF-8 specifics here.
  | Array: (v: list raw_data_item) -> raw_data_item
  | Map: (v: list (raw_data_item & raw_data_item)) -> raw_data_item
  | Tagged: (tag: U64.t) -> (v: raw_data_item) -> raw_data_item
//  | Float: (v: Float.float) -> raw_data_item // TODO

let content
  (h: header)
: Tot Type
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = 2uy || major_type = 3uy
      then Seq.lseq byte (U64.v (argument_as_uint64 b long_arg))
      else if major_type = 4uy
      then nlist (U64.v (argument_as_uint64 b long_arg)) raw_data_item
      else if major_type = 5uy
      then nlist (U64.v (argument_as_uint64 b long_arg)) (raw_data_item & raw_data_item)
      else if major_type = 6uy
      then raw_data_item
      else unit

let raw_data_item' = dtuple2 header content

let synth_raw_data_item'
  (h: header)
  (c: content h)
: Tot raw_data_item
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = 0uy
      then UInt64 (argument_as_uint64 b long_arg)
      else if major_type = 1uy
      then NegInt64 (argument_as_uint64 b long_arg)
      else if major_type = 2uy
      then ByteString c
      else if major_type = 3uy
      then TextString c
      else if major_type = 4uy
      then Array c
      else if major_type = 5uy
      then Map c
      else if major_type = 6uy
      then Tagged (argument_as_uint64 b long_arg) c
      else
        // TODO: support floats
        Simple (argument_as_simple_value b long_arg)

let synth_raw_data_item
  (x: raw_data_item')
: Tot raw_data_item
= match x with
  | (| h, c |) ->
    synth_raw_data_item' h c

#push-options "--z3rlimit 16"
#restart-solver
let synth_raw_data_item_injective : squash (synth_injective synth_raw_data_item) = ()
#pop-options

let parse_initial_byte : parser _ initial_byte =
  parse_filter (parse_bitsum' initial_byte_desc parse_u8) initial_byte_wf

let parse_long_argument
  (b: initial_byte)
: Tot (parser (strong_parser_kind 0 8 None) (long_argument b))
= match b with
  | (major_type, (additional_info, _)) ->
    if additional_info = 24uy
    then
      if major_type = 7uy
      then weaken _ (parse_filter parse_u8 simple_value_long_argument_wf)
      else weaken _ (parse_filter parse_u8 uint8_wf)
    else if additional_info = 25uy
    then weaken _ (parse_filter parse_u16 uint16_wf)
    else if additional_info = 26uy
    then weaken _ (parse_filter parse_u32 uint32_wf)
    else if additional_info = 27uy
    then weaken _ (parse_filter parse_u64 uint64_wf)
    else weaken _ parse_empty

let parse_header : parser _ header =
  parse_dtuple2 parse_initial_byte parse_long_argument

inline_for_extraction
let parse_content_kind : parser_kind = {
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

inline_for_extraction
let parse_raw_data_item_kind : parser_kind = {
  parser_kind_low = 1;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let parse_content
  (p: parser parse_raw_data_item_kind raw_data_item)
  (h: header) : parser parse_content_kind (content h)
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = 2uy || major_type = 3uy
      then weaken _ (parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg)))
      else if major_type = 4uy
      then weaken _ (parse_nlist (U64.v (argument_as_uint64 b long_arg)) p)
      else if major_type = 5uy
      then weaken _ (parse_nlist (U64.v (argument_as_uint64 b long_arg)) (p `nondep_then` p))
      else if major_type = 6uy
      then weaken _ p
      else weaken _ parse_empty

let parse_raw_data_item_aux
  (p: parser parse_raw_data_item_kind raw_data_item)
: Tot (parser parse_raw_data_item_kind raw_data_item)
= parse_dtuple2 parse_header (parse_content p) `parse_synth` synth_raw_data_item

let rec parse_raw_data_item_fuel
  (fuel: nat)
: Tot (parser parse_raw_data_item_kind raw_data_item)
= if fuel = 0
  then fail_parser _ _
  else parse_raw_data_item_aux (parse_raw_data_item_fuel (fuel - 1))

let parse_content_fuel_ext
  (fuel: nat)
  (fuel': nat { fuel <= fuel' })
  (prf: (
    (b: bytes { Seq.length b < fuel }) ->
    Lemma
    (parse (parse_raw_data_item_fuel fuel) b == parse (parse_raw_data_item_fuel fuel') b)
  ))
  (h: header)
  (input: bytes { Seq.length input < fuel })
: Lemma
  (parse (parse_content (parse_raw_data_item_fuel fuel) h) input == parse (parse_content (parse_raw_data_item_fuel fuel') h) input)
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = 4uy
      then
        parse_nlist_fuel_ext (U64.v (argument_as_uint64 b long_arg)) parse_raw_data_item_fuel fuel fuel' prf input
      else if major_type = 5uy
      then
        parse_nlist_fuel_ext (U64.v (argument_as_uint64 b long_arg)) (fun fuel -> parse_raw_data_item_fuel fuel `nondep_then` parse_raw_data_item_fuel fuel) fuel fuel'
          (fun input ->
            nondep_then_ext_l (parse_raw_data_item_fuel fuel) (parse_raw_data_item_fuel fuel') (parse_raw_data_item_fuel fuel) input (prf input);
            nondep_then_fuel_ext_r (parse_raw_data_item_fuel fuel') parse_raw_data_item_fuel fuel fuel' prf input
          )
          input
      else if major_type = 6uy
      then prf input
      else ()

let rec parse_raw_data_item_fuel_ext_gen
  (fuel: nat)
  (fuel': nat { fuel <= fuel' })
  (input: bytes { Seq.length input < fuel })
: Lemma
  (ensures (parse (parse_raw_data_item_fuel fuel) input == parse (parse_raw_data_item_fuel fuel') input))
  (decreases fuel)
= parse_synth_ext
    (parse_dtuple2 parse_header (parse_content (parse_raw_data_item_fuel (fuel - 1))))
    (parse_dtuple2 parse_header (parse_content (parse_raw_data_item_fuel (fuel' - 1))))
    synth_raw_data_item
    input
    (
      parse_dtuple2_fuel_ext_r_consumes_l
        parse_header
        (fun fuel -> parse_content (parse_raw_data_item_fuel fuel))
        (fuel - 1)
        (fuel' - 1)
        (parse_content_fuel_ext (fuel - 1) (fuel' - 1) (parse_raw_data_item_fuel_ext_gen (fuel - 1) (fuel' - 1)))
        input
    )

let closure
  (b: bytes)
: Tot (n: nat { Seq.length b < n })
= Seq.length b + 1

let parse_raw_data_item_fuel_ext
  (fuel: nat)
  (input: bytes { Seq.length input < fuel })
: Lemma
  (ensures (parse (parse_raw_data_item_fuel fuel) input == parse (parse_raw_data_item_fuel (closure input)) input))
= parse_raw_data_item_fuel_ext_gen (closure input) fuel input

let parse_raw_data_item : parser parse_raw_data_item_kind raw_data_item =
  close_by_fuel parse_raw_data_item_fuel closure parse_raw_data_item_fuel_ext

(*
// Ordering of map keys (Section 4.2)

let rec forall_list
  (#t: Type)
  (l: list t)
  (p: (x: t { x << l }) -> bool)
: Tot bool
= match l with
  | [] -> true
  | a :: q -> p a && forall_list q p

let rec forall_list_fst
  (#t1 #t2: Type)
  (l: list (t1 & t2))
  (p: (x: t1 { x << l }) -> bool)
: Tot bool
= match l with
  | [] -> true
  | (a, _) :: q -> p a && forall_list_fst q p

let rec forall_list_snd
  (#t1 #t2: Type)
  (l: list (t1 & t2))
  (p: (x: t2 { x << l }) -> bool)
: Tot bool
= match l with
  | [] -> true
  | (_, a) :: q -> p a && forall_list_snd q p

let rec data_item_wf (order: (raw_data_item -> raw_data_item -> bool)) (x: raw_data_item) : Tot bool
= match x with
  | Array l -> forall_list l (data_item_wf order)
  | Map l -> forall_list_fst l (data_item_wf order) && forall_list_snd l (data_item_wf order) &&
      FStar.List.Tot.sorted order (FStar.List.Tot.map fst l)
  | Tagged _ v -> data_item_wf order v
  | _ -> true

let data_item (order: (raw_data_item -> raw_data_item -> bool)) = (d: raw_data_item { data_item_wf order d })

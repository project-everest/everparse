module CBOR.Spec.Raw.EverParse
include CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.Valid
open LowParse.Spec
open LowParse.Spec.BitSum
open LowParse.Spec.Recursive
open LowParse.Spec.SeqBytes
open CBOR.Spec.Raw.EverParse.Assoc
open CBOR.Spec.Util

(* RFC 8949

   NOTE: we are only supporting definite-length encoding of objects
   without floating-point values, but we do support integers encoded
   in any length (not necessarily the shortest length.)
   
*)

(* Section 3: initial byte *)

[@filter_bitsum'_t_attr]
let initial_byte_desc : bitsum' uint8 8 =
  BitField 3 (BitField 5 (BitStop ()))

inline_for_extraction
let filter_initial_byte : filter_bitsum'_t initial_byte_desc =
  norm [delta_attr [`%filter_bitsum'_t_attr]; iota; zeta; primops]
    (mk_filter_bitsum'_t' initial_byte_desc)

inline_for_extraction
[@@ FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%filter_bitsum'_t_attr];
  delta_only [`%destr_bitsum'_bitstop; `%destr_bitsum'_bitfield];
iota; zeta; primops]; FStar.Tactics.trefl ())]
let destr_initial_byte : destr_bitsum'_t initial_byte_desc =
//  norm [delta_attr [`%filter_bitsum'_t_attr]; iota; zeta; primops]
    (mk_destr_bitsum'_t initial_byte_desc)

inline_for_extraction
let _cut_eq
  (#t: Type)
  (x y: t)
  (sq: squash (x == y))
: Tot t
= y

inline_for_extraction
let mk_synth_initial_byte : synth_bitsum'_recip_t initial_byte_desc =
  _ by (
    FStar.Tactics.apply (`(_cut_eq (mk_synth_bitsum'_recip initial_byte_desc)));
    FStar.Tactics.norm [delta_attr [`%filter_bitsum'_t_attr]; iota; zeta; primops];
    FStar.Tactics.trefl ()
  )

(* // FIXME: WHY WHY WHY does the following not fully normalize? Probably some interaction between `norm` and `inline_for_extraction`
inline_for_extraction
let mk_synth_initial_byte : synth_bitsum'_recip_t initial_byte_desc =
  norm [delta_attr [`%filter_bitsum'_t_attr]; iota; zeta; primops]
    (mk_synth_bitsum'_recip initial_byte_desc)
*)

module U8 = FStar.UInt8

inline_for_extraction
let additional_info_t = bitfield uint8 5

[@@CMacro]
let additional_info_long_argument_8_bits : additional_info_t = 24uy

[@@CMacro]
let additional_info_unassigned_min : additional_info_t = 28uy

inline_for_extraction
let initial_byte' = bitsum'_type initial_byte_desc

inline_for_extraction
let initial_byte_wf' (b: initial_byte') : Tot bool =
  match b with
  | (major_type, (additional_info, _)) ->
    (if major_type = cbor_major_type_simple_value then additional_info `U8.lte` additional_info_long_argument_8_bits else true) && // TODO: support floating-point numbers
    additional_info `U8.lt` additional_info_unassigned_min
    // we disallow value 31 because we do not support indefinite lengths (section 4.2.1)

type initial_byte_t = {
  major_type: major_type_t;
  additional_info: additional_info_t;
}

inline_for_extraction
let initial_byte_wf
  (x: initial_byte_t)
: Tot bool
= initial_byte_wf' (x.major_type, (x.additional_info, ()))

let initial_byte = parse_filter_refine initial_byte_wf

module SZ = FStar.SizeT

[@@CMacro]
let additional_info_long_argument_16_bits : additional_info_t = 25uy

[@@CMacro]
let additional_info_long_argument_32_bits : additional_info_t = 26uy

[@@CMacro]
let additional_info_long_argument_64_bits : additional_info_t = 27uy

inline_for_extraction
let argument_size
  (b: initial_byte)
: Tot SZ.t
=   if b.additional_info = additional_info_long_argument_8_bits
    then 1sz
    else if b.additional_info = additional_info_long_argument_16_bits
    then 2sz
    else if b.additional_info = additional_info_long_argument_32_bits
    then 3sz
    else if b.additional_info = additional_info_long_argument_64_bits
    then 4sz
    else 0sz

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

inline_for_extraction
let simple_value_long_argument_wf // 3.3: "an encoder MUST NOT issue two-byte sequences that start with 0xf8 and continue with a byte less than 0x20"
  (x: U8.t)
: Tot bool
= min_simple_value_long_argument `U8.lte` x

let long_argument_simple_value_prop
  (b: initial_byte)
: GTot prop
= b.additional_info == additional_info_long_argument_8_bits /\ b.major_type == cbor_major_type_simple_value

let long_argument_u8_prop
  (b: initial_byte)
: GTot prop
= b.additional_info == additional_info_long_argument_8_bits /\ ~ (b.major_type == cbor_major_type_simple_value)

let long_argument_u16_prop
  (b: initial_byte)
: GTot prop
= b.additional_info == additional_info_long_argument_16_bits

let long_argument_u32_prop
  (b: initial_byte)
: GTot prop
= b.additional_info == additional_info_long_argument_32_bits

let long_argument_u64_prop
  (b: initial_byte)
: GTot prop
= b.additional_info == additional_info_long_argument_64_bits

let long_argument_other_prop
  (b: initial_byte)
: GTot prop
= (
    ~ (b.additional_info == additional_info_long_argument_8_bits \/ b.additional_info == additional_info_long_argument_16_bits \/ b.additional_info == additional_info_long_argument_32_bits \/ b.additional_info == additional_info_long_argument_64_bits)
  )

// inline_for_extraction
type long_argument
  (b: initial_byte)
= | LongArgumentSimpleValue:
      (prf: squash (long_argument_simple_value_prop b)) ->
      (v: parse_filter_refine simple_value_long_argument_wf) ->
      long_argument b
  | LongArgumentU8:
      (prf: squash (long_argument_u8_prop b)) ->
      (v: U8.t) ->
      long_argument b
  | LongArgumentU16:
      (prf: squash (long_argument_u16_prop b)) ->
      (v: U16.t) ->
      long_argument b
  | LongArgumentU32:
      (prf: squash (long_argument_u32_prop b)) ->
      (v: U32.t) ->
      long_argument b
  | LongArgumentU64:
      (prf: squash (long_argument_u64_prop b)) ->
      (v: U64.t) ->
      long_argument b
  | LongArgumentOther:
      (prf: squash (long_argument_other_prop b)) ->
      (v: unit) -> // constructors are synth functions, hence this unit argument
      long_argument b

let header = dtuple2 initial_byte long_argument

module Cast = FStar.Int.Cast

inline_for_extraction
let argument_as_raw_uint64
  (b: initial_byte { ~ (long_argument_simple_value_prop b) })
  (x: long_argument b)
: Tot raw_uint64
= match x with
  | LongArgumentU8 _ v ->
    { size = 1uy; value = Cast.uint8_to_uint64 v }
  | LongArgumentU16 _ v ->
    { size = 2uy; value = Cast.uint16_to_uint64 v }
  | LongArgumentU32 _ v ->
    { size = 3uy; value = Cast.uint32_to_uint64 v }
  | LongArgumentU64 _ v ->
    { size = 4uy; value = v }
  | LongArgumentOther _ _ ->
    { size = 0uy; value = Cast.uint8_to_uint64 b.additional_info }

let argument_as_uint64
  (b: initial_byte { ~ (long_argument_simple_value_prop b) })
  (x: long_argument b)
: Tot U64.t
= (argument_as_raw_uint64 b x).value

[@@CMacro]
let additional_info_simple_value_max : additional_info_t = 24uy

let get_header_argument_as_simple_value_initial_byte_precond
  (b: initial_byte)
: GTot bool
= 
  b.major_type = cbor_major_type_simple_value && b.additional_info `U8.lte` additional_info_simple_value_max

inline_for_extraction
let argument_as_simple_value
  (b: initial_byte)
  (x: long_argument b)
: Pure simple_value
    (requires (get_header_argument_as_simple_value_initial_byte_precond b))
    (ensures (fun _ -> True))
= match x with
  | LongArgumentOther _ _ ->
    b.additional_info
  | LongArgumentSimpleValue _ v ->
    v

(* Raw data items, disregarding ordering of map entries *)

let lseq_utf8_correct
  (ty: major_type_byte_string_or_text_string)
  (len: nat)
  (x: Seq.lseq U8.t len)
: Tot bool
= if ty = cbor_major_type_text_string
  then CBOR.Spec.API.UTF8.correct x
  else true

let content
  (h: header)
: Tot Type
= match h with
  | (| b, long_arg |) ->
      if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
      then parse_filter_refine (lseq_utf8_correct b.major_type (U64.v (argument_as_uint64 b long_arg)))
      else if b.major_type = cbor_major_type_array
      then nlist (U64.v (argument_as_uint64 b long_arg)) raw_data_item
      else if b.major_type = cbor_major_type_map
      then nlist (U64.v (argument_as_uint64 b long_arg)) (raw_data_item & raw_data_item)
      else if b.major_type = cbor_major_type_tagged
      then raw_data_item
      else unit

let raw_data_item' = dtuple2 header content

let synth_raw_data_item'
  (h: header)
  (c: content h)
: Tot raw_data_item
= match h with
  | (| b, long_arg |) ->
      if b.major_type = cbor_major_type_uint64 || b.major_type = cbor_major_type_neg_int64
      then Int64 b.major_type (argument_as_raw_uint64 b long_arg)
      else if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
      then String b.major_type (argument_as_raw_uint64 b long_arg) c
      else if b.major_type = cbor_major_type_array
      then Array (argument_as_raw_uint64 b long_arg) c
      else if b.major_type = cbor_major_type_map
      then Map (argument_as_raw_uint64 b long_arg) c
      else if b.major_type = cbor_major_type_tagged
      then Tagged (argument_as_raw_uint64 b long_arg) c
      else
        // TODO: support floats
        Simple (argument_as_simple_value b long_arg)

let synth_raw_data_item
  (x: raw_data_item')
: Tot raw_data_item
= match x with
  | (| h, c |) ->
    synth_raw_data_item' h c

#push-options "--z3rlimit 64"
#restart-solver
let synth_raw_data_item_injective : squash (synth_injective synth_raw_data_item) = ()
#pop-options

let tot_parse_initial_byte' : tot_parser _ initial_byte' =
  tot_parse_bitsum' initial_byte_desc tot_parse_u8

let parse_initial_byte' : parser _ initial_byte' =
  parse_bitsum' initial_byte_desc parse_u8

let tot_parse_initial_byte'_eq (b: bytes) : Lemma
  (ensures (parse tot_parse_initial_byte' b == parse parse_initial_byte' b))
  [SMTPat (parse tot_parse_initial_byte' b)]
= synth_bitsum'_injective initial_byte_desc;
  parse_synth_eq (parse_u8 `parse_filter` filter_bitsum' initial_byte_desc) (synth_bitsum' initial_byte_desc) b;
  parse_filter_eq parse_u8 (filter_bitsum' initial_byte_desc) b;
  tot_parse_synth_eq (tot_parse_u8 `tot_parse_filter` filter_bitsum' initial_byte_desc) (synth_bitsum' initial_byte_desc) b;
  tot_parse_filter_eq tot_parse_u8 (filter_bitsum' initial_byte_desc) b

inline_for_extraction
noextract
let synth_initial_byte
  (x: initial_byte')
: Tot initial_byte_t
= match x with
  (major_type, (additional_info, _)) -> {
    major_type = major_type;
    additional_info = additional_info;
  }

let _ : squash (synth_injective synth_initial_byte) = ()

let tot_parse_initial_byte_t : tot_parser _ initial_byte_t =
    (tot_parse_synth tot_parse_initial_byte' synth_initial_byte)

let parse_initial_byte_t : parser _ initial_byte_t =
    (parse_synth parse_initial_byte' synth_initial_byte)

let tot_parse_initial_byte_t_eq (b: bytes) : Lemma
  (ensures (parse tot_parse_initial_byte_t b == parse parse_initial_byte_t b))
  [SMTPat (parse tot_parse_initial_byte_t b)]
= parse_synth_eq parse_initial_byte' synth_initial_byte b;
  tot_parse_synth_eq tot_parse_initial_byte' synth_initial_byte b

let tot_parse_initial_byte : tot_parser _ initial_byte =
  tot_parse_filter
    tot_parse_initial_byte_t
    initial_byte_wf

let parse_initial_byte : parser _ initial_byte =
  parse_filter
    parse_initial_byte_t
    initial_byte_wf

let tot_parse_initial_byte_eq (b: bytes) : Lemma
  (ensures (parse tot_parse_initial_byte b == parse parse_initial_byte b))
  [SMTPat (parse tot_parse_initial_byte b)]
= tot_parse_filter_eq tot_parse_initial_byte_t initial_byte_wf b;
  parse_filter_eq parse_initial_byte_t initial_byte_wf b

noextract
let parse_long_argument_kind = strong_parser_kind 0 8 None

let tot_parse_long_argument
  (b: initial_byte)
: Tot (tot_parser parse_long_argument_kind (long_argument b))
=   if b.additional_info = additional_info_long_argument_8_bits
    then
      if b.major_type = cbor_major_type_simple_value
      then tot_weaken _ (tot_parse_filter tot_parse_u8 simple_value_long_argument_wf `tot_parse_synth` LongArgumentSimpleValue ())
      else tot_weaken _ (tot_parse_u8 `tot_parse_synth` LongArgumentU8 ())
    else if b.additional_info = additional_info_long_argument_16_bits
    then tot_weaken _ (tot_parse_u16 `tot_parse_synth` LongArgumentU16 ())
    else if b.additional_info = additional_info_long_argument_32_bits
    then tot_weaken _ (tot_parse_u32 `tot_parse_synth` LongArgumentU32 ())
    else if b.additional_info = additional_info_long_argument_64_bits
    then tot_weaken _ (tot_parse_u64 `tot_parse_synth` LongArgumentU64 ())
    else tot_weaken _ (tot_parse_empty `tot_parse_synth` LongArgumentOther ())

let parse_long_argument
  (b: initial_byte)
: Tot (parser parse_long_argument_kind (long_argument b))
=   if b.additional_info = additional_info_long_argument_8_bits
    then
      if b.major_type = cbor_major_type_simple_value
      then weaken _ (parse_filter parse_u8 simple_value_long_argument_wf `parse_synth` LongArgumentSimpleValue ())
      else weaken _ (parse_u8 `parse_synth` LongArgumentU8 ())
    else if b.additional_info = additional_info_long_argument_16_bits
    then weaken _ (parse_u16 `parse_synth` LongArgumentU16 ())
    else if b.additional_info = additional_info_long_argument_32_bits
    then weaken _ (parse_u32 `parse_synth` LongArgumentU32 ())
    else if b.additional_info = additional_info_long_argument_64_bits
    then weaken _ (parse_u64 `parse_synth` LongArgumentU64 ())
    else weaken _ (parse_empty `parse_synth` LongArgumentOther ())

let tot_parse_long_argument_eq
  (b: initial_byte)
  (input: bytes)
: Lemma
  (ensures (parse (tot_parse_long_argument b) input == parse (parse_long_argument b) input))
  [SMTPat (parse (tot_parse_long_argument b) input)]
=
    if b.additional_info = additional_info_long_argument_8_bits
    then
      if b.major_type = cbor_major_type_simple_value
      then begin
        parse_synth_eq
          (parse_filter parse_u8 simple_value_long_argument_wf)
          (LongArgumentSimpleValue #b ())
          input;
        parse_filter_eq parse_u8 simple_value_long_argument_wf input;
        tot_parse_synth_eq
          (tot_parse_filter tot_parse_u8 simple_value_long_argument_wf)
          (LongArgumentSimpleValue #b ())
          input;
        tot_parse_filter_eq tot_parse_u8 simple_value_long_argument_wf input
      end
      else begin
        parse_synth_eq parse_u8 (LongArgumentU8 #b ()) input;
        tot_parse_synth_eq tot_parse_u8 (LongArgumentU8 #b ()) input
      end
    else if b.additional_info = additional_info_long_argument_16_bits
    then begin
      parse_synth_eq parse_u16 (LongArgumentU16 #b ()) input;
      tot_parse_synth_eq tot_parse_u16 (LongArgumentU16 #b ()) input
    end
    else if b.additional_info = additional_info_long_argument_32_bits
    then begin
      parse_synth_eq parse_u32 (LongArgumentU32 #b ()) input;
      tot_parse_synth_eq tot_parse_u32 (LongArgumentU32 #b ()) input
    end
    else if b.additional_info = additional_info_long_argument_64_bits
    then begin
      parse_synth_eq parse_u64 (LongArgumentU64 #b ()) input;
      tot_parse_synth_eq tot_parse_u64 (LongArgumentU64 #b ()) input
    end
    else begin
      parse_synth_eq parse_empty (LongArgumentOther #b ()) input;
      tot_parse_synth_eq tot_parse_empty (LongArgumentOther #b ()) input
    end

let parse_header_kind = and_then_kind (parse_filter_kind parse_u8_kind) parse_long_argument_kind

let tot_parse_header : tot_parser parse_header_kind header =
  tot_parse_dtuple2 tot_parse_initial_byte tot_parse_long_argument

let parse_header : parser parse_header_kind header =
  parse_dtuple2 parse_initial_byte parse_long_argument

let tot_parse_dtuple2_eq'
  (#kt1: parser_kind)
  (#t1: Type)
  (pt1: tot_parser kt1 t1)
  (#kt2: parser_kind)
  (#t2: (t1 -> Type))
  (pt2: ((x: t1) -> tot_parser kt2 (t2 x)))
  (#kg1: parser_kind)
  (pg1: parser kg1 t1)
  (#kg2: parser_kind)
  (pg2: ((x: t1) -> parser kg2 (t2 x)))
  (input: bytes)
: Lemma
  (requires (
    parse pt1 input == parse pg1 input /\
    begin match parse pt1 input with
    | None -> True
    | Some (h, consumed) -> 
      let input' = Seq.slice input consumed (Seq.length input) in
      parse (pt2 h) input' == parse (pg2 h) input'
    end
  ))
  (ensures (
    parse (tot_parse_dtuple2 pt1 pt2) input == parse (parse_dtuple2 pg1 pg2) input
  ))
= parse_dtuple2_eq pg1 pg2 input

let tot_parse_header_eq
  (input: bytes)
: Lemma
  (ensures (parse tot_parse_header input == parse parse_header input))
  [SMTPat (parse tot_parse_header input)]
= tot_parse_dtuple2_eq' tot_parse_initial_byte tot_parse_long_argument parse_initial_byte parse_long_argument input

inline_for_extraction
let parse_content_kind : parser_kind = {
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
  parser_kind_injective = true;
}

inline_for_extraction
let parse_raw_data_item_kind : parser_kind = {
  parser_kind_low = 1;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
  parser_kind_injective = true;
}

let parse_content
  (p: parser parse_raw_data_item_kind raw_data_item)
  (h: header) : parser parse_content_kind (content h)
= match h with
  | (| b, long_arg |) ->
      if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
      then weaken _ (parse_filter (parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct b.major_type _))
      else if b.major_type = cbor_major_type_array
      then weaken _ (parse_nlist (U64.v (argument_as_uint64 b long_arg)) p)
      else if b.major_type = cbor_major_type_map
      then weaken _ (parse_nlist (U64.v (argument_as_uint64 b long_arg)) (p `nondep_then` p))
      else if b.major_type = cbor_major_type_tagged
      then weaken _ p
      else weaken _ parse_empty

let parse_raw_data_item_aux
  (p: parser parse_raw_data_item_kind raw_data_item)
: Tot (parser parse_raw_data_item_kind raw_data_item)
= parse_dtuple2 parse_header (parse_content p) `parse_synth` synth_raw_data_item

(* 

  A raw data item ends with zero or more raw data items, but a raw
  data item does not contain a raw data item followed by something
  that is not a raw data item. In other words, parse_raw_data_item can
  be rewritten as:

  p `parse_dtuple2` (fun x -> parse_nlist (f x) parse_raw_data_item) `parse_synth` g

  where p contains no recursive call to parse_raw_data_item. Then, in
  that case, a validator or jumper can be implemented as a loop
  counting the number of raw data items left to parse.
  
*)

let leaf_content_seq_cond
  (h: header)
: GTot prop
= 
      let (| b, _ |) = h in
      b.major_type == cbor_major_type_byte_string \/ b.major_type == cbor_major_type_text_string

inline_for_extraction
type leaf_content
  (h: header)
= | LeafContentSeq:
    (prf: squash (leaf_content_seq_cond h)) ->
    (v: parse_filter_refine (lseq_utf8_correct (dfst h).major_type (U64.v (argument_as_uint64 (dfst h) (dsnd h))))) ->
    leaf_content h
  | LeafContentEmpty:
    (prf: squash (~ (leaf_content_seq_cond h))) ->
    (v: unit) ->
    leaf_content h

let tot_parse_leaf_content
  (h: header)
: tot_parser parse_content_kind (leaf_content h)
= let b = dfst h in
  let long_arg = dsnd h in
      if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
      then tot_weaken _ (tot_parse_filter (tot_parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct (dfst h).major_type _) `tot_parse_synth` LeafContentSeq ())
      else tot_weaken _ (tot_parse_empty `tot_parse_synth` LeafContentEmpty ())

let parse_leaf_content
  (h: header)
: parser parse_content_kind (leaf_content h)
= let b = dfst h in
  let long_arg = dsnd h in
      if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
      then weaken _ (parse_filter (parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct (dfst h).major_type _) `parse_synth` LeafContentSeq ())
      else weaken _ (parse_empty `parse_synth` LeafContentEmpty ())

let tot_parse_leaf_content_eq
  (h: header)
  (input: bytes)
: Lemma
  (ensures (parse (tot_parse_leaf_content h) input == parse (parse_leaf_content h) input))
  [SMTPat (parse (tot_parse_leaf_content h) input)]
= let b = dfst h in
  let long_arg = dsnd h in
      if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
      then begin
        tot_parse_filter_eq (tot_parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct (dfst h).major_type _) input;
        parse_filter_eq (parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct (dfst h).major_type _) input;
        (tot_parse_filter (tot_parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct (dfst h).major_type _) `tot_parse_synth_eq` LeafContentSeq #h ()) input;
        (parse_filter (parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct (dfst h).major_type _) `parse_synth_eq` LeafContentSeq #h ()) input
      end
      else begin
        (tot_parse_empty `tot_parse_synth_eq` LeafContentEmpty #h ()) input;
        (parse_empty `parse_synth_eq` LeafContentEmpty #h ()) input
      end

let leaf = dtuple2 header leaf_content

let tot_parse_leaf : tot_parser _ leaf = tot_parse_header `tot_parse_dtuple2` tot_parse_leaf_content

let parse_leaf : parser _ leaf = parse_header `parse_dtuple2` parse_leaf_content

let tot_parse_leaf_eq (input: bytes) : Lemma
  (ensures (parse tot_parse_leaf input == parse parse_leaf input))
  [SMTPat (parse tot_parse_leaf input)]
= tot_parse_dtuple2_eq' tot_parse_header tot_parse_leaf_content parse_header parse_leaf_content input

let remaining_data_items_header
  (h: header)
: Tot nat
= match h with
  | (| b, long_arg |) ->
      if b.major_type = cbor_major_type_array
      then
        U64.v (argument_as_uint64 b long_arg)
      else if b.major_type = cbor_major_type_map
      then
        let count = U64.v (argument_as_uint64 b long_arg) in
        count + count
      else if b.major_type = cbor_major_type_tagged
      then 1
      else 0

let remaining_data_items
  (l: leaf)
: Tot nat
= match l with
  | (| h, _ |) -> remaining_data_items_header h

let rec pair_list_of_list
  (t: Type)
  (nb_pairs: nat)
  (x: nlist (nb_pairs + nb_pairs) t)
: Tot (nlist nb_pairs (t & t))
= match x with
  | [] -> []
  | a :: b :: q -> (a, b) :: pair_list_of_list t (nb_pairs - 1) q

let rec list_of_pair_list
  (t: Type)
  (nb_pairs: nat)
  (x: nlist nb_pairs (t & t))
: Tot (nlist (nb_pairs + nb_pairs) t)
= CBOR.Spec.Util.list_of_pair_list_length x;
  CBOR.Spec.Util.list_of_pair_list x

let rec list_of_pair_list_of_list
  (#t: Type)
  (nb_pairs: nat)
  (x: nlist (nb_pairs + nb_pairs) t)
: Lemma
  (list_of_pair_list t nb_pairs (pair_list_of_list t nb_pairs x) == x)
= match x with
  | [] -> ()
  | _ :: _ :: q -> list_of_pair_list_of_list (nb_pairs - 1) q

let rec pair_list_of_list_of_pair_list
  (#t: Type)
  (nb_pairs: nat)
  (x: nlist nb_pairs (t & t))
: Lemma
  (pair_list_of_list t nb_pairs (list_of_pair_list t nb_pairs x) == x)
= match x with
  | [] -> ()
  | _ :: q -> pair_list_of_list_of_pair_list (nb_pairs - 1) q

let pair_list_of_list_inj
  (t: Type)
  (nb_pairs: nat)
  (x1 x2: nlist (nb_pairs + nb_pairs) t)
: Lemma
  (pair_list_of_list t nb_pairs x1 == pair_list_of_list t nb_pairs x2 ==> x1 == x2)
= list_of_pair_list_of_list nb_pairs x1; 
  list_of_pair_list_of_list nb_pairs x2

let synth_injective_pair_list_of_list
  (t: Type)
  (nb_pairs: nat)
: Lemma
  (synth_injective (pair_list_of_list t nb_pairs))
= Classical.forall_intro (list_of_pair_list_of_list #t nb_pairs)

let synth_injective_pair_list_of_list_pat
  (t: Type)
  (nb_pairs: nat)
: Lemma
  (synth_injective (pair_list_of_list t nb_pairs))
  [SMTPat (pair_list_of_list t nb_pairs)]
= synth_injective_pair_list_of_list t nb_pairs

let synth_inverse_pair_list_of_list
  (t: Type)
  (nb_pairs: nat)
: Lemma
  (synth_inverse (pair_list_of_list t nb_pairs) (list_of_pair_list t nb_pairs))
//  [SMTPat (pair_list_of_list t nb_pairs)]
= Classical.forall_intro (pair_list_of_list_of_pair_list #t nb_pairs)

let synth_injective_list_of_pair_list
  (t: Type)
  (nb_pairs: nat)
: Lemma
  (synth_injective (list_of_pair_list t nb_pairs))
  [SMTPat (list_of_pair_list t nb_pairs)]
= Classical.forall_intro (pair_list_of_list_of_pair_list #t nb_pairs)

let synth_inverse_list_of_pair_list
  (t: Type)
  (nb_pairs: nat)
: Lemma
  (synth_inverse (list_of_pair_list t nb_pairs) (pair_list_of_list t nb_pairs))
  [SMTPat (list_of_pair_list t nb_pairs)]
= Classical.forall_intro (list_of_pair_list_of_list #t nb_pairs)

#push-options "--z3rlimit 64"
#restart-solver

let rec parse_pair_list_as_list
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (nb_pairs: nat)
  (input: bytes)
: Lemma
  (ensures (
    match parse (parse_nlist nb_pairs (p `nondep_then` p)) input, parse (parse_nlist (nb_pairs + nb_pairs) p) input with
    | None, None -> True
    | Some (l, consumed), Some (l', consumed') ->
      consumed == consumed' /\
      l == pair_list_of_list t nb_pairs l'
    | _ -> False
  ))
  (decreases nb_pairs)
= parse_nlist_eq nb_pairs (p `nondep_then` p) input;
  parse_nlist_eq (nb_pairs + nb_pairs) p input;
  if nb_pairs = 0
  then ()
  else begin
    nondep_then_eq #k p #k p input;
    assert (nb_pairs + nb_pairs - 1 - 1 == (nb_pairs - 1) + (nb_pairs - 1));
    match parse p input with
    | None -> ()
    | Some (x1, consumed1) ->
      let input2 = Seq.slice input consumed1 (Seq.length input) in
      parse_nlist_eq (nb_pairs + nb_pairs - 1) p input2;
      match parse p input2 with
      | None -> ()
      | Some (x2, consumed2) ->
        let input3 = Seq.slice input2 consumed2 (Seq.length input2) in
        parse_pair_list_as_list p (nb_pairs - 1) input3;
        // FIXME: WHY WHY WHY do I need all of these?
        assert (Some? (parse (parse_nlist nb_pairs (p `nondep_then` p)) input) == Some? (parse (parse_nlist (nb_pairs - 1) (p `nondep_then` p)) input3));
        assert (Some? (parse (parse_nlist (nb_pairs + nb_pairs) p) input) == Some? (parse (parse_nlist (nb_pairs + nb_pairs - 1 - 1) p) input3));
        assert (Some? (parse (parse_nlist (nb_pairs + nb_pairs) p) input) == Some? (parse (parse_nlist ((nb_pairs - 1) + (nb_pairs - 1)) p) input3));
        assert (Some? (parse (parse_nlist (nb_pairs - 1) (p `nondep_then` p)) input3) == Some? (parse (parse_nlist ((nb_pairs - 1) + (nb_pairs - 1)) p) input3))
  end

#pop-options

let content_alt = parse_recursive_payload_t raw_data_item leaf remaining_data_items

let raw_data_item_alt = parse_recursive_alt_t raw_data_item leaf remaining_data_items

let synth_raw_data_item'_from_alt
  (x: raw_data_item_alt)
: Tot raw_data_item'
= match x with
  | (| l , c |) ->
    match l with
    | (| h, lc |) ->
      match h with
      | (| b, long_arg |) ->
          if b.major_type = cbor_major_type_array
          then (| h, c |)
          else if b.major_type = cbor_major_type_map
          then (| h, pair_list_of_list _ (U64.v (argument_as_uint64 b long_arg)) c |)
          else if b.major_type = cbor_major_type_tagged
          then (| h, List.Tot.hd c |)
          else if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
          then (| h, LeafContentSeq?.v lc |)
          else (| h, () |)

#push-options "--ifuel 3 --z3rlimit_factor 2"
#restart-solver

let synth_raw_data_item'_from_alt_injective : squash (synth_injective synth_raw_data_item'_from_alt) =
  Classical.forall_intro_3 (pair_list_of_list_inj raw_data_item)

#pop-options

let synth_raw_data_item_from_alt
  (x: raw_data_item_alt)
: Tot raw_data_item
= synth_raw_data_item (synth_raw_data_item'_from_alt x)

#restart-solver

let synth_raw_data_item_from_alt_injective : squash (synth_injective synth_raw_data_item_from_alt) = ()

let parse_raw_data_item_param = {
  t = raw_data_item;
  header = leaf;
  parse_header_kind = _;
  parse_header = tot_parse_leaf;
  count = remaining_data_items;
  synth_ = synth_raw_data_item_from_alt;
  synth_inj = synth_raw_data_item_from_alt_injective;
}

let tot_parse_raw_data_item : tot_parser parse_raw_data_item_kind raw_data_item =
  parse_recursive parse_raw_data_item_param

let parse_raw_data_item : parser parse_raw_data_item_kind raw_data_item =
  parser_of_tot_parser tot_parse_raw_data_item

let parse_nlist_zero
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma (
  parse (parse_nlist 0 p) b == Some ([], 0)
)
= parse_nlist_eq 0 p b

let parse_nlist_one
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma (
  parse (parse_nlist 1 p) b == (match parse p b with
  | None -> None
  | Some (x, consumed) -> Some ([x], consumed)
  )
)
= parse_nlist_eq 1 p b

let _ : squash (simple_value == parse_filter_refine simple_value_wf) = assert_norm (simple_value == parse_filter_refine simple_value_wf)

let tot_parse_nlist_parse_nlist'
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t)
  (n: nat)
  (b: bytes)
: Lemma
  (ensures (tot_parse_nlist n p b == parse_nlist n #k p b))
= tot_parse_nlist_parse_nlist n p b

#push-options "--z3rlimit 1024 --ifuel 8 --split_queries always"

#restart-solver
let parse_raw_data_item_eq
  (b: bytes)
: Lemma
  (parse parse_raw_data_item b == parse (parse_raw_data_item_aux parse_raw_data_item) b)
=
  parse_recursive_eq parse_raw_data_item_param b;
  parse_synth_eq (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item b;
  parse_dtuple2_eq parse_header (parse_content parse_raw_data_item) b;
  tot_parse_synth_eq (parse_recursive_alt parse_raw_data_item_param tot_parse_raw_data_item) synth_raw_data_item_from_alt b;
  match parse tot_parse_header b with
  | None -> ()
  | Some (h, consumed) ->
    let b1 = Seq.slice b consumed (Seq.length b) in
    let (| f, l |) = h in
    if f.major_type = cbor_major_type_byte_string || f.major_type = cbor_major_type_text_string
    then begin
        tot_parse_filter_eq (tot_parse_lseq_bytes (U64.v (argument_as_uint64 f l))) (lseq_utf8_correct (dfst h).major_type _) b1;
        parse_filter_eq (parse_lseq_bytes (U64.v (argument_as_uint64 f l))) (lseq_utf8_correct (dfst h).major_type _) b1;
        (tot_parse_filter (tot_parse_lseq_bytes (U64.v (argument_as_uint64 f l))) (lseq_utf8_correct (dfst h).major_type _) `tot_parse_synth_eq` LeafContentSeq #h ()) b1;
        (parse_filter (parse_lseq_bytes (U64.v (argument_as_uint64 f l))) (lseq_utf8_correct (dfst h).major_type _) `parse_synth_eq` LeafContentSeq #h ()) b1
    end
    else begin
      let lc = LeafContentEmpty #h () in
      let lf : leaf = (| h, lc () |) in
      tot_parse_synth_eq tot_parse_empty lc b1;
      tot_parse_nlist_parse_nlist' tot_parse_raw_data_item (parse_raw_data_item_param.count lf) b1;
      if f.major_type = cbor_major_type_tagged
      then tot_parse_nlist_eq (parse_raw_data_item_param.count lf) tot_parse_raw_data_item b1
      else if f.major_type = cbor_major_type_array
      then ()
      else if f.major_type = cbor_major_type_map
      then begin
        let nb_pairs = U64.v (argument_as_uint64 f l) in
        parse_pair_list_as_list #raw_data_item #parse_raw_data_item_kind parse_raw_data_item nb_pairs b1
      end
      else ()
    end

#pop-options

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_header_initial_byte
  (h: header)
: Tot initial_byte
= match h with (| b, _ |) -> b

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_header_long_argument
  (h: header)
: Tot (long_argument (get_header_initial_byte h))
= match h with (| _, l |) -> l

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_header_argument_as_uint64
  (h: header { ~ (long_argument_simple_value_prop (get_header_initial_byte h)) })
: Tot U64.t
= match h with (| b, l |) -> argument_as_uint64 b l

(* Serialization *)

let _ : squash (major_type_t == bitfield uint8 3) =
  assert_norm (major_type_t == bitfield_refine 8 U8.v 3);
  uint8_v_eq_fn ()

inline_for_extraction
let mk_initial_byte
  (t: major_type_t)
  (x: additional_info_t)
: Pure initial_byte
    (requires (initial_byte_wf' (t, (x, ()))))
    (ensures (fun _ -> True))
= {
    major_type = t;
    additional_info = x;
  }

#push-options "--z3rlimit 16"

let raw_uint64_as_argument
  (t: major_type_t)
  (x: raw_uint64)
: Pure header
    (requires (t `U8.lt` cbor_major_type_simple_value))
    (ensures (fun y ->
      let (| b, arg |) = y in
      t == b.major_type /\
      argument_as_raw_uint64 b arg = x
    ))
= if x.size = 0uy
  then (| mk_initial_byte t (Cast.uint64_to_uint8 x.value), LongArgumentOther () () |)
  else if x.size = 1uy
  then (| mk_initial_byte t additional_info_long_argument_8_bits, LongArgumentU8 () (Cast.uint64_to_uint8 x.value) |)
  else if x.size = 2uy
  then (| mk_initial_byte t additional_info_long_argument_16_bits, LongArgumentU16 () (Cast.uint64_to_uint16 x.value) |)
  else if x.size = 3uy
  then (| mk_initial_byte t additional_info_long_argument_32_bits, LongArgumentU32 () (Cast.uint64_to_uint32 x.value) |)
  else (| mk_initial_byte t additional_info_long_argument_64_bits, LongArgumentU64 () x.value |)

#pop-options

let simple_value_as_argument
  (x: simple_value)
: Pure header
    (requires True)
    (ensures (fun y ->
      let (| b, arg |) = y in
      b.major_type = cbor_major_type_simple_value /\
      b.additional_info `U8.lte` additional_info_long_argument_8_bits /\
      argument_as_simple_value b arg == x
    ))
= if x `U8.lte` max_simple_value_additional_info
  then (| mk_initial_byte cbor_major_type_simple_value x, LongArgumentOther () () |)
  else (| mk_initial_byte cbor_major_type_simple_value additional_info_long_argument_8_bits, LongArgumentSimpleValue () x |)

inline_for_extraction
noextract
let synth_initial_byte_recip
  (x: initial_byte_t)
: Tot initial_byte'
= (x.major_type, (x.additional_info, ()))

let tot_serialize_initial_byte' : tot_serializer tot_parse_initial_byte' =
      (tot_serialize_bitsum'
        initial_byte_desc
        tot_serialize_u8
      )

let serialize_initial_byte' : serializer parse_initial_byte' =
  serialize_ext (parser_of_tot_parser tot_parse_initial_byte') (serializer_of_tot_serializer tot_serialize_initial_byte') parse_initial_byte'

let tot_serialize_initial_byte_t : tot_serializer tot_parse_initial_byte_t =
    (tot_serialize_synth
      tot_parse_initial_byte'
      synth_initial_byte
      tot_serialize_initial_byte'
      synth_initial_byte_recip
      ()
    )

let serialize_initial_byte_t : serializer parse_initial_byte_t =
  serialize_ext (parser_of_tot_parser tot_parse_initial_byte_t) (serializer_of_tot_serializer tot_serialize_initial_byte_t) parse_initial_byte_t

let tot_serialize_initial_byte : tot_serializer tot_parse_initial_byte =
  tot_serialize_filter
    tot_serialize_initial_byte_t
    initial_byte_wf

let serialize_initial_byte : serializer parse_initial_byte =
  serialize_ext (parser_of_tot_parser tot_parse_initial_byte) (serializer_of_tot_serializer tot_serialize_initial_byte) parse_initial_byte

#restart-solver

let tot_serialize_long_argument
  (b: initial_byte)
: Tot (tot_serializer (tot_parse_long_argument b))
=   if b.additional_info = additional_info_long_argument_8_bits
    then
      if b.major_type = cbor_major_type_simple_value
      then
        tot_serialize_weaken _ (tot_serialize_synth _ (LongArgumentSimpleValue ()) (tot_serialize_filter tot_serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v ())
      else tot_serialize_weaken _ (tot_serialize_synth _ (LongArgumentU8 ()) (tot_serialize_u8) LongArgumentU8?.v ())
    else if b.additional_info = additional_info_long_argument_16_bits
    then tot_serialize_weaken _ (tot_serialize_synth _ (LongArgumentU16 ()) (tot_serialize_u16) LongArgumentU16?.v ())
    else if b.additional_info = additional_info_long_argument_32_bits
    then tot_serialize_weaken _ (tot_serialize_synth _ (LongArgumentU32 ()) (tot_serialize_u32) LongArgumentU32?.v ())
    else if b.additional_info = additional_info_long_argument_64_bits
    then tot_serialize_weaken _ (tot_serialize_synth _ (LongArgumentU64 ()) (tot_serialize_u64) LongArgumentU64?.v ())
    else tot_serialize_weaken _ (tot_serialize_synth _ (LongArgumentOther ()) tot_serialize_empty LongArgumentOther?.v ())

let serialize_long_argument
  (b: initial_byte)
: Tot (serializer (parse_long_argument b))
= serialize_ext (parser_of_tot_parser (tot_parse_long_argument b)) (serializer_of_tot_serializer (tot_serialize_long_argument b)) (parse_long_argument b)

let tot_serialize_header : tot_serializer tot_parse_header =
  tot_serialize_dtuple2 tot_serialize_initial_byte tot_serialize_long_argument

let serialize_header : serializer parse_header =
  serialize_ext (parser_of_tot_parser tot_parse_header) (serializer_of_tot_serializer tot_serialize_header) parse_header

#push-options "--z3rlimit 16"

let synth_raw_data_item_recip
  (x: raw_data_item)
: Tot raw_data_item'
= match x with
  | Simple v ->
    (| simple_value_as_argument v, () |)
  | Int64 m v ->
    (| raw_uint64_as_argument m v, () |)
  | String m len v ->
    (| raw_uint64_as_argument m len, v |)
  | Array len v ->
    (| raw_uint64_as_argument cbor_major_type_array len, v |)
  | Map len v ->
    (| raw_uint64_as_argument cbor_major_type_map len, v |)
  | Tagged tag v ->
    (| raw_uint64_as_argument cbor_major_type_tagged tag, v |)

#restart-solver
let synth_raw_data_item_recip_inverse : squash (synth_inverse synth_raw_data_item synth_raw_data_item_recip) = ()

#pop-options

let synth_raw_data_item'_from_alt_recip
  (x: raw_data_item')
: Tot raw_data_item_alt
= match x with
  | (| h, c |) ->
    match h with
    | (| b, long_arg |) ->
        if b.major_type = cbor_major_type_array
        then (| (| h, LeafContentEmpty () () |), c |)
        else if b.major_type = cbor_major_type_map
        then (| (| h, LeafContentEmpty () () |), list_of_pair_list _ (U64.v (argument_as_uint64 b long_arg)) c |)
        else if b.major_type = cbor_major_type_tagged
        then (| (| h, LeafContentEmpty () () |), [c] |)
        else if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
        then (| (| h, LeafContentSeq () c |), [] |)
        else (| (| h, LeafContentEmpty () () |), [] |)

#push-options "--ifuel 3"
#restart-solver

let synth_raw_data_item'_from_alt_inverse : squash (synth_inverse synth_raw_data_item'_from_alt synth_raw_data_item'_from_alt_recip ) =
  Classical.forall_intro_2 (pair_list_of_list_of_pair_list #raw_data_item)

#pop-options

let synth_raw_data_item_from_alt_recip
  (x: raw_data_item)
: Tot raw_data_item_alt
= synth_raw_data_item'_from_alt_recip (synth_raw_data_item_recip x)

#restart-solver

let synth_raw_data_item_from_alt_inverse : squash (synth_inverse synth_raw_data_item_from_alt synth_raw_data_item_from_alt_recip) = ()

let tot_serialize_leaf_content
  (h: header)
: Tot (tot_serializer (tot_parse_leaf_content h))
= match h with
  | (| b, long_arg |) ->
      if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
      then tot_serialize_weaken _ (tot_serialize_synth _ (LeafContentSeq ()) (tot_serialize_filter (tot_serialize_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct b.major_type _)) LeafContentSeq?.v ())
      else tot_serialize_weaken _ (tot_serialize_synth _ (LeafContentEmpty ()) tot_serialize_empty LeafContentEmpty?.v ())

let serialize_leaf_content
  (h: header)
: Tot (serializer (parse_leaf_content h))
=  match h with
  | (| b, long_arg |) ->
      if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
      then serialize_weaken _ (serialize_synth _ (LeafContentSeq ()) (serialize_filter (serialize_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct b.major_type _)) LeafContentSeq?.v ())
      else serialize_weaken _ (serialize_synth _ (LeafContentEmpty ()) serialize_empty LeafContentEmpty?.v ())

let tot_serialize_leaf : tot_serializer tot_parse_leaf =
  tot_serialize_dtuple2 tot_serialize_header tot_serialize_leaf_content

let serialize_leaf : serializer parse_leaf =
  serialize_dtuple2 serialize_header serialize_leaf_content

(* Construction of the serializer, by "step indexing" over the "level"
   (in fact the depth) of the raw data item. *)

open LowParse.WellFounded

let rec level
  (d: raw_data_item)
: Tot nat
= match d with
  | Array _ v ->
    let v : list raw_data_item = v in
    1 + fold_left_list v (acc_level v level) 0
  | Map _ v ->
    let v : list (raw_data_item & raw_data_item) = v in
    1 + fold_left_list v (acc_level_pair v level) 0
  | Tagged _ v -> 1 + level v
  | _ -> 0

unfold
let raw_data_item_has_level = has_level level

unfold
let raw_data_item_pair_has_level = pair_has_level level

let rec fold_left_list_acc_level_list_of_pair_list
  (n: nat)
  (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires (forall_list v (raw_data_item_pair_has_level n)))
  (ensures (forall_list (list_of_pair_list raw_data_item (List.Tot.length v) v) (raw_data_item_has_level n)))
  (decreases v)
= match v with
  | [] -> ()
  | (a1, a2) :: q ->
    forall_list_cons (a1, a2) q (raw_data_item_pair_has_level n);
    let q' = list_of_pair_list raw_data_item (List.Tot.length q) q in
    forall_list_cons a1 (a2 :: q') (raw_data_item_has_level n);
    forall_list_cons a2 q' (raw_data_item_has_level n);
    fold_left_list_acc_level_list_of_pair_list n q

unfold
let raw_data_item_list_has_pred_level = list_has_pred_level level

#push-options "--z3rlimit 32"
#restart-solver

let synth_raw_data_item_from_alt_recip_list_has_pred_level
  (x: raw_data_item)
  (n: nat)
: Lemma
  (requires (has_level level n x))
  (ensures (list_has_pred_level level n (dsnd (synth_raw_data_item_from_alt_recip x))))
= match x with
  | Array _ l ->
    let l : list raw_data_item = l in
    assert_norm (level x == 1 + fold_left_list l (acc_level l level) 0);
    fold_left_list_has_level_gen level (n - 1) l 0;
    assert (list_has_pred_level level n (dsnd (synth_raw_data_item_from_alt_recip x)))
  | Map _ l ->
    let l : list (raw_data_item & raw_data_item) = l in
    assert_norm (level x == 1 + fold_left_list l (acc_level_pair l level) 0);
    fold_left_list_pair_has_level_gen level (n - 1) l 0;
    assert (dsnd (synth_raw_data_item_from_alt_recip x) == list_of_pair_list raw_data_item (List.Tot.length l) l);
    fold_left_list_acc_level_list_of_pair_list (n - 1) l;
    assert (list_has_pred_level level n (dsnd (synth_raw_data_item_from_alt_recip x)))
  | _ -> ()

#pop-options

#restart-solver

let serialize_raw_data_item_param : serialize_recursive_param parse_raw_data_item_param = {
  serialize_header = tot_serialize_leaf;
  synth_recip = synth_raw_data_item_from_alt_recip;
  synth_inv = synth_raw_data_item_from_alt_inverse;
  level = level;
  level_correct = synth_raw_data_item_from_alt_recip_list_has_pred_level;
}

let tot_serialize_raw_data_item : tot_serializer tot_parse_raw_data_item =
  serialize_recursive serialize_raw_data_item_param

let serialize_raw_data_item : serializer parse_raw_data_item =
  serializer_of_tot_serializer tot_serialize_raw_data_item

(* Serialization equations to prove the functional correctness of implementations *)

#push-options "--z3rlimit 32"
#restart-solver

let serialize_content
  (h: header)
: Tot (serializer (parse_content parse_raw_data_item h))
= match h with
  | (| b, long_arg |) ->
      if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
      then serialize_weaken _ (serialize_filter (serialize_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) (lseq_utf8_correct b.major_type _))
      else if b.major_type = cbor_major_type_array
      then serialize_weaken _ (serialize_nlist (U64.v (argument_as_uint64 b long_arg)) serialize_raw_data_item)
      else if b.major_type = cbor_major_type_map
      then serialize_weaken _ (serialize_nlist (U64.v (argument_as_uint64 b long_arg)) (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item))
      else if b.major_type = cbor_major_type_tagged
      then serialize_weaken _ serialize_raw_data_item
      else serialize_weaken _ serialize_empty

#pop-options

let serialize_raw_data_item_aux : serializer (parse_raw_data_item_aux parse_raw_data_item) =
  serialize_synth
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()

let serialize_raw_data_item_aux_correct
  (x: raw_data_item)
: Lemma
  (bare_serialize serialize_raw_data_item x == bare_serialize serialize_raw_data_item_aux x)
= Classical.forall_intro parse_raw_data_item_eq;
  let s' = serialize_ext parse_raw_data_item serialize_raw_data_item (parse_raw_data_item_aux parse_raw_data_item) in
  serializer_unique #parse_raw_data_item_kind (parse_raw_data_item_aux parse_raw_data_item) serialize_raw_data_item_aux s' x

// Some lemmas about the initial byte

let get_major_type_synth_raw_data_item
  (x: raw_data_item')
: Lemma
  (get_major_type (synth_raw_data_item x) == (match x with (| (| b, _ |), _ |) -> b.major_type))
  [SMTPat (synth_raw_data_item x)]
= assert_norm (pow2 3 == 8)

let get_raw_data_item_header
  (x: raw_data_item)
: GTot header
= dfst (synth_raw_data_item_recip x)

let get_header_major_type
  (h: header)
: Tot major_type_t
= let (| b, _ |) = h in
  b.major_type

inline_for_extraction
noextract
let cps_simple_value_as_argument
  (t': Type)
  (t'_ifthenelse: if_combinator_weak t')
  (x: simple_value)
  (k: (h: header) -> Pure t'
    (requires (h == simple_value_as_argument x))
    (ensures (fun _ -> True))
  )
: Tot t'
= t'_ifthenelse (x `U8.lte` max_simple_value_additional_info)
    (fun _then -> k (| mk_initial_byte cbor_major_type_simple_value x, LongArgumentOther () () |))
    (fun _else -> k (| mk_initial_byte cbor_major_type_simple_value additional_info_long_argument_8_bits, LongArgumentSimpleValue () x |))

inline_for_extraction
noextract
let cps_raw_uint64_as_argument
  (t': Type)
  (t'_ifthenelse: if_combinator_weak t')
  (ty: major_type_t { ty `U8.lt` cbor_major_type_simple_value })
  (x: raw_uint64)
  (k: (h: header) -> Pure t'
    (requires (h == raw_uint64_as_argument ty x))
    (ensures (fun _ -> True))
  )
: Tot t'
= t'_ifthenelse (x.size = 0uy)
    (fun _ -> k (| mk_initial_byte ty (Cast.uint64_to_uint8 x.value), LongArgumentOther () () |))
    (fun _ -> t'_ifthenelse (x.size = 1uy)
      (fun _ -> k (| mk_initial_byte ty additional_info_long_argument_8_bits, LongArgumentU8 () (Cast.uint64_to_uint8 x.value) |))
      (fun _ -> t'_ifthenelse (x.size = 2uy)
        (fun _ -> k (| mk_initial_byte ty additional_info_long_argument_16_bits, LongArgumentU16 () (Cast.uint64_to_uint16 x.value) |))
        (fun _ -> t'_ifthenelse (x.size = 3uy)
          (fun _ -> k (| mk_initial_byte ty additional_info_long_argument_32_bits, LongArgumentU32 () (Cast.uint64_to_uint32 x.value) |))
          (fun _ -> k (| mk_initial_byte ty additional_info_long_argument_64_bits, LongArgumentU64 () x.value |))
        )
      )
    )

let get_uint64_as_initial_byte
  (ty: major_type_t { ty `U8.lt` cbor_major_type_simple_value })
  (x: raw_uint64)
: Tot U8.t
= cps_raw_uint64_as_argument
    U8.t
    (fun cond iftrue iffalse -> if cond then iftrue () else iffalse ())
    ty
    x
    (fun h -> match h with (| b, _ |) -> mk_synth_initial_byte (synth_initial_byte_recip b))

#push-options "--z3rlimit 32"
#restart-solver

let get_initial_byte_header_correct
  (h: header)
: Lemma
  (let b' = bare_serialize serialize_header h in
    Seq.length b' > 0 /\
    mk_synth_initial_byte (synth_initial_byte_recip (dfst h)) == Seq.index b' 0)
= let (| b, _ |) = h in
  tot_serialize_synth_eq
    tot_parse_initial_byte'
    synth_initial_byte
    tot_serialize_initial_byte'
    synth_initial_byte_recip
    ()
    b;
  tot_serialize_bitsum'_eq
    initial_byte_desc
    tot_serialize_u8
    (synth_initial_byte_recip b);
  serialize_u8_spec (synth_bitsum'_recip initial_byte_desc (synth_initial_byte_recip b))

#pop-options

#push-options "--z3rlimit 16"

#restart-solver
let get_initial_byte_header_inj
  (h1 h2: header)
: Lemma
  (requires (
    let b1 = bare_serialize serialize_header h1 in
    let b2 = bare_serialize serialize_header h2 in
    Seq.length b1 > 0 /\
    Seq.length b2 > 0 /\
    Seq.index (b1) 0 == Seq.index (b2) 0
  ))
  (ensures (dfst h1 == dfst h2))
=
  let (| b1, l1 |) = h1 in
  let (| b2, l2 |) = h2 in
  let b1' = synth_bitsum'_recip initial_byte_desc (synth_initial_byte_recip b1) in
  let b2' = synth_bitsum'_recip initial_byte_desc (synth_initial_byte_recip b2) in
  get_initial_byte_header_correct h1;
  get_initial_byte_header_correct h2;
  assert (synth_bitsum' initial_byte_desc b1' == synth_initial_byte_recip b1);
  assert (synth_bitsum' initial_byte_desc b2' == synth_initial_byte_recip b2)

let get_uint64_as_initial_byte_header_correct
  (ty: major_type_t { ty `U8.lt` cbor_major_type_simple_value })
  (x: raw_uint64)
: Lemma
  (let b' = bare_serialize serialize_header (raw_uint64_as_argument ty x) in
    Seq.length b' > 0 /\
    get_uint64_as_initial_byte ty x == Seq.index (b') 0)
= let h = raw_uint64_as_argument ty x in
  get_initial_byte_header_correct h

let get_major_type_synth_raw_data_item_recip
  (x: raw_data_item)
: Lemma
  (get_major_type x == get_header_major_type (dfst (synth_raw_data_item_recip x)))
= ()

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_int64_value
  (v: Ghost.erased raw_data_item)
  (h: header)
: Pure raw_uint64
    (requires h == dfst (synth_raw_data_item_recip v) /\ Int64? v)
    (ensures fun res -> Int64? v /\ res == Int64?.v v)
= match h with
  (| b, l |) -> argument_as_raw_uint64 b l

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_string_length
  (v: Ghost.erased raw_data_item)
  (h: header)
: Pure raw_uint64
    (requires h == dfst (synth_raw_data_item_recip v) /\ String? v)
    (ensures fun res -> String? v /\ res == String?.len v)
= match h with
  (| b, l |) -> argument_as_raw_uint64 b l

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_tagged_tag
  (v: Ghost.erased raw_data_item)
  (h: header)
: Pure raw_uint64
    (requires h == dfst (synth_raw_data_item_recip v) /\ Tagged? v)
    (ensures fun res -> Tagged? v /\ res == Tagged?.tag v)
= match h with
  (| b, l |) -> argument_as_raw_uint64 b l

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_simple_value
  (v: Ghost.erased raw_data_item)
  (h: header)
: Pure simple_value
    (requires h == dfst (synth_raw_data_item_recip v) /\ Simple? v)
    (ensures fun res -> Simple? v /\ res == Simple?.v v)
= match h with
  (| b, l |) -> argument_as_simple_value b l

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_array_length
  (v: Ghost.erased raw_data_item)
  (h: header)
: Pure raw_uint64
    (requires h == dfst (synth_raw_data_item_recip v) /\ Array? v)
    (ensures fun res -> Array? v /\ res == Array?.len v)
= match h with
  (| b, l |) -> argument_as_raw_uint64 b l

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_map_length
  (v: Ghost.erased raw_data_item)
  (h: header)
: Pure raw_uint64
    (requires h == dfst (synth_raw_data_item_recip v) /\ Map? v)
    (ensures fun res -> Map? v /\ res == Map?.len v)
= match h with
  (| b, l |) -> argument_as_raw_uint64 b l

#pop-options

// Ordering of map keys (Section 4.2)

let rec list_for_all_holds_on_pair_list_of_pair_list
  (#t: Type)
  (pred: t -> bool)
  (l: list (t & t))
: Lemma
  (List.Tot.for_all (holds_on_pair pred) l == List.Tot.for_all pred (list_of_pair_list _ (List.Tot.length l) l))
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_holds_on_pair_list_of_pair_list pred q

#push-options "--z3rlimit 64"

#restart-solver
let holds_on_raw_data_item_eq_recursive
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (holds_on_raw_data_item p x == (p x && List.Tot.for_all (holds_on_raw_data_item p) (get_children serialize_raw_data_item_param x)))
= holds_on_raw_data_item_eq p x;
  match x with
  | Map _ l ->
    let l : list (raw_data_item & raw_data_item) = l in
    list_for_all_holds_on_pair_list_of_pair_list (holds_on_raw_data_item p) l
  | _ -> ()

#pop-options

let holds_on_raw_data_item_pred (p: (raw_data_item -> bool)) : pred_recursive_t serialize_raw_data_item_param = {
  base = p;
  pred = holds_on_raw_data_item p;
  prf = holds_on_raw_data_item_eq_recursive p;
}

(* 4.2.1 Deterministically encoded CBOR: The keys in every map MUST be sorted in the bytewise lexicographic order of their deterministic encodings. *)

let serialized_lex_order
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x1 x2: t)
: GTot bool
= LowParse.Spec.SeqBytes.bytes_lex_order (s x1) (s x2)

let tot_serialized_lex_order
  (#k: parser_kind)
  (#t: Type)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (x1 x2: t)
: Tot bool
= LowParse.Spec.SeqBytes.bytes_lex_order (s x1) (s x2)

let deterministically_encoded_cbor_map_key_order
  (k1 k2: raw_data_item)
: Tot bool
= tot_serialized_lex_order tot_serialize_raw_data_item k1 k2

let deterministically_encoded_cbor_map_key_order_irrefl
  (x y: raw_data_item)
: Lemma
  (requires (Ghost.reveal deterministically_encoded_cbor_map_key_order x y))
  (ensures (~ (x == y)))
= LowParse.Spec.SeqBytes.bytes_lex_order_irrefl (serialize_raw_data_item x) (serialize_raw_data_item y)

let deterministically_encoded_cbor_map_key_order_trans
  (x y z: raw_data_item)
: Lemma
  (requires (Ghost.reveal deterministically_encoded_cbor_map_key_order x y /\ Ghost.reveal deterministically_encoded_cbor_map_key_order y z))
  (ensures (Ghost.reveal deterministically_encoded_cbor_map_key_order x z))
= LowParse.Spec.SeqBytes.bytes_lex_order_trans (serialize_raw_data_item x) (serialize_raw_data_item y) (serialize_raw_data_item z)

let deterministically_encoded_cbor_map_key_order_total
  (x y: raw_data_item)
: Lemma
  (ensures (x == y \/ Ghost.reveal deterministically_encoded_cbor_map_key_order x y \/ Ghost.reveal deterministically_encoded_cbor_map_key_order y x))
= Classical.move_requires (serializer_injective #parse_raw_data_item_kind parse_raw_data_item serialize_raw_data_item x) y;
  LowParse.Spec.SeqBytes.bytes_lex_order_total (serialize_raw_data_item x) (serialize_raw_data_item y)

let deterministically_encoded_cbor_map_key_order_assoc_ext :
  (m1: list (raw_data_item & raw_data_item)) ->
  (m2: list (raw_data_item & raw_data_item)) ->
  (ext: (
    (k: raw_data_item) ->
    Lemma
    (list_ghost_assoc k m1 == list_ghost_assoc k m2)
  )) ->
  squash (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m1) ->
  squash (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m2) ->
  Lemma
  (ensures (m1 == m2))
= fun m1 m2 ext _ _ -> map_entry_order_assoc_ext deterministically_encoded_cbor_map_key_order deterministically_encoded_cbor_map_key_order_irrefl deterministically_encoded_cbor_map_key_order_trans deterministically_encoded_cbor_map_key_order_total m1 m2 ext

(* Comparisons with unserialized values *)

module I16 = FStar.Int16

let byte_compare_pure_impl (x y: byte) : Pure I16.t
  (requires True)
  (ensures (fun res -> I16.v res `same_sign` byte_compare x y))
= FStar.Int.Cast.uint8_to_int16 x `I16.sub` FStar.Int.Cast.uint8_to_int16 y

#push-options "--z3rlimit 32"
#restart-solver

let int_compare (n1 n2: int) : int =
  if n1 < n2 then -1 else
  if n1 = n2 then 0 else
  1

let serialize_initial_byte_compare
  (b1 b2: initial_byte)
: Lemma
  (ensures (
    bytes_lex_compare
      (bare_serialize serialize_initial_byte b1)
      (bare_serialize serialize_initial_byte b2)
    == (
      let ty_compare = byte_compare b1.major_type b2.major_type in
      if ty_compare = 0
      then byte_compare b1.additional_info b2.additional_info
      else ty_compare
  )))
= let b1_ = synth_initial_byte_recip b1 in
  let b2_ = synth_initial_byte_recip b2 in
  tot_serialize_synth_eq
    tot_parse_initial_byte'
    synth_initial_byte
    tot_serialize_initial_byte'
    synth_initial_byte_recip
    ()
    b1;
  tot_serialize_synth_eq
    tot_parse_initial_byte'
    synth_initial_byte
    tot_serialize_initial_byte'
    synth_initial_byte_recip
    ()
    b2;
  tot_serialize_bitsum'_eq
    initial_byte_desc
    tot_serialize_u8
    b1_;
  tot_serialize_bitsum'_eq
    initial_byte_desc
    tot_serialize_u8
    b2_;
  let b1' = synth_bitsum'_recip initial_byte_desc b1_ in
  let b2' = synth_bitsum'_recip initial_byte_desc b2_ in
  serialize_u8_spec' b1';
  serialize_u8_spec' b2';
  assert (Seq.length (bare_serialize serialize_initial_byte b1) == 1);
  seq_to_list_length_one (bare_serialize serialize_initial_byte b1);
  assert (Seq.length (bare_serialize serialize_initial_byte b2) == 1);
  seq_to_list_length_one (bare_serialize serialize_initial_byte b2);  
  assert (bytes_lex_compare
      (bare_serialize serialize_initial_byte b1)
      (bare_serialize serialize_initial_byte b2) == byte_compare b1' b2'
  );
  assert (synth_bitsum' initial_byte_desc b1' == b1_);
  assert (synth_bitsum' initial_byte_desc b2' == b2_);
  assert (U8.v b1.major_type == get_bitfield (U8.v b1') 5 8);
  assert (U8.v b1.additional_info == get_bitfield (U8.v b1') 0 5);
  get_bitfield_eq (U8.v b1') 5 8;
  get_bitfield_eq (U8.v b1') 0 5;
  assert (U8.v b2.major_type == get_bitfield (U8.v b2') 5 8);
  assert (U8.v b2.additional_info == get_bitfield (U8.v b2') 0 5);
  get_bitfield_eq (U8.v b2') 5 8;
  get_bitfield_eq (U8.v b2') 0 5;
  assert_norm (pow2 5 == 32);
  assert_norm (pow2 3 == 8);
  ()

let serialize_initial_byte_lt
  (b1 b2: initial_byte)
: Lemma
  (ensures (
    bytes_lex_order
      (bare_serialize serialize_initial_byte b1)
      (bare_serialize serialize_initial_byte b2)
    == (
      (b1.major_type `U8.lt` b2.major_type) ||
        ((b1.major_type = b2.major_type) && (b1.additional_info `U8.lt` b2.additional_info))
  )))
= serialize_initial_byte_compare b1 b2

#pop-options

let tot_serialized_lex_compare
  (#k: parser_kind)
  (#t: Type)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (x1 x2: t)
: Tot int
= LowParse.Spec.SeqBytes.bytes_lex_compare (s x1) (s x2)

let serialized_lex_compare
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x1 x2: t)
: GTot int
= LowParse.Spec.SeqBytes.bytes_lex_compare (s x1) (s x2)

let tot_serialized_lex_compare_eq_ghost
  (#k: parser_kind)
  (#t: Type)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (x1 x2: t)
: Lemma
  (tot_serialized_lex_compare s x1 x2 == serialized_lex_compare (serializer_of_tot_serializer s) x1 x2)
= ()

let serialized_lex_compare_ext
  (#t: Type)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2)
  (x1 x2: t)
: Lemma
  (requires (forall x . parse p1 x == parse p2 x))
  (ensures (
    serialized_lex_compare s1 x1 x2 == serialized_lex_compare s2 x1 x2
  ))
= serializer_unique_strong s1 s2 x1;
  serializer_unique_strong s1 s2 x2

let tot_serialized_lex_compare_ext
  (#t: Type)
  (#k1: parser_kind)
  (#p1: tot_parser k1 t)
  (s1: tot_serializer p1)
  (#k2: parser_kind)
  (#p2: tot_parser k2 t)
  (s2: tot_serializer p2)
  (x1 x2: t)
: Lemma
  (requires (forall x . parse p1 x == parse p2 x))
  (ensures (
    tot_serialized_lex_compare s1 x1 x2 == tot_serialized_lex_compare s2 x1 x2
  ))
= tot_serialized_lex_compare_eq_ghost s1 x1 x2;
  tot_serialized_lex_compare_eq_ghost s2 x1 x2;
  serialized_lex_compare_ext (serializer_of_tot_serializer s1) (serializer_of_tot_serializer s2) x1 x2

let bytes_lex_compare_prefix
  (l: bytes)
  (l1 l2: bytes)
: Lemma
  (ensures (bytes_lex_compare (Seq.append l l1) (Seq.append l l2) == bytes_lex_compare l1 l2))
= seq_to_list_append l l1;
  seq_to_list_append l l2;
  lex_compare_prefix byte_compare (fun _ _ -> ()) (Seq.seq_to_list l) (Seq.seq_to_list l1) (Seq.seq_to_list l2)

#push-options "--z3rlimit 16"

let rec bytes_lex_compare_serialize_strong_prefix1
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (l1 l2: t)
  (suff1 suff2: bytes)
  (pre: bytes)
  (mid1 mid2: bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    bare_serialize s l1 == pre `Seq.append` mid1 /\
    bare_serialize s l2 == pre `Seq.append` mid2 /\
    Seq.length mid1 <= Seq.length mid2
  ))
  (ensures (
    bytes_lex_compare (bare_serialize s l1 `Seq.append` suff1) (bare_serialize s l2 `Seq.append` suff2) == (
      let comp = bytes_lex_compare mid1 mid2 in
      if comp = 0
      then bytes_lex_compare suff1 suff2
      else comp
  )))
  (decreases (Seq.length mid1))
= bytes_lex_compare_prefix pre mid1 mid2;
  Seq.append_assoc pre mid1 suff1;
  Seq.append_assoc pre mid2 suff2;
  bytes_lex_compare_prefix pre (mid1 `Seq.append` suff1) (mid2 `Seq.append` suff2);
  if Seq.length mid1 = 0
  then begin
    assert (mid1 `Seq.equal` Seq.empty);
    Seq.append_empty_r pre;
    Seq.append_empty_r (bare_serialize s l2);
    serialize_strong_prefix s l2 l1 Seq.empty mid2;
    bytes_lex_compare_prefix (bare_serialize s l1) suff1 suff2
  end else begin
    let x = Seq.index mid1 0 in
    let x2 = Seq.index mid2 0 in
    let mid1' = Seq.tail mid1 in
    let mid2' = Seq.tail mid2 in
    assert (mid1 `Seq.equal` Seq.cons x mid1');
    assert (mid2 `Seq.equal` Seq.cons x2 mid2');
    Seq.lemma_append_cons mid1 suff1;
    Seq.lemma_append_cons mid2 suff2;
    assert ((mid1 `Seq.append` suff1) == Seq.cons x (mid1' `Seq.append` suff1));
    assert ((mid2 `Seq.append` suff2) == Seq.cons x2 (mid2' `Seq.append` suff2));
    let c = byte_compare x x2 in
    if c = 0
    then begin
      assert (x == x2);
      let sx = Seq.slice mid1 0 1 in
      assert (sx `Seq.equal` Seq.slice mid2 0 1);
      let pre' = pre `Seq.append` sx in
      Seq.lemma_split mid1 1;
      Seq.lemma_split mid2 1;
      Seq.append_assoc pre sx (Seq.tail mid1);
      Seq.append_assoc pre sx (Seq.tail mid2);
      bytes_lex_compare_serialize_strong_prefix1 s l1 l2 suff1 suff2 pre' mid1' mid2'
    end
    else ()
  end

#pop-options

let rec lex_compare_oppose
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
: Lemma
  (requires (forall x1 x2 . compare x2 x1 == - compare x1 x2))
  (ensures (lex_compare compare l1 l2 == - lex_compare compare l2 l1))
= match l1, l2 with
  | [], [] -> ()
  | [], _ -> ()
  | a1 :: q1, [] -> ()
  | a1 :: q1, a2 :: q2 ->
    lex_compare_oppose compare q1 q2

let bytes_lex_compare_oppose
  (l1 l2: bytes)
: Lemma
  (bytes_lex_compare l1 l2 == - bytes_lex_compare l2 l1)
= lex_compare_oppose byte_compare (Seq.seq_to_list l1) (Seq.seq_to_list l2)

let bytes_lex_compare_serialize_strong_prefix0
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (l1 l2: t)
  (suff1 suff2: bytes)
  (pre: bytes)
  (mid1 mid2: bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    bare_serialize s l1 == pre `Seq.append` mid1 /\
    bare_serialize s l2 == pre `Seq.append` mid2
  ))
  (ensures (
    bytes_lex_compare (bare_serialize s l1 `Seq.append` suff1) (bare_serialize s l2 `Seq.append` suff2) == (
      let comp = bytes_lex_compare mid1 mid2 in
      if comp = 0
      then bytes_lex_compare suff1 suff2
      else comp
  )))
= if Seq.length mid1 <= Seq.length mid2
  then bytes_lex_compare_serialize_strong_prefix1 s l1 l2 suff1 suff2 pre mid1 mid2
  else begin
    lex_compare_oppose byte_compare (Seq.seq_to_list (bare_serialize s l1 `Seq.append` suff1)) (Seq.seq_to_list (bare_serialize s l2 `Seq.append` suff2));
    lex_compare_oppose byte_compare (Seq.seq_to_list mid1) (Seq.seq_to_list mid2);
    lex_compare_oppose byte_compare (Seq.seq_to_list suff1) (Seq.seq_to_list suff2);
    bytes_lex_compare_serialize_strong_prefix1 s l2 l1 suff2 suff1 pre mid2 mid1
  end

let bytes_lex_compare_serialize_strong_prefix
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (l1 l2: t)
  (suff1 suff2: bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong
  ))
  (ensures (
    bytes_lex_compare (bare_serialize s l1 `Seq.append` suff1) (bare_serialize s l2 `Seq.append` suff2) == (
      let comp = bytes_lex_compare (bare_serialize s l1) (bare_serialize s l2) in
      if comp = 0
      then bytes_lex_compare suff1 suff2
      else comp
  )))
= let s1 = bare_serialize s l1 in
  let s2 = bare_serialize s l2 in
  Seq.append_empty_l s1;
  Seq.append_empty_l s2;
  bytes_lex_compare_serialize_strong_prefix0 s l1 l2 suff1 suff2 Seq.empty s1 s2

let bytes_lex_compare_tot_serialize_strong_prefix
  (#k: parser_kind)
  (#t: Type)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (l1 l2: t)
  (suff1 suff2: bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong
  ))
  (ensures (
    bytes_lex_compare (bare_serialize s l1 `Seq.append` suff1) (bare_serialize s l2 `Seq.append` suff2) == (
      let comp = bytes_lex_compare (bare_serialize s l1) (bare_serialize s l2) in
      if comp = 0
      then bytes_lex_compare suff1 suff2
      else comp
  )))
= bytes_lex_compare_serialize_strong_prefix (serializer_of_tot_serializer s) l1 l2 suff1 suff2

#push-options "--z3rlimit 32"
#restart-solver

let serialized_lex_compare_major_type_intro
  (v1 v2: raw_data_item)
: Lemma
  (requires (
    byte_compare (get_major_type v1) (get_major_type v2) <> 0
  ))
  (ensures (
    tot_serialized_lex_compare tot_serialize_raw_data_item v1 v2 ==
      byte_compare (get_major_type v1) (get_major_type v2)
  ))
= get_major_type_synth_raw_data_item_recip v1;
  serialize_raw_data_item_aux_correct v1;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v1;
  let v1' = synth_raw_data_item_recip v1 in
  serialize_dtuple2_eq serialize_header serialize_content v1';
  let (| h1, c1 |) = v1' in
//  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h1;
  let (| b1, l1 |) = h1 in
  get_major_type_synth_raw_data_item_recip v2;
  serialize_raw_data_item_aux_correct v2;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v2;
  let v2' = synth_raw_data_item_recip v2 in
  serialize_dtuple2_eq serialize_header serialize_content v2';
  let (| h2, c2 |) = v2' in
//  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h2;
  let (| b2, l2 |) = h2 in
  serialize_initial_byte_compare b1 b2;
  Seq.append_assoc (bare_serialize serialize_initial_byte b1) (bare_serialize (serialize_long_argument b1) l1) (bare_serialize (serialize_content h1) c1);
  Seq.append_assoc (bare_serialize serialize_initial_byte b2) (bare_serialize (serialize_long_argument b2) l2) (bare_serialize (serialize_content h2) c2);
  bytes_lex_compare_serialize_strong_prefix serialize_initial_byte b1 b2 (bare_serialize (serialize_long_argument b1) l1 `Seq.append` bare_serialize (serialize_content h1) c1) (bare_serialize (serialize_long_argument b2) l2 `Seq.append` bare_serialize (serialize_content h2) c2)

let deterministically_encoded_cbor_map_key_order_major_type_intro
  (v1 v2: raw_data_item)
: Lemma
  (requires (
    U8.v (get_major_type v1) < U8.v (get_major_type v2)
  ))
  (ensures (
    deterministically_encoded_cbor_map_key_order v1 v2 == true
  ))
= serialized_lex_compare_major_type_intro v1 v2

let bytes_lex_compare_refl
  (x: bytes)
: Lemma
  (bytes_lex_compare x x == 0)
  [SMTPat (bytes_lex_compare x x)]
= Seq.append_empty_r x;
  bytes_lex_compare_prefix x Seq.empty Seq.empty

#pop-options

#push-options "--z3rlimit 256 --split_queries always"

let serialized_lex_compare_simple_value
  (x1 x2: simple_value)
: Lemma
  (ensures (
    tot_serialized_lex_compare tot_serialize_raw_data_item (Simple x1) (Simple x2) ==
      byte_compare x1 x2
  ))
= let v1 = Simple x1 in
  let v2 = Simple x2 in
  serialize_raw_data_item_aux_correct v1;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v1;
  let v1' = synth_raw_data_item_recip v1 in
  serialize_dtuple2_eq serialize_header serialize_content v1';
  let (| h1, c1 |) = v1' in
//  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h1;
  let (| b1, l1 |) = h1 in
  serialize_raw_data_item_aux_correct v2;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v2;
  let v2' = synth_raw_data_item_recip v2 in
  serialize_dtuple2_eq serialize_header serialize_content v2';
  let (| h2, c2 |) = v2' in
//  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h2;
  let (| b2, l2 |) = h2 in
  serialize_initial_byte_compare b1 b2;
  Seq.append_assoc (bare_serialize serialize_initial_byte b1) (bare_serialize (serialize_long_argument b1) l1) (bare_serialize (serialize_content h1) c1);
  Seq.append_assoc (bare_serialize serialize_initial_byte b2) (bare_serialize (serialize_long_argument b2) l2) (bare_serialize (serialize_content h2) c2);
  bytes_lex_compare_serialize_strong_prefix serialize_initial_byte b1 b2 (bare_serialize (serialize_long_argument b1) l1 `Seq.append` bare_serialize (serialize_content h1) c1) (bare_serialize (serialize_long_argument b2) l2 `Seq.append` bare_serialize (serialize_content h2) c2);
  tot_serialize_length tot_serialize_initial_byte b1;
  seq_to_list_length_one (bare_serialize serialize_initial_byte b1);
  tot_serialize_length tot_serialize_initial_byte b2;
  seq_to_list_length_one (bare_serialize serialize_initial_byte b2);
  seq_to_list_append (bare_serialize (serialize_long_argument b1) l1) (bare_serialize (serialize_content h1) c1);
  seq_to_list_append (bare_serialize (serialize_long_argument b2) l2) (bare_serialize (serialize_content h2) c2);
  if (x1 `U8.lte` max_simple_value_additional_info || x2 `U8.lte` max_simple_value_additional_info)
  then ()
  else begin
    assert (b1 == b2);
    assert (b1 == mk_initial_byte cbor_major_type_simple_value additional_info_long_argument_8_bits);
    let LongArgumentSimpleValue _ x1' = l1 in
    assert (x1 == x1');
    let p1' : tot_parser parse_long_argument_kind (long_argument b1) = LowParse.Spec.Base.tot_weaken parse_long_argument_kind (tot_parse_synth (tot_parse_filter tot_parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b1 ())) in
    assert (tot_parse_long_argument b1 == p1');
    let s1_pre = tot_serialize_synth #_ #_ #(long_argument b1) _ (LongArgumentSimpleValue #b1 ()) (tot_serialize_filter tot_serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v () in
    let s1' : tot_serializer p1' = tot_serialize_weaken parse_long_argument_kind s1_pre in
    serializer_unique #parse_long_argument_kind (parse_long_argument b1) (serialize_long_argument b1) s1' l1;
    serialize_u8_spec x1;
    tot_serialize_synth_eq #_ #_ #(long_argument b1) (tot_parse_filter tot_parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b1 ()) (tot_serialize_filter tot_serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v () l1;
    assert (bare_serialize s1_pre l1 == bare_serialize (tot_serialize_filter tot_serialize_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue?.v l1));
    assert (bare_serialize s1' l1 == bare_serialize (tot_serialize_filter tot_serialize_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue?.v l1));
    assert (bare_serialize s1' l1 == Seq.create 1 (x1' <: byte));
    seq_to_list_length_one (bare_serialize s1' l1);
    assert (bare_serialize (serialize_long_argument b1) l1 == Seq.create 1 (x1 <: U8.t));
    seq_to_list_length_one (bare_serialize (serialize_long_argument b1) l1);
    assert (b2 == mk_initial_byte cbor_major_type_simple_value additional_info_long_argument_8_bits);
    let LongArgumentSimpleValue _ x2' = l2 in
    assert (x2 == x2');
    let p2' : tot_parser parse_long_argument_kind (long_argument b2) = LowParse.Spec.Base.tot_weaken parse_long_argument_kind (tot_parse_synth (tot_parse_filter tot_parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b2 ())) in
    assert (tot_parse_long_argument b2 == p2');
    let s2_pre = tot_serialize_synth #_ #_ #(long_argument b2) _ (LongArgumentSimpleValue #b2 ()) (tot_serialize_filter tot_serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v () in
    let s2' : tot_serializer p2' = tot_serialize_weaken parse_long_argument_kind s2_pre in
    serializer_unique #parse_long_argument_kind (parse_long_argument b2) (serialize_long_argument b2) s2' l2;
    serialize_u8_spec x2;
    tot_serialize_synth_eq #_ #_ #(long_argument b2) (tot_parse_filter tot_parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b2 ()) (tot_serialize_filter tot_serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v () l2;
    assert (bare_serialize s2_pre l2 == bare_serialize (tot_serialize_filter tot_serialize_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue?.v l2));
    assert (bare_serialize s2' l2 == bare_serialize (tot_serialize_filter tot_serialize_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue?.v l2));
    assert (bare_serialize s2' l2 == Seq.create 1 x2');
    seq_to_list_length_one (bare_serialize s2' l2);
    assert (bare_serialize (serialize_long_argument b2) l2 == Seq.create 1 (x2 <: U8.t));
    seq_to_list_length_one (bare_serialize (serialize_long_argument b2) l2);
    bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (bare_serialize (serialize_content h1) c1) (bare_serialize (serialize_content h2) c2)
  end
#pop-options

let deterministically_encoded_cbor_map_key_order_simple_value_correct
  (x1 x2: simple_value)
: Lemma
  (ensures (deterministically_encoded_cbor_map_key_order (Simple x1) (Simple x2) == x1 `U8.lt` x2))
= serialized_lex_compare_simple_value x1 x2

#restart-solver
let lex_compare_with_header_long_argument
  (ty1: major_type_t { ty1 `U8.lt` cbor_major_type_simple_value })
  (x1: raw_uint64)
  (ty2: major_type_t { ty2 `U8.lt` cbor_major_type_simple_value })
  (x2: raw_uint64)
: Lemma
  (requires (
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2
  ))
  (ensures (
    let h1 = raw_uint64_as_argument ty1 x1 in
    let (| b1, l1 |) = h1 in
    let h2 = raw_uint64_as_argument ty2 x2 in
    let (| b2, l2 |) = h2 in
    ty1 == ty2 /\
    b1 == b2 /\
    (bytes_lex_compare (bare_serialize serialize_header h1) (bare_serialize serialize_header h2) ==
      bytes_lex_compare (bare_serialize (serialize_long_argument b1) l1) (bare_serialize (serialize_long_argument b2) l2))
  ))
=
  let h1 = raw_uint64_as_argument ty1 x1 in
  let h2 = raw_uint64_as_argument ty2 x2 in
  get_uint64_as_initial_byte_header_correct ty1 x1;
  get_uint64_as_initial_byte_header_correct ty2 x2;
  get_initial_byte_header_inj h1 h2;
//  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h1;
//  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h2;
  let (| b1, l1 |) = h1 in
  let (| _, l2 |) = h2 in
  bytes_lex_compare_prefix (bare_serialize serialize_initial_byte b1) (bare_serialize (serialize_long_argument b1) l1) (bare_serialize (serialize_long_argument b1) l2)

let rec lex_compare_values
  (#t: Type)
  (compare: t -> t -> int { forall x y . let c = compare x y in c == 0 \/ c == 1 \/ c == -1 })
  (l1 l2: list t)
: Lemma
  (let c = lex_compare compare l1 l2 in
    c == 0 \/ c == 1 \/ c == -1
  )
= match l1, l2 with
  | _ :: q1, _ :: q2 ->
    lex_compare_values compare q1 q2
  | _ -> ()

let bytes_lex_compare_values
  (x y: bytes)
: Lemma
  (let c = bytes_lex_compare x y in c == 0 \/ c == 1 \/ c == -1)
  [SMTPat (bytes_lex_compare x y)]
= lex_compare_values byte_compare (Seq.seq_to_list x) (Seq.seq_to_list y)

#push-options "--z3rlimit 32"

let big_endian_lex_compare'
  (n: nat)
  (x y: nat)
: Lemma
  (
    let open FStar.Mul in
    (x < pow2 (8 * n) /\ y < pow2 (8 * n)) ==>
    (bytes_lex_compare (LowParse.Endianness.n_to_be n x) (LowParse.Endianness.n_to_be n y) == int_compare x y)
  )
= if x < pow2 (let open FStar.Mul in 8 * n) && y < pow2 (let open FStar.Mul in 8 * n)
  then begin
    bytes_lex_compare_oppose (LowParse.Endianness.n_to_be n x) (LowParse.Endianness.n_to_be n y);
    LowParse.Spec.Endianness.big_endian_lex_compare n byte_compare (fun _ _ -> ()) (fun _ _ -> ()) x y;
    LowParse.Spec.Endianness.big_endian_lex_compare n byte_compare (fun _ _ -> ()) (fun _ _ -> ()) y x
  end
  else ()

#pop-options

#push-options "--z3rlimit 64"
#restart-solver
let lex_compare_with_header_uint
  (ty1: major_type_t { ty1 `U8.lt` cbor_major_type_simple_value })
  (x1: raw_uint64)
  (ty2: major_type_t { ty2 `U8.lt` cbor_major_type_simple_value })
  (x2: raw_uint64)
  (b1: initial_byte)
  (#t: Type)
  (#k: parser_kind)
  (p: tot_parser k t)
  (f: (t -> Tot (long_argument b1)) { synth_injective f })
  (g: (long_argument b1 -> Tot t) { synth_inverse f g })
  (s: tot_serializer p)
  (n: nat)
  (uv: (t -> FStar.UInt.uint_t (8 `op_Multiply` n)))
  (s_spec: (
    (x: t) ->
    Lemma
    (bare_serialize s x == FStar.Endianness.n_to_be n (uv x))
  ))
  (uv_spec: (
    (x: raw_uint64) ->
    Lemma
    (requires (
      dfst (raw_uint64_as_argument ty1 x) == b1
    ))
    (ensures (
      uv (g (dsnd (raw_uint64_as_argument ty1 x))) == U64.v x.value
    ))
  ))
: Lemma
  (requires (
    let h1 = raw_uint64_as_argument ty1 x1 in
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2 /\
    dfst h1 == b1 /\
    parse_long_argument_kind `is_weaker_than` k /\
    tot_parse_long_argument b1 == LowParse.Spec.Base.tot_weaken parse_long_argument_kind (tot_parse_synth p f)
  ))
  (ensures (
    ty1 == ty2 /\
    x1.size == x2.size /\
    bytes_lex_compare (bare_serialize serialize_header (raw_uint64_as_argument ty1 x1)) (bare_serialize serialize_header (raw_uint64_as_argument ty2 x2)) == int_compare (U64.v x1.value) (U64.v x2.value)
  ))
= lex_compare_with_header_long_argument ty1 x1 ty2 x2;
  uv_spec x1;
  uv_spec x2;
  let (| _, l1 |) = raw_uint64_as_argument ty1 x1 in
  let (| _, l2 |) = raw_uint64_as_argument ty2 x2 in
  let p1' : tot_parser parse_long_argument_kind (long_argument b1) = LowParse.Spec.Base.tot_weaken parse_long_argument_kind (tot_parse_synth (p) f) in
  assert (tot_parse_long_argument b1 == p1');
  let s1_pre = tot_serialize_synth #_ #_ #(long_argument b1) _ f (s) g () in
  let s1' : tot_serializer p1' = tot_serialize_weaken parse_long_argument_kind s1_pre in
  serializer_unique #parse_long_argument_kind (parse_long_argument b1) (serialize_long_argument b1) s1' l1;
  assert (bare_serialize s1' l1 == bare_serialize s1_pre l1);
  tot_serialize_synth_eq #_ #_ #(long_argument b1) _ f (s) g () l1;
  s_spec (g l1);
  serializer_unique #parse_long_argument_kind (parse_long_argument b1) (serialize_long_argument b1) s1' l2;
  assert (bare_serialize s1' l2 == bare_serialize s1_pre l2);
  tot_serialize_synth_eq #_ #_ #(long_argument b1) _ f (s) g () l2;
  s_spec (g l2);
  big_endian_lex_compare' n (uv (g l1)) (uv (g l2))

#restart-solver
let lex_compare_with_header_correct
  (ty1: major_type_t { ty1 `U8.lt` cbor_major_type_simple_value })
  (x1: raw_uint64)
  (ty2: major_type_t { ty2 `U8.lt` cbor_major_type_simple_value })
  (x2: raw_uint64)
: Lemma
  (requires (
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2
  ))
  (ensures (
    ty1 == ty2 /\
    x1.size == x2.size /\
    bytes_lex_compare (bare_serialize serialize_header (raw_uint64_as_argument ty1 x1)) (bare_serialize serialize_header (raw_uint64_as_argument ty2 x2)) == int_compare (U64.v x1.value) (U64.v x2.value)
  ))
= let h1 = raw_uint64_as_argument ty1 x1 in
  let (| b1, l1 |) = h1 in
  let a1 = b1.additional_info in
  if a1 = additional_info_long_argument_8_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 tot_parse_u8 (LongArgumentU8 #b1 ()) LongArgumentU8?.v tot_serialize_u8 1 U8.v (fun x -> serialize_u8_spec_be x) (fun x -> ())
  end else
  if a1 = additional_info_long_argument_16_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 tot_parse_u16 (LongArgumentU16 #b1 ()) LongArgumentU16?.v tot_serialize_u16 2 U16.v (fun x -> serialize_u16_spec_be x) (fun x -> ())
  end else
  if a1 = additional_info_long_argument_32_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 tot_parse_u32 (LongArgumentU32 #b1 ()) LongArgumentU32?.v tot_serialize_u32 4 U32.v (fun x -> serialize_u32_spec_be x) (fun x -> ())
  end else
  if a1 = additional_info_long_argument_64_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 tot_parse_u64 (LongArgumentU64 #b1 ()) LongArgumentU64?.v tot_serialize_u64 8 U64.v (fun x -> serialize_u64_spec_be x) (fun x -> ())
  end else
  begin
    lex_compare_with_header_long_argument ty1 x1 ty2 x2;
    let (| _, l2 |) = raw_uint64_as_argument ty2 x2 in
    let p1' : tot_parser parse_long_argument_kind (long_argument b1) = LowParse.Spec.Base.tot_weaken parse_long_argument_kind (tot_parse_synth tot_parse_empty (LongArgumentOther #b1 ())) in
    assert (tot_parse_long_argument b1 == p1');
    let s1_pre = tot_serialize_synth #_ #_ #(long_argument b1) _ (LongArgumentOther #b1 ()) tot_serialize_empty LongArgumentOther?.v () in
    let s1' : tot_serializer p1' = tot_serialize_weaken parse_long_argument_kind s1_pre in
    serializer_unique #parse_long_argument_kind (parse_long_argument b1) (serialize_long_argument b1) s1' l1;
    assert (bare_serialize s1' l1 == bare_serialize s1_pre l1);
    tot_serialize_synth_eq #_ #_ #(long_argument b1) _ (LongArgumentOther #b1 ()) tot_serialize_empty LongArgumentOther?.v () l1;
    assert (bare_serialize s1' l1 `Seq.equal` Seq.empty);
    assert (bare_serialize (serialize_long_argument b1) l1 == Seq.empty);
    serializer_unique #parse_long_argument_kind (parse_long_argument b1) (serialize_long_argument b1) s1' l2;
    assert (bare_serialize s1' l2 == bare_serialize s1_pre l2);
    assert (bare_serialize s1' l2 `Seq.equal` Seq.empty);
    assert (bare_serialize (serialize_long_argument b1) l2 == Seq.empty)
  end

#pop-options

let raw_uint64_compare
  (x1 x2: raw_uint64)
: Tot int
=
      let c = int_compare (U8.v x1.size) (U8.v x2.size) in
      if c = 0
      then int_compare (U64.v x1.value) (U64.v x2.value)
      else c

#push-options "--z3rlimit 64"
#restart-solver

let lex_compare_header_intro
  (ty: major_type_t { ty `U8.lt` cbor_major_type_simple_value })
  (x1: raw_uint64)
  (x2: raw_uint64)
: Lemma
  (ensures (
    bytes_lex_compare (bare_serialize serialize_header (raw_uint64_as_argument ty x1)) (bare_serialize serialize_header (raw_uint64_as_argument ty x2)) == raw_uint64_compare x1 x2
  ))
= get_uint64_as_initial_byte_header_correct ty x1;
  get_uint64_as_initial_byte_header_correct ty x2;
  if get_uint64_as_initial_byte ty x1 = get_uint64_as_initial_byte ty x2
  then lex_compare_with_header_correct ty x1 ty x2
  else begin
    let h1 = raw_uint64_as_argument ty x1 in
//    serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h1;
    let (| b1, l1 |) = h1 in
    let h2 = raw_uint64_as_argument ty x2 in
//    serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h2;
    let (| b2, l2 |) = h2 in
    serialize_initial_byte_compare b1 b2;
    bytes_lex_compare_serialize_strong_prefix serialize_initial_byte b1 b2 (bare_serialize (serialize_long_argument b1) l1) (bare_serialize (serialize_long_argument b2) l2)
  end

let serialized_lex_compare_int64
  (ty: major_type_uint64_or_neg_int64)
  (x1 x2: raw_uint64)
: Lemma
  (ensures (bytes_lex_compare (bare_serialize serialize_raw_data_item (Int64 ty x1)) (bare_serialize serialize_raw_data_item (Int64 ty x2)) == raw_uint64_compare x1 x2))
= 
  let v1 = Int64 ty x1 in
  serialize_raw_data_item_aux_correct v1;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v1;
  let v1' = synth_raw_data_item_recip v1 in
  serialize_dtuple2_eq serialize_header serialize_content v1';
  let (| h1, c1 |) = v1' in
  let v2 = Int64 ty x2 in
  serialize_raw_data_item_aux_correct v2;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v2;
  let v2' = synth_raw_data_item_recip v2 in
  serialize_dtuple2_eq serialize_header serialize_content v2';
  let (| h2, c2 |) = v2' in
  lex_compare_header_intro ty x1 x2;
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (bare_serialize (serialize_content h1) c1) (bare_serialize (serialize_content h2) c2)

let raw_uint64_lt
  (x1 x2: raw_uint64)
: Tot bool
= x1.size `U8.lt` x2.size || (x1.size = x2.size && x1.value `U64.lt` x2.value)

let lex_order_int64_correct
  (ty: major_type_uint64_or_neg_int64)
  (x1 x2: raw_uint64)
: Lemma
  (ensures (bytes_lex_order (bare_serialize serialize_raw_data_item (Int64 ty x1)) (bare_serialize serialize_raw_data_item (Int64 ty x2)) == x1 `raw_uint64_lt` x2))
= serialized_lex_compare_int64 ty x1 x2

#pop-options

#push-options "--z3rlimit 128"
#restart-solver

let serialized_lex_compare_string
  (ty: major_type_byte_string_or_text_string)
  (len1: raw_uint64)
  (x1: Seq.lseq byte (U64.v len1.value) { lseq_utf8_correct ty (U64.v len1.value) x1 })
  (len2: raw_uint64)
  (x2: Seq.lseq byte (U64.v len2.value) { lseq_utf8_correct ty (U64.v len2.value) x2 })
: Lemma
  (ensures (
    tot_serialized_lex_compare tot_serialize_raw_data_item (String ty len1 x1) (String ty len2 x2) == (
      let c = raw_uint64_compare len1 len2 in
      if c = 0
      then bytes_lex_compare x1 x2
      else c
  )))
= 
  let v1 = String ty len1 x1 in
  serialize_raw_data_item_aux_correct v1;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v1;
  let v1' = synth_raw_data_item_recip v1 in
  serialize_dtuple2_eq serialize_header serialize_content v1';
  let (| h1, c1 |) = v1' in
  let v2 = String ty len2 x2 in
  serialize_raw_data_item_aux_correct v2;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v2;
  let v2' = synth_raw_data_item_recip v2 in
  serialize_dtuple2_eq serialize_header serialize_content v2';
  let (| h2, c2 |) = v2' in
  lex_compare_header_intro ty len1 len2;
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (bare_serialize (serialize_content h1) c1) (bare_serialize (serialize_content h2) c2)

let deterministically_encoded_cbor_map_key_order_string_correct
  (ty: major_type_byte_string_or_text_string)
  (len1: raw_uint64)
  (x1: Seq.lseq byte (U64.v len1.value) { lseq_utf8_correct ty (U64.v len1.value) x1 })
  (len2: raw_uint64)
  (x2: Seq.lseq byte (U64.v len2.value) { lseq_utf8_correct ty (U64.v len2.value) x2 })
: Lemma
  (ensures (
    deterministically_encoded_cbor_map_key_order (String ty len1 x1) (String ty len2 x2) ==
      (len1 `raw_uint64_lt` len2 || (len1 = len2 && bytes_lex_order x1 x2))
  ))
= serialized_lex_compare_string ty len1 x1 len2 x2

let serialized_lex_compare_tagged
  (tag1: raw_uint64)
  (x1: raw_data_item)
  (tag2: raw_uint64)
  (x2: raw_data_item)
: Lemma
  (ensures (
    tot_serialized_lex_compare tot_serialize_raw_data_item (Tagged tag1 x1) (Tagged tag2 x2) == (
      let c = raw_uint64_compare tag1 tag2 in
      if c = 0
      then tot_serialized_lex_compare tot_serialize_raw_data_item x1 x2
      else c
  )))
= 
  let v1 = Tagged tag1 x1 in
  serialize_raw_data_item_aux_correct v1;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v1;
  let v1' = synth_raw_data_item_recip v1 in
  serialize_dtuple2_eq serialize_header serialize_content v1';
  let (| h1, c1 |) = v1' in
  let v2 = Tagged tag2 x2 in
  serialize_raw_data_item_aux_correct v2;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v2;
  let v2' = synth_raw_data_item_recip v2 in
  serialize_dtuple2_eq serialize_header serialize_content v2';
  let (| h2, c2 |) = v2' in
  lex_compare_header_intro cbor_major_type_tagged tag1 tag2;
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (bare_serialize (serialize_content h1) c1) (bare_serialize (serialize_content h2) c2)

let deterministically_encoded_cbor_map_key_order_tagged_correct
  (tag1: raw_uint64)
  (x1: raw_data_item)
  (tag2: raw_uint64)
  (x2: raw_data_item)
: Lemma
  (ensures (
    deterministically_encoded_cbor_map_key_order (Tagged tag1 x1) (Tagged tag2 x2) ==
      (tag1 `raw_uint64_lt` tag2 || (tag1 = tag2 && deterministically_encoded_cbor_map_key_order x1 x2))
  ))
= serialized_lex_compare_tagged tag1 x1 tag2 x2

#pop-options

#push-options "--z3rlimit 16"

let rec serialized_lex_compare_nlist
  (#t: Type)
  (#kt: parser_kind)
  (#pt: tot_parser kt t)
  (st: tot_serializer pt)
  (#kg: parser_kind)
  (#pg: parser kg t)
  (sg: serializer pg)
  (n: nat)
  (x1 x2: nlist n t)
: Lemma
  (requires (kg.parser_kind_subkind == Some ParserStrong /\
    (forall x . parse pt x == parse pg x)
  ))
  (ensures (
    serialized_lex_compare (serialize_nlist n sg) x1 x2 == lex_compare (tot_serialized_lex_compare st) x1 x2
  ))
  (decreases n)
= if n = 0
  then begin
    ()
  end
  else begin
    let a1 :: q1 = x1 in
    let a2 :: q2 = x2 in
    serialize_nlist_cons (n - 1) sg a1 q1;
    serializer_unique_strong sg (serializer_of_tot_serializer st) a1;
    serializer_unique_strong sg (serializer_of_tot_serializer st) a2;
    serialize_nlist_cons (n - 1) sg a2 q2;
    bytes_lex_compare_serialize_strong_prefix sg a1 a2 (bare_serialize (serialize_nlist (n - 1) sg) q1) (bare_serialize (serialize_nlist (n - 1) sg) q2);
    serialized_lex_compare_nlist st sg (n - 1) q1 q2
  end

let rec lex_compare_ext
  (#t: Type)
  (compare1 compare2: t -> t -> int)
  (l1 l2: list t)
  (prf: (x1: t) -> (x2: t { List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 }) -> Lemma
    (compare1 x1 x2 == compare2 x1 x2)
  )
: Lemma
  (ensures (lex_compare compare1 l1 l2 == lex_compare compare2 l1 l2))
  (decreases l1)
= match l1, l2 with
  | a1 :: q1, a2 :: q2 ->
    prf a1 a2;
    lex_compare_ext compare1 compare2 q1 q2 prf
  | _ -> ()

#pop-options

#push-options "--z3rlimit 64 --split_queries always"

let serialized_lex_compare_array_aux
  (len1: raw_uint64)
  (x1: list raw_data_item {List.Tot.length x1 == U64.v len1.value})
  (len2: raw_uint64)
  (x2: list raw_data_item {List.Tot.length x2 == U64.v len2.value})
: Lemma
  (ensures (
    bytes_lex_compare (serialize serialize_raw_data_item (Array len1 x1)) (serialize serialize_raw_data_item (Array len2 x2)) == (
      let c = raw_uint64_compare len1 len2 in
      if c = 0
      then bytes_lex_compare (serialize (serialize_nlist (U64.v len1.value) serialize_raw_data_item) x1) (serialize (serialize_nlist (U64.v len2.value) serialize_raw_data_item) x2)
      else c
  )))
= 
  let v1 = Array len1 x1 in
  serialize_raw_data_item_aux_correct v1;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v1;
  let v1' = synth_raw_data_item_recip v1 in
  serialize_dtuple2_eq serialize_header serialize_content v1';
  let (| h1, c1 |) = v1' in
  let v2 = Array len2 x2 in
  serialize_raw_data_item_aux_correct v2;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v2;
  let v2' = synth_raw_data_item_recip v2 in
  serialize_dtuple2_eq serialize_header serialize_content v2';
  let (| h2, c2 |) = v2' in
  lex_compare_header_intro cbor_major_type_array len1 len2;
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (bare_serialize (serialize_content h1) c1) (bare_serialize (serialize_content h2) c2)

#pop-options

#push-options "--z3rlimit 32"

let serialized_lex_compare_array
  (len1: raw_uint64)
  (x1: list raw_data_item {List.Tot.length x1 == U64.v len1.value})
  (len2: raw_uint64)
  (x2: list raw_data_item {List.Tot.length x2 == U64.v len2.value})
: Lemma
  (ensures (
    tot_serialized_lex_compare tot_serialize_raw_data_item (Array len1 x1) (Array len2 x2) == (
      let c = raw_uint64_compare len1 len2 in
      if c = 0
      then lex_compare (tot_serialized_lex_compare tot_serialize_raw_data_item) x1 x2
      else c
  )))
= 
  let v1 = Array len1 x1 in
  let v1' = synth_raw_data_item_recip v1 in
  let (| h1, c1 |) = v1' in
  let v2 = Array len2 x2 in
  let v2' = synth_raw_data_item_recip v2 in
  let (| h2, c2 |) = v2' in
  serialized_lex_compare_array_aux len1 x1 len2 x2;
  if len1 = len2
  then serialized_lex_compare_nlist tot_serialize_raw_data_item serialize_raw_data_item (U64.v len1.value) c1 c2
  else ()

let tot_nondep_then_eq_gen
  (#t1: Type)
  (#kt1: parser_kind)
  (pt1: tot_parser kt1 t1)
  (#kg1: parser_kind)
  (pg1: parser kg1 t1)
  (#t2: Type)
  (#kt2: parser_kind)
  (pt2: tot_parser kt2 t2)
  (#kg2: parser_kind)
  (pg2: parser kg2 t2)
  (sq: squash (
    (forall x . parse pt1 x == parse pg1 x) /\
    (forall x . parse pt2 x == parse pg2 x)
  ))
  (x: bytes)
: Lemma
  (ensures 
    parse (tot_nondep_then pt1 pt2) x == parse (nondep_then pg1 pg2) x
  )
= nondep_then_eq (parser_of_tot_parser pt1) (parser_of_tot_parser pt2) x;
  nondep_then_eq pg1 pg2 x

#pop-options

#push-options "--z3rlimit 64 --split_queries always"

let serialized_lex_compare_map_aux
  (len1: raw_uint64)
  (x1: list (raw_data_item & raw_data_item) {List.Tot.length x1 == U64.v len1.value})
  (len2: raw_uint64)
  (x2: list (raw_data_item & raw_data_item) {List.Tot.length x2 == U64.v len2.value})
: Lemma
  (ensures (
    bytes_lex_compare (serialize serialize_raw_data_item (Map len1 x1)) (serialize serialize_raw_data_item (Map len2 x2)) == (
      let c = raw_uint64_compare len1 len2 in
      if c = 0
      then bytes_lex_compare (serialize (serialize_nlist (U64.v len1.value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) x1) (serialize (serialize_nlist (U64.v len2.value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) x2)
      else c
  )))
= 
  let v1 = Map len1 x1 in
  serialize_raw_data_item_aux_correct v1;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v1;
  let v1' = synth_raw_data_item_recip v1 in
  serialize_dtuple2_eq serialize_header serialize_content v1';
  let (| h1, c1 |) = v1' in
  let v2 = Map len2 x2 in
  serialize_raw_data_item_aux_correct v2;
  serialize_synth_eq
    _
    synth_raw_data_item
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item_recip
    ()
    v2;
  let v2' = synth_raw_data_item_recip v2 in
  serialize_dtuple2_eq serialize_header serialize_content v2';
  let (| h2, c2 |) = v2' in
  lex_compare_header_intro cbor_major_type_map len1 len2;
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (bare_serialize (serialize_content h1) c1) (bare_serialize (serialize_content h2) c2)

let serialized_lex_compare_map
  (len1: raw_uint64)
  (x1: list (raw_data_item & raw_data_item) {List.Tot.length x1 == U64.v len1.value})
  (len2: raw_uint64)
  (x2: list (raw_data_item & raw_data_item) {List.Tot.length x2 == U64.v len2.value})
: Lemma
  (ensures (
    tot_serialized_lex_compare tot_serialize_raw_data_item (Map len1 x1) (Map len2 x2) == (
      let c = raw_uint64_compare len1 len2 in
      if c = 0
      then lex_compare (tot_serialized_lex_compare (tot_serialize_nondep_then tot_serialize_raw_data_item tot_serialize_raw_data_item)) x1 x2
      else c
  )))
= 
  let v1 = Map len1 x1 in
  let v1' = synth_raw_data_item_recip v1 in
  let (| h1, c1 |) = v1' in
  let v2 = Map len2 x2 in
  let v2' = synth_raw_data_item_recip v2 in
  let (| h2, c2 |) = v2' in
  serialized_lex_compare_map_aux len1 x1 len2 x2;
  if len1 = len2
  then begin
    Classical.forall_intro (tot_nondep_then_eq_gen tot_parse_raw_data_item parse_raw_data_item tot_parse_raw_data_item parse_raw_data_item ());
    serialized_lex_compare_nlist (tot_serialize_nondep_then tot_serialize_raw_data_item tot_serialize_raw_data_item) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) (U64.v len1.value) c1 c2
  end
  else ()

#pop-options

#push-options "--z3rlimit 16"

let tot_serialized_lex_compare_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: tot_parser k1 t1)
  (s1: tot_serializer p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: tot_parser k2 t2)
  (s2: tot_serializer p2)
  (x1 x2: (t1 & t2))
: Lemma
  (requires (k1.parser_kind_subkind == Some ParserStrong))
  (ensures (
    (tot_serialized_lex_compare (tot_serialize_nondep_then s1 s2)) x1 x2 == (
      let c = tot_serialized_lex_compare s1 (fst x1) (fst x2) in
      if c = 0
      then tot_serialized_lex_compare s2 (snd x1) (snd x2)
      else c
  )))
=
  tot_serialize_nondep_then_eq s1 s2 x1;
  tot_serialize_nondep_then_eq s1 s2 x2;
  bytes_lex_compare_serialize_strong_prefix (serializer_of_tot_serializer s1) (fst x1) (fst x2) (bare_serialize s2 (snd x1)) (bare_serialize s2 (snd x2))

#pop-options

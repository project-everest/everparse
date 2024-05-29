module CBOR.Spec.Format
include CBOR.Spec.Type
open LowParse.Spec
open LowParse.Spec.BitSum
open LowParse.Spec.Recursive
open LowParse.Spec.SeqBytes
open LowParse.Spec.Assoc

(* RFC 8949

   NOTE: we are only supporting Deterministically Encoded CBOR (Section 4.2),
   which is a requirement of COSE anyway (RFC 8152, Section 14)
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
let destr_initial_byte : destr_bitsum'_t initial_byte_desc =
  norm [delta_attr [`%filter_bitsum'_t_attr]; iota; zeta; primops]
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
let initial_byte_wf (b: bitsum'_type initial_byte_desc) : Tot bool =
  match b with
  | (major_type, (additional_info, _)) ->
    (if major_type = cbor_major_type_simple_value then additional_info `U8.lte` additional_info_long_argument_8_bits else true) && // TODO: support floating-point numbers
    additional_info `U8.lt` additional_info_unassigned_min
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
= match b with
  | (major_type, (additional_info, _)) ->
    if additional_info = additional_info_long_argument_8_bits
    then 1sz
    else if additional_info = additional_info_long_argument_16_bits
    then 2sz
    else if additional_info = additional_info_long_argument_32_bits
    then 3sz
    else if additional_info = additional_info_long_argument_64_bits
    then 4sz
    else 0sz

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

[@@CMacro]
let min_deterministic_uint8 = 24uy

inline_for_extraction
let uint8_wf
  (x: U8.t)
: Tot bool
= min_deterministic_uint8 `U8.lte` x

[@@CMacro]
let min_deterministic_uint16 = 256us

inline_for_extraction
let uint16_wf
  (x: U16.t)
: Tot bool
= min_deterministic_uint16 `U16.lte` x

[@@CMacro]
let min_deterministic_uint32 = 65536ul

inline_for_extraction
let uint32_wf
  (x: U32.t)
: Tot bool
= min_deterministic_uint32 `U32.lte` x

[@@CMacro]
let min_deterministic_uint64 = 4294967296uL

inline_for_extraction
let uint64_wf
  (x: U64.t)
: Tot bool
= min_deterministic_uint64 `U64.lte` x

inline_for_extraction
let simple_value_long_argument_wf // 3.3: "an encoder MUST NOT issue two-byte sequences that start with 0xf8 and continue with a byte less than 0x20"
  (x: U8.t)
: Tot bool
= min_simple_value_long_argument `U8.lte` x

let long_argument_simple_value_prop
  (b: initial_byte)
: GTot prop
= let (major_type, (additional_info, _)) = b in
  additional_info == additional_info_long_argument_8_bits /\ major_type == cbor_major_type_simple_value

let long_argument_u8_prop
  (b: initial_byte)
: GTot prop
= let (major_type, (additional_info, _)) = b in
  additional_info == additional_info_long_argument_8_bits /\ ~ (major_type == cbor_major_type_simple_value)

let long_argument_u16_prop
  (b: initial_byte)
: GTot prop
= let (major_type, (additional_info, _)) = b in
  additional_info == additional_info_long_argument_16_bits

let long_argument_u32_prop
  (b: initial_byte)
: GTot prop
= let (major_type, (additional_info, _)) = b in
  additional_info == additional_info_long_argument_32_bits

let long_argument_u64_prop
  (b: initial_byte)
: GTot prop
= let (major_type, (additional_info, _)) = b in
  additional_info == additional_info_long_argument_64_bits

let long_argument_other_prop
  (b: initial_byte)
  (a: additional_info_t)
: GTot prop
= let (major_type, (additional_info, _)) = b in
  a == additional_info /\ (
    ~ (additional_info == additional_info_long_argument_8_bits \/ additional_info == additional_info_long_argument_16_bits \/ additional_info == additional_info_long_argument_32_bits \/ additional_info == additional_info_long_argument_64_bits)
  )

inline_for_extraction
noextract
type long_argument
  (b: initial_byte)
= | LongArgumentSimpleValue:
      (prf: squash (long_argument_simple_value_prop b)) ->
      (v: parse_filter_refine simple_value_long_argument_wf) ->
      long_argument b
  | LongArgumentU8:
      (prf: squash (long_argument_u8_prop b)) ->
      (v: parse_filter_refine uint8_wf) ->
      long_argument b
  | LongArgumentU16:
      (prf: squash (long_argument_u16_prop b)) ->
      (v: parse_filter_refine uint16_wf) ->
      long_argument b
  | LongArgumentU32:
      (prf: squash (long_argument_u32_prop b)) ->
      (v: parse_filter_refine uint32_wf) ->
      long_argument b
  | LongArgumentU64:
      (prf: squash (long_argument_u64_prop b)) ->
      (v: parse_filter_refine uint64_wf) ->
      long_argument b
  | LongArgumentOther:
      (a: additional_info_t) ->
      (prf: squash (long_argument_other_prop b a)) ->
      (v: unit) -> // constructors are synth functions, hence this unit argument
      long_argument b

let header = dtuple2 initial_byte long_argument

module Cast = FStar.Int.Cast

inline_for_extraction
let argument_as_uint64
  (b: initial_byte)
  (x: long_argument b)
: Tot U64.t
= match x with
  | LongArgumentSimpleValue _ v
  | LongArgumentU8 _ v ->
    Cast.uint8_to_uint64 v
  | LongArgumentU16 _ v ->
    Cast.uint16_to_uint64 v
  | LongArgumentU32 _ v ->
    Cast.uint32_to_uint64 v
  | LongArgumentU64 _ v ->
    v
  | LongArgumentOther v _ _ ->
    Cast.uint8_to_uint64 v

[@@CMacro]
let additional_info_simple_value_max : additional_info_t = 24uy

let get_header_argument_as_simple_value_initial_byte_precond
  (b: initial_byte)
: GTot bool
= 
  let (major_type, (additional_info, _)) = b in
  major_type = cbor_major_type_simple_value && additional_info `U8.lte` additional_info_simple_value_max

inline_for_extraction
let argument_as_simple_value
  (b: initial_byte)
  (x: long_argument b)
: Pure simple_value
    (requires (get_header_argument_as_simple_value_initial_byte_precond b))
    (ensures (fun _ -> True))
= match x with
  | LongArgumentOther v _ _
  | LongArgumentSimpleValue _ v ->
    v

(* Raw data items, disregarding ordering of map entries *)

let content
  (h: header)
: Tot Type
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string
      then Seq.lseq byte (U64.v (argument_as_uint64 b long_arg))
      else if major_type = cbor_major_type_array
      then nlist (U64.v (argument_as_uint64 b long_arg)) raw_data_item
      else if major_type = cbor_major_type_map
      then nlist (U64.v (argument_as_uint64 b long_arg)) (raw_data_item & raw_data_item)
      else if major_type = cbor_major_type_tagged
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
      if major_type = cbor_major_type_uint64 || major_type = cbor_major_type_neg_int64
      then Int64 major_type (argument_as_uint64 b long_arg)
      else if major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string
      then String major_type c
      else if major_type = cbor_major_type_array
      then Array c
      else if major_type = cbor_major_type_map
      then Map c
      else if major_type = cbor_major_type_tagged
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

#push-options "--z3rlimit 64"
#restart-solver
let synth_raw_data_item_injective : squash (synth_injective synth_raw_data_item) = ()
#pop-options

let parse_initial_byte : parser _ initial_byte =
  parse_filter (parse_bitsum' initial_byte_desc parse_u8) initial_byte_wf

noextract
let parse_long_argument_kind = strong_parser_kind 0 8 None

let parse_long_argument
  (b: initial_byte)
: Tot (parser parse_long_argument_kind (long_argument b))
= match b with
  | (major_type, (additional_info, _)) ->
    if additional_info = additional_info_long_argument_8_bits
    then
      if major_type = cbor_major_type_simple_value
      then weaken _ (parse_filter parse_u8 simple_value_long_argument_wf `parse_synth` LongArgumentSimpleValue ())
      else weaken _ (parse_filter parse_u8 uint8_wf `parse_synth` LongArgumentU8 ())
    else if additional_info = additional_info_long_argument_16_bits
    then weaken _ (parse_filter parse_u16 uint16_wf `parse_synth` LongArgumentU16 ())
    else if additional_info = additional_info_long_argument_32_bits
    then weaken _ (parse_filter parse_u32 uint32_wf `parse_synth` LongArgumentU32 ())
    else if additional_info = additional_info_long_argument_64_bits
    then weaken _ (parse_filter parse_u64 uint64_wf `parse_synth` LongArgumentU64 ())
    else weaken _ (parse_empty `parse_synth` LongArgumentOther additional_info ())

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
      if major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string
      then weaken _ (parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg)))
      else if major_type = cbor_major_type_array
      then weaken _ (parse_nlist (U64.v (argument_as_uint64 b long_arg)) p)
      else if major_type = cbor_major_type_map
      then weaken _ (parse_nlist (U64.v (argument_as_uint64 b long_arg)) (p `nondep_then` p))
      else if major_type = cbor_major_type_tagged
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
      let (| (major_type, _), _ |) = h in
      major_type == cbor_major_type_byte_string \/ major_type == cbor_major_type_text_string

inline_for_extraction
type leaf_content
  (h: header)
= | LeafContentSeq:
    (prf: squash (leaf_content_seq_cond h)) ->
    (v: Seq.lseq byte (U64.v (argument_as_uint64 (dfst h) (dsnd h)))) ->
    leaf_content h
  | LeafContentEmpty:
    (prf: squash (~ (leaf_content_seq_cond h))) ->
    (v: unit) ->
    leaf_content h

let parse_leaf_content
  (h: header)
: parser parse_content_kind (leaf_content h)
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string
      then weaken _ (parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg)) `parse_synth` LeafContentSeq ())
      else weaken _ (parse_empty `parse_synth` LeafContentEmpty ())

let leaf = dtuple2 header leaf_content

let parse_leaf : parser _ leaf = parse_header `parse_dtuple2` parse_leaf_content

let remaining_data_items
  (l: leaf)
: Tot nat
= match l with
  | (| (| b, long_arg |), _ |) ->
    match b with
    | (major_type, _) ->
      if major_type = cbor_major_type_array
      then
        U64.v (argument_as_uint64 b long_arg)
      else if major_type = cbor_major_type_map
      then
        let count = U64.v (argument_as_uint64 b long_arg) in
        count + count
      else if major_type = cbor_major_type_tagged
      then 1
      else 0

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
= match x with
  | [] -> []
  | (a, b) :: q -> a :: b :: list_of_pair_list t (nb_pairs - 1) q

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

#push-options "--z3rlimit 32"
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
    nondep_then_eq p p input;
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
        match b with
        | (major_type, _) ->
          if major_type = cbor_major_type_array
          then (| h, c |)
          else if major_type = cbor_major_type_map
          then (| h, pair_list_of_list _ (U64.v (argument_as_uint64 b long_arg)) c |)
          else if major_type = cbor_major_type_tagged
          then (| h, List.Tot.hd c |)
          else if major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string
          then (| h, LeafContentSeq?.v lc |)
          else (| h, () |)

#push-options "--ifuel 3"
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
  parse_header = parse_leaf;
  count = remaining_data_items;
  synth_ = synth_raw_data_item_from_alt;
  synth_inj = synth_raw_data_item_from_alt_injective;
}

let parse_raw_data_item : parser parse_raw_data_item_kind raw_data_item =
  parse_recursive parse_raw_data_item_param

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

#push-options "--z3rlimit 128 --ifuel 8"
#restart-solver

let parse_raw_data_item_eq
  (b: bytes)
: Lemma
  (parse parse_raw_data_item b == parse (parse_raw_data_item_aux parse_raw_data_item) b)
=
  parse_recursive_eq parse_raw_data_item_param b;
  parse_synth_eq (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item b;
  parse_dtuple2_eq parse_header (parse_content parse_raw_data_item) b;
  parse_synth_eq (parse_recursive_alt parse_raw_data_item_param parse_raw_data_item) synth_raw_data_item_from_alt b;
  parse_dtuple2_eq parse_leaf (parse_recursive_payload parse_raw_data_item_param parse_raw_data_item) b;
  parse_dtuple2_eq parse_header parse_leaf_content b;
  match parse parse_header b with
  | None -> ()
  | Some _ ->
    Classical.forall_intro (parse_nlist_zero parse_raw_data_item);
    Classical.forall_intro (parse_nlist_one parse_raw_data_item);
    let prf_seq
      (h: header)
      (prf: squash (leaf_content_seq_cond h))
      (b: bytes)
    : Lemma
      (parse_synth (parse_lseq_bytes (U64.v (argument_as_uint64 (dfst h) (dsnd h)))) (LeafContentSeq #h prf) b == parse_synth' (parse_lseq_bytes (U64.v (argument_as_uint64 (dfst h) (dsnd h)))) (LeafContentSeq #h prf) b)
    = parse_synth_eq (parse_lseq_bytes (U64.v (argument_as_uint64 (dfst h) (dsnd h)))) (LeafContentSeq #h prf) b
    in
    Classical.forall_intro_3 prf_seq;
    let prf_empty
      (h: header)
      (prf: squash (~ (leaf_content_seq_cond h)))
      (b: bytes)
    : Lemma
      (parse_synth parse_empty (LeafContentEmpty #h prf) b == parse_synth' parse_empty (LeafContentEmpty #h prf) b)
    = parse_synth_eq parse_empty (LeafContentEmpty #h prf) b
    in
    Classical.forall_intro_3 prf_empty;
    Classical.forall_intro_2 (parse_pair_list_as_list parse_raw_data_item)

#pop-options

(* Serialization *)

let _ : squash (major_type_t == bitfield uint8 3) =
  assert_norm (major_type_t == bitfield_refine 8 U8.v 3);
  uint8_v_eq_fn ()

inline_for_extraction
let mk_initial_byte
  (t: major_type_t)
  (x: additional_info_t)
: Pure initial_byte
    (requires (initial_byte_wf (t, (x, ()))))
    (ensures (fun _ -> True))
= (t, (x, ()))


[@@CMacro]
let min_deterministic_uint8_as_uint64 = 24uL

[@@CMacro]
let min_deterministic_uint16_as_uint64 = 256uL

[@@CMacro]
let min_deterministic_uint32_as_uint64 = 65536uL

#push-options "--z3rlimit 16"

#restart-solver
let uint64_as_argument
  (t: major_type_t)
  (x: U64.t)
: Pure header
    (requires (t `U8.lt` cbor_major_type_simple_value))
    (ensures (fun y ->
      let (| b, arg |) = y in
      let (major_type', _) = b in
      t == major_type' /\
      argument_as_uint64 b arg = x
    ))
= if x `U64.lt` min_deterministic_uint8_as_uint64
  then (| mk_initial_byte t (Cast.uint64_to_uint8 x), LongArgumentOther (Cast.uint64_to_uint8 x) () () |)
  else if x `U64.lt` min_deterministic_uint16_as_uint64
  then (| mk_initial_byte t additional_info_long_argument_8_bits, LongArgumentU8 () (Cast.uint64_to_uint8 x) |)
  else if x `U64.lt` min_deterministic_uint32_as_uint64
  then (| mk_initial_byte t additional_info_long_argument_16_bits, LongArgumentU16 () (Cast.uint64_to_uint16 x) |)
  else if x `U64.lt` min_deterministic_uint64
  then (| mk_initial_byte t additional_info_long_argument_32_bits, LongArgumentU32 () (Cast.uint64_to_uint32 x) |)
  else (| mk_initial_byte t additional_info_long_argument_64_bits, LongArgumentU64 () x |)

#pop-options

let simple_value_as_argument
  (x: simple_value)
: Pure header
    (requires True)
    (ensures (fun y ->
      let (| b, arg |) = y in
      let (major_type, (additional_info, _)) = b in
      major_type = cbor_major_type_simple_value /\
      additional_info `U8.lte` additional_info_long_argument_8_bits /\
      argument_as_simple_value b arg == x
    ))
= if x `U8.lte` max_simple_value_additional_info
  then (| mk_initial_byte cbor_major_type_simple_value x, LongArgumentOther x () () |)
  else (| mk_initial_byte cbor_major_type_simple_value additional_info_long_argument_8_bits, LongArgumentSimpleValue () x |)

let serialize_initial_byte : serializer parse_initial_byte =
  serialize_filter
    (serialize_bitsum'
      initial_byte_desc
      serialize_u8
    )
    initial_byte_wf

let serialize_long_argument
  (b: initial_byte)
: Tot (serializer (parse_long_argument b))
= match b with
  | (major_type, (additional_info, _)) ->
    if additional_info = additional_info_long_argument_8_bits
    then
      if major_type = cbor_major_type_simple_value
      then
        serialize_weaken _ (serialize_synth _ (LongArgumentSimpleValue ()) (serialize_filter serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v ())
      else serialize_weaken _ (serialize_synth _ (LongArgumentU8 ()) (serialize_filter serialize_u8 uint8_wf) LongArgumentU8?.v ())
    else if additional_info = additional_info_long_argument_16_bits
    then serialize_weaken _ (serialize_synth _ (LongArgumentU16 ()) (serialize_filter serialize_u16 uint16_wf) LongArgumentU16?.v ())
    else if additional_info = additional_info_long_argument_32_bits
    then serialize_weaken _ (serialize_synth _ (LongArgumentU32 ()) (serialize_filter serialize_u32 uint32_wf) LongArgumentU32?.v ())
    else if additional_info = additional_info_long_argument_64_bits
    then serialize_weaken _ (serialize_synth _ (LongArgumentU64 ()) (serialize_filter serialize_u64 uint64_wf) LongArgumentU64?.v ())
    else serialize_weaken _ (serialize_synth _ (LongArgumentOther additional_info ()) serialize_empty LongArgumentOther?.v ())

let serialize_header : serializer parse_header =
  serialize_dtuple2 serialize_initial_byte serialize_long_argument

let synth_raw_data_item_recip
  (x: raw_data_item)
: Tot raw_data_item'
= match x with
  | Simple v ->
    (| simple_value_as_argument v, () |)
  | Int64 m v ->
    (| uint64_as_argument m v, () |)
  | String m v ->
    let len = U64.uint_to_t (Seq.length v) in
    (| uint64_as_argument m len, v |)
  | Array v ->
    let len = U64.uint_to_t (List.Tot.length v) in
    (| uint64_as_argument cbor_major_type_array len, v |)
  | Map v ->
    let len = U64.uint_to_t (List.Tot.length v) in
    (| uint64_as_argument cbor_major_type_map len, v |)
  | Tagged tag v ->
    (| uint64_as_argument cbor_major_type_tagged tag, v |)

#push-options "--z3rlimit 16"

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
      match b with
      | (major_type, _) ->
        if major_type = cbor_major_type_array
        then (| (| h, LeafContentEmpty () () |), c |)
        else if major_type = cbor_major_type_map
        then (| (| h, LeafContentEmpty () () |), list_of_pair_list _ (U64.v (argument_as_uint64 b long_arg)) c |)
        else if major_type = cbor_major_type_tagged
        then (| (| h, LeafContentEmpty () () |), [c] |)
        else if major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string
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

let serialize_leaf_content
  (h: header)
: Tot (serializer (parse_leaf_content h))
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string
      then serialize_weaken _ (serialize_synth _ (LeafContentSeq ()) (serialize_lseq_bytes (U64.v (argument_as_uint64 b long_arg))) LeafContentSeq?.v ())
      else serialize_weaken _ (serialize_synth _ (LeafContentEmpty ()) serialize_empty LeafContentEmpty?.v ())

let serialize_leaf : serializer parse_leaf =
  serialize_dtuple2 serialize_header serialize_leaf_content

(* Construction of the serializer, by "step indexing" over the "level"
   (in fact the depth) of the raw data item. *)

open LowParse.WellFounded

let rec level
  (d: raw_data_item)
: Tot nat
= match d with
  | Array v ->
    let v : list raw_data_item = v in
    1 + fold_left_list v (acc_level v level) 0
  | Map v ->
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
  | Array l ->
    let l : list raw_data_item = l in
    assert_norm (level x == 1 + fold_left_list l (acc_level l level) 0);
    fold_left_list_has_level_gen level (n - 1) l 0;
    assert (list_has_pred_level level n (dsnd (synth_raw_data_item_from_alt_recip x)))
  | Map l ->
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
  serialize_header = serialize_leaf;
  synth_recip = synth_raw_data_item_from_alt_recip;
  synth_inv = synth_raw_data_item_from_alt_inverse;
  level = level;
  level_correct = synth_raw_data_item_from_alt_recip_list_has_pred_level;
}

let serialize_raw_data_item : serializer parse_raw_data_item =
  serialize_recursive serialize_raw_data_item_param

(* Serialization equations to prove the functional correctness of implementations *)

let serialize_content
  (h: header)
: Tot (serializer (parse_content parse_raw_data_item h))
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string
      then serialize_weaken _ (serialize_lseq_bytes (U64.v (argument_as_uint64 b long_arg)))
      else if major_type = cbor_major_type_array
      then serialize_weaken _ (serialize_nlist (U64.v (argument_as_uint64 b long_arg)) serialize_raw_data_item)
      else if major_type = cbor_major_type_map
      then serialize_weaken _ (serialize_nlist (U64.v (argument_as_uint64 b long_arg)) (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item))
      else if major_type = cbor_major_type_tagged
      then serialize_weaken _ serialize_raw_data_item
      else serialize_weaken _ serialize_empty

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
  (serialize serialize_raw_data_item x == serialize serialize_raw_data_item_aux x)
= Classical.forall_intro parse_raw_data_item_eq;
  let s' = serialize_ext parse_raw_data_item serialize_raw_data_item (parse_raw_data_item_aux parse_raw_data_item) in
  serializer_unique (parse_raw_data_item_aux parse_raw_data_item) serialize_raw_data_item_aux s' x

// Some lemmas about the initial byte

let get_major_type_synth_raw_data_item
  (x: raw_data_item')
: Lemma
  (get_major_type (synth_raw_data_item x) == (match x with (| (| (major_type, _), _ |), _ |) -> major_type))
  [SMTPat (synth_raw_data_item x)]
= assert_norm (pow2 3 == 8)

let get_raw_data_item_header
  (x: raw_data_item)
: GTot header
= dfst (synth_raw_data_item_recip x)

noextract
let get_header_major_type
  (h: header)
: Tot major_type_t
= let (| (major_type, _), _ |) = h in
  major_type

noextract
let get_header_argument_as_uint64
  (h: header)
: Tot UInt64.t
= let (| b, l |) = h in
  argument_as_uint64 b l

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
    (fun _then -> k (| mk_initial_byte cbor_major_type_simple_value x, LongArgumentOther x () () |))
    (fun _else -> k (| mk_initial_byte cbor_major_type_simple_value additional_info_long_argument_8_bits, LongArgumentSimpleValue () x |))

inline_for_extraction
noextract
let cps_uint64_as_argument
  (t': Type)
  (t'_ifthenelse: if_combinator_weak t')
  (ty: major_type_t { ty `U8.lt` cbor_major_type_simple_value })
  (x: U64.t)
  (k: (h: header) -> Pure t'
    (requires (h == uint64_as_argument ty x))
    (ensures (fun _ -> True))
  )
: Tot t'
= t'_ifthenelse (x `U64.lt` min_deterministic_uint8_as_uint64)
    (fun _ -> k (| mk_initial_byte ty (Cast.uint64_to_uint8 x), LongArgumentOther (Cast.uint64_to_uint8 x) () () |))
    (fun _ -> t'_ifthenelse (x `U64.lt` min_deterministic_uint16_as_uint64)
      (fun _ -> k (| mk_initial_byte ty additional_info_long_argument_8_bits, LongArgumentU8 () (Cast.uint64_to_uint8 x) |))
      (fun _ -> t'_ifthenelse (x `U64.lt` min_deterministic_uint32_as_uint64)
        (fun _ -> k (| mk_initial_byte ty additional_info_long_argument_16_bits, LongArgumentU16 () (Cast.uint64_to_uint16 x) |))
        (fun _ -> t'_ifthenelse (x `U64.lt` min_deterministic_uint64)
          (fun _ -> k (| mk_initial_byte ty additional_info_long_argument_32_bits, LongArgumentU32 () (Cast.uint64_to_uint32 x) |))
          (fun _ -> k (| mk_initial_byte ty additional_info_long_argument_64_bits, LongArgumentU64 () x |))
        )
      )
    )


let get_uint64_as_initial_byte
  (ty: major_type_t { ty `U8.lt` cbor_major_type_simple_value })
  (x: U64.t)
: Tot U8.t
= cps_uint64_as_argument
    U8.t
    (fun cond iftrue iffalse -> if cond then iftrue () else iffalse ())
    ty
    x
    (fun h -> match h with (| b, _ |) -> mk_synth_initial_byte b)

let get_initial_byte_header_correct
  (h: header)
: Lemma
  (mk_synth_initial_byte (dfst h) == Seq.index (serialize serialize_header h) 0)
= serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h;
  let (| b, _ |) = h in
  serialize_bitsum'_eq
    initial_byte_desc
    serialize_u8
    b;
  serialize_u8_spec (synth_bitsum'_recip initial_byte_desc b)

let get_initial_byte_header_inj
  (h1 h2: header)
: Lemma
  (requires (Seq.index (serialize serialize_header h1) 0 == Seq.index (serialize serialize_header h2) 0))
  (ensures (dfst h1 == dfst h2))
=
  let (| b1, l1 |) = h1 in
  let (| b2, l2 |) = h2 in
  let b1' = synth_bitsum'_recip initial_byte_desc b1 in
  let b2' = synth_bitsum'_recip initial_byte_desc b2 in
  get_initial_byte_header_correct h1;
  get_initial_byte_header_correct h2;
  assert (synth_bitsum' initial_byte_desc b1' == b1);
  assert (synth_bitsum' initial_byte_desc b2' == b2)

let get_uint64_as_initial_byte_header_correct
  (ty: major_type_t { ty `U8.lt` cbor_major_type_simple_value })
  (x: U64.t)
: Lemma
  (get_uint64_as_initial_byte ty x == Seq.index (serialize serialize_header (uint64_as_argument ty x)) 0)
= let h = uint64_as_argument ty x in
  get_initial_byte_header_correct h

let get_major_type_synth_raw_data_item_recip
  (x: raw_data_item)
: Lemma
  (get_major_type x == get_header_major_type (dfst (synth_raw_data_item_recip x)))
= ()

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

#push-options "--z3rlimit 16"

#restart-solver
let holds_on_raw_data_item_eq_recursive
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (holds_on_raw_data_item p x == (p x && List.Tot.for_all (holds_on_raw_data_item p) (get_children serialize_raw_data_item_param x)))
= holds_on_raw_data_item_eq p x;
  match x with
  | Map l ->
    let l : list (raw_data_item & raw_data_item) = l in
    list_for_all_holds_on_pair_list_of_pair_list (holds_on_raw_data_item p) l
  | _ -> ()

#pop-options

let holds_on_raw_data_item_pred (p: (raw_data_item -> bool)) : pred_recursive_t serialize_raw_data_item_param = {
  base = p;
  pred = holds_on_raw_data_item p;
  prf = holds_on_raw_data_item_eq_recursive p;
}

let data_item_eq
  (order: (raw_data_item -> raw_data_item -> bool))
: Lemma
  (data_item order == parse_filter_refine (data_item_wf order))
  [SMTPat (data_item order)]
= assert_norm (data_item order == parse_filter_refine (data_item_wf order))

let map_entry_order_eq
  (#key: Type)
  (key_order: (key -> key -> bool))
  (value: Type)
: Lemma
  (CBOR.Spec.Type.map_entry_order key_order value == LowParse.Spec.Assoc.map_entry_order key_order value)
  [SMTPat (CBOR.Spec.Type.map_entry_order key_order value)]
= assert_norm (CBOR.Spec.Type.map_entry_order key_order value == LowParse.Spec.Assoc.map_entry_order key_order value)

let parse_data_item
  (order: (raw_data_item -> raw_data_item -> bool))
: Tot (parser parse_raw_data_item_kind (data_item order))
= parse_raw_data_item `parse_filter` data_item_wf order

let serialize_data_item
  (order: (raw_data_item -> raw_data_item -> bool))
: Tot (serializer (parse_data_item order))
= serialize_raw_data_item `serialize_filter` data_item_wf order

let data_item_wf_eq
  (order: (raw_data_item -> raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (data_item_wf order x == (data_item_wf_head order x && List.Tot.for_all (data_item_wf order) (get_children serialize_raw_data_item_param x)))
= holds_on_raw_data_item_eq_recursive (data_item_wf_head order) x

let data_item_wf_pred (order: (raw_data_item -> raw_data_item -> bool)) : pred_recursive_t serialize_raw_data_item_param =
  holds_on_raw_data_item_pred (data_item_wf_head order)

(* 4.2.1 Deterministically encoded CBOR: The keys in every map MUST be sorted in the bytewise lexicographic order of their deterministic encodings. *)

let serialized_lex_order
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x1 x2: t)
: GTot bool
= LowParse.Spec.SeqBytes.bytes_lex_order (serialize s x1) (serialize s x2)

let deterministically_encoded_cbor_map_key_order'
  (k1 k2: raw_data_item)
: GTot bool
= serialized_lex_order serialize_raw_data_item k1 k2

let deterministically_encoded_cbor_map_key_order : Ghost.erased (raw_data_item -> raw_data_item -> bool) = Ghost.hide (FStar.Ghost.Pull.pull (fun x -> FStar.Ghost.Pull.pull (deterministically_encoded_cbor_map_key_order' x)))

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
= Classical.move_requires (serializer_injective _ serialize_raw_data_item x) y;
  LowParse.Spec.SeqBytes.bytes_lex_order_total (serialize_raw_data_item x) (serialize_raw_data_item y)

let deterministically_encoded_cbor_map_key_order_assoc_ext :
  (m1: list (raw_data_item & raw_data_item)) ->
  (m2: list (raw_data_item & raw_data_item)) ->
  (ext: (
    (k: raw_data_item) ->
    Lemma
    (list_ghost_assoc k m1 == list_ghost_assoc k m2)
  )) ->
  Lemma
  (requires (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m1 /\ List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m2))
  (ensures (m1 == m2))
= map_entry_order_assoc_ext deterministically_encoded_cbor_map_key_order deterministically_encoded_cbor_map_key_order_irrefl deterministically_encoded_cbor_map_key_order_trans deterministically_encoded_cbor_map_key_order_total

(* 4.2.3 Length-First Map Key Ordering (a.k.a. "Canonical CBOR", RFC 7049 Section 3.9) *)

let canonical_cbor_map_key_order'
  (k1 k2: raw_data_item)
: GTot bool
= LowParse.Spec.SeqBytes.bytes_length_first_lex_order (serialize_raw_data_item k1) (serialize_raw_data_item k2)

let canonical_cbor_map_key_order : Ghost.erased (raw_data_item -> raw_data_item -> bool) = Ghost.hide (FStar.Ghost.Pull.pull (fun x -> FStar.Ghost.Pull.pull (canonical_cbor_map_key_order' x)))

let canonical_cbor_map_key_order_irrefl
  (x y: raw_data_item)
: Lemma
  (requires (Ghost.reveal canonical_cbor_map_key_order x y))
  (ensures (~ (x == y)))
= LowParse.Spec.SeqBytes.bytes_length_first_lex_order_irrefl (serialize_raw_data_item x) (serialize_raw_data_item y)

let canonical_cbor_map_key_order_trans
  (x y z: raw_data_item)
: Lemma
  (requires (Ghost.reveal canonical_cbor_map_key_order x y /\ Ghost.reveal canonical_cbor_map_key_order y z))
  (ensures (Ghost.reveal canonical_cbor_map_key_order x z))
= LowParse.Spec.SeqBytes.bytes_length_first_lex_order_trans (serialize_raw_data_item x) (serialize_raw_data_item y) (serialize_raw_data_item z)

let canonical_cbor_map_key_order_total
  (x y: raw_data_item)
: Lemma
  (ensures (x == y \/ Ghost.reveal canonical_cbor_map_key_order x y \/ Ghost.reveal canonical_cbor_map_key_order y x))
= Classical.move_requires (serializer_injective _ serialize_raw_data_item x) y;
  LowParse.Spec.SeqBytes.bytes_length_first_lex_order_total (serialize_raw_data_item x) (serialize_raw_data_item y)

let canonical_cbor_map_key_order_assoc_ext :
  (m1: list (raw_data_item & raw_data_item)) ->
  (m2: list (raw_data_item & raw_data_item)) ->
  (ext: (
    (k: raw_data_item) ->
    Lemma
    (list_ghost_assoc k m1 == list_ghost_assoc k m2)
  )) ->
  Lemma
  (requires (List.Tot.sorted (map_entry_order canonical_cbor_map_key_order _) m1 /\ List.Tot.sorted (map_entry_order canonical_cbor_map_key_order _) m2))
  (ensures (m1 == m2))
= map_entry_order_assoc_ext canonical_cbor_map_key_order canonical_cbor_map_key_order_irrefl canonical_cbor_map_key_order_trans canonical_cbor_map_key_order_total

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
      (serialize serialize_initial_byte b1)
      (serialize serialize_initial_byte b2)
    == (
      let (ty1, (info1, ())) = b1 in
      let (ty2, (info2, ())) = b2 in
      let ty_compare = byte_compare ty1 ty2 in
      if ty_compare = 0
      then byte_compare info1 info2
      else ty_compare
  )))
= serialize_bitsum'_eq
    initial_byte_desc
    serialize_u8
    b1;
  serialize_bitsum'_eq
    initial_byte_desc
    serialize_u8
    b2;
  let b1' = synth_bitsum'_recip initial_byte_desc b1 in
  let b2' = synth_bitsum'_recip initial_byte_desc b2 in
  serialize_u8_spec' b1';
  serialize_u8_spec' b2';
  seq_to_list_length_one (serialize serialize_initial_byte b1);
  seq_to_list_length_one (serialize serialize_initial_byte b2);  
  assert (bytes_lex_compare
      (serialize serialize_initial_byte b1)
      (serialize serialize_initial_byte b2) == byte_compare b1' b2'
  );
  let (ty1, (info1, ())) = b1 in
  let (ty2, (info2, ())) = b2 in
  assert (synth_bitsum' initial_byte_desc b1' == b1);
  assert (synth_bitsum' initial_byte_desc b2' == b2);
  assert (U8.v ty1 == get_bitfield (U8.v b1') 5 8);
  assert (U8.v info1 == get_bitfield (U8.v b1') 0 5);
  get_bitfield_eq (U8.v b1') 5 8;
  get_bitfield_eq (U8.v b1') 0 5;
  assert (U8.v ty2 == get_bitfield (U8.v b2') 5 8);
  assert (U8.v info2 == get_bitfield (U8.v b2') 0 5);
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
      (serialize serialize_initial_byte b1)
      (serialize serialize_initial_byte b2)
    == (
      let (ty1, (info1, ())) = b1 in
      let (ty2, (info2, ())) = b2 in
      (ty1 `U8.lt` ty2) ||
        ((ty1 = ty2) && (info1 `U8.lt` info2))
  )))
= serialize_initial_byte_compare b1 b2

#pop-options

let serialized_lex_compare'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x1 x2: t)
: GTot int
= LowParse.Spec.SeqBytes.bytes_lex_compare (serialize s x1) (serialize s x2)

let serialized_lex_compare1
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x1: t)
: GTot (t -> int)
= FStar.Ghost.Pull.pull (serialized_lex_compare' s x1)

let serialized_lex_compare
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: GTot (t -> t -> int)
= FStar.Ghost.Pull.pull (serialized_lex_compare1 s)

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
    serialize s l1 == pre `Seq.append` mid1 /\
    serialize s l2 == pre `Seq.append` mid2 /\
    Seq.length mid1 <= Seq.length mid2
  ))
  (ensures (
    bytes_lex_compare (serialize s l1 `Seq.append` suff1) (serialize s l2 `Seq.append` suff2) == (
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
    Seq.append_empty_r (serialize s l2);
    serialize_strong_prefix s l2 l1 Seq.empty mid2;
    bytes_lex_compare_prefix (serialize s l1) suff1 suff2
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
    serialize s l1 == pre `Seq.append` mid1 /\
    serialize s l2 == pre `Seq.append` mid2
  ))
  (ensures (
    bytes_lex_compare (serialize s l1 `Seq.append` suff1) (serialize s l2 `Seq.append` suff2) == (
      let comp = bytes_lex_compare mid1 mid2 in
      if comp = 0
      then bytes_lex_compare suff1 suff2
      else comp
  )))
= if Seq.length mid1 <= Seq.length mid2
  then bytes_lex_compare_serialize_strong_prefix1 s l1 l2 suff1 suff2 pre mid1 mid2
  else begin
    lex_compare_oppose byte_compare (Seq.seq_to_list (serialize s l1 `Seq.append` suff1)) (Seq.seq_to_list (serialize s l2 `Seq.append` suff2));
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
    bytes_lex_compare (serialize s l1 `Seq.append` suff1) (serialize s l2 `Seq.append` suff2) == (
      let comp = bytes_lex_compare (serialize s l1) (serialize s l2) in
      if comp = 0
      then bytes_lex_compare suff1 suff2
      else comp
  )))
= let s1 = serialize s l1 in
  let s2 = serialize s l2 in
  Seq.append_empty_l s1;
  Seq.append_empty_l s2;
  bytes_lex_compare_serialize_strong_prefix0 s l1 l2 suff1 suff2 Seq.empty s1 s2

#push-options "--z3rlimit 32"
#restart-solver

let serialized_lex_compare_major_type_intro
  (v1 v2: raw_data_item)
: Lemma
  (requires (
    byte_compare (get_major_type v1) (get_major_type v2) <> 0
  ))
  (ensures (
    serialized_lex_compare serialize_raw_data_item v1 v2 ==
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
  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h1;
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
  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h2;
  let (| b2, l2 |) = h2 in
  serialize_initial_byte_compare b1 b2;
  Seq.append_assoc (serialize serialize_initial_byte b1) (serialize (serialize_long_argument b1) l1) (serialize (serialize_content h1) c1);
  Seq.append_assoc (serialize serialize_initial_byte b2) (serialize (serialize_long_argument b2) l2) (serialize (serialize_content h2) c2);
  bytes_lex_compare_serialize_strong_prefix serialize_initial_byte b1 b2 (serialize (serialize_long_argument b1) l1 `Seq.append` serialize (serialize_content h1) c1) (serialize (serialize_long_argument b2) l2 `Seq.append` serialize (serialize_content h2) c2)

let deterministically_encoded_cbor_map_key_order_major_type_intro
  (v1 v2: raw_data_item)
: Lemma
  (requires (
    U8.v (get_major_type v1) < U8.v (get_major_type v2)
  ))
  (ensures (
    Ghost.reveal deterministically_encoded_cbor_map_key_order v1 v2 == true
  ))
= serialized_lex_compare_major_type_intro v1 v2

let bytes_lex_compare_refl
  (x: bytes)
: Lemma
  (bytes_lex_compare x x == 0)
  [SMTPat (bytes_lex_compare x x)]
= Seq.append_empty_r x;
  bytes_lex_compare_prefix x Seq.empty Seq.empty

let serialized_lex_compare_simple_value
  (x1 x2: simple_value)
: Lemma
  (ensures (
    serialized_lex_compare serialize_raw_data_item (Simple x1) (Simple x2) ==
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
  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h1;
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
  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h2;
  let (| b2, l2 |) = h2 in
  serialize_initial_byte_compare b1 b2;
  Seq.append_assoc (serialize serialize_initial_byte b1) (serialize (serialize_long_argument b1) l1) (serialize (serialize_content h1) c1);
  Seq.append_assoc (serialize serialize_initial_byte b2) (serialize (serialize_long_argument b2) l2) (serialize (serialize_content h2) c2);
  bytes_lex_compare_serialize_strong_prefix serialize_initial_byte b1 b2 (serialize (serialize_long_argument b1) l1 `Seq.append` serialize (serialize_content h1) c1) (serialize (serialize_long_argument b2) l2 `Seq.append` serialize (serialize_content h2) c2);
  seq_to_list_length_one (serialize serialize_initial_byte b1);
  seq_to_list_length_one (serialize serialize_initial_byte b2);
  seq_to_list_append (serialize (serialize_long_argument b1) l1) (serialize (serialize_content h1) c1);
  seq_to_list_append (serialize (serialize_long_argument b2) l2) (serialize (serialize_content h2) c2);
  let (ty1, (info1, ())) = b1 in
  let (ty2, (info2, ())) = b2 in
  if (x1 `U8.lte` max_simple_value_additional_info || x2 `U8.lte` max_simple_value_additional_info)
  then ()
  else begin
    assert (b1 == b2);
    assert (b1 == (cbor_major_type_simple_value, (additional_info_long_argument_8_bits, ())));
    let LongArgumentSimpleValue _ x1' = l1 in
    assert (x1 == x1');
    let p1' : parser parse_long_argument_kind (long_argument b1) = LowParse.Spec.Base.weaken parse_long_argument_kind (parse_synth (parse_filter parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b1 ())) in
    assert (parse_long_argument b1 == p1');
    let s1_pre = serialize_synth #_ #_ #(long_argument b1) _ (LongArgumentSimpleValue #b1 ()) (serialize_filter serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v () in
    let s1' : serializer p1' = serialize_weaken parse_long_argument_kind s1_pre in
    serializer_unique (parse_long_argument b1) (serialize_long_argument b1) s1' l1;
    serialize_u8_spec x1;
    serialize_synth_eq #_ #_ #(long_argument b1) (parse_filter parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b1 ()) (serialize_filter serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v () l1;
    assert (serialize s1_pre l1 == serialize (serialize_filter serialize_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue?.v l1));
    assert (serialize s1' l1 == serialize (serialize_filter serialize_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue?.v l1));
    assert (serialize s1' l1 == Seq.create 1 x1');
    seq_to_list_length_one (serialize s1' l1);
    assert (serialize (serialize_long_argument b1) l1 == Seq.create 1 (x1 <: U8.t));
    seq_to_list_length_one (serialize (serialize_long_argument b1) l1);
    assert (b2 == (cbor_major_type_simple_value, (additional_info_long_argument_8_bits, ())));
    let LongArgumentSimpleValue _ x2' = l2 in
    assert (x2 == x2');
    let p2' : parser parse_long_argument_kind (long_argument b2) = LowParse.Spec.Base.weaken parse_long_argument_kind (parse_synth (parse_filter parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b2 ())) in
    assert (parse_long_argument b2 == p2');
    let s2_pre = serialize_synth #_ #_ #(long_argument b2) _ (LongArgumentSimpleValue #b2 ()) (serialize_filter serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v () in
    let s2' : serializer p2' = serialize_weaken parse_long_argument_kind s2_pre in
    serializer_unique (parse_long_argument b2) (serialize_long_argument b2) s2' l2;
    serialize_u8_spec x2;
    serialize_synth_eq #_ #_ #(long_argument b2) (parse_filter parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b2 ()) (serialize_filter serialize_u8 simple_value_long_argument_wf) LongArgumentSimpleValue?.v () l2;
    assert (serialize s2_pre l2 == serialize (serialize_filter serialize_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue?.v l2));
    assert (serialize s2' l2 == serialize (serialize_filter serialize_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue?.v l2));
    assert (serialize s2' l2 == Seq.create 1 x2');
    seq_to_list_length_one (serialize s2' l2);
    assert (serialize (serialize_long_argument b2) l2 == Seq.create 1 (x2 <: U8.t));
    seq_to_list_length_one (serialize (serialize_long_argument b2) l2);
    bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (serialize (serialize_content h1) c1) (serialize (serialize_content h2) c2)
  end

let deterministically_encoded_cbor_map_key_order_simple_value_correct
  (x1 x2: simple_value)
: Lemma
  (ensures (Ghost.reveal deterministically_encoded_cbor_map_key_order (Simple x1) (Simple x2) == x1 `U8.lt` x2))
= serialized_lex_compare_simple_value x1 x2

#pop-options

#restart-solver
let lex_compare_with_header_long_argument
  (ty1: major_type_t { ty1 `U8.lt` cbor_major_type_simple_value })
  (x1: U64.t)
  (ty2: major_type_t { ty2 `U8.lt` cbor_major_type_simple_value })
  (x2: U64.t)
: Lemma
  (requires (
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2
  ))
  (ensures (
    let h1 = uint64_as_argument ty1 x1 in
    let (| b1, l1 |) = h1 in
    let h2 = uint64_as_argument ty2 x2 in
    let (| b2, l2 |) = h2 in
    ty1 == ty2 /\
    b1 == b2 /\
    (bytes_lex_compare (serialize serialize_header h1) (serialize serialize_header h2) ==
      bytes_lex_compare (serialize (serialize_long_argument b1) l1) (serialize (serialize_long_argument b2) l2))
  ))
=
  let h1 = uint64_as_argument ty1 x1 in
  let h2 = uint64_as_argument ty2 x2 in
  get_uint64_as_initial_byte_header_correct ty1 x1;
  get_uint64_as_initial_byte_header_correct ty2 x2;
  get_initial_byte_header_inj h1 h2;
  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h1;
  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h2;
  let (| b1, l1 |) = h1 in
  let (| _, l2 |) = h2 in
  bytes_lex_compare_prefix (serialize serialize_initial_byte b1) (serialize (serialize_long_argument b1) l1) (serialize (serialize_long_argument b1) l2)

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

#restart-solver
let lex_compare_with_header_uint
  (ty1: major_type_t { ty1 `U8.lt` cbor_major_type_simple_value })
  (x1: U64.t)
  (ty2: major_type_t { ty2 `U8.lt` cbor_major_type_simple_value })
  (x2: U64.t)
  (b1: initial_byte)
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (phi: (t -> GTot bool))
  (f: (parse_filter_refine phi -> GTot (long_argument b1)) { synth_injective f })
  (g: (long_argument b1 -> GTot (parse_filter_refine phi)) { synth_inverse f g })
  (s: serializer p)
  (n: nat)
  (uv: (t -> FStar.UInt.uint_t (8 `op_Multiply` n)))
  (s_spec: (
    (x: t) ->
    Lemma
    (serialize s x == FStar.Endianness.n_to_be n (uv x))
  ))
  (uv_spec: (
    (x: U64.t) ->
    Lemma
    (requires (
      dfst (uint64_as_argument ty1 x) == b1
    ))
    (ensures (
      uv (g (dsnd (uint64_as_argument ty1 x))) == U64.v x
    ))
  ))
: Lemma
  (requires (
    let h1 = uint64_as_argument ty1 x1 in
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2 /\
    dfst h1 == b1 /\
    parse_filter_kind parse_long_argument_kind `is_weaker_than` k /\
    parse_long_argument b1 == LowParse.Spec.Base.weaken parse_long_argument_kind (parse_synth (parse_filter p phi) f)
  ))
  (ensures (
    ty1 == ty2 /\
    bytes_lex_compare (serialize serialize_header (uint64_as_argument ty1 x1)) (serialize serialize_header (uint64_as_argument ty2 x2)) == int_compare (U64.v x1) (U64.v x2)
  ))
= lex_compare_with_header_long_argument ty1 x1 ty2 x2;
  uv_spec x1;
  uv_spec x2;
  let (| _, l1 |) = uint64_as_argument ty1 x1 in
  let (| _, l2 |) = uint64_as_argument ty2 x2 in
  let p1' : parser parse_long_argument_kind (long_argument b1) = LowParse.Spec.Base.weaken parse_long_argument_kind (parse_synth (parse_filter p phi) f) in
  assert (parse_long_argument b1 == p1');
  let s1_pre = serialize_synth #_ #_ #(long_argument b1) _ f (serialize_filter s phi) g () in
  let s1' : serializer p1' = serialize_weaken parse_long_argument_kind s1_pre in
  serializer_unique (parse_long_argument b1) (serialize_long_argument b1) s1' l1;
  assert (serialize s1' l1 == serialize s1_pre l1);
  serialize_synth_eq #_ #_ #(long_argument b1) _ f (serialize_filter s phi) g () l1;
  s_spec (g l1);
  serializer_unique (parse_long_argument b1) (serialize_long_argument b1) s1' l2;
  assert (serialize s1' l2 == serialize s1_pre l2);
  serialize_synth_eq #_ #_ #(long_argument b1) _ f (serialize_filter s phi) g () l2;
  s_spec (g l2);
  big_endian_lex_compare' n (uv (g l1)) (uv (g l2))

#restart-solver
let lex_compare_with_header_correct
  (ty1: major_type_t { ty1 `U8.lt` cbor_major_type_simple_value })
  (x1: U64.t)
  (ty2: major_type_t { ty2 `U8.lt` cbor_major_type_simple_value })
  (x2: U64.t)
: Lemma
  (requires (
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2
  ))
  (ensures (
    ty1 == ty2 /\
    bytes_lex_compare (serialize serialize_header (uint64_as_argument ty1 x1)) (serialize serialize_header (uint64_as_argument ty2 x2)) == int_compare (U64.v x1) (U64.v x2)
  ))
= let h1 = uint64_as_argument ty1 x1 in
  let (| b1, l1 |) = h1 in
  let (_, (a1, _)) = b1 in
  if a1 = additional_info_long_argument_8_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 parse_u8 uint8_wf (LongArgumentU8 #b1 ()) LongArgumentU8?.v serialize_u8 1 U8.v (fun x -> serialize_u8_spec_be x) (fun x -> ())
  end else
  if a1 = additional_info_long_argument_16_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 parse_u16 uint16_wf (LongArgumentU16 #b1 ()) LongArgumentU16?.v serialize_u16 2 U16.v (fun x -> serialize_u16_spec_be x) (fun x -> ())
  end else
  if a1 = additional_info_long_argument_32_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 parse_u32 uint32_wf (LongArgumentU32 #b1 ()) LongArgumentU32?.v serialize_u32 4 U32.v (fun x -> serialize_u32_spec_be x) (fun x -> ())
  end else
  if a1 = additional_info_long_argument_64_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 parse_u64 uint64_wf (LongArgumentU64 #b1 ()) LongArgumentU64?.v serialize_u64 8 U64.v (fun x -> serialize_u64_spec_be x) (fun x -> ())
  end else
  begin
    lex_compare_with_header_long_argument ty1 x1 ty2 x2;
    let (| _, l2 |) = uint64_as_argument ty2 x2 in
    let p1' : parser parse_long_argument_kind (long_argument b1) = LowParse.Spec.Base.weaken parse_long_argument_kind (parse_synth parse_empty (LongArgumentOther #b1 a1 ())) in
    assert (parse_long_argument b1 == p1');
    let s1_pre = serialize_synth #_ #_ #(long_argument b1) _ (LongArgumentOther #b1 a1 ()) serialize_empty LongArgumentOther?.v () in
    let s1' : serializer p1' = serialize_weaken parse_long_argument_kind s1_pre in
    serializer_unique (parse_long_argument b1) (serialize_long_argument b1) s1' l1;
    assert (serialize s1' l1 == serialize s1_pre l1);
    assert (serialize s1' l1 `Seq.equal` Seq.empty);
    assert (serialize (serialize_long_argument b1) l1 == Seq.empty);
    serializer_unique (parse_long_argument b1) (serialize_long_argument b1) s1' l2;
    assert (serialize s1' l2 == serialize s1_pre l2);
    assert (serialize s1' l2 `Seq.equal` Seq.empty);
    assert (serialize (serialize_long_argument b1) l2 == Seq.empty)
  end

#pop-options

#push-options "--z3rlimit 16"
#restart-solver

let lex_compare_header_intro
  (ty: major_type_t { ty `U8.lt` cbor_major_type_simple_value })
  (x1: U64.t)
  (x2: U64.t)
: Lemma
  (ensures (
    bytes_lex_compare (serialize serialize_header (uint64_as_argument ty x1)) (serialize serialize_header (uint64_as_argument ty x2)) == int_compare (U64.v x1) (U64.v x2)
  ))
= get_uint64_as_initial_byte_header_correct ty x1;
  get_uint64_as_initial_byte_header_correct ty x2;
  if get_uint64_as_initial_byte ty x1 = get_uint64_as_initial_byte ty x2
  then lex_compare_with_header_correct ty x1 ty x2
  else begin
    let h1 = uint64_as_argument ty x1 in
    serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h1;
    let (| b1, l1 |) = h1 in
    let h2 = uint64_as_argument ty x2 in
    serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h2;
    let (| b2, l2 |) = h2 in
    serialize_initial_byte_compare b1 b2;
    bytes_lex_compare_serialize_strong_prefix serialize_initial_byte b1 b2 (serialize (serialize_long_argument b1) l1) (serialize (serialize_long_argument b2) l2)
  end

let serialized_lex_compare_int64
  (ty: major_type_uint64_or_neg_int64)
  (x1 x2: U64.t)
: Lemma
  (ensures (bytes_lex_compare (serialize serialize_raw_data_item (Int64 ty x1)) (serialize serialize_raw_data_item (Int64 ty x2)) == int_compare (U64.v x1) (U64.v x2)))
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
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (serialize (serialize_content h1) c1) (serialize (serialize_content h2) c2)

let lex_order_int64_correct
  (ty: major_type_uint64_or_neg_int64)
  (x1 x2: U64.t)
: Lemma
  (ensures (bytes_lex_order (serialize serialize_raw_data_item (Int64 ty x1)) (serialize serialize_raw_data_item (Int64 ty x2)) == x1 `U64.lt` x2))
= serialized_lex_compare_int64 ty x1 x2

let serialized_lex_compare_string
  (ty: major_type_byte_string_or_text_string)
  (len1: U64.t)
  (x1: Seq.lseq byte (U64.v len1))
  (len2: U64.t)
  (x2: Seq.lseq byte (U64.v len2))
: Lemma
  (ensures (
    serialized_lex_compare serialize_raw_data_item (String ty x1) (String ty x2) == (
      let c = int_compare (U64.v len1) (U64.v len2) in
      if c = 0
      then bytes_lex_compare x1 x2
      else c
  )))
= 
  let v1 = String ty x1 in
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
  let v2 = String ty x2 in
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
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (serialize (serialize_content h1) c1) (serialize (serialize_content h2) c2)

let deterministically_encoded_cbor_map_key_order_string_correct
  (ty: major_type_byte_string_or_text_string)
  (len1: U64.t)
  (x1: Seq.lseq byte (U64.v len1))
  (len2: U64.t)
  (x2: Seq.lseq byte (U64.v len2))
: Lemma
  (ensures (
    Ghost.reveal deterministically_encoded_cbor_map_key_order (String ty x1) (String ty x2) ==
      (len1 `U64.lt` len2 || (len1 = len2 && bytes_lex_order x1 x2))
  ))
= serialized_lex_compare_string ty len1 x1 len2 x2

let serialized_lex_compare_tagged
  (tag1: U64.t)
  (x1: raw_data_item)
  (tag2: U64.t)
  (x2: raw_data_item)
: Lemma
  (ensures (
    serialized_lex_compare serialize_raw_data_item (Tagged tag1 x1) (Tagged tag2 x2) == (
      let c = int_compare (U64.v tag1) (U64.v tag2) in
      if c = 0
      then serialized_lex_compare serialize_raw_data_item x1 x2
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
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (serialize (serialize_content h1) c1) (serialize (serialize_content h2) c2)

let deterministically_encoded_cbor_map_key_order_tagged_correct
  (tag1: U64.t)
  (x1: raw_data_item)
  (tag2: U64.t)
  (x2: raw_data_item)
: Lemma
  (ensures (
    Ghost.reveal deterministically_encoded_cbor_map_key_order (Tagged tag1 x1) (Tagged tag2 x2) ==
      (tag1 `U64.lt` tag2 || (tag1 = tag2 && Ghost.reveal deterministically_encoded_cbor_map_key_order x1 x2))
  ))
= serialized_lex_compare_tagged tag1 x1 tag2 x2

#pop-options

#push-options "--z3rlimit 16"

let rec serialized_lex_compare_nlist
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (n: nat)
  (x1 x2: nlist n t)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    (serialized_lex_compare (serialize_nlist n s)) x1 x2 == lex_compare (serialized_lex_compare s) x1 x2
  ))
  (decreases n)
= if n = 0
  then begin
    ()
  end
  else begin
    let a1 :: q1 = x1 in
    let a2 :: q2 = x2 in
    serialize_nlist_cons (n - 1) s a1 q1;
    serialize_nlist_cons (n - 1) s a2 q2;
    bytes_lex_compare_serialize_strong_prefix s a1 a2 (serialize (serialize_nlist (n - 1) s) q1) (serialize (serialize_nlist (n - 1) s) q2);
    serialized_lex_compare_nlist s (n - 1) q1 q2
  end

#pop-options

#push-options "--z3rlimit 32"

let serialized_lex_compare_array
  (len1: U64.t)
  (x1: list raw_data_item {List.Tot.length x1 == U64.v len1})
  (len2: U64.t)
  (x2: list raw_data_item {List.Tot.length x2 == U64.v len2})
: Lemma
  (ensures (
    serialized_lex_compare serialize_raw_data_item (Array x1) (Array x2) == (
      let c = int_compare (U64.v len1) (U64.v len2) in
      if c = 0
      then lex_compare (serialized_lex_compare serialize_raw_data_item) x1 x2
      else c
  )))
= 
  let v1 = Array x1 in
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
  let v2 = Array x2 in
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
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (serialize (serialize_content h1) c1) (serialize (serialize_content h2) c2);
  if len1 = len2
  then serialized_lex_compare_nlist serialize_raw_data_item (U64.v len1) c1 c2
  else ()

let serialized_lex_compare_map
  (len1: U64.t)
  (x1: list (raw_data_item & raw_data_item) {List.Tot.length x1 == U64.v len1})
  (len2: U64.t)
  (x2: list (raw_data_item & raw_data_item) {List.Tot.length x2 == U64.v len2})
: Lemma
  (ensures (
    serialized_lex_compare serialize_raw_data_item (Map x1) (Map x2) == (
      let c = int_compare (U64.v len1) (U64.v len2) in
      if c = 0
      then lex_compare (serialized_lex_compare (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) x1 x2
      else c
  )))
= 
  let v1 = Map x1 in
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
  let v2 = Map x2 in
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
  bytes_lex_compare_serialize_strong_prefix serialize_header h1 h2 (serialize (serialize_content h1) c1) (serialize (serialize_content h2) c2);
  if len1 = len2
  then serialized_lex_compare_nlist (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) (U64.v len1) c1 c2
  else ()

#pop-options

#push-options "--z3rlimit 16"

let serialized_lex_compare_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x1 x2: (t1 & t2))
: Lemma
  (requires (k1.parser_kind_subkind == Some ParserStrong))
  (ensures (
    (serialized_lex_compare (serialize_nondep_then s1 s2)) x1 x2 == (
      let c = serialized_lex_compare s1 (fst x1) (fst x2) in
      if c = 0
      then serialized_lex_compare s2 (snd x1) (snd x2)
      else c
  )))
=
  serialize_nondep_then_eq s1 s2 x1;
  serialize_nondep_then_eq s1 s2 x2;
  bytes_lex_compare_serialize_strong_prefix s1 (fst x1) (fst x2) (serialize s2 (snd x1)) (serialize s2 (snd x2))

#pop-options

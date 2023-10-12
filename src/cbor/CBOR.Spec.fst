module CBOR.Spec
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
    (if major_type = major_type_simple_value then additional_info `U8.lte` additional_info_long_argument_8_bits else true) && // TODO: support floating-point numbers
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
  additional_info == additional_info_long_argument_8_bits /\ major_type == major_type_simple_value

let long_argument_u8_prop
  (b: initial_byte)
: GTot prop
= let (major_type, (additional_info, _)) = b in
  additional_info == additional_info_long_argument_8_bits /\ ~ (major_type == major_type_simple_value)

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
  major_type = major_type_simple_value && additional_info `U8.lte` additional_info_simple_value_max

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
      if major_type = major_type_byte_string || major_type = major_type_text_string
      then Seq.lseq byte (U64.v (argument_as_uint64 b long_arg))
      else if major_type = major_type_array
      then nlist (U64.v (argument_as_uint64 b long_arg)) raw_data_item
      else if major_type = major_type_map
      then nlist (U64.v (argument_as_uint64 b long_arg)) (raw_data_item & raw_data_item)
      else if major_type = major_type_tagged
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
      if major_type = major_type_uint64 || major_type = major_type_neg_int64
      then Int64 major_type (argument_as_uint64 b long_arg)
      else if major_type = major_type_byte_string || major_type = major_type_text_string
      then String major_type c
      else if major_type = major_type_array
      then Array c
      else if major_type = major_type_map
      then Map c
      else if major_type = major_type_tagged
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
      if major_type = major_type_simple_value
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
      if major_type = major_type_byte_string || major_type = major_type_text_string
      then weaken _ (parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg)))
      else if major_type = major_type_array
      then weaken _ (parse_nlist (U64.v (argument_as_uint64 b long_arg)) p)
      else if major_type = major_type_map
      then weaken _ (parse_nlist (U64.v (argument_as_uint64 b long_arg)) (p `nondep_then` p))
      else if major_type = major_type_tagged
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
      major_type == major_type_byte_string \/ major_type == major_type_text_string

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
      if major_type = major_type_byte_string || major_type = major_type_text_string
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
      if major_type = major_type_array
      then
        U64.v (argument_as_uint64 b long_arg)
      else if major_type = major_type_map
      then
        let count = U64.v (argument_as_uint64 b long_arg) in
        count + count
      else if major_type = major_type_tagged
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
          if major_type = major_type_array
          then (| h, c |)
          else if major_type = major_type_map
          then (| h, pair_list_of_list _ (U64.v (argument_as_uint64 b long_arg)) c |)
          else if major_type = major_type_tagged
          then (| h, List.Tot.hd c |)
          else if major_type = major_type_byte_string || major_type = major_type_text_string
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

#push-options "--z3rlimit 64 --ifuel 8"
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

let get_major_type
  (d: raw_data_item)
: Tot major_type_t
= match d with
  | Simple _ -> major_type_simple_value
  | Int64 m _ -> m
  | String m _ -> m
  | Array _ -> major_type_array
  | Map _ -> major_type_map
  | Tagged _ _ -> major_type_tagged

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
    (requires (t `U8.lt` major_type_simple_value))
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
      major_type = major_type_simple_value /\
      additional_info `U8.lte` additional_info_long_argument_8_bits /\
      argument_as_simple_value b arg == x
    ))
= if x `U8.lte` max_simple_value_additional_info
  then (| mk_initial_byte major_type_simple_value x, LongArgumentOther x () () |)
  else (| mk_initial_byte major_type_simple_value additional_info_long_argument_8_bits, LongArgumentSimpleValue () x |)

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
      if major_type = major_type_simple_value
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
    (| uint64_as_argument major_type_array len, v |)
  | Map v ->
    let len = U64.uint_to_t (List.Tot.length v) in
    (| uint64_as_argument major_type_map len, v |)
  | Tagged tag v ->
    (| uint64_as_argument major_type_tagged tag, v |)

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
        if major_type = major_type_array
        then (| (| h, LeafContentEmpty () () |), c |)
        else if major_type = major_type_map
        then (| (| h, LeafContentEmpty () () |), list_of_pair_list _ (U64.v (argument_as_uint64 b long_arg)) c |)
        else if major_type = major_type_tagged
        then (| (| h, LeafContentEmpty () () |), [c] |)
        else if major_type = major_type_byte_string || major_type = major_type_text_string
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
      if major_type = major_type_byte_string || major_type = major_type_text_string
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
      if major_type = major_type_byte_string || major_type = major_type_text_string
      then serialize_weaken _ (serialize_lseq_bytes (U64.v (argument_as_uint64 b long_arg)))
      else if major_type = major_type_array
      then serialize_weaken _ (serialize_nlist (U64.v (argument_as_uint64 b long_arg)) serialize_raw_data_item)
      else if major_type = major_type_map
      then serialize_weaken _ (serialize_nlist (U64.v (argument_as_uint64 b long_arg)) (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item))
      else if major_type = major_type_tagged
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
    (fun _then -> k (| mk_initial_byte major_type_simple_value x, LongArgumentOther x () () |))
    (fun _else -> k (| mk_initial_byte major_type_simple_value additional_info_long_argument_8_bits, LongArgumentSimpleValue () x |))

inline_for_extraction
noextract
let cps_uint64_as_argument
  (t': Type)
  (t'_ifthenelse: if_combinator_weak t')
  (ty: major_type_t { ty `U8.lt` major_type_simple_value })
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
  (ty: major_type_t { ty `U8.lt` major_type_simple_value })
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
  (ty: major_type_t { ty `U8.lt` major_type_simple_value })
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

let holds_on_pair_bounded
  (#t0: Type)
  (bound: t0)
  (#t: Type)
  (pred: ((x: t { x << bound }) -> bool))
  (x: (t & t) { x << bound })
: Tot bool
= let (x1, x2) = x in
  pred x1 && pred x2

let rec holds_on_raw_data_item
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
= p x &&
  begin match x with
  | Array l -> forall_list l (holds_on_raw_data_item p)
  | Map l ->
    let l : list (raw_data_item & raw_data_item) = l in // IMPORTANT to remove the refinement on the type of the `bound` arg to holds_on_pair_bounded
    forall_list l (holds_on_pair_bounded l (holds_on_raw_data_item p))
  | Tagged _ v -> holds_on_raw_data_item p v
  | _ -> true
  end

let holds_on_pair
  (#t: Type)
  (pred: (t -> bool))
  (x: (t & t))
: Tot bool
= let (x1, x2) = x in
  pred x1 && pred x2

let holds_on_raw_data_item'
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
= p x &&
  begin match x with
  | Array l -> List.Tot.for_all (holds_on_raw_data_item p) l
  | Map l ->
    List.Tot.for_all (holds_on_pair (holds_on_raw_data_item p)) l
  | Tagged _ v -> holds_on_raw_data_item p v
  | _ -> true
  end

#push-options "--z3rlimit 16"

#restart-solver
let holds_on_raw_data_item_eq
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (holds_on_raw_data_item p x == holds_on_raw_data_item' p x)
= match x with
  | Array l ->
    assert_norm (holds_on_raw_data_item p (Array l) == (p (Array l) && forall_list l (holds_on_raw_data_item p)));
    forall_list_correct (holds_on_raw_data_item p) l
  | Map l ->
    let l : list (raw_data_item & raw_data_item) = l in
    assert_norm (holds_on_raw_data_item p (Map l) == (p (Map l) && forall_list l (holds_on_pair_bounded l (holds_on_raw_data_item p))));
    forall_list_correct (holds_on_pair (holds_on_raw_data_item p)) l;
    forall_list_ext l (holds_on_pair (holds_on_raw_data_item p)) (holds_on_pair_bounded l (holds_on_raw_data_item p)) (fun _ -> ())
  | _ -> ()

#pop-options

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

let data_item_wf_head (order: (raw_data_item -> raw_data_item -> bool)) (x: raw_data_item) : Tot bool
= match x with
  | Map l ->
      FStar.List.Tot.sorted (map_entry_order order _) l
  | _ -> true

let data_item_wf (order: (raw_data_item -> raw_data_item -> bool)) : Tot (raw_data_item -> bool)
= holds_on_raw_data_item (data_item_wf_head order)

let data_item (order: (raw_data_item -> raw_data_item -> bool)) = parse_filter_refine (data_item_wf order)

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

let deterministically_encoded_cbor_map_key_order'
  (k1 k2: raw_data_item)
: GTot bool
= LowParse.Spec.SeqBytes.bytes_lex_order (serialize_raw_data_item k1) (serialize_raw_data_item k2)

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


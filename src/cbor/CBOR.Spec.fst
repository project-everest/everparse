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
  | ByteString: (v: Seq.seq byte { FStar.UInt.fits (Seq.length v) U64.n }) -> raw_data_item
  | TextString: (v: Seq.seq byte { FStar.UInt.fits (Seq.length v) U64.n }) -> raw_data_item // Setion 3.1: "a string containing an invalid UTF-8 sequence is well-formed but invalid", so we don't care about UTF-8 specifics here.
  | Array: (v: list raw_data_item { FStar.UInt.fits (List.Tot.length v) U64.n }) -> raw_data_item
  | Map: (v: list (raw_data_item & raw_data_item) { FStar.UInt.fits (List.Tot.length v) U64.n }) -> raw_data_item
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

let parse_content_ext
  (p: parser parse_raw_data_item_kind raw_data_item)
  (p': parser parse_raw_data_item_kind raw_data_item)
  (h: header)
  (input: bytes)
  (prf: (
    (b: bytes { Seq.length b <= Seq.length input }) ->
    Lemma
    (parse p b == parse p' b)
  ))
: Lemma
  (parse (parse_content p h) input == parse (parse_content p' h) input)
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = 4uy
      then
        parse_nlist_ext (U64.v (argument_as_uint64 b long_arg)) p p' input prf
      else if major_type = 5uy
      then
        parse_nlist_ext (U64.v (argument_as_uint64 b long_arg)) (p `nondep_then` p) (p' `nondep_then` p') input
          (fun input' ->
            nondep_then_ext_l p p' p input' (prf input');
            nondep_then_ext_r p' p p' input' prf
          )
      else if major_type = 6uy
      then prf input
      else ()

let parse_raw_data_item_aux_ext
  (p p': parser parse_raw_data_item_kind raw_data_item)
  (input: bytes)
  (prf:
    (input' : bytes { Seq.length input' < Seq.length input }) -> // IMPORTANT: lt, not leq, to make induction work
    Lemma
    (parse p input' == parse p' input')
  )
: Lemma
  (parse (parse_raw_data_item_aux p) input == parse (parse_raw_data_item_aux p') input)
= parse_synth_ext
    (parse_dtuple2 parse_header (parse_content p))
    (parse_dtuple2 parse_header (parse_content p'))
    synth_raw_data_item
    input
    (
      parse_dtuple2_ext_r
        parse_header
        (parse_content p)
        (parse_content p')
        input
        (fun h input -> parse_content_ext p p' h input prf)
    )

let rec parse_raw_data_item_fuel_ext_gen
  (fuel: nat)
  (fuel': nat { fuel <= fuel' })
  (input: bytes { Seq.length input < fuel })
: Lemma
  (ensures (parse (parse_raw_data_item_fuel fuel) input == parse (parse_raw_data_item_fuel fuel') input))
  (decreases fuel)
= parse_raw_data_item_aux_ext
    (parse_raw_data_item_fuel (fuel - 1))
    (parse_raw_data_item_fuel (fuel' - 1))
    input
    (fun input' ->
      parse_raw_data_item_fuel_ext_gen (fuel - 1) (fuel' - 1) input'
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

let parse_raw_data_item_eq
  (b: bytes)
: Lemma
  (parse parse_raw_data_item b == parse (parse_raw_data_item_aux parse_raw_data_item) b)
= let c = closure b in
  let p = parse_raw_data_item_fuel (c - 1) in
  assert (parse parse_raw_data_item b == parse (parse_raw_data_item_aux p) b);
  parse_raw_data_item_aux_ext p parse_raw_data_item b (fun input' -> // here hypothesis Seq.length input' < Seq.length input is used
    parse_raw_data_item_fuel_ext (c - 1) input'
  )

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

let leaf_content
  (h: header)
: Tot Type
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = 2uy || major_type = 3uy
      then Seq.lseq byte (U64.v (argument_as_uint64 b long_arg))
      else unit

let parse_leaf_content
  (h: header)
: parser parse_content_kind (leaf_content h)
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = 2uy || major_type = 3uy
      then weaken _ (parse_lseq_bytes (U64.v (argument_as_uint64 b long_arg)))
      else weaken _ parse_empty

let leaf = dtuple2 header leaf_content

let parse_leaf : parser _ leaf = parse_header `parse_dtuple2` parse_leaf_content

let remaining_data_items
  (l: leaf)
: Tot nat
= match l with
  | (| (| b, long_arg |), _ |) ->
    match b with
    | (major_type, _) ->
      if major_type = 4uy
      then
        U64.v (argument_as_uint64 b long_arg)
      else if major_type = 5uy
      then
        let count = U64.v (argument_as_uint64 b long_arg) in
        count + count
      else if major_type = 6uy
      then 1
      else 0

let content_alt
  (l: leaf)
: Tot Type
= nlist (remaining_data_items l) raw_data_item

let parse_content_alt
  (l: leaf)
: Tot (parser parse_content_kind (content_alt l))
= weaken _ (parse_nlist (remaining_data_items l) parse_raw_data_item)

let raw_data_item_alt = dtuple2 leaf content_alt

let parse_raw_data_item_alt : parser parse_raw_data_item_kind raw_data_item_alt =
  parse_dtuple2 parse_leaf parse_content_alt

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

#push-options "--z3rlimit 16"
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
          if major_type = 4uy
          then (| h, c |)
          else if major_type = 5uy
          then (| h, pair_list_of_list _ (U64.v (argument_as_uint64 b long_arg)) c |)
          else if major_type = 6uy
          then (| h, List.Tot.hd c |)
          else (| h, lc |)

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

#push-options "--z3rlimit 32"
#restart-solver

let parse_raw_data_item_alt_correct
  (b: bytes)
: Lemma
  (parse parse_raw_data_item b == parse (parse_raw_data_item_alt `parse_synth` synth_raw_data_item_from_alt) b)
= parse_raw_data_item_eq b;
  parse_synth_eq (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item b;
  parse_dtuple2_eq parse_header (parse_content parse_raw_data_item) b;
  parse_synth_eq parse_raw_data_item_alt synth_raw_data_item_from_alt b;
  parse_dtuple2_eq parse_leaf parse_content_alt b;
  parse_dtuple2_eq parse_header parse_leaf_content b;
  match parse parse_header b with
  | None -> ()
  | Some _ ->
    Classical.forall_intro (parse_nlist_zero parse_raw_data_item);
    Classical.forall_intro (parse_nlist_one parse_raw_data_item);
    Classical.forall_intro_2 (parse_pair_list_as_list parse_raw_data_item)

#pop-options

(* Serialization *)

let major_type_t = bitfield uint8 3
let additional_info_t = bitfield uint8 5

let get_major_type
  (d: raw_data_item)
: Tot major_type_t
= match d with
  | Simple _ -> 7uy
  | UInt64 _ -> 0uy
  | NegInt64 _ -> 1uy
  | ByteString _ -> 2uy
  | TextString _ -> 3uy
  | Array _ -> 4uy
  | Map _ -> 5uy
  | Tagged _ _ -> 6uy

inline_for_extraction
let mk_initial_byte
  (t: major_type_t)
  (x: additional_info_t)
: Pure initial_byte
    (requires (initial_byte_wf (t, (x, ()))))
    (ensures (fun _ -> True))
= (t, (x, ()))

let uint64_as_argument
  (t: major_type_t)
  (x: U64.t)
: Pure (b: initial_byte & long_argument b)
    (requires (t `U8.lt` 7uy))
    (ensures (fun y ->
      let (| b, arg |) = y in
      let (major_type', _) = b in
      t == major_type' /\
      argument_as_uint64 b arg = x
    ))
= if x `U64.lt` 24uL
  then (| mk_initial_byte t (Cast.uint64_to_uint8 x), () |)
  else if x `U64.lt` 256uL
  then (| mk_initial_byte t 24uy, Cast.uint64_to_uint8 x |)
  else if x `U64.lt` 65536uL
  then (| mk_initial_byte t 25uy, Cast.uint64_to_uint16 x |)
  else if x `U64.lt` 4294967296uL
  then (| mk_initial_byte t 26uy, Cast.uint64_to_uint32 x |)
  else (| mk_initial_byte t 27uy, x |)

let simple_value_as_argument
  (x: simple_value)
: Pure (b: initial_byte & long_argument b)
    (requires True)
    (ensures (fun y ->
      let (| b, arg |) = y in
      let (major_type, (additional_info, _)) = b in
      major_type = 7uy /\
      additional_info `U8.lte` 24uy /\
      argument_as_simple_value b arg == x
    ))
= if x `U8.lt` 24uy
  then (| mk_initial_byte 7uy x, () |)
  else (| mk_initial_byte 7uy 24uy, x |)

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
    if additional_info = 24uy
    then
      if major_type = 7uy
      then
        serialize_weaken _ (serialize_filter serialize_u8 simple_value_long_argument_wf)
      else serialize_weaken _ (serialize_filter serialize_u8 uint8_wf)
    else if additional_info = 25uy
    then serialize_weaken _ (serialize_filter serialize_u16 uint16_wf)
    else if additional_info = 26uy
    then serialize_weaken _ (serialize_filter serialize_u32 uint32_wf)
    else if additional_info = 27uy
    then serialize_weaken _ (serialize_filter serialize_u64 uint64_wf)
    else serialize_weaken _ serialize_empty

let serialize_header : serializer parse_header =
  serialize_dtuple2 serialize_initial_byte serialize_long_argument

let synth_raw_data_item_recip
  (x: raw_data_item)
: Tot raw_data_item'
= match x with
  | Simple v ->
    (| simple_value_as_argument v, () |)
  | UInt64 v ->
    (| uint64_as_argument 0uy v, () |)
  | NegInt64 v ->
    (| uint64_as_argument 1uy v, () |)
  | ByteString v ->
    let len = U64.uint_to_t (Seq.length v) in
    (| uint64_as_argument 2uy len, v |)
  | TextString v ->
    let len = U64.uint_to_t (Seq.length v) in
    (| uint64_as_argument 3uy len, v |)
  | Array v ->
    let len = U64.uint_to_t (List.Tot.length v) in
    (| uint64_as_argument 4uy len, v |)
  | Map v ->
    let len = U64.uint_to_t (List.Tot.length v) in
    (| uint64_as_argument 5uy len, v |)
  | Tagged tag v ->
    (| uint64_as_argument 6uy tag, v |)

let synth_raw_data_item_recip_inverse : squash (synth_inverse synth_raw_data_item synth_raw_data_item_recip) = ()

let synth_raw_data_item'_from_alt_recip
  (x: raw_data_item')
: Tot raw_data_item_alt
= match x with
  | (| h, c |) ->
    match h with
    | (| b, long_arg |) ->
      match b with
      | (major_type, _) ->
        if major_type = 4uy
        then (| (| h, () |), c |)
        else if major_type = 5uy
        then (| (| h, () |), list_of_pair_list _ (U64.v (argument_as_uint64 b long_arg)) c |)
        else if major_type = 6uy
        then (| (| h, () |), [c] |)
        else (| (| h, c |), [] |)

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
      if major_type = 2uy || major_type = 3uy
      then serialize_weaken _ (serialize_lseq_bytes (U64.v (argument_as_uint64 b long_arg)))
      else serialize_weaken _ serialize_empty

let serialize_leaf : serializer parse_leaf =
  serialize_dtuple2 serialize_header serialize_leaf_content

(* Construction of the serializer, by "step indexing" over the "level"
   (in fact the depth) of the raw data item. *)

let rec fold_left_list
  (#t: Type)
  (l: list t)
  (#t': Type)
  (p: t' -> (x: t { x << l }) -> t')
  (init: t')
: Tot t'
= match l with
  | [] -> init
  | a :: q -> fold_left_list q p (p init a)

let rec fold_left_list_ext
  (#t: Type)
  (l: list t)
  (#t': Type)
  (p1: t' -> (x: t { x << l }) -> t')
  (p2: t' -> (x: t { x << l }) -> t')
  (prf:
    (accu: t') ->
    (x: t { x << l }) ->
    Lemma
    (p1 accu x == p2 accu x)
  )
  (init: t')
: Lemma
  (ensures (fold_left_list l p1 init == fold_left_list l p2 init))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    prf init a;
    let accu' = p1 init a in
    fold_left_list_ext q p1 p2 prf accu'

let acc_level
  (#t0: Type)
  (l: t0)
  (#t: Type)
  (level: (x: t { x << l }) -> nat)
  (accu: nat)
  (x: t { x << l })
: Tot nat
= let n = level x in
  if n > accu then n else accu

let acc_level_pair
  (#t0: Type)
  (l: t0)
  (#t: Type)
  (level: (x: t { x << l }) -> nat)
  (accu: nat)
  (x: (t & t) { x << l })
= let (x1, x2) = x in
  acc_level l level (acc_level l level accu x1) x2

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

let rec fold_left_list_acc_level_ge_accu
  (v: list raw_data_item)
  (accu: nat)
: Lemma
  (ensures (fold_left_list v (acc_level v level) accu >= accu))
= match v with
  | [] -> ()
  | a :: q ->
    let accu' = acc_level v level accu a in
    fold_left_list_ext q (acc_level v level) (acc_level q level) (fun _ _ -> ()) accu';
    fold_left_list_acc_level_ge_accu q accu'

let rec fold_left_list_acc_level_pair_ge_accu
  (v: list (raw_data_item & raw_data_item))
  (accu: nat)
: Lemma
  (ensures (fold_left_list v (acc_level_pair v level) accu >= accu))
= match v with
  | [] -> ()
  | a :: q ->
    let accu' = acc_level_pair v level accu a in
    fold_left_list_ext q (acc_level_pair v level) (acc_level_pair q level) (fun _ _ -> ()) accu';
    fold_left_list_acc_level_pair_ge_accu q accu'

let forall_list_f
  (#t: Type)
  (l: list t)
  (p: (x: t { x << l }) -> bool)
  (init: bool)
  (a: t { a << l })
: Tot bool
= init && p a

let forall_list
  (#t: Type)
  (l: list t)
  (p: (x: t { x << l }) -> bool)
: Tot bool
= fold_left_list l (forall_list_f l p) true

let forall_list_ext
  (#t: Type)
  (l: list t)
  (p1: (x: t { x << l }) -> bool)
  (p2: (x: t { x << l }) -> bool)
  (prf:
    (x: t { x << l }) ->
    Lemma
    (p1 x == p2 x)
  )
: Lemma
  (forall_list l p1 == forall_list l p2)
= fold_left_list_ext l (forall_list_f l p1) (forall_list_f l p2) (fun _ x -> prf x) true

let rec fold_left_list_forall_list_aux
  (#t: Type)
  (l: list t)
  (p: (x: t { x << l }) -> bool)
  (init: bool)
: Lemma
  (ensures (fold_left_list l (forall_list_f l p) init ==
    (init && fold_left_list l (forall_list_f l p) true)
  ))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    fold_left_list_ext q (forall_list_f l p) (forall_list_f q p) (fun _ _ -> ()) (init && p a);
    fold_left_list_ext q (forall_list_f l p) (forall_list_f q p) (fun _ _ -> ()) true;
    fold_left_list_forall_list_aux q p (init && p a)

let forall_list_cons'
  (#t: Type)
  (l: list t)
  (a: t)
  (q: list t)
  (p: (x: t { x << a :: q }) -> bool)
: Lemma
  (requires (
    l == a :: q
  ))
  (ensures (
    a << a :: q /\
    q << a :: q /\
    forall_list (a :: q) p == (p a && forall_list q p)
  ))
  (decreases l)
= match l with
  | _ :: _ ->
  assert (a << a :: q);
  assert (q << a :: q);
  fold_left_list_ext q (forall_list_f (a :: q) p) (forall_list_f q p) (fun _ _ -> ()) (p a);
  fold_left_list_forall_list_aux q p (p a)

let forall_list_cons
  (#t: Type)
  (a: t)
  (q: list t)
  (p: (x: t { x << a :: q }) -> bool)
: Lemma
  (ensures (
    a << a :: q /\
    q << a :: q /\
    forall_list (a :: q) p == (p a && forall_list q p)
  ))
= forall_list_cons' (a :: q) a q p

let raw_data_item_has_level
  (n: nat)
  (d: raw_data_item)
: Tot bool
= level d <= n

let raw_data_item_pair_has_level
  (n: nat)
  (d: (raw_data_item & raw_data_item))
: Tot bool
= let (d1, d2) = d in
  raw_data_item_has_level n d1 &&
  raw_data_item_has_level n d2

let rec fold_left_list_has_level_gen
  (n: nat)
  (v: list raw_data_item)
  (accu: nat)
: Lemma
  (requires (n >= fold_left_list v (acc_level v level) accu))
  (ensures (forall_list v (raw_data_item_has_level n)))
  (decreases v)
= match v with
  | [] -> ()
  | a :: q ->
    let accu' = acc_level v level accu a in
    forall_list_cons a q (raw_data_item_has_level n);
    fold_left_list_ext q (acc_level v level) (acc_level q level) (fun _ _ -> ()) accu';
    fold_left_list_acc_level_ge_accu q accu';
    fold_left_list_has_level_gen n q accu'

let fold_left_list_has_level
  (v: list raw_data_item)
  (accu: nat)
: Lemma
  (forall_list v (raw_data_item_has_level (fold_left_list v (acc_level v level) accu)))
= fold_left_list_has_level_gen (fold_left_list v (acc_level v level) accu) v accu

let rec fold_left_list_pair_has_level_gen
  (n: nat)
  (v: list (raw_data_item & raw_data_item))
  (accu: nat)
: Lemma
  (requires (n >= fold_left_list v (acc_level_pair v level) accu))
  (ensures (forall_list v (raw_data_item_pair_has_level n)))
  (decreases v)
= match v with
  | [] -> ()
  | a :: q ->
    let accu' = acc_level_pair v level accu a in
    forall_list_cons a q (raw_data_item_pair_has_level n);
    fold_left_list_ext q (acc_level_pair v level) (acc_level_pair q level) (fun _ _ -> ()) accu';
    fold_left_list_acc_level_pair_ge_accu q accu';
    fold_left_list_pair_has_level_gen n q accu'

let fold_left_list_pair_has_level
  (v: list (raw_data_item & raw_data_item))
  (accu: nat)
: Lemma
  (forall_list v (raw_data_item_pair_has_level (fold_left_list v (acc_level_pair v level) accu)))
= fold_left_list_pair_has_level_gen (fold_left_list v (acc_level_pair v level) accu) v accu

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

let raw_data_item_list_has_pred_level (n: nat) (l: list raw_data_item) : bool = if n = 0 then Nil? l else forall_list l (raw_data_item_has_level (n - 1))

let raw_data_item_alt_has_pred_level
  (n: nat)
  (x: raw_data_item_alt)
: Tot bool
= raw_data_item_list_has_pred_level n (dsnd x)

#push-options "--z3rlimit 16"
#restart-solver

let synth_raw_data_item_from_alt_recip_list_has_pred_level
  (n: nat)
  (x: parse_filter_refine (raw_data_item_has_level n))
: Lemma
  (raw_data_item_alt_has_pred_level n (synth_raw_data_item_from_alt_recip x))
= match x with
  | Array l ->
    let l : list raw_data_item = l in
    assert_norm (level x == 1 + fold_left_list l (acc_level l level) 0);
    fold_left_list_has_level_gen (n - 1) l 0
  | Map l ->
    let l : list (raw_data_item & raw_data_item) = l in
    assert_norm (level x == 1 + fold_left_list l (acc_level_pair l level) 0);
    fold_left_list_pair_has_level_gen (n - 1) l 0;
    assert (dsnd (synth_raw_data_item_from_alt_recip x) == list_of_pair_list raw_data_item (List.Tot.length l) l);
    fold_left_list_acc_level_list_of_pair_list (n - 1) l;
    assert (raw_data_item_list_has_pred_level n (dsnd (synth_raw_data_item_from_alt_recip x)))
  | _ -> ()

#pop-options

#restart-solver

let mk_serialize_raw_data_item_with_level
  (n: nat)
  (s: serializer (parse_filter parse_raw_data_item_alt (raw_data_item_alt_has_pred_level n)))
: Tot (serializer (parse_filter parse_raw_data_item (raw_data_item_has_level n)))
= 
  let s'
    (x: parse_filter_refine (raw_data_item_has_level n))
  : GTot bytes
  = synth_raw_data_item_from_alt_recip_list_has_pred_level n x;
    s (synth_raw_data_item_from_alt_recip x)
  in
  let prf
    (x: parse_filter_refine (raw_data_item_has_level n))
  : Lemma
    (let b = s' x in
      parse (parse_filter parse_raw_data_item (raw_data_item_has_level n)) b == Some (x, Seq.length b)
    )
  = let b = s' x in
    synth_raw_data_item_from_alt_recip_list_has_pred_level n x;
    parse_filter_eq parse_raw_data_item_alt (raw_data_item_alt_has_pred_level n) b;
    parse_filter_eq parse_raw_data_item (raw_data_item_has_level n) b;
    parse_raw_data_item_alt_correct b;
    parse_synth_eq parse_raw_data_item_alt synth_raw_data_item_from_alt b
  in
  Classical.forall_intro prf;
  s'

let bare_serialize_raw_data_item_list_has_pred_level_zero (len: nat) : bare_serializer (parse_filter_refine #(nlist len raw_data_item) (raw_data_item_list_has_pred_level 0)) =
  fun _ -> Seq.empty

let serialize_raw_data_item_list_has_pred_level_zero (n: nat { n == 0 }) (len: nat) : serializer (parse_nlist len parse_raw_data_item `parse_filter` raw_data_item_list_has_pred_level n) =
  let prf
    (x: parse_filter_refine #(nlist len raw_data_item) (raw_data_item_list_has_pred_level n))
  : Lemma
    (let b = bare_serialize_raw_data_item_list_has_pred_level_zero len x in
      parse (parse_nlist len parse_raw_data_item `parse_filter` raw_data_item_list_has_pred_level n) b == Some (x, Seq.length b))
  =
    assert (Nil? x);
    let res : bytes = Seq.empty in
    parse_filter_eq (parse_nlist len parse_raw_data_item) (raw_data_item_list_has_pred_level n) res;
    parse_nlist_zero parse_raw_data_item res
  in
  Classical.forall_intro prf;
  bare_serialize_raw_data_item_list_has_pred_level_zero len

#restart-solver

let rec serialize_raw_data_item_list_has_pred_level_pos
  (n: pos)
  (s: serializer (parse_filter parse_raw_data_item (raw_data_item_has_level (n - 1))))
  (len: nat)
: Tot (serializer (parse_nlist len parse_raw_data_item `parse_filter` raw_data_item_list_has_pred_level n))
  (decreases len)
= let s'
    (l: parse_filter_refine #(nlist len raw_data_item) (raw_data_item_list_has_pred_level n))
  : GTot bytes
  = match l with
    | [] -> Seq.empty
    | a :: q ->
      forall_list_cons a q (raw_data_item_has_level (n - 1));
      s a `Seq.append` serialize_raw_data_item_list_has_pred_level_pos n s (len - 1) q
  in
  let prf
    (l: parse_filter_refine #(nlist len raw_data_item) (raw_data_item_list_has_pred_level n))
  : Lemma
    (let b = s' l in
      parse (parse_nlist len parse_raw_data_item `parse_filter` raw_data_item_list_has_pred_level n) b == Some (l, Seq.length b)
    )
  = let b = s' l in
    parse_filter_eq (parse_nlist len parse_raw_data_item) (raw_data_item_list_has_pred_level n) b;
    parse_nlist_eq len parse_raw_data_item b;
    match l with
    | [] -> ()
    | a :: q ->
      forall_list_cons a q (raw_data_item_has_level (n - 1));
      parse_filter_eq parse_raw_data_item (raw_data_item_has_level (n - 1)) (s a);
      let b' = serialize_raw_data_item_list_has_pred_level_pos n s (len - 1) q in
      assert_norm (s' (a :: q) == s a `Seq.append` b');
      assert (parse parse_raw_data_item (s a) == Some (a, Seq.length (s a)));
      let (b1, b2) = Seq.split_eq b (Seq.length (s a)) in
      Seq.lemma_append_inj b1 b2 (s a) b';
      parse_strong_prefix parse_raw_data_item (s a) b;
      parse_filter_eq (parse_nlist (len - 1) parse_raw_data_item) (raw_data_item_list_has_pred_level n) b'
  in
  Classical.forall_intro prf;
  s'

#restart-solver

let mk_serialize_raw_data_item_alt_with_level
  (n: nat)
  (s: ((l: leaf) -> serializer (weaken parse_content_kind (parse_nlist (remaining_data_items l) parse_raw_data_item `parse_filter` raw_data_item_list_has_pred_level n))))
: Tot (serializer (parse_filter parse_raw_data_item_alt (raw_data_item_alt_has_pred_level n)))
= let s1 = serialize_dtuple2 #_ #leaf #parse_leaf serialize_leaf s in
  let s'
    (x: parse_filter_refine (raw_data_item_alt_has_pred_level n))
  = let (| l, c |) = x in
    s1 (| l, c |)
  in
  let prf
    (x: parse_filter_refine (raw_data_item_alt_has_pred_level n))
  : Lemma
    (let b = s' x in
      parse (parse_filter parse_raw_data_item_alt (raw_data_item_alt_has_pred_level n)) b == Some (x, Seq.length b)
    )
  = let b = s' x in
    parse_filter_eq parse_raw_data_item_alt (raw_data_item_alt_has_pred_level n) b;
    parse_dtuple2_eq parse_leaf parse_content_alt b;
    parse_dtuple2_eq parse_leaf (fun l -> weaken parse_content_kind (parse_nlist (remaining_data_items l) parse_raw_data_item `parse_filter` raw_data_item_list_has_pred_level n)) b;
    let Some (l, consumed) = parse parse_leaf b in
    let b' = Seq.slice b consumed (Seq.length b) in
    parse_filter_eq (parse_nlist (remaining_data_items l) parse_raw_data_item) (raw_data_item_list_has_pred_level n) b'
  in
  Classical.forall_intro prf;
  s'

let rec serialize_raw_data_item_with_level
  (n: nat)
: Tot (serializer (parse_filter parse_raw_data_item (raw_data_item_has_level n)))
= mk_serialize_raw_data_item_with_level
    n
    (mk_serialize_raw_data_item_alt_with_level
      n
      (fun l ->
        let len = remaining_data_items l in
        serialize_weaken _
        (
          if n = 0
          then serialize_raw_data_item_list_has_pred_level_zero n len
          else serialize_raw_data_item_list_has_pred_level_pos n (serialize_raw_data_item_with_level (n - 1)) len
        )
      )
    )

#push-options "--z3rlimit 16"
#restart-solver

let serialize_raw_data_item : serializer parse_raw_data_item =
  let s' (x: raw_data_item) : GTot bytes =
    serialize_raw_data_item_with_level (level x) x
  in
  let prf
    (x: raw_data_item)
  : Lemma
    (let b = s' x in
      parse parse_raw_data_item b == Some (x, Seq.length b)
    )
  = parse_filter_eq parse_raw_data_item (raw_data_item_has_level (level x)) (s' x)
  in
  Classical.forall_intro prf;
  s'

#pop-options

(* Serialization equations to prove the functional correctness of implementations *)

let serialize_content
  (h: header)
: Tot (serializer (parse_content parse_raw_data_item h))
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      if major_type = 2uy || major_type = 3uy
      then serialize_weaken _ (serialize_lseq_bytes (U64.v (argument_as_uint64 b long_arg)))
      else if major_type = 4uy
      then serialize_weaken _ (serialize_nlist (U64.v (argument_as_uint64 b long_arg)) serialize_raw_data_item)
      else if major_type = 5uy
      then serialize_weaken _ (serialize_nlist (U64.v (argument_as_uint64 b long_arg)) (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item))
      else if major_type = 6uy
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

let serialize_content_alt
  (l: leaf)
: Tot (serializer (parse_content_alt l))
= serialize_weaken _ (serialize_nlist (remaining_data_items l) serialize_raw_data_item)

let serialize_raw_data_item_alt : serializer parse_raw_data_item_alt =
  serialize_dtuple2 serialize_leaf serialize_content_alt

let serialize_raw_data_item_alt_synth : serializer (parse_raw_data_item_alt `parse_synth` synth_raw_data_item_from_alt) =
  serialize_synth
    _
    synth_raw_data_item_from_alt
    serialize_raw_data_item_alt
    synth_raw_data_item_from_alt_recip
    ()

let serialize_raw_data_item_alt_synth_correct
  (x: raw_data_item)
: Lemma
  (serialize serialize_raw_data_item x == serialize serialize_raw_data_item_alt_synth x)
= Classical.forall_intro parse_raw_data_item_alt_correct;
  let s' = serialize_ext parse_raw_data_item serialize_raw_data_item (parse_raw_data_item_alt `parse_synth` synth_raw_data_item_from_alt) in
  serializer_unique (parse_raw_data_item_alt `parse_synth` synth_raw_data_item_from_alt) serialize_raw_data_item_alt_synth s' x

(*
// Ordering of map keys (Section 4.2)

let rec data_item_wf (order: (raw_data_item -> raw_data_item -> bool)) (x: raw_data_item) : Tot bool
= match x with
  | Array l -> forall_list l (data_item_wf order)
  | Map l -> forall_list_fst l (data_item_wf order) && forall_list_snd l (data_item_wf order) &&
      FStar.List.Tot.sorted order (FStar.List.Tot.map fst l)
  | Tagged _ v -> data_item_wf order v
  | _ -> true

let data_item (order: (raw_data_item -> raw_data_item -> bool)) = (d: raw_data_item { data_item_wf order d })

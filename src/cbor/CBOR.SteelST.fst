module CBOR.SteelST
include CBOR.Spec
open LowParse.SteelST.Combinators
open LowParse.SteelST.Recursive
open LowParse.SteelST.BitSum
open LowParse.SteelST.Int
open LowParse.SteelST.Access

#set-options "--print_universes"

inline_for_extraction
let validate_initial_byte : validator parse_initial_byte =
  validate_filter_with_cps_reader
    (validate_bitsum'
      filter_initial_byte
      validate_u8
      (cps_reader_of_leaf_reader read_u8)
    )
    (read_bitsum'
      destr_initial_byte
      (cps_reader_of_leaf_reader read_u8)
    )
    initial_byte_wf
    (fun x -> initial_byte_wf x)

inline_for_extraction
let jump_initial_byte : jumper parse_initial_byte =
  jump_filter
    (jump_bitsum'
      initial_byte_desc
      jump_u8
    )
    initial_byte_wf

inline_for_extraction
let read_initial_byte : cps_reader parse_initial_byte =
  cps_read_filter
    (read_bitsum'
      destr_initial_byte
      (cps_reader_of_leaf_reader read_u8)
    )
    initial_byte_wf

noeq
type long_argument_case = | LongArgCase24Subcase7 | LongArgCase24Other | LongArgCase25 | LongArgCase26 | LongArgCase27 | LongArgCaseOther

let get_long_argument_case
  (major_type: major_type_t)
  (additional_info: additional_info_t)
: Tot long_argument_case  
=   if additional_info = 24uy
    then
      if major_type = 7uy
      then LongArgCase24Subcase7
      else LongArgCase24Other
    else if additional_info = 25uy
    then LongArgCase25
    else if additional_info = 26uy
    then LongArgCase26
    else if additional_info = 27uy
    then LongArgCase27
    else LongArgCaseOther

inline_for_extraction
noextract
let destr_long_argument_case
  (u: (long_argument_case -> Tot (Type u#a)))
  (u_if: ((k: Ghost.erased long_argument_case) -> Tot (if_combinator_weak (u (Ghost.reveal k)))))
  (f: ((k: long_argument_case) -> Tot (u k)))
  (major_type: major_type_t)
  (additional_info: additional_info_t)
: Tot (u (get_long_argument_case major_type additional_info))
= [@inline_let]
  let k = Ghost.hide (get_long_argument_case major_type additional_info) in
  u_if k (additional_info = 24uy)
    (fun _true ->
      u_if k (major_type = 7uy)
        (fun _true -> f LongArgCase24Subcase7)
        (fun _false -> f LongArgCase24Other)
    )
    (fun _false ->
      u_if k (additional_info = 25uy)
        (fun _true -> f LongArgCase25)
        (fun _false ->
          u_if k (additional_info = 26uy)
            (fun _true -> f LongArgCase26)
            (fun _false ->
              u_if k (additional_info = 27uy)
                (fun _true -> f LongArgCase27)
                (fun _false -> f LongArgCaseOther)
            )
        )
    )

let long_argument0
  (l: long_argument_case)
: Tot Type
= match l with
  | LongArgCase24Subcase7 -> parse_filter_refine simple_value_long_argument_wf
  | LongArgCase24Other -> parse_filter_refine uint8_wf
  | LongArgCase25 -> parse_filter_refine uint16_wf
  | LongArgCase26 -> parse_filter_refine uint32_wf
  | LongArgCase27 -> parse_filter_refine uint64_wf
  | _ -> unit

let parse_long_argument0
  (c: long_argument_case)
: Tot (parser (strong_parser_kind 0 8 None) (long_argument0 c))
= match c with
  | LongArgCase24Subcase7 -> weaken _ (parse_filter parse_u8 simple_value_long_argument_wf)
  | LongArgCase24Other -> weaken _ (parse_filter parse_u8 uint8_wf)
  | LongArgCase25 -> weaken _ (parse_filter parse_u16 uint16_wf)
  | LongArgCase26 -> weaken _ (parse_filter parse_u32 uint32_wf)
  | LongArgCase27 -> weaken _ (parse_filter parse_u64 uint64_wf)
  | LongArgCaseOther -> weaken _ parse_empty

let long_argument0_correct
  (x: initial_byte)
: Lemma
  (let (major_type, (additional_info, _)) = x in
    let c = get_long_argument_case major_type additional_info in
    long_argument x == long_argument0 c /\
    parse_long_argument x == parse_long_argument0 c
  )
= ()

inline_for_extraction
let validate_long_argument0
  (c: long_argument_case)
: Tot (validator (parse_long_argument0 c))
= match c returns (validator (parse_long_argument0 c)) with
  | LongArgCase24Subcase7 -> validate_weaken _ (validate_filter validate_u8 read_u8 simple_value_long_argument_wf (fun x -> simple_value_long_argument_wf x)) ()
  | LongArgCase24Other -> validate_weaken _ (validate_filter validate_u8 read_u8 uint8_wf (fun x -> uint8_wf x)) ()
  | LongArgCase25 -> validate_weaken _ (validate_filter validate_u16 read_u16 uint16_wf (fun x -> uint16_wf x)) ()
  | LongArgCase26 -> validate_weaken _ (validate_filter validate_u32 read_u32 uint32_wf (fun x -> uint32_wf x)) ()
  | LongArgCase27 -> validate_weaken _ (validate_filter validate_u64 read_u64 uint64_wf (fun x -> uint64_wf x)) ()
  | LongArgCaseOther -> validate_weaken _ (validate_total_constant_size parse_empty 0sz) ()

inline_for_extraction
let validate_long_argument
  (x: initial_byte)
: Tot (validator (parse_long_argument x))
= match x with
  | (major_type, (additional_info, _)) ->  
    rewrite_validator
      (destr_long_argument_case
        (fun c -> validator (parse_long_argument0 c))
        (fun _ -> ifthenelse_validate)
        validate_long_argument0
        major_type
        additional_info
      )
      (parse_long_argument x)

inline_for_extraction
let jump_long_argument0
  (c: long_argument_case)
: Tot (jumper (parse_long_argument0 c))
= match c returns (jumper (parse_long_argument0 c)) with
  | LongArgCase24Subcase7 -> jump_weaken _ (jump_filter jump_u8 simple_value_long_argument_wf) ()
  | LongArgCase24Other -> jump_weaken _ (jump_filter jump_u8 uint8_wf) ()
  | LongArgCase25 -> jump_weaken _ (jump_filter jump_u16 uint16_wf) ()
  | LongArgCase26 -> jump_weaken _ (jump_filter jump_u32 uint32_wf) ()
  | LongArgCase27 -> jump_weaken _ (jump_filter jump_u64 uint64_wf) ()
  | LongArgCaseOther -> jump_weaken _ (jump_constant_size parse_empty 0sz) ()

inline_for_extraction
let jump_long_argument
  (x: initial_byte)
: Tot (jumper (parse_long_argument x))
= match x with
  | (major_type, (additional_info, _)) ->  
    rewrite_jumper
      (destr_long_argument_case
        (fun c -> jumper (parse_long_argument0 c))
        (fun _ -> ifthenelse_jump)
        jump_long_argument0
        major_type
        additional_info
      )
      (parse_long_argument x)

inline_for_extraction
let read_long_argument0
  (c: long_argument_case)
: Tot (leaf_reader (parse_long_argument0 c))
= match c returns (leaf_reader (parse_long_argument0 c)) with
  | LongArgCase24Subcase7 -> read_weaken _ (read_filter read_u8 simple_value_long_argument_wf)
  | LongArgCase24Other -> read_weaken _ (read_filter read_u8 uint8_wf)
  | LongArgCase25 -> read_weaken _ (read_filter read_u16 uint16_wf)
  | LongArgCase26 -> read_weaken _ (read_filter read_u32 uint32_wf) 
  | LongArgCase27 -> read_weaken _ (read_filter read_u64 uint64_wf)
  | LongArgCaseOther -> read_weaken _ read_empty

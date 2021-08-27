module ASN1.Spec.IdentifierU32

open ASN1.Base

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.Int

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

let byte = U8.t

(* Ref X690 8.1.2 *)

(* common *)

let decode_asn1_identifier_class (b : byte { U8.v b <= 3 }) : asn1_id_class_t
= match b with
  | 0uy -> UNIVERSAL
  | 1uy -> APPLICATION
  | 2uy -> CONTEXT_SPECIFIC
  | 3uy -> PRIVATE

let decode_asn1_identifier_flag (b : byte { U8.v b <= 1 }) : asn1_id_flag_t
= match b with
  | 0uy -> PRIMITIVE
  | 1uy -> CONSTRUCTED

(* Identifier30 : short form 1 byte identifier range [0, 30] *)

let parse_asn1_identifier30_kind = strong_parser_kind 1 1 None

let is_valid_asn1_identifier30 (b : byte)
= (U8.rem b 32uy) <> 31uy

let decode_asn1_identifier30 (b : byte) : asn1_id_t
= MK_ASN1_ID
  (decode_asn1_identifier_class (U8.shift_right b 6ul))
  (decode_asn1_identifier_flag (U8.rem (U8.shift_right b 5ul) 2uy))
  (Cast.uint8_to_uint32 (U8.rem b 32uy))

#push-options "--z3rlimit 128"

let parse_asn1_identifier30 : parser parse_asn1_identifier30_kind asn1_id_t
= parse_u8
  `parse_filter`
  is_valid_asn1_identifier30
  `parse_synth`
  decode_asn1_identifier30

(* Identifier_UXX : supports up to (XX div 7) bytes in long form *)

(* Haobin: opitmizable with fewer argument passing*)

type asn1_partial_id_t =
| MK_ASN1_PARTIAL_ID :
  pid_class : asn1_id_class_t ->
  pid_flag : asn1_id_flag_t ->
  pid_value : U32.t ->
  asn1_partial_id_t

let update_value (v : U32.t) (b : byte) : U32.t
= (U32.logor (U32.shift_left v 7ul) (Cast.uint8_to_uint32 b))

let update_finish (state : asn1_partial_id_t) (buf : byte) : asn1_id_t
= let buf' = U8.rem buf 128uy in
  (MK_ASN1_ID state.pid_class state.pid_flag (update_value state.pid_value buf'))

let update_loop (state : asn1_partial_id_t) (buf : byte) : asn1_partial_id_t
= let buf' = U8.rem buf 128uy in
  (MK_ASN1_PARTIAL_ID state.pid_class state.pid_flag (update_value state.pid_value buf'))

let parse_asn1_identifier_tail_kind = strong_parser_kind 0 0 None

let parse_asn1_identifier_tail (state : asn1_partial_id_t) (buf : byte) : parser parse_asn1_identifier_tail_kind asn1_id_t
= if (U8.v buf) < 128 then
    weaken (parse_asn1_identifier_tail_kind) (parse_ret (update_finish state buf))
  else
    fail_parser (parse_asn1_identifier_tail_kind) asn1_id_t

let lemma_parse_asn1_identifier_tail_injective (state : asn1_partial_id_t) : and_then_cases_injective (parse_asn1_identifier_tail state)
= admit ()

let parse_asn1_identifier_loop_kind = strong_parser_kind 0 1 None

let parse_asn1_identifier_loop (state : asn1_partial_id_t) (buf : byte) : parser parse_asn1_identifier_loop_kind asn1_id_t
= if (U8.v buf) < 128 then
    weaken (parse_asn1_identifier_loop_kind) (parse_ret (update_finish state buf))
  else
    let state' = update_loop state buf in
    let p' = parse_asn1_identifier_tail state' in
    let _ : and_then_cases_injective p' = lemma_parse_asn1_identifier_tail_injective state' in
    weaken (parse_asn1_identifier_loop_kind)
      (parse_u8
      `and_then`
      p')

let lemma_parse_asn1_identifier_loop_injective (state : asn1_partial_id_t) : and_then_cases_injective (parse_asn1_identifier_loop state)
= admit()

let parse_asn1_identifier_head_kind = strong_parser_kind 0 2 None

let parse_asn1_identifier_head (state : asn1_partial_id_t) (buf : byte) : parser parse_asn1_identifier_head_kind asn1_id_t
= if (U8.v buf) < 128 then
    if (U8.v buf) < 31 then
      fail_parser (parse_asn1_identifier_head_kind) asn1_id_t
    else
      weaken (parse_asn1_identifier_head_kind) (parse_ret (update_finish state buf))
  else
    if (U8.v buf) = 128 then
      fail_parser (parse_asn1_identifier_head_kind) asn1_id_t
    else
      let state' = update_loop state buf in
      let p' = parse_asn1_identifier_loop state' in
      let _ : and_then_cases_injective p' = lemma_parse_asn1_identifier_loop_injective state' in
      weaken (parse_asn1_identifier_head_kind)
        (parse_u8
         `and_then`
         p')

let lemma_parse_asn1_identifier_head_injective (state : asn1_partial_id_t) : and_then_cases_injective (parse_asn1_identifier_head state)
= admit ()

let parse_asn1_identifier_first_kind = strong_parser_kind 0 3 None

let parse_asn1_identifier_first (buf : byte) : parser parse_asn1_identifier_first_kind asn1_id_t
= let x = U8.rem buf 32uy in
  assert (U8.v x < 32);
  if U8.v x < 31 then
    weaken (parse_asn1_identifier_first_kind) (parse_ret (decode_asn1_identifier30 x))
  else
    let c = (U8.shift_right buf 6ul) in
    let f = (U8.rem (U8.shift_right buf 5ul) 2uy) in 
    let state = MK_ASN1_PARTIAL_ID (decode_asn1_identifier_class c) (decode_asn1_identifier_flag f) (U32.zero) in
    let p' = parse_asn1_identifier_head state in
    let _ : and_then_cases_injective p' = lemma_parse_asn1_identifier_head_injective state in
    weaken (parse_asn1_identifier_first_kind) 
      (parse_u8
      `and_then`
      p')


let lemma_parse_asn1_identifier_first_injective () : and_then_cases_injective parse_asn1_identifier_first
= admit()

let parse_asn1_identifier_u21_kind = strong_parser_kind 1 4 None

//#set-options "--query_stats"

//#push-options "--fuel 128 --ifuel 16"

let parse_asn1_identifier_u21 : parser parse_asn1_identifier_u21_kind asn1_id_t
= let p' = parse_asn1_identifier_first in
  let _ : and_then_cases_injective p' = lemma_parse_asn1_identifier_first_injective () in
  parse_u8
  `and_then`
  p'


(*

type asn1_partial_id_t (lb : nat) (ub : nat) = 
| MK_ASN1_PARTIAL_ID :
  pid_class : asn1_id_class_t ->
  pid_flag : asn1_id_flag_t ->
  pid_value : U32.t {(lb <= (U32.v pid_value) /\ (U32.v pid_value) <= ub)} ->
  pid_buf : U8.t ->
  asn1_partial_id_t lb ub

(* Haobin : Note that there are many ways to implement this 
   and it seems that there could be a difference in known id vs unknown id
   is there a way to pe known id? *)


let parse_asn1_identifier_u8_kind = parse_u8_kind

let parse_asn1_identifier_u8 : parser parse_asn1_identifier_u8_kind asn1_id_t
= parse_u8
 `parse_synth`
  decode_asn1_identifier_u8

(*
#set-options "--query_stats"
#push-options "--z3rlimit 128"

let logand1 (b : byte) : (b' : byte {U8.v b' <= 1}) = U8.logand b 1uy
*)

let parse_asn1_identifier_head_kind = parse_u8_kind

let decode_asn1_identifier_head (b : byte) : asn1_partial_id_t 0 0
= MK_ASN1_PARTIAL_ID
  (decode_asn1_identifier_class (U8.shift_right b 6ul))
  (decode_asn1_identifier_flag (U8.rem (U8.shift_right b 5ul) 2uy))
  (0ul)
  (b)


#push-options "--z3rlimit 128"

let parse_asn1_identifier_head : parser parse_asn1_identifier_head_kind (asn1_partial_id_t 0 0)
= parse_u8
  `parse_synth`
  decode_asn1_identifier_head

    
let asn1_identifier_payload_loop_kind = strong_parser_kind 0 4 None

let parse_asn1_identifier_payload_loop (s : asn1_partial_id_t 0 0) : parser asn1_identifier_payload_loop_kind asn1_id_t
= weaken (asn1_identifier_payload_loop_kind) (parse_ret (MK_ASN1_ID s.pid_class s.pid_flag s.pid_value))

let asn1_identifier_payload_kind = strong_parser_kind 0 5 None

let update_partial_head (s : asn1_partial_id_t 0 0) (b : byte) : asn1_partial_id_t 0 0 = MK_ASN1_PARTIAL_ID s.pid_class s.pid_flag U32.zero b

let parse_asn1_identifier_payload (s : asn1_partial_id_t 0 0) : parser asn1_identifier_payload_kind asn1_id_t
= let x = U8.v (U8.rem s.pid_buf 32uy) in
  assert (x < 32);
  if x < 31 then
    weaken (asn1_identifier_payload_kind) (parse_ret (MK_ASN1_ID s.pid_class s.pid_flag (U32.uint_to_t x)))
  else
    parse_u8
    `parse_synth`
    (update_partial_head s)
    `and_then`
    (parse_asn1_identifier_payload_loop) 

(*

let parse_asn1_temp_kind = strong_parser 

let parse_asn1_temp : parser parse_asn1_temp_kind asn1_temp
=

let lemma_parse_asn1_temp_unfold input :
  Lemma (parse parse_asn1_temp input == ())
=

let serialize_asn1_temp : serializer parse_asn1_temp
=

*)
*)

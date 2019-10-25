module Test
open FStar.HyperStack.ST

open LowParse.Spec.BitSum

(* From https://tools.ietf.org/html/draft-ietf-quic-transport-23#section-17 *)

inline_for_extraction
noextract
type header_form_t =
  | Long
  | Short

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_form : enum header_form_t (bitfield uint8 1) = [
  Long, 1uy;
  Short, 0uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let fixed_bit : enum unit (bitfield uint8 1) = [
  (), 1uy;
]

inline_for_extraction
noextract
type long_packet_type_t =
  | Initial
  | ZeroRTT
  | Handshake
  | Retry

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let long_packet_type : enum long_packet_type_t (bitfield uint8 2) = [
  Initial, 0uy;
  ZeroRTT, 1uy;
  Handshake, 2uy;
  Retry, 3uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let reserved_bits : enum unit (bitfield uint8 2) = [
  (), 0uy;
]

open LowParse.Spec.BoundedInt

inline_for_extraction
noextract
type packet_number_length_t = bounded_int32 1 4

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let packet_number_length : enum packet_number_length_t (bitfield uint8 2) = [
  1ul, 0uy;
  2ul, 1uy;
  3ul, 2uy;
  4ul, 3uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let rrpp : bitsum' uint8 4 =
  BitSum' _ _ reserved_bits (fun _ -> BitSum' _ _ packet_number_length (fun _ -> BitStop ()))

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_byte : bitsum' uint8 0 =
  BitSum' _ _ header_form (function
    | Short ->
      BitSum' _ _ fixed_bit (fun _ ->
        BitField (* spin bit *) 1 (
          BitSum' _ _ reserved_bits (fun _ ->
            BitField (* key phase *) 1 (
              BitSum' _ _ packet_number_length (fun _ ->
                BitStop ()
              )
            )
          )
        )
      )
    | Long ->
      BitSum' _ _ fixed_bit (fun _ ->
        BitSum' _ _ long_packet_type (function
          | Retry -> BitField (* unused *) 4 (BitStop ())
          | _ -> rrpp
        )
      )
  )

[@filter_bitsum'_t_attr]
let filter_header_byte
: (x: FStar.UInt8.t) ->
  Tot (b: bool { b == filter_bitsum' header_byte x })
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (mk_filter_bitsum'_t' header_byte)

(*
// How to test normalization:
module T = FStar.Tactics
let f (x: FStar.UInt8.t) : Tot unit =
  assert (filter_header_byte x == true) by (
    T.norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]];
    T.fail "abc"
  )
*)

open LowParse.Spec.Bytes
open LowParse.Spec.DepLen

module FB = FStar.Bytes

noeq
type long_message_specifics =
| MInitial:
  (token: parse_bounded_vlbytes_t 0 127) -> // TODO: change bounds and use parse_vlgen
  (packet_number: parse_bounded_vlbytes_t 1 4) ->
  // TODO: add payload using deplen
  long_message_specifics
| MZeroRTT:
  (packet_number: parse_bounded_vlbytes_t 1 4) ->
  // TODO: add payload using deplen
  long_message_specifics
| MHandshake:
  (packet_number: parse_bounded_vlbytes_t 1 4) ->
  // TODO: add payload using deplen
  long_message_specifics
| MRetry:
  (unused: bitfield uint8 4) ->
  (odcid: parse_bounded_vlbytes_t 0 20) -> // TODO: change bounds to drop instead of rejecting as invalid
  // TODO: add retry token (where is its length?)
  long_message_specifics

noeq
type message_t =
| MLong:
  (version: FB.lbytes 4) ->
  (dcid: parse_bounded_vlbytes_t 0 20) ->
  (scid: parse_bounded_vlbytes_t 0 20) ->
  (spec: long_message_specifics) ->
  message_t
| MShort:
  (spin: bool) ->
  (key_phase: bool) ->
  // TODO: add destination connection ID (where is its length?)
  (packet_number: parse_bounded_vlbytes_t 1 4) ->
  message_t

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let header_of_message
  (t: Type0)
  (f: (bitsum'_type header_byte -> Tot t))
  (m: message_t)
: Tot t
= match m with
  | MShort spin key_phase packet_number ->
    let spin : bitfield uint8 1 = if spin then 1uy else 0uy in
    let key_phase : bitfield uint8 1 = if key_phase then 1uy else 0uy in
    let pn_length : packet_number_length_t = FB.len packet_number in
    f (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |)
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial _ packet_number ->
      let pn_length : packet_number_length_t = FB.len packet_number in
      f (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |)
    | MZeroRTT packet_number ->
      let pn_length : packet_number_length_t = FB.len packet_number in
      f (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |)
    | MHandshake packet_number ->
      let pn_length : packet_number_length_t = FB.len packet_number in
      f (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |)
    | MRetry unused _ ->
      f (| Long, (| (), (| Retry, (unused, ()) |) |) |)
    end

#pop-options

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let common_long_t
: Type0
= (FB.lbytes 4 & (parse_bounded_vlbytes_t 0 20 & parse_bounded_vlbytes_t 0 20))

module U32 = FStar.UInt32

#push-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let body_type
  (k' : bitsum'_key_type header_byte)
: Tot Type0
= match k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    (FB.lbytes (U32.v pn_length))
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & (parse_bounded_vlbytes_t 0 127 & FB.lbytes (U32.v pn_length)))
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & FB.lbytes (U32.v pn_length))
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & FB.lbytes (U32.v pn_length))
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (common_long_t & parse_bounded_vlbytes_t 0 20)

open LowParse.Spec.BitSum // again, for coerce

#pop-options

#push-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_message
  (k' : bitsum'_type header_byte)
  (pl: body_type (bitsum'_key_of_t header_byte k'))
: Tot (refine_with_tag (header_of_message (bitsum'_type header_byte) id) k')
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    let spin = (spin = 1uy) in
    let key_phase = (key_phase = 1uy) in
    MShort spin key_phase pl
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & (parse_bounded_vlbytes_t 0 127 & FB.lbytes (U32.v pn_length))) pl with
    | ((version, (dcid, scid)), (token, packet_number)) ->
      MLong version dcid scid (MInitial token packet_number)
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & FB.lbytes (U32.v pn_length)) pl with
    | ((version, (dcid, scid)), packet_number) ->
      MLong version dcid scid (MZeroRTT packet_number)
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & FB.lbytes (U32.v pn_length)) pl with
    | ((version, (dcid, scid)), packet_number) ->
      MLong version dcid scid (MHandshake packet_number)
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match coerce (common_long_t & parse_bounded_vlbytes_t 0 20) pl with
    | ((version, (dcid, scid)), odcid) ->
      MLong version dcid scid (MRetry unused odcid)
    end

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_body
  (k' : bitsum'_type header_byte)
  (pl: refine_with_tag (header_of_message (bitsum'_type header_byte) id) k')
: Tot (body_type (bitsum'_key_of_t header_byte k'))
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    begin match pl with
    | MShort _ _ pl -> pl
    end
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MInitial token packet_number) ->
      coerce (body_type (bitsum'_key_of_t header_byte k')) (((version, (dcid, scid)), (token, packet_number)) <: (common_long_t & (parse_bounded_vlbytes_t 0 127 & FB.lbytes (U32.v pn_length))))
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MZeroRTT packet_number) ->
      coerce (body_type (bitsum'_key_of_t header_byte k')) (((version, (dcid, scid)), packet_number) <: (common_long_t & FB.lbytes (U32.v pn_length)))
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MHandshake packet_number) ->
      coerce (body_type (bitsum'_key_of_t header_byte k')) (((version, (dcid, scid)), packet_number) <: (common_long_t & FB.lbytes (U32.v pn_length)))
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MRetry unused odcid) ->
      coerce (body_type (bitsum'_key_of_t header_byte k')) (((version, (dcid, scid)), odcid) <: (common_long_t & parse_bounded_vlbytes_t 0 20))
    end

#pop-options

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let message : bitsum = BitSum
  _
  _
  _
  header_byte
  _
  header_of_message
  (fun _ _ _ -> ())
  body_type
  (SynthCase
    #_ #_ #_ #header_byte #_ #header_of_message #body_type
    mk_message
    (fun k x y -> ())
    mk_body
    (fun k x -> ())
  )

#pop-options

let main
  (argc: Int32.t)
  (argv: LowStar.Buffer.buffer C.String.t)
: ST C.exit_code
    (requires (fun h -> True))
    (ensures (fun _ _ _ -> True))
= C.EXIT_SUCCESS

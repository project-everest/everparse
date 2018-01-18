module TLSParse.SLow
open LowParse.SLow
include TLSParse.Spec

inline_for_extraction
let parse32_protocolVersion : stateful_validator parse_protocolVersion =
  parse32_u16_st

inline_for_extraction
let parse_protocolVersion_st : parser_st parse_protocolVersion =
  parse_u16_st

#set-options "--z3rlimit 128"

inline_for_extraction
let parse32_random : stateful_validator parse_random =
  parse32_array parse32_u8_st parse_random_precond

inline_for_extraction
let parse32_maybe_cipherSuite : stateful_validator parse_maybe_cipherSuite =
  parse32_maybe_total_enum_key cipherSuite_enum (parse32_nondep_then parse32_u8_st parse32_u8_st)

inline_for_extraction
let parse32_maybe_extensionType : stateful_validator parse_maybe_extensionType =
  parse32_maybe_total_enum_key extensionType_enum parse32_u16_st

inline_for_extraction
let parse32_extension : stateful_validator parse_extension =
  (
    parse32_maybe_extensionType `parse32_nondep_then` (
    parse32_bounded_vlbytes 0ul 65535ul (parse32_seq parse32_u8_st)
  )) `parse32_synth` synth_extension

inline_for_extraction
let parse32_clientHello_legacy_session_id_t : stateful_validator parse_clientHello_legacy_session_id_t =
  parse32_vlarray parse32_u8_st clientHello_legacy_session_id_t_precond

#set-options "--initial_fuel 64 --max_fuel 64 --initial_ifuel 64 --max_ifuel 64 --z3rlimit 1024"

inline_for_extraction
let parse32_clientHello : stateful_validator parse_clientHello =
  (
    parse32_filter_st' parse_protocolVersion_st (fun (legacy_version: protocolVersion) -> legacy_version = 0x0303us) `parse32_nondep_then` (
    parse32_random `parse32_nondep_then` (
    parse32_clientHello_legacy_session_id_t `parse32_nondep_then` (
    parse32_bounded_vlbytes 2ul 65534ul (parse32_seq parse32_maybe_cipherSuite) `parse32_nondep_then` (
    parse32_bounded_vlbytes 1ul 255ul (parse32_seq parse32_u8_st) `parse32_nondep_then` (
    parse32_bounded_vlbytes 8ul 65534ul (parse32_seq parse32_extension)
  )))))) `parse32_synth` synth_clientHello

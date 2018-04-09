module Parse_alertDescription

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type alertDescription' =
  | Close_notify
  | End_of_early_data
  | Unexpected_message
  | Bad_record_mac
  | Record_overflow
  | Handshake_failure
  | Bad_certificate
  | Unsupported_certificate
  | Certificate_revoked
  | Certificate_expired
  | Certificate_unknown
  | Illegal_parameter
  | Unknown_ca
  | Access_denied
  | Decode_error
  | Decrypt_error
  | Protocol_version
  | Insufficient_security
  | Internal_error
  | Inappropriate_fallback
  | User_canceled
  | Missing_extension
  | Unsupported_extension
  | Certificate_unobtainable
  | Unrecognized_name
  | Bad_certificate_status_response
  | Bad_certificate_hash_value
  | Unknown_psk_identity
  | Unknown_alertDescription of (v:U8.t{not (L.mem v [0z; 1z; 10z; 20z; 22z; 40z; 42z; 43z; 44z; 45z; 46z; 47z; 48z; 49z; 50z; 51z; 70z; 71z; 80z; 86z; 90z; 109z; 110z; 111z; 112z; 113z; 114z; 115z])})

type alertDescription = v:alertDescription'{~(Unknown_alertDescription? v)}

inline_for_extraction val alertDescription_parser_kind_metadata : LP.parser_kind_metadata_t
inline_for_extraction let alertDescription_parser_kind = LP.strong_parser_kind 1 1 alertDescription_parser_kind_metadata

inline_for_extraction val alertDescription_parser: LP.parser alertDescription_parser_kind alertDescription
inline_for_extraction val alertDescription_parser32: LP.parser32 alertDescription_parser

inline_for_extraction val alertDescription_serializer: LP.serializer alertDescription_parser
inline_for_extraction val alertDescription_serializer32: LP.serializer32 alertDescription_serializer


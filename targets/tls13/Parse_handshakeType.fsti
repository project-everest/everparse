module Parse_handshakeType

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type handshakeType' =
  | Client_hello
  | Server_hello
  | New_session_ticket
  | Hello_retry_request
  | Encrypted_extensions
  | Certificate
  | Certificate_request
  | Certificate_verify
  | Finished
  | Key_update
  | Unknown_handshakeType of (v:U8.t{not (L.mem v [1z; 2z; 4z; 6z; 8z; 11z; 13z; 15z; 20z; 24z])})

type handshakeType = v:handshakeType'{~(Unknown_handshakeType? v)}

inline_for_extraction val handshakeType_parser_kind_metadata : LP.parser_kind_metadata_t
inline_for_extraction let handshakeType_parser_kind = LP.strong_parser_kind 1 1 handshakeType_parser_kind_metadata

inline_for_extraction val handshakeType_parser: LP.parser handshakeType_parser_kind handshakeType
inline_for_extraction val handshakeType_parser32: LP.parser32 handshakeType_parser

inline_for_extraction val handshakeType_serializer: LP.serializer handshakeType_parser
inline_for_extraction val handshakeType_serializer32: LP.serializer32 handshakeType_serializer


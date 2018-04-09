module Parse_signatureScheme

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type signatureScheme' =
  | Rsa_pkcs1_sha1
  | Rsa_pkcs1_sha256
  | Rsa_pkcs1_sha384
  | Rsa_pkcs1_sha512
  | Ecdsa_secp256r1_sha256
  | Ecdsa_secp384r1_sha384
  | Ecdsa_secp521r1_sha512
  | Rsa_pss_sha256
  | Rsa_pss_sha384
  | Rsa_pss_sha512
  | Ed25519
  | Ed448
  | Unknown_signatureScheme of (v:U16.t{not (L.mem v [513us; 1025us; 1281us; 1537us; 1027us; 1283us; 1539us; 1792us; 1793us; 1794us; 1795us; 1796us])})

type signatureScheme = v:signatureScheme'{~(Unknown_signatureScheme? v)}

inline_for_extraction val signatureScheme_parser_kind_metadata : LP.parser_kind_metadata_t
inline_for_extraction let signatureScheme_parser_kind = LP.strong_parser_kind 2 2 signatureScheme_parser_kind_metadata

inline_for_extraction val signatureScheme_parser: LP.parser signatureScheme_parser_kind signatureScheme
inline_for_extraction val signatureScheme_parser32: LP.parser32 signatureScheme_parser

inline_for_extraction val signatureScheme_serializer: LP.serializer signatureScheme_parser
inline_for_extraction val signatureScheme_serializer32: LP.serializer32 signatureScheme_serializer


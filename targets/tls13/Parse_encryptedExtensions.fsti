module Parse_encryptedExtensions

open FStar.Bytes
open Parse_extension

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type encryptedExtensions_extensions = l:list extension{0 <= L.length l /\ L.length l <= 16383}

type encryptedExtensions = {
	extensions : encryptedExtensions_extensions;
}

val bytesize: encryptedExtensions -> nat

inline_for_extraction val encryptedExtensions_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let encryptedExtensions_parser_kind = LP.strong_parser_kind 2 65537 encryptedExtensions_parser_kind_metadata

val encryptedExtensions_parser: LP.parser encryptedExtensions_parser_kind encryptedExtensions

inline_for_extraction val encryptedExtensions_parser32: LP.parser32 encryptedExtensions_parser

val encryptedExtensions_serializer: LP.serializer encryptedExtensions_parser

inline_for_extraction val encryptedExtensions_serializer32: LP.serializer32 encryptedExtensions_serializer


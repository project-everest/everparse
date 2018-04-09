module Parse_alert

open FStar.Bytes
open Parse_alertLevel
open Parse_alertDescription

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type alert = {
	level : alertLevel;
	description : alertDescription;
}

inline_for_extraction val alert_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let alert_parser_kind = LP.strong_parser_kind 2 2 alert_parser_kind_metadata

val alert_parser: LP.parser alert_parser_kind alert

inline_for_extraction val alert_parser32: LP.parser32 alert_parser

val alert_serializer: LP.serializer alert_parser

inline_for_extraction val alert_serializer32: LP.serializer32 alert_serializer


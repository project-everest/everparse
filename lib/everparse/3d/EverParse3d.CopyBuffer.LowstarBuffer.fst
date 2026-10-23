module EverParse3d.CopyBuffer.LowstarBuffer

module AP = Pulse.Lib.ArrayPtr
module U8 = FStar.UInt8
module U64 = FStar.UInt64

[@@FStar.Attributes.custard_extern "EVERPARSE_COPY_BUFFER_T"; FStar.Attributes.custard_c_header "EverParse.h"]
assume val copy_buffer_t : Type0
[@@FStar.Attributes.rename_let "EverParseStreamOf"; FStar.Attributes.custard_declare_in_c_header]
assume val stream_of : copy_buffer_t -> AP.ptr U8.t
[@@FStar.Attributes.rename_let "EverParseStreamLen"; FStar.Attributes.custard_declare_in_c_header]
assume val stream_len : copy_buffer_t -> U64.t

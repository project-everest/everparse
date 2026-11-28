module EverParse3d.CopyBuffer.LowstarExtern
module T = EverParse3d.InputStream.LowstarExtern.Types

// Legacy extern copy-buffer ABI: EverParseStreamOf returns the named record.
// The logical length parameter is unit, so no EverParseStreamLen C primitive
// and no persistent cursor projection are needed on this backend.
[@@FStar.Attributes.custard_extern "EVERPARSE_COPY_BUFFER_T"; FStar.Attributes.custard_c_header "EverParseEndianness.h"]
assume val copy_buffer_t : Type0
[@@FStar.Attributes.rename_let "EverParseStreamOf"; FStar.Attributes.custard_declare_in_c_header]
assume val stream_of : copy_buffer_t -> T.input_buffer

inline_for_extraction noextract
let stream_len (_: copy_buffer_t) : unit = ()

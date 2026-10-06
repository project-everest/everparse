module EverParse3d.CopyBuffer.LowstarExtern
module T = EverParse3d.InputStream.LowstarExtern.Types

// Legacy extern copy-buffer ABI: EverParseStreamOf returns the named record.
// The logical length parameter is unit, so no EverParseStreamLen C primitive
// and no persistent cursor projection are needed on this backend.
assume val copy_buffer_t : Type0
assume val stream_of : copy_buffer_t -> T.input_buffer

inline_for_extraction noextract
let stream_len (_: copy_buffer_t) : unit = ()

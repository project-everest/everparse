module EverParse3d.CopyBuffer.LowstarBuffer

module AP = Pulse.Lib.ArrayPtr
module U8 = FStar.UInt8
module U64 = FStar.UInt64

assume val copy_buffer_t : Type0
assume val stream_of : copy_buffer_t -> AP.ptr U8.t
assume val stream_len : copy_buffer_t -> U64.t

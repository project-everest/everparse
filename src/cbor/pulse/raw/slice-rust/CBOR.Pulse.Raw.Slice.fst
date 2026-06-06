module CBOR.Pulse.Raw.Slice
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8

// Rust backend implementation: `byte_slice0` unfolds straight to `slice uint8_t`,
// leaving no nominal abbreviation, so Rust keeps the native `&[u8]` model type.
inline_for_extraction noextract [@@noextract_to "krml"]
let byte_slice0 : (t: Type0 { t == S.slice U8.t }) = S.slice U8.t

// `byte_slice0` (hence `byte_slice1`) is transparently `slice uint8_t` here, so
// the coercions are the identity and erase at extraction.
inline_for_extraction noextract [@@noextract_to "krml"]
let to_slice (x: byte_slice1) : S.slice U8.t = x

inline_for_extraction noextract [@@noextract_to "krml"]
let of_slice (x: S.slice U8.t) : byte_slice1 = x

let to_of_slice x = ()
let of_to_slice x = ()

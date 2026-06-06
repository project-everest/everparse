module CBOR.Pulse.Raw.Slice
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8

// CBOR-owned name for the monomorphic `slice uint8_t` byte-slice type, used as
// the type of the byte-slice fields in CBOR.Pulse.Raw.EverParse.Type.
//
// `byte_slice0` is abstract here so the backend behaviour can be chosen by the
// implementation that is on the include path at extraction time:
//   - the C implementation unfolds `byte_slice0` to a *plain* (extracted) abbrev
//     `byte_slice = slice uint8_t`, which survives KaRaMeL monomorphization and
//     names the emitted C struct `byte_slice` (folding in every `slice uint8_t`
//     use, including the iterator's Serialized payload) instead of the canonical
//     `Pulse_Lib_Slice_slice__uint8_t`, avoiding the duplicate-typedef collision
//     in CDDL/COSE consumer headers;
//   - the Rust implementation unfolds `byte_slice0` straight to `slice uint8_t`,
//     leaving no nominal abbrev, so Rust keeps the native `&[u8]` model type.
//
// The `inline_for_extraction noextract [@@noextract_to "krml"]` qualifiers make
// `byte_slice0` itself unfold at its use sites and emit no KaRaMeL declaration, so
// it never competes as a name; only the C implementation's plain `byte_slice`
// abbrev does. The refinement `t == slice uint8_t` exposes the propositional
// equality used to coerce between `byte_slice0` and `slice uint8_t`.
inline_for_extraction noextract [@@noextract_to "krml"]
val byte_slice0 : (t: Type0 { t == S.slice U8.t })

// A clean named handle for the field type. Transparent (so it unfolds to
// `byte_slice0`), with the refinement on its kind re-exposed so the equality
// `byte_slice1 == slice uint8_t` is available at use sites for `coerce_eq`.
inline_for_extraction noextract [@@noextract_to "krml"]
let byte_slice1 : (t: Type0 { t == S.slice U8.t }) = byte_slice0

// Coercions between `byte_slice1` and `slice uint8_t`, provided per backend as
// the identity (in each implementation module `byte_slice0` is transparently
// `slice uint8_t`, so the identity typechecks). Declared `inline_for_extraction
// noextract [@@noextract_to "krml"]` so they inline to nothing and emit no
// KaRaMeL code — no `coerce_eq` survives in either backend. Their parameters are
// the *unrefined* `byte_slice1` / `slice uint8_t`, so a refined field value
// (e.g. `ptr: byte_slice1{...}`) is upcast automatically before coercing, keeping
// the call sites free of explicit type arguments or ascriptions.
inline_for_extraction noextract [@@noextract_to "krml"]
val to_slice (x: byte_slice1) : S.slice U8.t

inline_for_extraction noextract [@@noextract_to "krml"]
val of_slice (x: S.slice U8.t) : byte_slice1

// Round-trip lemmas exposing that the two coercions are mutual inverses. With
// the backend implementations realizing both as the identity these hold trivially;
// the SMT patterns let the construction sites (which build a field with `of_slice`
// and read it back through `to_slice` in the match predicate) discharge the
// `to_slice (of_slice s) == s` obligation automatically.
val to_of_slice (x: S.slice U8.t) : Lemma
  (ensures to_slice (of_slice x) == x)
  [SMTPat (to_slice (of_slice x))]

val of_to_slice (x: byte_slice1) : Lemma
  (ensures of_slice (to_slice x) == x)
  [SMTPat (of_slice (to_slice x))]

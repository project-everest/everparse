module CBOR.Pulse.Raw.Format.Serialize
include CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Format
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice

val cbor_serialize
  (x: cbor_raw)
  (output: S.slice U8.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
: stt SZ.t
    (exists* v . cbor_match pm x y ** pts_to output v ** pure (Seq.length (serialize_cbor y) <= SZ.v (S.len output)))
    (fun res -> exists* v . cbor_match pm x y ** pts_to output v ** pure (
      let s = serialize_cbor y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))
    ))

noextract [@@noextract_to "krml"]
let cbor_size_post
  (bound: SZ.t)
  (y: raw_data_item)
  (res: SZ.t)
: Tot prop
=
      let s = Seq.length (serialize_cbor y) in
      (SZ.v res == 0 <==> s > SZ.v bound) /\
      (SZ.v res > 0 ==> SZ.v res == s)

val cbor_size
  (x: cbor_raw)
  (bound: SZ.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
: stt SZ.t
    (cbor_match pm x y)
    (fun res -> cbor_match pm x y ** pure (
      cbor_size_post bound y res
    ))

noextract [@@noextract_to "krml"]
let cbor_serialize_tag_postcond
  (tag: raw_uint64)
  (output: S.slice U8.t)
  (res: SZ.t)
  (v': Seq.seq U8.t)
: Tot prop
= let s = serialize_cbor_tag tag in
  let len = Seq.length s in
  SZ.v (S.len output) == Seq.length v' /\
  SZ.v res <= Seq.length v' /\
  (res == 0sz <==> len > Seq.length v') /\
  (len <= Seq.length v' ==> Seq.slice v' 0 (SZ.v res) == s)

val cbor_serialize_tag
  (tag: raw_uint64)
  (output: S.slice U8.t)
: stt SZ.t
  (exists* v . pts_to output v)
  (fun res -> exists* v . pts_to output v ** pure (cbor_serialize_tag_postcond tag output res v))

let cbor_serialize_array_precond
  (len: raw_uint64)
  (l: list raw_data_item)
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= SZ.v off <= Seq.length v /\
  Seq.slice v 0 (SZ.v off) == serialize_cbor_list l /\
  List.Tot.length l == U64.v len.value

let cbor_serialize_array_postcond
  (len: raw_uint64)
  (l: list raw_data_item)
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= List.Tot.length l == U64.v len.value /\
  SZ.v res <= Seq.length v /\
  (res == 0sz <==> Seq.length (serialize_cbor (Array len l)) > Seq.length v) /\
  (SZ.v res > 0 ==> Seq.slice v 0 (SZ.v res) `Seq.equal` serialize_cbor (Array len l))

val cbor_serialize_array
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list raw_data_item))
  (off: SZ.t)
: stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_serialize_array_precond len l off v)
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_serialize_array_postcond len l res v)
  )

let cbor_serialize_string_precond
  (ty: major_type_byte_string_or_text_string)
  (off: raw_uint64)
  (v: Seq.seq U8.t)
: Tot prop
= U64.v off.value <= Seq.length v /\
  (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct (Seq.slice v 0 (U64.v off.value)))

let cbor_serialize_string_postcond
  (ty: major_type_byte_string_or_text_string)
  (off: raw_uint64)
  (v: Seq.seq U8.t)
  (res: SZ.t)
  (v': Seq.seq U8.t)
: Tot prop
= cbor_serialize_string_precond ty off v /\
  begin let l = Seq.slice v 0 (U64.v off.value) in
  Seq.length v' == Seq.length v /\
  SZ.v res <= Seq.length v' /\
  (res == 0sz <==> Seq.length (serialize_cbor (String ty off l)) > Seq.length v') /\
  (SZ.v res > 0 ==> Seq.slice v' 0 (SZ.v res) `Seq.equal` serialize_cbor (String ty off l))
  end

inline_for_extraction
let cbor_serialize_string_t =
  (ty: major_type_byte_string_or_text_string) ->
  (off: raw_uint64) ->
  (out: S.slice U8.t) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
  (pts_to out v **
    pure (cbor_serialize_string_precond ty off v)
  )
  (fun res -> exists* v' .
    pts_to out v' **
    pure (cbor_serialize_string_postcond ty off v res v')
  )

val cbor_serialize_string (_: unit) : cbor_serialize_string_t

let cbor_serialize_map_precond
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= SZ.v off <= Seq.length v /\
  Seq.slice v 0 (SZ.v off) == serialize_cbor_map l /\
  List.Tot.length l == U64.v len.value

let cbor_serialize_map_postcond
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= List.Tot.length l == U64.v len.value /\
  SZ.v res <= Seq.length v /\
  (res == 0sz <==> Seq.length (serialize_cbor (Map len l)) > Seq.length v) /\
  (SZ.v res > 0 ==> Seq.slice v 0 (SZ.v res) `Seq.equal` serialize_cbor (Map len l))

val cbor_serialize_map
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off: SZ.t)
: stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_serialize_map_precond len l off v)
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_serialize_map_postcond len l res v)
  )

module CBOR.Pulse.Raw.EverParse.Det.Serialize

open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* ============================================================
   Postconditions over raw_data_item.
   ============================================================ *)

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

val cbor_serialize_array_precond
  (len: raw_uint64)
  (l: list raw_data_item)
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop

val cbor_serialize_array_postcond
  (len: raw_uint64)
  (l: list raw_data_item)
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop

val cbor_serialize_string_precond
  (ty: major_type_byte_string_or_text_string)
  (off: raw_uint64)
  (v: Seq.seq U8.t)
: Tot prop

val cbor_serialize_string_postcond
  (ty: major_type_byte_string_or_text_string)
  (off: raw_uint64)
  (v: Seq.seq U8.t)
  (res: SZ.t)
  (v': Seq.seq U8.t)
: Tot prop

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

val cbor_serialize_map_precond
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop

val cbor_serialize_map_postcond
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop

(* Operations *)

val cbor_serialize_tag
  (tag: raw_uint64)
  (output: S.slice U8.t)
: stt SZ.t
  (exists* v . pts_to output v)
  (fun res -> exists* v . pts_to output v ** pure (cbor_serialize_tag_postcond tag output res v))

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

val cbor_serialize_string (_: unit) : cbor_serialize_string_t

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

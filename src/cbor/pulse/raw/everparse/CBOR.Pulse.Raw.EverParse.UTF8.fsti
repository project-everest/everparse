module CBOR.Pulse.Raw.EverParse.UTF8
#lang-pulse
include CBOR.Spec.API.UTF8
open Pulse.Lib.Pervasives
open CBOR.Spec.Constants
open CBOR.Spec.Raw.EverParse
open LowParse.Pulse.Combinators
open LowParse.Pulse.SeqBytes

module U8 = FStar.UInt8
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

val impl_correct
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt bool
    (pts_to s #p v)
    (fun res -> pts_to s #p v ** pure (res == correct v))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn impl_lseq_utf8_correct (ty: major_type_byte_string_or_text_string) (n: SZ.t) :
  validate_filter_test_t #_ #_ #_ (serialize_lseq_bytes (SZ.v n)) (lseq_utf8_correct ty (SZ.v n))
= (x: _) (#pm: _) (#v: _)
{
  if (ty = cbor_major_type_byte_string) {
    true
  } else {
    pts_to_serialized_lseq_bytes_elim (SZ.v n) _ x _;
    let res = impl_correct x;
    Trade.elim _ _;
    res
  }
}

module LowParse.Pulse.FLData
#lang-pulse
include LowParse.Spec.FLData
include LowParse.Pulse.Base
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT

inline_for_extraction
fn validate_fldata_strong
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (w: validator p)
  (len: SZ.t)
: validator #_ #_ (parse_fldata_strong s (SZ.v len))
=
  (input: _)
  (poffset: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  S.pts_to_len input;
  let off = !poffset;
  if (SZ.lt (SZ.sub (S.len input) off) len) {
    false
  } else {
    let off_len = SZ.add off len;
    let (inl, _) = S.split_trade input off_len;
    let res = w inl poffset;
    Trade.elim _ _;
    let off' = !poffset;
    (res && (off' = off_len))
  }
}

ghost
fn pts_to_serialized_fldata_strong_intro
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (length: nat)
  (input: S.slice byte)
  (#pm: perm)
  (#v: t)
requires
  pts_to_serialized s input #pm v ** pure (SZ.v (S.len input) == length)
ensures exists* v' .
  pts_to_serialized (serialize_fldata_strong s length) input #pm v' ** pure (v == (v' <: t))
{
  unfold (pts_to_serialized s input #pm v);
  S.pts_to_len input;
  let v' : parse_fldata_strong_t s length = v;
  fold (pts_to_serialized (serialize_fldata_strong s length) input #pm v')
}

ghost
fn pts_to_serialized_fldata_strong_elim
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (length: nat)
  (input: S.slice byte)
  (#pm: perm)
  (#v: parse_fldata_strong_t s length)
requires
  pts_to_serialized (serialize_fldata_strong s length) input #pm v
ensures
  pts_to_serialized s input #pm (v <: t) ** pure (SZ.v (S.len input) == length)
{
  unfold (pts_to_serialized (serialize_fldata_strong s length) input #pm v);
  S.pts_to_len input;
  fold (pts_to_serialized s input #pm (v <: t))
}

ghost
fn pts_to_serialized_fldata_strong_intro_trade
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (length: nat)
  (input: S.slice byte)
  (#pm: perm)
  (#v: t)
requires
  pts_to_serialized s input #pm v ** pure (SZ.v (S.len input) == length)
ensures exists* v' .
  pts_to_serialized (serialize_fldata_strong s length) input #pm v' ** pure (v == (v' <: t)) **
  Trade.trade
    (pts_to_serialized (serialize_fldata_strong s length) input #pm v')
    (pts_to_serialized s input #pm v)
{
  pts_to_serialized_fldata_strong_intro s length input;
  with v' . assert (pts_to_serialized (serialize_fldata_strong s length) input #pm v');
  ghost fn aux (_: unit)
  requires emp ** pts_to_serialized (serialize_fldata_strong s length) input #pm v'
  ensures pts_to_serialized s input #pm v
  {
    pts_to_serialized_fldata_strong_elim s length input
  };
  Trade.intro _ _ _ aux
}

ghost
fn pts_to_serialized_fldata_strong_elim_trade
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (length: nat)
  (input: S.slice byte)
  (#pm: perm)
  (#v: parse_fldata_strong_t s length)
requires
  pts_to_serialized (serialize_fldata_strong s length) input #pm v
ensures
  pts_to_serialized s input #pm (v <: t) ** pure (SZ.v (S.len input) == length) **
  Trade.trade
    (pts_to_serialized s input #pm (v <: t))
    (pts_to_serialized (serialize_fldata_strong s length) input #pm v)
{
  pts_to_serialized_fldata_strong_elim s length input;
  ghost fn aux (_: unit)
  requires emp ** pts_to_serialized s input #pm v
  ensures pts_to_serialized (serialize_fldata_strong s length) input #pm v
  {
    pts_to_serialized_fldata_strong_intro s length input
  };
  Trade.intro _ _ _ aux
}

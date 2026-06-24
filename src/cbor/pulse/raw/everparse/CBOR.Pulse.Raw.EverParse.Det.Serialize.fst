module CBOR.Pulse.Raw.EverParse.Det.Serialize
#lang-pulse

friend CBOR.Spec.Raw.Format

open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Pulse.Base
open LowParse.Spec.Base

module RawSerialize = CBOR.Pulse.Raw.EverParse.Serialize
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module Swap = Pulse.Lib.Swap.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* ============================================================
   Postconditions over raw_data_item — bodies live in fsti
   ============================================================ *)

(* ============================================================
   cbor_serialize_tag (ported from old Format.Serialize:2126-2148)
   ============================================================ *)

#push-options "--z3rlimit 32"
fn cbor_serialize_tag
  (tag: raw_uint64)
  (output: S.slice U8.t)
norewrite
requires
  (exists* v . pts_to output v)
returns res: SZ.t
ensures
  (exists* v . pts_to output v ** pure (cbor_serialize_tag_postcond tag output res v))
{
  serialize_cbor_tag_length tag;
  let h = raw_uint64_as_argument cbor_major_type_tagged tag;
  let mut slen = S.len output;
  let fits = RawSerialize.size_header h slen;
  S.pts_to_len output;
  if (fits) {
    let res = RawSerialize.write_header h output 0sz;
    S.pts_to_len output;
    res
  } else {
    0sz
  }
}
#pop-options

(* ============================================================
   Common utility: shape lemmas for splice
   ============================================================ *)

let seq_length_append_slice_left
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
= assert (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1)

inline_for_extraction noextract [@@noextract_to "krml"]
let sz_zero : SZ.t = 0sz

(* ============================================================
   cbor_serialize_array (ported from old Format.Serialize:2160-2302)
   ============================================================ *)

#push-options "--z3rlimit 64"

let cbor_serialize_array_postcond_zero
  (len: raw_uint64)
  (l: list raw_data_item)
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Lemma
  (requires (
    cbor_serialize_array_precond len l off v /\
    Seq.length (serialize_header (raw_uint64_as_argument cbor_major_type_array len)) > Seq.length v - SZ.v off
  ))
  (ensures (
    cbor_serialize_array_postcond len l sz_zero v
  ))
= serialize_array_eq len l;
  ()

let cbor_serialize_array_postcond_nonzero
  (len: raw_uint64)
  (l: list raw_data_item)
  (off: SZ.t)
  (v: Seq.seq U8.t)
  (res: SZ.t)
  (v2: Seq.seq U8.t)
  (v': Seq.seq U8.t)
: Lemma
  (requires (
    cbor_serialize_array_precond len l off v /\
    SZ.v res == Seq.length (Seq.append (serialize_header (raw_uint64_as_argument cbor_major_type_array len)) (serialize_cbor_list l)) /\
    Seq.length v == SZ.v res + Seq.length v2 /\
    v' == Seq.append (Seq.append (serialize_header (raw_uint64_as_argument cbor_major_type_array len)) (serialize_cbor_list l)) v2
  ))
  (ensures (
    cbor_serialize_array_postcond len l res v'
  ))
=
  serialize_array_eq len l;
  let h = raw_uint64_as_argument cbor_major_type_array len in
  serialize_length serialize_header h;
  seq_length_append_slice_left (Seq.append (serialize_header h) (serialize_cbor_list l)) v2;
  ()

#restart-solver

let cbor_serialize_array_post
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list raw_data_item))
  (off: SZ.t)
  (res: SZ.t)
: Tot slprop
=
  exists* v .
    pts_to out v **
    pure (cbor_serialize_array_postcond len l res v)

#restart-solver

fn cbor_serialize_array'
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list raw_data_item))
  (off: SZ.t)
norewrite
requires
  exists* v . pts_to out v **
    pure (cbor_serialize_array_precond len l off v)
returns res: SZ.t
ensures
  cbor_serialize_array_post len out l off res
{
  let sq_len : squash (SZ.v off == Seq.length (serialize_cbor_list l)) = ();
  with v . assert (pts_to out v);
  S.pts_to_len out;
  Seq.lemma_split v (SZ.v off);
  serialize_array_eq len l;
  let slen = S.len out;
  let mut rem = (SZ.sub slen off <: SZ.t);
  let h = raw_uint64_as_argument cbor_major_type_array len;
  serialize_length serialize_header h;
  let hfits = RawSerialize.size_header h rem;
  if (hfits) {
    let llen = RawSerialize.write_header h out off;
    let sp = S.split out llen;
    match sp {
      Mktuple2 sp1 sp2 -> {
        S.pts_to_len sp1;
        with v1 . assert (pts_to sp1 v1);
        with v2g . assert (pts_to sp2 v2g);
        Seq.lemma_split v1 (SZ.v off);
        assert (pure (Seq.equal v1 (Seq.append (serialize_cbor_list l) (serialize_header h))));
        rewrite (pts_to sp1 v1) as (pts_to sp1 (Seq.append (serialize_cbor_list l) (serialize_header h)));
        Swap.slice_swap' sp1 off (serialize_cbor_list l) (serialize_header h);
        seq_length_append_slice_left (Seq.append (serialize_header h) (serialize_cbor_list l)) v2g;
        S.join sp1 sp2 out;
        with v' . assert (pts_to out v');
        Classical.move_requires (cbor_serialize_array_postcond_nonzero len l off v llen v2g) v';
        assert (pure (cbor_serialize_array_postcond len l llen v'));
        fold (cbor_serialize_array_post len out l off llen);
        llen
      }
    }
  } else {
    cbor_serialize_array_postcond_zero len (Ghost.reveal l) off v;
    fold (cbor_serialize_array_post len out l off sz_zero);
    sz_zero
  }
}

fn cbor_serialize_array
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list raw_data_item))
  (off: SZ.t)
norewrite
requires
  exists* v . pts_to out v **
    pure (cbor_serialize_array_precond len l off v)
returns res: SZ.t
ensures
  exists* v .
    pts_to out v **
    pure (cbor_serialize_array_postcond len l res v)
{
  let res = cbor_serialize_array' len out l off;
  unfold (cbor_serialize_array_post len out l off res);
  res
}

#restart-solver

(* ============================================================
   cbor_serialize_string (ported from old Format.Serialize:2306-2347)
   ============================================================ *)

let cbor_serialize_string_postcond_nonzero
  (ty: major_type_byte_string_or_text_string)
  (off: raw_uint64)
  (v: Seq.seq U8.t)
  (res: SZ.t)
  (v2: Seq.seq U8.t)
  (v': Seq.seq U8.t)
: Lemma
  (requires (
    cbor_serialize_string_precond ty off v /\
    SZ.v res == Seq.length (Seq.append (serialize_header (raw_uint64_as_argument ty off)) (Seq.slice v 0 (U64.v off.value))) /\
    Seq.length v == SZ.v res + Seq.length v2 /\
    Seq.length v' == Seq.length v /\
    v' == Seq.append (Seq.append (serialize_header (raw_uint64_as_argument ty off)) (Seq.slice v 0 (U64.v off.value))) v2
  ))
  (ensures (
    cbor_serialize_string_postcond ty off v res v'
  ))
=
  serialize_string_eq ty off (Seq.slice v 0 (U64.v off.value));
  let h = raw_uint64_as_argument ty off in
  serialize_length serialize_header h;
  seq_length_append_slice_left (Seq.append (serialize_header h) (Seq.slice v 0 (U64.v off.value))) v2;
  ()

fn cbor_serialize_string
  (_: unit)
: cbor_serialize_string_t
=
  (ty: _)
  (off: _)
  (out: _)
  (#v: _)
{
  with v . assert (pts_to out v);
  S.pts_to_len out;
  Seq.lemma_split v (U64.v off.value);
  let w = Ghost.hide (Seq.slice v 0 (U64.v off.value));
  serialize_string_eq ty off w;
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let soff = SZ.uint64_to_sizet off.value;
  let slen = S.len out;
  let mut rem = (SZ.sub slen soff <: SZ.t);
  let h = raw_uint64_as_argument ty off;
  serialize_length serialize_header h;
  let hfits = RawSerialize.size_header h rem;
  if (hfits) {
    let llen = RawSerialize.write_header h out soff;
    let sp = S.split out llen;
    match sp {
      Mktuple2 sp1 sp2 -> {
        S.pts_to_len sp1;
        with v1 . assert (pts_to sp1 v1);
        with v2g . assert (pts_to sp2 v2g);
        Seq.lemma_split v1 (SZ.v soff);
        assert (pure (Seq.equal v1 (Seq.append w (serialize_header h))));
        rewrite (pts_to sp1 v1) as (pts_to sp1 (Seq.append w (serialize_header h)));
        Swap.slice_swap' sp1 soff w (serialize_header h);
        seq_length_append_slice_left (Seq.append (serialize_header h) w) v2g;
        S.join sp1 sp2 out;
        with v' . assert (pts_to out v');
        Classical.move_requires (cbor_serialize_string_postcond_nonzero ty off v llen v2g) v';
        llen
      }
    }
  } else {
    sz_zero
  }
}

(* ============================================================
   cbor_serialize_map (ported from old Format.Serialize:2349-2490)
   ============================================================ *)

let cbor_serialize_map_postcond_zero
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Lemma
  (requires (
    cbor_serialize_map_precond len l off v /\
    Seq.length (serialize_header (raw_uint64_as_argument cbor_major_type_map len)) > Seq.length v - SZ.v off
  ))
  (ensures (
    cbor_serialize_map_postcond len l sz_zero v
  ))
= serialize_map_eq len l;
  ()

let cbor_serialize_map_postcond_nonzero
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (v: Seq.seq U8.t)
  (res: SZ.t)
  (v2: Seq.seq U8.t)
  (v': Seq.seq U8.t)
: Lemma
  (requires (
    cbor_serialize_map_precond len l off v /\
    SZ.v res == Seq.length (Seq.append (serialize_header (raw_uint64_as_argument cbor_major_type_map len)) (serialize_cbor_map l)) /\
    Seq.length v == SZ.v res + Seq.length v2 /\
    v' == Seq.append (Seq.append (serialize_header (raw_uint64_as_argument cbor_major_type_map len)) (serialize_cbor_map l)) v2
  ))
  (ensures (
    cbor_serialize_map_postcond len l res v'
  ))
=
  serialize_map_eq len l;
  let h = raw_uint64_as_argument cbor_major_type_map len in
  serialize_length serialize_header h;
  seq_length_append_slice_left (Seq.append (serialize_header h) (serialize_cbor_map l)) v2;
  ()

#restart-solver

let cbor_serialize_map_post
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off: SZ.t)
  (res: SZ.t)
: Tot slprop
=
  exists* v .
    pts_to out v **
    pure (cbor_serialize_map_postcond len l res v)

#pop-options

#push-options "--z3rlimit 256"

#restart-solver

fn cbor_serialize_map'
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off: SZ.t)
norewrite
requires
  exists* v . pts_to out v **
    pure (cbor_serialize_map_precond len l off v)
returns res: SZ.t
ensures
  cbor_serialize_map_post len out l off res
{
  let sq_len : squash (SZ.v off == Seq.length (serialize_cbor_map l)) = ();
  with v . assert (pts_to out v);
  S.pts_to_len out;
  Seq.lemma_split v (SZ.v off);
  serialize_map_eq len l;
  let slen = S.len out;
  let mut rem = (SZ.sub slen off <: SZ.t);
  let h = raw_uint64_as_argument cbor_major_type_map len;
  serialize_length serialize_header h;
  let hfits = RawSerialize.size_header h rem;
  if (hfits) {
    let llen = RawSerialize.write_header h out off;
    let sp = S.split out llen;
    match sp {
      Mktuple2 sp1 sp2 -> {
        S.pts_to_len sp1;
        with v1 . assert (pts_to sp1 v1);
        with v2 . assert (pts_to sp2 v2);
        Seq.lemma_split v1 (SZ.v off);
        assert (pure (Seq.equal v1 (Seq.append (serialize_cbor_map l) (serialize_header h))));
        rewrite (pts_to sp1 v1) as (pts_to sp1 (Seq.append (serialize_cbor_map l) (serialize_header h)));
        Swap.slice_swap' sp1 off (serialize_cbor_map l) (serialize_header h);
        seq_length_append_slice_left (Seq.append (serialize_header h) (serialize_cbor_map l)) v2;
        S.join sp1 sp2 out;
        with v' . assert (pts_to out v');
        cbor_serialize_map_postcond_nonzero len l off v llen v2 v';
        assert (pure (cbor_serialize_map_postcond len l llen v'));
        fold (cbor_serialize_map_post len out l off llen);
        llen
      }
    }
  } else {
    cbor_serialize_map_postcond_zero len (Ghost.reveal l) off v;
    fold (cbor_serialize_map_post len out l off sz_zero);
    sz_zero
  }
}

fn cbor_serialize_map
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off: SZ.t)
norewrite
requires
  exists* v . pts_to out v **
    pure (cbor_serialize_map_precond len l off v)
returns res: SZ.t
ensures
  exists* v .
    pts_to out v **
    pure (cbor_serialize_map_postcond len l res v)
{
  let res = cbor_serialize_map' len out l off;
  unfold (cbor_serialize_map_post len out l off res);
  res
}

#pop-options


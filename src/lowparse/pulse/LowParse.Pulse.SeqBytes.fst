module LowParse.Pulse.SeqBytes
#lang-pulse
include LowParse.Pulse.Base
include LowParse.Spec.SeqBytes
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

ghost fn pts_to_serialized_lseq_bytes_intro
  (n: nat)
  (p: perm)
  (s: S.slice byte)
  (v: Seq.seq byte)
requires
  (pts_to s #p v ** pure (Seq.length v == n))
ensures
  exists* (v': Seq.lseq byte n) . pts_to_serialized (serialize_lseq_bytes n) s #p v' **
    Trade.trade (pts_to_serialized (serialize_lseq_bytes n) s #p v') (pts_to s #p v) **
    pure (v == v')
{
  let v' : Seq.lseq byte n = v;
  Trade.rewrite_with_trade
    (pts_to s #p v)
    (pts_to_serialized (serialize_lseq_bytes n) s #p v')
}

ghost fn pts_to_serialized_lseq_bytes_elim
  (n: nat)
  (p: perm)
  (s: S.slice byte)
  (v: Seq.lseq byte n)
requires
  pts_to_serialized (serialize_lseq_bytes n) s #p v
ensures
  exists* (v': Seq.seq byte) . pts_to s #p v' **
    Trade.trade (pts_to s #p v') (pts_to_serialized (serialize_lseq_bytes n) s #p v) **
    pure (v' == v)
{
  let v' : Seq.seq byte = v;
  Trade.rewrite_with_trade
    (pts_to_serialized (serialize_lseq_bytes n) s #p v)
    (pts_to s #p v')
}

let pts_to_seqbytes
  (n: nat)
  (s: with_perm (S.slice byte))
  (v: Seq.lseq byte n)
: Tot slprop
= exists* (v': Seq.seq byte) . pts_to s.v #s.p v' ** pure (v' == v)

ghost
fn pts_to_seqbytes_intro
  (n: nat)
  (p: perm)
  (s: S.slice byte)
  (v: bytes)
  (res: with_perm (S.slice byte))
requires
  pts_to s #p v ** pure (Seq.length v == n /\ res.v == s /\ res.p == p)
returns v': Ghost.erased (Seq.lseq byte n)
ensures
  pts_to_seqbytes n res v' **
  Trade.trade
    (pts_to_seqbytes n res v')
    (pts_to s #p v) **
  pure (v == Ghost.reveal v')
{
  let v' : Seq.lseq byte n = v;
  rewrite each s as res.v;
  fold (pts_to_seqbytes n res v');
  intro
    (Trade.trade
      (pts_to_seqbytes n res v')
      (pts_to s #p v)
    )
    #emp
    fn _
  {
    unfold (pts_to_seqbytes n res v');
    rewrite each res.v as s;
  };
  v'
}

inline_for_extraction
fn l2r_write_lseq_bytes_copy
  (n: Ghost.erased nat)
: l2r_writer #_ #_ (pts_to_seqbytes n) #_ #_ (serialize_lseq_bytes n)
=
  (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  unfold (pts_to_seqbytes n x' x);
  pts_to_len out;
  pts_to_len x'.v;
  let length = S.len x'.v;
  let sp11, sp12 = S.split out offset;
  with v12 . assert (pts_to sp12 v12);
  let sp21, sp22 = S.split sp12 length;
  pts_to_len sp21;
  S.copy sp21 x'.v;
  fold (pts_to_seqbytes n x' x);
  S.join sp21 sp22 sp12;
  S.join sp11 sp12 out;
  SZ.add offset length;
}

inline_for_extraction
fn compute_remaining_size_lseq_bytes_copy
  (n: Ghost.erased nat)
: compute_remaining_size #_ #_ (pts_to_seqbytes n) #_ #_ (serialize_lseq_bytes n)
=
  (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  unfold (pts_to_seqbytes n x' x);
  pts_to_len x'.v;
  fold (pts_to_seqbytes n x' x);
  let length = S.len x'.v;
  let cur = !out;
  if (SZ.lt cur length) {
    false
  } else {
    out := SZ.sub cur length;
    true
  }
}

module LowParse.Pulse.SeqBytes
include LowParse.Pulse.Base
include LowParse.Spec.SeqBytes
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

let pts_to_seqbytes
  (n: nat)
  (s: with_perm (S.slice byte))
  (v: Seq.lseq byte n)
: Tot slprop
= exists* (v': Seq.seq byte) . pts_to s.v #s.p v' ** pure (v' == v)

inline_for_extraction
```pulse
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
  let sp1 = S.split out offset;
  match sp1 {
    SlicePair sp11 sp12 -> {
      with v12 . assert (pts_to sp12 v12);
      let sp2 = S.split sp12 length;
      match sp2 {
        SlicePair sp21 sp22 -> {
          pts_to_len sp21;
          S.copy sp21 x'.v;
          fold (pts_to_seqbytes n x' x);
          S.join sp21 sp22 sp12;
          S.join sp11 sp12 out;
          SZ.add offset length;
        }
      }
    }
  }
}
```

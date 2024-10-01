module LowParse.Pulse.SeqBytes
include LowParse.Pulse.Base
include LowParse.Spec.SeqBytes
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

let pts_to_seqbytes
  (n: nat)
  (p: perm)
  (s: S.slice byte)
  (v: Seq.lseq byte n)
: Tot slprop
= exists* (v': Seq.seq byte) . S.pts_to s #p v' ** pure (v' == v)

inline_for_extraction
```pulse
fn l2r_write_lseq_bytes_copy
  (n: Ghost.erased nat)
  (p: perm)
: l2r_writer #_ #_ (pts_to_seqbytes n p) #_ #_ (serialize_lseq_bytes n)
=
  (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  unfold (pts_to_seqbytes n p x' x);
  S.pts_to_len out;
  S.pts_to_len x';
  let length = S.len x';
  let sp1 = S.split true out offset;
  match sp1 {
    SlicePair sp11 sp12 -> {
      unfold (S.split_post out 1.0R v offset sp1);
      unfold (S.split_post' out 1.0R v offset sp11 sp12);
      with v12 . assert (S.pts_to sp12 v12);
      let sp2 = S.split true sp12 length;
      match sp2 {
        SlicePair sp21 sp22 -> {
          unfold (S.split_post sp12 1.0R v12 length sp2);
          unfold (S.split_post' sp12 1.0R v12 length sp21 sp22);
          S.pts_to_len sp21;
          S.copy sp21 x';
          fold (pts_to_seqbytes n p x' x);
          S.join sp21 sp22 sp12;
          S.join sp11 sp12 out;
          SZ.add offset length;
        }
      }
    }
  }
}
```

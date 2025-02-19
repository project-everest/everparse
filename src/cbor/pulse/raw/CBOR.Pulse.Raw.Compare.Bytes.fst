module CBOR.Pulse.Raw.Compare.Bytes
#lang-pulse
include CBOR.Pulse.Raw.Compare.Base
include CBOR.Spec.Raw.Format
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice
module SM = Pulse.Lib.SeqMatch.Util
module SZ = FStar.SizeT
module I16 = FStar.Int16
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8

let uint8_compare (x1 x2: U8.t) : Tot int =
  if U8.lt x1 x2
  then (-1)
  else if U8.gt x1 x2
  then 1
  else 0

let rec bytes_lex_compare_lex_compare
  (s1 s2: Seq.seq U8.t)
: Lemma
  (ensures (same_sign (bytes_lex_compare s1 s2) (lex_compare uint8_compare (Seq.seq_to_list s1) (Seq.seq_to_list s2))))
  (decreases (Seq.length s1))
= if Seq.length s1 = 0 || Seq.length s2 = 0
  then ()
  else
    let _ = Seq.cons_head_tail s1 in
    let _ = Seq.cons_head_tail s2 in    
    let c = uint8_compare (Seq.index s1 0) (Seq.index s2 0) in
    if c = 0
    then bytes_lex_compare_lex_compare (Seq.tail s1) (Seq.tail s2)
    else ()

fn impl_uint8_compare (_: unit)
: impl_compare_scalar_t u#0 #_ uint8_compare
= (x1: _)
  (x2: _)
{
  if (U8.lt x1 x2) {
    (-1s)
  } else if (U8.gt x1 x2) {
    1s
  } else {
    0s
  }
}

fn lex_compare_bytes
  (s1: S.slice U8.t)
  (s2: S.slice U8.t)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased (Seq.seq U8.t))
  (#v2: Ghost.erased (Seq.seq U8.t))
requires
  pts_to s1 #p1 v1 ** pts_to s2 #p2 v2
returns res: I16.t
ensures
  pts_to s1 #p1 v1 ** pts_to s2 #p2 v2 ** pure (
    same_sign (I16.v res) (bytes_lex_compare v1 v2)
  )
{
  bytes_lex_compare_lex_compare v1 v2;
  lex_compare_slices uint8_compare (impl_uint8_compare ()) s1 s2
}


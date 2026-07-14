module LowParse.Pulse.SeqBytes
#lang-pulse
include LowParse.Pulse.Base
include LowParse.Spec.SeqBytes
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module PPB = LowParse.PulseParse.Base
module PPBY = LowParse.PulseParse.Bytes
module LPS = LowParse.Pulse.Base
module PPC = LowParse.PulseParse.Combinators
module LPC = LowParse.Pulse.Combinators
module PPCV = LowParse.PulseParse.VLData
module U32 = FStar.UInt32
module M = FStar.Math.Lemmas
module LPPI = LowParse.Pulse.Int

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

(* ---------------------------------------------------------------------------
   Copyful (owned, freeable) fixed-length-bytes combinators over [Seq.seq byte].

   These are the [Seq]-native analogs of the [FStar.Bytes] flbytes block in
   [LowParse.PulseParse.Bytes] (validate_flbytes / vmatch_copy_bytes /
   flbytes_conv / free_copy_bytes / copyful_parse_flbytes /
   l2r_safe_writer_flbytes / l2r_safe_size_flbytes). They let if-then-else
   discriminant tags be emitted as a registered, *copyful, non-leaf* type whose
   high-level value is a plain [Seq.lseq byte sz] (no [FStar.Bytes]), as required
   to make QuackyDucky's TypeIfeq sound and -pulse-ready.

   The freeable low-level representation is reused verbatim from the FStar.Bytes
   library: [PPBY.lvec byte] (a [Pulse.Lib.Vec] plus a refined runtime length)
   and the content-agnostic [PPBY.alloc_and_copy]; only the vmatch (which here
   ranges over [Seq.seq byte] instead of [B32.bytes]) and the vmatch-folding
   combinators are Seq-specific. The conversion of [Seq.seq byte] to its
   serialized bytes is the identity, so all the [B32.reveal _] coercions of the
   FStar.Bytes version disappear. *)

inline_for_extraction
let validate_seq_flbytes
  (sz: nat { sz < 4294967296 })
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: validator (parse_lseq_bytes sz)
= validate_total_constant_size (parse_lseq_bytes sz) sz_sz

let vmatch_copy_seqbytes
  (x: PPBY.lvec byte)
  (v: Seq.seq byte)
: slprop
= V.pts_to x.lvec_vec v **
  pure (V.is_full_vec x.lvec_vec)

let seq_flbytes_conv
  (sz: nat { sz < 4294967296 })
  (b: Seq.seq byte)
: GTot (option (Seq.lseq byte sz))
= if Seq.length b = sz then Some (b <: Seq.lseq byte sz) else None

inline_for_extraction
fn free_copy_seqbytes
  (x: PPBY.lvec byte)
  (#v: Ghost.erased (Seq.seq byte))
requires
  vmatch_copy_seqbytes x v
ensures
  emp
{
  unfold (vmatch_copy_seqbytes x v);
  V.free x.lvec_vec
}

inline_for_extraction
fn copyful_parse_seq_flbytes
  (sz: nat { sz < 4294967296 })
: PPB.copyful_parse #(PPBY.lvec byte) #(Seq.seq byte) #(Seq.lseq byte sz) vmatch_copy_seqbytes (parse_lseq_bytes sz) (seq_flbytes_conv sz)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (Seq.lseq byte sz))
{
  PPB.pts_to_parsed_elim input;
  with w. assert (S.pts_to input #pm w);
  let vc = PPBY.alloc_and_copy input;
  Trade.elim (S.pts_to input #pm w) (PPB.pts_to_parsed (parse_lseq_bytes sz) input #pm v);
  rewrite (V.pts_to vc.lvec_vec w) as (V.pts_to vc.lvec_vec (Ghost.reveal v));
  fold (vmatch_copy_seqbytes vc v);
  PPB.intro_vmatch_conv vmatch_copy_seqbytes (seq_flbytes_conv sz) vc (Ghost.reveal v <: Seq.seq byte) (Ghost.reveal v);
  vc
}

let seq_flbytes_prefix_slice_lemma (x v2: Seq.seq byte)
: Lemma (Seq.slice (Seq.append x v2) 0 (Seq.length x) == x)
= Seq.lemma_eq_intro (Seq.slice (Seq.append x v2) 0 (Seq.length x)) x

let serialize_lseq_bytes_eq (sz: nat { sz < 4294967296 }) (x: Seq.lseq byte sz)
: Lemma (serialize (serialize_lseq_bytes sz) x == x)
= ()

(* Copyful safe serializer for a fixed-length byte array. Fails gracefully
   (err=true) iff the owned value does not have length [sz] (so [seq_flbytes_conv
   sz] is None) or the output slice has fewer than [sz] bytes. On success it
   copies the owned bytes into the [sz]-byte prefix of [out]. The runtime length
   is read from the refined [lvec_len] field, so no impossible runtime
   [V.length] lookup is needed. *)
inline_for_extraction
fn l2r_safe_writer_seq_flbytes
  (sz: nat { sz < 4294967296 })
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: PPB.l2r_safe_writer #(PPBY.lvec byte) #(Seq.seq byte) #(Seq.lseq byte sz) vmatch_copy_seqbytes #_ #(parse_lseq_bytes sz) (serialize_lseq_bytes sz) (seq_flbytes_conv sz)
=
  (x: PPBY.lvec byte)
  (#y: Ghost.erased (Seq.seq byte))
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  unfold (vmatch_copy_seqbytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  S.pts_to_len out;
  let lout = S.len out;
  if (SZ.eq n sz_sz) {
    if (SZ.lt lout sz_sz) {
      perr := true;
      fold (vmatch_copy_seqbytes x y);
      sz_sz
    } else {
      let sp1, sp2 = S.split out sz_sz;
      S.pts_to_len sp1;
      V.to_array_pts_to x.lvec_vec;
      let vecslice = S.from_array (V.vec_to_array x.lvec_vec) n;
      S.pts_to_len vecslice;
      S.copy sp1 vecslice;
      S.to_array vecslice;
      V.to_vec_pts_to x.lvec_vec;
      S.join sp1 sp2 out;
      seq_flbytes_prefix_slice_lemma (Ghost.reveal y) (Seq.slice (Ghost.reveal v) sz (Seq.length (Ghost.reveal v)));
      serialize_lseq_bytes_eq sz (Ghost.reveal y <: Seq.lseq byte sz);
      perr := false;
      fold (vmatch_copy_seqbytes x y);
      sz_sz
    }
  } else {
    perr := true;
    fold (vmatch_copy_seqbytes x y);
    sz_sz
  }
}

(* Copyful safe SIZE for a fixed-length byte array: the size-computation analog
   of [l2r_safe_writer_seq_flbytes]. It does not serialize; it only reports the
   (constant) serialized size [sz]. It fails gracefully (err=true) iff the owned
   value does not have length [sz] (so [seq_flbytes_conv sz] is None). *)
inline_for_extraction
fn l2r_safe_size_seq_flbytes
  (sz: nat { sz < 4294967296 })
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: PPB.l2r_safe_size #(PPBY.lvec byte) #(Seq.seq byte) #(Seq.lseq byte sz) vmatch_copy_seqbytes #_ #(parse_lseq_bytes sz) (serialize_lseq_bytes sz) (seq_flbytes_conv sz)
=
  (x: PPBY.lvec byte)
  (#y: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  unfold (vmatch_copy_seqbytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  if (SZ.eq n sz_sz) {
    assert_norm (pow2 64 == 18446744073709551616);
    serialize_lseq_bytes_eq sz (Ghost.reveal y <: Seq.lseq byte sz);
    perr := false;
    fold (vmatch_copy_seqbytes x y);
    sz_sz
  } else {
    perr := true;
    fold (vmatch_copy_seqbytes x y);
    sz_sz
  }
}

(* ---------------------------------------------------------------------------
   Variable-length, Seq-native (NO FStar.Bytes) byte combinators over
   [Seq.seq byte] / [parse_bounded_seq_vlbytes_t min max].

   These are the [Seq]-native analogs of the [FStar.Bytes] bounded-vlbytes
   combinators in [LowParse.PulseParse.Bytes]. The high-level (ghost) value is a
   plain [Seq.seq byte] (no [FStar.Bytes]); the owned low representation
   [PPBY.lvec byte] and the vmatch [vmatch_copy_seqbytes] are reused verbatim
   from the fixed-length Seq block above. Because the seq-all-bytes serializer is
   the identity, every [B32.reveal]/[B32.hide] coercion of the FStar.Bytes
   version disappears. *)

let seq_vlbytes_conv
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (b: Seq.seq byte)
: GTot (option (parse_bounded_seq_vlbytes_t min max))
= if min <= Seq.length b && Seq.length b <= max
  then Some (b <: parse_bounded_seq_vlbytes_t min max)
  else None

(* Build a [SZ.t] equal to a [nat] bound below [2^32]. The portable [%dsz]
   literal notation only guarantees values up to [2^16 - 1], so length bounds of
   3- or 4-byte vlbytes (e.g. [2^24 - 1]) cannot be passed as literals; this
   helper produces them under the ambient [fits_u64] assumption. *)
inline_for_extraction noextract
let mk_seq_sizet
  (x: nat { x < 4294967296 })
  (sq: squash FStar.SizeT.fits_u64)
: Tot (y: SZ.t { SZ.v y == x })
= FStar.SizeT.fits_u64_implies_fits_32 ();
  FStar.SizeT.uint32_to_sizet (U32.uint_to_t x)


inline_for_extraction
fn jump_seq_all_bytes
  (_: squash FStar.SizeT.fits_u64)
: LPS.jumper parse_seq_all_bytes
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  S.pts_to_len input;
  parser_kind_prop_equiv parse_seq_all_bytes_kind parse_seq_all_bytes;
  S.len input
}

inline_for_extraction
fn validate_seq_all_bytes
  (_: squash FStar.SizeT.fits_u64)
: LPS.validator parse_seq_all_bytes
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  S.pts_to_len input;
  parser_kind_prop_equiv parse_seq_all_bytes_kind parse_seq_all_bytes;
  // parse_seq_all_bytes always succeeds, consuming the whole remaining input
  let input_len = S.len input;
  poffset := input_len;
  true
}

inline_for_extraction
let validate_bounded_seq_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (_: squash FStar.SizeT.fits_u64)
: LPS.validator (parse_bounded_seq_vlbytes min max)
= LPC.validate_synth
    (PPCV.validate_bounded_vldata_strong min max serialize_seq_all_bytes (validate_seq_all_bytes ()) lr ())
    (synth_bounded_seq_vlbytes min max)

inline_for_extraction
let jump_bounded_seq_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: LPS.leaf_reader (serialize_bounded_integer (log256' max)))
  (_: squash FStar.SizeT.fits_u64)
: LPS.jumper (parse_bounded_seq_vlbytes min max)
= LPC.jump_synth
    (PPCV.jump_bounded_vldata_strong min max serialize_seq_all_bytes lr ())
    (synth_bounded_seq_vlbytes min max)

let vldata_seq_all_bytes_conv
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (b: Seq.seq byte)
: GTot (option (parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes))
= if (let sz = Seq.length (serialize_seq_all_bytes b) in min <= sz && sz <= max)
  then Some (b <: parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes)
  else None

inline_for_extraction
fn copyful_parse_seq_all_bytes
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires
  PPB.pts_to_parsed parse_seq_all_bytes input #pm v
returns vc: PPBY.lvec byte
ensures
  PPB.pts_to_parsed parse_seq_all_bytes input #pm v **
  vmatch_copy_seqbytes vc v
{
  PPB.pts_to_parsed_elim input;
  with w. assert (S.pts_to input #pm w);
  let vc = PPBY.alloc_and_copy input;
  Trade.elim (S.pts_to input #pm w) (PPB.pts_to_parsed parse_seq_all_bytes input #pm v);
  rewrite (V.pts_to vc.lvec_vec w) as (V.pts_to vc.lvec_vec (Ghost.reveal v));
  fold (vmatch_copy_seqbytes vc v);
  vc
}

inline_for_extraction
fn copyful_parse_bounded_seq_vldata_strong_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse #(PPBY.lvec byte) #(Seq.seq byte) #(parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes) vmatch_copy_seqbytes (parse_bounded_vldata_strong min max serialize_seq_all_bytes) (vldata_seq_all_bytes_conv min max)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes))
{
  let result = PPCV.accessor_bounded_vldata_strong_payload min max serialize_seq_all_bytes lr u input;
  with pm' v2. assert (PPB.pts_to_parsed parse_seq_all_bytes result #pm' v2);
  let vc = copyful_parse_seq_all_bytes result;
  Trade.elim
    (PPB.pts_to_parsed parse_seq_all_bytes result #pm' v2)
    (PPB.pts_to_parsed (parse_bounded_vldata_strong min max serialize_seq_all_bytes) input #pm v);
  rewrite (vmatch_copy_seqbytes vc v2) as (vmatch_copy_seqbytes vc v);
  PPB.intro_vmatch_conv vmatch_copy_seqbytes (vldata_seq_all_bytes_conv min max) vc (Ghost.reveal v <: Seq.seq byte) (Ghost.reveal v);
  vc
}

inline_for_extraction
fn copyful_parse_bounded_seq_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse #(PPBY.lvec byte) #(Seq.seq byte) #(parse_bounded_seq_vlbytes_t min max) vmatch_copy_seqbytes (parse_bounded_seq_vlbytes min max) (seq_vlbytes_conv min max)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_seq_vlbytes_t min max))
{
  PPC.pts_to_parsed_synth_l2r_trade
    (parse_bounded_seq_vlbytes' min max)
    (synth_bounded_seq_vlbytes min max)
    (synth_bounded_seq_vlbytes_recip min max)
    input;
  let vc = copyful_parse_bounded_seq_vldata_strong_payload min max lr u input;
  Trade.elim
    (PPB.pts_to_parsed (parse_bounded_seq_vlbytes' min max) input #pm (synth_bounded_seq_vlbytes_recip min max v))
    (PPB.pts_to_parsed (parse_bounded_seq_vlbytes min max) input #pm v);
  PPB.elim_vmatch_conv vmatch_copy_seqbytes (vldata_seq_all_bytes_conv min max) vc (synth_bounded_seq_vlbytes_recip min max v);
  with vm . assert (vmatch_copy_seqbytes vc vm ** pure (vldata_seq_all_bytes_conv min max vm == Some (synth_bounded_seq_vlbytes_recip min max v)));
  PPB.intro_vmatch_conv vmatch_copy_seqbytes (seq_vlbytes_conv min max) vc vm (Ghost.reveal v);
  vc
}

#push-options "--z3rlimit 64"

(* Copyful safe serializer for a bounded variable-length byte array (Seq-native).
   Fails gracefully (err=true) iff the owned value's length is out of [min, max]
   (so [seq_vlbytes_conv min max] is None) or the output slice cannot hold the
   [(log256' max) + length] serialized bytes. On success it writes the
   [(log256' max)]-byte big-endian length header into the prefix and copies the
   owned payload bytes after it. The runtime length is read from the [lvec_len]
   field (sound by its refinement). Because the seq-all-bytes serializer is the
   identity, all the [B32.reveal] coercions of the FStar.Bytes version
   disappear. *)
inline_for_extraction
fn l2r_safe_writer_bounded_seq_vlbytes
  (min: nat)
  (min_sz: SZ.t { SZ.v min_sz == min })
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (max_sz: SZ.t { SZ.v max_sz == max })
  (l_sz: SZ.t { SZ.v l_sz == log256' max })
  (sq: squash FStar.SizeT.fits_u64)
: PPB.l2r_safe_writer #(PPBY.lvec byte) #(Seq.seq byte) #(parse_bounded_seq_vlbytes_t min max) vmatch_copy_seqbytes #_ #(parse_bounded_seq_vlbytes min max) (serialize_bounded_seq_vlbytes min max) (seq_vlbytes_conv min max)
=
  (x: PPBY.lvec byte)
  (#y: Ghost.erased (Seq.seq byte))
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  unfold (vmatch_copy_seqbytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  S.pts_to_len out;
  let lout = S.len out;
  if (SZ.lte min_sz n && SZ.lte n max_sz) {
    (* conv y == Some y; serialized length is (log256' max) + n *)
    length_serialize_bounded_seq_vlbytes min max (Ghost.reveal y);
    PPBY.vlbytes_total_fits_lemma (log256' max) (SZ.v n) max;
    SZ.fits_u64_implies_fits (SZ.v l_sz + SZ.v n);
    let tot_sz = SZ.add l_sz n;
    if (SZ.lt lout tot_sz) {
      perr := true;
      fold (vmatch_copy_seqbytes x y);
      tot_sz
    } else {
      let sp1, sp2 = S.split out l_sz;
      S.pts_to_len sp1;
      with hv. assert (S.pts_to sp1 hv);
      (* write the big-endian length header into sp1 == out[0, log256' max) *)
      let n_u32 = SZ.sizet_to_uint32 n;
      M.pow2_le_compat (FStar.Mul.op_Star 8 (log256' max)) (FStar.Mul.op_Star 8 (log256' max));
      let write_hdr = LPPI.write_bounded_integer_header (log256' max) l_sz;
      write_hdr n_u32 sp1 #hv l_sz;
      with hdr. assert (S.pts_to sp1 hdr);
      S.pts_to_len sp1;
      (* copy the payload into sp2a == out[log256' max, (log256' max) + n) *)
      let sp2a, sp2b = S.split sp2 n;
      S.pts_to_len sp2a;
      V.to_array_pts_to x.lvec_vec;
      let vecslice = S.from_array (V.vec_to_array x.lvec_vec) n;
      S.pts_to_len vecslice;
      S.copy sp2a vecslice;
      S.to_array vecslice;
      V.to_vec_pts_to x.lvec_vec;
      S.join sp2a sp2b sp2;
      S.join sp1 sp2 out;
      (* close the postcondition: written prefix == serialized bytes *)
      serialize_bounded_seq_vlbytes_bytes_eq min max (Ghost.reveal y);
      serialize_bounded_integer_spec (log256' max) (U32.uint_to_t (Seq.length (Ghost.reveal y)));
      PPBY.vlbytes_prefix_slice_lemma hdr (Ghost.reveal y) (Seq.slice (Ghost.reveal v) (log256' max + SZ.v n) (Seq.length (Ghost.reveal v)));
      perr := false;
      fold (vmatch_copy_seqbytes x y);
      tot_sz
    }
  } else {
    perr := true;
    fold (vmatch_copy_seqbytes x y);
    0sz
  }
}

#pop-options

#push-options "--z3rlimit 64"

(* Copyful safe SIZE for a bounded variable-length byte array (Seq-native): the
   size-computation analog of [l2r_safe_writer_bounded_seq_vlbytes]. It does not
   serialize; it only computes the serialized size [(log256' max) + n]. It fails
   gracefully (err=true) iff the owned value's length is out of [min, max] (so
   [seq_vlbytes_conv min max] is None). *)
inline_for_extraction
fn l2r_safe_size_bounded_seq_vlbytes
  (min: nat)
  (min_sz: SZ.t { SZ.v min_sz == min })
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (max_sz: SZ.t { SZ.v max_sz == max })
  (l_sz: SZ.t { SZ.v l_sz == log256' max })
  (sq: squash FStar.SizeT.fits_u64)
: PPB.l2r_safe_size #(PPBY.lvec byte) #(Seq.seq byte) #(parse_bounded_seq_vlbytes_t min max) vmatch_copy_seqbytes #_ #(parse_bounded_seq_vlbytes min max) (serialize_bounded_seq_vlbytes min max) (seq_vlbytes_conv min max)
=
  (x: PPBY.lvec byte)
  (#y: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  unfold (vmatch_copy_seqbytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  if (SZ.lte min_sz n && SZ.lte n max_sz) {
    (* conv y == Some y; serialized length is (log256' max) + n *)
    length_serialize_bounded_seq_vlbytes min max (Ghost.reveal y);
    PPBY.vlbytes_total_fits_lemma (log256' max) (SZ.v n) max;
    SZ.fits_u64_implies_fits (SZ.v l_sz + SZ.v n);
    let tot_sz = SZ.add l_sz n;
    perr := false;
    fold (vmatch_copy_seqbytes x y);
    tot_sz
  } else {
    perr := true;
    fold (vmatch_copy_seqbytes x y);
    0sz
  }
}

#pop-options

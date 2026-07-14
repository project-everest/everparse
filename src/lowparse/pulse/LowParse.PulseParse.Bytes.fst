module LowParse.PulseParse.Bytes
#lang-pulse
include LowParse.Spec.Bytes
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module LPC = LowParse.Pulse.Combinators
module PPCV = LowParse.PulseParse.VLData
module PPVG = LowParse.PulseParse.VLGen
module U32 = FStar.UInt32

inline_for_extraction
let validate_flbytes
  (sz: nat { sz < 4294967296 })
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: LPS.validator (parse_flbytes sz)
= LPS.validate_total_constant_size (parse_flbytes sz) sz_sz

inline_for_extraction
let jump_flbytes
  (sz: nat { sz < 4294967296 })
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: LPS.jumper (parse_flbytes sz)
= LPS.jump_constant_size (parse_flbytes sz) sz_sz

inline_for_extraction
fn jump_all_bytes
  (_: squash FStar.SizeT.fits_u64)
: LPS.jumper parse_all_bytes
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  pts_to_len input;
  parser_kind_prop_equiv parse_all_bytes_kind parse_all_bytes;
  len input
}

inline_for_extraction
fn validate_all_bytes
  (_: squash FStar.SizeT.fits_u64)
: LPS.validator parse_all_bytes
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  pts_to_len input;
  let offset_val = !poffset;
  let input_len = len input;
  let remaining = SZ.sub input_len offset_val;
  SZ.fits_u64_implies_fits_32 ();
  // parse_all_bytes succeeds only for inputs < 4294967296 bytes
  if SZ.gt remaining (SZ.uint32_to_sizet 4294967295ul) {
    false
  } else {
    poffset := input_len;
    true
  }
}

inline_for_extraction
let validate_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (_: squash FStar.SizeT.fits_u64)
: LPS.validator (parse_bounded_vlbytes' min max l)
= LPC.validate_synth
    (PPCV.validate_bounded_vldata_strong' min max l serialize_all_bytes (validate_all_bytes ()) lr ())
    (synth_bounded_vlbytes min max)

inline_for_extraction
let validate_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (_: squash FStar.SizeT.fits_u64)
: LPS.validator (parse_bounded_vlbytes min max)
= validate_bounded_vlbytes' min max (log256' max) lr ()

inline_for_extraction
let validate_bounded_vlgenbytes
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.validator (parse_bounded_vlgenbytes vmin vmax pk)
= LPC.validate_synth
    (PPVG.validate_bounded_vlgen vmin vmax vk rk serialize_all_bytes (validate_all_bytes ()) ())
    (synth_bounded_vlbytes vmin vmax)


inline_for_extraction
let jump_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (lr: LPS.leaf_reader (serialize_bounded_integer l))
  (_: squash FStar.SizeT.fits_u64)
: LPS.jumper (parse_bounded_vlbytes' min max l)
= LPC.jump_synth
    (PPCV.jump_bounded_vldata_strong' min max l serialize_all_bytes lr ())
    (synth_bounded_vlbytes min max)

inline_for_extraction
let jump_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: LPS.leaf_reader (serialize_bounded_integer (log256' max)))
  (_: squash FStar.SizeT.fits_u64)
: LPS.jumper (parse_bounded_vlbytes min max)
= jump_bounded_vlbytes' min max (log256' max) lr ()

inline_for_extraction
let jump_bounded_vlgenbytes
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.jumper (parse_bounded_vlgenbytes vmin vmax pk)
= LPC.jump_synth
    (PPVG.jump_bounded_vlgen vmin vmax jk rk serialize_all_bytes ())
    (synth_bounded_vlbytes vmin vmax)

module B32 = LowParse.Bytes32
module V = Pulse.Lib.Vec
module A = Pulse.Lib.Array
module E = LowParse.Pulse.Endianness
module EI = LowParse.Spec.Endianness.Instances
module LPPI = LowParse.Pulse.Int
module FE = FStar.Endianness
module M = FStar.Math.Lemmas

(* A sized, owned vector: an owned [Pulse.Lib.Vec.vec] paired with a *runtime*
   length field whose [SizeT] value is, by a type refinement, provably equal to
   the vector's (ghost) length [V.length].

   WHY A REFINED LENGTH FIELD (rather than a bare pair or a pure proposition):
   [V.length] is [Ghost], so there is NO runtime operation to recover a vector's
   size. A copyful serializer (l2r_safe_writer) must, at run time, read the byte
   length to (a) compute the serialized size and (b) gracefully fail when the
   high-level conv rejects the value (e.g. a wrong-length [flbytes], or an
   out-of-bounds [vlbytes]). Carrying the length as a refined field makes the
   runtime [lvec_len] a *sound* stand-in for the ghost vector length, so those
   checks need no (impossible) runtime length lookup. The vector comes FIRST
   because the refinement on [lvec_len] mentions [lvec_vec]. *)
noeq
type lvec (t: Type0) = {
  lvec_vec: V.vec t;
  lvec_len: (n: SZ.t { SZ.v n == V.length lvec_vec });
}

(* Copyful parsing for bytes: the left-hand side of the vmatch is a freshly
   allocated, owned (freeable) [lvec byte] holding a copy of the parsed bytes
   together with their runtime length.

   NOTE on the choice of left-hand-side type: a [Pulse.Lib.Slice.slice] is a
   borrowing *view* with no allocation/deallocation API, and a slice value does
   not let one recover its concrete backing array/vector at run time (the
   backing is existentially/ghost-bound). Consequently a [free_t] combinator,
   which only receives the left-hand-side value plus a ghost high-level value,
   cannot soundly free a bare slice. We therefore use an owned, freeable
   [lvec byte] as the left-hand side; a read-only slice view is always derivable
   on demand via [from_array (vec_to_array _)].

   The length equality [SZ.v x.lvec_len == B32.length v] is NOT stated here: it
   follows from [V.pts_to_len] (giving [V.length x.lvec_vec == B32.length v])
   composed with the [lvec_len] field refinement. *)
let vmatch_copy_bytes
  (x: lvec byte)
  (v: B32.bytes)
: slprop
= V.pts_to x.lvec_vec (B32.reveal v) **
  pure (V.is_full_vec x.lvec_vec)

let flbytes_conv
  (sz: nat { sz < 4294967296 })
  (b: B32.bytes)
: GTot (option (B32.lbytes sz))
= if B32.length b = sz then Some (b <: B32.lbytes sz) else None

let vldata_all_bytes_conv
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (b: B32.bytes)
: GTot (option (parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes))
= if (let sz = Seq.length (serialize_all_bytes b) in min <= sz && sz <= max)
  then Some (b <: parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes)
  else None

let vlbytes_conv
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (b: B32.bytes)
: GTot (option (parse_bounded_vlbytes_t min max))
= if (min <= B32.length b && B32.length b <= max)
  then Some (b <: parse_bounded_vlbytes_t min max)
  else None

inline_for_extraction
fn free_copy_bytes
  (x: lvec byte)
  (#v: Ghost.erased B32.bytes)
requires
  vmatch_copy_bytes x v
ensures
  emp
{
  unfold (vmatch_copy_bytes x v);
  V.free x.lvec_vec
}

inline_for_extraction
fn alloc_and_copy
  (input: S.slice byte)
  (#pm: perm)
  (#w: Ghost.erased (Seq.seq byte))
requires
  S.pts_to input #pm w
returns res: lvec byte
ensures
  S.pts_to input #pm w **
  V.pts_to res.lvec_vec w **
  pure (V.is_full_vec res.lvec_vec /\ SZ.v res.lvec_len == Seq.length w)
{
  S.pts_to_len input;
  let length = S.len input;
  let vc = V.alloc 0uy length;
  V.to_array_pts_to vc;
  let tmp = S.from_array (V.vec_to_array vc) length;
  S.pts_to_len tmp;
  SZ.size_v_inj (S.len input);
  SZ.size_v_inj (S.len tmp);
  S.copy tmp input;
  S.to_array tmp;
  V.to_vec_pts_to vc;
  let res : lvec byte = { lvec_vec = vc; lvec_len = length };
  rewrite (V.pts_to vc w) as (V.pts_to res.lvec_vec w);
  res
}

inline_for_extraction
fn copyful_parse_all_bytes
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased B32.bytes)
requires
  PPB.pts_to_parsed parse_all_bytes input #pm v
returns vc: lvec byte
ensures
  PPB.pts_to_parsed parse_all_bytes input #pm v **
  vmatch_copy_bytes vc v
{
  PPB.pts_to_parsed_elim input;
  with w. assert (S.pts_to input #pm w);
  let vc = alloc_and_copy input;
  Trade.elim (S.pts_to input #pm w) (PPB.pts_to_parsed parse_all_bytes input #pm v);
  assert (pure (Ghost.reveal w == B32.reveal v));
  rewrite (V.pts_to vc.lvec_vec w) as (V.pts_to vc.lvec_vec (B32.reveal v));
  fold (vmatch_copy_bytes vc v);
  vc
}

inline_for_extraction
fn copyful_parse_flbytes
  (sz: nat { sz < 4294967296 })
: PPB.copyful_parse #(lvec byte) #B32.bytes #(B32.lbytes sz) vmatch_copy_bytes (parse_flbytes sz) (flbytes_conv sz)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (B32.lbytes sz))
{
  PPB.pts_to_parsed_elim input;
  with w. assert (S.pts_to input #pm w);
  let vc = alloc_and_copy input;
  Trade.elim (S.pts_to input #pm w) (PPB.pts_to_parsed (parse_flbytes sz) input #pm v);
  rewrite (V.pts_to vc.lvec_vec w) as (V.pts_to vc.lvec_vec (B32.reveal v));
  fold (vmatch_copy_bytes vc v);
  PPB.intro_vmatch_conv vmatch_copy_bytes (flbytes_conv sz) vc (Ghost.reveal v <: B32.bytes) (Ghost.reveal v);
  vc
}

let flbytes_prefix_slice_lemma (x v2: Seq.seq byte)
: Lemma (Seq.slice (Seq.append x v2) 0 (Seq.length x) == x)
= Seq.lemma_eq_intro (Seq.slice (Seq.append x v2) 0 (Seq.length x)) x

let serialize_flbytes_eq (sz: nat { sz < 4294967296 }) (x: B32.lbytes sz)
: Lemma (serialize (serialize_flbytes sz) x == B32.reveal x)
= ()

(* Copyful safe serializer for a fixed-length byte array. Fails gracefully
   (err=true) iff the owned value does not have length [sz] (so the conv
   [flbytes_conv sz] is None) or the output slice has fewer than [sz] bytes.
   On success it copies the owned bytes into the [sz]-byte prefix of [out].
   The runtime length is read from the [lvec_len] field (sound by its
   refinement), so no impossible runtime [V.length] lookup is needed. *)
inline_for_extraction
fn l2r_safe_writer_flbytes
  (sz: nat { sz < 4294967296 })
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: PPB.l2r_safe_writer #(lvec byte) #B32.bytes #(B32.lbytes sz) vmatch_copy_bytes #_ #(parse_flbytes sz) (serialize_flbytes sz) (flbytes_conv sz)
=
  (x: lvec byte)
  (#y: Ghost.erased B32.bytes)
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  unfold (vmatch_copy_bytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  S.pts_to_len out;
  let lout = S.len out;
  if (SZ.eq n sz_sz) {
    if (SZ.lt lout sz_sz) {
      perr := true;
      fold (vmatch_copy_bytes x y);
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
      flbytes_prefix_slice_lemma (B32.reveal y) (Seq.slice (Ghost.reveal v) sz (Seq.length (Ghost.reveal v)));
      serialize_flbytes_eq sz (Ghost.reveal y <: B32.lbytes sz);
      perr := false;
      fold (vmatch_copy_bytes x y);
      sz_sz
    }
  } else {
    perr := true;
    fold (vmatch_copy_bytes x y);
    sz_sz
  }
}

inline_for_extraction
fn copyful_parse_bounded_vldata_strong_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse #(lvec byte) #B32.bytes #(parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes) vmatch_copy_bytes (parse_bounded_vldata_strong' min max l serialize_all_bytes) (vldata_all_bytes_conv min max)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes))
{
  let result = PPCV.accessor_bounded_vldata_strong_payload' min max l serialize_all_bytes lr u input;
  with pm' v2. assert (PPB.pts_to_parsed parse_all_bytes result #pm' v2);
  let vc = copyful_parse_all_bytes result;
  Trade.elim
    (PPB.pts_to_parsed parse_all_bytes result #pm' v2)
    (PPB.pts_to_parsed (parse_bounded_vldata_strong' min max l serialize_all_bytes) input #pm v);
  rewrite (vmatch_copy_bytes vc v2) as (vmatch_copy_bytes vc v);
  PPB.intro_vmatch_conv vmatch_copy_bytes (vldata_all_bytes_conv min max) vc (Ghost.reveal v <: B32.bytes) (Ghost.reveal v);
  vc
}

inline_for_extraction
fn copyful_parse_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse #(lvec byte) #B32.bytes #(parse_bounded_vlbytes_t min max) vmatch_copy_bytes (parse_bounded_vlbytes' min max l) (vlbytes_conv min max)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vlbytes_t min max))
{
  PPC.pts_to_parsed_synth_l2r_trade
    (parse_bounded_vldata_strong' min max l serialize_all_bytes)
    (synth_bounded_vlbytes min max)
    (synth_bounded_vlbytes_recip min max)
    input;
  let vc = copyful_parse_bounded_vldata_strong_payload min max l lr u input;
  Trade.elim
    (PPB.pts_to_parsed (parse_bounded_vldata_strong' min max l serialize_all_bytes) input #pm (synth_bounded_vlbytes_recip min max v))
    (PPB.pts_to_parsed (parse_bounded_vlbytes' min max l) input #pm v);
  PPB.elim_vmatch_conv vmatch_copy_bytes (vldata_all_bytes_conv min max) vc (synth_bounded_vlbytes_recip min max v);
  with vm . assert (vmatch_copy_bytes vc vm ** pure (vldata_all_bytes_conv min max vm == Some (synth_bounded_vlbytes_recip min max v)));
  PPB.intro_vmatch_conv vmatch_copy_bytes (vlbytes_conv min max) vc vm (Ghost.reveal v);
  vc
}

inline_for_extraction
let copyful_parse_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse #(lvec byte) #B32.bytes #(parse_bounded_vlbytes_t min max) vmatch_copy_bytes (parse_bounded_vlbytes min max) (vlbytes_conv min max)
= copyful_parse_bounded_vlbytes' min max (log256' max) lr u

#push-options "--z3rlimit 128"

inline_for_extraction
fn accessor_bounded_vlgen_all_bytes_payload
  (vmin: Ghost.erased nat)
  (vmax: Ghost.erased nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.accessor (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) parse_all_bytes (PPCV.clens_bounded_vldata_strong vmin vmax serialize_all_bytes)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t vmin vmax #_ #_ #parse_all_bytes serialize_all_bytes))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vlgen_unfold_aux vmin vmax pk serialize_all_bytes bytes;
  parser_kind_prop_equiv sk pk;
  let off1 = jk input 0sz;
  let len = PPB.read_parsed_from_validator_success rk input 0sz off1;
  let input_key, input_payload = split_trade input off1;
  with wb_key . assert (S.pts_to input_key #pm wb_key);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_key #pm wb_key) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) input #pm v);
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) parse_all_bytes_kind) (parse_fldata_strong serialize_all_bytes (U32.v len));
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) parse_all_bytes_kind) (parse_fldata parse_all_bytes (U32.v len));
  parser_kind_prop_equiv parse_all_bytes_kind parse_all_bytes;
  Seq.lemma_eq_elim wb_payload (Seq.slice wb_payload 0 (Seq.length wb_payload));
  PPB.pts_to_parsed_intro parse_all_bytes input_payload (Ghost.reveal v <: B32.bytes);
  Trade.trans (PPB.pts_to_parsed parse_all_bytes input_payload #(pm /. 2.0R) (Ghost.reveal v <: B32.bytes)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) input #pm v);
  input_payload
}

#pop-options

inline_for_extraction
fn copyful_parse_bounded_vlgen_payload
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.copyful_parse #(lvec byte) #B32.bytes #(parse_bounded_vldata_strong_t vmin vmax #_ #_ #parse_all_bytes serialize_all_bytes) vmatch_copy_bytes (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) (vldata_all_bytes_conv vmin vmax)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t vmin vmax #_ #_ #parse_all_bytes serialize_all_bytes))
{
  let result = accessor_bounded_vlgen_all_bytes_payload vmin vmax jk rk sq input;
  with pm' v2. assert (PPB.pts_to_parsed parse_all_bytes result #pm' v2);
  let vc = copyful_parse_all_bytes result;
  Trade.elim
    (PPB.pts_to_parsed parse_all_bytes result #pm' v2)
    (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) input #pm v);
  rewrite (vmatch_copy_bytes vc v2) as (vmatch_copy_bytes vc v);
  PPB.intro_vmatch_conv vmatch_copy_bytes (vldata_all_bytes_conv vmin vmax) vc (Ghost.reveal v <: B32.bytes) (Ghost.reveal v);
  vc
}

inline_for_extraction
fn copyful_parse_bounded_vlgenbytes
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (u: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.copyful_parse #(lvec byte) #B32.bytes #(parse_bounded_vlbytes_t vmin vmax) vmatch_copy_bytes (parse_bounded_vlgenbytes vmin vmax pk) (vlbytes_conv vmin vmax)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vlbytes_t vmin vmax))
{
  PPC.pts_to_parsed_synth_l2r_trade
    (parse_bounded_vlgen vmin vmax pk serialize_all_bytes)
    (synth_bounded_vlbytes vmin vmax)
    (synth_bounded_vlbytes_recip vmin vmax)
    input;
  let vc = copyful_parse_bounded_vlgen_payload vmin vmax jk rk u input;
  Trade.elim
    (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) input #pm (synth_bounded_vlbytes_recip vmin vmax v))
    (PPB.pts_to_parsed (parse_bounded_vlgenbytes vmin vmax pk) input #pm v);
  PPB.elim_vmatch_conv vmatch_copy_bytes (vldata_all_bytes_conv vmin vmax) vc (synth_bounded_vlbytes_recip vmin vmax v);
  with vm . assert (vmatch_copy_bytes vc vm ** pure (vldata_all_bytes_conv vmin vmax vm == Some (synth_bounded_vlbytes_recip vmin vmax v)));
  PPB.intro_vmatch_conv vmatch_copy_bytes (vlbytes_conv vmin vmax) vc vm (Ghost.reveal v);
  vc
}

(* The serialized form of a [bounded_vlbytes] value [y] is the [l]-byte
   big-endian length header (encoding [B32.length y]) followed by the raw
   payload bytes [B32.reveal y]. Derived from [serialize_synth_eq] over the
   strong-vldata serializer (whose [aux] is exactly that append). *)
let serialize_bounded_vlbytes'_bytes_eq
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (y: parse_bounded_vlbytes_t min max)
: Lemma (
    serialize (serialize_bounded_vlbytes' min max l) y ==
    Seq.append
      (serialize (serialize_bounded_integer l) (U32.uint_to_t (B32.length y)))
      (B32.reveal y)
  )
= serialize_synth_eq
    (parse_bounded_vlbytes_aux min max l)
    (synth_bounded_vlbytes min max)
    (serialize_bounded_vlbytes_aux min max l)
    (synth_bounded_vlbytes_recip min max)
    ()
    y

let vlbytes_prefix_slice_lemma (hdr pay tail: Seq.seq byte)
: Lemma
  (ensures Seq.slice (Seq.append hdr (Seq.append pay tail)) 0 (Seq.length hdr + Seq.length pay)
           == Seq.append hdr pay)
= Seq.lemma_eq_intro
    (Seq.slice (Seq.append hdr (Seq.append pay tail)) 0 (Seq.length hdr + Seq.length pay))
    (Seq.append hdr pay)

let vlbytes_total_fits_lemma (l n max: nat)
: Lemma (requires l <= 4 /\ n <= max /\ max < 4294967296)
        (ensures l + n < pow2 64)
= assert_norm (pow2 64 == 18446744073709551616)

#push-options "--z3rlimit 64"

(* Copyful safe serializer for a bounded variable-length byte array. Fails
   gracefully (err=true) iff the owned value's length is out of [min, max] (so
   the conv [vlbytes_conv min max] is None) or the output slice cannot hold the
   [l + length] serialized bytes. On success it writes the [l]-byte big-endian
   length header into the prefix [0, l) and copies the owned payload bytes into
   [l, l + n). The runtime length is read from the [lvec_len] field (sound by its
   refinement), so no impossible runtime [V.length] lookup is needed. The extra
   [SZ.t] parameters [min_sz]/[max_sz]/[l_sz] are runtime mirrors of the spec
   nats [min]/[max]/[l]. *)
inline_for_extraction
fn l2r_safe_writer_bounded_vlbytes'
  (min: nat)
  (min_sz: SZ.t { SZ.v min_sz == min })
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (max_sz: SZ.t { SZ.v max_sz == max })
  (l: nat { l >= log256' max /\ l <= 4 })
  (l_sz: SZ.t { SZ.v l_sz == l })
  (sq: squash FStar.SizeT.fits_u64)
: PPB.l2r_safe_writer #(lvec byte) #B32.bytes #(parse_bounded_vlbytes_t min max) vmatch_copy_bytes #_ #(parse_bounded_vlbytes' min max l) (serialize_bounded_vlbytes' min max l) (vlbytes_conv min max)
=
  (x: lvec byte)
  (#y: Ghost.erased B32.bytes)
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  unfold (vmatch_copy_bytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  S.pts_to_len out;
  let lout = S.len out;
  if (SZ.lte min_sz n && SZ.lte n max_sz) {
    (* conv y == Some y; serialized length is l + n *)
    length_serialize_bounded_vlbytes' min max l (Ghost.reveal y);
    vlbytes_total_fits_lemma l (SZ.v n) max;
    SZ.fits_u64_implies_fits (SZ.v l_sz + SZ.v n);
    let tot_sz = SZ.add l_sz n;
    if (SZ.lt lout tot_sz) {
      perr := true;
      fold (vmatch_copy_bytes x y);
      tot_sz
    } else {
      let sp1, sp2 = S.split out l_sz;
      S.pts_to_len sp1;
      with hv. assert (S.pts_to sp1 hv);
      (* write the big-endian length header into sp1 == out[0, l) *)
      let n_u32 = SZ.sizet_to_uint32 n;
      M.pow2_le_compat (FStar.Mul.op_Star 8 l) (FStar.Mul.op_Star 8 (log256' max));
      let write_hdr = LPPI.write_bounded_integer_header l l_sz;
      write_hdr n_u32 sp1 #hv l_sz;
      with hdr. assert (S.pts_to sp1 hdr);
      S.pts_to_len sp1;
      (* copy the payload into sp2a == out[l, l + n) *)
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
      serialize_bounded_vlbytes'_bytes_eq min max l (Ghost.reveal y);
      serialize_bounded_integer_spec l (U32.uint_to_t (B32.length (Ghost.reveal y)));
      vlbytes_prefix_slice_lemma hdr (B32.reveal y) (Seq.slice (Ghost.reveal v) (l + SZ.v n) (Seq.length (Ghost.reveal v)));
      perr := false;
      fold (vmatch_copy_bytes x y);
      tot_sz
    }
  } else {
    perr := true;
    fold (vmatch_copy_bytes x y);
    0sz
  }
}

#pop-options

inline_for_extraction
let l2r_safe_writer_bounded_vlbytes
  (min: nat)
  (min_sz: SZ.t { SZ.v min_sz == min })
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (max_sz: SZ.t { SZ.v max_sz == max })
  (l_sz: SZ.t { SZ.v l_sz == log256' max })
  (sq: squash FStar.SizeT.fits_u64)
: PPB.l2r_safe_writer #(lvec byte) #B32.bytes #(parse_bounded_vlbytes_t min max) vmatch_copy_bytes #_ #(parse_bounded_vlbytes min max) (serialize_bounded_vlbytes min max) (vlbytes_conv min max)
= l2r_safe_writer_bounded_vlbytes' min min_sz max max_sz (log256' max) l_sz sq

(* Copyful safe SIZE for a fixed-length byte array: the size-computation analog
   of [l2r_safe_writer_flbytes]. It does not serialize; it only reports the
   serialized size [sz] (which is constant for [serialize_flbytes sz]). It fails
   gracefully (err=true) iff the owned value does not have length [sz] (so the
   conv [flbytes_conv sz] is None). The runtime length is read from the
   [lvec_len] field (sound by its refinement). The constant size [sz] always
   fits in a machine word. *)
inline_for_extraction
fn l2r_safe_size_flbytes
  (sz: nat { sz < 4294967296 })
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: PPB.l2r_safe_size #(lvec byte) #B32.bytes #(B32.lbytes sz) vmatch_copy_bytes #_ #(parse_flbytes sz) (serialize_flbytes sz) (flbytes_conv sz)
=
  (x: lvec byte)
  (#y: Ghost.erased B32.bytes)
  (perr: R.ref bool)
{
  unfold (vmatch_copy_bytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  if (SZ.eq n sz_sz) {
    (* conv y == Some y; serialized length is exactly sz *)
    assert_norm (pow2 64 == 18446744073709551616);
    serialize_flbytes_eq sz (Ghost.reveal y <: B32.lbytes sz);
    perr := false;
    fold (vmatch_copy_bytes x y);
    sz_sz
  } else {
    (* length =/= sz, so flbytes_conv sz y == None *)
    perr := true;
    fold (vmatch_copy_bytes x y);
    sz_sz
  }
}

#push-options "--z3rlimit 64"

(* Copyful safe SIZE for a bounded variable-length byte array: the
   size-computation analog of [l2r_safe_writer_bounded_vlbytes']. It does not
   serialize; it only computes the serialized size [l + n] of the [l]-byte
   length header plus the [n]-byte payload. It fails gracefully (err=true) iff
   the owned value's length is out of [min, max] (so the conv
   [vlbytes_conv min max] is None). The runtime length is read from the
   [lvec_len] field (sound by its refinement). The total [l + n <= 4 + max]
   always fits in a machine word. *)
inline_for_extraction
fn l2r_safe_size_bounded_vlbytes'
  (min: nat)
  (min_sz: SZ.t { SZ.v min_sz == min })
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (max_sz: SZ.t { SZ.v max_sz == max })
  (l: nat { l >= log256' max /\ l <= 4 })
  (l_sz: SZ.t { SZ.v l_sz == l })
  (sq: squash FStar.SizeT.fits_u64)
: PPB.l2r_safe_size #(lvec byte) #B32.bytes #(parse_bounded_vlbytes_t min max) vmatch_copy_bytes #_ #(parse_bounded_vlbytes' min max l) (serialize_bounded_vlbytes' min max l) (vlbytes_conv min max)
=
  (x: lvec byte)
  (#y: Ghost.erased B32.bytes)
  (perr: R.ref bool)
{
  unfold (vmatch_copy_bytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  if (SZ.lte min_sz n && SZ.lte n max_sz) {
    (* conv y == Some y; serialized length is l + n *)
    length_serialize_bounded_vlbytes' min max l (Ghost.reveal y);
    vlbytes_total_fits_lemma l (SZ.v n) max;
    SZ.fits_u64_implies_fits (SZ.v l_sz + SZ.v n);
    let tot_sz = SZ.add l_sz n;
    perr := false;
    fold (vmatch_copy_bytes x y);
    tot_sz
  } else {
    (* length out of [min, max], so vlbytes_conv min max y == None *)
    perr := true;
    fold (vmatch_copy_bytes x y);
    0sz
  }
}

#pop-options

inline_for_extraction
let l2r_safe_size_bounded_vlbytes
  (min: nat)
  (min_sz: SZ.t { SZ.v min_sz == min })
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (max_sz: SZ.t { SZ.v max_sz == max })
  (l_sz: SZ.t { SZ.v l_sz == log256' max })
  (sq: squash FStar.SizeT.fits_u64)
: PPB.l2r_safe_size #(lvec byte) #B32.bytes #(parse_bounded_vlbytes_t min max) vmatch_copy_bytes #_ #(parse_bounded_vlbytes min max) (serialize_bounded_vlbytes min max) (vlbytes_conv min max)
= l2r_safe_size_bounded_vlbytes' min min_sz max max_sz (log256' max) l_sz sq

(* ============================================================================ *)
(* Copyful safe writer/size for a generic-length-prefixed byte array (vlgenbytes) *)
(* ============================================================================ *)

(* The serialized form of a [bounded_vlgenbytes] value [y] is the variable-width
   length header (the generic serializer [ssk] applied to the byte length of [y])
   followed by the raw payload bytes [B32.reveal y]. Derived from
   [serialize_synth_eq] over the bounded-vlgen serializer (whose unfold, via
   [serialize_bounded_vlgen_unfold], is exactly that append, using the identity
   [serialize serialize_all_bytes y == B32.reveal y]). *)
let serialize_bounded_vlgenbytes_bytes_eq
  (vmin: nat)
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (y: parse_bounded_vlbytes_t vmin vmax)
: Lemma (
    serialize (serialize_bounded_vlgenbytes vmin vmax ssk) y ==
    Seq.append
      (serialize ssk (U32.uint_to_t (B32.length y)))
      (B32.reveal y)
  )
= serialize_synth_eq
    (parse_bounded_vlgen vmin vmax pk serialize_all_bytes)
    (synth_bounded_vlbytes vmin vmax)
    (serialize_bounded_vlgen vmin vmax ssk serialize_all_bytes)
    (synth_bounded_vlbytes_recip vmin vmax)
    ()
    y;
  serialize_bounded_vlgen_unfold vmin vmax ssk serialize_all_bytes
    (synth_bounded_vlbytes_recip vmin vmax y)

#push-options "--z3rlimit 64"

(* Copyful safe serializer for a bounded variable-length byte array whose length
   is framed by a generic (variable-width) length header [ssk]. The
   variable-width analog of [l2r_safe_writer_bounded_vlbytes']: the header value
   is the payload byte length [n] (read from the [lvec_len] field, sound by its
   refinement); the header bytes are written by the generic leaf writer [hw] and
   their size is computed up-front by [hsize].

   Fails gracefully (err=true) iff the owned value's length is out of
   [vmin, vmax] (so the conv [vlbytes_conv vmin vmax] is None) or the output
   slice cannot hold the [header ++ payload] serialized bytes. Room is checked
   incrementally (header first, then payload) so no [SZ.t] overflow can occur:
   on success [tot = h + n <= length out] always fits. *)
inline_for_extraction
fn l2r_safe_writer_bounded_vlgenbytes
  (vmin: nat) (vmin_sz: SZ.t { SZ.v vmin_sz == vmin })
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 }) (vmax_sz: SZ.t { SZ.v vmax_sz == vmax })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (hsize: (x: bounded_int32 vmin vmax -> Pure SZ.t (requires True) (ensures fun sz -> SZ.v sz == Seq.length (serialize ssk x) /\ SZ.v sz < pow2 64)))
  (hw: LPS.l2r_leaf_writer ssk)
  (sq: squash FStar.SizeT.fits_u64)
: PPB.l2r_safe_writer #(lvec byte) #B32.bytes #(parse_bounded_vlbytes_t vmin vmax) vmatch_copy_bytes #_ #(parse_bounded_vlgenbytes vmin vmax pk) (serialize_bounded_vlgenbytes vmin vmax ssk) (vlbytes_conv vmin vmax)
=
  (x: lvec byte)
  (#y: Ghost.erased B32.bytes)
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  unfold (vmatch_copy_bytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  S.pts_to_len out;
  let lout = S.len out;
  if (SZ.lte vmin_sz n && SZ.lte n vmax_sz) {
    (* conv y == Some y; serialized length is h + n *)
    SZ.fits_u64_implies_fits_32 ();
    FStar.Math.Lemmas.small_mod (SZ.v n) (pow2 32);
    let n32 : bounded_int32 vmin vmax = SZ.sizet_to_uint32 n;
    U32.v_inj n32 (B32.len (Ghost.reveal y));
    let h = hsize n32;
    length_serialize_bounded_vlgenbytes vmin vmax ssk (Ghost.reveal y);
    serialize_bounded_vlgenbytes_bytes_eq vmin vmax ssk (Ghost.reveal y);
    if (SZ.lt lout h) {
      (* not enough room even for the header *)
      perr := true;
      fold (vmatch_copy_bytes x y);
      h
    } else {
      let sp1, sp2 = S.split out h;
      S.pts_to_len sp1;
      S.pts_to_len sp2;
      with hv. assert (S.pts_to sp1 hv);
      (* write the variable-width length header into sp1 == out[0, h) *)
      let res_hdr = hw n32 sp1 0sz;
      with hdr. assert (S.pts_to sp1 hdr);
      S.pts_to_len sp1;
      Seq.lemma_eq_elim hdr (Seq.slice hdr 0 (SZ.v h));
      let lrest = S.len sp2;
      if (SZ.lt lrest n) {
        (* header written but not enough room for the payload *)
        S.join sp1 sp2 out;
        perr := true;
        fold (vmatch_copy_bytes x y);
        h
      } else {
        (* copy the payload into sp2a == out[h, h + n) *)
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
        SZ.fits_lte (SZ.v h + SZ.v n) (SZ.v lout);
        let tot = SZ.add h n;
        (* close the postcondition: written prefix == serialized bytes *)
        vlbytes_prefix_slice_lemma hdr (B32.reveal y)
          (Seq.slice (Ghost.reveal v) (SZ.v h + SZ.v n) (Seq.length (Ghost.reveal v)));
        perr := false;
        fold (vmatch_copy_bytes x y);
        tot
      }
    }
  } else {
    (* length out of [vmin, vmax], so vlbytes_conv vmin vmax y == None *)
    perr := true;
    fold (vmatch_copy_bytes x y);
    0sz
  }
}

#pop-options

#push-options "--z3rlimit 64"

(* Copyful safe SIZE for a bounded variable-length byte array framed by a generic
   (variable-width) length header: the size-computation analog of
   [l2r_safe_writer_bounded_vlgenbytes]. It does not serialize; it only computes
   the serialized size [h + n] of the variable-width header (size [h = hsize n32])
   plus the [n]-byte payload, gracefully failing (err=true) on [SZ.t] overflow
   (only possible for a pathological header serializer, since [n <= vmax]). It
   also fails gracefully iff the owned value's length is out of [vmin, vmax] (so
   the conv [vlbytes_conv vmin vmax] is None). The runtime length is read from
   the [lvec_len] field (sound by its refinement). *)
inline_for_extraction
fn l2r_safe_size_bounded_vlgenbytes
  (vmin: nat) (vmin_sz: SZ.t { SZ.v vmin_sz == vmin })
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 }) (vmax_sz: SZ.t { SZ.v vmax_sz == vmax })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (hsize: (x: bounded_int32 vmin vmax -> Pure SZ.t (requires True) (ensures fun sz -> SZ.v sz == Seq.length (serialize ssk x) /\ SZ.v sz < pow2 64)))
  (sq: squash FStar.SizeT.fits_u64)
: PPB.l2r_safe_size #(lvec byte) #B32.bytes #(parse_bounded_vlbytes_t vmin vmax) vmatch_copy_bytes #_ #(parse_bounded_vlgenbytes vmin vmax pk) (serialize_bounded_vlgenbytes vmin vmax ssk) (vlbytes_conv vmin vmax)
=
  (x: lvec byte)
  (#y: Ghost.erased B32.bytes)
  (perr: R.ref bool)
{
  unfold (vmatch_copy_bytes x y);
  V.pts_to_len x.lvec_vec;
  let n = x.lvec_len;
  if (SZ.lte vmin_sz n && SZ.lte n vmax_sz) {
    (* conv y == Some y; serialized length is h + n *)
    SZ.fits_u64_implies_fits_32 ();
    FStar.Math.Lemmas.small_mod (SZ.v n) (pow2 32);
    let n32 : bounded_int32 vmin vmax = SZ.sizet_to_uint32 n;
    U32.v_inj n32 (B32.len (Ghost.reveal y));
    let h = hsize n32;
    length_serialize_bounded_vlgenbytes vmin vmax ssk (Ghost.reveal y);
    assert_norm (pow2 64 == 18446744073709551616);
    let tot = PPB.size_add_checked sq h n perr;
    fold (vmatch_copy_bytes x y);
    tot
  } else {
    (* length out of [vmin, vmax], so vlbytes_conv vmin vmax y == None *)
    perr := true;
    fold (vmatch_copy_bytes x y);
    0sz
  }
}

#pop-options

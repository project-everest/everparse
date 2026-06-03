module LowParse.PulseParse.Array
#lang-pulse
include LowParse.Spec.Array
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPC = LowParse.PulseParse.Combinators
module LPC = LowParse.Pulse.Combinators
module PPCF = LowParse.PulseParse.FLData
module LPC = LowParse.Pulse.Combinators
module PPCL = LowParse.PulseParse.List
module LPC = LowParse.Pulse.Combinators
module PPCV = LowParse.PulseParse.VLData
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base

inline_for_extraction
let validate_array'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (array_byte_size: nat)
  (array_byte_size_sz: SZ.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond k array_byte_size elem_count == true /\
    SZ.v array_byte_size_sz == array_byte_size
  })
: LPS.validator (parse_array' s array_byte_size elem_count)
= fldata_to_array_inj s array_byte_size elem_count ();
  LPC.validate_synth
    (PPCF.validate_fldata_strong (serialize_list _ s) (PPCL.validate_list v ()) array_byte_size_sz)
    (fldata_to_array s array_byte_size elem_count ())

inline_for_extraction
let validate_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (array_byte_size: nat)
  (array_byte_size_sz: SZ.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond k array_byte_size elem_count == true /\
    SZ.v array_byte_size_sz == array_byte_size
  })
: LPS.validator (parse_array s array_byte_size elem_count)
= if k.parser_kind_metadata = Some ParserKindMetadataTotal
  then LPS.validate_total_constant_size (parse_array s array_byte_size elem_count) array_byte_size_sz
  else LPS.validate_ext (validate_array' s v array_byte_size array_byte_size_sz elem_count u) (parse_array s array_byte_size elem_count)

inline_for_extraction
let validate_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' array_byte_size_max)))
  (_: squash (FStar.SizeT.fits_u64 /\ array_byte_size_max < 4294967296))
: LPS.validator (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  LPC.validate_synth
    (PPCV.validate_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s) (PPCL.validate_list v ()) lr ())
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())


inline_for_extraction
let jump_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (array_byte_size_sz: SZ.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond k array_byte_size elem_count == true /\
    SZ.v array_byte_size_sz == array_byte_size
  })
: LPS.jumper (parse_array s array_byte_size elem_count)
= LPS.jump_constant_size (parse_array s array_byte_size elem_count) array_byte_size_sz

inline_for_extraction
let jump_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (lr: LPS.leaf_reader (serialize_bounded_integer (log256' array_byte_size_max)))
  (_: squash (FStar.SizeT.fits_u64 /\ array_byte_size_max < 4294967296))
: LPS.jumper (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  LPC.jump_synth
    (PPCV.jump_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s) lr ())
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())

module SM = Pulse.Lib.SeqMatch
module V = Pulse.Lib.Vec
module L = FStar.List.Tot
module Seq = FStar.Seq

let vmatch_array
  (#el #eh: Type0)
  (elem_vmatch: el -> eh -> slprop)
  (elem_count_sz: SZ.t)
  (vv: V.vec el)
  (l: list eh)
: slprop
= exists* (s: Seq.seq el).
    V.pts_to vv s **
    SM.seq_list_match s l elem_vmatch **
    pure (V.is_full_vec vv /\ Seq.length s == L.length l /\ L.length l == SZ.v elem_count_sz)

let rec index_append_hd (#a:Type) (acc: list a) (hd: a) (tl: list a)
  : Lemma
    (ensures (
      L.append_length acc (hd :: tl);
      L.index (acc `L.append` (hd :: tl)) (L.length acc) == hd))
    (decreases acc)
  = L.append_length acc (hd :: tl);
    match acc with | [] -> () | _ :: q -> index_append_hd q hd tl

inline_for_extraction
fn free_array
  (#eh #el: Type0)
  (#elem_vmatch: el -> eh -> slprop)
  (free_elem: PPB.free_t elem_vmatch)
  (elem_count_sz: SZ.t)
: PPB.free_t #(V.vec el) #(list eh) (vmatch_array elem_vmatch elem_count_sz)
=
  (x: V.vec el) (#v: Ghost.erased (list eh))
{
  unfold (vmatch_array elem_vmatch elem_count_sz x v);
  with s. assert (V.pts_to x s ** SM.seq_list_match s v elem_vmatch);
  V.pts_to_len x;
  SM.seq_list_match_length elem_vmatch s v;
  SM.seq_list_match_seq_seq_match elem_vmatch s v;
  let mut pi = 0sz;
  while (let i = !pi; SZ.lt i elem_count_sz)
  invariant exists* i. R.pts_to pi i ** V.pts_to x s ** SM.seq_seq_match elem_vmatch s (Seq.seq_of_list v) (SZ.v i) (L.length v) ** pure (SZ.v i <= SZ.v elem_count_sz /\ Seq.length s == SZ.v elem_count_sz /\ L.length v == SZ.v elem_count_sz)
  {
    let i = !pi;
    SM.seq_seq_match_dequeue_left elem_vmatch s (Seq.seq_of_list v) (SZ.v i) (L.length v);
    let elem = V.op_Array_Access x i;
    free_elem elem;
    pi := SZ.add i 1sz;
  };
  let i = !pi;
  SM.seq_seq_match_empty_elim elem_vmatch s (Seq.seq_of_list v) (L.length v);
  V.free x;
}

inline_for_extraction
fn extract_elem
  (#eh: Type0) (#k: parser_kind) (#p: parser k eh)
  (#el: Type0) (#elem_vmatch: el -> eh -> slprop)
  (w: PPB.copyful_parse elem_vmatch p)
  (j: LPS.jumper p)
  (input: slice byte)
  (cur_off_sz: SZ.t)
  (#pm: perm)
  (#w_bytes: Ghost.erased bytes)
  (#hd: Ghost.erased eh)
  (#tl: Ghost.erased (list eh))
  requires S.pts_to input #pm w_bytes **
    pure (k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 /\
      SZ.v cur_off_sz <= Seq.length w_bytes /\
      (let rem = Seq.slice w_bytes (SZ.v cur_off_sz) (Seq.length w_bytes) in
       parse (parse_list p) rem == Some (Ghost.reveal hd :: Ghost.reveal tl, Seq.length rem)))
  returns res: (el & SZ.t)
  ensures S.pts_to input #pm w_bytes **
    elem_vmatch (fst res) hd **
    pure (
      SZ.v cur_off_sz <= SZ.v (snd res) /\ SZ.v (snd res) <= Seq.length w_bytes /\
      (let rem2 = Seq.slice w_bytes (SZ.v (snd res)) (Seq.length w_bytes) in
       parse (parse_list p) rem2 == Some (Ghost.reveal tl, Seq.length rem2)))
{
  S.pts_to_len input;
  parse_list_eq' p (Seq.slice w_bytes (SZ.v cur_off_sz) (Seq.length w_bytes));
  let off2 = j input cur_off_sz;
  let s1s, restA = split_trade input cur_off_sz;
  let elem, restB = split_trade restA (SZ.sub off2 cur_off_sz);
  parse_strong_prefix p
    (Seq.slice w_bytes (SZ.v cur_off_sz) (Seq.length w_bytes))
    (Seq.slice (Seq.slice w_bytes (SZ.v cur_off_sz) (Seq.length w_bytes)) 0 (SZ.v off2 - SZ.v cur_off_sz));
  PPB.pts_to_parsed_intro p elem (Ghost.reveal hd);
  let elx = w elem;
  Trade.elim _ (S.pts_to elem #pm _);
  Trade.elim _ (S.pts_to restA #pm _);
  Trade.elim _ (S.pts_to input #pm w_bytes);
  (elx, off2)
}

let parse_array_synth_eq_pt
  (#k: parser_kind) (#t: Type) (#p: parser k t)
  (s: serializer p) (sz: nat) (n: nat)
  (u: unit { fldata_array_precond k sz n == true })
  (x: bytes)
  : Lemma
    (ensures (
      fldata_to_array_inj s sz n u;
      parse (parse_array s sz n) x ==
      parse (parse_synth (parse_fldata_strong (serialize_list _ s) sz) (fldata_to_array s sz n u)) x))
  = fldata_to_array_inj s sz n u

let parse_array_synth_ext
  (#k: parser_kind) (#t: Type) (#p: parser k t)
  (s: serializer p) (sz: nat) (n: nat)
  (u: unit { fldata_array_precond k sz n == true })
  : Lemma
    (requires synth_injective (fldata_to_array s sz n u))
    (ensures (forall (x:bytes).
      parse (parse_array s sz n) x ==
      parse (parse_synth (parse_fldata_strong (serialize_list _ s) sz) (fldata_to_array s sz n u)) x))
  = Classical.forall_intro (parse_array_synth_eq_pt s sz n u)

let rec splitAt_index_hd (#a:Type) (i:nat) (l:list a)
  : Lemma (requires i < L.length l)
    (ensures (L.lemma_splitAt_snd_length i l; L.hd (snd (L.splitAt i l)) == L.index l i))
    (decreases i)
  = if i = 0 then ()
    else (match l with x :: xs -> splitAt_index_hd (i-1) xs)

let rec splitAt_tl (#a:Type) (i:nat) (l:list a)
  : Lemma (requires i < L.length l)
    (ensures (L.lemma_splitAt_snd_length i l; L.tl (snd (L.splitAt i l)) == snd (L.splitAt (i+1) l)))
    (decreases i)
  = if i = 0 then ()
    else (match l with x :: xs -> splitAt_tl (i-1) xs)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn copyful_parse_array
  (#eh: Type0)
  (#k: parser_kind)
  (#p: parser k eh)
  (s: serializer p)
  (#el: Type0)
  (#elem_vmatch: el -> eh -> slprop)
  (w: PPB.copyful_parse elem_vmatch p)
  (j: LPS.jumper p)
  (array_byte_size: nat)
  (array_byte_size_sz: SZ.t)
  (elem_count: nat)
  (elem_count_sz: SZ.t)
  (u: squash (
    fldata_array_precond k array_byte_size elem_count == true /\
    SZ.v array_byte_size_sz == array_byte_size /\
    SZ.v elem_count_sz == elem_count /\
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    elem_count > 0
  ))
  (input: slice byte) (#pm: perm) (#v: Ghost.erased (LowParse.Spec.Array.array eh elem_count))
requires
  PPB.pts_to_parsed (parse_array s array_byte_size elem_count) input #pm v
returns res: V.vec el
ensures
  PPB.pts_to_parsed (parse_array s array_byte_size elem_count) input #pm v **
  vmatch_array elem_vmatch elem_count_sz res (Ghost.reveal v)
{
  let fl : Ghost.erased (list eh) = Ghost.hide (Ghost.reveal v <: list eh);
  // STEP A: convert parse_array down to parse_list, accumulating a back trade
  fldata_to_array_inj s array_byte_size elem_count ();
  array_to_fldata_to_array s array_byte_size elem_count () ();
  parse_array_synth_ext s array_byte_size elem_count ();
  PPB.pts_to_parsed_ext_trade
    (parse_synth (parse_fldata_strong (serialize_list _ s) array_byte_size) (fldata_to_array s array_byte_size elem_count ()))
    input;
  PPC.pts_to_parsed_synth_l2r_trade
    (parse_fldata_strong (serialize_list _ s) array_byte_size)
    (fldata_to_array s array_byte_size elem_count ())
    (array_to_fldata s array_byte_size elem_count ())
    input;
  Trade.trans
    (PPB.pts_to_parsed (parse_fldata_strong (serialize_list _ s) array_byte_size) input #pm (array_to_fldata s array_byte_size elem_count () (Ghost.reveal v)))
    (PPB.pts_to_parsed (parse_synth (parse_fldata_strong (serialize_list _ s) array_byte_size) (fldata_to_array s array_byte_size elem_count ())) input #pm v)
    (PPB.pts_to_parsed (parse_array s array_byte_size elem_count) input #pm v);
  PPCF.pts_to_parsed_fldata_strong_payload_trade (serialize_list _ s) array_byte_size input;
  Trade.trans
    (PPB.pts_to_parsed (parse_list p) input #pm ((array_to_fldata s array_byte_size elem_count () (Ghost.reveal v)) <: list eh))
    (PPB.pts_to_parsed (parse_fldata_strong (serialize_list _ s) array_byte_size) input #pm (array_to_fldata s array_byte_size elem_count () (Ghost.reveal v)))
    (PPB.pts_to_parsed (parse_array s array_byte_size elem_count) input #pm v);
  rewrite (PPB.pts_to_parsed (parse_list p) input #pm ((array_to_fldata s array_byte_size elem_count () (Ghost.reveal v)) <: list eh))
    as (PPB.pts_to_parsed (parse_list p) input #pm (Ghost.reveal fl));
  // STEP B: down to raw bytes
  PPB.pts_to_parsed_elim input;
  with w_bytes. assert (S.pts_to input #pm w_bytes);
  Trade.trans
    (S.pts_to input #pm w_bytes)
    (PPB.pts_to_parsed (parse_list p) input #pm (Ghost.reveal fl))
    (PPB.pts_to_parsed (parse_array s array_byte_size elem_count) input #pm v);
  S.pts_to_len input;
  // back : trade (S.pts_to input #pm w_bytes) (pts_to_parsed (parse_array) input v)
  // STEP D: seed element 0
  Seq.lemma_eq_elim (Seq.slice w_bytes 0 (Seq.length w_bytes)) w_bytes;
  assert (pure (Cons? (Ghost.reveal fl)));
  let r0 = extract_elem w j input 0sz #pm #w_bytes #(Ghost.hide (L.hd (Ghost.reveal fl))) #(Ghost.hide (L.tl (Ghost.reveal fl)));
  let el0 = fst r0;
  let off1 = snd r0;
  let vec = V.alloc el0 elem_count_sz;
  V.pts_to_len vec;
  let sl : Ghost.erased (Seq.seq eh) = Ghost.hide (Seq.seq_of_list (Ghost.reveal fl));
  Seq.lemma_seq_of_list_index (Ghost.reveal fl) 0;
  assert (pure (L.hd (Ghost.reveal fl) == L.index (Ghost.reveal fl) 0));
  rewrite (elem_vmatch (fst r0) (L.hd (Ghost.reveal fl)))
    as (elem_vmatch el0 (L.index (Ghost.reveal fl) 0));
  SM.seq_seq_match_singleton_intro elem_vmatch (Seq.create (SZ.v elem_count_sz) el0) (Ghost.reveal sl) 0 el0 (L.index (Ghost.reveal fl) 0);
  splitAt_tl 0 (Ghost.reveal fl);
  let mut pi = 1sz;
  let mut poff = off1;
  while (let i = !pi; SZ.lt i elem_count_sz)
  invariant exists* i cur_off_sz s1.
    R.pts_to pi i ** R.pts_to poff cur_off_sz **
    S.pts_to input #pm w_bytes **
    V.pts_to vec s1 **
    SM.seq_seq_match elem_vmatch s1 (Ghost.reveal sl) 0 (SZ.v i) **
    pure (
      1 <= SZ.v i /\ SZ.v i <= SZ.v elem_count_sz /\
      Seq.length s1 == SZ.v elem_count_sz /\
      SZ.v cur_off_sz <= Seq.length w_bytes /\
      (let rem = Seq.slice w_bytes (SZ.v cur_off_sz) (Seq.length w_bytes) in
       parse (parse_list p) rem == Some (snd (L.splitAt (SZ.v i) (Ghost.reveal fl)), Seq.length rem))
    )
  {
    let i = !pi;
    let cur = !poff;
    with s1. assert (V.pts_to vec s1);
    L.lemma_splitAt_snd_length (SZ.v i) (Ghost.reveal fl);
    assert (pure (Cons? (snd (L.splitAt (SZ.v i) (Ghost.reveal fl)))));
    let r = extract_elem w j input cur #pm #w_bytes
      #(Ghost.hide (L.hd (snd (L.splitAt (SZ.v i) (Ghost.reveal fl)))))
      #(Ghost.hide (L.tl (snd (L.splitAt (SZ.v i) (Ghost.reveal fl)))));
    let elx = fst r;
    let off2 = snd r;
    V.op_Array_Assignment vec i elx;
    with s1'. assert (V.pts_to vec s1');
    SM.seq_seq_match_rewrite_seq elem_vmatch s1 s1' (Ghost.reveal sl) (Ghost.reveal sl) 0 (SZ.v i);
    splitAt_index_hd (SZ.v i) (Ghost.reveal fl);
    Seq.lemma_seq_of_list_index (Ghost.reveal fl) (SZ.v i);
    splitAt_tl (SZ.v i) (Ghost.reveal fl);
    assert (pure (Seq.index (Ghost.reveal sl) (SZ.v i) == L.hd (snd (L.splitAt (SZ.v i) (Ghost.reveal fl)))));
    assert (pure (Seq.index s1' (SZ.v i) == elx));
    rewrite (elem_vmatch (fst r) (L.hd (snd (L.splitAt (SZ.v i) (Ghost.reveal fl)))))
      as (elem_vmatch (Seq.index s1' (SZ.v i)) (Seq.index (Ghost.reveal sl) (SZ.v i)));
    SM.seq_seq_match_enqueue_right elem_vmatch s1' (Ghost.reveal sl) 0 (SZ.v i) (Seq.index s1' (SZ.v i)) (Seq.index (Ghost.reveal sl) (SZ.v i));
    poff := off2;
    pi := SZ.add i 1sz;
  };
  let i = !pi;
  with s_final. assert (V.pts_to vec s_final);
  SM.seq_seq_match_seq_list_match elem_vmatch s_final (Ghost.reveal fl);
  Trade.elim
    (S.pts_to input #pm w_bytes)
    (PPB.pts_to_parsed (parse_array s array_byte_size elem_count) input #pm v);
  fold (vmatch_array elem_vmatch elem_count_sz vec (Ghost.reveal fl));
  rewrite (vmatch_array elem_vmatch elem_count_sz vec (Ghost.reveal fl))
    as (vmatch_array elem_vmatch elem_count_sz vec (Ghost.reveal v));
  vec
}

#pop-options

module LowParse.PulseParse.VLGen
#lang-pulse
include LowParse.Spec.VLGen
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
module PPCF = LowParse.PulseParse.FLData
module U32 = FStar.UInt32
module SC = LowParse.Pulse.SizeComparison

inline_for_extraction
fn validate_bounded_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong))
: LPS.validator (parse_bounded_vlgen vmin vmax pk s)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_bounded_vlgen_unfold_aux vmin vmax pk s sinput;
  let offset_val = !poffset;
  let n_valid = vk input poffset;
  if n_valid {
    let off1 = !poffset;
    let len = PPB.read_parsed_from_validator_success rk input offset_val off1;
    pts_to_len input;
    let remaining = SZ.sub (S.len input) off1;
    if SC.u32_lte_sizet len remaining {
      SZ.fits_lte (U32.v len) (SZ.v remaining);
      PPCF.validate_fldata_strong s v (SZ.uint32_to_sizet len) input poffset
    } else {
      false
    }
  } else {
    false
  }
}

inline_for_extraction
let validate_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond vmin vmax k })
  (v: LPS.validator p)
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong))
: LPS.validator (parse_vlgen vmin vmax pk s)
= LPC.validate_synth
    (validate_bounded_vlgen vmin vmax vk rk s v sq)
    (synth_vlgen vmin vmax s)

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_vlgen_weak
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong))
: LPS.validator (parse_vlgen_weak vmin vmax pk p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_vlgen_weak_unfold vmin vmax pk p sinput;
  let offset_val = !poffset;
  let n_valid = vk input poffset;
  if n_valid {
    let off1 = !poffset;
    let len = PPB.read_parsed_from_validator_success rk input offset_val off1;
    pts_to_len input;
    let remaining = SZ.sub (S.len input) off1;
    if SC.u32_lte_sizet len remaining {
      SZ.fits_lte (U32.v len) (SZ.v remaining);
      PPCF.validate_fldata v (SZ.uint32_to_sizet len) input poffset
    } else {
      false
    }
  } else {
    false
  }
}

#pop-options

(* ========== VLGen jumpers ========== *)

inline_for_extraction
fn jump_bounded_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong))
: LPS.jumper (parse_bounded_vlgen vmin vmax pk s)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_vlgen_unfold_aux vmin vmax pk s sinput;
  pts_to_len input;
  let off1 = jk input offset;
  let len = PPB.read_parsed_from_validator_success rk input offset off1;
  let remaining = SZ.sub (S.len input) off1;
  SZ.fits_lte (U32.v len) (SZ.v remaining);
  PPCF.jump_fldata_strong s (SZ.uint32_to_sizet len) input off1
}

module LPC = LowParse.Pulse.Combinators

inline_for_extraction
let jump_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond vmin vmax k })
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong))
: LPS.jumper (parse_vlgen vmin vmax pk s)
= LPC.jump_synth
    (jump_bounded_vlgen vmin vmax jk rk s sq)
    (synth_vlgen vmin vmax s)

(* ========== VLGen accessors ========== *)

include LowParse.CLens
module PPCV = LowParse.PulseParse.VLData

#push-options "--z3rlimit 128"

inline_for_extraction
fn accessor_bounded_vlgen_payload
  (vmin: Ghost.erased nat)
  (vmax: Ghost.erased nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_bounded_vlgen vmin vmax pk s) p (PPCV.clens_bounded_vldata_strong vmin vmax s)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t vmin vmax s))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vlgen_unfold_aux vmin vmax pk s bytes;
  parser_kind_prop_equiv sk pk;
  let off1 = jk input 0sz;
  let len = PPB.read_parsed_from_validator_success rk input 0sz off1;
  let input_key, input_payload = split_trade input off1;
  with wb_key . assert (S.pts_to input_key #pm wb_key);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_key #pm wb_key) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk s) input #pm v);
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) k) (parse_fldata_strong s (U32.v len));
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) k) (parse_fldata p (U32.v len));
  parser_kind_prop_equiv k p;
  Seq.lemma_eq_elim wb_payload (Seq.slice wb_payload 0 (Seq.length wb_payload));
  PPB.pts_to_parsed_intro p input_payload (Ghost.reveal v <: t);
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) (Ghost.reveal v <: t)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk s) input #pm v);
  input_payload
}

inline_for_extraction
fn accessor_vlgen_payload
  (vmin: Ghost.erased nat)
  (vmax: Ghost.erased nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond vmin vmax k })
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_vlgen vmin vmax pk s) p (clens_id t)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_vlgen_unfold vmin vmax pk s bytes;
  parser_kind_prop_equiv sk pk;
  let off1 = jk input 0sz;
  let len = PPB.read_parsed_from_validator_success rk input 0sz off1;
  let input_key, input_payload = split_trade input off1;
  with wb_key . assert (S.pts_to input_key #pm wb_key);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_key #pm wb_key) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_vlgen vmin vmax pk s) input #pm v);
  Seq.lemma_eq_elim wb_payload (Seq.slice bytes (SZ.v off1) (SZ.v off1 + U32.v len));
  PPB.pts_to_parsed_intro p input_payload (Ghost.reveal v);
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) (Ghost.reveal v)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_vlgen vmin vmax pk s) input #pm v);
  input_payload
}

#pop-options

(* ============================================================================ *)
(* Copyful parse for bounded generic-length-prefixed data                       *)
(* ============================================================================ *)

(* The generic length-prefix framing produces the same refined high-level type
   [parse_bounded_vldata_strong_t vmin vmax s] as the bounded vldata-strong
   combinator, so the separation-logic predicate ([PPCV.vmatch_vldata_strong])
   and destructor ([PPCV.free_vldata_strong]) are reused unchanged; only the
   copyful parser is specific (it parses the generic length header and splits off
   the payload). Mirrors [accessor_bounded_vlgen_payload]. *)

#push-options "--z3rlimit 128"

inline_for_extraction
fn copyful_parse_bounded_vlgen_payload
  (vmin: Ghost.erased nat)
  (vmax: Ghost.erased nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#conv: tm -> GTot (option t))
  (s: serializer p)
  (w: PPB.copyful_parse vmatch p conv)
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong))
: PPB.copyful_parse (PPCV.vmatch_vldata_strong vmin vmax s vmatch) (parse_bounded_vlgen vmin vmax pk s) (PPCV.vldata_strong_conv vmin vmax s conv)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t vmin vmax s))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vlgen_unfold_aux vmin vmax pk s bytes;
  parser_kind_prop_equiv sk pk;
  let off1 = jk input 0sz;
  let len = PPB.read_parsed_from_validator_success rk input 0sz off1;
  let input_key, input_payload = split_trade input off1;
  with wb_key . assert (S.pts_to input_key #pm wb_key);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_key #pm wb_key) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk s) input #pm v);
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) k) (parse_fldata_strong s (U32.v len));
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) k) (parse_fldata p (U32.v len));
  parser_kind_prop_equiv k p;
  Seq.lemma_eq_elim wb_payload (Seq.slice wb_payload 0 (Seq.length wb_payload));
  PPB.pts_to_parsed_intro p input_payload (Ghost.reveal v <: t);
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) (Ghost.reveal v <: t)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk s) input #pm v);
  let res = w input_payload;
  Trade.elim
    (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) (Ghost.reveal v <: t))
    (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk s) input #pm v);
  PPB.elim_vmatch_conv vmatch conv res (Ghost.reveal v <: t);
  with vm . assert (vmatch res vm ** pure (conv vm == Some (Ghost.reveal v <: t)));
  fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch res vm);
  PPB.intro_vmatch_conv (PPCV.vmatch_vldata_strong vmin vmax s vmatch) (PPCV.vldata_strong_conv vmin vmax s conv) res vm (Ghost.reveal v);
  res
}

#pop-options

(* ============================================================================ *)
(* Copyful safe writer for bounded generic-length-prefixed data (vlgen)         *)
(* ============================================================================ *)

(* Content lemma: slicing a prefix that lands inside the second component of an
   append (replicated locally from LowParse.PulseParse.Combinators.slice_append_prefix). *)
let vlgen_slice_append_prefix (#a:Type) (x y: Seq.seq a) (j: nat)
  : Lemma
    (j <= Seq.length y ==>
      Seq.slice (Seq.append x y) 0 (Seq.length x + j) == Seq.append x (Seq.slice y 0 j))
  = if j <= Seq.length y
    then Seq.lemma_eq_intro (Seq.slice (Seq.append x y) 0 (Seq.length x + j)) (Seq.append x (Seq.slice y 0 j))
    else ()

(* Step A (trial-write failure).  When the up-front size pass [psz] signals an
   error we can no longer conclude the framing conv is None (the weakened,
   fits_u64-free size contract only tells us the payload is >= pow2 16, which need
   NOT exceed [vmax]).  Instead we perform a trial write of the payload into the
   output slice [out] to observe its serialized size portably.  If THAT write
   fails (error flag true), its own postcondition says either the payload conv is
   None (so the framing conv is None too, err=true) or the observed output length
   [Seq.length v'] is below the payload's serialized length [len]; since the full
   framing length is [header ++ payload] which is at least [len], the output is
   also too short for the framing, so err=true.  Sound on any >= 16-bit size_t. *)
let vlgen_trial_fail_lemma
  (#tm #t: Type)
  (vmin: nat)
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (y: tm)
  (v': Seq.seq byte)
  (res: SZ.t)
: Lemma (requires PPB.l2r_safe_writer_postcond conv s y v' res true)
        (ensures PPB.l2r_safe_writer_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) y v' res true)
= match conv y with
  | None -> ()
  | Some x ->
    let sz = Seq.length (serialize s x) in
    if vmin <= sz && sz <= vmax
    then serialize_bounded_vlgen_unfold vmin vmax ssk s (x <: parse_bounded_vldata_strong_t vmin vmax s)
    else ()

(* Step A' (trial-write success => size postcond).  A SUCCESSFUL payload write
   observes the exact serialized payload size [res] (its postcondition guarantees
   [conv y = Some x] and [SZ.v res == Seq.length (serialize s x)]).  This is
   exactly the information the size pass [psz] would have returned on success, so
   we can reuse the very same in-bounds writing lemmas.  The [len < pow2 16 ==>
   err == false] clause of the size postcond is vacuously satisfied (err==false
   here). *)
let writer_success_implies_size_postcond
  (#tm #t: Type)
  (#k: parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (y: tm)
  (v': Seq.seq byte)
  (res: SZ.t)
: Lemma (requires PPB.l2r_safe_writer_postcond conv s y v' res false)
        (ensures PPB.l2r_safe_size_postcond conv s y res false)
= match conv y with
  | None -> ()
  | Some x -> ()

(* Step B: the size pass succeeded but the payload size is out of [vmin, vmax];
   the framing conv is None, so err=true. *)
let vlgen_oob_lemma
  (#tm #t: Type)
  (vmin: nat)
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (y: tm)
  (n: SZ.t)
  (v: Seq.seq byte)
  (res: SZ.t)
: Lemma (requires
    PPB.l2r_safe_size_postcond conv s y n false /\
    ~(vmin <= SZ.v n /\ SZ.v n <= vmax))
  (ensures PPB.l2r_safe_writer_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) y v res true)
= match conv y with
  | None -> ()
  | Some y' -> ()

(* Step C: not enough room even for the length header.  The output bytes are
   unchanged ([v]); since the total serialized length is at least the header
   length, [Seq.length v < total], so err=true. *)
let vlgen_header_noroom_lemma
  (#tm #t: Type)
  (vmin: nat)
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (y: tm)
  (n: SZ.t)
  (v: Seq.seq byte)
  (res: SZ.t)
: Lemma (requires
    PPB.l2r_safe_size_postcond conv s y n false /\
    vmin <= SZ.v n /\ SZ.v n <= vmax /\
    Seq.length v < Seq.length (serialize ssk (U32.uint_to_t (SZ.v n))))
  (ensures PPB.l2r_safe_writer_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) y v res true)
= match conv y with
  | None -> ()
  | Some y' ->
    let y'' : parse_bounded_vldata_strong_t vmin vmax s = y' in
    serialize_bounded_vlgen_unfold vmin vmax ssk s y''

(* Step D: the payload writer ran out of room.  The output bytes [v'] = header ++
   rest_post, with rest_post the (length-preserved) post-state of the payload
   region, and the payload writer's error flag (true) constrains rest_post so the
   total written length is below the full serialized length. *)
let vlgen_payload_noroom_lemma
  (#tm #t: Type)
  (vmin: nat)
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (y: tm)
  (n: SZ.t)
  (v': Seq.seq byte)
  (rest_post: Seq.seq byte)
  (res: SZ.t)
: Lemma (requires
    PPB.l2r_safe_size_postcond conv s y n false /\
    vmin <= SZ.v n /\ SZ.v n <= vmax /\
    PPB.l2r_safe_writer_postcond conv s y rest_post res true /\
    Seq.length v' == Seq.length (serialize ssk (U32.uint_to_t (SZ.v n))) + Seq.length rest_post)
  (ensures PPB.l2r_safe_writer_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) y v' res true)
= match conv y with
  | None -> ()
  | Some y' ->
    let y'' : parse_bounded_vldata_strong_t vmin vmax s = y' in
    serialize_bounded_vlgen_unfold vmin vmax ssk s y''

(* Step E: success.  The output bytes [v'] = hdr_written ++ rest_post where
   hdr_written is the serialized length header (the value [n32]) and
   rest_post[0, res) is the serialized payload. *)
let vlgen_success_lemma
  (#tm #t: Type)
  (vmin: nat)
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (y: tm)
  (n: SZ.t)
  (res: SZ.t)
  (tot: SZ.t)
  (hdr_written: Seq.seq byte)
  (rest_post: Seq.seq byte)
  (v': Seq.seq byte)
: Lemma (requires
    PPB.l2r_safe_size_postcond conv s y n false /\
    vmin <= SZ.v n /\ SZ.v n <= vmax /\
    PPB.l2r_safe_writer_postcond conv s y rest_post res false /\
    SZ.v tot == Seq.length (serialize ssk (U32.uint_to_t (SZ.v n))) + SZ.v res /\
    Seq.length hdr_written == Seq.length (serialize ssk (U32.uint_to_t (SZ.v n))) /\
    hdr_written == serialize ssk (U32.uint_to_t (SZ.v n)) /\
    SZ.v res <= Seq.length rest_post /\
    v' == Seq.append hdr_written rest_post)
  (ensures PPB.l2r_safe_writer_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) y v' tot false)
= match conv y with
  | None -> ()
  | Some y' ->
    let y'' : parse_bounded_vldata_strong_t vmin vmax s = y' in
    serialize_bounded_vlgen_unfold vmin vmax ssk s y'';
    vlgen_slice_append_prefix hdr_written rest_post (SZ.v res)

#push-options "--z3rlimit 64"

(* Shared "in-bounds writing" tail, factored out of the safe writer so it can be
   driven by EITHER the up-front size pass OR a trial write (see the writer below).
   Precondition [gsz]: the payload conv is [Some] and [n] is its exact serialized
   size (i.e. the size postcond holds with err=false).  Writes [header ++ payload]
   into [out], failing gracefully (err=true) iff the payload size is out of
   [vmin, vmax] or [out] cannot hold the framed bytes.  No fits_u64. *)
inline_for_extraction
fn write_bounded_vlgen_payload_in_bounds
  (vmin: nat) (vmin_u32: U32.t { (U32.v vmin_u32 <: nat) == vmin })
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 }) (vmax_u32: U32.t { (U32.v vmax_u32 <: nat) == vmax })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (hsize: (x: bounded_int32 vmin vmax -> Pure SZ.t (requires True) (ensures fun sz -> SZ.v sz == Seq.length (serialize ssk x) /\ SZ.v sz < pow2 64)))
  (hw: LPS.l2r_leaf_writer ssk)
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t) (#conv: tm -> GTot (option t))
  (s: serializer p)
  (pw: PPB.l2r_safe_writer vmatch s conv)
  (x: tl)
  (#y: Ghost.erased tm)
  (out: slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
  (n: SZ.t)
  (gsz: squash (PPB.l2r_safe_size_postcond conv s (Ghost.reveal y) n false))
  requires S.pts_to out v ** vmatch x y ** (exists* e. R.pts_to perr e)
  returns tot: SZ.t
  ensures exists* v' err. S.pts_to out v' ** vmatch x y ** R.pts_to perr err **
    pure (PPB.l2r_safe_writer_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) (Ghost.reveal y) v' tot err)
{
  let c1 = SC.u32_lte_sizet vmin_u32 n;
  let c2 = SC.sizet_lte_u32 n vmax_u32;
  if (not (c1 && c2)) {
    vlgen_oob_lemma vmin vmax ssk s conv (Ghost.reveal y) n (Ghost.reveal v) n;
    perr := true;
    n
  } else {
    FStar.Math.Lemmas.small_mod (SZ.v n) (pow2 32);
    let n32 : bounded_int32 vmin vmax = SZ.sizet_to_uint32 n;
    let h = hsize n32;
    S.pts_to_len out;
    let lout = S.len out;
    if (SZ.lt lout h) {
      vlgen_header_noroom_lemma vmin vmax ssk s conv (Ghost.reveal y) n (Ghost.reveal v) n;
      perr := true;
      n
    } else {
      let hdr, rest = S.split out h;
      S.pts_to_len hdr;
      S.pts_to_len rest;
      with hdr0. assert (S.pts_to hdr hdr0);
      let res_hdr = hw n32 hdr 0sz;
      with hdr_written. assert (S.pts_to hdr hdr_written);
      S.pts_to_len hdr;
      Seq.lemma_eq_elim hdr_written (Seq.slice hdr_written 0 (SZ.v h));
      let res2 = pw x rest perr;
      let e_pw = !perr;
      with rest_post. assert (S.pts_to rest rest_post);
      S.pts_to_len rest;
      if e_pw {
        vlgen_payload_noroom_lemma vmin vmax ssk s conv (Ghost.reveal y) n
          (Seq.append hdr_written rest_post) rest_post res2;
        S.join hdr rest out;
        perr := true;
        res2
      } else {
        SZ.fits_lte (SZ.v h + SZ.v res2) (SZ.v lout);
        let tot = SZ.add h res2;
        S.join hdr rest out;
        vlgen_success_lemma vmin vmax ssk s conv (Ghost.reveal y) n res2 tot
          hdr_written rest_post (Seq.append hdr_written rest_post);
        perr := false;
        tot
      }
    }
  }
}

(* l2r safe writer for bounded generic-length-prefixed data (vlgen): serialize the
   payload (via the sub-writer [pw]) preceded by a generic-length header written by
   [hw].  The payload's serialized size is normally computed up-front by the size
   pass [psz]; when [psz] reports an error (the fits_u64-free size contract only
   promises non-error below pow2 16, so a large-but-in-range payload can trip it)
   we FALL BACK to a trial write of the payload to observe its size portably.  We
   then split off the exact header region [h = hsize n], write the header, and
   write the payload.  Fails gracefully (err=true) iff the payload conv is None,
   the payload's serialized size is out of [vmin, vmax], or the output slice cannot
   hold the [header ++ payload] serialized bytes.  Sound on any >= 16-bit size_t. *)
inline_for_extraction
fn l2r_safe_writer_bounded_vlgen_payload
  (vmin: nat) (vmin_u32: U32.t { (U32.v vmin_u32 <: nat) == vmin })
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 }) (vmax_u32: U32.t { (U32.v vmax_u32 <: nat) == vmax })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (hsize: (x: bounded_int32 vmin vmax -> Pure SZ.t (requires True) (ensures fun sz -> SZ.v sz == Seq.length (serialize ssk x) /\ SZ.v sz < pow2 64)))
  (hw: LPS.l2r_leaf_writer ssk)
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t) (#conv: tm -> GTot (option t))
  (s: serializer p)
  (pw: PPB.l2r_safe_writer vmatch s conv)
  (psz: PPB.l2r_safe_size vmatch s conv)
: PPB.l2r_safe_writer (PPCV.vmatch_vldata_strong vmin vmax s vmatch) (serialize_bounded_vlgen vmin vmax ssk s) (PPCV.vldata_strong_conv vmin vmax s conv)
=
  (x: tl)
  (#y: Ghost.erased tm)
  (out: slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  unfold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
  let n = psz x perr;
  let e_sz = !perr;
  if e_sz {
    (* Size pass failed: fall back to a trial write to observe the payload size. *)
    let res_trial = pw x out perr;
    let e_trial = !perr;
    with v_trial. assert (S.pts_to out v_trial);
    if e_trial {
      vlgen_trial_fail_lemma vmin vmax ssk s conv (Ghost.reveal y) v_trial res_trial;
      fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
      res_trial
    } else {
      writer_success_implies_size_postcond s conv (Ghost.reveal y) v_trial res_trial;
      let tot = write_bounded_vlgen_payload_in_bounds vmin vmin_u32 vmax vmax_u32 ssk hsize hw s pw x out perr res_trial ();
      fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
      tot
    }
  } else {
    let tot = write_bounded_vlgen_payload_in_bounds vmin vmin_u32 vmax vmax_u32 ssk hsize hw s pw x out perr n ();
    fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
    tot
  }
}

#pop-options

(* ============================================================================ *)
(* Safe SIZE computation for bounded generic-length-prefixed data (vlgen)        *)
(* ============================================================================ *)

(* Size analog of Step A (size pass error): the payload size pass signalled an
   error.  Under the fits_u64-free size contract this only guarantees the payload
   conv is None OR the payload's serialized size is >= pow2 16 (NOT necessarily
   > vmax).  When the framing conv is None the framing err=true holds directly;
   when it is [Some] (payload in [vmin, vmax]) the framing size is [header ++
   payload] which is at least the payload size >= pow2 16, so the framing size
   postcond's [len < pow2 16 ==> err == false] clause is vacuous. *)
let vlgen_size_postcond_err_lemma
  (#tm #t: Type)
  (vmin: nat)
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (y: tm)
  (n: SZ.t)
: Lemma (requires PPB.l2r_safe_size_postcond conv s y n true)
        (ensures PPB.l2r_safe_size_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) y n true)
= match conv y with
  | None -> ()
  | Some y' ->
    let sz = Seq.length (serialize s y') in
    if vmin <= sz && sz <= vmax
    then serialize_bounded_vlgen_unfold vmin vmax ssk s (y' <: parse_bounded_vldata_strong_t vmin vmax s)
    else ()

(* Size analog of Step B (out of bounds): the size pass succeeded but the payload
   size is out of [vmin, vmax]; the framing conv is None, so err=true. *)
let vlgen_size_postcond_oob_lemma
  (#tm #t: Type)
  (vmin: nat)
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (y: tm)
  (n: SZ.t)
: Lemma (requires
    PPB.l2r_safe_size_postcond conv s y n false /\
    ~(vmin <= SZ.v n /\ SZ.v n <= vmax))
  (ensures PPB.l2r_safe_size_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) y n true)
= match conv y with
  | None -> ()
  | Some y' -> ()

(* Size analog of Step E (success): the total serialized size [tot] is the header
   size (for value [n32 = U32.uint_to_t (SZ.v n)]) plus the payload size [n].  The
   parameters [tot] and [e] are taken straight from the fits_u64-free
   [size_add_checked] applied to the header size [h] and payload size [n]:
   [e == false ==> tot == h + n] (soundness) and [h + n < pow2 16 ==> e == false]
   (guaranteed non-error below pow2 16).  Since the framing size equals [h + n],
   both clauses of the framing size postcond follow directly. *)
let vlgen_size_success_lemma
  (#tm #t: Type)
  (vmin: nat)
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (y: tm)
  (n: SZ.t)
  (h: SZ.t)
  (tot: SZ.t)
  (e: bool)
: Lemma (requires
    PPB.l2r_safe_size_postcond conv s y n false /\
    vmin <= SZ.v n /\ SZ.v n <= vmax /\
    SZ.v h == Seq.length (serialize ssk (U32.uint_to_t (SZ.v n))) /\
    (e == false ==> SZ.v tot == SZ.v h + SZ.v n) /\
    (SZ.v h + SZ.v n < pow2 16 ==> e == false))
  (ensures PPB.l2r_safe_size_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) y tot e)
= match conv y with
  | None -> ()
  | Some y' ->
    let y'' : parse_bounded_vldata_strong_t vmin vmax s = y' in
    serialize_bounded_vlgen_unfold vmin vmax ssk s y''

#push-options "--z3rlimit 64"

(* l2r safe size for bounded generic-length-prefixed data (vlgen): compute the
   serialized byte size of the [header ++ payload] form, where the payload's size
   is computed by the sub-size pass [psz] and the header size for that value is
   given by [hsize].  No output buffer is touched.  Fails gracefully (err=true)
   iff the payload conv is None, the payload's serialized size is out of
   [vmin, vmax], or the (header + payload) size overflows a machine word (which
   cannot happen in practice for these bounds, but is still discharged). *)
inline_for_extraction
fn l2r_safe_size_bounded_vlgen_payload
  (vmin: nat) (vmin_u32: U32.t { (U32.v vmin_u32 <: nat) == vmin })
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 }) (vmax_u32: U32.t { (U32.v vmax_u32 <: nat) == vmax })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (hsize: (x: bounded_int32 vmin vmax -> Pure SZ.t (requires True) (ensures fun sz -> SZ.v sz == Seq.length (serialize ssk x) /\ SZ.v sz < pow2 64)))
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t) (#conv: tm -> GTot (option t))
  (s: serializer p)
  (psz: PPB.l2r_safe_size vmatch s conv)
: PPB.l2r_safe_size (PPCV.vmatch_vldata_strong vmin vmax s vmatch) (serialize_bounded_vlgen vmin vmax ssk s) (PPCV.vldata_strong_conv vmin vmax s conv)
=
  (x: tl)
  (#y: Ghost.erased tm)
  (perr: R.ref bool)
{
  unfold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
  let n = psz x perr;
  let e_sz = !perr;
  if e_sz {
    vlgen_size_postcond_err_lemma vmin vmax ssk s conv (Ghost.reveal y) n;
    perr := true;
    fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
    n
  } else {
    let c1 = SC.u32_lte_sizet vmin_u32 n;
    let c2 = SC.sizet_lte_u32 n vmax_u32;
    if (not (c1 && c2)) {
      vlgen_size_postcond_oob_lemma vmin vmax ssk s conv (Ghost.reveal y) n;
      perr := true;
      fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
      n
    } else {
      FStar.Math.Lemmas.small_mod (SZ.v n) (pow2 32);
      let n32 : bounded_int32 vmin vmax = SZ.sizet_to_uint32 n;
      let h = hsize n32;
      let tot = PPB.size_add_checked h n perr;
      let e = !perr;
      vlgen_size_success_lemma vmin vmax ssk s conv (Ghost.reveal y) n h tot e;
      fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
      tot
    }
  }
}

#pop-options

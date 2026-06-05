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
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
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
    SZ.fits_u64_implies_fits_32 ();
    PPCF.validate_fldata_strong s v (SZ.uint32_to_sizet len) input poffset
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
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
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
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
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
    SZ.fits_u64_implies_fits_32 ();
    PPCF.validate_fldata v (SZ.uint32_to_sizet len) input poffset
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
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
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
  SZ.fits_u64_implies_fits_32 ();
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
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
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
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.accessor (parse_bounded_vlgen vmin vmax pk s) p (PPCV.clens_bounded_vldata_strong vmin vmax s)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t vmin vmax s))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
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
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.accessor (parse_vlgen vmin vmax pk s) p (clens_id t)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
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
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.copyful_parse (PPCV.vmatch_vldata_strong vmin vmax s vmatch) (parse_bounded_vlgen vmin vmax pk s) (PPCV.vldata_strong_conv vmin vmax s conv)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t vmin vmax s))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
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

(* Step A: the size pass signalled an error.  Either the payload conv is None, or
   the payload's serialized size does not fit in a machine word (>= pow2 64), in
   which case it exceeds [vmax]; either way the framing conv is None and err=true. *)
let vlgen_size_err_lemma
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
: Lemma (requires PPB.l2r_safe_size_postcond conv s y n true)
        (ensures PPB.l2r_safe_writer_postcond (PPCV.vldata_strong_conv vmin vmax s conv) (serialize_bounded_vlgen vmin vmax ssk s) y v res true)
= assert_norm (pow2 64 == 18446744073709551616);
  match conv y with
  | None -> ()
  | Some y' -> ()

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

(* l2r safe writer for bounded generic-length-prefixed data (vlgen): serialize the
   payload (via the sub-writer [pw]) preceded by a generic-length header written by
   [hw].  Unlike the fixed-width vldata combinator, the header value [n] is computed
   up-front by the size pass [psz], so no backpatch is needed: we split off the
   exact header region [h = hsize n], write the header, then write the payload into
   the rest.  Fails gracefully (err=true) iff the payload conv is None, the payload's
   serialized size is out of [vmin, vmax], or the output slice cannot hold the
   [header ++ payload] serialized bytes. *)
inline_for_extraction
fn l2r_safe_writer_bounded_vlgen_payload
  (vmin: nat) (vmin_sz: SZ.t { SZ.v vmin_sz == vmin })
  (vmax: nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 }) (vmax_sz: SZ.t { SZ.v vmax_sz == vmax })
  (#sk: parser_kind) (#pk: parser sk (bounded_int32 vmin vmax))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong })
  (hsize: (x: bounded_int32 vmin vmax -> Pure SZ.t (requires True) (ensures fun sz -> SZ.v sz == Seq.length (serialize ssk x) /\ SZ.v sz < pow2 64)))
  (hw: LPS.l2r_leaf_writer ssk)
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t) (#conv: tm -> GTot (option t))
  (s: serializer p)
  (pw: PPB.l2r_safe_writer vmatch s conv)
  (psz: PPB.l2r_safe_size vmatch s conv)
  (sq: squash FStar.SizeT.fits_u64)
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
    vlgen_size_err_lemma vmin vmax ssk s conv (Ghost.reveal y) n (Ghost.reveal v) n;
    perr := true;
    fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
    n
  } else {
    if (SZ.lt n vmin_sz || SZ.lt vmax_sz n) {
      vlgen_oob_lemma vmin vmax ssk s conv (Ghost.reveal y) n (Ghost.reveal v) n;
      perr := true;
      fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
      n
    } else {
      SZ.fits_u64_implies_fits_32 ();
      FStar.Math.Lemmas.small_mod (SZ.v n) (pow2 32);
      let n32 : bounded_int32 vmin vmax = SZ.sizet_to_uint32 n;
      let h = hsize n32;
      S.pts_to_len out;
      let lout = S.len out;
      if (SZ.lt lout h) {
        vlgen_header_noroom_lemma vmin vmax ssk s conv (Ghost.reveal y) n (Ghost.reveal v) n;
        perr := true;
        fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
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
          fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
          res2
        } else {
          SZ.fits_lte (SZ.v h + SZ.v res2) (SZ.v lout);
          let tot = SZ.add h res2;
          S.join hdr rest out;
          vlgen_success_lemma vmin vmax ssk s conv (Ghost.reveal y) n res2 tot
            hdr_written rest_post (Seq.append hdr_written rest_post);
          perr := false;
          fold (PPCV.vmatch_vldata_strong vmin vmax s vmatch x y);
          tot
        }
      }
    }
  }
}

#pop-options

module LowParse.Pulse.R2L
#lang-pulse
include LowParse.Spec.VCList
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice.Util
open Pulse.Lib.Trade
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice

(* Right-to-left (R2L) serializers.

   An R2L writer serializes a value into the output slice `out` *backwards*:
   the position out-parameter `pos` initially points just past the free space
   `out[0..pos)`; on success, the encoding is written to `out[pos'..pos)` and
   `pos` is moved leftwards to `pos'`. The bytes at or to the right of the
   initial position are never touched.

   R2L writers are fallible: they return `false` if and only if there is not
   enough room, i.e. iff the encoding is longer than the initial position. In
   that case, the new position and the contents of `out[0..pos)` are
   unspecified.

   The point of writing right-to-left is that length-prefixed encodings
   (e.g. DER TLVs) can be produced in a single pass, without a size
   pre-computation pass: the payload is written first, then its length is
   known and the header can be written to its left (see `r2l_write_framed`.)

   Most combinators are stated over an arbitrary encoding function
   `enc: t -> GTot bytes`, related to a low-level value by `vmatch`;
   `r2l_writer vmatch s` is the special case `enc = bare_serialize s`.
*)

(* Specification *)

let r2l_post (enc: bytes) (p: nat) (v: bytes) (res: bool) (p': nat) (v': bytes) : prop =
  Seq.length v' == Seq.length v /\
  p <= Seq.length v /\
  Seq.slice v' p (Seq.length v) == Seq.slice v p (Seq.length v) /\
  (res == true <==> Seq.length enc <= p) /\
  (res == true ==> (p' + Seq.length enc == p /\ Seq.slice v' p' p == enc))

inline_for_extraction
let r2l_writer_f (#t' #t: Type0) (vmatch: t' -> t -> slprop) (enc: t -> GTot bytes) =
  (x': t') -> (#x: Ghost.erased t) ->
  (out: slice byte) -> (pos: ref SZ.t) -> (#v: Ghost.erased bytes) -> (#p: Ghost.erased SZ.t) ->
  stt bool
    (pts_to out v ** pts_to pos p ** vmatch x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** vmatch x' x **
       pure (r2l_post (enc x) (SZ.v p) v res (SZ.v p') v'))

inline_for_extraction
let r2l_writer (#t' #t: Type0) (vmatch: t' -> t -> slprop) (#k: parser_kind) (#p: parser k t) (s: serializer p) =
  r2l_writer_f vmatch (bare_serialize s)

inline_for_extraction
let r2l_leaf_writer (#t: Type0) (enc: t -> GTot bytes) =
  r2l_writer_f (eq_as_slprop t) enc

type jit_writer_result =
| JIT_WRITER_OK
| JIT_WRITER_NO_SPACE
| JIT_WRITER_INVALID

let r2l_jit_post (#t #t0: Type0) (f: (t -> GTot (option t0))) (enc: t0 -> GTot bytes) (x: t) (p: nat) (v: bytes) (res: jit_writer_result) (p': nat) (v': bytes) : prop =
  Seq.length v' == Seq.length v /\
  p <= Seq.length v /\
  Seq.slice v' p (Seq.length v) == Seq.slice v p (Seq.length v) /\
  begin match res with
  | JIT_WRITER_OK -> Some? (f x) /\ Seq.length (enc (Some?.v (f x))) <= p
  | JIT_WRITER_NO_SPACE -> Some? (f x) ==> Seq.length (enc (Some?.v (f x))) > p
  | JIT_WRITER_INVALID -> None? (f x)
  end /\
  (res == JIT_WRITER_OK ==> (p' + Seq.length (enc (Some?.v (f x))) == p /\ Seq.slice v' p' p == enc (Some?.v (f x))))

inline_for_extraction
let r2l_jit_writer (#t' #t #t0: Type0) (vmatch: t' -> t -> slprop) (#k: parser_kind) (#p: parser k t0) (s: serializer p) (f: (t -> GTot (option t0))) =
  (x': t') -> (#x: Ghost.erased t) ->
  (out: slice byte) -> (pos: ref SZ.t) -> (#v: Ghost.erased bytes) -> (#p: Ghost.erased SZ.t) ->
  stt jit_writer_result
    (pts_to out v ** pts_to pos p ** vmatch x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** vmatch x' x **
       pure (r2l_jit_post f s x (SZ.v p) v res (SZ.v p') v'))


(* Sequence lemmas *)

let r2l_post_append
  (enc1 enc2: bytes) (p: nat) (v: bytes) (p1: nat) (v1: bytes) (res: bool) (p2: nat) (v2: bytes)
: Lemma
  (requires r2l_post enc2 p v true p1 v1 /\ r2l_post enc1 p1 v1 res p2 v2)
  (ensures r2l_post (enc1 `Seq.append` enc2) p v res p2 v2)
= let n = Seq.length v in
  Seq.slice_slice v1 p1 n (p - p1) (n - p1);
  Seq.slice_slice v2 p1 n (p - p1) (n - p1);
  Seq.slice_slice v1 p1 n 0 (p - p1);
  Seq.slice_slice v2 p1 n 0 (p - p1);
  if res then begin
    assert (Seq.equal (Seq.slice v2 p2 p) (Seq.append (Seq.slice v2 p2 p1) (Seq.slice v2 p1 p)))
  end

let r2l_post_false_weaken
  (enc1 enc2: bytes) (p: nat) (v: bytes) (p': nat) (v': bytes)
: Lemma
  (requires r2l_post enc1 p v false p' v' /\ Seq.length enc1 <= Seq.length enc2)
  (ensures r2l_post enc2 p v false p' v')
= ()

let r2l_post_empty
  (p: nat) (v: bytes)
: Lemma
  (requires p <= Seq.length v)
  (ensures r2l_post Seq.empty p v true p v)
= assert (Seq.equal (Seq.slice v p p) Seq.empty)

(* Structural combinators *)

inline_for_extraction
fn r2l_writer_ext
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#enc1: t -> GTot bytes)
  (w: r2l_writer_f vmatch enc1)
  (enc2: (t -> GTot bytes) { forall x . enc1 x == enc2 x })
: r2l_writer_f #t' #t vmatch enc2
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  w x' out pos
}

inline_for_extraction
fn r2l_writer_serializer_ext
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (w: r2l_writer vmatch s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2 { forall b . parse p1 b == parse p2 b })
: r2l_writer #t' #t vmatch #k2 #p2 s2
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  serializer_unique_strong s1 s2 x;
  w x' out pos
}

inline_for_extraction
fn r2l_writer_ifthenelse
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (enc: t -> GTot bytes)
  (cond: bool)
  (iftrue: (squash (cond == true) -> r2l_writer_f vmatch enc))
  (iffalse: (squash (cond == false) -> r2l_writer_f vmatch enc))
: r2l_writer_f #t' #t vmatch enc
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  if (cond) {
    iftrue () x' out pos
  } else {
    iffalse () x' out pos
  }
}

inline_for_extraction
fn r2l_writer_ifthenelse_low
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (enc: t -> GTot bytes)
  (cond: (t' -> bool))
  (iftrue: r2l_writer_f (vmatch_with_cond vmatch cond) enc)
  (iffalse: r2l_writer_f (vmatch_with_cond vmatch (pnot cond)) enc)
: r2l_writer_f #t' #t vmatch enc
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  if (cond x') {
    fold (vmatch_with_cond vmatch cond x' x);
    let res = iftrue x' out pos;
    unfold (vmatch_with_cond vmatch cond x' x);
    res
  } else {
    fold (vmatch_with_cond vmatch (pnot cond) x' x);
    let res = iffalse x' out pos;
    unfold (vmatch_with_cond vmatch (pnot cond) x' x);
    res
  }
}

inline_for_extraction
fn r2l_writer_frame
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#enc: t -> GTot bytes)
  (const: slprop)
  (w: r2l_writer_f vmatch enc)
: r2l_writer_f #t' #t (vmatch_and_const const vmatch) enc
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  unfold (vmatch_and_const const vmatch x' x);
  let res = w x' out pos;
  fold (vmatch_and_const const vmatch x' x);
  res
}

inline_for_extraction
fn r2l_writer_lens
  (#t1' #t2' #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#vmatch2: t2' -> t -> slprop)
  (lens: vmatch_lens vmatch1 vmatch2)
  (#enc: t -> GTot bytes)
  (w: r2l_writer_f vmatch2 enc)
: r2l_writer_f #t1' #t vmatch1 enc
= (x1': t1')
  (#x: Ghost.erased t)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  let x2' = lens x1' _;
  let res = w x2' out pos;
  elim_trade _ _;
  res
}

inline_for_extraction
fn r2l_writer_ext_gen
  (#t' #t1 #t2: Type0)
  (#vmatch: t' -> t2 -> slprop)
  (#enc1: t1 -> GTot bytes)
  (w: r2l_writer_f (vmatch_ext t1 vmatch) enc1)
  (enc2: (t2 -> GTot bytes) { t1 == t2 /\ (forall (x: t1) . enc1 x == enc2 x) })
: r2l_writer_f #t' #t2 vmatch enc2
= (x': t')
  (#x: Ghost.erased t2)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  let x1 : Ghost.erased t1 = Ghost.hide #t1 (Ghost.reveal #t2 x);
  fold (vmatch_ext t1 vmatch x' x1);
  let res = w x' out pos;
  unfold (vmatch_ext t1 vmatch x' x1);
  with x2 . assert (vmatch x' x2);
  rewrite (vmatch x' x2) as (vmatch x' x);
  res
}

let enc_empty (t: Type) (x: t) : GTot bytes = Seq.empty

inline_for_extraction
fn r2l_write_empty
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
: r2l_writer_f #t' #t vmatch (enc_empty t)
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  r2l_post_empty (SZ.v p) v;
  true
}

let enc_empty_zero_size
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_high == Some 0))
  (x: t)
: Lemma
  (enc_empty t x == bare_serialize s x)
= serialize_length s x;
  assert (Seq.equal (bare_serialize s x) Seq.empty)

inline_for_extraction
let r2l_writer_zero_size
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_high == Some 0))
: r2l_writer #t' #t vmatch #k #p s
= r2l_writer_ext (r2l_write_empty vmatch) (Classical.forall_intro (enc_empty_zero_size s sq); bare_serialize s)

(* Primitive writers *)

let enc_byte (x: byte) : GTot bytes = Seq.create 1 x

inline_for_extraction
fn r2l_write_byte
  (_: unit)
: r2l_leaf_writer #byte enc_byte
= (x': byte)
  (#x: Ghost.erased byte)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  unfold (eq_as_slprop byte x' x);
  fold (eq_as_slprop byte x' x);
  let vp = !pos;
  if (SZ.gt vp 0sz) {
    S.pts_to_len out;
    let vp' = SZ.sub vp 1sz;
    S.(out.(vp') <- x');
    pos := vp';
    with v' . assert (pts_to out v');
    assert (pure (Seq.equal (Seq.slice v' (SZ.v vp') (SZ.v vp)) (enc_byte x)));
    assert (pure (Seq.equal (Seq.slice v' (SZ.v vp) (Seq.length v)) (Seq.slice v (SZ.v vp) (Seq.length v))));
    true
  } else {
    false
  }
}

let vmatch_bytes (pm: perm) (s: slice byte) (w: bytes) : slprop =
  S.pts_to s #pm w

let enc_bytes (w: bytes) : GTot bytes = w

inline_for_extraction
fn r2l_write_copy
  (pm: perm)
: r2l_writer_f #(slice byte) #bytes (vmatch_bytes pm) enc_bytes
= (x': slice byte)
  (#x: Ghost.erased bytes)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  unfold (vmatch_bytes pm x' x);
  S.pts_to_len x';
  S.pts_to_len out;
  let len = S.len x';
  let vp = !pos;
  if (SZ.lt vp len) {
    fold (vmatch_bytes pm x' x);
    false
  } else {
    let vp' = SZ.sub vp len;
    let sp1, sp23 = S.split out vp';
    with v23 . assert (pts_to sp23 v23);
    let sp2, sp3 = S.split sp23 len;
    S.pts_to_len sp2;
    S.copy sp2 x';
    S.join sp2 sp3 sp23;
    S.join sp1 sp23 out;
    pos := vp';
    fold (vmatch_bytes pm x' x);
    with v' . assert (pts_to out v');
    assert (pure (Seq.equal (Seq.slice v' (SZ.v vp') (SZ.v vp)) x));
    assert (pure (Seq.equal (Seq.slice v' (SZ.v vp) (Seq.length v)) (Seq.slice v (SZ.v vp) (Seq.length v))));
    true
  }
}

(* Sequencing *)

let enc_pair
  (#t1 #t2: Type)
  (enc1: t1 -> GTot bytes)
  (enc2: t2 -> GTot bytes)
  (x: (t1 & t2))
: GTot bytes
= enc1 (fst x) `Seq.append` enc2 (snd x)

inline_for_extraction
fn r2l_write_nondep_then
  (#tl1 #tl2 #th1 #th2: Type0)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#enc1: th1 -> GTot bytes)
  (w1: r2l_writer_f vmatch1 enc1)
  (#vmatch2: tl2 -> th2 -> slprop)
  (#enc2: th2 -> GTot bytes)
  (w2: r2l_writer_f vmatch2 enc2)
  (#tl: Type0)
  (vmatch: tl -> (th1 & th2) -> slprop)
  (f1: (xl: tl) -> (xh: Ghost.erased (th1 & th2)) -> stt tl1
    (vmatch xl xh)
    (fun xl1 -> vmatch1 xl1 (fst xh) ** trade (vmatch1 xl1 (fst xh)) (vmatch xl xh))
  )
  (f2: (xl: tl) -> (xh: Ghost.erased (th1 & th2)) -> stt tl2
    (vmatch xl xh)
    (fun xl2 -> vmatch2 xl2 (snd xh) ** trade (vmatch2 xl2 (snd xh)) (vmatch xl xh))
  )
: r2l_writer_f #tl #(th1 & th2) vmatch (enc_pair enc1 enc2)
= (x': tl)
  (#x: Ghost.erased (th1 & th2))
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  let x2 = f2 x' x;
  let res2 = w2 x2 #(Ghost.hide (snd x)) out pos;
  Trade.elim _ _;
  if (res2) {
    with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
    let x1 = f1 x' x;
    let res1 = w1 x1 #(Ghost.hide (fst x)) out pos;
    Trade.elim _ _;
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    r2l_post_append (enc1 (fst x)) (enc2 (snd x)) (SZ.v p) v (SZ.v p1) v1 res1 (SZ.v p2) v2;
    res1
  } else {
    false
  }
}

inline_for_extraction
let r2l_write_nondep_then_direct
  (#tl1 #tl2 #th1 #th2: Type0)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#enc1: th1 -> GTot bytes)
  (w1: r2l_writer_f vmatch1 enc1)
  (#vmatch2: tl2 -> th2 -> slprop)
  (#enc2: th2 -> GTot bytes)
  (w2: r2l_writer_f vmatch2 enc2)
: r2l_writer_f #(tl1 & tl2) #(th1 & th2) (vmatch_pair vmatch1 vmatch2) (enc_pair enc1 enc2)
= r2l_write_nondep_then
    w1
    w2
    _
    (l2r_write_nondep_then_direct_proj1 vmatch1 vmatch2)
    (l2r_write_nondep_then_direct_proj2 vmatch1 vmatch2)

let enc_pair_serialize_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 & t2)
: Lemma
  (enc_pair (bare_serialize s1) (bare_serialize s2) x == bare_serialize (serialize_nondep_then s1 s2) x)
= serialize_nondep_then_eq s1 s2 x

inline_for_extraction
let r2l_write_serialize_nondep_then
  (#tl1 #tl2 #th1 #th2: Type0)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: r2l_writer vmatch1 s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#vmatch2: tl2 -> th2 -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 th2)
  (#s2: serializer p2)
  (w2: r2l_writer vmatch2 s2)
  (#tl: Type0)
  (vmatch: tl -> (th1 & th2) -> slprop)
  (f1: (xl: tl) -> (xh: Ghost.erased (th1 & th2)) -> stt tl1
    (vmatch xl xh)
    (fun xl1 -> vmatch1 xl1 (fst xh) ** trade (vmatch1 xl1 (fst xh)) (vmatch xl xh))
  )
  (f2: (xl: tl) -> (xh: Ghost.erased (th1 & th2)) -> stt tl2
    (vmatch xl xh)
    (fun xl2 -> vmatch2 xl2 (snd xh) ** trade (vmatch2 xl2 (snd xh)) (vmatch xl xh))
  )
: r2l_writer #tl #(th1 & th2) vmatch #(and_then_kind k1 k2) #(nondep_then p1 p2) (serialize_nondep_then s1 s2)
= r2l_writer_ext
    (r2l_write_nondep_then w1 w2 vmatch f1 f2)
    (Classical.forall_intro (enc_pair_serialize_nondep_then s1 s2); bare_serialize (serialize_nondep_then s1 s2))

let enc_synth
  (#t1 #t2: Type)
  (enc: t1 -> GTot bytes)
  (f21: t2 -> GTot t1)
  (x: t2)
: GTot bytes
= enc (f21 x)

inline_for_extraction
fn r2l_write_synth
  (#t' #t1 #t2: Type0)
  (#vmatch: t' -> t1 -> slprop)
  (#enc: t1 -> GTot bytes)
  (w: r2l_writer_f vmatch enc)
  (f21: t2 -> GTot t1)
: r2l_writer_f #t' #t2 (vmatch_synth vmatch f21) (enc_synth enc f21)
= (x': t')
  (#x: Ghost.erased t2)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  unfold (vmatch_synth vmatch f21 x' x);
  let res = w x' #(Ghost.hide (f21 x)) out pos;
  fold (vmatch_synth vmatch f21 x' x);
  res
}

inline_for_extraction
fn r2l_write_synth_recip
  (#t' #t1 #t2: Type0)
  (#vmatch: t' -> t2 -> slprop)
  (f12: t1 -> GTot t2)
  (f21: t2 -> GTot t1 { forall x . f12 (f21 x) == x })
  (#enc: t1 -> GTot bytes)
  (w: r2l_writer_f (vmatch_synth vmatch f12) enc)
: r2l_writer_f #t' #t2 vmatch (enc_synth enc f21)
= (x': t')
  (#x: Ghost.erased t2)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  rewrite (vmatch x' x) as (vmatch x' (f12 (f21 x)));
  fold (vmatch_synth vmatch f12 x' (f21 x));
  let res = w x' #(Ghost.hide (f21 x)) out pos;
  unfold (vmatch_synth vmatch f12 x' (f21 x));
  rewrite (vmatch x' (f12 (f21 x))) as (vmatch x' x);
  res
}

inline_for_extraction
let r2l_write_serialize_synth
  (#t' #t1 #t2: Type0)
  (#vmatch: t' -> t1 -> slprop)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: r2l_writer vmatch s1)
  (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
: r2l_writer #t' #t2 (vmatch_synth vmatch f1) #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= r2l_writer_ext
    (r2l_write_synth w f1)
    (Classical.forall_intro (serialize_synth_eq p1 f2 s1 f1 ()); bare_serialize (serialize_synth p1 f2 s1 f1 ()))

inline_for_extraction
let r2l_write_serialize_synth_recip
  (#t' #t1 #t2: Type0)
  (#vmatch: t' -> t2 -> slprop)
  (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: r2l_writer (vmatch_synth vmatch f2) s1)
: r2l_writer #t' #t2 vmatch #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= r2l_writer_ext
    (r2l_write_synth_recip f2 f1 w)
    (Classical.forall_intro (serialize_synth_eq p1 f2 s1 f1 ()); bare_serialize (serialize_synth p1 f2 s1 f1 ()))

(* Options and sums *)

let vmatch_option
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (xl: option tl)
  (xh: option th)
: slprop
= match xl with
  | None -> pure (xh == None)
  | Some a -> exists* b . vmatch a b ** pure (xh == Some b)

let enc_option
  (#t: Type)
  (enc: t -> GTot bytes)
  (x: option t)
: GTot bytes
= match x with
  | None -> Seq.empty
  | Some y -> enc y

inline_for_extraction
fn r2l_write_option
  (#tl #th: Type0)
  (#vmatch: tl -> th -> slprop)
  (#enc: th -> GTot bytes)
  (w: r2l_writer_f vmatch enc)
: r2l_writer_f #(option tl) #(option th) (vmatch_option vmatch) (enc_option enc)
= (x': option tl)
  (#x: Ghost.erased (option th))
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      unfold (vmatch_option vmatch None x);
      fold (vmatch_option vmatch None x);
      r2l_post_empty (SZ.v p) v;
      true
    }
    Some a -> {
      unfold (vmatch_option vmatch (Some a) x);
      with b . assert (vmatch a b);
      let res = w a #b out pos;
      fold (vmatch_option vmatch (Some a) x);
      res
    }
  }
}

let vmatch_either
  (#tl1 #th1 #tl2 #th2: Type0)
  (vmatch1: tl1 -> th1 -> slprop)
  (vmatch2: tl2 -> th2 -> slprop)
  (xl: either tl1 tl2)
  (xh: either th1 th2)
: slprop
= match xl with
  | Inl a -> exists* b . vmatch1 a b ** pure (xh == Inl b)
  | Inr a -> exists* b . vmatch2 a b ** pure (xh == Inr b)

let enc_either
  (#t1 #t2: Type)
  (enc1: t1 -> GTot bytes)
  (enc2: t2 -> GTot bytes)
  (x: either t1 t2)
: GTot bytes
= match x with
  | Inl y -> enc1 y
  | Inr y -> enc2 y

inline_for_extraction
fn r2l_write_either
  (#tl1 #th1 #tl2 #th2: Type0)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#enc1: th1 -> GTot bytes)
  (w1: r2l_writer_f vmatch1 enc1)
  (#vmatch2: tl2 -> th2 -> slprop)
  (#enc2: th2 -> GTot bytes)
  (w2: r2l_writer_f vmatch2 enc2)
: r2l_writer_f #(either tl1 tl2) #(either th1 th2) (vmatch_either vmatch1 vmatch2) (enc_either enc1 enc2)
= (x': either tl1 tl2)
  (#x: Ghost.erased (either th1 th2))
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  match x' {
    Inl a -> {
      unfold (vmatch_either vmatch1 vmatch2 (Inl a) x);
      with b . assert (vmatch1 a b);
      let res = w1 a #b out pos;
      fold (vmatch_either vmatch1 vmatch2 (Inl a) x);
      res
    }
    Inr a -> {
      unfold (vmatch_either vmatch1 vmatch2 (Inr a) x);
      with b . assert (vmatch2 a b);
      let res = w2 a #b out pos;
      fold (vmatch_either vmatch1 vmatch2 (Inr a) x);
      res
    }
  }
}

(* Length-prefixed (framed) encodings *)

let vmatch_sz (n: SZ.t) (m: nat) : slprop = pure (SZ.v n == m)

let enc_framed
  (#t: Type)
  (hdr_enc: nat -> GTot bytes)
  (enc: t -> GTot bytes)
  (x: t)
: GTot bytes
= let c = enc x in
  hdr_enc (Seq.length c) `Seq.append` c

inline_for_extraction
fn r2l_write_framed
  (#hdr_enc: nat -> GTot bytes)
  (hdr: r2l_writer_f vmatch_sz hdr_enc)
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#enc: t -> GTot bytes)
  (w: r2l_writer_f vmatch enc)
: r2l_writer_f #t' #t vmatch (enc_framed hdr_enc enc)
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  let p0 = !pos;
  let res = w x' out pos;
  if (res) {
    with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
    let vp1 = !pos;
    let len = SZ.sub p0 vp1;
    fold (vmatch_sz len (Seq.length (enc x)));
    let res' = hdr len #(Ghost.hide (Seq.length (enc x))) out pos;
    unfold (vmatch_sz len (Seq.length (enc x)));
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    r2l_post_append (hdr_enc (Seq.length (enc x))) (enc x) (SZ.v p) v (SZ.v p1) v1 res' (SZ.v p2) v2;
    res'
  } else {
    false
  }
}

let enc_sz_as_nat
  (enc: SZ.t -> GTot bytes)
  (n: nat)
: GTot bytes
= if SZ.fits n then enc (SZ.uint_to_t n) else Seq.empty

inline_for_extraction
fn r2l_writer_sz_of_leaf_writer
  (#enc: SZ.t -> GTot bytes)
  (w: r2l_leaf_writer enc)
: r2l_writer_f #SZ.t #nat vmatch_sz (enc_sz_as_nat enc)
= (x': SZ.t)
  (#x: Ghost.erased nat)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  unfold (vmatch_sz x' x);
  fold (vmatch_sz x' x);
  fold (eq_as_slprop SZ.t x' x');
  let res = w x' #(Ghost.hide x') out pos;
  unfold (eq_as_slprop SZ.t x' x');
  res
}

(* Leaf writers from left-to-right leaf writers of known size *)

let r2l_of_l2r_post_lemma
  (bs: bytes) (vp: nat) (v: bytes) (v1: bytes) (v1': bytes) (v2: bytes) (v': bytes)
: Lemma
  (requires
    Seq.length bs <= vp /\ vp <= Seq.length v /\
    v1 == Seq.slice v 0 vp /\ v2 == Seq.slice v vp (Seq.length v) /\
    Seq.length v1' == vp /\
    Seq.slice v1' (vp - Seq.length bs) vp == bs /\
    v' == Seq.append v1' v2)
  (ensures r2l_post bs vp v true (vp - Seq.length bs) v')
= assert (Seq.equal (Seq.slice v' (vp - Seq.length bs) vp) (Seq.slice v1' (vp - Seq.length bs) vp));
  assert (Seq.equal (Seq.slice v' vp (Seq.length v)) v2)

inline_for_extraction
fn r2l_leaf_writer_of_l2r
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: l2r_leaf_writer s)
  (sz: (x: t) -> (n: SZ.t { SZ.v n == Seq.length (bare_serialize s x) }))
: r2l_leaf_writer #t (bare_serialize s)
= (x': t)
  (#x: Ghost.erased t)
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p0: Ghost.erased SZ.t)
{
  unfold (eq_as_slprop t x' x);
  fold (eq_as_slprop t x' x);
  let vp = !pos;
  let n = sz x';
  if (SZ.lt vp n) {
    false
  } else {
    S.pts_to_len out;
    let sp1, sp2 = S.split out vp;
    with v1 . assert (pts_to sp1 v1);
    with v2 . assert (pts_to sp2 v2);
    S.pts_to_len sp1;
    let off = SZ.sub vp n;
    let _res = w x' sp1 off;
    with v1' . assert (pts_to sp1 v1');
    S.pts_to_len sp1;
    S.join sp1 sp2 out;
    r2l_of_l2r_post_lemma (bare_serialize s x) (SZ.v vp) v v1 v1' v2 (Seq.append v1' v2);
    pos := off;
    true
  }
}

(* Byte sequences given by their length and an index function, e.g. the
   encoding of a constant or of a small value computed on the fly *)

let indexed_inv (v: bytes) (e: bytes) (start: nat) (i: nat) (vi: bytes) : prop =
  start + Seq.length e <= Seq.length v /\
  i <= Seq.length e /\
  Seq.length vi == Seq.length v /\
  (forall (j: nat) . {:pattern (Seq.index vi j)} j < Seq.length v ==> Seq.index vi j == (
    if start <= j && j < start + i then Seq.index e (j - start) else Seq.index v j))

let indexed_inv_end (v: bytes) (e: bytes) (start: nat) (vi: bytes)
: Lemma
  (requires indexed_inv v e start (Seq.length e) vi)
  (ensures r2l_post e (start + Seq.length e) v true start vi)
= let p = start + Seq.length e in
  assert (Seq.equal (Seq.slice vi start p) e);
  assert (Seq.equal (Seq.slice vi p (Seq.length v)) (Seq.slice v p (Seq.length v)))

inline_for_extraction
fn r2l_write_indexed
  (len: SZ.t)
  (f: (i: SZ.t { SZ.v i < SZ.v len }) -> byte)
  (e: Ghost.erased bytes { Seq.length e == SZ.v len /\ (forall (i: nat) . i < SZ.v len ==> Seq.index e i == f (SZ.uint_to_t i)) })
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
requires pts_to out v ** pts_to pos p ** pure (SZ.v p <= Seq.length v)
returns res: bool
ensures exists* v' p' . pts_to out v' ** pts_to pos p' ** pure (r2l_post e (SZ.v p) v res (SZ.v p') v')
{
  let vp = !pos;
  if (SZ.lt vp len) {
    false
  } else {
    S.pts_to_len out;
    let start = SZ.sub vp len;
    let mut pi = 0sz;
    while (
      let i = !pi;
      SZ.lt i len
    ) invariant exists* vi i . pts_to out vi ** pts_to pi i ** pure (indexed_inv v e (SZ.v start) (SZ.v i) vi)
    decreases (SZ.v len - SZ.v (!pi))
    {
      let i = !pi;
      S.pts_to_len out;
      S.(out.(SZ.add start i) <- f i);
      pi := SZ.add i 1sz;
    };
    with vi . assert (pts_to out vi);
    indexed_inv_end v e (SZ.v start) vi;
    pos := start;
    true
  }
}

(* Arrays *)

let rec enc_seq
  (#t: Type)
  (enc: t -> GTot bytes)
  (s: Seq.seq t)
: GTot bytes
  (decreases (Seq.length s))
= if Seq.length s = 0
  then Seq.empty
  else enc (Seq.head s) `Seq.append` enc_seq enc (Seq.tail s)

let rec enc_seq_append
  (#t: Type)
  (enc: t -> GTot bytes)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures (enc_seq enc (Seq.append s1 s2) == Seq.append (enc_seq enc s1) (enc_seq enc s2)))
  (decreases (Seq.length s1))
= if Seq.length s1 = 0
  then begin
    assert (Seq.equal (Seq.append s1 s2) s2);
    assert (Seq.equal (Seq.append (enc_seq enc s1) (enc_seq enc s2)) (enc_seq enc s2))
  end else begin
    let s = Seq.append s1 s2 in
    assert (Seq.head s == Seq.head s1);
    assert (Seq.equal (Seq.tail s) (Seq.append (Seq.tail s1) s2));
    enc_seq_append enc (Seq.tail s1) s2;
    Seq.append_assoc (enc (Seq.head s1)) (enc_seq enc (Seq.tail s1)) (enc_seq enc s2)
  end

let enc_seq_slice_step
  (#t: Type)
  (enc: t -> GTot bytes)
  (s: Seq.seq t)
  (i: nat { 0 < i /\ i <= Seq.length s })
: Lemma
  (enc_seq enc (Seq.slice s (i - 1) (Seq.length s)) == enc (Seq.index s (i - 1)) `Seq.append` enc_seq enc (Seq.slice s i (Seq.length s)))
= let s' = Seq.slice s (i - 1) (Seq.length s) in
  assert (Seq.equal (Seq.tail s') (Seq.slice s i (Seq.length s)))

let enc_seq_slice_length
  (#t: Type)
  (enc: t -> GTot bytes)
  (s: Seq.seq t)
  (i: nat { i <= Seq.length s })
: Lemma
  (Seq.length (enc_seq enc (Seq.slice s i (Seq.length s))) <= Seq.length (enc_seq enc s))
= assert (Seq.equal s (Seq.append (Seq.slice s 0 i) (Seq.slice s i (Seq.length s))));
  enc_seq_append enc (Seq.slice s 0 i) (Seq.slice s i (Seq.length s))

let enc_seq_r2l_step
  (#t: Type)
  (enc: t -> GTot bytes)
  (s: Seq.seq t)
  (i: nat { 0 < i /\ i <= Seq.length s })
  (p: nat) (v: bytes) (p1: nat) (v1: bytes) (res: bool) (p2: nat) (v2: bytes)
: Lemma
  (requires (
    r2l_post (enc_seq enc (Seq.slice s i (Seq.length s))) p v true p1 v1 /\
    r2l_post (enc (Seq.index s (i - 1))) p1 v1 res p2 v2
  ))
  (ensures (
    (res == true ==> r2l_post (enc_seq enc (Seq.slice s (i - 1) (Seq.length s))) p v true p2 v2) /\
    (res == false ==> r2l_post (enc_seq enc s) p v false p2 v2)
  ))
= enc_seq_slice_step enc s i;
  r2l_post_append (enc (Seq.index s (i - 1))) (enc_seq enc (Seq.slice s i (Seq.length s))) p v p1 v1 res p2 v2;
  enc_seq_slice_length enc s (i - 1);
  if not res
  then r2l_post_false_weaken (enc_seq enc (Seq.slice s (i - 1) (Seq.length s))) (enc_seq enc s) p v p2 v2

let r2l_write_seq_slice_inv
  (#t: Type)
  (enc: t -> GTot bytes)
  (s: Seq.seq t)
  (p: nat) (v: bytes)
  (i: nat) (ok: bool) (p': nat) (v': bytes)
: Tot prop
= i <= Seq.length s /\
  (ok == true ==> r2l_post (enc_seq enc (Seq.slice s i (Seq.length s))) p v true p' v') /\
  (ok == false ==> r2l_post (enc_seq enc s) p v false p' v')

let vmatch_slice_seq (t: Type0) (pm: perm) (sl: slice t) (s: Seq.seq t) : slprop =
  S.pts_to sl #pm s

#push-options "--z3rlimit 32"

inline_for_extraction
fn r2l_write_seq_slice
  (#t: Type0)
  (#enc: t -> GTot bytes)
  (w: r2l_leaf_writer enc)
  (pm: perm)
: r2l_writer_f #(slice t) #(Seq.seq t) (vmatch_slice_seq t pm) (enc_seq enc)
= (x': slice t)
  (#x: Ghost.erased (Seq.seq t))
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  unfold (vmatch_slice_seq t pm x' x);
  S.pts_to_len x';
  let n = S.len x';
  r2l_post_empty (SZ.v p) v;
  assert (pure (Seq.equal (Seq.slice x (SZ.v n) (Seq.length x)) Seq.empty));
  let mut pi = n;
  let mut pok = true;
  while (
    let i = !pi;
    let ok = !pok;
    (ok && SZ.gt i 0sz)
  ) invariant exists* i ok v' p' .
    pts_to pi i ** pts_to pok ok **
    pts_to out v' ** pts_to pos p' **
    S.pts_to x' #pm x **
    pure (r2l_write_seq_slice_inv enc x (SZ.v p) v (SZ.v i) ok (SZ.v p') v')
  decreases %[(if !pok then 1 else 0); (SZ.v (!pi))]
  {
    with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
    let i = !pi;
    let i' = SZ.sub i 1sz;
    let a = S.(x'.(i'));
    fold (eq_as_slprop t a a);
    let res = w a #(Ghost.hide a) out pos;
    unfold (eq_as_slprop t a a);
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    enc_seq_r2l_step enc x (SZ.v i) (SZ.v p) v (SZ.v p1) v1 res (SZ.v p2) v2;
    if (res) {
      pi := i';
    } else {
      pok := false;
    }
  };
  fold (vmatch_slice_seq t pm x' x);
  let ok = !pok;
  if (ok) {
    with i . assert (pts_to pi i);
    assert (pure (Seq.equal (Seq.slice x (SZ.v i) (Seq.length x)) x));
    true
  } else {
    false
  }
}

#pop-options

let rec enc_list
  (#t: Type)
  (enc: t -> GTot bytes)
  (l: list t)
: GTot bytes
= match l with
  | [] -> Seq.empty
  | a :: q -> enc a `Seq.append` enc_list enc q

let rec enc_seq_seq_of_list
  (#t: Type)
  (enc: t -> GTot bytes)
  (l: list t)
: Lemma
  (ensures (enc_seq enc (Seq.seq_of_list l) == enc_list enc l))
  (decreases l)
= Seq.lemma_seq_of_list_induction l;
  match l with
  | [] -> ()
  | _ :: q -> enc_seq_seq_of_list enc q

let rec enc_list_serialize_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (l: nlist n t)
: Lemma
  (ensures (enc_list (bare_serialize s) l == bare_serialize (serialize_nlist n s) l))
  (decreases n)
= if n = 0
  then serialize_nlist_nil p s
  else begin
    let a :: q = l in
    enc_list_serialize_nlist (n - 1) s q;
    serialize_nlist_cons (n - 1) s a q
  end

let vmatch_slice_nlist (t: Type0) (pm: perm) (n: nat) (sl: slice t) (l: nlist n t) : slprop =
  S.pts_to sl #pm (Seq.seq_of_list l)

inline_for_extraction
fn r2l_write_nlist_slice
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: r2l_leaf_writer (bare_serialize s))
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (pm: perm)
  (n: Ghost.erased nat)
: r2l_writer #(slice t) #(nlist n t) (vmatch_slice_nlist t pm n) #(parse_nlist_kind n k) #(parse_nlist n p) (serialize_nlist n s)
= (x': slice t)
  (#x: Ghost.erased (nlist n t))
  (out: slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p: Ghost.erased SZ.t)
{
  unfold (vmatch_slice_nlist t pm n x' x);
  fold (vmatch_slice_seq t pm x' (Seq.seq_of_list x));
  let res = r2l_write_seq_slice w pm x' #(Ghost.hide (Seq.seq_of_list x)) out pos;
  unfold (vmatch_slice_seq t pm x' (Seq.seq_of_list x));
  fold (vmatch_slice_nlist t pm n x' x);
  enc_seq_seq_of_list (bare_serialize s) x;
  enc_list_serialize_nlist n s x;
  res
}

(* Smoke test *)

inline_for_extraction
let r2l_write_byte_pair
: r2l_writer_f #(byte & byte) #(byte & byte)
    (vmatch_pair (eq_as_slprop byte) (eq_as_slprop byte))
    (enc_pair enc_byte enc_byte)
= r2l_write_nondep_then_direct (r2l_write_byte ()) (r2l_write_byte ())

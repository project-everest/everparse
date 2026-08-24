module EverParse3d.InputStream.Buffer
open Pulse.Lib.Pervasives
#lang-pulse

(* The [buffer] backend: an input stream is a byte array [b] of length [len],
   together with a reference [pos] holding the number of bytes consumed so far.
   All three are passed as separate arguments, so that KaRaMeL extracts them as
   three C arguments instead of a struct. *)

module AP = Pulse.Lib.ArrayPtr
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module I = EverParse3d.InputStream.Base
module LP = LowParse.Spec.Base
module API = LowParse.Pulse.ArrayPtr.Int
module Trade = Pulse.Lib.Trade.Util
module Common = EverParse3d.Actions.Common
module CB = EverParse3d.CopyBuffer

let base_t = AP.ptr U8.t
let len_t = SZ.t
let pos_t = R.ref SZ.t

let stream_pts_to
  (b: base_t) (len: len_t) (pos: pos_t)
  (contents: Seq.seq U8.t) (v: Seq.seq U8.t)
: Tot slprop
= exists* (p: SZ.t).
    AP.pts_to b contents **
    R.pts_to pos p **
    pure (
      Seq.length contents == SZ.v len /\
      SZ.v p <= SZ.v len /\
      v == Seq.slice contents (SZ.v p) (SZ.v len)
    )

(* After [truncate], the enclosing stream keeps the ownership of the bytes
   beyond the truncation point, together with the fact that they are physically
   adjacent to the truncated prefix. *)
let stream_is_prefix_of
  (base_x: base_t) (len_x: len_t) (pos_x: pos_t)
  (base_y: base_t) (len_y: len_t) (pos_y: pos_t)
  (contents0: Seq.seq U8.t) (suffix: Seq.seq U8.t)
: Tot slprop
= exists* (s': base_t).
    AP.pts_to s' suffix **
    pure (
      base_x == base_y /\ pos_x == pos_y /\
      AP.adjacent base_x (SZ.v len_x) s' /\
      SZ.v len_x + Seq.length suffix == SZ.v len_y
    )

noextract
inline_for_extraction
let pts_to_inst : I.input_stream_pts_to base_t len_t pos_t = {
  pts_to = stream_pts_to;
  is_prefix_of = stream_is_prefix_of;
}

ghost
fn stream_pts_to_is_suffix_of
  (b: base_t) (len: len_t) (pos: pos_t)
  (contents: Seq.seq U8.t) (v: Seq.seq U8.t)
requires stream_pts_to b len pos contents v
ensures stream_pts_to b len pos contents v ** pure (v `I.seq_is_suffix_of` contents)
{
  unfold (stream_pts_to b len pos contents v);
  Seq.lemma_eq_elim
    (Seq.slice contents (Seq.length contents - Seq.length v) (Seq.length contents))
    v;
  fold (stream_pts_to b len pos contents v);
}

inline_for_extraction
fn stream_get_position
  (b: base_t) (len: len_t) (pos: pos_t)
  (contents: Ghost.erased (Seq.seq U8.t)) (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos contents v
returns res: SZ.t
ensures stream_pts_to b len pos contents v **
  pure (SZ.v res + Seq.length v == Seq.length contents)
{
  unfold (stream_pts_to b len pos contents v);
  let p = !pos;
  fold (stream_pts_to b len pos contents v);
  p
}

inline_for_extraction
fn stream_has
  (b: base_t) (len: len_t) (pos: pos_t) (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t)) (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos contents v
returns res: bool
ensures stream_pts_to b len pos contents v **
  pure (res == true <==> SZ.v n <= Seq.length v)
{
  unfold (stream_pts_to b len pos contents v);
  let p = !pos;
  let avail = SZ.sub len p;
  fold (stream_pts_to b len pos contents v);
  SZ.lte n avail
}

inline_for_extraction
fn stream_has_at
  (b: base_t) (len: len_t) (pos: pos_t) (off: SZ.t) (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t)) (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos contents v ** pure (SZ.v off <= Seq.length v)
returns res: bool
ensures stream_pts_to b len pos contents v ** pure (
  (res == true <==> SZ.v off + SZ.v n <= Seq.length v) /\
  (res == true ==> SZ.fits (SZ.v off + SZ.v n))
)
{
  unfold (stream_pts_to b len pos contents v);
  let p = !pos;
  let avail = SZ.sub (SZ.sub len p) off;
  fold (stream_pts_to b len pos contents v);
  SZ.lte n avail
}

inline_for_extraction
fn stream_skip
  (b: base_t) (len: len_t) (pos: pos_t) (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t)) (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos contents v ** pure (Seq.length v >= SZ.v n)
ensures exists* v' .
  stream_pts_to b len pos contents v' **
  pure (Seq.length v >= SZ.v n /\ v' `Seq.equal` Seq.slice v (SZ.v n) (Seq.length v))
{
  unfold (stream_pts_to b len pos contents v);
  let p = !pos;
  let p' = SZ.add p n;
  pos := p';
  Seq.lemma_eq_elim
    (Seq.slice contents (SZ.v p') (SZ.v len))
    (Seq.slice v (SZ.v n) (Seq.length v));
  fold (stream_pts_to b len pos contents (Seq.slice contents (SZ.v p') (SZ.v len)));
}

inline_for_extraction
fn stream_empty
  (b: base_t) (len: len_t) (pos: pos_t)
  (contents: Ghost.erased (Seq.seq U8.t)) (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos contents v
returns res: SZ.t
ensures stream_pts_to b len pos contents Seq.empty **
  pure (SZ.v res == Seq.length v)
{
  unfold (stream_pts_to b len pos contents v);
  let p = !pos;
  pos := len;
  Seq.lemma_eq_elim (Seq.slice contents (SZ.v len) (SZ.v len)) (Seq.empty #U8.t);
  fold (stream_pts_to b len pos contents (Seq.empty #U8.t));
  SZ.sub len p
}

inline_for_extraction
fn stream_truncate
  (b: base_t) (len: len_t) (pos: pos_t) (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t)) (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos contents v ** pure (SZ.v n <= Seq.length v)
returns res: (base_t & len_t & pos_t)
ensures exists* contents' v1 v2 .
  stream_pts_to res._1 res._2 res._3 contents' v1 **
  stream_is_prefix_of res._1 res._2 res._3 b len pos contents v2 **
  pure (
    SZ.v n <= Seq.length v /\
    Seq.equal v1 (Seq.slice v 0 (SZ.v n)) /\
    Seq.equal v2 (Seq.slice v (SZ.v n) (Seq.length v)) /\
    Seq.length v <= Seq.length contents /\
    Seq.equal contents' (Seq.append (Seq.slice contents 0 (Seq.length contents - Seq.length v)) v1) /\
    Ghost.reveal v == Seq.append v1 v2
  )
{
  unfold (stream_pts_to b len pos contents v);
  let p = !pos;
  let m = SZ.add p n;
  let s' = AP.ghost_split b m;
  Seq.lemma_eq_elim
    (Ghost.reveal v)
    (Seq.append
      (Seq.slice contents (SZ.v p) (SZ.v m))
      (Seq.slice contents (SZ.v m) (SZ.v len)));
  let bb : base_t = b;
  let mm : len_t = m;
  let pp : pos_t = pos;
  let ret : (base_t & len_t & pos_t) = (bb, mm, pp);
  fold (stream_pts_to b m pos
          (Seq.slice contents 0 (SZ.v m))
          (Seq.slice contents (SZ.v p) (SZ.v m)));
  fold (stream_is_prefix_of b m pos b len pos contents
          (Seq.slice contents (SZ.v m) (SZ.v len)));
  rewrite (stream_pts_to b m pos
             (Seq.slice contents 0 (SZ.v m))
             (Seq.slice contents (SZ.v p) (SZ.v m)))
    as (stream_pts_to ret._1 ret._2 ret._3
             (Seq.slice contents 0 (SZ.v m))
             (Seq.slice contents (SZ.v p) (SZ.v m)));
  rewrite (stream_is_prefix_of b m pos b len pos contents
             (Seq.slice contents (SZ.v m) (SZ.v len)))
    as (stream_is_prefix_of ret._1 ret._2 ret._3 b len pos contents
             (Seq.slice contents (SZ.v m) (SZ.v len)));
  ret
}

ghost
fn stream_untruncate
  (base_x: base_t) (len_x: len_t) (pos_x: pos_t)
  (base_y: base_t) (len_y: len_t) (pos_y: pos_t)
  (contents: Seq.seq U8.t) (v: Seq.seq U8.t)
  (contents0: Seq.seq U8.t) (suffix: Seq.seq U8.t)
requires
  stream_pts_to base_x len_x pos_x contents v **
  stream_is_prefix_of base_x len_x pos_x base_y len_y pos_y contents0 suffix **
  pure (contents0 == Seq.append contents suffix)
ensures stream_pts_to base_y len_y pos_y contents0 (Seq.append v suffix)
{
  unfold (stream_pts_to base_x len_x pos_x contents v);
  unfold (stream_is_prefix_of base_x len_x pos_x base_y len_y pos_y contents0 suffix);
  with s' . assert (AP.pts_to s' suffix);
  AP.join base_x s';
  with p . assert (R.pts_to pos_x p);
  rewrite (AP.pts_to base_x (Seq.append contents suffix))
    as (AP.pts_to base_y contents0);
  rewrite (R.pts_to pos_x p) as (R.pts_to pos_y p);
  Seq.lemma_eq_elim
    (Seq.append v suffix)
    (Seq.slice contents0 (SZ.v p) (SZ.v len_y));
  fold (stream_pts_to base_y len_y pos_y contents0 (Seq.append v suffix));
}

inline_for_extraction
fn stream_read
  (t': Type0) (k: LP.parser_kind) (p: LP.parser k t') (r: API.leaf_reader p)
  (b: base_t) (len: len_t) (pos: pos_t) (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t)) (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos contents v ** pure (
  k.LP.parser_kind_subkind == Some LP.ParserStrong /\
  k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
  k.LP.parser_kind_low == SZ.v n /\
  Some? (LP.parse p v)
)
returns dst': t'
ensures exists* v' .
  stream_pts_to b len pos contents v' ** pure (
  Seq.length v >= SZ.v n /\
  LP.parse p (Seq.slice v 0 (SZ.v n)) == Some (dst', SZ.v n) /\
  LP.parse p v == Some (dst', SZ.v n) /\
  Seq.equal v' (Seq.slice v (SZ.v n) (Seq.length v))
)
{
  LP.parser_kind_prop_equiv k p;
  unfold (stream_pts_to b len pos contents v);
  let p0 = !pos;
  let m = SZ.add p0 n;
  (* [AP.split] is pure pointer arithmetic: it extracts to [b + p0] and gives
     [sub] the ownership of the bytes from the current position onwards, which
     is exactly the remaining input [v]. The reader looks at the first [n] of
     them; the strong-prefix property makes the rest irrelevant. *)
  let sub = AP.split b p0;
  Seq.lemma_eq_elim (Seq.slice contents (SZ.v p0) (Seq.length contents)) v;
  let res = r sub;
  LP.parse_strong_prefix p v (Seq.slice v 0 (SZ.v n));
  (* [AP.join] is ghost, so restoring the whole buffer costs nothing at run
     time. *)
  AP.join b sub;
  Seq.lemma_eq_elim
    (Seq.append (Seq.slice contents 0 (SZ.v p0)) (Seq.slice contents (SZ.v p0) (Seq.length contents)))
    contents;
  pos := m;
  Seq.lemma_eq_elim
    (Seq.slice contents (SZ.v m) (SZ.v len))
    (Seq.slice v (SZ.v n) (Seq.length v));
  fold (stream_pts_to b len pos contents (Seq.slice contents (SZ.v m) (SZ.v len)));
  res
}

noextract
inline_for_extraction
instance input_stream_buffer : I.input_stream_inst base_t len_t pos_t = {
  pts_to_inst = pts_to_inst;
  pts_to_is_suffix_of = stream_pts_to_is_suffix_of;
  get_position = stream_get_position;
  has = stream_has;
  has_at = stream_has_at;
  read = stream_read;
  skip = stream_skip;
  empty = stream_empty;
  truncate = stream_truncate;
  untruncate = stream_untruncate;
}

(* The error handler used when 3d is invoked with `--use_error_handler_macro`.
   Each backend provides its own; the 3D frontend passes the one matching the
   selected `--input_stream` to `validate_with_error_handler`. *)
[@@CMacro]
assume val error_handler_macro : Common.error_handler #base_t #len_t #pos_t

(* Copy buffers, used as the destination of probe actions. Only the `buffer`
   backend provides them.

   A copy buffer is a *pointer* to the descriptor, not the descriptor itself,
   so that a probe callback can overwrite the latter -- in particular, repoint
   the buffer at the probed bytes rather than copying into it, as the Low*
   backend allows.

   The descriptor is a monomorphic record here rather than a polymorphic one
   in `EverParse3d.CopyBuffer`, so that KaRaMeL emits it under the stable name
   `EVERPARSE_COPY_BUFFER_DESCR` in `EverParse.h`. `copy_buffer_t` itself is
   an abbreviation and is inlined away by KaRaMeL, so the C type a wrapper
   sees is `EVERPARSE_COPY_BUFFER_DESCR *`; `EverParsePulseEndianness.h`
   defines `EVERPARSE_COPY_BUFFER_T` as exactly that. *)
noeq
type copy_buffer_descr = {
  cb_base: base_t;
  cb_len: len_t;
  cb_pos: pos_t;
}

type copy_buffer_t = R.ref copy_buffer_descr

(* Pulse eagerly eliminates a top-level `exists*` in a `requires`, which would
   give `copy_buffer_reset` a type with an extra ghost binder instead of the
   `stt` the class field expects. Hiding the existential behind this
   (transparent) definition keeps the two convertible. *)
let cb_pts_to (c: copy_buffer_t) (contents: Seq.seq U8.t) (v: Seq.seq U8.t) : Tot slprop =
  exists* (d: copy_buffer_descr).
    R.pts_to c d ** I.pts_to d.cb_base d.cb_len d.cb_pos contents v

inline_for_extraction
fn copy_buffer_reset
  (c: copy_buffer_t)
  (contents: Ghost.erased (Seq.seq U8.t)) (v: Ghost.erased (Seq.seq U8.t))
requires cb_pts_to c contents v
ensures cb_pts_to c contents contents
{
  unfold (cb_pts_to c contents v);
  with d. assert (R.pts_to c d ** I.pts_to d.cb_base d.cb_len d.cb_pos contents v);
  let dv = !c;
  rewrite (I.pts_to d.cb_base d.cb_len d.cb_pos contents v)
    as (stream_pts_to d.cb_base d.cb_len d.cb_pos contents v);
  unfold (stream_pts_to d.cb_base d.cb_len d.cb_pos contents v);
  dv.cb_pos := 0sz;
  Seq.lemma_eq_elim (Seq.slice contents 0 (SZ.v d.cb_len)) contents;
  fold (stream_pts_to d.cb_base d.cb_len d.cb_pos contents contents);
  rewrite (stream_pts_to d.cb_base d.cb_len d.cb_pos contents contents)
    as (I.pts_to d.cb_base d.cb_len d.cb_pos contents contents);
  fold (cb_pts_to c contents contents);
}

noextract
inline_for_extraction
instance copy_buffer_buffer : CB.copy_buffer copy_buffer_t base_t len_t pos_t = {
  descr_t = copy_buffer_descr;
  base_of = (fun d -> d.cb_base);
  len_of = (fun d -> d.cb_len);
  pos_of = (fun d -> d.cb_pos);
  descr = (fun c -> c);
  reset = copy_buffer_reset;
}

(* `field_ptr`: the address of the current position in the input stream.
   Only the `buffer` backend can provide it. *)
module AB = EverParse3d.Actions.Base

inline_for_extraction
fn field_ptr_impl
  (b: base_t) (len: len_t) (pos: pos_t)
  (contents: Ghost.erased (Seq.seq U8.t)) (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos contents v
returns res: AP.ptr U8.t
ensures stream_pts_to b len pos contents v
{
  unfold (stream_pts_to b len pos contents v);
  let p = !pos;
  let s' = AP.split b p;
  AP.join b s';
  Seq.lemma_split contents (SZ.v p);
  Seq.lemma_eq_elim
    (Seq.append (Seq.slice contents 0 (SZ.v p)) (Seq.slice contents (SZ.v p) (Seq.length contents)))
    contents;
  fold (stream_pts_to b len pos contents v);
  s'
}

[@@EverParse3d.Actions.Common.specialize_backend]
noextract
inline_for_extraction
let field_ptr
: option (AB.field_ptr_t base_t len_t pos_t #input_stream_buffer (AP.ptr U8.t))
= Some field_ptr_impl

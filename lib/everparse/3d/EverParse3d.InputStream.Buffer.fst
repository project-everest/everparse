module EverParse3d.InputStream.Buffer
open Pulse.Lib.Pervasives
#lang-pulse

(* The [buffer] backend: an input stream is a byte array [b] of length [len],
   together with a reference [pos] holding the number of bytes consumed so far.
   All three are passed as separate arguments, so that KaRaMeL extracts them as
   three C arguments instead of a struct. *)

module AP = Pulse.Lib.ArrayPtr
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module I = EverParse3d.InputStream.Base
module LP = LowParse.Spec.Base
module LPL = LowParse.PulseParse.Base
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

(* Undo [Pulse.Lib.Slice.subslice]: give back the ownership of the whole slice.
   [Pulse.Lib.Slice] exposes [subslice_rest] but no elimination form for it. *)
ghost
fn subslice_join
  (#t: Type0) (sub: S.slice t) (sl: S.slice t) (pm: perm) (i: SZ.t) (j: SZ.t)
  (v: Ghost.erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
requires
  S.pts_to sub #pm (Seq.slice v (SZ.v i) (SZ.v j)) **
  S.subslice_rest sub sl pm i j v
ensures S.pts_to sl #pm v
{
  unfold (S.subslice_rest sub sl pm i j v);
  with s1 s2 s3 . assert (
    S.is_split sl s1 s2 **
    S.is_split s2 sub s3
  );
  S.join sub s3 s2;
  S.join s1 s2 sl;
  Seq.lemma_eq_elim
    (Seq.append
      (Seq.slice v 0 (SZ.v i))
      (Seq.append
        (Seq.slice v (SZ.v i) (SZ.v j))
        (Seq.slice v (SZ.v j) (Seq.length v))))
    (Ghost.reveal v);
  rewrite (S.pts_to sl #pm
    (Seq.append
      (Seq.slice v 0 (SZ.v i))
      (Seq.append
        (Seq.slice v (SZ.v i) (SZ.v j))
        (Seq.slice v (SZ.v j) (Seq.length v)))))
    as (S.pts_to sl #pm v);
}

inline_for_extraction
fn stream_read
  (t': Type0) (k: LP.parser_kind) (p: LP.parser k t') (r: LPL.leaf_reader p)
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
  let sl = S.arrayptr_to_slice_intro b len;
  let sub = S.subslice sl p0 m;
  Seq.lemma_eq_elim
    (Seq.slice contents (SZ.v p0) (SZ.v m))
    (Seq.slice v 0 (SZ.v n));
  LP.parse_strong_prefix p v (Seq.slice v 0 (SZ.v n));
  let gv : Ghost.erased t' = Ghost.hide (fst (Some?.v (LP.parse p (Ghost.reveal v))));
  LPL.pts_to_parsed_intro p sub (Ghost.reveal gv);
  let res = r sub;
  Trade.elim _ _;
  subslice_join sub sl 1.0R p0 m contents;
  S.arrayptr_to_slice_elim sl;
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
   backend provides them. *)
noeq
type copy_buffer_t = {
  cb_base: base_t;
  cb_len: len_t;
  cb_pos: pos_t;
}

noextract
inline_for_extraction
instance copy_buffer_buffer : CB.copy_buffer copy_buffer_t base_t len_t pos_t = {
  base_of = (fun c -> c.cb_base);
  len_of = (fun c -> c.cb_len);
  pos_of = (fun c -> c.cb_pos);
}

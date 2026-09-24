module EverParse3d.InputStream.Extern
open Pulse.Lib.Pervasives
#lang-pulse

(* The [extern] backend: the input stream is an abstract, client-provided C
   object. Everything about it is assumed, exactly as in the Low* version
   (src/3d/prelude/extern/EverParse3d.InputStream.Extern.Base.fsti): the C
   client is trusted to implement the EverParseHas/Read/Peep/Skip/Empty
   primitives declared in EverParse.h.

   The stream carries its own length on the C side, so in the common case
   there is nothing for [len_t] to hold. It cannot be [unit] all the same:
   [t_exact], [t_at_most] and variable-size [nlist] truncate the stream to a
   sub-region, and that bound exists only on our side of the boundary. So
   [len_t] is [SZ.t], encoding an *optional* bound on the absolute stream
   position at which the current view ends:

     - [0]  -- unbounded: the view ends where the client says it does, and the
               [has]/[has_at]/[empty] primitives are forwarded to the client;
     - [n]  -- bounded: the view ends at absolute position [n - 1], and those
               three primitives are answered here instead, without asking the
               client. (The offset of one is what makes [0] available as the
               "unbounded" tag: a zero-length view at absolute position 0 is
               legal and must be distinguishable from it.)

   This mirrors the Low* backend, whose stream record carries a
   [has_length: bool] / [length: pos_t] pair and branches on it in exactly the
   same three places (src/3d/prelude/extern/EverParse3d.InputStream.Extern.fst,
   [has], [has_at], [empty]). A pair is not an option here: [len_t] is passed
   by value to every validator, and a struct would be monomorphized by KaRaMeL
   into whichever *generated* module used it first -- the very thing the
   [trunc_t] design in EverParse3d.InputStream.Base exists to avoid.

   Consequently truncation is a pure computation on [len_t] -- there is no
   `EverParseStreamTruncate` primitive for the client to implement -- and
   [trunc_t = len_t], as in the buffer backend.

   [pos_t] is [SZ.t] too: the *origin* of the current top-level
   validation, that is, the absolute stream position at which the wrapper
   invoked the validator. The stream's own position is cumulative across
   successive validations of the same stream, whereas the field positions that
   3D actions observe (`field_pos_32`, `field_pos_64`) must be offsets relative
   to the start of the record being validated -- that is what Low* gets from
   its explicit `StartPosition` argument, which the generated wrapper always
   passes as 0. So the origin is subtracted in [stream_get_relative_position],
   and it is threaded unchanged through nested type calls and truncations,
   exactly as Low* threads its `pos`.

   Every other primitive takes the origin as a [Ghost.erased], so that the C
   signatures the client has to implement (EverParseHas/Read/Peep/Skip/...)
   are unchanged; only the validators themselves gain the extra argument. *)

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module I = EverParse3d.InputStream.Base
module LP = LowParse.Spec.Base
module API = LowParse.Pulse.ArrayPtr.Int
module Common = EverParse3d.Actions.Common
module AP = Pulse.Lib.ArrayPtr

open EverParse3d.InputStream.Base { seq_is_suffix_of }

assume val input_stream_base : Type0

inline_for_extraction
noextract
let base_t = input_stream_base
(* [0] is "unbounded"; [n > 0] means the view ends at absolute position
   [n - 1]. See the header comment. *)
inline_for_extraction
noextract
let len_t = SZ.t
inline_for_extraction
noextract
let pos_t = SZ.t

(* The raw, client-side view of the stream. It takes no [len]: the client knows
   nothing of our truncation bounds, and dropping the argument here is what
   keeps the assumed C prototypes (EverParseStreamHas, ...Read, ...Skip, ...)
   exactly as they were. *)
assume val stream_pts_to_raw
  (base: base_t) (pos: Ghost.erased pos_t)
  (contents: Seq.seq U8.t) (v: Seq.seq U8.t)
: slprop

assume val stream_is_prefix_of_raw
  (base_x: base_t) (pos_x: Ghost.erased pos_t)
  (base_y: base_t) (pos_y: Ghost.erased pos_t)
  (contents: Seq.seq U8.t) (suffix: Seq.seq U8.t)
: slprop

inline_for_extraction
noextract
let bounded (len: len_t) : Tot bool = SZ.gt len 0sz

(* What a [len] asserts about the view it labels. The [fits] conjunct is the
   standing assumption that the whole stream is addressable, without which the
   bound of a truncation could not be computed. *)
let bound_ok (len: len_t) (pos: pos_t) (contents: Seq.seq U8.t) : prop =
  SZ.fits (SZ.v pos + Seq.length contents + 1) /\
  (bounded len ==> SZ.v len == SZ.v pos + Seq.length contents + 1)

let stream_pts_to
  (base: base_t) (len: len_t) (pos: pos_t)
  (contents: Seq.seq U8.t) (v: Seq.seq U8.t)
: slprop
= stream_pts_to_raw base pos contents v ** pure (bound_ok len pos contents)

(* [x] is a truncation of [y]. Beyond the raw witness this records what
   [untruncate] needs in order to rebuild [y]'s bound from [x]'s: a truncated
   view is always bounded, and its bound falls short of its parent's by exactly
   the suffix that was withheld. *)
let stream_is_prefix_of
  (base_x: base_t) (len_x: len_t) (pos_x: pos_t)
  (base_y: base_t) (len_y: len_t) (pos_y: pos_t)
  (contents: Seq.seq U8.t) (suffix: Seq.seq U8.t)
: slprop
= stream_is_prefix_of_raw base_x pos_x base_y pos_y contents suffix **
  pure (
    pos_x == pos_y /\
    bounded len_x /\
    SZ.fits (SZ.v len_x + Seq.length suffix) /\
    (bounded len_y ==> SZ.v len_y == SZ.v len_x + Seq.length suffix)
  )

noextract
inline_for_extraction
let pts_to_inst : I.input_stream_pts_to base_t len_t pos_t = {
  pts_to = stream_pts_to;
  is_prefix_of = stream_is_prefix_of;
}

assume val stream_pts_to_raw_is_suffix_of :
(base: base_t) ->
    (pos: Ghost.erased pos_t) ->
    (contents: Seq.seq U8.t) ->
    (v: Seq.seq U8.t) ->
    stt_ghost unit emp_inames
      (stream_pts_to_raw base pos contents v)
      (fun _ -> stream_pts_to_raw base pos contents v ** pure (v `seq_is_suffix_of` contents))

ghost
fn stream_pts_to_is_suffix_of
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (contents: Seq.seq U8.t)
  (v: Seq.seq U8.t)
requires stream_pts_to base len pos contents v
ensures stream_pts_to base len pos contents v ** pure (v `seq_is_suffix_of` contents)
{
  unfold (stream_pts_to base len pos contents v);
  stream_pts_to_raw_is_suffix_of base pos contents v;
  fold (stream_pts_to base len pos contents v);
}

(* The client's EverParseStreamGetPosition returns the *absolute* position of
   the stream, i.e. the total number of bytes it has consumed since it was
   created. By the meaning of [stream_pts_to_raw base origin contents v]
   ("the stream has consumed [origin] bytes before [contents] started, and
   [v] of [contents] is left"), that is [origin + (|contents| - |v|)].

   It stays truthful under truncation: truncating withholds bytes from the
   view but consumes nothing, so [|contents| - |v|] is unchanged. *)
assume val stream_get_position :
(base: base_t) ->
    (pos: Ghost.erased pos_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt SZ.t
    (requires (
      stream_pts_to_raw base pos contents v
    ))
    (ensures fun res ->
      stream_pts_to_raw base pos contents v **
      pure (
        Seq.length v <= Seq.length contents /\
        SZ.v res == SZ.v pos + Seq.length contents - Seq.length v
      )
    )

inline_for_extraction
noextract
fn stream_get_position_bounded
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to base len pos contents v
returns res: SZ.t
ensures stream_pts_to base len pos contents v **
  pure (
    Seq.length v <= Seq.length contents /\
    SZ.v res == SZ.v pos + Seq.length contents - Seq.length v
  )
{
  unfold (stream_pts_to base len pos contents v);
  let res = stream_get_position base pos contents v;
  fold (stream_pts_to base len pos contents v);
  res
}

(* ... so the position relative to the current validation's origin, which is
   what the `input_stream_inst` interface specifies and what the field-position
   actions report, is obtained by subtracting the origin. *)
inline_for_extraction
noextract
fn stream_get_relative_position
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to base len pos contents v
returns res: SZ.t
ensures stream_pts_to base len pos contents v **
  pure (SZ.v res + Seq.length v == Seq.length contents)
{
  let abs = stream_get_position_bounded base len pos contents v;
  SZ.sub abs pos
}

(* The number of bytes left in a *bounded* view, computed from its bound alone.
   Only ever called under [bounded len], where it is exactly [|v|]. *)
inline_for_extraction
noextract
fn stream_remaining
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to base len pos contents v ** pure (bounded len)
returns res: SZ.t
ensures stream_pts_to base len pos contents v **
  pure (bounded len /\ SZ.v res == Seq.length v)
{
  unfold (stream_pts_to base len pos contents v);
  let abs = stream_get_position base pos contents v;
  fold (stream_pts_to base len pos contents v);
  SZ.sub (SZ.sub len 1sz) abs
}

assume val stream_has :
(base: base_t) ->
    (pos: Ghost.erased pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt bool
    (requires (
      stream_pts_to_raw base pos contents v
    ))
    (ensures (fun res ->
      stream_pts_to_raw base pos contents v **
      pure (res == true <==> SZ.v n <= Seq.length v)
    ))

(* Bounded views must *not* consult the client: it reports what the underlying
   stream still holds, which is more than the truncated view exposes. This is
   the same branch Low* takes on [x.Aux.has_length]. *)
inline_for_extraction
noextract
fn stream_has_bounded
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to base len pos contents v
returns res: bool
ensures stream_pts_to base len pos contents v **
  pure (res == true <==> SZ.v n <= Seq.length v)
{
  if bounded len {
    let rem = stream_remaining base len pos contents v;
    SZ.lte n rem
  } else {
    unfold (stream_pts_to base len pos contents v);
    let res = stream_has base pos n contents v;
    fold (stream_pts_to base len pos contents v);
    res
  }
}

(* [has_at base len pos off n] tests whether [n] bytes are available
     starting [off] bytes after the current position, without consuming
     anything. This is what the "no read" (non-consuming) validators need,
     since they track their position in a separate [SZ.t] reference. *)
assume val stream_has_at :
(base: base_t) ->
    (pos: Ghost.erased pos_t) ->
    (off: SZ.t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt bool
    (requires (
      stream_pts_to_raw base pos contents v ** pure (
      SZ.v off <= Seq.length v
    )))
    (ensures (fun res ->
      stream_pts_to_raw base pos contents v ** pure (
      (res == true <==> SZ.v off + SZ.v n <= Seq.length v) /\
      (res == true ==> SZ.fits (SZ.v off + SZ.v n))
    )))

inline_for_extraction
noextract
fn stream_has_at_bounded
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (off: SZ.t)
  (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to base len pos contents v ** pure (SZ.v off <= Seq.length v)
returns res: bool
ensures stream_pts_to base len pos contents v **
  pure (
    (res == true <==> SZ.v off + SZ.v n <= Seq.length v) /\
    (res == true ==> SZ.fits (SZ.v off + SZ.v n))
  )
{
  if bounded len {
    let rem = stream_remaining base len pos contents v;
    SZ.lte n (SZ.sub rem off)
  } else {
    unfold (stream_pts_to base len pos contents v);
    let res = stream_has_at base pos off n contents v;
    fold (stream_pts_to base len pos contents v);
    res
  }
}

(* The `EverParseRead` primitive: copy the next `n` bytes of the stream into the
   caller-provided scratch buffer `dst` and consume them.

   Unlike Low*, where `EverParseRead` returns a pointer that may alias either
   the client's own storage or `dst`, this always copies. `read` is only ever
   used to parse a leaf integer, so `n` is at most 8 and the copy is free; in
   exchange the C signature carries no aliasing obligation and the separation
   logic postcondition stays a plain points-to. *)
assume val stream_read_bytes :
(base: base_t) ->
    (pos: Ghost.erased pos_t) ->
    (n: SZ.t) ->
    (dst: AP.ptr U8.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    (dv: Ghost.erased (Seq.seq U8.t)) ->
    stt unit
    (requires (
      stream_pts_to_raw base pos contents v ** AP.pts_to dst dv ** pure (
      SZ.v n <= Seq.length v /\
      Seq.length dv == SZ.v n
    )))
    (ensures (fun _ -> exists* v' dv' .
      stream_pts_to_raw base pos contents v' **
      AP.pts_to dst dv' ** pure (
      SZ.v n <= Seq.length v /\
      Seq.equal dv' (Seq.slice v 0 (SZ.v n)) /\
      Seq.equal v' (Seq.slice v (SZ.v n) (Seq.length v))
    )))

(* Consuming primitives need no bounded/unbounded branch: they are only ever
   reached after a successful [has], so the bytes they take are inside the
   view, and consuming them leaves [contents] -- hence the bound -- unchanged. *)
inline_for_extraction
noextract
fn stream_read_bytes_bounded
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (n: SZ.t)
  (dst: AP.ptr U8.t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
  (dv: Ghost.erased (Seq.seq U8.t))
requires
  stream_pts_to base len pos contents v ** AP.pts_to dst dv ** pure (
  SZ.v n <= Seq.length v /\
  Seq.length dv == SZ.v n
)
ensures exists* v' dv' .
  stream_pts_to base len pos contents v' **
  AP.pts_to dst dv' ** pure (
  SZ.v n <= Seq.length v /\
  Seq.equal dv' (Seq.slice v 0 (SZ.v n)) /\
  Seq.equal v' (Seq.slice v (SZ.v n) (Seq.length v))
)
{
  unfold (stream_pts_to base len pos contents v);
  stream_read_bytes base pos n dst contents v dv;
  with v' . assert (stream_pts_to_raw base pos contents v');
  fold (stream_pts_to base len pos contents v');
}

(* `read` cannot itself be assumed: it takes the leaf reader `r` as an argument,
   and an F* function value has no C representation. So the client provides the
   byte-level primitive above and the reader is applied here, on our side of the
   boundary, exactly as the Low* version applies it to the pointer returned by
   `EverParseRead`. Since every caller passes a literal `n` and this is
   `inline_for_extraction`, the scratch buffer extracts to a fixed-size C stack
   array, not a VLA. *)
inline_for_extraction
noextract
fn stream_read
  (t': Type0)
  (k: LP.parser_kind)
  (p: LP.parser k t')
  (r: API.leaf_reader p)
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
  requires (
    stream_pts_to base len pos contents v ** pure (
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\
    k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
    k.LP.parser_kind_low == SZ.v n /\
    Some? (LP.parse p v)
  ))
  returns dst': t'
  ensures (exists* v' .
    stream_pts_to base len pos contents v' ** pure (
    Seq.length v >= SZ.v n /\
    LP.parse p (Seq.slice v 0 (SZ.v n)) == Some (dst', SZ.v n) /\
    LP.parse p v == Some (dst', SZ.v n) /\
    Seq.equal v' (Seq.slice v (SZ.v n) (Seq.length v))
  ))
{
  API.parse_constant_size_eq p v;
  LP.parse_strong_prefix p v (Seq.slice v 0 (SZ.v n));
  let mut scratch = [| 0uy; n |];
  let sp = AP.from_array scratch;
  stream_read_bytes_bounded base len pos n sp contents v _;
  let res = r sp;
  AP.to_array sp scratch;
  res
}

assume val stream_skip :
(base: base_t) ->
    (pos: Ghost.erased pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt unit
    (requires (
      stream_pts_to_raw base pos contents v ** pure (
      Seq.length v >= SZ.v n
    )))
    (ensures (fun _ -> exists* v' .
      stream_pts_to_raw base pos contents v' ** pure (
      Seq.length v >= SZ.v n /\
      v' `Seq.equal` Seq.slice v (SZ.v n) (Seq.length v)
    )))

inline_for_extraction
noextract
fn stream_skip_bounded
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to base len pos contents v ** pure (Seq.length v >= SZ.v n)
ensures exists* v' .
  stream_pts_to base len pos contents v' ** pure (
  Seq.length v >= SZ.v n /\
  v' `Seq.equal` Seq.slice v (SZ.v n) (Seq.length v)
)
{
  unfold (stream_pts_to base len pos contents v);
  stream_skip base pos n contents v;
  with v' . assert (stream_pts_to_raw base pos contents v');
  fold (stream_pts_to base len pos contents v');
}

assume val stream_empty :
(base: base_t) ->
    (pos: Ghost.erased pos_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt SZ.t
    (requires (
      stream_pts_to_raw base pos contents v
    ))
    (ensures (fun res ->
      stream_pts_to_raw base pos contents Seq.empty ** pure (
      SZ.v res == Seq.length v
    )))

(* Bounded: skip exactly what the bound says is left, rather than asking the
   client to drain the stream to *its* end -- which would swallow the bytes
   that follow the truncated region. Low*'s [empty] branches identically. *)
inline_for_extraction
noextract
fn stream_empty_bounded
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to base len pos contents v
returns res: SZ.t
ensures stream_pts_to base len pos contents Seq.empty **
  pure (SZ.v res == Seq.length v)
{
  if bounded len {
    let rem = stream_remaining base len pos contents v;
    stream_skip_bounded base len pos rem contents v;
    with v' . assert (stream_pts_to base len pos contents v');
    rewrite (stream_pts_to base len pos contents v')
       as (stream_pts_to base len pos contents Seq.empty);
    rem
  } else {
    unfold (stream_pts_to base len pos contents v);
    let res = stream_empty base pos contents v;
    fold (stream_pts_to base len pos contents Seq.empty);
    res
  }
}

(* Truncation only rewrites the bound, so [trunc_t = len_t] and the base and
   origin are carried over unchanged. Together with the buffer backend's
   [trunc_t = len_t] this keeps the (base, len, pos) triple from ever being
   built as a C struct; see the comment on [trunc_t] in
   EverParse3d.InputStream.Base. *)
inline_for_extraction
noextract
let stream_trunc_base (b: base_t) (len: len_t) (pos: pos_t) (tr: len_t) : Tot base_t = b

inline_for_extraction
noextract
let stream_trunc_len (b: base_t) (len: len_t) (pos: pos_t) (tr: len_t) : Tot len_t = tr

(* Truncation preserves the origin: the truncated view continues the parent's
   position accounting, so field positions inside a truncated sub-stream stay
   relative to the same enclosing validation. *)
inline_for_extraction
noextract
let stream_trunc_pos (b: base_t) (len: len_t) (pos: pos_t) (tr: len_t) : Tot pos_t = pos

(* The ghost half of truncation: split the client's single, indivisible
   ownership of the stream into the first [n] bytes and the rest. Nothing
   happens at run time -- [stt_ghost] is erased -- and in particular no
   primitive is asked of the client; all that remains at the C level is the
   arithmetic in [stream_truncate] below. *)
assume val stream_split :
(base: base_t) ->
    (pos: Ghost.erased pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt_ghost unit emp_inames
    (requires (
      stream_pts_to_raw base pos contents v ** pure (
      SZ.v n <= Seq.length v
    )))
    (ensures (fun _ -> exists* contents' v1 v2 .
      stream_pts_to_raw base pos contents' v1 **
      stream_is_prefix_of_raw base pos base pos contents v2 **
      pure (
      	SZ.v n <= Seq.length v /\
        Seq.equal v1 (Seq.slice v 0 (SZ.v n)) /\
	Seq.equal v2 (Seq.slice v (SZ.v n) (Seq.length v)) /\
	Seq.length v <= Seq.length contents /\
	Seq.equal contents' (Seq.append (Seq.slice contents 0 (Seq.length contents - Seq.length v)) v1) /\
	Ghost.reveal v == Seq.append v1 v2
    )))

assume val stream_join :
(base_x: base_t) ->
    (pos_x: Ghost.erased pos_t) ->
    (base_y: base_t) ->
    (pos_y: Ghost.erased pos_t) ->
    (contents: Seq.seq U8.t) ->
    (v: Seq.seq U8.t) ->
    (contents0: Seq.seq U8.t) ->
    (suffix: Seq.seq U8.t) ->
    stt_ghost unit emp_inames
    (requires (
       stream_pts_to_raw base_x pos_x contents v **
       stream_is_prefix_of_raw base_x pos_x base_y pos_y contents0 suffix **
       pure (contents0 == Seq.append contents suffix)
    ))
    (ensures (fun _ ->
       stream_pts_to_raw base_y pos_y contents0 (Seq.append v suffix)
    ))

(* The new bound is the absolute position just past the last byte of the
   truncated region, plus the one that keeps [0] meaning "unbounded". It is
   the only thing this computes: a couple of size_t additions, no call. *)
inline_for_extraction
noextract
fn stream_truncate
  (base: base_t)
  (len: len_t)
  (pos: pos_t)
  (n: SZ.t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to base len pos contents v ** pure (SZ.v n <= Seq.length v)
returns res: len_t
ensures exists* contents' v1 v2 .
  stream_pts_to (stream_trunc_base base len pos res) (stream_trunc_len base len pos res) (stream_trunc_pos base len pos res) contents' v1 **
  stream_is_prefix_of (stream_trunc_base base len pos res) (stream_trunc_len base len pos res) (stream_trunc_pos base len pos res) base len pos contents v2 **
  pure (
    SZ.v n <= Seq.length v /\
    Seq.equal v1 (Seq.slice v 0 (SZ.v n)) /\
    Seq.equal v2 (Seq.slice v (SZ.v n) (Seq.length v)) /\
    Seq.length v <= Seq.length contents /\
    Seq.equal contents' (Seq.append (Seq.slice contents 0 (Seq.length contents - Seq.length v)) v1) /\
    Ghost.reveal v == Seq.append v1 v2
  )
{
  unfold (stream_pts_to base len pos contents v);
  let abs = stream_get_position base pos contents v;
  let res = SZ.add (SZ.add abs n) 1sz;
  stream_split base pos n contents v;
  with contents' v1 . assert (stream_pts_to_raw base pos contents' v1);
  with v2 . assert (stream_is_prefix_of_raw base pos base pos contents v2);
  fold (stream_pts_to base res pos contents' v1);
  fold (stream_is_prefix_of base res pos base len pos contents v2);
  res
}

ghost
fn stream_untruncate
  (base_x: base_t)
  (len_x: len_t)
  (pos_x: pos_t)
  (base_y: base_t)
  (len_y: len_t)
  (pos_y: pos_t)
  (contents: Seq.seq U8.t)
  (v: Seq.seq U8.t)
  (contents0: Seq.seq U8.t)
  (suffix: Seq.seq U8.t)
requires
  stream_pts_to base_x len_x pos_x contents v **
  stream_is_prefix_of base_x len_x pos_x base_y len_y pos_y contents0 suffix **
  pure (contents0 == Seq.append contents suffix)
ensures
  stream_pts_to base_y len_y pos_y contents0 (Seq.append v suffix)
{
  unfold (stream_pts_to base_x len_x pos_x contents v);
  unfold (stream_is_prefix_of base_x len_x pos_x base_y len_y pos_y contents0 suffix);
  stream_join base_x pos_x base_y pos_y contents v contents0 suffix;
  Seq.lemma_len_append contents suffix;
  fold (stream_pts_to base_y len_y pos_y contents0 (Seq.append v suffix));
}

noextract
inline_for_extraction
instance input_stream_extern : I.input_stream_inst base_t len_t pos_t = {
  pts_to_inst = pts_to_inst;
  pts_to_is_suffix_of = (fun b l (p: pos_t) c v -> stream_pts_to_is_suffix_of b l p c v);
  get_position = stream_get_relative_position;
  has = (fun b l (p: pos_t) n c v -> stream_has_bounded b l p n c v);
  has_at = (fun b l (p: pos_t) off n c v -> stream_has_at_bounded b l p off n c v);
  read = stream_read;
  skip = (fun b l (p: pos_t) n c v -> stream_skip_bounded b l p n c v);
  empty = (fun b l (p: pos_t) c v -> stream_empty_bounded b l p c v);
  trunc_t = len_t;
  trunc_base = stream_trunc_base;
  trunc_len = stream_trunc_len;
  trunc_pos = stream_trunc_pos;
  truncate = (fun b l (p: pos_t) n c v -> stream_truncate b l p n c v);
  untruncate = (fun bx lx (px: pos_t) b2 l2 (p2: pos_t) c v c0 sfx -> stream_untruncate bx lx px b2 l2 p2 c v c0 sfx);
}

(* The error handler used when 3d is invoked with `--use_error_handler_macro`.
   Each backend provides its own; the 3D frontend passes the one matching the
   selected `--input_stream` to `validate_with_error_handler`. *)
[@@CMacro]
assume val error_handler_macro : Common.error_handler #base_t #len_t #pos_t

(* No `copy_buffer` instance: probing is unavailable for the `extern` backend,
   as in Low*. *)

(* `field_ptr_after`: the address just past the next `sz` bytes of the input
   stream, obtained from the client-provided `EverParseStreamPeep` primitive.
   Only the `extern` backend provides it, as in Low*. *)

module AP = Pulse.Lib.ArrayPtr
module R = Pulse.Lib.Reference
module AB = EverParse3d.Actions.Base
open EverParse3d.State

noextract
inline_for_extraction
let ___PUINT8 = AP.ptr U8.t

(* As for the stream primitives, the origin and the truncation bound are absent
   from the assumed C prototype: EverParseStreamPeep is unchanged. *)
assume val field_ptr_after_impl
  (sz: FStar.UInt64.t)
  (w: R.ref ___PUINT8)
  (sl_base: base_t)
  (sl_pos: Ghost.erased pos_t)
  (w0: Ghost.erased ___PUINT8)
  (contents_sl: Ghost.erased (Seq.seq U8.t))
  (v_sl: Ghost.erased (Seq.seq U8.t))
: stt bool
    (R.pts_to w #1.0R w0 ** stream_pts_to_raw sl_base sl_pos contents_sl v_sl)
    (fun _ -> exists* w' . R.pts_to w #1.0R w' ** stream_pts_to_raw sl_base sl_pos contents_sl v_sl)

inline_for_extraction
noextract
fn field_ptr_after_unchecked
  (sz: FStar.UInt64.t)
  (w: R.ref ___PUINT8)
  (sl_base: base_t)
  (sl_len: len_t)
  (sl_pos: pos_t)
  (w0: Ghost.erased ___PUINT8)
  (contents_sl: Ghost.erased (Seq.seq U8.t))
  (v_sl: Ghost.erased (Seq.seq U8.t))
requires R.pts_to w #1.0R w0 ** I.pts_to sl_base sl_len sl_pos contents_sl v_sl
returns res: bool
ensures exists* w' . R.pts_to w #1.0R w' ** I.pts_to sl_base sl_len sl_pos contents_sl v_sl
{
  rewrite (I.pts_to sl_base sl_len sl_pos contents_sl v_sl)
       as (stream_pts_to sl_base sl_len sl_pos contents_sl v_sl);
  unfold (stream_pts_to sl_base sl_len sl_pos contents_sl v_sl);
  let res = field_ptr_after_impl sz w sl_base sl_pos w0 contents_sl v_sl;
  fold (stream_pts_to sl_base sl_len sl_pos contents_sl v_sl);
  rewrite (stream_pts_to sl_base sl_len sl_pos contents_sl v_sl)
       as (I.pts_to sl_base sl_len sl_pos contents_sl v_sl);
  res
}

(* The client's Peep answers for the whole stream, so inside a truncated view
   it must be preceded by our own bounds check -- as in Low*, where [peep]
   calls the [has_length]-aware [has] before [peep0]. *)
inline_for_extraction
noextract
fn field_ptr_after_wrapped
  (sz: FStar.UInt64.t)
  (w: R.ref ___PUINT8)
  (sl_base: base_t)
  (sl_len: len_t)
  (sl_pos: pos_t)
  (w0: Ghost.erased ___PUINT8)
  (contents_sl: Ghost.erased (Seq.seq U8.t))
  (v_sl: Ghost.erased (Seq.seq U8.t))
requires R.pts_to w #1.0R w0 ** I.pts_to sl_base sl_len sl_pos contents_sl v_sl
returns res: bool
ensures exists* w' . R.pts_to w #1.0R w' ** I.pts_to sl_base sl_len sl_pos contents_sl v_sl
{
  if bounded sl_len {
    rewrite (I.pts_to sl_base sl_len sl_pos contents_sl v_sl)
         as (stream_pts_to sl_base sl_len sl_pos contents_sl v_sl);
    let rem = stream_remaining sl_base sl_len sl_pos contents_sl v_sl;
    rewrite (stream_pts_to sl_base sl_len sl_pos contents_sl v_sl)
         as (I.pts_to sl_base sl_len sl_pos contents_sl v_sl);
    if FStar.UInt64.lte sz (SZ.sizet_to_uint64 rem) {
      field_ptr_after_unchecked sz w sl_base sl_len sl_pos w0 contents_sl v_sl
    } else {
      false
    }
  } else {
    field_ptr_after_unchecked sz w sl_base sl_len sl_pos w0 contents_sl v_sl
  }
}

noextract
inline_for_extraction
let field_ptr_after_fn
: AB.field_ptr_after_t base_t len_t pos_t #input_stream_extern ___PUINT8
= fun sz w sl_base sl_len (sl_pos: pos_t) w0 contents_sl v_sl ->
    field_ptr_after_wrapped sz w sl_base sl_len sl_pos w0 contents_sl v_sl

[@@EverParse3d.Actions.Common.specialize_backend]
noextract
inline_for_extraction
let field_ptr_after
: option (AB.field_ptr_after_t base_t len_t pos_t #input_stream_extern ___PUINT8)
= Some field_ptr_after_fn

assume val null_ptr : ___PUINT8

(* An opaque alias for the state-dictionary invariant. It is a plain (hence
   delta-reducible) definition, so that it is convertible with the `exists*`
   that `field_ptr_after_setter_t` expects, while being opaque enough that
   Pulse does not lift the existential into an implicit binder of the `fn`
   below. *)
let all_states (d: state_dict) : slprop =
  exists* (extra: forevery_values d) . forevery_state d extra

(* `noextract` as well as `inline_for_extraction`: its only caller,
   `field_ptr_after_with_setter` below, is itself noextract and inlined into
   the generated validators. Without `noextract` KaRaMeL must materialise a
   real definition for it -- which, now that this module is public (an API of
   the EverParse bundle), would resurrect EverParse.c just for this one
   function. *)
noextract
inline_for_extraction
fn field_ptr_after_with_setter_impl
  (#extra_state: state_dict)
  (sz: FStar.UInt64.t)
  (write_to: (___PUINT8 -> AB.external_action extra_state unit))
  (sl_base: base_t)
  (sl_len: len_t)
  (sl_pos: pos_t)
  (contents_sl: Ghost.erased (Seq.seq U8.t))
  (v_sl: Ghost.erased (Seq.seq U8.t))
requires
  I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
  all_states extra_state
returns res: bool
ensures
  I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
  all_states extra_state
{
  let mut w = null_ptr;
  let ok = field_ptr_after_wrapped sz w sl_base sl_len sl_pos _ contents_sl v_sl;
  if ok {
    let q = !w;
    unfold (all_states extra_state);
    write_to q ();
    fold (all_states extra_state);
    true
  } else {
    false
  }
}

[@@EverParse3d.Actions.Common.specialize_backend]
noextract
inline_for_extraction
let field_ptr_after_with_setter (extra_state: state_dict)
: option (AB.field_ptr_after_setter_t base_t len_t pos_t #input_stream_extern extra_state ___PUINT8)
= Some (field_ptr_after_with_setter_impl #extra_state)

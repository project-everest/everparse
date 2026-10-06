module EverParse3d.InputStream.LowstarExtern
open Pulse.Lib.Pervasives
#lang-pulse

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module AP = Pulse.Lib.ArrayPtr
module I = EverParse3d.InputStream.Base
module LP = LowParse.Spec.Base
module API = LowParse.Pulse.ArrayPtr.Int
module Util = EverParse3d.Util
module Raw = EverParse3d.InputStream.LowstarExtern.Raw
module EH = EverParse3d.Actions.ErrorHandler.LowstarExtern
include EverParse3d.InputStream.LowstarExtern.Types

ghost
fn stream_pts_to_is_suffix_of
  (b: base_t) (len: len_t) (pos: pos_t) (c v: Seq.seq U8.t)
requires stream_pts_to b len pos c v
ensures stream_pts_to b len pos c v ** pure (I.seq_is_suffix_of v c)
{
  unfold (stream_pts_to b len pos c v);
  with current. _;
  unfold (public_pts_to b current c v);
  fold (public_pts_to b current c v);
  fold (stream_pts_to b len pos c v);
}

inline_for_extraction noextract
fn stream_get_position
  (b: base_t) (len: len_t) (pos: pos_t)
  (c v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos c v
returns res: U64.t
ensures stream_pts_to b len pos c v **
  pure (U64.v res + Seq.length v == Seq.length c)
{
  unfold (stream_pts_to b len pos c v);
  with current. _;
  unfold (public_pts_to b current c v);
  let res = !pos;
  fold (public_pts_to b current c v);
  fold (stream_pts_to b len pos c v);
  res
}

// Full-width internal has is shared with Peep's U64 bounds check.
inline_for_extraction noextract
fn stream_has_u64
  (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: base_t) (len: len_t) (pos: pos_t) (n: U64.t)
  (c v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos c v
returns res: bool
ensures stream_pts_to b len pos c v **
  pure (res == true <==> U64.v n <= Seq.length v)
{
  unfold (stream_pts_to b len pos c v);
  with current. _;
  unfold (public_pts_to b current c v);
  let res = if b.has_length {
    let cur = !pos;
    U64.lte n (U64.sub b.length cur)
  } else {
    Raw.has b.base n
  };
  fold (public_pts_to b current c v);
  fold (stream_pts_to b len pos c v);
  res
}

inline_for_extraction noextract
fn stream_has
  (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: base_t) (len: len_t) (pos: pos_t) (n: SZ.t)
  (c v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos c v
returns res: bool
ensures stream_pts_to b len pos c v **
  pure (res == true <==> SZ.v n <= Seq.length v)
{
  let count = I.native_scan_to_u64 n;
  stream_has_u64 b len pos count c v
}

inline_for_extraction noextract
fn stream_has_at
  (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: base_t) (len: len_t) (pos: pos_t) (off: U64.t) (n: SZ.t)
  (c v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos c v
returns res: bool
ensures stream_pts_to b len pos c v ** pure (
  U64.v off <= Seq.length v ==>
    ((res == true <==> U64.v off + SZ.v n <= Seq.length v) /\
     (res == true ==> U64.fits (U64.v off + SZ.v n))))
{
  let count = I.native_scan_to_u64 n;
  // Check overflow even for out-of-range speculative offsets. No wrapping
  // arithmetic or truncated SizeT count is passed to EverParseHas.
  if U64.lte off (U64.sub 18446744073709551615UL count) {
    stream_has_u64 b len pos (U64.add off count) c v
  } else {
    stream_pts_to_is_suffix_of b len pos c v;
    unfold (stream_pts_to b len pos c v);
    with current. _;
    unfold (public_pts_to b current c v);
    fold (public_pts_to b current c v);
    fold (stream_pts_to b len pos c v);
    false
  }
}

inline_for_extraction noextract
fn stream_skip
  (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: base_t) (len: len_t) (pos: pos_t) (n: U64.t)
  (c v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos c v ** pure (U64.v n <= Seq.length v)
ensures exists* v'.
  stream_pts_to b len pos c v' **
  pure (Seq.length v >= U64.v n /\
    Seq.equal v' (Seq.slice v (U64.v n) (Seq.length v)))
{
  unfold (stream_pts_to b len pos c v);
  with current. _;
  unfold (public_pts_to b current c v);
  let cur = !pos;
  Raw.skip b.base n;
  let next = U64.add cur n;
  pos := next;
  let rest = Ghost.hide (Seq.slice v (U64.v n) (Seq.length v));
  rewrite (storage b.base (U64.v current + U64.v n))
    as (storage b.base (U64.v next));
  fold (public_pts_to b next c rest);
  fold (stream_pts_to b len pos c rest);
}

inline_for_extraction noextract
fn stream_empty
  (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: base_t) (len: len_t) (pos: pos_t)
  (c v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos c v
ensures stream_pts_to b len pos c Seq.empty
{
  // Both branches update the count once. In particular, an unbounded drain
  // never calls Skip, even if EverParseEmpty returns more than SIZE_MAX.
  if b.has_length {
    let cur = stream_get_position b len pos c v;
    unfold (stream_pts_to b len pos c v);
    with current. _;
    unfold (public_pts_to b current c v);
    fold (public_pts_to b current c v);
    fold (stream_pts_to b len pos c v);
    stream_skip b len pos (U64.sub b.length cur) c v;
    with rest. _;
    rewrite (stream_pts_to b len pos c rest)
      as (stream_pts_to b len pos c Seq.empty);
  } else {
    unfold (stream_pts_to b len pos c v);
    with current. _;
    unfold (public_pts_to b current c v);
    let cur = !pos;
    let count = Raw.empty b.base;
    let next = U64.add cur count;
    pos := next;
    rewrite (storage b.base (Seq.length (get_all b.base)))
      as (storage b.base (U64.v next));
    fold (public_pts_to b next c Seq.empty);
    fold (stream_pts_to b len pos c Seq.empty);
  }
}

inline_for_extraction noextract
fn stream_read
  (#[Util.solve_from_ctx ()] extra: extra_t)
  (t': Type0) (k: LP.parser_kind) (p: LP.parser k t')
  (reader: API.leaf_reader p)
  (b: base_t) (len: len_t) (pos: pos_t) (n: SZ.t)
  (c v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos c v ** pure (
  k.LP.parser_kind_subkind == Some LP.ParserStrong /\
  k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
  k.LP.parser_kind_low == SZ.v n /\ Some? (LP.parse p v))
returns res: t'
ensures exists* v'.
  stream_pts_to b len pos c v' ** pure (
    Seq.length v >= SZ.v n /\
    LP.parse p (Seq.slice v 0 (SZ.v n)) == Some (res, SZ.v n) /\
    LP.parse p v == Some (res, SZ.v n) /\
    Seq.equal v' (Seq.slice v (SZ.v n) (Seq.length v)))
{
  API.parse_constant_size_eq p v;
  LP.parse_strong_prefix p v (Seq.slice v 0 (SZ.v n));
  unfold (stream_pts_to b len pos c v);
  with current. _;
  unfold (public_pts_to b current c v);
  let cur = !pos;
  let count = I.native_scan_to_u64 n;
  let mut scratch = [| 0uy; n |];
  let dst = AP.from_array scratch;
  let bytes = Raw.read b.base count dst;
  let res = reader bytes;
  Raw.restore_read b.base count (U64.v cur) dst bytes;
  AP.to_array dst scratch;
  let next = U64.add cur count;
  pos := next;
  let rest = Ghost.hide (Seq.slice v (SZ.v n) (Seq.length v));
  rewrite (storage b.base (U64.v cur + U64.v count))
    as (storage b.base (U64.v next));
  fold (public_pts_to b next c rest);
  fold (stream_pts_to b len pos c rest);
  res
}

inline_for_extraction noextract
let stream_trunc_base (_: base_t) (_: len_t) (_: pos_t) (tr: base_t) = tr
inline_for_extraction noextract
let stream_trunc_len (_: base_t) (_: len_t) (_: pos_t) (_: base_t) = ()
inline_for_extraction noextract
let stream_trunc_pos (_: base_t) (_: len_t) (pos: pos_t) (_: base_t) = pos

inline_for_extraction noextract
fn stream_truncate
  (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: base_t) (len: len_t) (pos: pos_t) (n: SZ.t)
  (c v: Ghost.erased (Seq.seq U8.t))
requires stream_pts_to b len pos c v ** pure (SZ.v n <= Seq.length v)
returns res: base_t
ensures exists* c' v1 v2.
  stream_pts_to res () pos c' v1 **
  stream_is_prefix_of res () pos b len pos c v2 **
  pure (SZ.v n <= Seq.length v /\
    Seq.equal v1 (Seq.slice v 0 (SZ.v n)) /\
    Seq.equal v2 (Seq.slice v (SZ.v n) (Seq.length v)) /\
    Seq.length v <= Seq.length c /\
    Seq.equal c' (Seq.append (Seq.slice c 0 (Seq.length c - Seq.length v)) v1) /\
    Ghost.reveal v == Seq.append v1 v2)
{
  unfold (stream_pts_to b len pos c v);
  with current. _;
  unfold (public_pts_to b current c v);
  let cur = !pos;
  let count = I.native_scan_to_u64 n;
  let limit = U64.add cur count;
  let res = { base = b.base; has_length = true; length = limit };
  let c' = Ghost.hide (Seq.slice c 0 (U64.v limit));
  let v1 = Ghost.hide (Seq.slice v 0 (SZ.v n));
  let v2 = Ghost.hide (Seq.slice v (SZ.v n) (Seq.length v));
  Seq.lemma_split v (SZ.v n);
  rewrite (storage b.base (U64.v current))
    as (storage res.base (U64.v cur));
  fold (public_pts_to res cur c' v1);
  fold (stream_pts_to res () pos c' v1);
  fold (stream_is_prefix_of res () pos b len pos c v2);
  res
}

ghost
fn stream_untruncate
  (bx: base_t) (lx: len_t) (px: pos_t)
  (parent: base_t) (ly: len_t) (py: pos_t)
  (c v c0 suffix: Seq.seq U8.t)
requires stream_pts_to bx lx px c v **
  stream_is_prefix_of bx lx px parent ly py c0 suffix **
  pure (c0 == Seq.append c suffix)
ensures stream_pts_to parent ly py c0 (Seq.append v suffix)
{
  unfold (stream_pts_to bx lx px c v);
  with current. _;
  unfold (public_pts_to bx current c v);
  unfold (stream_is_prefix_of bx lx px parent ly py c0 suffix);
  rewrite (storage bx.base (U64.v current))
    as (storage parent.base (U64.v current));
  rewrite (R.pts_to px current) as (R.pts_to py current);
  fold (public_pts_to parent current c0 (Seq.append v suffix));
  fold (stream_pts_to parent ly py c0 (Seq.append v suffix));
}

inline_for_extraction noextract
let scan_add (x: U64.t) (n: SZ.t)
  : Pure U64.t
    (requires U64.fits (U64.v x + SZ.v n))
    (ensures fun y -> U64.v y == U64.v x + SZ.v n)
  = U64.add x (I.native_scan_to_u64 n)

noextract inline_for_extraction
instance input_stream_extern : I.input_stream_inst base_t len_t pos_t = {
  pts_to_inst = pts_to_inst;
  error_handler_t = EH.error_handler;
  error_handler_arrow_of_t = EH.error_handler_arrow_of;
  extra_t = extra_t;
  scan_t = U64.t;
  scan_v = U64.v;
  scan_fits = U64.fits;
  scan_zero = 0UL;
  scan_add = scan_add;
  scan_to_u64 = (fun x -> x);
  pts_to_is_suffix_of = stream_pts_to_is_suffix_of;
  get_position = stream_get_position;
  has = stream_has;
  has_at = stream_has_at;
  read = stream_read;
  skip = stream_skip;
  empty = stream_empty;
  trunc_t = base_t;
  trunc_base = stream_trunc_base;
  trunc_len = stream_trunc_len;
  trunc_pos = stream_trunc_pos;
  truncate = stream_truncate;
  untruncate = stream_untruncate;
}

// Static mode changes only the linkage of Raw's legacy C primitives.
noextract inline_for_extraction
let input_stream_static = input_stream_extern

[@@CMacro]
assume val error_handler_macro : EH.error_handler

module AB = EverParse3d.Actions.Base
open EverParse3d.State

// The FFI result is nullable AP.ptr. Keep the ordinary action/destination
// type (the destination may initially contain NULL), but pass a pointer to
// an action only after converting it to the checked non-null refinement.
noextract inline_for_extraction
let ___PUINT8 = AP.ptr U8.t
noextract inline_for_extraction
let non_null_ptr = p:___PUINT8 { not (AP.g_is_null p) }

inline_for_extraction noextract
fn field_ptr_after_wrapped
  (#[Util.solve_from_ctx ()] extra: extra_t)
  (sz: U64.t) (w: R.ref ___PUINT8)
  (b: base_t) (len: len_t) (pos: pos_t)
  (w0: Ghost.erased ___PUINT8)
  (c v: Ghost.erased (Seq.seq U8.t))
requires R.pts_to w w0 ** I.pts_to b len pos c v
returns res: bool
ensures exists* w'. R.pts_to w w' ** I.pts_to b len pos c v **
  pure ((res == false ==> w' == w0) /\
        (res == true ==> not (AP.g_is_null w')))
{
  rewrite (I.pts_to b len pos c v) as (stream_pts_to b len pos c v);
  let available = stream_has_u64 b len pos sz c v;
  if available {
    unfold (stream_pts_to b len pos c v);
    with current. _;
    unfold (public_pts_to b current c v);
    let ptr = Raw.peep b.base sz;
    let is_null = AP.is_null ptr;
    Raw.restore_peep b.base sz (U64.v current) ptr;
    fold (public_pts_to b current c v);
    fold (stream_pts_to b len pos c v);
    rewrite (stream_pts_to b len pos c v) as (I.pts_to b len pos c v);
    if is_null {
      false
    } else {
      let checked: non_null_ptr = ptr;
      w := checked;
      true
    }
  } else {
    rewrite (stream_pts_to b len pos c v) as (I.pts_to b len pos c v);
    false
  }
}

noextract inline_for_extraction
fn field_ptr_after_fn
  (extra: extra_t) (sz: U64.t) (w: R.ref ___PUINT8)
  (b: base_t) (len: len_t) (pos: pos_t)
  (w0: Ghost.erased ___PUINT8)
  (c v: Ghost.erased (Seq.seq U8.t))
requires R.pts_to w w0 ** I.pts_to b len pos c v
returns res: bool
ensures exists* w'. R.pts_to w w' ** I.pts_to b len pos c v
{
  field_ptr_after_wrapped #extra sz w b len pos w0 c v
}

[@@EverParse3d.Actions.Common.specialize_backend]
noextract inline_for_extraction
let field_ptr_after
  : option (AB.field_ptr_after_t base_t len_t pos_t #input_stream_extern ___PUINT8)
  = Some field_ptr_after_fn

let all_states (d: state_dict) : slprop =
  exists* (extra: forevery_values d). forevery_state d extra

inline_for_extraction noextract
fn field_ptr_after_with_setter_impl
  (#d: state_dict) (extra: extra_t) (sz: U64.t)
  (write_to: ___PUINT8 -> AB.external_action d unit)
  (b: base_t) (len: len_t) (pos: pos_t)
  (c v: Ghost.erased (Seq.seq U8.t))
requires I.pts_to b len pos c v ** all_states d
returns res: bool
ensures I.pts_to b len pos c v ** all_states d
{
  rewrite (I.pts_to b len pos c v) as (stream_pts_to b len pos c v);
  let available = stream_has_u64 b len pos sz c v;
  if available {
    unfold (stream_pts_to b len pos c v);
    with current. _;
    unfold (public_pts_to b current c v);
    let ptr = Raw.peep b.base sz;
    let is_null = AP.is_null ptr;
    Raw.restore_peep b.base sz (U64.v current) ptr;
    // Restore the client resource before calling arbitrary application code.
    fold (public_pts_to b current c v);
    fold (stream_pts_to b len pos c v);
    rewrite (stream_pts_to b len pos c v) as (I.pts_to b len pos c v);
    if is_null {
      false
    } else {
      unfold (all_states d);
      let checked: non_null_ptr = ptr;
      write_to checked ();
      fold (all_states d);
      true
    }
  } else {
    rewrite (stream_pts_to b len pos c v) as (I.pts_to b len pos c v);
    false
  }
}

[@@EverParse3d.Actions.Common.specialize_backend]
noextract inline_for_extraction
let field_ptr_after_with_setter (d: state_dict)
  : option (AB.field_ptr_after_setter_t base_t len_t pos_t
      #input_stream_extern d ___PUINT8)
  = Some (field_ptr_after_with_setter_impl #d)

module CBE = EverParse3d.CopyBuffer.LowstarExtern
module CB = EverParse3d.CopyBuffer

inline_for_extraction noextract
let copy_buffer_t = CBE.copy_buffer_t

// Keep physical storage at its actual consumed position. There is no local
// reference here and no operation pretending that a consumed stream rewinds.
inline_for_extraction noextract
let copy_buffer_storage (c: copy_buffer_t) (contents v: Seq.seq U8.t) =
  exists* position. public_pts_to (CBE.stream_of c) position contents v

inline_for_extraction noextract
fn copy_buffer_with_view
  (a: Type0) (c: copy_buffer_t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (pre: slprop) (post: a -> Seq.seq U8.t -> Tot slprop)
  (body: (base:base_t -> len:len_t -> pos:pos_t ->
    stt a
      (I.pts_to base len pos contents contents ** pre)
      (fun result -> exists* v.
        I.pts_to base len pos contents v ** post result v)))
requires copy_buffer_storage c contents contents ** pre
returns result: a
ensures exists* v. copy_buffer_storage c contents v ** post result v
{
  unfold (copy_buffer_storage c contents contents);
  with initial. _;
  unfold (public_pts_to (CBE.stream_of c) initial contents contents);
  let b = CBE.stream_of c;
  let mut cursor = 0UL;
  rewrite (storage (CBE.stream_of c).base (U64.v initial))
    as (storage b.base (U64.v 0UL));
  fold (public_pts_to b 0UL contents contents);
  fold (stream_pts_to b () cursor contents contents);
  rewrite (stream_pts_to b () cursor contents contents)
    as (I.pts_to b () cursor contents contents);
  let result = body b () cursor;
  with v. assert (I.pts_to b () cursor contents v);
  rewrite (I.pts_to b () cursor contents v)
    as (stream_pts_to b () cursor contents v);
  unfold (stream_pts_to b () cursor contents v);
  with final. _;
  rewrite (public_pts_to b final contents v)
    as (public_pts_to (CBE.stream_of c) final contents v);
  fold (copy_buffer_storage c contents v);
  result
}

inline_for_extraction noextract
let copy_buffer_report_error_t =
  typename:string -> fieldname:string -> reason:string ->
  ctxt:EverParse3d.AppCtxt.app_ctxt -> c:copy_buffer_t ->
  contents:Ghost.erased (Seq.seq U8.t) -> v:Ghost.erased (Seq.seq U8.t) ->
  stt unit
    (exists* vc. R.pts_to ctxt vc ** copy_buffer_storage c contents v)
    (fun _ -> exists* vc'. R.pts_to ctxt vc' ** copy_buffer_storage c contents v)

inline_for_extraction noextract
fn copy_buffer_report_error (handler: EH.error_handler)
  : copy_buffer_report_error_t
  = (typename: _) (fieldname: _) (reason: _)
    (ctxt: _) (c: _) (contents: _) (v: _)
{
  // Probe diagnostics intentionally use kind zero and retain their supplied
  // reason. The callback sees the legacy record, never the scoped cursor.
  handler typename fieldname reason 0UL ctxt (CBE.stream_of c) 0UL
}

noextract inline_for_extraction
instance copy_buffer_extern : CB.copy_buffer copy_buffer_t base_t len_t pos_t = {
  storage = copy_buffer_storage;
  report_failed_array_element = true;
  with_view = copy_buffer_with_view;
  report_error = copy_buffer_report_error;
}

// Temporary frontend compatibility name; it denotes exactly the same dict.
noextract inline_for_extraction
let copy_buffer_buffer = copy_buffer_extern

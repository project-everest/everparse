module EverParse3d.InputStream.LowstarBuffer
open Pulse.Lib.Pervasives
#lang-pulse

module B = EverParse3d.InputStream.Buffer
module I = EverParse3d.InputStream.Base
module EH = EverParse3d.Actions.ErrorHandler.LowstarBuffer
module CBB = EverParse3d.CopyBuffer.LowstarBuffer
module CB = EverParse3d.CopyBuffer
module AP = Pulse.Lib.ArrayPtr
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64

include EverParse3d.InputStream.Buffer.Types

noextract inline_for_extraction
instance input_stream_buffer : I.input_stream_inst base_t len_t pos_t = {
  B.input_stream_buffer with
  error_handler_t = EH.error_handler;
  error_handler_arrow_of_t = EH.error_handler_arrow_of;
}

[@@CMacro]
assume val error_handler_macro : EH.error_handler

inline_for_extraction noextract
let copy_buffer_t = CBB.copy_buffer_t

inline_for_extraction noextract
let copy_buffer_storage (c: copy_buffer_t) (contents v: Seq.seq U8.t) =
  AP.pts_to (CBB.stream_of c) contents **
  pure (Seq.length contents == U64.v (CBB.stream_len c) /\
        Seq.length contents < 4294967296 /\
        SZ.fits (Seq.length contents) /\
        I.seq_is_suffix_of v contents)

inline_for_extraction noextract
fn copy_buffer_with_view
  (a: Type0) (c: copy_buffer_t)
  (contents: Ghost.erased (Seq.seq U8.t))
  (pre: slprop) (post: (a -> Seq.seq U8.t -> Tot slprop))
  (body: (base:base_t -> len:len_t -> pos:pos_t ->
    stt a
      (I.pts_to base len pos contents contents ** pre)
      (fun result -> exists* v. I.pts_to base len pos contents v ** post result v)))
requires copy_buffer_storage c contents contents ** pre
returns result: a
ensures exists* v. copy_buffer_storage c contents v ** post result v
{
  unfold (copy_buffer_storage c contents contents);
  let base = CBB.stream_of c;
  let len = SZ.uint64_to_sizet (CBB.stream_len c);
  let mut cursor = 0sz;
  rewrite (AP.pts_to (CBB.stream_of c) contents) as (AP.pts_to base contents);
  Seq.lemma_eq_elim (Seq.slice contents 0 (Seq.length contents)) contents;
  fold (stream_pts_to base len cursor contents contents);
  rewrite (stream_pts_to base len cursor contents contents)
    as (I.pts_to base len cursor contents contents);
  let result = body base len cursor;
  with v. assert (I.pts_to base len cursor contents v);
  rewrite (I.pts_to base len cursor contents v)
    as (stream_pts_to base len cursor contents v);
  B.stream_pts_to_is_suffix_of base len cursor contents v;
  unfold (stream_pts_to base len cursor contents v);
  rewrite (AP.pts_to base contents) as (AP.pts_to (CBB.stream_of c) contents);
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
fn copy_buffer_report_error (handler: EH.error_handler) : copy_buffer_report_error_t
  = (typename: _) (fieldname: _) (reason: _)
    (ctxt: _) (c: _) (contents: _) (v: _)
{
  handler typename fieldname reason 0UL ctxt (CBB.stream_of c) 0UL
}

noextract inline_for_extraction
instance copy_buffer_buffer : CB.copy_buffer copy_buffer_t base_t len_t pos_t = {
  storage = copy_buffer_storage;
  report_failed_array_element = true;
  with_view = copy_buffer_with_view;
  report_error = copy_buffer_report_error;
}

[@@EverParse3d.Actions.Common.specialize_backend]
noextract inline_for_extraction
let field_ptr
  : option (EverParse3d.Actions.Base.field_ptr_t base_t len_t pos_t #input_stream_buffer (AP.ptr U8.t))
  = Some B.field_ptr_impl

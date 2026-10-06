module EverParse3d.CopyBuffer
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Pulse.Lib.Pervasives

(* Storage belongs to the opaque handle, independently of the cursor used by
   a validator. A scoped view lends a fresh stream over unread storage and
   restores ownership at the resulting suffix. Native instances may reuse a
   client cursor; Low* ABI instances keep their cursor local, requiring no
   additional client projection. Error reporting is instance-specific too.

   A probe may replace the storage predicate with ownership of a different
   region. As with Low*'s assumed probe contracts, clients must ensure that
   the returned storage stays live and disjoint from the validator's other
   state throughout the scoped view. *)
noextract
inline_for_extraction
class copy_buffer (copy_buffer_t: Type0) (base_t: Type0) (len_t: Type0) (pos_t: Type0) {| inst: I.input_stream_inst base_t len_t pos_t |} = {
  storage : copy_buffer_t -> Seq.seq U8.t -> Seq.seq U8.t -> Tot slprop;

  (* Low* reports the enclosing array frame even when its element reported
     an error already; the native Pulse API historically omits that frame. *)
  report_failed_array_element : bool;

  with_view :
    (a: Type0) ->
    (c: copy_buffer_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (pre: slprop) ->
    (post: (a -> Seq.seq U8.t -> Tot slprop)) ->
    (body: (base:base_t -> len:len_t -> pos:pos_t ->
      stt a
        (I.pts_to base len pos contents contents ** pre)
        (fun result -> exists* v.
          I.pts_to base len pos contents v ** post result v))) ->
    stt a
      (storage c contents contents ** pre)
      (fun result -> exists* v. storage c contents v ** post result v);

  report_error :
    (handler: inst.error_handler_t) ->
    (typename: string) ->
    (fieldname: string) ->
    (reason: string) ->
    (ctxt: AppCtxt.app_ctxt) ->
    (c: copy_buffer_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt unit
      (exists* vc. Pulse.Lib.Reference.pts_to ctxt vc ** storage c contents v)
      (fun _ -> exists* vc'. Pulse.Lib.Reference.pts_to ctxt vc' ** storage c contents v);
}

let pts_to
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| I.input_stream_inst base_t len_t pos_t |}
  {| cb: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (c: copy_buffer_t) (contents: Seq.seq U8.t) (v: Seq.seq U8.t) : Tot slprop =
  cb.storage c contents v

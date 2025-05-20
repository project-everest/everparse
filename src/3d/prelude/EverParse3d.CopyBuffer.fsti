module EverParse3d.CopyBuffer
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.All
module B = LowStar.Buffer
module HS = FStar.HyperStack
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open LowStar.Buffer
open FStar.HyperStack.ST
val region : HS.rid

val copy_buffer_t : Type0

val stream_of : copy_buffer_t -> I.t
val stream_len (c:copy_buffer_t) : I.tlen (stream_of c)

type maybe a =
  | Nothing
  | Just of a

let loc_of (x:copy_buffer_t) : GTot B.loc =
  I.footprint (stream_of x)

let inv (x:copy_buffer_t) (h:HS.mem) = I.live (stream_of x) h

let liveness_preserved (x:copy_buffer_t) =
  let sl = stream_of x in
  forall l h0 h1. {:pattern (modifies l h0 h1)}
    (I.live sl h0 /\
     B.modifies l h0 h1 /\
     address_liveness_insensitive_locs `loc_includes` l) ==>
    I.live sl h1

val properties (x:copy_buffer_t)
  : Lemma (
      //copy buffer is disjoint from fresh stack frame
      (forall h0 h1.
        I.live (stream_of x) h0 /\
        HS.fresh_frame h0 h1 /\
        B.loc_disjoint (loc_of x) (B.loc_region_only true (HS.get_tip h1))) /\
      //popping the top-most frame does not change the liveness or permissions of the copy buffer
      (forall h0 h1.
        HS.popped h0 h1 /\
        I.live (stream_of x) h0 ==>
        I.live (stream_of x) h1 /\
        I.get_read (stream_of x) h1 == I.get_read (stream_of x) h0) /\
      // modifying a liveness insensitive location does not change the liveness of the copy buffer
      liveness_preserved x /\
      // copy buffers live in the distinct `region` constant
      B.loc_region_only true region `loc_includes` loc_of x /\
      // and that region is disjoint from the AppCtxt region
      region `HS.disjoint` AppCtxt.region
    )
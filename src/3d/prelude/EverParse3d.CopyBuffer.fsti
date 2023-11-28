module EverParse3d.CopyBuffer
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.All
module B = LowStar.Buffer
module HS = FStar.HyperStack
module U64 = FStar.UInt64
open LowStar.Buffer
open FStar.HyperStack.ST
val region : HS.rid

val t : Type0

val as_input_stream : t -> (sl:I.t & I.tlen sl)

let stream_of (x:t) = dfst (as_input_stream x)

let loc_of (x:t) : GTot B.loc =
  I.footprint (stream_of x)

let liveness_preserved (x:t) =
  let sl = stream_of x in
  forall l h0 h1. {:pattern (modifies l h0 h1)}
    (I.live sl h0 /\
     B.modifies l h0 h1 /\
     address_liveness_insensitive_locs `loc_includes` l) ==>
    I.live sl h1

val properties (x:t)
  : Lemma (
      liveness_preserved x /\
      B.loc_region_only true region `loc_includes` loc_of x /\
      region `HS.disjoint` AppCtxt.region
    )


let probe_fn = src:U64.t -> len:U64.t -> dest:t ->
  Stack bool
    (fun h0 ->
      I.live (stream_of dest) h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      I.live sl h1 /\
      (if b
       then (
        Seq.length (I.get_read sl h1) == 0 /\
        modifies (I.footprint sl) h0 h1
       )
       else (
        h0 == h1
       )))
module CBOR.Pulse.API.Borrow.ArrayPtr
open Pulse
open CBOR.Pulse.API.Borrow
open Pulse.Lib.Trade
module AP = Pulse.Lib.ArrayPtr
open CBOR.Pulse.API.Borrow.Array
#lang-pulse

inline_for_extraction
let bptr (a: lifetime) t = AP.ptr t

let pts_to #a #t (r: bptr a t) (v: Seq.seq t) =
  exists* p. a >:> AP.pts_to r #p v

unfold instance bref_pts_to #a #t : has_pts_to (bptr a t) (Seq.seq t) = { pts_to = fun p #f r -> pts_to p r }

instance val duplicable_pts_to #a #t (r: bptr a t) v : duplicable (r |-> v)

inline_for_extraction
unobservable
fn bptr_of_ptr #a #t (r: AP.ptr t) (#y: erased (Seq.seq t))
  requires exists* p. a >:> AP.pts_to r #p y
  returns r: bptr a t
  ensures r |-> y

inline_for_extraction
unobservable
fn use_bref #a #t (r: bptr a t) (#y: erased (Seq.seq t))
  requires a
  requires r |-> y
  returns r: AP.ptr t
  ensures exists* p. AP.pts_to r #p y ** trade (AP.pts_to r #p y) a

inline_for_extraction
unobservable
fn bptr_of_barray #a #t (r: barray a t) (len: SizeT.t) (#y: erased (Seq.seq t))
  requires r |-> y
  requires pure (Seq.length y == SizeT.v len)
  returns r: bptr a t
  ensures r |-> y
module CBOR.Pulse.API.Borrow.Array
open Pulse
open CBOR.Pulse.API.Borrow
open Pulse.Lib.Trade
module A = Pulse.Lib.Array
#lang-pulse

inline_for_extraction
val barray (a: lifetime) (t: Type0) : Type0

val pts_to #a #t (r: barray a t) (v: Seq.seq t) : slprop

unfold instance bref_pts_to #a #t : has_pts_to (barray a t) (Seq.seq t) = { pts_to = fun p #f r -> pts_to p r }

instance val duplicable_pts_to #a #t (r: barray a t) v : duplicable (r |-> v)

inline_for_extraction
unobservable
fn barray_of_array #a #t (r: A.array t) (#y: erased (Seq.seq t))
  requires exists* p. a >:> A.pts_to r #p y
  returns r: barray a t
  ensures r |-> y

inline_for_extraction
unobservable
fn use_bref #a #t (r: barray a t) (#y: erased (Seq.seq t))
  requires a
  requires r |-> y
  returns r: A.array t
  ensures exists* p. A.pts_to r #p y ** trade (A.pts_to r #p y) a

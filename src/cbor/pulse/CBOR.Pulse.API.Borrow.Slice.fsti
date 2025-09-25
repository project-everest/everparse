module CBOR.Pulse.API.Borrow.Slice
open Pulse
open CBOR.Pulse.API.Borrow
open Pulse.Lib.Trade
module S = Pulse.Lib.Slice
open CBOR.Pulse.API.Borrow.Array
open CBOR.Pulse.API.Borrow.ArrayPtr
#lang-pulse

inline_for_extraction
val bslice (a: lifetime) (t: Type0) : Type0

inline_for_extraction
val len #a #t (r: bslice a t) : SizeT.t

val pts_to #a #t (r: bslice a t) (v: Seq.seq t) : slprop

unfold instance bref_pts_to #a #t : has_pts_to (bslice a t) (Seq.seq t) = { pts_to = fun p #f r -> pts_to p r }

instance val duplicable_pts_to #a #t (r: bslice a t) v : duplicable (r |-> v)

ghost fn pts_to_len #a #t (r: bslice a t) (#y: erased (Seq.seq t))
  preserves r |-> y
  ensures pure (Seq.length y == SizeT.v (len r))

inline_for_extraction
unobservable
fn bslice_of_slice #a #t (r: S.slice t) (#y: erased (Seq.seq t))
  requires exists* p. a >:> S.pts_to r #p y
  returns r: bslice a t
  ensures r |-> y

inline_for_extraction
unobservable
fn use_bref #a #t (r: bslice a t) (#y: erased (Seq.seq t))
  requires a
  requires r |-> y
  returns r: S.slice t
  ensures exists* p. S.pts_to r #p y ** trade (S.pts_to r #p y) a

inline_for_extraction
unobservable
fn bslice_of_barray #a #t (r: barray a t) (len: SizeT.t) (#y: erased (Seq.seq t))
  requires r |-> y
  requires pure (Seq.length y == SizeT.v len)
  returns r: bslice a t
  ensures r |-> y

inline_for_extraction
unobservable
fn bslice_of_bptr #a #t (r: bptr a t) (len: SizeT.t) (#y: erased (Seq.seq t))
  requires r |-> y
  requires pure (Seq.length y == SizeT.v len)
  returns r: bslice a t
  ensures r |-> y

inline_for_extraction
unobservable
fn bptr_of_bslice #a #t (r: bslice a t) (#y: erased (Seq.seq t))
  requires r |-> y
  returns r: bptr a t
  ensures r |-> y
module CBOR.Pulse.API.Borrow.Slice
open Pulse
open CBOR.Pulse.API.Borrow
open Pulse.Lib.Trade
module S = Pulse.Lib.Slice
#lang-pulse

inline_for_extraction
let bslice (a: lifetime) t = S.slice t

let pts_to #a #t (r: bslice a t) (v: Seq.seq t) =
  exists* p. a >:> S.pts_to r #p v

unfold instance bref_pts_to #a #t : has_pts_to (bslice a t) (Seq.seq t) = { pts_to = fun p #f r -> pts_to p r }

fn dup_pts_to #a #t (r: bslice a t) v () : duplicable_f (r |-> v) = {
  unfold pts_to #a #t r v;
  with p. assert a >:> S.pts_to r #p v;
  dup (a >:> S.pts_to r #p v) ();
  fold pts_to #a #t r v;
  fold pts_to #a #t r v;
}

let duplicable_pts_to #a #t r v = { dup_f = dup_pts_to #a #t r v }

inline_for_extraction
unobservable
fn bslice_of_slice #a #t (r: S.slice t) (#y: erased (Seq.seq t))
  requires exists* p. a >:> S.pts_to r #p y
  returns r: bslice a t
  ensures r |-> y
{
  fold pts_to #a #t r y;
  r
}

inline_for_extraction
unobservable
fn use_bref #a #t (r: bslice a t) (#y: erased (Seq.seq t))
  requires a
  requires r |-> y
  returns r: S.slice t
  ensures exists* p. S.pts_to r #p y ** trade (S.pts_to r #p y) a
{
  unfold pts_to #a #t r y;
  use_borrow a _;
  r
}
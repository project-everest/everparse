module CBOR.Pulse.API.Borrow.Ref
open Pulse
open CBOR.Pulse.API.Borrow
open Pulse.Lib.Trade
module R = Pulse.Lib.Reference
#lang-pulse

inline_for_extraction
let bref (a: lifetime) t = ref t

let pts_to #a #t (r: bref a t) (v: t) =
  exists* p. a >:> R.pts_to r #p v

fn dup_pts_to #a #t (r: bref a t) v () : duplicable_f (r |-> v) = {
  unfold pts_to #a #t r v;
  with p. assert a >:> R.pts_to r #p v;
  dup (a >:> R.pts_to r #p v) ();
  fold pts_to #a #t r v;
  fold pts_to #a #t r v;
}

let duplicable_pts_to #a #t r v = { dup_f = dup_pts_to #a #t r v }

inline_for_extraction
fn read #a #t (r: bref a t) (#y: erased t)
  preserves a
  preserves r |-> y
  returns x: t
  ensures rewrites_to x (reveal y)
{
  unfold pts_to r y; with p. _;
  dup (a >:> R.(pts_to r #p y)) ();
  use_borrow a R.(pts_to r #p y);
  let x = R.(!r);
  elim_trade _ _;
  fold pts_to r y;
  x
}

inline_for_extraction
unobservable
fn bref_of_ref #a #t (r: ref t) (#y: erased t)
  requires exists* p. a >:> R.pts_to r #p y
  returns r: bref a t
  ensures r |-> y
{
  fold pts_to #a #t r y;
  r
}

inline_for_extraction
unobservable
fn use_bref #a #t (r: bref a t) (#y: erased t)
  requires a
  requires r |-> y
  returns r: ref t
  ensures exists* p. R.pts_to r #p y ** trade (R.pts_to r #p y) a
{
  unfold pts_to #a #t r y;
  use_borrow a _;
  r
}
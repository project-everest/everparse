module CBOR.Pulse.API.Borrow.Ref
open Pulse
open CBOR.Pulse.API.Borrow
open Pulse.Lib.Trade
#lang-pulse

inline_for_extraction
val bref (a: lifetime) (t: Type0) : Type0

val pts_to #a #t (r: bref a t) (v: t) : slprop
unfold instance bref_pts_to #a #t : has_pts_to (bref a t) t = { pts_to = fun p #f r -> pts_to p r }

instance val duplicable_pts_to #a #t (r: bref a t) v : duplicable (r |-> v)

inline_for_extraction
fn read #a #t (r: bref a t) (#y: erased t)
  preserves a
  preserves r |-> y
  returns x: t
  ensures rewrites_to x (reveal y)

inline_for_extraction
unobservable
fn bref_of_ref #a #t (r: ref t) (#y: erased t)
  requires exists* p. a >:> r |-> Frac p y
  returns r: bref a t
  ensures a >:> r |-> y

inline_for_extraction
unobservable
fn use_bref #a #t (r: bref a t) (#y: erased t)
  requires a
  requires r |-> y
  returns r: ref t
  ensures exists* p. r |-> Frac p y ** trade (r |-> Frac p y) a
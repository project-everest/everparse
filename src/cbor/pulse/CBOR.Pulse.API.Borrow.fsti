module CBOR.Pulse.API.Borrow
open Pulse
open Pulse.Lib.Trade
module T = FStar.Tactics.V2
#lang-pulse

[@@erasable]
type lifetime = slprop

val (>:>) (a: lifetime) (p: slprop) : slprop

instance val duplicable_borrow a p : duplicable (a >:> p)

val borrowed ([@@@mkey] a: lifetime) (p: slprop) : slprop

instance val duplicable_emp : duplicable emp

ghost fn borrow (p: slprop)
  returns a: lifetime
  ensures borrowed a p
  ensures a >:> p

ghost fn end_borrow (a: lifetime) (#p: slprop)
  requires a
  requires borrowed a p
  ensures p

ghost fn use_borrow (a: lifetime) (p: slprop)
  requires a
  requires a >:> p
  ensures p
  ensures trade p a

ghost fn sub_borrow (a: lifetime) (p: slprop) (q: slprop)
    (#[T.exact (`emp)] extra:slprop) {| duplicable extra |}
    (f: unit -> stt_ghost unit emp_inames (p ** extra) (fun _ -> q ** trade q p))
  requires a >:> p
  requires extra
  ensures a >:> q

inline_for_extraction
fn with_borrow u#a (#t: Type u#a) (a: lifetime) (p: slprop) pre post
    (f: unit -> stt t (p ** pre) (fun x -> p ** post x))
  preserves a
  preserves a >:> p
  requires pre
  returns x: t
  ensures post x
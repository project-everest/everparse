module CBOR.Pulse.API.Borrow
open Pulse
open Pulse.Lib.Shift
open Pulse.Lib.Trade
module Trade = Pulse.Lib.Trade.Util
module T = FStar.Tactics.V2
#lang-pulse

let (>:>) (a: lifetime) (p: slprop) : slprop =
  shift a (p ** trade p a)

instance duplicable_borrow a p : duplicable (a >:> p) = shift_duplicable _ _

let borrowed ([@@@mkey] a: lifetime) (p: slprop) : slprop =
  pure (a == p)

fn dup_emp () : duplicable_f emp = {}
instance duplicable_emp : duplicable emp = { dup_f = dup_emp }

ghost fn borrow (p: slprop)
  returns a: lifetime
  ensures borrowed a p
  ensures a >:> p
{
  fold borrowed p p;
  intro (shift p (p ** trade p p)) fn _ { intro (trade p p) fn _ {} };
  fold p >:> p;
  p
}

ghost fn end_borrow (a: lifetime) (#p: slprop)
  requires a
  requires borrowed a p
  ensures p
{
  unfold borrowed;
  rewrite a as p;
}

ghost fn use_borrow (a: lifetime) (p: slprop)
  requires a
  requires a >:> p
  ensures p
  ensures trade p a
{
  unfold a >:> p;
  elim_shift _ _;
}

ghost fn sub_borrow (a: lifetime) (p: slprop) (q: slprop)
    (#[T.exact (`emp)] extra:slprop) {| duplicable extra |}
    (f: unit -> stt_ghost unit emp_inames (p ** extra) (fun _ -> q ** trade q p))
  requires a >:> p
  requires extra
  ensures a >:> q
{
  intro (shift a (q ** trade q a)) #(extra ** (a >:> p)) fn _ {
    use_borrow a p;
    f ();
    Trade.trans q p a;
  };
  fold a >:> q;
}

inline_for_extraction
fn with_borrow u#a (#t: Type u#a) (a: lifetime) (p: slprop) pre post
    (f: unit -> stt t (p ** pre) (fun x -> p ** post x))
  preserves a
  preserves a >:> p
  requires pre
  returns x: t
  ensures post x
{
  dup (a >:> p) ();
  use_borrow a p;
  let x = f ();
  elim_trade _ _;
  x
}
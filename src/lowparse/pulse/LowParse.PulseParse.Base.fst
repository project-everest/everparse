module LowParse.PulseParse.Base
#lang-pulse
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base
module LPS = LowParse.Pulse.Base

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice

let pts_to_parsed_prop
  (#k: parser_kind) (#t: Type) (p: parser k t)
  (w: Seq.seq byte)
  (v: t)
: Tot prop
= match parse p w with
  | None -> False
  | Some (v', consumed) -> v' == v /\
    consumed == Seq.length w

let pts_to_parsed
  (#k: parser_kind) (#t: Type) (p: parser k t)
  ([@@@mkey]input: slice byte)
  (#[exact (`1.0R)] pm: perm)
  (v: t)
: slprop =
  exists* w . S.pts_to input #pm w **
  pure (pts_to_parsed_prop p w v)

ghost fn pts_to_parsed_intro
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  ([@@@mkey]input: slice byte)
  (#pm: perm)
  (#w: Seq.seq byte)
  (v: t)
requires
  S.pts_to input #pm w **
  pure (pts_to_parsed_prop p w v)
ensures
  pts_to_parsed p input #(pm /. 2.0R) v **
  Trade.trade
    (pts_to_parsed p input #(pm /. 2.0R) v)
    (S.pts_to input #pm w)
{
  S.share input;
  fold (pts_to_parsed p input #(pm /. 2.0R) v);
  intro
    (Trade.trade
      (pts_to_parsed p input #(pm /. 2.0R) v)
      (S.pts_to input #pm w)
    )
    #((S.pts_to input #(pm /. 2.0R) w))
    fn _ {
      unfold (pts_to_parsed p input #(pm /. 2.0R) v);
      S.gather input
    };
}

ghost fn pts_to_parsed_intro_injective
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (#w: Seq.seq byte)
  (v: t)
requires
  S.pts_to input #pm w **
  pure (pts_to_parsed_prop p w v /\
    k.parser_kind_injective == true
  )
ensures
  pts_to_parsed p input #(pm) v **
  Trade.trade
    (pts_to_parsed p input #(pm) v)
    (S.pts_to input #pm w)
{
  fold (pts_to_parsed p input #(pm) v);
  intro
    (Trade.trade
      (pts_to_parsed p input #(pm) v)
      (S.pts_to input #pm w)
    )
    #emp
    fn _ {
      unfold (pts_to_parsed p input #(pm) v);
      with w' . assert (S.pts_to input #pm w');
      parse_injective p w w';
      assert pure (Seq.equal w w')
    };
}

ghost fn pts_to_parsed_elim
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (#pm: perm)
  (#v: t)
  (input: slice byte)
requires
  pts_to_parsed p input #(pm) v
ensures exists* w .
  S.pts_to input #pm w **
  Trade.trade
    (S.pts_to input #pm w)
    (pts_to_parsed p input #(pm) v) **
  pure (pts_to_parsed_prop p w v)
{
  unfold (pts_to_parsed p input #(pm) v);
  with w . assert (S.pts_to input #pm w);
  intro
    (Trade.trade
      (S.pts_to input #pm w)
      (pts_to_parsed p input #(pm) v)
    )
    #emp
    fn _ {
      fold (pts_to_parsed p input #(pm) v);
    };
}

ghost fn pts_to_parsed_ext
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_parsed p1 input #pm v ** pure (
    forall x . parse p1 x == parse p2 x
  )
  ensures pts_to_parsed p2 input #pm v
{
  unfold (pts_to_parsed p1 input #pm v);
  fold (pts_to_parsed p2 input #pm v)
}

ghost fn pts_to_parsed_ext_trade
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_parsed p1 input #pm v ** pure (
    forall x . parse p1 x == parse p2 x
  )
  ensures pts_to_parsed p2 input #pm v **
    Trade.trade
      (pts_to_parsed p2 input #pm v)
      (pts_to_parsed p1 input #pm v)
{
    pts_to_parsed_ext p2 input;
    intro
      (Trade.trade
        (pts_to_parsed p2 input #pm v)
        (pts_to_parsed p1 input #pm v)
      )
      #emp
      fn _ {
        pts_to_parsed_ext p1 input
      }
}

ghost fn pts_to_parsed_ext_gen
  (#t1: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (#t2:Type0)
  (#k2: parser_kind)
  (p2: parser k2 t2)
  (input: slice byte)
  (#pm: perm)
  (#v1: t1)
  requires pts_to_parsed p1 input #pm v1 ** pure (
    LPS.pts_to_serialized_ext_trade_gen_precond p1 p2
  )
  ensures exists* (v2: t2) . pts_to_parsed p2 input #pm v2 ** pure (
    LPS.pts_to_serialized_ext_trade_gen_post t1 t2 v1 v2
  )
{
  unfold (pts_to_parsed p1 input #pm v1);
  fold (pts_to_parsed p2 input #pm v1)
}

ghost fn pts_to_parsed_ext_trade_gen
  (#t1: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (#t2:Type0)
  (#k2: parser_kind)
  (p2: parser k2 t2)
  (input: slice byte)
  (#pm: perm)
  (#v1: t1)
  requires pts_to_parsed p1 input #pm v1 ** pure (
    LPS.pts_to_serialized_ext_trade_gen_precond p1 p2
  )
  ensures exists* (v2: t2) . pts_to_parsed p2 input #pm v2 **
    Trade.trade
      (pts_to_parsed p2 input #pm v2)
      (pts_to_parsed p1 input #pm v1) **
    pure (
      LPS.pts_to_serialized_ext_trade_gen_post t1 t2 v1 v2
    )
{
  pts_to_parsed_ext_gen p2 input;
  with v2 . assert (pts_to_parsed p2 input #pm v2);
  intro
    (Trade.trade
      (pts_to_parsed p2 input #pm v2)
      (pts_to_parsed p1 input #pm v1)
    )
    #emp
    fn _ {
      pts_to_parsed_ext_gen p1 input;
      with v1' . rewrite (pts_to_parsed p1 input #pm v1')
        as (pts_to_parsed p1 input #pm v1)
    }
}

ghost fn pts_to_serialized_parsed
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (#s: serializer p)
  (#v: t)
  (#pm: perm)
  (input: S.slice byte)
requires
  LPS.pts_to_serialized s input #pm v
ensures
  pts_to_parsed p input #pm v **
  Trade.trade
    (pts_to_parsed p input #pm v)
    (LPS.pts_to_serialized s input #pm v)
{
  LPS.pts_to_serialized_elim_trade s input;
  pts_to_parsed_intro_injective p input v;
  Trade.trans (pts_to_parsed p input #pm v) _ _
}

ghost fn pts_to_parsed_serialized
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (s: serializer p)
  (#v: t)
  (#pm: perm)
  (input: S.slice byte)
requires
  pts_to_parsed p input #pm v
ensures
  LPS.pts_to_serialized s input #pm v **
  Trade.trade
    (LPS.pts_to_serialized s input #pm v)
    (pts_to_parsed p input #pm v)
{
  pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_injective p w (serialize s v);
  LPS.pts_to_serialized_intro_trade s input v;
  Trade.trans (LPS.pts_to_serialized s input #pm v) _ _
}

let pts_to_parsed_strong_prefix_prop
  (#k: parser_kind) (#t: Type) (p: parser k t)
  (w: Seq.seq byte)
  (v: t)
: Tot prop
= k.parser_kind_subkind == Some ParserStrong /\
  begin match parse p w with
  | None -> False
  | Some (v', consumed) -> v' == v
  end

let pts_to_parsed_strong_prefix
  (#k: parser_kind) (#t: Type) (p: parser k t)
  ([@@@mkey]input: slice byte)
  (#[exact (`1.0R)] pm: perm)
  (v: t)
: slprop =
  exists* v' .
  S.pts_to input #pm v' **
  pure (
    pts_to_parsed_strong_prefix_prop p v' v
  )

ghost fn pts_to_parsed_strong_prefix_intro
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (v: t)
  (#v': bytes)
requires
  S.pts_to input #pm v' **
  pure (
    pts_to_parsed_strong_prefix_prop p v' v
  )
ensures
  pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v **
  Trade.trade
    (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v)
    (S.pts_to input #pm v')
{
  S.share input;
  fold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
  intro
    (Trade.trade
      (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v)
      (S.pts_to input #pm v')
    )
    #(S.pts_to input #(pm /. 2.0R) v')
    fn _ {
      unfold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
      S.gather input
    };
}

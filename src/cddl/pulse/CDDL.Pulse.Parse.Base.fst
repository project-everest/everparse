module CDDL.Pulse.Parse.Base
#lang-pulse
include CDDL.Pulse.Base
include CDDL.Pulse.Types
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_parse
    (#ty: Type0)
    (vmatch: perm -> ty -> cbor -> slprop)
    (#t: typ)
    (#tgt: Type0)
    (#tgt_serializable: tgt -> bool)
    (ps: parser_spec t tgt tgt_serializable)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
    (c: ty) ->
    (#p: perm) ->
    (#v: Ghost.erased cbor) ->
    stt impl_tgt
        (vmatch p c v ** pure (t v))
        (fun res -> exists* v' . vmatch p c v ** 
          r res v' **
          pure (
            t v == true /\
            ps v == v'
          )
        )

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_zero_copy_parse
    (#ty: Type0)
    (vmatch: perm -> ty -> cbor -> slprop)
    (#t: typ)
    (#tgt: Type0)
    (#tgt_serializable: tgt -> bool)
    (ps: parser_spec t tgt tgt_serializable)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
    (c: ty) ->
    (#p: perm) ->
    (#v: Ghost.erased cbor) ->
    stt impl_tgt
        (vmatch p c v ** pure (t v))
        (fun res -> exists* v' .
          r res v' **
          Trade.trade
            (r res v')
            (vmatch p c v) **
          pure (
            t v == true /\
            ps v == v'
          )
        )

let impl_zero_copy_parse_t_eq
    (#ty: Type0)
    (vmatch: perm -> ty -> cbor -> slprop)
    (#t: typ)
    (#tgt: Type0)
    (#tgt_serializable: tgt -> bool)
    (ps: parser_spec t tgt tgt_serializable)
    (#impl_tgt1: Type0)
    (r: rel impl_tgt1 tgt)
    (impl_tgt2: Type0)
    (ieq: squash (impl_tgt1 == impl_tgt2))
: Tot (squash (impl_zero_copy_parse vmatch ps #impl_tgt1 r == impl_zero_copy_parse vmatch ps #impl_tgt2 (coerce_rel r impl_tgt2 ieq)))
= ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_unit
    (#ty: Type0)
    (vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt_serializable: Ghost.erased (unit -> bool))
    ([@@@erasable]ps: Ghost.erased (parser_spec t unit tgt_serializable))
: impl_copyful_parse #ty vmatch #(Ghost.reveal t) #unit #(Ghost.reveal tgt_serializable) (Ghost.reveal ps) #unit rel_unit // FIXME: WHY WHY WHY do I need to fill in all implicits by hand?
=
    (c: _)
    (#p: _)
    (#v: _)
{
  let res = ();
  fold (rel_unit res ());
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_unit
    (#ty: Type0)
    (vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt_serializable: Ghost.erased (unit -> bool))
    ([@@@erasable]ps: Ghost.erased (parser_spec t unit tgt_serializable))
: impl_zero_copy_parse #ty vmatch #(Ghost.reveal t) #unit #(Ghost.reveal tgt_serializable) (Ghost.reveal ps) #unit rel_unit // FIXME: WHY WHY WHY do I need to fill in all implicits by hand?
=
    (c: _)
    (#p: _)
    (#v: _)
{
  let res = ();
  fold (rel_unit res ());
  ghost fn aux (_: unit)
  requires vmatch p c v ** rel_unit res ()
  ensures vmatch p c v
  {
    unfold (rel_unit res ())
  };
  Trade.intro_trade _ _ _ aux;
  res
}

(*
inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_always_false
    (#ty: Type0)
    (vmatch: perm -> ty -> cbor -> slprop)
    (#t: Ghost.erased typ)
    (#tgt_serializable: Ghost.erased (squash False -> bool))
    (ps: Ghost.erased (parser_spec t (squash False) tgt_serializable))
: impl_copyful_parse #ty vmatch #(Ghost.reveal t) #(squash False) #(Ghost.reveal tgt_serializable) (Ghost.reveal ps) #(squash False) (rel_always_false (squash False) (squash False)) // FIXME: WHY WHY WHY do I need to fill in all implicits by hand?
=
    (c: _)
    (#p: _)
    (#v: _)
{
  let res : squash False = Ghost.reveal ps v;
  fold (rel_always_false _ _ res res);
  res
}
*)

let reveal_squash_false (x: Ghost.hide (squash False)) : Tot (squash False) = Ghost.reveal x

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_always_false
    (#ty: Type0)
    (vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt_serializable: Ghost.erased (squash False -> bool))
    ([@@@erasable]ps: Ghost.erased (parser_spec t (squash False) tgt_serializable))
: impl_zero_copy_parse #ty vmatch #(Ghost.reveal t) #(squash False) #(Ghost.reveal tgt_serializable) (Ghost.reveal ps) #(squash False) (rel_always_false (squash False) (squash False)) // FIXME: WHY WHY WHY do I need to fill in all implicits by hand?
=
    (c: _)
    (#p: _)
    (#v: _)
{
  reveal_squash_false (Ghost.reveal ps v);
  let res : squash False = ();
  fold (rel_always_false _ _ res res);
  rewrite (vmatch p c v) as (Trade.trade (rel_always_false _ _ res res) (vmatch p c v)); // by contradiction
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_pure_as_zero_copy
    (#ty: Type0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]tgt_serializable: Ghost.erased (tgt -> bool))
    (#[@@@erasable]ps: Ghost.erased (parser_spec t tgt tgt_serializable))
    (i: impl_copyful_parse vmatch ps (rel_pure tgt))
: impl_zero_copy_parse #_ vmatch #(Ghost.reveal t) #tgt #(Ghost.reveal tgt_serializable) (Ghost.reveal ps) #tgt (rel_pure tgt) 
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let res = i c;
  with v' . assert (rel_pure tgt res v');
  ghost fn aux (_: unit)
  requires vmatch p c v ** rel_pure tgt res v'
  ensures vmatch p c v
  {
    unfold (rel_pure tgt res v')
  };
  Trade.intro_trade _ _ _ aux;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_ext
    (#ty: Type0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]tgt_serializable: Ghost.erased (tgt -> bool))
    (#[@@@erasable]ps: Ghost.erased (parser_spec t tgt tgt_serializable))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_copyful_parse vmatch ps r)
    (#[@@@erasable]t': Ghost.erased typ)
    (#[@@@erasable]tgt_serializable': Ghost.erased (tgt -> bool))
    ([@@@erasable]ps': Ghost.erased (parser_spec t' tgt tgt_serializable'))
    ([@@@erasable]sq: squash (
      typ_included t' t /\
      (forall (x: cbor) . Ghost.reveal t' x ==> ((Ghost.reveal ps' x <: tgt) == Ghost.reveal ps x))
    ))
: impl_copyful_parse #_ vmatch #(Ghost.reveal t') #tgt #(Ghost.reveal tgt_serializable') (Ghost.reveal ps') #impl_tgt r
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  i c
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_ext
    (#ty: Type0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]tgt_serializable: Ghost.erased (tgt -> bool))
    (#[@@@erasable]ps: Ghost.erased (parser_spec t tgt tgt_serializable))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_zero_copy_parse vmatch ps r)
    (#[@@@erasable]t': Ghost.erased typ)
    (#[@@@erasable]tgt_serializable': Ghost.erased (tgt -> bool))
    ([@@@erasable]ps': Ghost.erased (parser_spec t' tgt tgt_serializable'))
    ([@@@erasable]sq: squash (
      typ_included t' t /\
      (forall (x: cbor) . Ghost.reveal t' x ==> ((Ghost.reveal ps' x <: tgt) == Ghost.reveal ps x))
    ))
: impl_zero_copy_parse #_ vmatch #(Ghost.reveal t') #tgt #(Ghost.reveal tgt_serializable') (Ghost.reveal ps') #impl_tgt r
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  i c
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_choice
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased typ)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (parser_spec t1 tgt1 tgt_serializable1))
    (#impl1: Type0)
    (#[@@@erasable]r1: rel impl1 tgt1)
    (v1: impl_typ vmatch t1)
    (p1: impl_zero_copy_parse vmatch ps1 r1)
    (#[@@@erasable]t2: Ghost.erased typ)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable]tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#[@@@erasable]ps2: Ghost.erased (parser_spec t2 tgt2 tgt_serializable2))
    (#impl2: Type0)
    (#[@@@erasable]r2: rel impl2 tgt2)
    (p2: impl_zero_copy_parse vmatch ps2 r2)
: impl_zero_copy_parse #_ vmatch #(t_choice (Ghost.reveal t1) (Ghost.reveal t2)) #(either tgt1 tgt2) #(spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) (parser_spec_choice (Ghost.reveal ps1) (Ghost.reveal ps2) (spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2))) #(either impl1 impl2) (rel_either r1 r2)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let test = v1 c;
  if test {
    let res = p1 c;
    with v' . assert (r1 res v');
    fold (rel_either r1 r2 (Inl res) (Inl v'));
    rewrite each r1 res v' as rel_either r1 r2 (Inl res) (Inl v');
    Inl res
  } else {
    let res = p2 c;
    with v' . assert (r2 res v');
    fold (rel_either r1 r2 (Inr res) (Inr v'));
    rewrite each r2 res v' as rel_either r1 r2 (Inr res) (Inr v');
    Inr res
  }
}

// A parser implementation that skips some data instead of reading
// it. This parser implementation has no equivalent serializer

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_skip
    (#ty: Type0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#t: Ghost.erased typ)
    (#tgt: Type0)
    (#tgt_serializable: Ghost.erased (tgt -> bool))
    (ps: Ghost.erased (parser_spec t tgt tgt_serializable))
: impl_copyful_parse #_ vmatch #(Ghost.reveal t) #tgt #(Ghost.reveal tgt_serializable) (Ghost.reveal ps) #(Ghost.erased tgt) (rel_skip tgt)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let res = Ghost.hide (Ghost.reveal ps v <: tgt);
  fold (rel_skip tgt res (Ghost.reveal res));
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_either_skip
    (#ty: Type0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#t: Ghost.erased typ)
    (#tgt: Type0)
    (#tgt_serializable: Ghost.erased (tgt -> bool))
    (ps: Ghost.erased (parser_spec t tgt tgt_serializable))
    (#implt: Type0)
    (r: rel implt tgt)
: impl_copyful_parse #_ vmatch #(Ghost.reveal t) #tgt #(Ghost.reveal tgt_serializable) (Ghost.reveal ps) #(either implt (Ghost.erased tgt)) (rel_either_skip r true)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let w : Ghost.erased tgt = Ghost.hide (Ghost.reveal ps v <: tgt);
  fold (rel_either_skip r true (Inr w) (Ghost.reveal w));
  Inr w
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_skip
    (#ty: Type0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#t: Ghost.erased typ)
    (#tgt: Type0)
    (#tgt_serializable: Ghost.erased (tgt -> bool))
    (ps: Ghost.erased (parser_spec t tgt tgt_serializable))
: impl_zero_copy_parse #_ vmatch #(Ghost.reveal t) #tgt #(Ghost.reveal tgt_serializable) (Ghost.reveal ps) #(Ghost.erased tgt) (rel_skip tgt)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let res = Ghost.hide (Ghost.reveal ps v <: tgt);
  fold (rel_skip tgt res (Ghost.reveal res));
  ghost fn aux (_: unit)
  requires vmatch p c v ** rel_skip tgt res (Ghost.reveal res)
  ensures vmatch p c v
  {
    unfold (rel_skip tgt res (Ghost.reveal res));
  };
  Trade.intro_trade _ _ _ aux;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_either_skip
    (#ty: Type0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (skippable: Ghost.erased bool)
    (#t: Ghost.erased typ)
    (#tgt: Type0)
    (#tgt_serializable: Ghost.erased (tgt -> bool))
    (#ps: Ghost.erased (parser_spec t tgt tgt_serializable))
    (#implt: Type0)
    (#r: rel implt tgt)
    (ips: impl_zero_copy_parse vmatch ps r)
: impl_zero_copy_parse #_ vmatch #(Ghost.reveal t) #tgt #(Ghost.reveal tgt_serializable) (Ghost.reveal ps) #(either implt (Ghost.erased tgt)) (rel_either_skip r (Ghost.reveal skippable))
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let w = ips c;
  with v' . assert (r w v');
  Trade.rewrite_with_trade
    (r w v')
    (rel_either_skip r skippable (Inl w) v');
  Trade.trans _ _ (vmatch p c v);
  Inl w
}

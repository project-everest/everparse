module CDDL.Pulse.Parse.Base
include CDDL.Pulse.Base
include CDDL.Pulse.Types
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade

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

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_copyful_unit
    (#ty: Type0)
    (vmatch: perm -> ty -> cbor -> slprop)
    (#t: Ghost.erased typ)
    (#tgt_serializable: Ghost.erased (unit -> bool))
    (ps: Ghost.erased (parser_spec t unit tgt_serializable))
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

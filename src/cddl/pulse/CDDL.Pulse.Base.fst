module CDDL.Pulse.Base
#lang-pulse
include CDDL.Spec.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_typ
    (#ty: Type)
    (vmatch: perm -> ty -> cbor -> slprop)
    (#b: option cbor)
    (t: bounded_typ_gen b)
=
    (c: ty) ->
    (#p: perm) ->
    (#v: Ghost.erased cbor) ->
    stt bool
        (vmatch p c v ** pure (
            opt_precedes (Ghost.reveal v) b
        ))
        (fun res -> vmatch p c v ** pure (
            opt_precedes (Ghost.reveal v) b /\
            res == t v
        ))

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_coerce_to_bounded_typ
    (#ty: Type u#0)
    (vmatch: perm -> ty -> cbor -> slprop)
    (b: Ghost.erased (option cbor))
    (#t: Ghost.erased typ)
    (f: impl_typ vmatch t)
: impl_typ u#0 #ty vmatch #b (coerce_to_bounded_typ b t) // FIXME: WHY WHY WHY do I need to provide the implicit argument
= (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    f c;
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_t_choice
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#b: Ghost.erased (option cbor))
    (#t1 #t2: Ghost.erased (bounded_typ_gen b))
    (f1: impl_typ vmatch t1)
    (f2: impl_typ vmatch t2)
: impl_typ u#0 #ty vmatch #b (t_choice t1 t2)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let test = f1 c;
    if (test)
    {
        true
    } else {
        f2 c
    }
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_t_choice_none // FIXME: WHY WHY WHY can F* not automatically infer t1 and t2 by reducing (reveal (hide None)) to None?
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#t1 #t2: bounded_typ_gen None)
    (f1: impl_typ vmatch t1)
    (f2: impl_typ vmatch t2)
: Tot (impl_typ vmatch (t_choice t1 t2))
= impl_t_choice #_ #_ #None #t1 #t2 f1 f2

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_any
    (#ty: Type u#0)
    (vmatch: perm -> ty -> cbor -> slprop)
: impl_typ u#0 #ty vmatch #None any
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    true
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_ext
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable] t1: Ghost.erased typ)
    (f1: impl_typ vmatch t1)
    ([@@@erasable] t2: Ghost.erased typ { typ_equiv t1 t2 })
: impl_typ u#0 #ty vmatch #None (Ghost.reveal t2)
= (c: _)
  (#p: _)
  (#v: _)
{
  f1 c
}

inline_for_extraction
let with_cbor_literal_cont_t
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (k: cbor)
  (pre: slprop)
  (t' : Type0)
  (post: (t' -> slprop))
=
    (pk: perm) ->
    (ck: t) ->
    stt t'
      (vmatch pk ck k ** pre)
      (fun res -> vmatch pk ck k ** post res)

inline_for_extraction
let with_cbor_literal_t
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (k: cbor)
=
  (pre: slprop) ->
  (t' : Type0) ->
  (post: (t' -> slprop)) ->
  (cont: (with_cbor_literal_cont_t vmatch k pre t' post)) ->
  stt t'
    pre
    (fun res -> post res)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_always_false
    (#ty: Type u#0)
    (vmatch: perm -> ty -> cbor -> slprop)
: impl_typ u#0 #ty vmatch #None t_always_false
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  false
}

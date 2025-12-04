module CDDL.Pulse.ArrayGroup
#lang-pulse
include CDDL.Spec.ArrayGroup
include CDDL.Pulse.Base
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base

module R = Pulse.Lib.Reference

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_array_group
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#b: Ghost.erased (option cbor))
    (g: array_group b)
=
    (pi: R.ref cbor_array_iterator_t) ->
    (#p: perm) ->
    (#i: Ghost.erased cbor_array_iterator_t) ->
    (#l: Ghost.erased (list cbor)) ->
    stt bool
        (R.pts_to pi i **
            cbor_array_iterator_match p i l **
            pure (opt_precedes_list (Ghost.reveal l) b)
        )
        (fun res -> exists* i' l'.
            R.pts_to pi i' **
            cbor_array_iterator_match p i' l' **
            Trade.trade
              (cbor_array_iterator_match p i' l')
              (cbor_array_iterator_match p i l) **
            pure (
                opt_precedes_list (Ghost.reveal l) b /\
                res == Some? (g l) /\
                (res == true ==> snd (Some?.v (g l)) == l')
            )
        )

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_array_group_concat
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#b: Ghost.erased (option cbor))
    (#g1: Ghost.erased (array_group b))
    (f1: impl_array_group cbor_array_iterator_match g1)
    (#g2: Ghost.erased (array_group b))
    (f2: impl_array_group cbor_array_iterator_match g2)
: impl_array_group #cbor_array_iterator_t cbor_array_iterator_match #b (array_group_concat g1 g2)
=
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list cbor))
{
    let test1 = f1 pi;
    if (test1) {
        let test2 = f2 pi;
        Trade.trans _ _ (cbor_array_iterator_match p gi l);
        test2
    } else {
        false
    }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_array_group_ext
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#b: Ghost.erased (option cbor))
    (#g1: Ghost.erased (array_group b))
    (f1: impl_array_group cbor_array_iterator_match g1)
    (g2: Ghost.erased (array_group b))
    (sq: squash (array_group_equiv g1 g2))
: impl_array_group #cbor_array_iterator_t cbor_array_iterator_match #b (Ghost.reveal g2)
=
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list cbor))
{
  f1 pi
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_array_group_empty
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#b: Ghost.erased (option cbor))
    (_: unit)
: impl_array_group #cbor_array_iterator_t cbor_array_iterator_match #b (array_group_empty #b)
=
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list cbor))
{
  Trade.refl (cbor_array_iterator_match p gi l);
  true
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_array_group_always_false
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#b: Ghost.erased (option cbor))
    (_: unit)
: impl_array_group #cbor_array_iterator_t cbor_array_iterator_match #b (array_group_always_false #b)
=
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list cbor))
{
  Trade.refl (cbor_array_iterator_match p gi l);
  false
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_array_group_choice
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#b: Ghost.erased (option cbor))
    (#g1: Ghost.erased (array_group b))
    (f1: impl_array_group cbor_array_iterator_match g1)
    (#g2: Ghost.erased (array_group b))
    (f2: impl_array_group cbor_array_iterator_match g2)
: impl_array_group #cbor_array_iterator_t cbor_array_iterator_match #b (array_group_choice g1 g2)
=
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list cbor))
{
    let i = !pi;
    let test1 = f1 pi;
    if (test1) {
      true
    } else {
      Trade.elim _ (cbor_array_iterator_match p i l);
      pi := i;
      f2 pi
    }
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_array_group_zero_or_one
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#b: Ghost.erased (option cbor))
    (#g1: Ghost.erased (array_group b))
    (f1: impl_array_group cbor_array_iterator_match g1)
: impl_array_group #cbor_array_iterator_t cbor_array_iterator_match #b (array_group_zero_or_one g1)
= impl_array_group_choice f1 (impl_array_group_empty ())

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_array_group_zero_or_more
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#g1: Ghost.erased (array_group None) { array_group_is_nonempty g1 })
    (f1: impl_array_group cbor_array_iterator_match g1)
: impl_array_group #cbor_array_iterator_t cbor_array_iterator_match #None (array_group_zero_or_more g1)
=
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list cbor))
{
    let mut pcont = true;
    Trade.refl (cbor_array_iterator_match p gi l);
    while (
      let cont = !pcont;
      cont
    ) invariant cont . exists* gi1 l1 .
      R.pts_to pi gi1 **
      cbor_array_iterator_match p gi1 l1 **
      Trade.trade
        (cbor_array_iterator_match p gi1 l1)
        (cbor_array_iterator_match p gi l) **
      R.pts_to pcont cont **
      pure (
        begin match array_group_zero_or_more g1 l, array_group_zero_or_more g1 l1 with
        | None, None -> True
        | Some (_, rem), Some (_, rem1) -> rem == rem1
        | _ -> False
        end /\
        (cont == false ==> None? (Ghost.reveal g1 l1))
      )
    {
      with gi1 l1 . assert (cbor_array_iterator_match p gi1 l1);
      let i1 = !pi;
      Trade.rewrite_with_trade
        (cbor_array_iterator_match p gi1 l1)
        (cbor_array_iterator_match p i1 l1);
      Trade.trans _ _ (cbor_array_iterator_match p gi l);
      let cont = f1 pi;
      if (not cont) {
        Trade.elim _ (cbor_array_iterator_match p i1 l1);
        pi := i1;
        pcont := false;
      } else {
        Trade.trans _ _ (cbor_array_iterator_match p gi l)
      }
    };
    true
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_array_group_one_or_more
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#g1: Ghost.erased (array_group None) { array_group_is_nonempty g1 })
    (f1: impl_array_group cbor_array_iterator_match g1)
: impl_array_group #cbor_array_iterator_t cbor_array_iterator_match #None (array_group_one_or_more g1)
= (impl_array_group_concat f1 (impl_array_group_zero_or_more f1))

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_array_group_item
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (cbor_array_iterator_is_done: array_iterator_is_empty_t cbor_array_iterator_match)
  (cbor_array_iterator_next: array_iterator_next_t vmatch cbor_array_iterator_match)
    (#b: Ghost.erased (option cbor))
    (#ty: Ghost.erased (bounded_typ_gen b))
    (fty: impl_typ u#0 vmatch ty)
: impl_array_group #cbor_array_iterator_t cbor_array_iterator_match #b (array_group_item ty)
=
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list cbor))
{
    let i = !pi;
    let is_done = cbor_array_iterator_is_done i;
    if (is_done) {
      Trade.rewrite_with_trade
        (cbor_array_iterator_match p gi l)
        (cbor_array_iterator_match p i l);
        false
    } else {
        let c = cbor_array_iterator_next pi;
        let test = fty c;
        Trade.elim_hyp_l _ _ (cbor_array_iterator_match p gi l);
        test
    }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_t_array
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_array_iterator_init: array_iterator_start_t vmatch cbor_array_iterator_match)
  (cbor_array_iterator_is_done: array_iterator_is_empty_t cbor_array_iterator_match)
    (#b: Ghost.erased (option cbor))
    (#g: Ghost.erased (array_group b))
    (ig: (impl_array_group cbor_array_iterator_match (g)))
: impl_typ u#0 #t vmatch #b (t_array g)
=
    (c: t)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let ty = cbor_get_major_type c;
    if (ty = cbor_major_type_array) {
        let i = cbor_array_iterator_init c;
        with p' (l: list cbor) . assert (cbor_array_iterator_match p' i l);
        let l' : Ghost.erased (list cbor) = Ghost.hide (Ghost.reveal (CArray?.v (unpack v)));
        Trade.rewrite_with_trade (cbor_array_iterator_match p' i l) (cbor_array_iterator_match p' i l'); // FIXME: WHY WHY WHY?
        Trade.trans _ _ (vmatch p c v);
        let mut pi = i;
        let b_success = ig pi #p' #i #l';
        Trade.trans _ _ (vmatch p c v);
        if (b_success) {
          with l2 gi2 . assert (cbor_array_iterator_match p' gi2 l2);
          let i' = ! pi;
          Trade.rewrite_with_trade
            (cbor_array_iterator_match p' gi2 l2)
            (cbor_array_iterator_match p' i' l2);
          Trade.trans _ _ (vmatch p c v);
          let b_end = cbor_array_iterator_is_done i';
          Trade.elim _ _;
          b_end
        } else {
          Trade.elim _ _;
          false
        }
   } else {
     false
   }
}

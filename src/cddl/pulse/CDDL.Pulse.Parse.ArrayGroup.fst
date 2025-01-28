module CDDL.Pulse.Parse.ArrayGroup
include CDDL.Spec.ArrayGroup
include CDDL.Pulse.Parse.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference

let impl_zero_copy_array_group_precond
  (t: array_group None)
  (l: list cbor)
: Tot prop
= match t l with
  | Some (l1, l2) ->
    t l1 == Some (l1, [])
  | _ -> False

let impl_zero_copy_array_group_postcond
  (#t: array_group None)
  (#tgt: Type0)
  (#tgt_size: tgt -> nat)
  (#tgt_serializable: tgt -> bool)
  (ps: array_group_parser_spec t tgt_size tgt_serializable)
  (l: list cbor)
  (v: tgt)
  (l': list cbor)
: Tot prop
= match t l with
  | Some (l1, l2) ->
    t l1 == Some (l1, []) /\
    ps l1 == v /\
    l2 == l'
  | _ -> False

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_zero_copy_array_group
  (#cbor_array_iterator_t: Type)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#t: array_group None)
    (#tgt: Type0)
    (#tgt_size: tgt -> nat)
    (#tgt_serializable: tgt -> bool)
    (ps: array_group_parser_spec t tgt_size tgt_serializable)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
    (pc: R.ref cbor_array_iterator_t) ->
    (#c: Ghost.erased cbor_array_iterator_t) ->
    (#p: perm) ->
    (#l: Ghost.erased (list cbor)) ->
    stt impl_tgt
        (R.pts_to pc c **
          cbor_array_iterator_match p c l **
          pure (impl_zero_copy_array_group_precond t l)
        )
        (fun res -> exists* v p' c' l' .
          r res v **
          R.pts_to pc c' **
          cbor_array_iterator_match p' c' l' **
          Trade.trade
            (r res v ** cbor_array_iterator_match p' c' l')
            (cbor_array_iterator_match p c l) **
          pure (impl_zero_copy_array_group_postcond ps l v l')
        )

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_array_iterator_start: array_iterator_start_t vmatch cbor_array_iterator_match)
    (#t: Ghost.erased (array_group None))
    (#tgt: Type0)
    (#tgt_size: Ghost.erased (tgt -> nat))
    (#tgt_serializable: Ghost.erased (tgt -> bool))
    (#ps: Ghost.erased (array_group_parser_spec t tgt_size tgt_serializable))
    (#impl_tgt: Type0)
    (#r: rel impl_tgt tgt)
    (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
: impl_zero_copy_parse #ty vmatch #(t_array (Ghost.reveal t)) #tgt #(spec_array_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable)) (parser_spec_array_group (Ghost.reveal ps) (spec_array_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable))) #impl_tgt r
=
  (c: _)
  (#p: _)
  (#v: _)
{
  let ar = cbor_array_iterator_start c;
  with pl (l1: list cbor) . assert (cbor_array_iterator_match pl ar l1);
  let l : Ghost.erased (list cbor) = Ghost.hide l1;
  Trade.rewrite_with_trade (cbor_array_iterator_match pl ar l1)
    (cbor_array_iterator_match pl ar l);
  Trade.trans _ _ (vmatch p c v);
  let mut a = ar;
  let l1 : Ghost.erased (list cbor) = Ghost.hide (fst (Some?.v (Ghost.reveal t l)));
  List.Tot.append_l_nil l1;
  let res = pa a #ar #pl #l;
  Trade.elim_hyp_r _ _ _;
  Trade.trans _ _ (vmatch p c v);
  res
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array_group_item
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_array_iterator_next: array_iterator_next_t vmatch cbor_array_iterator_match)
    (#t: Ghost.erased typ)
    (#tgt: Type0)
    (#tgt_serializable: Ghost.erased (tgt -> bool))
    (#ps: Ghost.erased (parser_spec t tgt tgt_serializable))
    (#impl_tgt: Type0)
    (#r: rel impl_tgt tgt)
    (pa: impl_zero_copy_parse vmatch ps r)
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_item (Ghost.reveal t)) #tgt #(ag_spec_item_size tgt) #(Ghost.reveal tgt_serializable) (array_group_parser_spec_item (Ghost.reveal ps) (ag_spec_item_size tgt)) #impl_tgt r
=
  (pc: _)
  (#c: _)
  (#p: _)
  (#l: _)
{
  let x = cbor_array_iterator_next pc;
  let res = pa x;
  Trade.trans_hyp_l _ _ _ _;
  res
}
```

(* FAIL: I need an operation to truncate an array iterator

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array_group_concat
  (#cbor_array_iterator_t: Type)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#t1: Ghost.erased (array_group None))
    (#tgt1: Type0)
    (#tgt_size1: Ghost.erased (tgt1 -> nat))
    (#tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1)
    (#t2: Ghost.erased (array_group None))
    (#tgt2: Type0)
    (#tgt_size2: Ghost.erased (tgt2 -> nat))
    (#tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#ps2: Ghost.erased (array_group_parser_spec t2 tgt_size2 tgt_serializable2))
    (#impl_tgt2: Type0)
    (#r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_array_group cbor_array_iterator_match ps2 r2)
    (sq: squash (
      array_group_concat_unique_weak t1 t2
    ))
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_concat (Ghost.reveal t1) (Ghost.reveal t2)) #(tgt1 & tgt2) #(ag_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) #(ag_spec_concat_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) (array_group_parser_spec_concat (Ghost.reveal ps1) (Ghost.reveal ps2) (ag_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (ag_spec_concat_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2))) #(impl_tgt1 & impl_tgt2) (rel_pair r1 r2)
=
  (pc: _)
  (#c: _)
  (#p: _)
  (#l: _)
{
  let l1 = Ghost.hide (fst (Some?.v (array_group_concat t1 t2 l)));
  array_group_concat_unique_weak_elim1 t1 t2 l1;
  let res1 = pa1 pc;
  let res2 = pa2 pc;
  Trade.trans_hyp_r _ _ _ (cbor_array_iterator_match p c l);
  admit ()
}
```

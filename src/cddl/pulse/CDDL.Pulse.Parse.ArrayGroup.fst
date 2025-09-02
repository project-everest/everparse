module CDDL.Pulse.Parse.ArrayGroup
#lang-pulse
include CDDL.Pulse.ArrayGroup
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
= t l == Some (l, [])

let impl_zero_copy_array_group_postcond
  (#t: array_group None)
  (#tgt: Type0)
  (#tgt_size: tgt -> nat)
  (#tgt_serializable: tgt -> bool)
  (ps: array_group_parser_spec t tgt_size tgt_serializable)
  (l: list cbor)
  (v: tgt)
: Tot prop
= t l == Some (l, []) /\
  ps l == v

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_zero_copy_array_group
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#t: array_group None)
    (#tgt: Type0)
    (#tgt_size: tgt -> nat)
    (#tgt_serializable: tgt -> bool)
    (ps: array_group_parser_spec t tgt_size tgt_serializable)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
    (c: cbor_array_iterator_t) ->
    (#p: perm) ->
    (#l: Ghost.erased (list cbor)) ->
    stt impl_tgt
        (
          cbor_array_iterator_match p c l **
          pure (impl_zero_copy_array_group_precond t l)
        )
        (fun res -> exists* v .
          r res v **
          Trade.trade
            (r res v)
            (cbor_array_iterator_match p c l) **
          pure (impl_zero_copy_array_group_postcond ps l v)
        )

let impl_zero_copy_array_group_t_eq
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#t: array_group None)
    (#tgt: Type0)
    (#tgt_size: tgt -> nat)
    (#tgt_serializable: tgt -> bool)
    (ps: array_group_parser_spec t tgt_size tgt_serializable)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
    (impl_tgt2: Type0)
    (ieq: squash (impl_tgt == impl_tgt2))
: Tot (squash (impl_zero_copy_array_group cbor_array_iterator_match ps #impl_tgt r == impl_zero_copy_array_group cbor_array_iterator_match ps #impl_tgt2 (coerce_rel r impl_tgt2 ieq)))
= ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_array
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_array_iterator_start: array_iterator_start_t vmatch cbor_array_iterator_match)
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]tgt_size: Ghost.erased (tgt -> nat))
    (#[@@@erasable]tgt_serializable: Ghost.erased (tgt -> bool))
    (#[@@@erasable]ps: Ghost.erased (array_group_parser_spec t tgt_size tgt_serializable))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
: impl_zero_copy_parse #ty vmatch #(t_array (Ghost.reveal t)) #tgt #(spec_array_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable)) (parser_spec_array_group (Ghost.reveal ps) (spec_array_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable))) #impl_tgt r
=
  (c: _)
  (#p: _)
  (#v: _)
{
  let ar = cbor_array_iterator_start c;
  // BEGIN FIXME: change the type of l1 in the signature of cbor_array_iterator_start
  with pl (l1: list cbor) . assert (cbor_array_iterator_match pl ar l1);
  let l : Ghost.erased (list cbor) = Ghost.hide l1;
  Trade.rewrite_with_trade (cbor_array_iterator_match pl ar l1)
    (cbor_array_iterator_match pl ar l);
  Trade.trans _ _ (vmatch p c v);
  // END FIXME
  let res = pa ar;
  Trade.trans _ _ (vmatch p c v);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_array_group_ext
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#[@@@erasable]g1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt -> bool))
    (#[@@@erasable]ps1: Ghost.erased (array_group_parser_spec g1 tgt_size1 tgt_serializable1))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (f1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r)
    (#[@@@erasable]g2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt_size2: Ghost.erased (tgt -> nat))
    (#[@@@erasable]tgt_serializable2: Ghost.erased (tgt -> bool))
    ([@@@erasable]ps2: Ghost.erased (array_group_parser_spec g2 tgt_size2 tgt_serializable2))
    ([@@@erasable]sq: squash (
      array_group_included g2 g1 /\
      (forall (x: list cbor) . array_group_parser_spec_refinement g2 x ==> (
        (Ghost.reveal ps2 x <: tgt) == (Ghost.reveal ps1 x <: tgt)
      ))
    ))
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(Ghost.reveal g2) #tgt #(Ghost.reveal tgt_size2) #(Ghost.reveal tgt_serializable2) (Ghost.reveal ps2) #impl_tgt r
=
    (c: cbor_array_iterator_t)
    (#p: perm)
    (#l: Ghost.erased (list cbor))
{
  f1 c
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_array_group_bij
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#[@@@erasable]g1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt -> bool))
    (#[@@@erasable]ps1: Ghost.erased (array_group_parser_spec g1 tgt_size1 tgt_serializable1))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_zero_copy_array_group cbor_array_iterator_match ps1 r)
    (#[@@@erasable]tgt' : Type0)
    ([@@@erasable]f12: Ghost.erased (tgt -> tgt'))
    ([@@@erasable]f21: Ghost.erased (tgt' -> tgt))
    ([@@@erasable]fprf_21_12: (x: tgt) -> squash (Ghost.reveal f21 (Ghost.reveal f12 x) == x))
    (#impl_tgt' : Type0)
    (g12: (impl_tgt -> impl_tgt'))
    (g21: (impl_tgt' -> impl_tgt))
    ([@@@erasable]gprf_21_12: (x: impl_tgt) -> squash (g21 (g12 x) == x))
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(Ghost.reveal g1) #tgt' #(ag_size_inj tgt_size1 f21) #(serializable_inj tgt_serializable1 f21) (array_group_parser_spec_inj ps1 f12 f21 fprf_21_12) #impl_tgt' (rel_fun r g21 (Ghost.reveal f21))
=
    (c: cbor_array_iterator_t)
    (#p: perm)
    (#l: Ghost.erased (list cbor))
{
  let res1 = i c;
  with w1 . assert (r res1 w1);
  let res2 = g12 res1;
  let _ = gprf_21_12 res1;
  let _ = fprf_21_12 w1;
  Trade.rewrite_with_trade
    (r res1 w1)
    (rel_fun r g21 (Ghost.reveal f21) res2 (Ghost.reveal f12 (Ghost.reveal w1)));
  Trade.trans _ _ (cbor_array_iterator_match p c l);
  res2
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_array_group_item
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_array_iterator_next: array_iterator_next_t vmatch cbor_array_iterator_match)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]tgt_serializable: Ghost.erased (tgt -> bool))
    (#[@@@erasable]ps: Ghost.erased (parser_spec t tgt tgt_serializable))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (pa: impl_zero_copy_parse vmatch ps r)
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_item (Ghost.reveal t)) #tgt #(ag_spec_item_size tgt) #(Ghost.reveal tgt_serializable) (array_group_parser_spec_item (Ghost.reveal ps) (ag_spec_item_size tgt)) #impl_tgt r
=
  (c: _)
  (#p: _)
  (#l: _)
{
  let mut pc = c;
  let x = cbor_array_iterator_next pc;
  Trade.elim_hyp_r _ _ _;
  let res = pa x;
  Trade.trans _ _ (cbor_array_iterator_match p c l);
  res
}

module U64 = FStar.UInt64

let list_append_length_pat
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (ensures (List.Tot.length (List.Tot.append l1 l2) == List.Tot.length l1 + List.Tot.length l2))
  [SMTPat (List.Tot.append l1 l2)]
= List.Tot.append_length l1 l2

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_array_group_concat
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1)
    (v1: impl_array_group cbor_array_iterator_match t1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable]tgt_size2: Ghost.erased (tgt2 -> nat))
    (#[@@@erasable]tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#[@@@erasable]ps2: Ghost.erased (array_group_parser_spec t2 tgt_size2 tgt_serializable2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_array_group cbor_array_iterator_match ps2 r2)
    ([@@@erasable]sq: squash (
      array_group_concat_unique_weak t1 t2
    ))
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_concat (Ghost.reveal t1) (Ghost.reveal t2)) #(tgt1 & tgt2) #(ag_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) #(ag_spec_concat_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) (array_group_parser_spec_concat (Ghost.reveal ps1) (Ghost.reveal ps2) (ag_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (ag_spec_concat_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2))) #(impl_tgt1 & impl_tgt2) (rel_pair r1 r2)
=
  (c0: _)
  (#p: _)
  (#l: _)
{
  let gl = Ghost.hide (Some?.v (Ghost.reveal t1 l));
  let gl1 = Ghost.hide (fst gl);
  let gl2 = Ghost.hide (snd gl);
  CBOR.Spec.Util.list_splitAt_append_elim gl1 gl2;
  let rlen0 = length c0;
  share c0;
  intro
    (Trade.trade
      (cbor_array_iterator_match (p /. 2.0R) c0 l ** cbor_array_iterator_match (p /. 2.0R) c0 l)
      (cbor_array_iterator_match p c0 l)
    )
    #emp
    fn _
  {
    gather c0 #(p /. 2.0R) #l #(p /. 2.0R) #l;
    rewrite (cbor_array_iterator_match (p /. 2.0R +. p /. 2.0R) c0 l)
      as (cbor_array_iterator_match p c0 l)
  };
  let mut pc = c0;
  let _tmp = v1 pc;
  assert (pure (_tmp));
  with p1 gc1 l1 . assert (pts_to pc gc1 ** cbor_array_iterator_match p1 gc1 l1);
  Trade.trans_hyp_r _ _ _ _;
  let c1 = !pc;
  Trade.rewrite_with_trade (cbor_array_iterator_match p1 gc1 l1)
    (cbor_array_iterator_match p1 c1 l1);
  Trade.trans_hyp_r _ _ _ _;
  let rlen1 = length c1;
  assert (pure (U64.v rlen1 <= U64.v rlen0));
  let c0' = truncate c0 (rlen0 `U64.sub` rlen1);
  Trade.trans_hyp_l _ _ _ _;
  let w1 = pa1 c0';
  Trade.trans_hyp_l _ _ _ _;
  let w2 = pa2 c1;
  Trade.trans_hyp_r _ _ _ _;
  with z1 z2 . assert (r1 w1 z1 ** r2 w2 z2);
  let res = (w1, w2);
  Trade.rewrite_with_trade
    (r1 w1 z1 ** r2 w2 z2)
    (rel_pair r1 r2 res (z1, z2));
  Trade.trans (rel_pair r1 r2 res (z1, z2)) _ _;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_array_group_choice
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1)
    (v1: impl_array_group cbor_array_iterator_match t1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable]tgt_size2: Ghost.erased (tgt2 -> nat))
    (#[@@@erasable]tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#[@@@erasable]ps2: Ghost.erased (array_group_parser_spec t2 tgt_size2 tgt_serializable2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_array_group cbor_array_iterator_match ps2 r2)
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_choice (Ghost.reveal t1) (Ghost.reveal t2)) #(tgt1 `either` tgt2) #(ag_spec_choice_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) #(ag_spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) (array_group_parser_spec_choice (Ghost.reveal ps1) (Ghost.reveal ps2) (ag_spec_choice_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (ag_spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2))) #(impl_tgt1 `either` impl_tgt2) (rel_either r1 r2)
=
  (c0: _)
  (#p: _)
  (#l: _)
{
  let mut pc = c0;
  let test1 = v1 pc;
  Trade.elim _ _;
  if (test1) {
    let w1 = pa1 c0;
    with z1 . assert (r1 w1 z1);
    let res : either impl_tgt1 impl_tgt2 = Inl w1;
    Trade.rewrite_with_trade (r1 w1 z1) (rel_either r1 r2 res (Inl z1));
    Trade.trans _ (r1 w1 z1) _;
    res
  } else {
    let w2 = pa2 c0;
    with z2 . assert (r2 w2 z2);
    let res : either impl_tgt1 impl_tgt2 = Inr w2;
    Trade.rewrite_with_trade (r2 w2 z2) (rel_either r1 r2 res (Inr z2));
    Trade.trans _ (r2 w2 z2) _;
    res
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_array_group_zero_or_one
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1)
    (v1: impl_array_group cbor_array_iterator_match t1)
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_zero_or_one (Ghost.reveal t1)) #(option tgt1) #(ag_spec_zero_or_one_size (Ghost.reveal tgt_size1)) #(ag_spec_zero_or_one_serializable (Ghost.reveal tgt_serializable1)) (array_group_parser_spec_zero_or_one (Ghost.reveal ps1) (ag_spec_zero_or_one_size (Ghost.reveal tgt_size1)) (ag_spec_zero_or_one_serializable (Ghost.reveal tgt_serializable1))) #(option impl_tgt1) (rel_option r1)
=
  (c0: _)
  (#p: _)
  (#l: _)
{
  let mut pc = c0;
  let test1 = v1 pc;
  Trade.elim _ _;
  if (test1) {
    let w1 = pa1 c0;
    with z1 . assert (r1 w1 z1);
    let res : option impl_tgt1 = Some w1;
    Trade.rewrite_with_trade (r1 w1 z1) (rel_option r1 res (Some z1));
    Trade.trans _ (r1 w1 z1) _;
    res
  } else {
    let res : option impl_tgt1 = None #impl_tgt1;
    emp_unit (cbor_array_iterator_match p c0 l);
    Trade.rewrite_with_trade
      (cbor_array_iterator_match p c0 l)
      (rel_option r1 res None ** cbor_array_iterator_match p c0 l);
    Trade.elim_hyp_r _ _ _;
    res
  }
}

module Iterator = CDDL.Pulse.Iterator.Base

noeq
type array_iterator_t (#cbor_array_iterator_t: Type0) (impl_elt: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  ([@@@erasable]spec: Ghost.erased (Iterator.type_spec impl_elt)) // hopefully there should be at most one spec per impl_elt, otherwise Karamel monomorphization will introduce conflicts. Anyway, src_elt MUST NOT be extracted (it contains list types, etc.)
: Type0 = {
  cddl_array_iterator_contents: cbor_array_iterator_t;
  [@@@erasable]pm: perm;
  [@@@erasable]ty: Ghost.erased (array_group None);
  [@@@erasable]sz: Ghost.erased (dfst spec -> nat);
  [@@@erasable]ser: Ghost.erased (dfst spec -> bool);
  [@@@erasable]ps: Ghost.erased (array_group_parser_spec ty sz ser);
  cddl_array_iterator_impl_validate: impl_array_group cbor_array_iterator_match ty;
  cddl_array_iterator_impl_parse: impl_zero_copy_array_group cbor_array_iterator_match ps (dsnd spec);
}

inline_for_extraction
let cddl_array_iterator_impl_validate
  (#cbor_array_iterator_t: Type0) (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (#[@@@erasable]spec: Ghost.erased (Iterator.type_spec impl_elt))
  (i: array_iterator_t impl_elt cbor_array_iterator_match spec)
: Tot (impl_array_group cbor_array_iterator_match i.ty)
= i.cddl_array_iterator_impl_validate

inline_for_extraction
let cddl_array_iterator_impl_parse
  (#cbor_array_iterator_t: Type0) (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (#[@@@erasable]spec: Ghost.erased (Iterator.type_spec impl_elt))
  (i: array_iterator_t impl_elt cbor_array_iterator_match spec)
: Tot (impl_zero_copy_array_group cbor_array_iterator_match i.ps (dsnd spec))
= i.cddl_array_iterator_impl_parse

inline_for_extraction
let mk_array_iterator
  (#cbor_array_iterator_t: Type0) (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (#[@@@erasable]src_elt: Type0)
  (#[@@@erasable]r: rel impl_elt src_elt)
  (contents: cbor_array_iterator_t)
  ([@@@erasable]pm: perm)
  (#[@@@erasable]ty: Ghost.erased (array_group None))
  (#[@@@erasable]sz: Ghost.erased (src_elt -> nat))
  (#[@@@erasable]ser: Ghost.erased (src_elt -> bool))
  (#[@@@erasable]ps: Ghost.erased (array_group_parser_spec ty sz ser))
  (va: impl_array_group cbor_array_iterator_match (Ghost.reveal ty))
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
: Tot (array_iterator_t impl_elt cbor_array_iterator_match (Iterator.mk_spec r))
= {
  cddl_array_iterator_contents = contents;
  pm = pm;
  ty = ty;
  sz = sz;
  ser = ser;
  ps = ps;
  cddl_array_iterator_impl_validate = va;
  cddl_array_iterator_impl_parse = pa;
}

let mk_array_iterator_eq
  (#cbor_array_iterator_t: Type0) (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (#src_elt: Type0)
  (#r: rel impl_elt src_elt)
  (contents: cbor_array_iterator_t)
  (pm: perm)
  (#ty: Ghost.erased (array_group None))
  (#sz: Ghost.erased (src_elt -> nat))
  (#ser: Ghost.erased (src_elt -> bool))
  (#ps: Ghost.erased (array_group_parser_spec ty sz ser))
  (va: impl_array_group cbor_array_iterator_match (Ghost.reveal ty))
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
: Lemma
  (ensures (let res = mk_array_iterator contents pm va pa in
    res.cddl_array_iterator_contents == contents /\
    res.pm == pm /\
    res.ty == ty /\
    res.sz == sz /\
    res.ser == ser /\
    array_group_parser_spec ty sz ser == array_group_parser_spec res.ty res.sz res.ser /\
    res.ps == coerce_eq () ps /\
    Ghost.reveal res.ps == coerce_eq () (Ghost.reveal ps)
  ))
  [SMTPat (mk_array_iterator contents pm va pa)]
= assert_norm (
    let res = mk_array_iterator contents pm va pa in array_group_parser_spec ty sz ser == array_group_parser_spec res.ty res.sz res.ser
  );
  assert_norm (let res = mk_array_iterator contents pm va pa in res.ps == coerce_eq () ps)

let array_group_parser_spec_zero_or_more0_mk_array_iterator_eq'
  (#cbor_array_iterator_t: Type0) (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (#src_elt: Type0)
  (#r: rel impl_elt src_elt)
  (contents: cbor_array_iterator_t)
  (pm: perm)
  (#ty: Ghost.erased (array_group None))
  (#sz: Ghost.erased (src_elt -> nat))
  (#ser: Ghost.erased (src_elt -> bool))
  (#ps: Ghost.erased (array_group_parser_spec ty sz ser))
  (va: impl_array_group cbor_array_iterator_match (Ghost.reveal ty))
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
  (sq: squash (
    array_group_concat_unique_strong (Ghost.reveal ty) (Ghost.reveal ty)
  ))
: Tot (squash (
    array_group_parser_spec_zero_or_more0 (Ghost.reveal (mk_array_iterator contents pm va pa).ps) () == array_group_parser_spec_zero_or_more0 (Ghost.reveal ps) ()
  ))
= _ by (FStar.Tactics.trefl ()) // FIXME: WHY WHY WHY tactics? assert_norm does not work

#push-options "--print_implicits"

let array_group_parser_spec_zero_or_more0_mk_array_iterator_eq
  (#cbor_array_iterator_t: Type0) (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (#src_elt: Type0)
  (#r: rel impl_elt src_elt)
  (contents: cbor_array_iterator_t)
  (pm: perm)
  (#ty: Ghost.erased (array_group None))
  (#sz: Ghost.erased (src_elt -> nat))
  (#ser: Ghost.erased (src_elt -> bool))
  (#ps: Ghost.erased (array_group_parser_spec ty sz ser))
  (va: impl_array_group cbor_array_iterator_match (Ghost.reveal ty))
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
  (sq: squash (
    array_group_concat_unique_strong (Ghost.reveal ty) (Ghost.reveal ty)
  ))
: Lemma
  (let res = mk_array_iterator contents pm va pa in
    array_group_parser_spec ty sz ser == array_group_parser_spec res.ty res.sz res.ser /\
    array_group_parser_spec (array_group_zero_or_more ty) (ag_spec_zero_or_more_size sz) (ag_spec_zero_or_more_serializable ser) ==
      array_group_parser_spec (array_group_zero_or_more res.ty) (ag_spec_zero_or_more_size res.sz) (ag_spec_zero_or_more_serializable res.ser) /\
    array_group_parser_spec_zero_or_more0 (Ghost.reveal res.ps) () == coerce_eq () (array_group_parser_spec_zero_or_more0 (Ghost.reveal ps) ())
  )
= 
  let _ : squash (
    let res = mk_array_iterator contents pm va pa in
    array_group_parser_spec (array_group_zero_or_more ty) (ag_spec_zero_or_more_size sz) (ag_spec_zero_or_more_serializable ser) ==
      array_group_parser_spec (array_group_zero_or_more res.ty) (ag_spec_zero_or_more_size res.sz) (ag_spec_zero_or_more_serializable res.ser) 
  ) = _ by (
    FStar.Tactics.norm
      [
        delta_only [
          (`%(Iterator.mk_spec));
          (`%mk_array_iterator);
          (`%dfst);
          (`%Mkdtuple2?._1);
          (`%Mkdtuple2?._2);
          (`%Mkarray_iterator_t?.ty);
          (`%Mkarray_iterator_t?.sz);
          (`%Mkarray_iterator_t?.ser);
        ];
        zeta; iota; primops
      ];
    FStar.Tactics.trefl ())
  in
  array_group_parser_spec_zero_or_more0_mk_array_iterator_eq' contents pm va pa sq

let array_group_parser_spec_zero_or_more0_mk_array_iterator_eq_f
  (#cbor_array_iterator_t: Type0) (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (#src_elt: Type0)
  (#r: rel impl_elt src_elt)
  (contents: cbor_array_iterator_t)
  (pm: perm)
  (#ty: Ghost.erased (array_group None))
  (#sz: Ghost.erased (src_elt -> nat))
  (#ser: Ghost.erased (src_elt -> bool))
  (#ps: Ghost.erased (array_group_parser_spec ty sz ser))
  (va: impl_array_group cbor_array_iterator_match (Ghost.reveal ty))
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
  (sq: squash (
    array_group_concat_unique_strong (Ghost.reveal ty) (Ghost.reveal ty)
  ))
  (l: array_group_parser_spec_arg (array_group_zero_or_more ty))
: Lemma
  (let res = mk_array_iterator contents pm va pa in
    array_group_parser_spec ty sz ser == array_group_parser_spec res.ty res.sz res.ser /\
    array_group_parser_spec (array_group_zero_or_more ty) (ag_spec_zero_or_more_size sz) (ag_spec_zero_or_more_serializable ser) ==
      array_group_parser_spec (array_group_zero_or_more res.ty) (ag_spec_zero_or_more_size res.sz) (ag_spec_zero_or_more_serializable res.ser) /\
    (array_group_parser_spec_zero_or_more0 (Ghost.reveal res.ps) () l <: list src_elt) == (array_group_parser_spec_zero_or_more0 (Ghost.reveal ps) () l <: list src_elt)
  )
= array_group_parser_spec_zero_or_more0_mk_array_iterator_eq contents pm va pa sq

let rel_array_iterator_cond
  (#cbor_array_iterator_t: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (spec: Ghost.erased (Iterator.type_spec impl_elt))
  (i: array_iterator_t impl_elt cbor_array_iterator_match spec)
  (s: list (dfst spec))
  (l: list cbor)
: Tot prop
=
      array_group_zero_or_more i.ty l == Some (l, []) /\
      array_group_concat_unique_strong i.ty i.ty /\
      array_group_parser_spec_zero_or_more0 i.ps () l == (s <: list (dfst spec))

let rel_array_iterator_cond_intro
  (#cbor_array_iterator_t: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (#src_elt: Type0)
  (r: rel impl_elt src_elt)
  (i: array_iterator_t impl_elt cbor_array_iterator_match (Iterator.mk_spec r))
  (s: list src_elt)
  (l: list cbor)
: Lemma
  (requires (
      array_group_zero_or_more i.ty l == Some (l, []) /\
      array_group_concat_unique_strong i.ty i.ty /\
      array_group_parser_spec_zero_or_more0 i.ps () l == (s <: list src_elt)
  ))
  (ensures (rel_array_iterator_cond cbor_array_iterator_match (Iterator.mk_spec r) i s l))
= assert_norm ((
      array_group_zero_or_more i.ty l == Some (l, []) /\
      array_group_concat_unique_strong i.ty i.ty /\
      array_group_parser_spec_zero_or_more0 i.ps () l == (s <: list src_elt)
  ) == rel_array_iterator_cond cbor_array_iterator_match (Iterator.mk_spec r) i s l
  );
  ()

let rel_array_iterator
  (#cbor_array_iterator_t: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0) (spec: Ghost.erased (Iterator.type_spec impl_elt))
: rel (array_iterator_t impl_elt cbor_array_iterator_match spec) (list (dfst spec))
= mk_rel (fun i s -> exists* (l: list cbor) . cbor_array_iterator_match i.pm i.cddl_array_iterator_contents l **
    pure (rel_array_iterator_cond cbor_array_iterator_match spec i s l)
  )

inline_for_extraction
let cddl_array_iterator_is_empty_t
  (#cbor_array_iterator_t: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (impl_elt: Type0) =
  (spec: Ghost.erased (Iterator.type_spec impl_elt)) -> // taking `spec` as argument to the operator, rather than the type, guarantees that Karamel will produce it only (at most) once per `impl_elt` type.
  (i: array_iterator_t impl_elt cbor_array_iterator_match spec) ->
  (#l: Ghost.erased (list (dfst spec))) ->
  stt bool
    (rel_array_iterator cbor_array_iterator_match spec i l)
    (fun res ->
      rel_array_iterator cbor_array_iterator_match spec i l **
      pure (res == Nil? l)
    )

inline_for_extraction
fn cddl_array_iterator_is_empty
  (#cbor_array_iterator_t: Type0)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)   (cbor_array_iterator_is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
(impl_elt: Type0)
: cddl_array_iterator_is_empty_t #_ cbor_array_iterator_match impl_elt
= (spec: _)
  (i: _)
  (#l: _)
{
  unfold (rel_array_iterator cbor_array_iterator_match spec i l);
  let res = cbor_array_iterator_is_empty i.cddl_array_iterator_contents;
  fold (rel_array_iterator cbor_array_iterator_match spec i l);
  res
}

inline_for_extraction
let cddl_array_iterator_next_t
  (#cbor_array_iterator_t: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (impl_elt: Type0) =
  (spec: Ghost.erased (Iterator.type_spec impl_elt)) -> // taking `spec` as argument to the operator, rather than the type, guarantees that Karamel will produce it only (at most) once per `impl_elt` type.
  (pi: ref (array_iterator_t impl_elt cbor_array_iterator_match spec)) ->
  (#gi: Ghost.erased (array_iterator_t impl_elt cbor_array_iterator_match spec)) ->
  (#l: Ghost.erased (list (dfst spec))) ->
  stt impl_elt
    (
      pts_to pi gi **
      rel_array_iterator cbor_array_iterator_match (spec) gi l **
      pure (Cons? l)
    )
    (fun res -> exists* a (gi': array_iterator_t impl_elt cbor_array_iterator_match spec) q .
      pts_to pi gi' **
      dsnd spec res a **
      rel_array_iterator cbor_array_iterator_match (spec) gi' q **
      Trade.trade
        (dsnd spec res a ** rel_array_iterator cbor_array_iterator_match (spec) gi' q)
        (rel_array_iterator cbor_array_iterator_match (spec) gi l) **
      pure (Ghost.reveal l == a :: q)
    )

inline_for_extraction
fn cddl_array_iterator_next
  (#cbor_array_iterator_t: Type0) (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
  (impl_elt: Type0)
: cddl_array_iterator_next_t #_ cbor_array_iterator_match impl_elt
= (spec: _)
  (pi: _)
  (#gi: _)
  (#l: _)
{
  let i = !pi;
  unfold (rel_array_iterator cbor_array_iterator_match spec i l);
  with pmi li . assert (cbor_array_iterator_match pmi i.cddl_array_iterator_contents li);
  intro
    (Trade.trade
      (cbor_array_iterator_match pmi i.cddl_array_iterator_contents li)
      (rel_array_iterator cbor_array_iterator_match spec i l)
    )
    #emp
    fn _
  {
    fold (rel_array_iterator cbor_array_iterator_match spec i l)
  };
  array_group_concat_unique_weak_zero_or_more_right i.ty i.ty;
  array_group_concat_unique_weak_elim1 i.ty (array_group_zero_or_more i.ty) li;
  let li1 = Ghost.hide (fst (Some?.v (Ghost.reveal i.ty li)));
  let li2 = Ghost.hide (snd (Some?.v (Ghost.reveal i.ty li)));
  List.Tot.append_length li1 li2;
  CBOR.Spec.Util.list_splitAt_append_elim li1 li2;
  assert (pure (Ghost.reveal i.ty li1 == Some (Ghost.reveal li1, [])));
  share i.cddl_array_iterator_contents;
  intro
    (Trade.trade
      (cbor_array_iterator_match (pmi /. 2.0R) i.cddl_array_iterator_contents li ** cbor_array_iterator_match (pmi /. 2.0R) i.cddl_array_iterator_contents li )
      (cbor_array_iterator_match pmi i.cddl_array_iterator_contents li)
    )
    #emp
    fn _
  {
    gather i.cddl_array_iterator_contents #(pmi /. 2.0R) #li #(pmi /. 2.0R) #li;
    rewrite (cbor_array_iterator_match (pmi /. 2.0R +. pmi /. 2.0R) i.cddl_array_iterator_contents li)
      as (cbor_array_iterator_match pmi i.cddl_array_iterator_contents li)
  };
  Trade.trans _ _ (rel_array_iterator cbor_array_iterator_match spec gi l);
  let len0 = length i.cddl_array_iterator_contents;
  let mut pj = i.cddl_array_iterator_contents;
  let _test : bool = cddl_array_iterator_impl_validate i pj;
  assert (pure (_test == true));
  Trade.trans_hyp_r _ _ _ _;
  with pmj gj lj . assert (pts_to pj gj ** cbor_array_iterator_match pmj gj lj);
  assert (pure (lj == li2));
  let ji = !pj;
  Trade.rewrite_with_trade
    (cbor_array_iterator_match pmj gj lj)
    (cbor_array_iterator_match pmj ji lj);
  Trade.trans_hyp_r _ _ _ _;
  let len1 = length ji;
  let j : array_iterator_t impl_elt cbor_array_iterator_match spec = { i with
    cddl_array_iterator_contents = ji;
    pm = pmj /. 2.0R;
  };
  share ji;
  rewrite (cbor_array_iterator_match (pmj /. 2.0R) ji lj)
    as (cbor_array_iterator_match j.pm j.cddl_array_iterator_contents lj);
  fold (rel_array_iterator cbor_array_iterator_match spec j (List.Tot.tl l));
  intro
    (Trade.trade
      (rel_array_iterator cbor_array_iterator_match spec j (List.Tot.tl l))
      (cbor_array_iterator_match pmj ji lj)
    )
    #(cbor_array_iterator_match (pmj /. 2.0R) ji lj)
    fn _
  {
    unfold (rel_array_iterator cbor_array_iterator_match spec j (List.Tot.tl l));
    with lj' . assert (cbor_array_iterator_match j.pm j.cddl_array_iterator_contents lj');
    rewrite (cbor_array_iterator_match j.pm j.cddl_array_iterator_contents lj')
      as (cbor_array_iterator_match (pmj /. 2.0R) ji lj');
    gather ji #(pmj /. 2.0R) #lj #(pmj /. 2.0R) #lj';
    rewrite (cbor_array_iterator_match (pmj /. 2.0R +. pmj /. 2.0R) ji lj)
      as (cbor_array_iterator_match pmj ji lj)
  };
  Trade.trans_hyp_r _ _ _ _;
  pi := j;
  let tri : cbor_array_iterator_t = truncate i.cddl_array_iterator_contents (U64.sub len0 len1);
  Trade.trans_hyp_l _ _ _ _;
  with li' . assert (cbor_array_iterator_match 1.0R tri li');
  assert (pure (li' == li1));
  assert (pure (impl_zero_copy_array_group_precond i.ty li1));
//  let wq : impl_zero_copy_array_group cbor_array_iterator_match i.ps (dsnd spec) = i.cddl_array_iterator_impl_parse;
  let res : impl_elt = cddl_array_iterator_impl_parse i tri #1.0R #li';
  Trade.trans_hyp_l _ _ _ _;
  res;
}

#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_array_group_zero_or_more'
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (va1: impl_array_group cbor_array_iterator_match (Ghost.reveal t1)) // MUST be a function pointer
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1) // MUST be a function pointer
    ([@@@erasable]sq: squash (
      array_group_concat_unique_strong t1 t1
    ))
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_zero_or_more (Ghost.reveal t1)) #(list tgt1) #(ag_spec_zero_or_more_size (Ghost.reveal tgt_size1)) #(ag_spec_zero_or_more_serializable (Ghost.reveal tgt_serializable1)) 
  (array_group_parser_spec_zero_or_more0 (Ghost.reveal ps1) ())
  #(array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1)) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1))
=
  (c: _)
  (#p: _)
  (#l: _)
{
  share c;
  let res : array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1) =
    mk_array_iterator c (p /. 2.0R) va1 pa1;
  let v : (v: Ghost.erased (list tgt1) { Ghost.reveal v == (array_group_parser_spec_zero_or_more0 (Ghost.reveal res.ps) () l <: list tgt1) })  = Ghost.hide (array_group_parser_spec_zero_or_more0 (Ghost.reveal res.ps) () l <: list tgt1); // FIXME: WHY WHY WHY do I need this refinement annotation?
  array_group_parser_spec_zero_or_more0_mk_array_iterator_eq_f c (p /. 2.0R) va1 pa1 () l;
  rewrite (cbor_array_iterator_match (p /. 2.0R) c l)
    as (cbor_array_iterator_match res.pm res.cddl_array_iterator_contents l);
  rel_array_iterator_cond_intro cbor_array_iterator_match r1 res v l;
  fold (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) res (Ghost.reveal v));
  intro
    (Trade.trade
      (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) res (Ghost.reveal v))
      (cbor_array_iterator_match p c l)
    )
    #(cbor_array_iterator_match (p /. 2.0R) c l)
    fn _
  {
    unfold (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) res (Ghost.reveal v));
    with (l1: list cbor) . assert (cbor_array_iterator_match res.pm res.cddl_array_iterator_contents l1);
    rewrite (cbor_array_iterator_match res.pm res.cddl_array_iterator_contents l1)
      as (cbor_array_iterator_match (p /. 2.0R) c l1);
    gather c #(p /. 2.0R) #l #(p /. 2.0R) #l1;
    rewrite (cbor_array_iterator_match (p /. 2.0R +. p /. 2.0R) c l) // FIXME: WHY WHY WHY is `rewrite` always needed when head symbol is a variable
      as (cbor_array_iterator_match p c l)
  };
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_array_group_zero_or_more
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (va1: impl_array_group cbor_array_iterator_match (Ghost.reveal t1)) // MUST be a function pointer
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1) // MUST be a function pointer
    ([@@@erasable]sq: squash (
      array_group_concat_unique_strong t1 t1
    ))
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_zero_or_more (Ghost.reveal t1)) #(list tgt1) #(ag_spec_zero_or_more_size (Ghost.reveal tgt_size1)) #(ag_spec_zero_or_more_serializable (Ghost.reveal tgt_serializable1)) 
  (array_group_parser_spec_zero_or_more0 (Ghost.reveal ps1) ())
  #(either (slice impl_tgt1) (array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1))) (rel_either_left (rel_slice_of_list r1 false) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1)))
=
  (c: _)
  (#p: _)
  (#l: _)
{
  let i = impl_zero_copy_array_group_zero_or_more' share gather va1 pa1 sq c;
  with v . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) i v);
  let res : either (slice impl_tgt1) (array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1)) = Inr i;
  Trade.rewrite_with_trade
    (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) i v)
    (rel_either_left (rel_slice_of_list r1 false) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1)) res v);
  Trade.trans _ _ (cbor_array_iterator_match p c l);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_zero_copy_array_group_one_or_more
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (va1: impl_array_group cbor_array_iterator_match (Ghost.reveal t1)) // MUST be a function pointer
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1) // MUST be a function pointer
    ([@@@erasable]sq: squash (
      array_group_concat_unique_strong t1 t1 /\
      array_group_is_nonempty t1
    ))
: impl_zero_copy_array_group cbor_array_iterator_match (array_group_parser_spec_one_or_more0 (Ghost.reveal ps1) ())
  (rel_either_left (rel_slice_of_list r1 false) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1)))
= impl_zero_copy_array_group_ext
    (impl_zero_copy_array_group_zero_or_more share gather va1 pa1 ())
    _
    ()

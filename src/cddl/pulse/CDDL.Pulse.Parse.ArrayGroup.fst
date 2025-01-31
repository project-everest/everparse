module CDDL.Pulse.Parse.ArrayGroup
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
        (fun res -> exists* v c' .
          r res v **
          R.pts_to pc c' **
          Trade.trade
            (r res v)
            (cbor_array_iterator_match p c l) **
          pure (impl_zero_copy_array_group_postcond ps l v)
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
  // BEGIN FIXME: change the type of l1 in the signature of cbor_array_iterator_start
  with pl (l1: list cbor) . assert (cbor_array_iterator_match pl ar l1);
  let l : Ghost.erased (list cbor) = Ghost.hide l1;
  Trade.rewrite_with_trade (cbor_array_iterator_match pl ar l1)
    (cbor_array_iterator_match pl ar l);
  Trade.trans _ _ (vmatch p c v);
  // END FIXME
  let mut a = ar;
  let res = pa a;
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
  Trade.elim_hyp_r _ _ _;
  let res = pa x;
  Trade.trans _ _ (cbor_array_iterator_match p c l);
  res
}
```

module U64 = FStar.UInt64

let list_append_length_pat
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (ensures (List.Tot.length (List.Tot.append l1 l2) == List.Tot.length l1 + List.Tot.length l2))
  [SMTPat (List.Tot.append l1 l2)]
= List.Tot.append_length l1 l2

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array_group_concat
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: array_iterator_share_t cbor_array_iterator_match)
  (gather: array_iterator_gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#t1: Ghost.erased (array_group None))
    (#tgt1: Type0)
    (#tgt_size1: Ghost.erased (tgt1 -> nat))
    (#tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1)
    (v1: impl_array_group cbor_array_iterator_match t1)
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
  (#gc: _)
  (#p: _)
  (#l: _)
{
  let gl = Ghost.hide (Some?.v (Ghost.reveal t1 l));
  let gl1 = Ghost.hide (fst gl);
  let gl2 = Ghost.hide (snd gl);
  CBOR.Spec.Util.list_splitAt_append_elim gl1 gl2;
  let c0 = !pc;
  Trade.rewrite_with_trade
    (cbor_array_iterator_match p gc l)
    (cbor_array_iterator_match p c0 l); // FIXME: WHY WHY WHY? variable as head symbol
  let rlen0 = length c0;
  share c0;
  ghost fn aux (_: unit)
  requires emp ** (cbor_array_iterator_match (p /. 2.0R) c0 l ** cbor_array_iterator_match (p /. 2.0R) c0 l)
  ensures cbor_array_iterator_match p c0 l
  {
    gather c0 #(p /. 2.0R) #l #(p /. 2.0R) #l;
    rewrite (cbor_array_iterator_match (p /. 2.0R +. p /. 2.0R) c0 l)
      as (cbor_array_iterator_match p c0 l)
  };
  Trade.intro _ _ _ aux;
  Trade.trans _ _ (cbor_array_iterator_match p gc l);
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
  pc := c0';
  let w1 = pa1 pc;
  Trade.trans_hyp_l _ _ _ _;
  pc := c1;
  let w2 = pa2 pc;
  Trade.trans_hyp_r _ _ _ _;
  with z1 z2 . assert (r1 w1 z1 ** r2 w2 z2);
  let res = (w1, w2);
  Trade.rewrite_with_trade
    (r1 w1 z1 ** r2 w2 z2)
    (rel_pair r1 r2 res (z1, z2));
  Trade.trans (rel_pair r1 r2 res (z1, z2)) _ _;
  res
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array_group_choice
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#t1: Ghost.erased (array_group None))
    (#tgt1: Type0)
    (#tgt_size1: Ghost.erased (tgt1 -> nat))
    (#tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1)
    (v1: impl_array_group cbor_array_iterator_match t1)
    (#t2: Ghost.erased (array_group None))
    (#tgt2: Type0)
    (#tgt_size2: Ghost.erased (tgt2 -> nat))
    (#tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#ps2: Ghost.erased (array_group_parser_spec t2 tgt_size2 tgt_serializable2))
    (#impl_tgt2: Type0)
    (#r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_array_group cbor_array_iterator_match ps2 r2)
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_choice (Ghost.reveal t1) (Ghost.reveal t2)) #(tgt1 `either` tgt2) #(ag_spec_choice_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) #(ag_spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) (array_group_parser_spec_choice (Ghost.reveal ps1) (Ghost.reveal ps2) (ag_spec_choice_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (ag_spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2))) #(impl_tgt1 `either` impl_tgt2) (rel_either r1 r2)
=
  (pc: _)
  (#gc: _)
  (#p: _)
  (#l: _)
{
  let c0 = !pc;
  let test1 = v1 pc;
  Trade.elim _ _;
  pc := c0;
  if (test1) {
    let w1 = pa1 pc;
    with z1 . assert (r1 w1 z1);
    let res : either impl_tgt1 impl_tgt2 = Inl w1;
    Trade.rewrite_with_trade (r1 w1 z1) (rel_either r1 r2 res (Inl z1));
    Trade.trans _ (r1 w1 z1) _;
    res
  } else {
    let w2 = pa2 pc;
    with z2 . assert (r2 w2 z2);
    let res : either impl_tgt1 impl_tgt2 = Inr w2;
    Trade.rewrite_with_trade (r2 w2 z2) (rel_either r1 r2 res (Inr z2));
    Trade.trans _ (r2 w2 z2) _;
    res
  }
}
```

noeq
type array_iterator_t (#cbor_array_iterator_t: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (impl_elt: Type0)
  (spec: Ghost.erased (src_elt: Type0 & rel impl_elt src_elt)) // hopefully there should be at most one spec per impl_elt, otherwise Karamel monomorphization will introduce conflicts. Anyway, src_elt MUST NOT be extracted (it contains list types, etc.)
: Type0 = {
  cddl_array_iterator_contents: cbor_array_iterator_t;
  pm: perm;
  ty: Ghost.erased (array_group None);
  sz: Ghost.erased (dfst spec -> nat);
  ser: Ghost.erased (dfst spec -> bool);
  ps: Ghost.erased (array_group_parser_spec ty sz ser);
  cddl_array_iterator_impl_parse: impl_zero_copy_array_group cbor_array_iterator_match ps (dsnd spec);
}

module Iterator = CDDL.Pulse.Iterator.Base

inline_for_extraction
let mk_array_iterator
  (#cbor_array_iterator_t: Type0) (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0)
  (#src_elt: Type0)
  (#r: rel impl_elt src_elt)
  (contents: cbor_array_iterator_t)
  (pm: perm)
  (#ty: Ghost.erased (array_group None))
  (#sz: Ghost.erased (src_elt -> nat))
  (#ser: Ghost.erased (src_elt -> bool))
  (#ps: Ghost.erased (array_group_parser_spec ty sz ser))
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
: Tot (array_iterator_t cbor_array_iterator_match impl_elt (Iterator.mk_spec r))
= {
  cddl_array_iterator_contents = contents;
  pm = pm;
  ty = ty;
  sz = sz;
  ser = ser;
  ps = ps;
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
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
: Lemma
  (ensures (let res = mk_array_iterator contents pm pa in
    res.cddl_array_iterator_contents == contents /\
    res.pm == pm /\
    res.ty == ty /\
    res.sz == sz /\
    res.ser == ser /\
    array_group_parser_spec ty sz ser == array_group_parser_spec res.ty res.sz res.ser /\
    res.ps == coerce_eq () ps /\
    Ghost.reveal res.ps == coerce_eq () (Ghost.reveal ps)
  ))
  [SMTPat (mk_array_iterator contents pm pa)]
= let res = mk_array_iterator contents pm pa in
  assert_norm (array_group_parser_spec ty sz ser == array_group_parser_spec res.ty res.sz res.ser);
  assert_norm (res.ps == coerce_eq () ps)

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
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
  (sq: squash (
    array_group_concat_unique_strong (Ghost.reveal ty) (Ghost.reveal ty)
  ))
: Tot (squash (
    array_group_parser_spec_zero_or_more0 (Ghost.reveal (mk_array_iterator contents pm pa).ps) () == array_group_parser_spec_zero_or_more0 (Ghost.reveal ps) ()
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
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
  (sq: squash (
    array_group_concat_unique_strong (Ghost.reveal ty) (Ghost.reveal ty)
  ))
: Lemma
  (let res = mk_array_iterator contents pm pa in
    array_group_parser_spec ty sz ser == array_group_parser_spec res.ty res.sz res.ser /\
    array_group_parser_spec (array_group_zero_or_more ty) (ag_spec_zero_or_more_size sz) (ag_spec_zero_or_more_serializable ser) ==
      array_group_parser_spec (array_group_zero_or_more res.ty) (ag_spec_zero_or_more_size res.sz) (ag_spec_zero_or_more_serializable res.ser) /\
    array_group_parser_spec_zero_or_more0 (Ghost.reveal res.ps) () == coerce_eq () (array_group_parser_spec_zero_or_more0 (Ghost.reveal ps) ())
  )
= 
  let _ : squash (
    let res = mk_array_iterator contents pm pa in
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
  array_group_parser_spec_zero_or_more0_mk_array_iterator_eq' contents pm pa sq

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
  (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
  (sq: squash (
    array_group_concat_unique_strong (Ghost.reveal ty) (Ghost.reveal ty)
  ))
  (l: array_group_parser_spec_arg (array_group_zero_or_more ty))
: Lemma
  (let res = mk_array_iterator contents pm pa in
    array_group_parser_spec ty sz ser == array_group_parser_spec res.ty res.sz res.ser /\
    array_group_parser_spec (array_group_zero_or_more ty) (ag_spec_zero_or_more_size sz) (ag_spec_zero_or_more_serializable ser) ==
      array_group_parser_spec (array_group_zero_or_more res.ty) (ag_spec_zero_or_more_size res.sz) (ag_spec_zero_or_more_serializable res.ser) /\
    (array_group_parser_spec_zero_or_more0 (Ghost.reveal res.ps) () l <: list src_elt) == (array_group_parser_spec_zero_or_more0 (Ghost.reveal ps) () l <: list src_elt)
  )
= array_group_parser_spec_zero_or_more0_mk_array_iterator_eq contents pm pa sq

let rel_array_iterator_cond
  (#cbor_array_iterator_t: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0) (#src_elt: Type0) (r: rel impl_elt src_elt)
  (i: array_iterator_t cbor_array_iterator_match impl_elt (Iterator.mk_spec r))
  (s: list src_elt)
  (l: list cbor)
: Tot prop
=
      array_group_zero_or_more i.ty l == Some (l, []) /\
      array_group_concat_unique_strong i.ty i.ty /\
      array_group_parser_spec_zero_or_more0 i.ps () l == (s <: list src_elt)

let rel_array_iterator
  (#cbor_array_iterator_t: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop) (#impl_elt: Type0) (#src_elt: Type0) (r: rel impl_elt src_elt) :
    rel (array_iterator_t cbor_array_iterator_match impl_elt (Iterator.mk_spec r)) (list src_elt)
= mk_rel (fun i s -> exists* (l: list cbor) . cbor_array_iterator_match i.pm i.cddl_array_iterator_contents l **
    pure (rel_array_iterator_cond cbor_array_iterator_match r i s l)
  )

#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array_group_zero_or_more
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (share: array_iterator_share_t cbor_array_iterator_match)
  (gather: array_iterator_gather_t cbor_array_iterator_match)
    (#t1: Ghost.erased (array_group None))
    (#tgt1: Type0)
    (#tgt_size1: Ghost.erased (tgt1 -> nat))
    (#tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1) // MUST be a function pointer
    (sq: squash (
      array_group_concat_unique_strong t1 t1
    ))
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_zero_or_more (Ghost.reveal t1)) #(list tgt1) #(ag_spec_zero_or_more_size (Ghost.reveal tgt_size1)) #(ag_spec_zero_or_more_serializable (Ghost.reveal tgt_serializable1)) 
  (array_group_parser_spec_zero_or_more0 (Ghost.reveal ps1) ())
  #(array_iterator_t cbor_array_iterator_match impl_tgt1 (Iterator.mk_spec r1)) (rel_array_iterator cbor_array_iterator_match r1)
=
  (pc: _)
  (#gc: _)
  (#p: _)
  (#l: _)
{
  share gc;
  let c = !pc;
  let res : array_iterator_t cbor_array_iterator_match impl_tgt1 (Iterator.mk_spec r1) =
    mk_array_iterator c (p /. 2.0R) pa1;
  let v : (v: Ghost.erased (list tgt1) { Ghost.reveal v == (array_group_parser_spec_zero_or_more0 (Ghost.reveal res.ps) () l <: list tgt1) })  = Ghost.hide (array_group_parser_spec_zero_or_more0 (Ghost.reveal res.ps) () l <: list tgt1); // FIXME: WHY WHY WHY do I need this refinement annotation?
  array_group_parser_spec_zero_or_more0_mk_array_iterator_eq_f c (p /. 2.0R) pa1 () l;
  rewrite (cbor_array_iterator_match (p /. 2.0R) gc l)
    as (cbor_array_iterator_match res.pm res.cddl_array_iterator_contents l);
  fold (rel_array_iterator cbor_array_iterator_match r1 res (Ghost.reveal v));
  ghost fn aux (_: unit)
  requires cbor_array_iterator_match (p /. 2.0R) gc l ** rel_array_iterator cbor_array_iterator_match r1 res (Ghost.reveal v)
  ensures cbor_array_iterator_match p gc l
  {
    unfold (rel_array_iterator cbor_array_iterator_match r1 res (Ghost.reveal v));
    with (l1: list cbor) . assert (cbor_array_iterator_match res.pm res.cddl_array_iterator_contents l1);
    rewrite (cbor_array_iterator_match res.pm res.cddl_array_iterator_contents l1)
      as (cbor_array_iterator_match (p /. 2.0R) gc l1);
    gather gc #(p /. 2.0R) #l #(p /. 2.0R) #l1;
    rewrite (cbor_array_iterator_match (p /. 2.0R +. p /. 2.0R) gc l) // FIXME: WHY WHY WHY is `rewrite` always needed when head symbol is a variable
      as (cbor_array_iterator_match p gc l)
  };
  Trade.intro _ _ _ aux;
  res
}
```

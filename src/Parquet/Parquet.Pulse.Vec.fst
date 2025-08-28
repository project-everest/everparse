module Parquet.Pulse.Vec
#lang-pulse
open Pulse.Lib.Pervasives

module Trade = Pulse.Lib.Trade.Util
module SM = Pulse.Lib.SeqMatch.Util
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Rel = CDDL.Pulse.Types.Base

// a custom vector type for extractionnoeq
noeq
type vec (t:Type0) = {
  data: V.vec t;
  len: (len:SZ.t { SZ.v len == V.length data });
}


let rel_vec_of_list
  (#low #high: Type)
  (r: Rel.rel low high)
: Rel.rel (vec low) (list high)
= Rel.mk_rel (fun x y ->
    exists* s . pts_to x.data s ** SM.seq_list_match s y r ** pure (V.is_full_vec x.data /\ V.length x.data == SZ.v x.len)
  )

let option_hd
  (#t: Type)
  (l: list t)
: Tot (option t)
= match l with
  | [] -> None
  | a :: _ -> Some a

inline_for_extraction
fn impl_hd
  (#implt #spect: Type0)
  (r: Rel.rel implt spect)
  (x: vec implt)
  (#y: Ghost.erased (list spect))
requires
  rel_vec_of_list r x y
returns z: option implt
ensures
  Rel.rel_option r z (option_hd y) **
  Trade.trade
    (Rel.rel_option r z (option_hd y))
    (rel_vec_of_list r x y)
{
  unfold (rel_vec_of_list r x y);
  V.pts_to_len x.data;
  SM.seq_list_match_length r _ y;
  if (0sz = x.len) {
    fold (rel_vec_of_list r x y);
    rewrite emp as (Rel.rel_option r None (option_hd y));
    ghost fn aux (_: unit)
    requires rel_vec_of_list r x y ** Rel.rel_option r None (option_hd y)
    ensures rel_vec_of_list r x y
    {
      rewrite (Rel.rel_option r None (option_hd y)) as emp
    };
    Trade.intro _ _ _ aux;
    None
  } else {
    with s . assert (pts_to x.data s ** SM.seq_list_match s y r);
    ghost fn aux (_: unit)
    requires emp ** (pts_to x.data s ** SM.seq_list_match s y r)
    ensures rel_vec_of_list r x y
    {
      fold (rel_vec_of_list r x y)
    };
    Trade.intro _ _ _ aux;
    let rv = V.op_Array_Access x.data 0sz;
    Trade.elim_hyp_l _ _ _;
    SM.seq_list_match_cons_elim_trade _ _ r;
    Trade.trans _ _ (rel_vec_of_list r x y);
    Trade.elim_hyp_r _ _ _;
    Trade.rewrite_with_trade
      (r _ _)
      (Rel.rel_option r (Some rv) (option_hd y));
    Trade.trans _ _ (rel_vec_of_list r x y);
    Some rv
  }
}

// Two possible views:
// impl_pred #spec_footer_t #pulse_footer_t (p_data |-> data) r_spec_pulse_footer validate_all
// alternative: 
// impl_pred #seq u8 #slice u8 (r_spec_pulse_footer spec_footer impl_footer) (|->) validate_all
inline_for_extraction
let impl_pred
  (#spect #implt: Type0)
  (precond: slprop)
  (r: Rel.rel implt spect)
  (f: (spect -> GTot bool))
=
  (x: implt) ->
  (y: Ghost.erased spect) ->
  stt bool
    (precond ** r x y)
    (fun res -> precond ** r x y ** pure (res == f y))

inline_for_extraction
fn impl_for_all
  (#spect #implt: Type0)
  (precond: slprop)
  (r: Rel.rel implt spect)
  (f: Ghost.erased (spect -> Tot bool))
  (implf: impl_pred precond r f)
: impl_pred #_ #_ precond (rel_vec_of_list r) (List.Tot.for_all f)
=
  (x: _)
  (y: _)
{
  unfold (rel_vec_of_list r x y);
  V.pts_to_len x.data;
  with s . assert (pts_to x.data s);
  SM.seq_list_match_length r s y;
  Trade.refl (SM.seq_list_match s y r);
  let mut pi = 0sz;
  let mut pres = true;
  let pll = GR.alloc #(list spect) [];
  while (
    if (!pres) {
      let i = !pi;
      (SZ.lt i x.len)
    } else {
      false
    }
  ) invariant b . exists* i ll lr sr res . (
    precond **
    pts_to pi i **
    pts_to x.data s **
    pts_to pres res **
    GR.pts_to pll ll **
    SM.seq_list_match sr lr r **
    Trade.trade
      (SM.seq_list_match sr lr r)
      (SM.seq_list_match s y r) **
    pure (
      SZ.v i <= Seq.length s /\
      sr == Seq.slice s (SZ.v i) (Seq.length s) /\
      b == (res && (SZ.v i < Seq.length s)) /\
      List.Tot.length ll == SZ.v i /\
      Ghost.reveal y == List.Tot.append ll lr /\
      List.Tot.length y == List.Tot.length ll + List.Tot.length lr /\
      List.Tot.for_all f y == (res && List.Tot.for_all f lr)
    )
  ) {
    with sr lr . assert (SM.seq_list_match sr lr r);
    SM.seq_list_match_length _ _ _;
    SM.seq_list_match_cons_elim_trade _ _ _;
    let i = !pi;
    Trade.rewrite_with_trade
      (r _ _)
      (r (Seq.index s (SZ.v i)) (List.Tot.hd lr));
    Trade.trans_hyp_l _ _ _ _;
    let elt = V.op_Array_Access x.data i;
    let res = implf elt _;
    pres := res;
    if (res) {
      Trade.elim_hyp_l _ _ _;
      Trade.trans _ (SM.seq_list_match sr lr r) _;
      with ll . assert (GR.pts_to pll ll);
      List.Tot.append_assoc ll [List.Tot.hd lr] (List.Tot.tl lr);
      List.Tot.append_length ll [List.Tot.hd lr];
      GR.op_Colon_Equals pll (List.Tot.append ll [List.Tot.hd lr]);
      pi := SZ.add i 1sz;
    } else {
      Trade.elim _ (SM.seq_list_match sr lr r)
    }
  };
  GR.free pll;
  Trade.elim _ _;
  fold (rel_vec_of_list r x y);
  !pres
}

inline_for_extraction
let impl_pred2
  (#spect1 #implt1: Type0)
  (#spect2 #implt2: Type0)
  (precond: slprop)
  (r1: Rel.rel implt1 spect1)
  (r2: Rel.rel implt2 spect2)
  (f12: (spect1 -> spect2 -> GTot bool))
=
  (x1: implt1) ->
  (y1: Ghost.erased spect1) ->
  impl_pred (precond ** r1 x1 y1) r2 (f12 y1)

inline_for_extraction
fn impl_pred2_swap
  (#spect1 #implt1: Type0)
  (#spect2 #implt2: Type0)
  (#precond: slprop)
  (#r1: Rel.rel implt1 spect1)
  (#r2: Rel.rel implt2 spect2)
  (#f12: Ghost.erased (spect1 -> spect2 -> Tot bool))
  (impl12: impl_pred2 precond r1 r2 f12)
  (f21: Ghost.erased (spect2 -> spect1 -> Tot bool) {
    forall x1 x2 . Ghost.reveal f12 x1 x2 == Ghost.reveal f21 x2 x1
  })
: impl_pred2 #_ #_ #_ #_ precond r2 r1 (Ghost.reveal f21)
=
  (x2: _)
  (y2: _)
  (x1: _)
  (y1: _)
{
  impl12 x1 y1 x2 y2
}

inline_for_extraction
let impl_f_t
  (#t' #implt #spect: Type0)
  (f: (spect -> GTot t'))
  (r: Rel.rel implt spect)
= (x: implt) ->
  (y: Ghost.erased spect) ->
  stt t'
    (r x y)
    (fun res -> r x y ** pure (res == f y))

inline_for_extraction
fn impl_mem_map
  (#spect #implt: Type0)
  (#t' : eqtype)
  (r: Rel.rel implt spect)
  (f: Ghost.erased (spect -> Tot t'))
  (implf: impl_f_t f r)
  (a: t')
: impl_pred #_ #_ emp (rel_vec_of_list r) (fun l -> List.Tot.mem a (List.Tot.map (Ghost.reveal f) l))
=
  (x: _)
  (y: _)
{
  unfold (rel_vec_of_list r x y);
  V.pts_to_len x.data;
  with s . assert (pts_to x.data s);
  SM.seq_list_match_length r s y;
  Trade.refl (SM.seq_list_match s y r);
  let mut pi = 0sz;
  let mut pres = false;
  while (
    if (!pres) {
      false
    } else {
      let i = !pi;
      (SZ.lt i x.len)
    }
  ) invariant b . exists* i lr sr res . (
    pts_to pi i **
    pts_to x.data s **
    pts_to pres res **
    SM.seq_list_match sr lr r **
    Trade.trade
      (SM.seq_list_match sr lr r)
      (SM.seq_list_match s y r) **
    pure (
      SZ.v i <= Seq.length s /\
      sr == Seq.slice s (SZ.v i) (Seq.length s) /\
      b == ((not res) && (SZ.v i < Seq.length s)) /\
      List.Tot.mem a (List.Tot.map f y) == (res || List.Tot.mem a (List.Tot.map f lr))
    )
  ) {
    with sr lr . assert (SM.seq_list_match sr lr r);
    SM.seq_list_match_length _ _ _;
    SM.seq_list_match_cons_elim_trade _ _ _;
    with gelt gl . assert (r gelt gl);
    let i = !pi;
    let elt = V.op_Array_Access x.data i;
    rewrite each gelt as elt;
    let z = implf elt _;
    let res = (z = a);
    pres := res;
    if (res) {
      Trade.elim _ (SM.seq_list_match sr lr r);
      pres := true
    } else {
      Trade.elim_hyp_l _ _ _;
      Trade.trans _ (SM.seq_list_match sr lr r) _;
      pi := SZ.add i 1sz;
    }
  };
  SM.seq_list_match_length _ _ _;
  Trade.elim _ _;
  fold (rel_vec_of_list r x y);
  !pres
}

inline_for_extraction
let impl_pred3
  (#spect1 #implt1: Type0)
  (#spect2 #implt2: Type0)
  (#spect3 #implt3: Type0)
  (precond: slprop)
  (r1: Rel.rel implt1 spect1)
  (r2: Rel.rel implt2 spect2)
  (r3: Rel.rel implt3 spect3)
  (f123: (spect1 -> spect2 -> spect3 -> GTot bool))
=
  (x1: implt1) ->
  (y1: Ghost.erased spect1) ->
  impl_pred2 (precond ** r1 x1 y1) r2 r3 (f123 y1)

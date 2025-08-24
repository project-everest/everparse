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

// Two possible views:
// impl_pred #spec_footer_t #pulse_footer_t (p_data |-> data) r_spec_pulse_footer validate_all
// alternative: 
// impl_pred #seq u8 #slice u8 (r_spec_pulse_footer spec_footer impl_footer) (|->) validate_all
inline_for_extraction
let impl_pred
  (#spect #implt: Type0)
  (precond: slprop)
  (r: Rel.rel implt spect)
  (f: (spect -> Tot bool))
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

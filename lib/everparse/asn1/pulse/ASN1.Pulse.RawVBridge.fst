module ASN1.Pulse.RawVBridge
#lang-pulse

(* Bridging the value-level relation `raw_varel d` (`ASN1.Pulse.RawVRel`:
   the Pulse value `x` described by the impl descriptor `d` represents the
   raw value `y`) and the byte-level relation `raw_arel d`
   (`ASN1.Pulse.RawRel`: the bytes the JIT writer writes for `x`):
   - `split`: `raw_varel d pm x y` can be split into
     `raw_varel d (pm / 2) x y ** raw_arel d (pm / 2) x (rb k y)`;
   - `absorb`: `raw_varel d p1 x y ** raw_arel d p2 x w` can be absorbed
     back into `raw_varel d (p1 + p2) x y`, whatever `w`.
   This is the descriptor version of `ASN1.Pulse.RawBridge`, which does the
   same for the legacy descriptor `legacy_adesc k`. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Spec.Raw
open ASN1.Spec.Raw.Props
open ASN1.Pulse.RawValueRel
open ASN1.Pulse.RawRel
open ASN1.Pulse.RawBytes
open ASN1.Pulse.RawBridge
open ASN1.Pulse.RawVRel

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SB = LowParse.Spec.Base
module It = LowParse.PulseParse.Iterator
module Het = LowParse.PulseParse.Iterator.Het
module WA = ASN1.Pulse.WriteAdb
module In = ASN1.Pulse.Interpreter
module RR = ASN1.Pulse.RawRel
module T = FStar.Tactics
module Ser = ASN1.Spec.Serializer

(* VIEW nodes *)

ghost
fn split_view (#t #ty #u: Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes) (c: split_t a r f) (view: ty -> t)
: split_t (vview a view) (raw_view r view) f
= (pm: perm) (x: ty) (y: u)
{
  unfold (vview a view pm x y);
  c pm (view x) y;
  fold (vview a view (pm /. 2.0R) x y);
  fold (raw_view r view (pm /. 2.0R) x (f y))
}

ghost
fn absorb_view (#t #ty #u: Type0) (a: prel t u) (r: bprel t) (c: absorb_t a r) (view: ty -> t)
: absorb_t (vview a view) (raw_view r view)
= (p1: perm) (p2: perm) (x: ty) (y: u) (w: SB.bytes)
{
  unfold (vview a view p1 x y);
  unfold (raw_view r view p2 x w);
  c p1 p2 (view x) y w;
  fold (vview a view (p1 +. p2) x y)
}

let br_view (#t #ty #u: Type0) (#a: prel t u) (#r: bprel t) (#f: u -> GTot SB.bytes) (c: br_t a r f) (view: ty -> t)
: br_t (vview a view) (raw_view r view) f
= { sp = split_view a r f c.sp view; ab = absorb_view a r c.ab view }

(* KEEP-BYTES nodes: the writer only needs the value, the bytes are only
   carried along *)

ghost
fn split_keep_v (#s: _) (k: asn1_k s) (pm: perm) (r: option (S.slice U8.t)) (y: asn1_raw_t k)
requires keep_v k pm r y
ensures keep_v k (pm /. 2.0R) r y ** keep_own (pm /. 2.0R) r
{
  half_perm_pos pm;
  match r {
    None -> {
      unfold (keep_v k pm None y);
      fold (keep_v k (pm /. 2.0R) None y);
      fold (keep_own (pm /. 2.0R) None)
    }
    Some sl -> {
      unfold (keep_v k pm (Some sl) y);
      with v . assert (prel_slice_ser (Ser.asn1_enc k) pm sl v);
      unfold (prel_slice_ser (Ser.asn1_enc k) pm sl v);
      S.share sl;
      fold (prel_slice_ser (Ser.asn1_enc k) (pm /. 2.0R) sl v);
      fold (keep_v k (pm /. 2.0R) (Some sl) y);
      fold (keep_own (pm /. 2.0R) (Some sl))
    }
  }
}

ghost
fn absorb_keep_v (#s: _) (k: asn1_k s) (p1 p2: perm) (r: option (S.slice U8.t)) (y: asn1_raw_t k)
requires keep_v k p1 r y ** keep_own p2 r
ensures keep_v k (p1 +. p2) r y
{
  match r {
    None -> {
      unfold (keep_v k p1 None y);
      unfold (keep_own p2 None);
      fold (keep_v k (p1 +. p2) None y)
    }
    Some sl -> {
      unfold (keep_v k p1 (Some sl) y);
      with v . assert (prel_slice_ser (Ser.asn1_enc k) p1 sl v);
      unfold (prel_slice_ser (Ser.asn1_enc k) p1 sl v);
      unfold (keep_own p2 (Some sl));
      S.gather sl;
      fold (prel_slice_ser (Ser.asn1_enc k) (p1 +. p2) sl v);
      fold (keep_v k (p1 +. p2) (Some sl) y)
    }
  }
}

ghost
fn split_keep (#s: _) (k: asn1_k s) (#t: Type0) (a: prel t (asn1_raw_t k)) (r: bprel t) (f: asn1_raw_t k -> GTot SB.bytes) (c: split_t a r f)
: split_t (vkeep a (keep_v k)) (raw_keep r) f
= (pm: perm) (x: kept t) (y: asn1_raw_t k)
{
  unfold (vkeep a (keep_v k) pm x y);
  c (pm /. 2.0R) x.kval y;
  split_keep_v k (pm /. 2.0R) x.kraw y;
  fold (vkeep a (keep_v k) (pm /. 2.0R) x y);
  fold (raw_keep r (pm /. 2.0R) x (f y))
}

ghost
fn absorb_keep (#s: _) (k: asn1_k s) (#t: Type0) (a: prel t (asn1_raw_t k)) (r: bprel t) (c: absorb_t a r)
: absorb_t (vkeep a (keep_v k)) (raw_keep r)
= (p1: perm) (p2: perm) (x: kept t) (y: asn1_raw_t k) (w: SB.bytes)
{
  unfold (vkeep a (keep_v k) p1 x y);
  unfold (raw_keep r p2 x w);
  c (p1 /. 2.0R) (p2 /. 2.0R) x.kval y w;
  absorb_keep_v k (p1 /. 2.0R) (p2 /. 2.0R) x.kraw y;
  assert (pure (p1 /. 2.0R +. p2 /. 2.0R == (p1 +. p2) /. 2.0R));
  rewrite each (p1 /. 2.0R +. p2 /. 2.0R) as ((p1 +. p2) /. 2.0R);
  fold (vkeep a (keep_v k) (p1 +. p2) x y)
}

let br_keep (#s: _) (k: asn1_k s) (#t: Type0) (#a: prel t (asn1_raw_t k)) (#r: bprel t) (#f: asn1_raw_t k -> GTot SB.bytes) (c: br_t a r f)
: br_t (vkeep a (keep_v k)) (raw_keep r) f
= { sp = split_keep k a r f c.sp; ab = absorb_keep k a r c.ab }

(* SEQUENCE OF / SET OF, for any element relation *)

ghost
fn het_split_g (#s: _) (k: asn1_k s) (#t: Type0) (a: prel t (asn1_raw_t k)) (r: bprel t) (c: split_t a r (rb k))
: Het.split_t #t #(asn1_raw_t k) #SB.bytes a r (rb_r k)
= (x: t) (pm0: perm) (y1: asn1_raw_t k) (y2: SB.bytes { rb_r k y1 y2 })
{
  c pm0 x y1;
  rewrite (r (pm0 /. 2.0R) x (rb k y1)) as (r (pm0 /. 2.0R) x y2)
}

ghost
fn het_absorb_g (#s: _) (k: asn1_k s) (#t: Type0) (a: prel t (asn1_raw_t k)) (r: bprel t) (c: absorb_t a r)
: Het.absorb_t #t #(asn1_raw_t k) #SB.bytes a r
= (x: t) (pm1: perm) (pm2: perm) (y1: asn1_raw_t k) (y2: SB.bytes)
{
  c pm1 pm2 x y1 y2
}

let gml_rel (#s: _) (k: asn1_k s) (#t: Type0) (a: prel t (asn1_raw_t k)) : prel (ml t) (list (asn1_raw_t k)) =
  It.mixed_list_match a ml_ops #asn1_strong_parser_kind (parse_raw k)

ghost
fn split_gml_gen (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (#t: Type0) (a: prel t (asn1_raw_t k)) (r: bprel t) (c: split_t a r (rb k))
  (pm: perm) (x: ml t) (y: list (asn1_raw_t k))
requires gml_rel k a pm x y
ensures gml_rel k a (pm /. 2.0R) x y ** It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw (pm /. 2.0R) x (rb_list k y)
{
  half_perm_pos pm;
  rb_parsers_fwd k u;
  rb_r_functional k;
  rb_list_rel k y;
  unfold (gml_rel k a pm x y);
  Het.mixed_list_match_split a r ml_ops (parse_raw k) p_raw (rb_r k) () pm x y (rb_list k y) (het_split_g k a r c);
  fold (gml_rel k a (pm /. 2.0R) x y)
}

ghost
fn split_gml (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (#t: Type0) (a: prel t (asn1_raw_t k)) (r: bprel t) (c: split_t a r (rb k))
: split_t (gml_rel k a) (raw_ml r) (f_ml k)
= (pm: perm) (x: ml t) (y: list (asn1_raw_t k))
{
  split_gml_gen k u a r c pm x y;
  fold (raw_ml r (pm /. 2.0R) x (f_ml k y))
}

ghost
fn split_gml_sorted (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (#t: Type0) (a: prel t (asn1_raw_t k)) (r: bprel t) (c: split_t a r (rb k))
: split_t (gml_rel k a) (raw_ml_sorted r) (f_ml_sorted k)
= (pm: perm) (x: ml t) (y: list (asn1_raw_t k))
{
  split_gml_gen k u a r c pm x y;
  fold (raw_ml_sorted r (pm /. 2.0R) x (f_ml_sorted k y))
}

ghost
fn absorb_gml (#s: _) (k: asn1_k s) (#t: Type0) (a: prel t (asn1_raw_t k)) (r: bprel t) (c: absorb_t a r)
: absorb_t (gml_rel k a) (raw_ml r)
= (p1: perm) (p2: perm) (x: ml t) (y: list (asn1_raw_t k)) (w: SB.bytes)
{
  unfold (gml_rel k a p1 x y);
  unfold (raw_ml r p2 x w);
  with l . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw p2 x l);
  Het.mixed_list_match_absorb a r ml_ops (parse_raw k) p_raw p1 p2 x y l (het_absorb_g k a r c);
  fold (gml_rel k a (p1 +. p2) x y)
}

ghost
fn absorb_gml_sorted (#s: _) (k: asn1_k s) (#t: Type0) (a: prel t (asn1_raw_t k)) (r: bprel t) (c: absorb_t a r)
: absorb_t (gml_rel k a) (raw_ml_sorted r)
= (p1: perm) (p2: perm) (x: ml t) (y: list (asn1_raw_t k)) (w: SB.bytes)
{
  unfold (gml_rel k a p1 x y);
  unfold (raw_ml_sorted r p2 x w);
  with l . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw p2 x l);
  Het.mixed_list_match_absorb a r ml_ops (parse_raw k) p_raw p1 p2 x y l (het_absorb_g k a r c);
  fold (gml_rel k a (p1 +. p2) x y)
}

let br_gml (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (#t: Type0) (#a: prel t (asn1_raw_t k)) (#r: bprel t) (c: br_t a r (rb k))
: br_t (gml_rel k a) (raw_ml r) (f_ml k)
= { sp = split_gml k u a r c.sp; ab = absorb_gml k a r c.ab }

let br_gml_sorted (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (#t: Type0) (#a: prel t (asn1_raw_t k)) (#r: bprel t) (c: br_t a r (rb k))
: br_t (gml_rel k a) (raw_ml_sorted r) (f_ml_sorted k)
= { sp = split_gml_sorted k u a r c.sp; ab = absorb_gml_sorted k a r c.ab }

let vml_gml (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (pequiv #(ml t) #(list (asn1_raw_t k)) (gml_rel k (raw_varel d)) (vml_rel d))
= assert (pequiv #(ml t) #(list (asn1_raw_t k)) (gml_rel k (raw_varel d)) (vml_rel d)) by (T.norm [delta_only [`%pequiv; `%gml_rel; `%vml_rel]]; let _ = T.forall_intros () in T.trefl ())

(* CHOICE alternatives *)

let vlc_br_t (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (ld: lcdesc lc t) : Type =
  br_t (raw_vlcrel ld) (raw_lcrel ld) (f_lc lc)

let brd_lc_nil : vlc_br_t LC_NIL =
  br_false (raw_vlcrel LC_NIL) (raw_lcrel LC_NIL) (f_lc []) vlc_nil_eq

let brd_lc_single (id': asn1_id_t) (#c: asn1_content_k) (#t: Type0) (cd: cdesc c t)
  (cc: br_t (raw_vcrel cd) (raw_crel id' cd) (rb_content id' c))
: vlc_br_t (LC_SINGLE id' cd)
= lc_single_equiv id' cd;
  br_ext (raw_vlcrel (LC_SINGLE id' cd)) (raw_vlcrel (LC_SINGLE id' cd)) (raw_crel id' cd) (raw_lcrel (LC_SINGLE id' cd)) (f_lc [(id', c)]) (f_lc [(id', c)]) ()
    (br_cond cc (raw_vlcrel (LC_SINGLE id' cd)) (f_lc [(id', c)]) (fun y -> dfst y = id') (fun y _ -> raw_lc_head_val id' c [] y ())
      (vlc_single_eq id' cd) (lc_single_f id' c))

let brd_lc_cons (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (cc: br_t (raw_vcrel cd) (raw_crel id' cd) (rb_content id' c)) (ct: vlc_br_t dtl)
: vlc_br_t (LC_CONS id' cd dtl)
= lc_cons_equiv id' cd dtl;
  br_ext (raw_vlcrel (LC_CONS id' cd dtl)) (raw_vlcrel (LC_CONS id' cd dtl))
    (raw_either (raw_crel id' cd) (raw_lcrel dtl)) (raw_lcrel (LC_CONS id' cd dtl))
    (f_lc ((id', c) :: hd2 :: tl2)) (f_lc ((id', c) :: hd2 :: tl2)) ()
    (br_either #t1 #t2 cc ct
      (raw_vlcrel (LC_CONS id' cd dtl)) (f_lc ((id', c) :: hd2 :: tl2)) (fun y -> dfst y = id')
      (fun y _ -> raw_lc_head_val id' c (hd2 :: tl2) y ()) (fun y _ -> raw_lc_tail_val (id', c) (hd2 :: tl2) y ())
      (vlc_cons_inl_eq id' cd dtl) (vlc_cons_inr_eq id' cd dtl) (lc_cons_f id' c hd2 tl2))

(* ANY DEFINED BY, without a fallback *)

let vsx_br_t (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t) : Type =
  br_t (raw_vsxrel dsx) (raw_sxrel kid dsx) (f_adb kid key_k ls)

let vitems_br_t (srt: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (di: idesc items t) : Type =
  br_t (raw_virel di) (raw_irel srt di) (rb_items srt items)

let brd_sx_nil (kid: asn1_id_t) (key_k: asn1_terminal_k) : vsx_br_t kid (SX_NIL key_k) =
  br_false (raw_vsxrel (SX_NIL key_k)) (raw_sxrel kid (SX_NIL key_k)) (f_adb kid key_k []) (vadb_nil_eq #key_k)

let brd_sx_single (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t)
  (ci: vitems_br_t false di)
: vsx_br_t kid (SX_SINGLE key_k kx y di)
= adb_single_equiv kid kx y di;
  br_ext (raw_vsxrel (SX_SINGLE key_k kx y di)) (raw_vsxrel (SX_SINGLE key_k kx y di))
    (raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di)) (raw_sxrel kid (SX_SINGLE key_k kx y di))
    (f_adb kid key_k [(kx, y)]) (f_adb kid key_k [(kx, y)]) ()
    (br_cond (br_pre (WA.raw_key_enc kid key_k kx) ci) (raw_vsxrel (SX_SINGLE key_k kx y di)) (f_adb kid key_k [(kx, y)])
      (fun v -> dfst v = raw_key_of_lit key_k kx) (fun v _ -> rady_head_val kx y [] v ())
      (vadb_single_eq kx y di) (adb_single_f kid kx y))

let brd_sx_cons (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (ci: vitems_br_t false di) (ct: vsx_br_t kid dtl)
: vsx_br_t kid (SX_CONS key_k kx y di dtl)
= adb_cons_equiv kid kx y di dtl;
  br_ext (raw_vsxrel (SX_CONS key_k kx y di dtl)) (raw_vsxrel (SX_CONS key_k kx y di dtl))
    (raw_either (raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di)) (raw_sxrel kid dtl)) (raw_sxrel kid (SX_CONS key_k kx y di dtl))
    (f_adb kid key_k ((kx, y) :: hd2 :: tl2)) (f_adb kid key_k ((kx, y) :: hd2 :: tl2)) ()
    (br_either #t1 #t2 (br_pre (WA.raw_key_enc kid key_k kx) ci) ct
      (raw_vsxrel (SX_CONS key_k kx y di dtl)) (f_adb kid key_k ((kx, y) :: hd2 :: tl2))
      (fun v -> dfst v = raw_key_of_lit key_k kx)
      (fun v _ -> rady_head_val kx y (hd2 :: tl2) v ()) (fun v _ -> rady_tail_val kx y (hd2 :: tl2) v ())
      (vadb_cons_inl_eq kx y di dtl) (vadb_cons_inr_eq kx y di dtl) (adb_cons_f kid kx y hd2 tl2))

(* ANY DEFINED BY, with a fallback *)

let vfx_br_t (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) t) : Type =
  br_t (raw_vfxrel dfx (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb)) (raw_fxrel kid dfx (raw_dfbr kid key_k dfb)) (f_afb kid key_k ls gfb)

let fx_single_equiv (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t) (#fbt: Type0) (fbr: bprel fbt)
: Lemma (RR.prel_equiv #(either t fbt) (raw_either (raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di)) (raw_fxrel kid (FX_NIL key_k #fbt) fbr)) (raw_fxrel kid (FX_SINGLE key_k kx y di #fbt) fbr))
= assert (RR.prel_equiv #(either t fbt) (raw_either (raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di)) (raw_fxrel kid (FX_NIL key_k #fbt) fbr)) (raw_fxrel kid (FX_SINGLE key_k kx y di #fbt) fbr))
    by (T.norm [delta_only [`%RR.prel_equiv; `%ASN1.Pulse.RelShare.prel_equiv]];
        let _ = T.forall_intros () in
        T.norm [delta_only [`%raw_fxrel; `%raw_either]; zeta; iota];
        T.trefl ())

let brd_fx_nil (kid: asn1_id_t) (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (cf: vitems_br_t false dfb)
: vfx_br_t kid dfb (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb))
= afb_nil_equiv kid key_k (raw_dfbr kid key_k dfb);
  afb_nil_sq kid key_k gfb;
  Classical.forall_intro_3 (vafb_nil_eq key_k dfb);
  br_ext (raw_vfxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (raw_vfxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb)) (raw_fxrel kid (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_dfbr kid key_k dfb))
    (f_afb kid key_k [] gfb) (f_afb kid key_k [] gfb) ()
    (br_map (br_cat (br_term kid key_k) cf)
      (raw_vfxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
      (f_afb kid key_k [] gfb) (afb_nil_g gfb) ())

let brd_fx_single (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (ci: vitems_br_t false di) (cf: vitems_br_t false dfb)
: vfx_br_t kid dfb (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb))
= fx_single_equiv kid kx y di (raw_dfbr kid key_k dfb);
  br_ext (raw_vfxrel (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (raw_vfxrel (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (raw_either (raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di)) (raw_fxrel kid (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_dfbr kid key_k dfb)))
    (raw_fxrel kid (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (raw_dfbr kid key_k dfb))
    (f_afb kid key_k [(kx, y)] gfb) (f_afb kid key_k [(kx, y)] gfb) ()
    (br_either #t1 #(asn1_terminal_impl_t key_k & tfb) (br_pre (WA.raw_key_enc kid key_k kx) ci) (brd_fx_nil kid key_k dfb cf)
      (raw_vfxrel (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb)) (f_afb kid key_k [(kx, y)] gfb)
      (fun v -> dfst v = raw_key_of_lit key_k kx)
      (fun v _ -> rady_fb_head_val kx y [] gfb v ()) (fun v _ -> rady_fb_tail_val kx y [] gfb v ())
      (vafb_single_inl_eq kx y di gfb (raw_vfbr key_k dfb)) (vafb_single_inr_eq kx y di gfb (raw_vfbr key_k dfb)) (afb_single_f kid kx y gfb))

let brd_fx_cons (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) (asn1_terminal_impl_t key_k & tfb) t2)
  (ci: vitems_br_t false di) (ct: vfx_br_t kid dfb dtl)
: vfx_br_t kid dfb (FX_CONS key_k kx y di dtl)
= afb_cons_equiv kid kx y di dtl (raw_dfbr kid key_k dfb);
  br_ext (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (raw_either (raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di)) (raw_fxrel kid dtl (raw_dfbr kid key_k dfb)))
    (raw_fxrel kid (FX_CONS key_k kx y di dtl) (raw_dfbr kid key_k dfb))
    (f_afb kid key_k ((kx, y) :: hd2 :: tl2) gfb) (f_afb kid key_k ((kx, y) :: hd2 :: tl2) gfb) ()
    (br_either #t1 #t2 (br_pre (WA.raw_key_enc kid key_k kx) ci) ct
      (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb)) (f_afb kid key_k ((kx, y) :: hd2 :: tl2) gfb)
      (fun v -> dfst v = raw_key_of_lit key_k kx)
      (fun v _ -> rady_fb_head_val kx y (hd2 :: tl2) gfb v ()) (fun v _ -> rady_fb_tail_val kx y (hd2 :: tl2) gfb v ())
      (vafb_cons_inl_eq kx y di dtl gfb (raw_vfbr key_k dfb)) (vafb_cons_inr_eq kx y di dtl gfb (raw_vfbr key_k dfb)) (afb_cons_f kid kx y hd2 tl2 gfb))

let rb_content_adb_some_g (id: asn1_id_t) (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pf: _) (pf': _)
  (y: asn1_raw_content_t (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some fb) pf pf'))
: Lemma (rb_content id (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some fb) pf pf') y == f_tlv id (rb_items_any prefix (f_afb kid key_k ls fb)) y)
= let (| fbids, fbitems |) = fb in
  rb_content_adb_some id ipd prefix kid key_k ls fbids fbitems pf pf' y

(* The whole bridge, by mutual recursion on the descriptor *)

let va_br_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type = br_t (raw_varel d) (raw_arel d) (rb k)
let vc_br_t (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t) : Type = br_t (raw_vcrel cd) (raw_crel id cd) (rb_content id k)
let vd_br_t (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (dd: ddesc dk t) : Type = br_t (raw_vdrel dd) (raw_drel dd) (rb_dec dk)
let via_br_t (#ids: _) (#items: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (dpre: iadesc items sfxi t)
  (#sfxs: Type0) (sfxr: prel sfxi sfxs) (rsfx: bprel sfxi) (fs: sfxs -> GTot SB.bytes) : Type =
  br_t (raw_viarel dpre #sfxs sfxr) (raw_iarel dpre rsfx) (rb_items_any items fs)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec brd_a (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (u: squash (raw_ok k))
: Tot (va_br_t d) (decreases d)
= match d with
  | D_ILC id cd ->
    vrel_ilc_equiv id cd;
    rel_ilc_equiv id cd;
    br_ext _ _ _ _ _ _ () (brd_c id cd ())
  | D_CHOICE lc pf ld ->
    vrel_choice_equiv lc pf ld;
    rel_choice_equiv lc pf ld;
    br_ext _ _ _ _ _ _ () (brd_lc ld ())
  | D_ANY ->
    vrel_any_equiv ();
    rel_any_equiv ();
    br_ext _ _ _ _ _ _ () (br_slice asn1_value_enc)
  | D_VIEW d' ty view mk law ->
    vrel_view_equiv d' ty view mk law;
    rel_view_equiv d' ty view mk law;
    br_ext _ _ _ _ _ _ () (br_view (brd_a d' ()) view)
  | D_KEEP #_ #k' d' wf ->
    vrel_keep_equiv d' wf;
    rel_keep_equiv d' wf;
    br_ext _ _ _ _ _ _ () (br_keep k' (brd_a d' ()))

and brd_c (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t) (u: squash (ok_content id k))
: Tot (vc_br_t id cd) (decreases cd)
= match cd with
  | CD_TERMINAL k' ->
    vcontent_terminal_equiv k';
    content_terminal_equiv id k';
    br_ext _ _ _ _ _ _ () (br_term id k')
  | CD_RESTRICTED k' r ->
    vcontent_restricted_equiv k' r;
    content_restricted_equiv id k' r;
    br_ext _ _ _ _ _ _ () (br_term id k')
  | CD_PREFIXED d' ->
    vcontent_prefixed_equiv d';
    content_prefixed_equiv id d';
    br_ext _ _ _ _ _ _ () (br_tlv id (brd_a d' ()))
  | CD_SEQUENCE gitems di ->
    vcontent_sequence_equiv gitems di;
    content_sequence_equiv id gitems di;
    br_ext _ _ _ _ _ _ () (br_tlv id (brd_i false di ()))
  | CD_SET ids items pf di ->
    vcontent_set_equiv ids items pf di;
    content_set_equiv id ids items pf di;
    br_ext _ _ _ _ _ _ () (br_tlv id (brd_i true di ()))
  | CD_SEQUENCE_OF ne #_ #k' d' ->
    vml_gml d';
    vcontent_seq_of_equiv ne d';
    content_seq_of_equiv id ne d';
    br_ext _ _ _ _ _ _ () (br_tlv id (br_gml k' () (brd_a d' ())))
  | CD_SET_OF ne #_ #k' d' ->
    vml_gml d';
    vcontent_set_of_equiv ne d';
    content_set_of_equiv id ne d';
    br_ext _ _ _ _ _ _ () (br_tlv id (br_gml_sorted k' () (brd_a d' ())))
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    vcontent_adb_none_equiv ipd prefix kid key_k ls pf pf' dsx dpre;
    content_adb_none_equiv id ipd prefix kid key_k ls pf pf' dsx dpre;
    Classical.forall_intro (rb_content_adb_none id ipd prefix kid key_k ls pf pf');
    br_ext _ _ _ _ _ _ ()
      (br_tlv id (brd_ia dpre () (raw_vsxrel dsx) (raw_sxrel kid dsx) (f_adb kid key_k ls) (brd_sx kid dsx ())))
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre ->
    vcontent_adb_some_equiv ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    content_adb_some_equiv id ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    Classical.forall_intro (rb_content_adb_some_g id ipd prefix kid key_k ls fb pf pf');
    br_ext _ _ _ _ _ _ ()
      (br_tlv id (brd_ia dpre ()
        (raw_vfxrel dfx (raw_items_t (dsnd fb)) (raw_vfbr key_k #fb dfb)) (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)) (f_afb kid key_k ls fb)
        (brd_fx kid dfb (brd_i false dfb ()) dfx ())))
  | CD_VIEW d' ty view mk law ->
    vcontent_view_equiv d' ty view mk law;
    content_view_equiv id d' ty view mk law;
    br_ext _ _ _ _ _ _ () (br_view (brd_c id d' ()) view)

and brd_sx (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t) (u: squash (ok_ls ls))
: Tot (vsx_br_t kid dsx) (decreases dsx)
= match dsx with
  | SX_NIL _ -> brd_sx_nil kid key_k
  | SX_SINGLE _ kx y di -> brd_sx_single kid kx y di (brd_i false di ())
  | SX_CONS _ kx y di dtl -> brd_sx_cons kid kx y di dtl (brd_i false di ()) (brd_sx kid dtl ())

and brd_fx (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb) (cf: vitems_br_t false dfb)
  (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) t) (u: squash (ok_ls ls))
: Tot (vfx_br_t kid dfb dfx) (decreases dfx)
= match dfx with
  | FX_NIL _ -> brd_fx_nil kid key_k dfb cf
  | FX_SINGLE _ kx y di -> brd_fx_single kid kx y di dfb (brd_i false di ()) cf
  | FX_CONS _ kx y di dtl -> brd_fx_cons kid kx y di dfb dtl (brd_i false di ()) (brd_fx kid dfb cf dtl ())

and brd_ia (#ids: _) (#items: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (dpre: iadesc items sfxi t) (u: squash (ok_items items))
  (#sfxs: Type0) (sfxr: prel sfxi sfxs) (rsfx: bprel sfxi) (fs: sfxs -> GTot SB.bytes) (cs: br_t sfxr rsfx fs)
: Tot (via_br_t dpre sfxr rsfx fs) (decreases dpre)
= match dpre with
  | IA_NIL ->
    vitems_any_nil_equiv sfxr;
    items_any_nil_equiv rsfx;
    br_ext _ _ _ _ _ _ () cs
  | IA_SINGLE dd ->
    vitems_any_single_equiv dd sfxr;
    items_any_single_equiv dd rsfx;
    br_ext _ _ _ _ _ _ () (br_cat (brd_d dd ()) cs)
  | IA_CONS dd dtl ->
    vitems_any_cons_equiv dd dtl sfxr;
    items_any_cons_equiv dd dtl rsfx;
    br_ext _ _ _ _ _ _ () (br_cat (brd_d dd ()) (brd_ia dtl () sfxr rsfx fs cs))

and brd_lc (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (ld: lcdesc lc t) (u: squash (ok_lc lc))
: Tot (vlc_br_t ld) (decreases ld)
= match ld with
  | LC_NIL -> brd_lc_nil
  | LC_SINGLE id' cd -> brd_lc_single id' cd (brd_c id' cd ())
  | LC_CONS id' cd dtl -> brd_lc_cons id' cd dtl (brd_c id' cd ()) (brd_lc dtl ())

and brd_d (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (dd: ddesc dk t) (u: squash (ok_dec dk))
: Tot (vd_br_t dd) (decreases dd)
= match dd with
  | DD_PLAIN d' ->
    vdec_plain_equiv d';
    dec_plain_equiv d';
    br_ext _ _ _ _ _ _ () (brd_a d' ())
  | DD_OPTION d' ->
    vdec_option_equiv d';
    dec_option_equiv d';
    br_ext _ _ _ _ _ _ () (br_opt (brd_a d' ()))
  | DD_DEFAULT id0 #k defv ->
    vdec_default_equiv id0 defv;
    dec_default_equiv id0 defv;
    if In.adb_key_supported k
    then (default_nd_equiv id0 k defv; br_ext _ _ _ _ _ _ () (br_opt_nd (WA.raw_key_enc id0 k defv) (br_term id0 k)))
    else (default_opt_equiv id0 k defv; br_ext _ _ _ _ _ _ () (br_opt (br_term id0 k)))
  | DD_DEFAULT_RESTRICTED id0 #k r defv ->
    vdec_default_restricted_equiv id0 r defv;
    dec_default_restricted_equiv id0 r defv;
    if In.adb_key_supported k
    then (default_nd_equiv id0 k defv; br_ext _ _ _ _ _ _ () (br_opt_nd (WA.raw_key_enc id0 k defv) (br_term id0 k)))
    else (default_opt_equiv id0 k defv; br_ext _ _ _ _ _ _ () (br_opt (br_term id0 k)))
  | DD_VIEW d' ty view mk law ->
    vdec_view_equiv d' ty view mk law;
    dec_view_equiv d' ty view mk law;
    br_ext _ _ _ _ _ _ () (br_view (brd_d d' ()) view)

and brd_i (srt: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (di: idesc items t) (u: squash (ok_items items))
: Tot (vitems_br_t srt di) (decreases di)
= match di with
  | ID_NIL ->
    vitems_nil_equiv ();
    items_nil_equiv srt;
    br_ext _ _ _ _ _ _ () br_emp
  | ID_SINGLE dd ->
    vitems_single_equiv dd;
    items_single_equiv srt dd;
    br_ext _ _ _ _ _ _ () (brd_d dd ())
  | ID_CONS dd dtl ->
    vitems_cons_equiv dd dtl;
    items_cons_equiv srt dd dtl;
    br_ext _ _ _ _ _ _ () (br_join srt (brd_d dd ()) (brd_i srt dtl ()))
#pop-options

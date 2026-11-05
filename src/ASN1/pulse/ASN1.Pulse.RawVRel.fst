module ASN1.Pulse.RawVRel
#lang-pulse

(* The value-level relation `raw_varel d pm x y` between a Pulse value
   `x: t` described by an impl descriptor `d: adesc k t`
   (`ASN1.Pulse.Rel`, with named structs and case types) and a raw value
   `y: ASN1.Spec.Raw.asn1_raw_t k`, i.e. a value without value conditions
   (no restrictions, no DEFAULT normalization, no sorting).

   It mirrors `ASN1.Pulse.Rel.arel` (the relation of parsers, on typed
   values `asn1_t k`) and `ASN1.Pulse.RawValueRel.asn1_raw_rel` (the same
   relation on the legacy descriptor `legacy_adesc k`). Writers use it as
   their precondition: a user relates the Pulse value they built to a raw
   value, and never needs to reason about bytes.
   `ASN1.Pulse.RawVBridge` relates it to the byte-level relation
   `ASN1.Pulse.RawRel.raw_arel d`. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Spec.Raw
open ASN1.Spec.Raw.Props
open ASN1.Pulse.RawValueRel

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module It = LowParse.PulseParse.Iterator
module T = FStar.Tactics

let rec raw_varel (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: t) (y: asn1_raw_t k) : Tot slprop (decreases d) =
  match d with
  | D_ILC _ cd -> raw_vcrel cd pm x y
  | D_CHOICE _ _ ld -> raw_vlcrel ld pm x y
  | D_ANY -> prel_slice_ser asn1_value_enc pm x y
  | D_VIEW d' _ view _ _ -> raw_varel d' pm (view x) y

and raw_vcrel (#k: asn1_content_k) (#t: Type0) (d: cdesc k t) (pm: perm) (x: t) (y: asn1_raw_content_t k) : Tot slprop (decreases d) =
  match d with
  | CD_TERMINAL k' -> asn1_raw_terminal_rel k' pm x y
  | CD_RESTRICTED k' _ -> asn1_raw_terminal_rel k' pm x y
  | CD_SEQUENCE _ di -> raw_virel di pm x y
  | CD_SET _ _ _ di -> raw_virel di pm x y
  | CD_SEQUENCE_OF _ #_ #k' d' -> It.mixed_list_match (raw_varel d') ml_ops #asn1_strong_parser_kind (parse_raw k') pm x y
  | CD_SET_OF _ #_ #k' d' -> It.mixed_list_match (raw_varel d') ml_ops #asn1_strong_parser_kind (parse_raw k') pm x y
  | CD_PREFIXED d' -> raw_varel d' pm x y
  | CD_ADB_NONE _ _ _ key_k ls _ _ dsx dpre ->
    raw_viarel dpre #(rady key_k ls) (raw_vsxrel dsx) pm x y
  | CD_ADB_SOME _ _ _ key_k ls fb _ _ #tfb dfb dfx dpre ->
    raw_viarel dpre #(rady_fb key_k ls fb)
      (raw_vfxrel dfx (raw_items_t (dsnd fb))
        (fun pm (z: asn1_terminal_impl_t key_k & tfb) key (v: raw_items_t (dsnd fb)) ->
          asn1_raw_terminal_rel key_k pm (fst z) key ** raw_virel dfb pm (snd z) v))
      pm x y
  | CD_VIEW d' _ view _ _ -> raw_vcrel d' pm (view x) y

and raw_vsxrel (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (d: sxdesc key_k ls t)
  (pm: perm) (x: t) (y: rady key_k ls)
: Tot slprop (decreases d)
= match d with
  | SX_NIL _ -> pure False
  | SX_SINGLE _ key' it di ->
    let (| key, v |) = y in
    if key = raw_key_of_lit key_k key'
    then raw_virel di pm x v
    else pure False
  | SX_CONS _ key' it #t1 di #_ #_ #t2 dtl ->
    let (| key, v |) = y in
    let x' : either t1 t2 = x in
    begin match x' with
    | Inl a -> if key = raw_key_of_lit key_k key' then raw_virel di pm a v else pure False
    | Inr b -> if key = raw_key_of_lit key_k key' then pure False else raw_vsxrel dtl pm b (| key, v |)
    end

and raw_vfxrel (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t: Type0) (d: fxdesc key_k ls fbt t)
  (fbs: Type) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> fbs -> slprop)
  (pm: perm) (x: t) (y: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) fbs)
: Tot slprop (decreases d)
= match d with
  | FX_NIL _ ->
    let (| key, v |) = y in
    fbr pm x key v
  | FX_SINGLE _ key' it #t1 di ->
    let (| key, v |) = y in
    let x' : either t1 fbt = x in
    begin match x' with
    | Inl a -> if key = raw_key_of_lit key_k key' then raw_virel di pm a v else pure False
    | Inr b -> if key = raw_key_of_lit key_k key' then pure False else fbr pm b key v
    end
  | FX_CONS _ key' it #t1 di #_ #_ #_ #t2 dtl ->
    let (| key, v |) = y in
    let x' : either t1 t2 = x in
    begin match x' with
    | Inl a -> if key = raw_key_of_lit key_k key' then raw_virel di pm a v else pure False
    | Inr b -> if key = raw_key_of_lit key_k key' then pure False else raw_vfxrel dtl fbs fbr pm b (| key, v |)
    end

and raw_vlcrel (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (d: lcdesc lc t) (pm: perm) (x: t) (y: make_gen_choice_type (raw_lc_t lc)) : Tot slprop (decreases d) =
  match d with
  | LC_NIL -> pure False
  | LC_SINGLE id' cd ->
    let (| id, v |) = y in
    if id = id'
    then raw_vcrel cd pm x v
    else pure False
  | LC_CONS id' #_ #t1 cd #_ #_ #t2 dtl ->
    let (| id, v |) = y in
    let x' : either t1 t2 = x in
    begin match x' with
    | Inl a -> if id = id' then raw_vcrel cd pm a v else pure False
    | Inr b -> if id = id' then pure False else raw_vlcrel dtl pm b (| id, v |)
    end

and raw_vdrel (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t) (pm: perm) (x: t) (y: raw_dec_t dk) : Tot slprop (decreases d) =
  match d with
  | DD_PLAIN d' -> raw_varel d' pm x y
  | DD_OPTION #_ #k' #t' d' ->
    let x' : option t' = x in
    let y' : option (asn1_raw_t k') = y in
    begin match x', y' with
    | None, None -> emp
    | Some a, Some b -> raw_varel d' pm a b
    | _ -> pure False
    end
  | DD_DEFAULT _ #k' _ ->
    let x' : option (asn1_terminal_impl_t k') = x in
    let y' : option (asn1_raw_terminal_t k') = y in
    begin match x', y' with
    | None, None -> emp
    | Some a, Some b -> asn1_raw_terminal_rel k' pm a b
    | _ -> pure False
    end
  | DD_DEFAULT_RESTRICTED _ #k' _ _ ->
    let x' : option (asn1_terminal_impl_t k') = x in
    let y' : option (asn1_raw_terminal_t k') = y in
    begin match x', y' with
    | None, None -> emp
    | Some a, Some b -> asn1_raw_terminal_rel k' pm a b
    | _ -> pure False
    end
  | DD_VIEW d' _ view _ _ -> raw_vdrel d' pm (view x) y

and raw_virel (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (d: idesc ls t) (pm: perm) (x: t) (y: raw_items_t ls) : Tot slprop (decreases d) =
  match d with
  | ID_NIL -> emp
  | ID_SINGLE dd -> raw_vdrel dd pm x y
  | ID_CONS #_ #_ #dk #t1 dd #s2 #d2 #dk2 #ids2 #tl2 #t2 dtl ->
    let x' : t1 & t2 = x in
    let y' : raw_dec_t dk & raw_items_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) = y in
    raw_vdrel dd pm (fst x') (fst y') ** raw_virel dtl pm (snd x') (snd y')

and raw_viarel (#ids: _) (#ls: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (d: iadesc ls sfxi t) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (pm: perm) (x: t) (y: raw_items_any_t ls sfxs) : Tot slprop (decreases d) =
  match d with
  | IA_NIL -> sfxr pm x y
  | IA_SINGLE #_ #_ #dk #t1 dd ->
    let x' : t1 & sfxi = x in
    let y' : raw_dec_t dk & sfxs = y in
    raw_vdrel dd pm (fst x') (fst y') ** sfxr pm (snd x') (snd y')
  | IA_CONS #_ #_ #dk #t1 dd #s2 #d2 #dk2 #ids2 #tl2 #_ #t2 dtl ->
    let x' : t1 & t2 = x in
    let y' : raw_dec_t dk & raw_items_any_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs = y in
    raw_vdrel dd pm (fst x') (fst y') ** raw_viarel dtl sfxr pm (snd x') (snd y')

(* The fallback of an ANY DEFINED BY: the key, then the payload *)

let raw_vfbr (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
: perm -> (asn1_terminal_impl_t key_k & tfb) -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd gfb) -> slprop
= fun pm (z: asn1_terminal_impl_t key_k & tfb) key (v: raw_items_t (dsnd gfb)) ->
    asn1_raw_terminal_rel key_k pm (fst z) key ** raw_virel dfb pm (snd z) v

(* Equations, so that proofs need not unfold the relation of a whole
   descriptor *)

let solve_vequiv () : T.Tac unit =
  T.norm [delta_only [`%pequiv]];
  let _ = T.forall_intros () in
  T.norm [delta_only [`%raw_varel; `%raw_vcrel; `%raw_vsxrel; `%raw_vfxrel; `%raw_vlcrel; `%raw_vdrel; `%raw_virel; `%raw_viarel; `%raw_vfbr; `%prel_pair; `%prel_option; `%rady; `%rady_fb]; zeta; iota];
  T.trefl ()

let vrel_ilc_equiv (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t)
: Lemma (pequiv #t #(asn1_raw_content_t k) (raw_vcrel cd) (raw_varel (D_ILC id cd)))
= assert (pequiv #t #(asn1_raw_content_t k) (raw_vcrel cd) (raw_varel (D_ILC id cd))) by (solve_vequiv ())

let vrel_choice_equiv (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (#t: Type0) (ld: lcdesc lc t)
: Lemma (pequiv #t #(make_gen_choice_type (raw_lc_t lc)) (raw_vlcrel ld) (raw_varel (D_CHOICE lc pf ld)))
= assert (pequiv #t #(make_gen_choice_type (raw_lc_t lc)) (raw_vlcrel ld) (raw_varel (D_CHOICE lc pf ld))) by (solve_vequiv ())

let vrel_any_equiv (_: unit)
: Lemma (pequiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (raw_varel D_ANY))
= assert (pequiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (raw_varel D_ANY)) by (solve_vequiv ())

let vview (#t #ty #u: Type0) (r: prel t u) (view: ty -> t) (pm: perm) (x: ty) (y: u) : slprop =
  r pm (view x) y

let vrel_view_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
: Lemma (pequiv #ty #(asn1_raw_t k) (vview (raw_varel d) view) (raw_varel (D_VIEW d ty view mk law)))
= assert (pequiv #ty #(asn1_raw_t k) (vview (raw_varel d) view) (raw_varel (D_VIEW d ty view mk law))) by (T.norm [delta_only [`%vview]]; solve_vequiv ())

let vcontent_terminal_equiv (k: asn1_terminal_k)
: Lemma (pequiv #(asn1_terminal_impl_t k) #(asn1_raw_terminal_t k) (asn1_raw_terminal_rel k) (raw_vcrel (CD_TERMINAL k)))
= assert (pequiv #(asn1_terminal_impl_t k) #(asn1_raw_terminal_t k) (asn1_raw_terminal_rel k) (raw_vcrel (CD_TERMINAL k))) by (solve_vequiv ())

let vcontent_restricted_equiv (k: asn1_terminal_k) (r: asn1_restriction k)
: Lemma (pequiv #(asn1_terminal_impl_t k) #(asn1_raw_terminal_t k) (asn1_raw_terminal_rel k) (raw_vcrel (CD_RESTRICTED k r)))
= assert (pequiv #(asn1_terminal_impl_t k) #(asn1_raw_terminal_t k) (asn1_raw_terminal_rel k) (raw_vcrel (CD_RESTRICTED k r))) by (solve_vequiv ())

let vcontent_prefixed_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (pequiv #t #(asn1_raw_t k) (raw_varel d) (raw_vcrel (CD_PREFIXED d)))
= assert (pequiv #t #(asn1_raw_t k) (raw_varel d) (raw_vcrel (CD_PREFIXED d))) by (solve_vequiv ())

let vcontent_sequence_equiv (gitems: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd gitems) t)
: Lemma (pequiv #t #(raw_items_t (dsnd gitems)) (raw_virel di) (raw_vcrel (CD_SEQUENCE gitems di)))
= assert (pequiv #t #(raw_items_t (dsnd gitems)) (raw_virel di) (raw_vcrel (CD_SEQUENCE gitems di))) by (solve_vequiv ())

let vcontent_set_equiv (ids: _) (items: asn1_gen_items_l ids) (pf: _) (#t: Type0) (di: idesc items t)
: Lemma (pequiv #t #(raw_items_t items) (raw_virel di) (raw_vcrel (CD_SET ids items pf di)))
= assert (pequiv #t #(raw_items_t items) (raw_virel di) (raw_vcrel (CD_SET ids items pf di))) by (solve_vequiv ())

let vml_rel (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : prel (ml t) (list (asn1_raw_t k)) =
  It.mixed_list_match (raw_varel d) ml_ops #asn1_strong_parser_kind (parse_raw k)

let vcontent_seq_of_equiv (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (pequiv #(ml t) #(list (asn1_raw_t k)) (vml_rel d) (raw_vcrel (CD_SEQUENCE_OF ne d)))
= assert (pequiv #(ml t) #(list (asn1_raw_t k)) (vml_rel d) (raw_vcrel (CD_SEQUENCE_OF ne d))) by (T.norm [delta_only [`%vml_rel]]; solve_vequiv ())

let vcontent_set_of_equiv (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (pequiv #(ml t) #(list (asn1_raw_t k)) (vml_rel d) (raw_vcrel (CD_SET_OF ne d)))
= assert (pequiv #(ml t) #(list (asn1_raw_t k)) (vml_rel d) (raw_vcrel (CD_SET_OF ne d))) by (T.norm [delta_only [`%vml_rel]]; solve_vequiv ())

let vcontent_adb_none_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#ts: Type0) (dsx: sxdesc key_k ls ts) (#t: Type0) (dpre: iadesc prefix ts t)
: Lemma (pequiv #t #(raw_items_any_t prefix (rady key_k ls)) (raw_viarel dpre #(rady key_k ls) (raw_vsxrel dsx)) (raw_vcrel (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre)))
= assert (pequiv #t #(raw_items_any_t prefix (rady key_k ls)) (raw_viarel dpre #(rady key_k ls) (raw_vsxrel dsx)) (raw_vcrel (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre))) by (solve_vequiv ())

let vcontent_adb_some_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#tfb: Type0) (dfb: idesc (dsnd fb) tfb)
  (#ts: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts) (#t: Type0) (dpre: iadesc prefix ts t)
: Lemma (pequiv #t #(raw_items_any_t prefix (rady_fb key_k ls fb))
    (raw_viarel dpre #(rady_fb key_k ls fb) (raw_vfxrel dfx (raw_items_t (dsnd fb)) (raw_vfbr key_k #fb dfb)))
    (raw_vcrel (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre)))
= assert (pequiv #t #(raw_items_any_t prefix (rady_fb key_k ls fb))
    (raw_viarel dpre #(rady_fb key_k ls fb) (raw_vfxrel dfx (raw_items_t (dsnd fb)) (raw_vfbr key_k #fb dfb)))
    (raw_vcrel (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre))) by (solve_vequiv ())

let vcontent_view_equiv (#k: asn1_content_k) (#t: Type0) (d: cdesc k t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
: Lemma (pequiv #ty #(asn1_raw_content_t k) (vview (raw_vcrel d) view) (raw_vcrel (CD_VIEW d ty view mk law)))
= assert (pequiv #ty #(asn1_raw_content_t k) (vview (raw_vcrel d) view) (raw_vcrel (CD_VIEW d ty view mk law))) by (T.norm [delta_only [`%vview]]; solve_vequiv ())

let vdec_plain_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (pequiv #t #(asn1_raw_t k) (raw_varel d) (raw_vdrel (DD_PLAIN d)))
= assert (pequiv #t #(asn1_raw_t k) (raw_varel d) (raw_vdrel (DD_PLAIN d))) by (solve_vequiv ())

let vdec_option_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (pequiv #(option t) #(option (asn1_raw_t k)) (prel_option (raw_varel d)) (raw_vdrel (DD_OPTION d)))
= assert (pequiv #(option t) #(option (asn1_raw_t k)) (prel_option (raw_varel d)) (raw_vdrel (DD_OPTION d))) by (solve_vequiv ())

let vdec_default_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k)
: Lemma (pequiv #(option (asn1_terminal_impl_t k)) #(option (asn1_raw_terminal_t k)) (prel_option (asn1_raw_terminal_rel k)) (raw_vdrel (DD_DEFAULT id0 #k defv)))
= assert (pequiv #(option (asn1_terminal_impl_t k)) #(option (asn1_raw_terminal_t k)) (prel_option (asn1_raw_terminal_rel k)) (raw_vdrel (DD_DEFAULT id0 #k defv))) by (solve_vequiv ())

let vdec_default_restricted_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) })
: Lemma (pequiv #(option (asn1_terminal_impl_t k)) #(option (asn1_raw_terminal_t k)) (prel_option (asn1_raw_terminal_rel k)) (raw_vdrel (DD_DEFAULT_RESTRICTED id0 #k r defv)))
= assert (pequiv #(option (asn1_terminal_impl_t k)) #(option (asn1_raw_terminal_t k)) (prel_option (asn1_raw_terminal_rel k)) (raw_vdrel (DD_DEFAULT_RESTRICTED id0 #k r defv))) by (solve_vequiv ())

let vdec_view_equiv (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
: Lemma (pequiv #ty #(raw_dec_t dk) (vview (raw_vdrel d) view) (raw_vdrel (DD_VIEW d ty view mk law)))
= assert (pequiv #ty #(raw_dec_t dk) (vview (raw_vdrel d) view) (raw_vdrel (DD_VIEW d ty view mk law))) by (T.norm [delta_only [`%vview]]; solve_vequiv ())

let vitems_nil_equiv (_: unit)
: Lemma (pequiv #unit #unit (prel_emp unit unit) (raw_virel ID_NIL))
= assert (pequiv #unit #unit (prel_emp unit unit) (raw_virel ID_NIL)) by (T.norm [delta_only [`%prel_emp]]; solve_vequiv ())

let vitems_single_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t)
: Lemma (pequiv #t #(raw_dec_t dk) (raw_vdrel dd) (raw_virel (ID_SINGLE dd)))
= assert (pequiv #t #(raw_dec_t dk) (raw_vdrel dd) (raw_virel (ID_SINGLE dd))) by (solve_vequiv ())

let vitems_cons_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#s2: _) (#d2: _) (#dk2: asn1_decorated_k s2 d2) (#ids2: _) (#tl2: asn1_gen_items_l ids2) (#t2: Type0)
  (dtl: idesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) t2)
: Lemma (pequiv #(t1 & t2) #(raw_dec_t dk & raw_items_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (prel_pair (raw_vdrel dd) (raw_virel dtl)) (raw_virel (ID_CONS dd dtl)))
= assert (pequiv #(t1 & t2) #(raw_dec_t dk & raw_items_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (prel_pair (raw_vdrel dd) (raw_virel dtl)) (raw_virel (ID_CONS dd dtl))) by (solve_vequiv ())

let vitems_any_nil_equiv (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (pequiv #sfxi #sfxs sfxr (raw_viarel (IA_NIL #sfxi) sfxr))
= assert (pequiv #sfxi #sfxs sfxr (raw_viarel (IA_NIL #sfxi) sfxr)) by (solve_vequiv ())

let vitems_any_single_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (pequiv #(t & sfxi) #(raw_dec_t dk & sfxs) (prel_pair (raw_vdrel dd) sfxr) (raw_viarel (IA_SINGLE dd #sfxi) sfxr))
= assert (pequiv #(t & sfxi) #(raw_dec_t dk & sfxs) (prel_pair (raw_vdrel dd) sfxr) (raw_viarel (IA_SINGLE dd #sfxi) sfxr)) by (solve_vequiv ())

let vitems_any_cons_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#s2: _) (#d2: _) (#dk2: asn1_decorated_k s2 d2) (#ids2: _) (#tl2: asn1_gen_items_l ids2) (#sfxi: Type0) (#t2: Type0)
  (dtl: iadesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi t2) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (pequiv #(t1 & t2) #(raw_dec_t dk & raw_items_any_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs) (prel_pair (raw_vdrel dd) (raw_viarel dtl sfxr)) (raw_viarel (IA_CONS dd dtl) sfxr))
= assert (pequiv #(t1 & t2) #(raw_dec_t dk & raw_items_any_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs) (prel_pair (raw_vdrel dd) (raw_viarel dtl sfxr)) (raw_viarel (IA_CONS dd dtl) sfxr)) by (solve_vequiv ())

(* CHOICE alternatives *)

let vlc_nil_eq (pm: perm) (x: unit) (y: make_gen_choice_type (raw_lc_t []))
: Lemma (raw_vlcrel LC_NIL pm x y == pure False)
= assert_norm (raw_vlcrel LC_NIL pm x y == pure False)

let vlc_single_eq (id': asn1_id_t) (#c: asn1_content_k) (#t: Type0) (cd: cdesc c t) (pm: perm) (x: t)
  (v: make_gen_choice_type (raw_lc_t [(id', c)]))
: Lemma (raw_vlcrel (LC_SINGLE id' cd) pm x v == (if dfst v = id' then raw_vcrel cd pm x (raw_lc_head_val id' c [] v ()) else pure False))
= assert_norm (raw_vlcrel (LC_SINGLE id' cd) pm x v == (let (| id, v |) = v in if id = id' then raw_vcrel cd pm x v else pure False))

let vlc_cons_inl_aux (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pm: perm) (a: t1) (id: asn1_id_t) (w: idlookup_t id (raw_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (raw_vlcrel (LC_CONS id' cd dtl) pm (Inl #t1 #t2 a) ((| id, w |) <: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2))) ==
    (if id = id' then raw_vcrel cd pm a (raw_lc_head_val id' c (hd2 :: tl2) ((| id, w |) <: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2))) ()) else pure False))
= assert (raw_vlcrel (LC_CONS id' cd dtl) pm (Inl #t1 #t2 a) ((| id, w |) <: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2))) ==
    (if id = id' then raw_vcrel cd pm a (raw_lc_head_val id' c (hd2 :: tl2) ((| id, w |) <: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2))) ()) else pure False))
  by (T.norm [delta_only [`%raw_vlcrel; `%raw_lc_head_val]; zeta; iota]; T.trefl ())

let vlc_cons_inl_eq (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pm: perm) (a: t1) (v: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (raw_vlcrel (LC_CONS id' cd dtl) pm (Inl #t1 #t2 a) v ==
    (if dfst v = id' then raw_vcrel cd pm a (raw_lc_head_val id' c (hd2 :: tl2) v ()) else pure False))
= let (| id, w |) = v in
  vlc_cons_inl_aux id' cd dtl pm a id w

let vlc_cons_inr_aux (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pm: perm) (b: t2) (id: asn1_id_t) (w: idlookup_t id (raw_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (raw_vlcrel (LC_CONS id' cd dtl) pm (Inr #t1 #t2 b) ((| id, w |) <: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2))) ==
    (if id = id' then pure False else raw_vlcrel dtl pm b (raw_lc_tail_val (id', c) (hd2 :: tl2) ((| id, w |) <: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2))) ())))
= assert (raw_vlcrel (LC_CONS id' cd dtl) pm (Inr #t1 #t2 b) ((| id, w |) <: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2))) ==
    (if id = id' then pure False else raw_vlcrel dtl pm b (raw_lc_tail_val (id', c) (hd2 :: tl2) ((| id, w |) <: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2))) ())))
  by (T.norm [delta_only [`%raw_vlcrel; `%raw_lc_tail_val]; zeta; iota]; T.trefl ())

let vlc_cons_inr_eq (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pm: perm) (b: t2) (v: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (raw_vlcrel (LC_CONS id' cd dtl) pm (Inr #t1 #t2 b) v ==
    (if dfst v = id' then pure False else raw_vlcrel dtl pm b (raw_lc_tail_val (id', c) (hd2 :: tl2) v ())))
= let (| id, w |) = v in
  vlc_cons_inr_aux id' cd dtl pm b id w

(* ANY DEFINED BY, without a fallback *)

let vadb_nil_eq (#key_k: asn1_terminal_k) (pm: perm) (x: unit) (y: rady key_k [])
: Lemma (raw_vsxrel (SX_NIL key_k) pm x y == pure False)
= assert_norm (raw_vsxrel (SX_NIL key_k) pm x y == pure False)

let vadb_single_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t) (pm: perm)
  (r: t) (key: asn1_raw_terminal_t key_k) (w: idlookup_t key (raw_any_t_core key_k [(kx, y)]))
: Lemma (raw_vsxrel (SX_SINGLE key_k kx y di) pm r ((| key, w |) <: rady key_k [(kx, y)]) ==
    (if key = raw_key_of_lit key_k kx then raw_virel di pm r (rady_head_val kx y [] ((| key, w |) <: rady key_k [(kx, y)]) ()) else pure False))
= assert (raw_vsxrel (SX_SINGLE key_k kx y di) pm r ((| key, w |) <: rady key_k [(kx, y)]) ==
    (if key = raw_key_of_lit key_k kx then raw_virel di pm r (rady_head_val kx y [] ((| key, w |) <: rady key_k [(kx, y)]) ()) else pure False))
  by (T.norm [delta_only [`%raw_vsxrel; `%rady_head_val; `%rady]; zeta; iota]; T.trefl ())

let vadb_single_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t) (pm: perm)
  (r: t) (v: rady key_k [(kx, y)])
: Lemma (raw_vsxrel (SX_SINGLE key_k kx y di) pm r v ==
    (if dfst v = raw_key_of_lit key_k kx then raw_virel di pm r (rady_head_val kx y [] v ()) else pure False))
= let (| key, w |) = v in
  vadb_single_aux kx y di pm r key w

let vadb_cons_inl_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (a: t1) (key: asn1_raw_terminal_t key_k) (w: idlookup_t key (raw_any_t_core key_k ((kx, y) :: hd2 :: tl2)))
: Lemma (raw_vsxrel (SX_CONS key_k kx y di dtl) pm (Inl #t1 #t2 a) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = raw_key_of_lit key_k kx then raw_virel di pm a (rady_head_val kx y (hd2 :: tl2) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ()) else pure False))
= assert (raw_vsxrel (SX_CONS key_k kx y di dtl) pm (Inl #t1 #t2 a) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = raw_key_of_lit key_k kx then raw_virel di pm a (rady_head_val kx y (hd2 :: tl2) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ()) else pure False))
  by (T.norm [delta_only [`%raw_vsxrel; `%rady_head_val; `%rady]; zeta; iota]; T.trefl ())

let vadb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (a: t1) (v: rady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (raw_vsxrel (SX_CONS key_k kx y di dtl) pm (Inl #t1 #t2 a) v ==
    (if dfst v = raw_key_of_lit key_k kx then raw_virel di pm a (rady_head_val kx y (hd2 :: tl2) v ()) else pure False))
= let (| key, w |) = v in
  vadb_cons_inl_aux kx y di dtl pm a key w

let vadb_cons_inr_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (b: t2) (key: asn1_raw_terminal_t key_k) (w: idlookup_t key (raw_any_t_core key_k ((kx, y) :: hd2 :: tl2)))
: Lemma (raw_vsxrel (SX_CONS key_k kx y di dtl) pm (Inr #t1 #t2 b) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_vsxrel dtl pm b (rady_tail_val kx y (hd2 :: tl2) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ())))
= assert (raw_vsxrel (SX_CONS key_k kx y di dtl) pm (Inr #t1 #t2 b) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_vsxrel dtl pm b (rady_tail_val kx y (hd2 :: tl2) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ())))
  by (T.norm [delta_only [`%raw_vsxrel; `%rady_tail_val; `%rady]; zeta; iota]; T.trefl ())

let vadb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (b: t2) (v: rady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (raw_vsxrel (SX_CONS key_k kx y di dtl) pm (Inr #t1 #t2 b) v ==
    (if dfst v = raw_key_of_lit key_k kx then pure False else raw_vsxrel dtl pm b (rady_tail_val kx y (hd2 :: tl2) v ())))
= let (| key, w |) = v in
  vadb_cons_inr_aux kx y di dtl pm b key w

(* ANY DEFINED BY, with a fallback *)

let vafb_nil_aux (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb) (pm: perm) (z: asn1_terminal_impl_t key_k & tfb)
  (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k []) (raw_items_t (dsnd gfb)))
: Lemma (raw_vfxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb) pm z ((| key, w |) <: rady_fb key_k [] gfb) ==
    prel_pair (asn1_raw_terminal_rel key_k) (raw_virel dfb) pm z (key, rady_fb_nil_val gfb ((| key, w |) <: rady_fb key_k [] gfb)))
= assert (raw_vfxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb) pm z ((| key, w |) <: rady_fb key_k [] gfb) ==
    prel_pair (asn1_raw_terminal_rel key_k) (raw_virel dfb) pm z (key, rady_fb_nil_val gfb ((| key, w |) <: rady_fb key_k [] gfb)))
  by (T.norm [delta_only [`%raw_vfxrel; `%raw_vfbr; `%prel_pair; `%rady_fb_nil_val; `%rady_fb]; zeta; iota]; T.trefl ())

let vafb_nil_eq (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb) (pm: perm) (z: asn1_terminal_impl_t key_k & tfb)
  (v: rady_fb key_k [] gfb)
: Lemma (raw_vfxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb) pm z v ==
    prel_pair (asn1_raw_terminal_rel key_k) (raw_virel dfb) pm z (dfst v, rady_fb_nil_val gfb v))
= let (| key, w |) = v in
  vafb_nil_aux key_k dfb pm z key w

let vafb_single_inl_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#fbt: Type0) (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd gfb) -> slprop) (pm: perm)
  (a: t1) (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k [(kx, y)]) (raw_items_t (dsnd gfb)))
: Lemma (raw_vfxrel (FX_SINGLE key_k kx y di #fbt) (raw_items_t (dsnd gfb)) fbr pm (Inl #t1 #fbt a) ((| key, w |) <: rady_fb key_k [(kx, y)] gfb) ==
    (if key = raw_key_of_lit key_k kx then raw_virel di pm a (rady_fb_head_val kx y [] gfb ((| key, w |) <: rady_fb key_k [(kx, y)] gfb) ()) else pure False))
= assert (raw_vfxrel (FX_SINGLE key_k kx y di #fbt) (raw_items_t (dsnd gfb)) fbr pm (Inl #t1 #fbt a) ((| key, w |) <: rady_fb key_k [(kx, y)] gfb) ==
    (if key = raw_key_of_lit key_k kx then raw_virel di pm a (rady_fb_head_val kx y [] gfb ((| key, w |) <: rady_fb key_k [(kx, y)] gfb) ()) else pure False))
  by (T.norm [delta_only [`%raw_vfxrel; `%rady_fb_head_val; `%rady_fb]; zeta; iota]; T.trefl ())

let vafb_single_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#fbt: Type0) (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd gfb) -> slprop) (pm: perm)
  (a: t1) (v: rady_fb key_k [(kx, y)] gfb)
: Lemma (raw_vfxrel (FX_SINGLE key_k kx y di #fbt) (raw_items_t (dsnd gfb)) fbr pm (Inl #t1 #fbt a) v ==
    (if dfst v = raw_key_of_lit key_k kx then raw_virel di pm a (rady_fb_head_val kx y [] gfb v ()) else pure False))
= let (| key, w |) = v in
  vafb_single_inl_aux kx y di gfb fbr pm a key w

let vafb_single_inr_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#fbt: Type0) (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd gfb) -> slprop) (pm: perm)
  (b: fbt) (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k [(kx, y)]) (raw_items_t (dsnd gfb)))
: Lemma (raw_vfxrel (FX_SINGLE key_k kx y di #fbt) (raw_items_t (dsnd gfb)) fbr pm (Inr #t1 #fbt b) ((| key, w |) <: rady_fb key_k [(kx, y)] gfb) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_vfxrel (FX_NIL key_k #fbt) (raw_items_t (dsnd gfb)) fbr pm b (rady_fb_tail_val kx y [] gfb ((| key, w |) <: rady_fb key_k [(kx, y)] gfb) ())))
= assert (raw_vfxrel (FX_SINGLE key_k kx y di #fbt) (raw_items_t (dsnd gfb)) fbr pm (Inr #t1 #fbt b) ((| key, w |) <: rady_fb key_k [(kx, y)] gfb) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_vfxrel (FX_NIL key_k #fbt) (raw_items_t (dsnd gfb)) fbr pm b (rady_fb_tail_val kx y [] gfb ((| key, w |) <: rady_fb key_k [(kx, y)] gfb) ())))
  by (T.norm [delta_only [`%raw_vfxrel; `%rady_fb_tail_val; `%rady_fb]; zeta; iota]; T.trefl ())

let vafb_single_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#fbt: Type0) (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd gfb) -> slprop) (pm: perm)
  (b: fbt) (v: rady_fb key_k [(kx, y)] gfb)
: Lemma (raw_vfxrel (FX_SINGLE key_k kx y di #fbt) (raw_items_t (dsnd gfb)) fbr pm (Inr #t1 #fbt b) v ==
    (if dfst v = raw_key_of_lit key_k kx then pure False else raw_vfxrel (FX_NIL key_k #fbt) (raw_items_t (dsnd gfb)) fbr pm b (rady_fb_tail_val kx y [] gfb v ())))
= let (| key, w |) = v in
  vafb_single_inr_aux kx y di gfb fbr pm b key w

let vafb_cons_inl_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) fbt t2)
  (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd gfb) -> slprop) (pm: perm)
  (a: t1) (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k ((kx, y) :: hd2 :: tl2)) (raw_items_t (dsnd gfb)))
: Lemma (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) fbr pm (Inl #t1 #t2 a) ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ==
    (if key = raw_key_of_lit key_k kx then raw_virel di pm a (rady_fb_head_val kx y (hd2 :: tl2) gfb ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ()) else pure False))
= assert (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) fbr pm (Inl #t1 #t2 a) ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ==
    (if key = raw_key_of_lit key_k kx then raw_virel di pm a (rady_fb_head_val kx y (hd2 :: tl2) gfb ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ()) else pure False))
  by (T.norm [delta_only [`%raw_vfxrel; `%rady_fb_head_val; `%rady_fb]; zeta; iota]; T.trefl ())

let vafb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) fbt t2)
  (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd gfb) -> slprop) (pm: perm)
  (a: t1) (v: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb)
: Lemma (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) fbr pm (Inl #t1 #t2 a) v ==
    (if dfst v = raw_key_of_lit key_k kx then raw_virel di pm a (rady_fb_head_val kx y (hd2 :: tl2) gfb v ()) else pure False))
= let (| key, w |) = v in
  vafb_cons_inl_aux kx y di dtl gfb fbr pm a key w

let vafb_cons_inr_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) fbt t2)
  (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd gfb) -> slprop) (pm: perm)
  (b: t2) (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k ((kx, y) :: hd2 :: tl2)) (raw_items_t (dsnd gfb)))
: Lemma (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) fbr pm (Inr #t1 #t2 b) ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_vfxrel dtl (raw_items_t (dsnd gfb)) fbr pm b (rady_fb_tail_val kx y (hd2 :: tl2) gfb ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ())))
= assert (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) fbr pm (Inr #t1 #t2 b) ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_vfxrel dtl (raw_items_t (dsnd gfb)) fbr pm b (rady_fb_tail_val kx y (hd2 :: tl2) gfb ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ())))
  by (T.norm [delta_only [`%raw_vfxrel; `%rady_fb_tail_val; `%rady_fb]; zeta; iota]; T.trefl ())

let vafb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) fbt t2)
  (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd gfb) -> slprop) (pm: perm)
  (b: t2) (v: rady_fb key_k ((kx, y) :: hd2 :: tl2) gfb)
: Lemma (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) fbr pm (Inr #t1 #t2 b) v ==
    (if dfst v = raw_key_of_lit key_k kx then pure False else raw_vfxrel dtl (raw_items_t (dsnd gfb)) fbr pm b (rady_fb_tail_val kx y (hd2 :: tl2) gfb v ())))
= let (| key, w |) = v in
  vafb_cons_inr_aux kx y di dtl gfb fbr pm b key w

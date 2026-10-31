module ASN1.Pulse.Writer
#lang-pulse

(* The right-to-left writer interpreter: from a well-formed schema value `k`
   supported by the writers (SET fields in canonical order, ANY DEFINED BY
   keys of supported kinds), a writer from `asn1_rel k pm` to the generic DER encoding of the
   value, `asn1_value_enc (to_value k x)`. Combined with
   `ASN1.Spec.Serializer.asn1_ser_eq`, this is the DER encoding of `x`. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc
open ASN1.Spec.ToValue
open ASN1.Pulse.Rel
open ASN1.Pulse.WriteComb

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module SB = LowParse.Spec.Base
module W = LowParse.Pulse.R2L
module Conf = ASN1.Spec.Conformance
module WL = ASN1.Pulse.WriteLeaf
module RS = ASN1.Pulse.RelShare
module WLm = ASN1.Pulse.Writer.Lemmas
module PS = ASN1.Pulse.ParseSequence
module PA = ASN1.Pulse.ParseAdb
module AL = ASN1.Pulse.ParseAdb.Lemmas
module In = ASN1.Pulse.Interpreter
module WA = ASN1.Pulse.WriteAdb

let rec write_content (id: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k: asn1_content_k) (u: squash (RS.wsupported_content k /\ Conf.wf_content id k)) (pm: perm)
  (x': asn1_content_impl_t k) (#x: Ghost.erased (asn1_content_t k))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (asn1_content_rel k pm) (WLm.cenc id k) x' x out pos v p)
  (decreases k)
= [@inline_let] let vf : W.r2l_writer_f #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_rel k pm) (WLm.cenc id k) =
  (match k with
  | ASN1_TERMINAL k' ->
    RS.content_terminal_equiv k';
    write_ext #(asn1_terminal_impl_t k') #(asn1_terminal_t k') (asn1_terminal_rel k') (asn1_content_rel (ASN1_TERMINAL k')) ()
      (WLm.cenc id (ASN1_TERMINAL k')) (fun x -> WLm.cenc_terminal id k' x) pm
      (fun x' #x out pos #v #p -> WL.r2l_write_terminal id k' () pm x' #x out pos #v #p)
  | ASN1_RESTRICTED_TERMINAL k' r ->
    write_restricted id k' r pm
      (fun x' #x out pos #v #p -> WL.r2l_write_terminal id k' () pm x' #x out pos #v #p)
  | ASN1_PREFIXED k' ->
    RS.content_prefixed_equiv k';
    write_ext #(asn1_impl_t k') #(asn1_t k') (asn1_rel k') (asn1_content_rel (ASN1_PREFIXED k')) ()
      (WLm.cenc id (ASN1_PREFIXED k')) (fun x -> WLm.cenc_prefixed id k' x) pm
      (WL.r2l_write_encap id () #_ #_ #(asn1_rel k' pm) #(to_value k')
        (fun x' #x out pos #v #p -> write_k k' () pm x' #x out pos #v #p))
  | ASN1_SEQUENCE gitems ->
    RS.content_sequence_equiv gitems;
    write_ext #(asn1_items_impl_t (dsnd gitems)) #(asn1_sequence_t_core (dsnd gitems)) (asn1_items_rel (dsnd gitems)) (asn1_content_rel (ASN1_SEQUENCE gitems)) ()
      (WLm.cenc id (ASN1_SEQUENCE gitems)) (fun x -> WLm.cenc_sequence id gitems x) pm
      (WL.r2l_write_tlv id (fun x' #x out pos #v #p -> write_items (dsnd gitems) () pm x' #x out pos #v #p))
  | ASN1_SET ids items pf ->
    RS.content_set_equiv ids items pf;
    write_ext #(asn1_items_impl_t items) #(asn1_sequence_t_core items) (asn1_items_rel items) (asn1_content_rel (ASN1_SET ids items pf)) ()
      (WLm.cenc id (ASN1_SET ids items pf)) (fun x -> WLm.cenc_set id ids items pf x) pm
      (WL.r2l_write_tlv id (fun x' #x out pos #v #p -> write_items items () pm x' #x out pos #v #p))
  | ASN1_SEQUENCE_OF ne k' ->
    write_seq_of id ne k' ()
      (fun pm x' #x out pos #v #p -> write_k k' () pm x' #x out pos #v #p)
      (RS.share_k k' ()) (RS.gather_k k' ()) pm
  | ASN1_SET_OF ne k' ->
    write_set_of id ne k' ()
      (fun pm x' #x out pos #v #p -> write_k k' () pm x' #x out pos #v #p)
      (RS.share_k k' ()) (RS.gather_k k' ()) pm
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None ->
      RS.adb_none_equiv ipd prefix kid key_k ls pf pf';
      write_ext #(asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls None)) #(asn1_sequence_any_t_core prefix (AL.ady key_k ls))
        (asn1_items_any_rel prefix (asn1_adb_rel key_k ls)) (asn1_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf')) ()
        (WLm.cenc id (PA.adb_k_none ipd prefix kid key_k ls pf pf')) (fun x -> WLm.cenc_adb_none id ipd prefix kid key_k ls pf pf' x) pm
        (WL.r2l_write_tlv id (fun x' #x out pos #v #p ->
          write_items_any prefix () (asn1_adb_rel key_k ls) (WLm.adb_sv kid key_k ls) pm
            (fun x' #x out pos #v #p -> write_adb kid key_k () ls () pm x' #x out pos #v #p)
            x' #x out pos #v #p))
    | Some fb ->
      RS.adb_some_equiv ipd prefix kid key_k ls fb pf pf';
      write_ext #(asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls (Some (PA.fbt key_k fb)))) #(asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb))
        (asn1_items_any_rel prefix (PA.afb_rel key_k ls fb)) (asn1_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf')) ()
        (WLm.cenc id (PA.adb_k_some ipd prefix kid key_k ls fb pf pf')) (fun x -> WLm.cenc_adb_some id ipd prefix kid key_k ls fb pf pf' x) pm
        (WL.r2l_write_tlv id (fun x' #x out pos #v #p ->
          write_items_any prefix () (PA.afb_rel key_k ls fb) (WLm.adb_fb_sv kid key_k ls fb) pm
            (fun x' #x out pos #v #p -> write_afb kid key_k () ls () fb pm
              (fun x' #x out pos #v #p -> write_items (dsnd fb) () pm x' #x out pos #v #p)
              x' #x out pos #v #p)
            x' #x out pos #v #p))
    end)
  in vf x' #x out pos #v #p

(* ANY DEFINED BY: the prefix items, then the suffix (written first) *)
and write_items_any (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (RS.wsupported_items ls /\ Conf.wf_items ls))
  (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs) (sv: Ghost.erased (sfxs -> Tot (list asn1_value))) (pm: perm)
  ([@@@FStar.Attributes.monomorphize] ws: W.r2l_writer_f (sfxr pm) (WLm.vlenc (Ghost.reveal sv)))
  (x': asn1_items_any_impl_t ls sfxi) (#x: Ghost.erased (asn1_sequence_any_t_core ls sfxs))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (asn1_items_any_rel ls sfxr pm) (WLm.aenc ls (Ghost.reveal sv)) x' x out pos v p)
  (decreases ls)
= [@inline_let] let vf : W.r2l_writer_f #(asn1_items_any_impl_t ls sfxi) #(asn1_sequence_any_t_core ls sfxs) (asn1_items_any_rel ls sfxr pm) (WLm.aenc ls (Ghost.reveal sv)) =
  (match ls with
  | ASN1_GEN_ITEMS_NIL ->
    RS.items_any_nil_equiv sfxr;
    write_ext #sfxi #sfxs sfxr (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr) ()
      (WLm.aenc ASN1_GEN_ITEMS_NIL (Ghost.reveal sv)) (fun x -> WLm.aenc_nil (Ghost.reveal sv) x) pm
      ws
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    RS.items_any_single_equiv dk sfxr;
    write_ext #(asn1_decorated_impl_t dk & sfxi) #(asn1_decorated_t_core dk & sfxs)
      (prel_pair (asn1_decorated_rel dk) sfxr) (asn1_items_any_rel (PS.single dk) sfxr) ()
      (WLm.aenc (PS.single dk) (Ghost.reveal sv)) (fun x -> WLm.aenc_single dk (Ghost.reveal sv) x) pm
      (write_pair (asn1_decorated_rel dk) sfxr pm
        (fun x' #x out pos #v #p -> write_dec dk () pm x' #x out pos #v #p)
        ws)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    RS.items_any_cons_equiv dk dk2 tl2 sfxr;
    write_ext
      #(asn1_decorated_impl_t dk & asn1_items_any_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi)
      #(asn1_decorated_t_core dk & asn1_sequence_any_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs)
      (prel_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr))
      (asn1_items_any_rel (PS.cons2 dk dk2 tl2) sfxr) ()
      (WLm.aenc (PS.cons2 dk dk2 tl2) (Ghost.reveal sv)) (fun x -> WLm.aenc_cons dk dk2 tl2 (Ghost.reveal sv) x) pm
      (write_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr) pm
        (fun x' #x out pos #v #p -> write_dec dk () pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> write_items_any (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) () sfxr sv pm ws x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

(* The key, then the payload selected by the key *)
and write_adb (kid: asn1_id_t) ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) (u: squash (Conf.wf_terminal kid key_k /\ In.adb_key_supported key_k))
  ([@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (u': squash (RS.wsupported_ls ls /\ Conf.wf_ls ls)) (pm: perm)
  (x': asn1_adb_suffix_impl_t key_k ls None) (#x: Ghost.erased (AL.ady key_k ls))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (asn1_adb_rel key_k ls pm) (WLm.senc kid key_k ls) x' x out pos v p)
  (decreases ls)
= [@inline_let] let vf : W.r2l_writer_f #(asn1_adb_suffix_impl_t key_k ls None) #(AL.ady key_k ls) (asn1_adb_rel key_k ls pm) (WLm.senc kid key_k ls) =
  (match ls with
  | [] -> WA.write_adb_nil kid key_k pm
  | [(kx, y)] ->
    WA.write_adb_single kid () kx y pm
      (fun x' #x out pos #v #p -> write_items (dsnd y) () pm x' #x out pos #v #p)
  | (kx, y) :: hd2 :: tl2 ->
    WA.write_adb_cons kid () kx y hd2 tl2 pm
      (fun x' #x out pos #v #p -> write_items (dsnd y) () pm x' #x out pos #v #p)
      (fun x' #x out pos #v #p -> write_adb kid key_k () (hd2 :: tl2) () pm x' #x out pos #v #p))
  in vf x' #x out pos #v #p

(* The same, with a fallback, whose items writer is `wfb` *)
and write_afb (kid: asn1_id_t) ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) (u: squash (Conf.wf_terminal kid key_k /\ In.adb_key_supported key_k))
  ([@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (u': squash (RS.wsupported_ls ls /\ Conf.wf_ls ls))
  ([@@@FStar.Attributes.monomorphize] fb: asn1_gen_items_lk) (pm: perm)
  ([@@@FStar.Attributes.monomorphize] wfb: W.r2l_writer_f (asn1_items_rel (dsnd fb) pm) (WLm.ienc (dsnd fb)))
  (x': asn1_adb_suffix_impl_t key_k ls (Some (PA.fbt key_k fb))) (#x: Ghost.erased (AL.ady_fb key_k ls fb))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (PA.afb_rel key_k ls fb pm) (WLm.fsenc kid key_k ls fb) x' x out pos v p)
  (decreases ls)
= [@inline_let] let vf : W.r2l_writer_f #(asn1_adb_suffix_impl_t key_k ls (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k ls fb) (PA.afb_rel key_k ls fb pm) (WLm.fsenc kid key_k ls fb) =
  (match ls with
  | [] -> WA.write_afb_nil kid key_k fb () pm wfb
  | [(kx, y)] ->
    WA.write_afb_single kid () kx y fb pm
      (fun x' #x out pos #v #p -> write_items (dsnd y) () pm x' #x out pos #v #p)
      (WA.write_afb_nil kid key_k fb () pm wfb)
  | (kx, y) :: hd2 :: tl2 ->
    WA.write_afb_cons kid () kx y hd2 tl2 fb pm
      (fun x' #x out pos #v #p -> write_items (dsnd y) () pm x' #x out pos #v #p)
      (fun x' #x out pos #v #p -> write_afb kid key_k () (hd2 :: tl2) () fb pm wfb x' #x out pos #v #p))
  in vf x' #x out pos #v #p

and write_items (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (RS.wsupported_items ls /\ Conf.wf_items ls)) (pm: perm)
  (x': asn1_items_impl_t ls) (#x: Ghost.erased (asn1_sequence_t_core ls))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (asn1_items_rel ls pm) (WLm.ienc ls) x' x out pos v p)
  (decreases ls)
= [@inline_let] let vf : W.r2l_writer_f #(asn1_items_impl_t ls) #(asn1_sequence_t_core ls) (asn1_items_rel ls pm) (WLm.ienc ls) =
  (match ls with
  | ASN1_GEN_ITEMS_NIL ->
    RS.items_nil_equiv ();
    write_ext #unit #unit (prel_emp unit unit) (asn1_items_rel ASN1_GEN_ITEMS_NIL) ()
      (WLm.ienc ASN1_GEN_ITEMS_NIL) (fun x -> WLm.ienc_nil x) pm
      (write_emp_unit pm)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    RS.items_single_equiv dk;
    write_ext #(asn1_decorated_impl_t dk) #(asn1_decorated_t_core dk) (asn1_decorated_rel dk) (asn1_items_rel (PS.single dk)) ()
      (WLm.ienc (PS.single dk)) (fun x -> WLm.ienc_single dk x) pm
      (fun x' #x out pos #v #p -> write_dec dk () pm x' #x out pos #v #p)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    RS.items_cons_equiv dk dk2 tl2;
    write_ext
      #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
      #(asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
      (prel_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
      (asn1_items_rel (PS.cons2 dk dk2 tl2)) ()
      (WLm.ienc (PS.cons2 dk dk2 tl2)) (fun x -> WLm.ienc_cons dk dk2 tl2 x) pm
      (write_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) pm
        (fun x' #x out pos #v #p -> write_dec dk () pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> write_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) () pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and write_dec (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] d: _) ([@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s d) (u: squash (RS.wsupported_dec dk /\ Conf.wf_dec dk)) (pm: perm)
  (x': asn1_decorated_impl_t dk) (#x: Ghost.erased (asn1_decorated_t_core dk))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (asn1_decorated_rel dk pm) (WLm.denc dk) x' x out pos v p)
  (decreases dk)
= [@inline_let] let vf : W.r2l_writer_f #(asn1_decorated_impl_t dk) #(asn1_decorated_t_core dk) (asn1_decorated_rel dk pm) (WLm.denc dk) =
  (match dk with
  | ASN1_PLAIN_ILC k ->
    RS.dec_plain_equiv k;
    write_ext #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) (asn1_decorated_rel (ASN1_PLAIN_ILC k)) ()
      (WLm.denc (ASN1_PLAIN_ILC k)) (fun x -> WLm.denc_plain k x) pm
      (fun x' #x out pos #v #p -> write_k k () pm x' #x out pos #v #p)
  | ASN1_OPTION_ILC k ->
    RS.dec_option_equiv k;
    write_ext #(option (asn1_impl_t k)) #(option (asn1_t k)) (prel_option (asn1_rel k)) (asn1_decorated_rel (ASN1_OPTION_ILC k)) ()
      (WLm.denc (ASN1_OPTION_ILC k)) (fun x -> WLm.denc_option k x) pm
      (write_option (asn1_rel k) pm (fun x' #x out pos #v #p -> write_k k () pm x' #x out pos #v #p))
  | ASN1_DEFAULT_TERMINAL id0 #k defv ->
    RS.dec_default_equiv id0 defv;
    write_ext #(option (asn1_terminal_impl_t k)) #(default_tv (key_of_lit k defv)) (RS.prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)) ()
      (WLm.denc (ASN1_DEFAULT_TERMINAL id0 #k defv)) (fun x -> WLm.denc_default id0 defv x) pm
      (write_default (asn1_terminal_rel k) (key_of_lit k defv) pm
        (fun x' #x out pos #v #p -> WL.r2l_write_terminal id0 k () pm x' #x out pos #v #p))
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv ->
    RS.dec_default_restricted_equiv id0 r defv;
    write_ext #(option (asn1_terminal_impl_t k)) #(default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv))
      (RS.prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)) ()
      (WLm.denc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)) (fun x -> WLm.denc_default_restricted id0 r defv x) pm
      (write_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv) pm
        (write_restricted id0 k r pm
          (fun x' #x out pos #v #p -> WL.r2l_write_terminal id0 k () pm x' #x out pos #v #p))))
  in vf x' #x out pos #v #p

and write_k (#[@@@FStar.Attributes.monomorphize] s: _) ([@@@FStar.Attributes.monomorphize] k: asn1_k s) (u: squash (RS.wsupported_k k /\ Conf.wf k)) (pm: perm)
  (x': asn1_impl_t k) (#x: Ghost.erased (asn1_t k))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (asn1_rel k pm) (WLm.kenc k) x' x out pos v p)
  (decreases k)
= [@inline_let] let vf : W.r2l_writer_f #(asn1_impl_t k) #(asn1_t k) (asn1_rel k pm) (WLm.kenc k) =
  (match k with
  | ASN1_ILC id k' ->
    RS.rel_ilc_equiv id k';
    write_ext #(asn1_content_impl_t k') #(asn1_content_t k') (asn1_content_rel k') (asn1_rel (ASN1_ILC id k')) ()
      (WLm.kenc (ASN1_ILC id k')) (fun x -> WLm.kenc_ilc id k' x) pm
      (fun x' #x out pos #v #p -> write_content id k' () pm x' #x out pos #v #p)
  | ASN1_CHOICE_ILC lc pf ->
    RS.rel_choice_equiv lc pf;
    write_ext #(asn1_lc_impl_t lc) #(make_gen_choice_type (asn1_lc_t lc)) (asn1_lc_rel lc) (asn1_rel (ASN1_CHOICE_ILC lc pf)) ()
      (WLm.kenc (ASN1_CHOICE_ILC lc pf)) (fun x -> WLm.kenc_choice lc pf x) pm
      (fun x' #x out pos #v #p -> write_lc lc () pm x' #x out pos #v #p)
  | ASN1_ANY_ILC ->
    RS.rel_any_equiv ();
    write_ext #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (asn1_rel ASN1_ANY_ILC) ()
      (WLm.kenc ASN1_ANY_ILC) (fun x -> WLm.kenc_any x) pm
      (write_slice_ser asn1_value_enc pm))
  in vf x' #x out pos #v #p

and write_lc ([@@@FStar.Attributes.monomorphize] lc: list (asn1_id_t & asn1_content_k)) (u: squash (RS.wsupported_lc lc /\ Conf.wf_lc lc)) (pm: perm)
  (x': asn1_lc_impl_t lc) (#x: Ghost.erased (make_gen_choice_type (asn1_lc_t lc)))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (asn1_lc_rel lc pm) (WLm.lcenc lc) x' x out pos v p)
  (decreases lc)
= [@inline_let] let vf : W.r2l_writer_f #(asn1_lc_impl_t lc) #(make_gen_choice_type (asn1_lc_t lc)) (asn1_lc_rel lc pm) (WLm.lcenc lc) =
  (match lc with
  | [] -> write_lc_nil pm
  | [(id', c)] ->
    write_lc_single id' c pm (fun x' #x out pos #v #p -> write_content id' c () pm x' #x out pos #v #p)
  | (id', c) :: hd2 :: tl2 ->
    write_lc_cons id' c hd2 tl2 pm
      (fun x' #x out pos #v #p -> write_content id' c () pm x' #x out pos #v #p)
      (fun x' #x out pos #v #p -> write_lc (hd2 :: tl2) () pm x' #x out pos #v #p))
  in vf x' #x out pos #v #p

module ASN1.Pulse.JitFrame

(* The raw bytes of a present component other than ANY are one TLV whose
   identifier is one of those of the component (`L.framed`). The JIT
   writers (ASN1.Pulse.JitWriter) use this to tell that a SEQUENCE is
   invalid as soon as one of its present components is. *)

#lang-pulse
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.RawRel

module SB = LowParse.Spec.Base
module L = ASN1.Pulse.JitWriter.Lemmas
module PA = ASN1.Pulse.ParseAdb
module FS = FStar.Set

let fr_t (#t: Type0) (r: bprel t) (s: FS.set asn1_id_t) =
  (pm: perm) -> (y: t) -> (x: Ghost.erased SB.bytes) ->
  stt_ghost unit emp_inames (r pm y x) (fun _ -> r pm y x ** pure (L.framed s x))

ghost
fn fr_tlv (id: asn1_id_t) (#t: Type0) (r: bprel t) (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires raw_tlv id r pm y x
ensures raw_tlv id r pm y x ** pure (L.framed (FS.singleton id) x)
{
  unfold (raw_tlv id r pm y x);
  with c . assert (r pm y c);
  L.framed_intro id (FS.singleton id) c;
  fold (raw_tlv id r pm y x);
}

ghost
fn fr_ext (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2)) (s: FS.set asn1_id_t) (f: fr_t r1 s)
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r2 pm y x
ensures r2 pm y x ** pure (L.framed s x)
{
  rewrite (r2 pm y x) as (r1 pm y x);
  f pm y x;
  rewrite (r1 pm y x) as (r2 pm y x);
}

ghost
fn fr_sub (#t: Type0) (r: bprel t) (s1 s2: FS.set asn1_id_t) (sq: squash (FS.subset s1 s2)) (f: fr_t r s1)
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r pm y x
ensures r pm y x ** pure (L.framed s2 x)
{
  f pm y x;
  L.framed_sub s1 s2 x;
}

ghost
fn fr_either (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (s1 s2 s: FS.set asn1_id_t)
  (sub: squash (FS.subset s1 s /\ FS.subset s2 s)) (f1: fr_t r1 s1) (f2: fr_t r2 s2)
  (pm: perm) (y: either t1 t2) (x: Ghost.erased SB.bytes)
requires raw_either r1 r2 pm y x
ensures raw_either r1 r2 pm y x ** pure (L.framed s x)
{
  match y {
    Inl a -> {
      rewrite (raw_either r1 r2 pm y x) as (r1 pm a x);
      f1 pm a x;
      L.framed_sub s1 s x;
      rewrite (r1 pm a x) as (raw_either r1 r2 pm y x);
    }
    Inr b -> {
      rewrite (raw_either r1 r2 pm y x) as (r2 pm b x);
      f2 pm b x;
      L.framed_sub s2 s x;
      rewrite (r2 pm b x) as (raw_either r1 r2 pm y x);
    }
  }
}

ghost
fn fr_false (t: Type0) (s: FS.set asn1_id_t) (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires raw_false t pm y x
ensures raw_false t pm y x ** pure (L.framed s x)
{
  unfold (raw_false t pm y x);
  unreachable ()
}

ghost
fn fr_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k)
  (pm: perm) (y: asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (x: Ghost.erased SB.bytes)
requires raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm y x
ensures raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm y x ** pure (L.framed (FS.singleton id) x)
{
  terminal_prefixed_eq id id2 k2 pm y x;
  rewrite (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm y x) as (raw_tlv id (raw_terminal_rel id2 k2) pm (prefixed_down id2 k2 y) x);
  fr_tlv id (raw_terminal_rel id2 k2) pm (prefixed_down id2 k2 y) x;
  rewrite (raw_tlv id (raw_terminal_rel id2 k2) pm (prefixed_down id2 k2 y) x) as (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm y x);
}

let fr_terminal (id: asn1_id_t) (k: asn1_terminal_k) : fr_t (raw_terminal_rel id k) (FS.singleton id) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 -> fun pm y x -> fr_prefixed id id2 k2 pm y x
  | _ ->
    terminal_leaf_equiv id k;
    fr_ext (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_leaf k) pm y x)

let fr_content (id: asn1_id_t) (k: asn1_content_k) : fr_t (raw_content_rel id k) (FS.singleton id) =
  match k with
  | ASN1_TERMINAL k' ->
    content_terminal_equiv id k';
    fr_ext (raw_terminal_rel id k') (raw_content_rel id k) () (FS.singleton id) (fr_terminal id k')
  | ASN1_RESTRICTED_TERMINAL k' r ->
    content_restricted_equiv id k' r;
    fr_ext (raw_terminal_rel id k') (raw_content_rel id k) () (FS.singleton id) (fr_terminal id k')
  | ASN1_PREFIXED k' ->
    content_prefixed_equiv id k';
    fr_ext (raw_tlv id (raw_rel k')) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_rel k') pm y x)
  | ASN1_SEQUENCE gitems ->
    content_sequence_equiv id gitems;
    fr_ext (raw_tlv id (raw_items_rel false (dsnd gitems))) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_items_rel false (dsnd gitems)) pm y x)
  | ASN1_SET ids items pf ->
    content_set_equiv id ids items pf;
    fr_ext (raw_tlv id (raw_items_rel true items)) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_items_rel true items) pm y x)
  | ASN1_SEQUENCE_OF ne k' ->
    content_seq_of_equiv id ne k';
    fr_ext (raw_tlv id (raw_ml (raw_rel k'))) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_ml (raw_rel k')) pm y x)
  | ASN1_SET_OF ne k' ->
    content_set_of_equiv id ne k';
    fr_ext (raw_tlv id (raw_ml_sorted (raw_rel k'))) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_ml_sorted (raw_rel k')) pm y x)
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None ->
      content_adb_none_equiv id ipd prefix kid key_k ls pf pf';
      fr_ext (raw_tlv id (raw_items_any_rel prefix (raw_adb_rel kid key_k ls))) (raw_content_rel id k) () (FS.singleton id)
        (fun pm y x -> fr_tlv id (raw_items_any_rel prefix (raw_adb_rel kid key_k ls)) pm y x)
    | Some fb ->
      content_adb_some_equiv id ipd prefix kid key_k ls fb pf pf';
      fr_ext (raw_tlv id (raw_items_any_rel prefix (raw_afb_rel kid key_k ls fb))) (raw_content_rel id k) () (FS.singleton id)
        (fun pm y x -> fr_tlv id (raw_items_any_rel prefix (raw_afb_rel kid key_k ls fb)) pm y x)
    end

let lc_set (lc: list (asn1_id_t & asn1_content_k)) : FS.set asn1_id_t =
  FS.as_set' (List.Tot.map fst lc)

let rec fr_lc (lc: list (asn1_id_t & asn1_content_k)) : Tot (fr_t (raw_lc_rel lc) (lc_set lc)) (decreases lc) =
  match lc with
  | [] ->
    lc_nil_equiv ();
    fr_ext (raw_false unit) (raw_lc_rel []) () (lc_set lc) (fun pm y x -> fr_false unit (lc_set lc) pm y x)
  | [(id', c)] ->
    lc_single_equiv id' c;
    assert_norm (lc_set [(id', c)] == FS.union (FS.singleton id') FS.empty);
    fr_ext (raw_content_rel id' c) (raw_lc_rel lc) () (lc_set lc)
      (fun pm y x -> fr_sub (raw_content_rel id' c) (FS.singleton id') (lc_set lc) () (fr_content id' c) pm y x)
  | (id', c) :: hd2 :: tl2 ->
    lc_cons_equiv id' c hd2 tl2;
    assert_norm (lc_set ((id', c) :: hd2 :: tl2) == FS.union (FS.singleton id') (lc_set (hd2 :: tl2)));
    fr_ext (raw_either (raw_content_rel id' c) (raw_lc_rel (hd2 :: tl2))) (raw_lc_rel lc) () (lc_set lc)
      (fun pm y x -> fr_either (raw_content_rel id' c) (raw_lc_rel (hd2 :: tl2)) (FS.singleton id') (lc_set (hd2 :: tl2)) (lc_set lc) ()
        (fr_content id' c) (fr_lc (hd2 :: tl2)) pm y x)

let fr_k (#s: _) (k: asn1_k s) (u: squash (~ (ASN1_ANY_ILC? k))) : fr_t (raw_rel k) s =
  match k with
  | ASN1_ILC id k' ->
    rel_ilc_equiv id k';
    fr_ext (raw_content_rel id k') (raw_rel k) () s (fr_content id k')
  | ASN1_CHOICE_ILC lc pf ->
    rel_choice_equiv lc pf;
    fr_ext (raw_lc_rel lc) (raw_rel k) () s
      (fun pm y x -> fr_sub (raw_lc_rel lc) (lc_set lc) s () (fr_lc lc) pm y x)

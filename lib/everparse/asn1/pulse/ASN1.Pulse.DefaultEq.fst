module ASN1.Pulse.DefaultEq
#lang-pulse

(* Runtime decision of whether a raw terminal value is exactly a DEFAULT
   literal, i.e. whether its bytes are `WA.raw_key_enc id k defl`. Used
   to omit explicit default values, as in DER. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Sequence
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.RawRel
module SB = LowParse.Spec.Base
module E = ASN1.Spec.Content.Enc
module In = ASN1.Pulse.Interpreter
module L = ASN1.Pulse.JitWriter.Lemmas
module JT = ASN1.Pulse.JitTerminal
module JK = ASN1.Pulse.JitAdbKey
module WA = ASN1.Pulse.WriteAdb

(* Exact decider of `c == d` for the bytes `c` of `r pm x' c` *)
inline_for_extraction
let dd (#t: Type0) (r: bprel t) (d: SB.bytes) (pm: perm) =
  (x': t) -> (#c: Ghost.erased SB.bytes) ->
  stt bool (r pm x' c) (fun res -> r pm x' c ** pure (res == true <==> Ghost.reveal c == d))

(* Pure lemmas *)

let enc_tlv_inj' (id: asn1_id_t) (c d: SB.bytes)
: Lemma (requires (enc_tlv id true c == enc_tlv id true d)) (ensures (c == d))
= Seq.append_empty_r (enc_tlv id true c);
  Seq.append_empty_r (enc_tlv id true d);
  enc_tlv_prefix_free id id true true c d Seq.empty Seq.empty

let enc_tlv_inj (id: asn1_id_t) (c d: SB.bytes)
: Lemma (enc_tlv id true c == enc_tlv id true d <==> c == d)
= Classical.move_requires (enc_tlv_inj' id c) d

#push-options "--fuel 1 --ifuel 1 --z3rlimit 32"
let leaf_key_c (k: E.leaf_k { In.adb_key_supported k }) (defl: asn1_key_lit k)
: Lemma (JK.raw_key_c k defl == E.leaf_enc k (key_of_lit k defl))
= match k with
  | ASN1_OID ->
    let x' : asn1_oid_t = defl in
    WA.oid_arcs_enc x'
  | _ ->
    JK.raw_key_list_eq k defl;
    In.key_enc_list_correct k defl
#pop-options

let leaf_is_default (k: E.leaf_k) (defv: asn1_terminal_t k) (c: SB.bytes)
: Lemma ((L.tacc k c /\ ~ (L.holds k (defaultv_filter defv) c)) <==> c == E.leaf_enc k defv)
= L.leaf_tacc k defv (defaultv_filter defv) (E.leaf_enc k defv);
  E.leaf_enc_consumed k c;
  Seq.lemma_eq_elim (Seq.slice c 0 (Seq.length c)) c

(* Leaves: the content is valid and not different from the default *)

inline_for_extraction
fn dd_leaf (k: E.leaf_k) (defl: asn1_key_lit k) (u: squash (In.adb_key_supported k)) (pm: perm)
: dd #(asn1_terminal_impl_t k) (raw_leaf k) (JK.raw_key_c k defl) pm
= (x': asn1_terminal_impl_t k) (#c: Ghost.erased SB.bytes)
{
  leaf_key_c k defl;
  leaf_is_default k (key_of_lit k defl) c;
  assert (pure (JT.ptrue c));
  let ok = JT.pv k () pm x' #c;
  if ok {
    let ne = JT.pn k defl () pm x' #c;
    not ne
  } else {
    false
  }
}

(* A TLV with the same identifier *)

inline_for_extraction
fn dd_tlv (id: asn1_id_t) (#t: Type0) (r: bprel t) (d: SB.bytes) (pm: perm) (f: dd r d pm)
: dd #t (raw_tlv id r) (enc_tlv id true d) pm
= (x': t) (#c: Ghost.erased SB.bytes)
{
  unfold (raw_tlv id r pm x' c);
  with c0 . assert (r pm x' c0);
  let res = f x' #c0;
  enc_tlv_inj id c0 d;
  fold (raw_tlv id r pm x' c);
  res
}

(* Terminals *)

inline_for_extraction
fn dd_leaf_tlv (id: asn1_id_t) (k: E.leaf_k) (defl: asn1_key_lit k) (u: squash (In.adb_key_supported k)) (pm: perm)
: dd #(asn1_terminal_impl_t k) (raw_terminal_rel id k) (WA.raw_key_enc id k defl) pm
= (x': asn1_terminal_impl_t k) (#c: Ghost.erased SB.bytes)
{
  terminal_leaf_equiv id k;
  JK.raw_key_enc_c id k defl;
  rewrite (raw_terminal_rel id k pm x' c) as (raw_tlv id (raw_leaf k) pm x' c);
  let res = dd_tlv id (raw_leaf k) (JK.raw_key_c k defl) pm (fun x2 #c2 -> dd_leaf k defl () pm x2 #c2) x' #c;
  rewrite (raw_tlv id (raw_leaf k) pm x' c) as (raw_terminal_rel id k pm x' c);
  res
}

inline_for_extraction
fn dd_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (defl: asn1_key_lit (ASN1_PREFIXED_TERMINAL id2 k2)) (pm: perm)
  (f: dd #(asn1_terminal_impl_t k2) (raw_terminal_rel id2 k2) (WA.raw_key_enc id2 k2 (In.prefixed_lit id2 k2 defl)) pm)
: dd #(asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2)) (WA.raw_key_enc id (ASN1_PREFIXED_TERMINAL id2 k2) defl) pm
= (x': asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (#c: Ghost.erased SB.bytes)
{
  terminal_prefixed_eq id id2 k2 pm x' c;
  JK.raw_key_enc_c id (ASN1_PREFIXED_TERMINAL id2 k2) defl;
  let x2 = prefixed_down id2 k2 x';
  rewrite (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x' c) as (raw_tlv id (raw_terminal_rel id2 k2) pm x2 c);
  let res = dd_tlv id (raw_terminal_rel id2 k2) (WA.raw_key_enc id2 k2 (In.prefixed_lit id2 k2 defl)) pm f x2 #c;
  rewrite (raw_tlv id (raw_terminal_rel id2 k2) pm x2 c) as (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x' c);
  res
}

[@@In.asn1_pulse_attr]
let rec dd_term (id: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) ([@@@FStar.Attributes.monomorphize] defl: asn1_key_lit k) (u: squash (In.adb_key_supported k)) (pm: perm)
  (x': asn1_terminal_impl_t k) (#c: Ghost.erased SB.bytes)
: Tot (stt bool (raw_terminal_rel id k pm x' c) (fun res -> raw_terminal_rel id k pm x' c ** pure (res == true <==> Ghost.reveal c == WA.raw_key_enc id k defl)))
  (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    dd_prefixed id id2 k2 defl pm
      (fun x' #c -> dd_term id2 k2 (In.prefixed_lit id2 k2 defl) () pm x' #c) x' #c
  | _ -> dd_leaf_tlv id k defl () pm x' #c

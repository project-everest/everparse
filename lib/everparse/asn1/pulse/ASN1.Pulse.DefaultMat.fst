module ASN1.Pulse.DefaultMat
#lang-pulse

(* Materializers of DEFAULT values (`dmat`, for `DD_DEFAULT_V`): when a
   DEFAULT component is absent, the parser returns its default value. The
   value is parsed from its DER content bytes, held in a static array (in
   C, `static const`, in .rodata), with the terminal parser: slices of the
   value (strings, big INTEGERs) point into that array. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module G = Pulse.Lib.GlobalArray
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module SB = LowParse.Spec.Base
module In = ASN1.Pulse.Interpreter
module P = ASN1.Pulse.Parser
module CE = ASN1.Spec.Content.Enc

let rec seq_of_list_append (#a: Type) (l m: list a)
: Lemma (ensures (Seq.seq_of_list (List.Tot.append l m) == Seq.append (Seq.seq_of_list l) (Seq.seq_of_list m))) (decreases l)
= match l with
  | [] ->
    Seq.lemma_seq_of_list_induction #a [];
    Seq.lemma_eq_elim (Seq.seq_of_list (List.Tot.append l m)) (Seq.append (Seq.seq_of_list l) (Seq.seq_of_list m))
  | h :: t ->
    seq_of_list_append t m;
    Seq.lemma_seq_of_list_induction (h :: t);
    Seq.lemma_seq_of_list_induction (h :: List.Tot.append t m);
    Seq.append_assoc (Seq.create 1 h) (Seq.seq_of_list t) (Seq.seq_of_list m)

let slice_padded (l: list U8.t)
: Lemma (requires (List.Tot.length (List.Tot.append l [0uy]) == List.Tot.length l + 1))
  (ensures (Seq.slice (Seq.seq_of_list (List.Tot.append l [0uy])) 0 (List.Tot.length l) == Seq.seq_of_list l))
= seq_of_list_append l [0uy];
  Seq.lemma_eq_elim (Seq.slice (Seq.seq_of_list (List.Tot.append l [0uy])) 0 (List.Tot.length l)) (Seq.seq_of_list l)

(* The terminals whose DEFAULT values are materialized from their content
   bytes (`In.key_enc_list`): not OBJECT IDENTIFIER, not EXPLICIT-tagged
   (see `mat_prefixed`) *)
[@@In.asn1_pulse_attr]
let mat_leaf_k (k: asn1_terminal_k) : Tot bool =
  In.adb_key_supported k && not (ASN1_OID? k) && not (ASN1_PREFIXED_TERMINAL? k)

(* `l0` is the content bytes, padded with one byte (C has no empty arrays) *)
let mat_leaf_ok (k: asn1_terminal_k { mat_leaf_k k }) (defv: asn1_key_lit k) (l0: list U8.t) (n: SZ.t) : prop =
  l0 == List.Tot.append (In.key_enc_list k defv) [0uy] /\
  List.Tot.length l0 == SZ.v n + 1

let mat_leaf_parsed (k: asn1_terminal_k { mat_leaf_k k }) (defv: asn1_key_lit k) (l0: list U8.t) (n: SZ.t)
: Lemma (requires (mat_leaf_ok k defv l0 n))
  (ensures (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser k) (Seq.slice (Seq.seq_of_list l0) 0 (SZ.v n)) (key_of_lit k defv)))
= In.key_enc_list_correct k defv;
  List.Tot.Properties.append_length (In.key_enc_list k defv) [0uy];
  slice_padded (In.key_enc_list k defv);
  CE.parse_leaf_enc k (key_of_lit k defv)

[@@In.asn1_pulse_attr]
inline_for_extraction
fn mat_leaf ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k { mat_leaf_k k })
  (defv: asn1_key_lit k) (l0: Ghost.erased (list U8.t))
  (arr: G.static_array U8.t { G.static_array_elems arr == Seq.seq_of_list l0 })
  (n: SZ.t) (sq: squash (mat_leaf_ok k defv l0 n))
: dmat k (key_of_lit k defv)
= (_: unit)
{
  mat_leaf_parsed k defv l0 n;
  let a = G.array_of_static_array arr;
  with p . assert (A.pts_to a #p (G.static_array_elems arr));
  A.pts_to_len a;
  let s0 = S.from_array a #p (SZ.add n 1sz);
  let s = S.subslice s0 0sz n;
  with r . assert (S.subslice_rest s s0 p 0sz n r);
  drop_ (S.subslice_rest s s0 p 0sz n r);
  drop_ (S.is_from_array a s0);
  let pt : aparser #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) #asn1_weak_parser_kind (asn1_terminal_as_parser k) =
    (fun input #pm #w #v -> P.parse_terminal k input #pm #w #v);
  let res = pt s #p #(Seq.slice (G.static_array_elems arr) 0 (SZ.v n)) #(key_of_lit k defv);
  drop_ (Pulse.Lib.Trade.trade (asn1_terminal_rel k p res (key_of_lit k defv)) (S.pts_to s #p (Seq.slice (G.static_array_elems arr) 0 (SZ.v n))));
  fold (dv_any_rel k (key_of_lit k defv) res);
  res
}

inline_for_extraction
let up_impl (id2: asn1_id_t) (k2: asn1_terminal_k) (x: asn1_terminal_impl_t k2) : Tot (asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) =
  assert_norm (asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_impl_t k2);
  coerce_eq () x

let up_rel (id2: asn1_id_t) (k2: asn1_terminal_k) (p: perm) (x: asn1_terminal_impl_t k2) (v: asn1_terminal_t k2)
: Lemma (asn1_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2) p (up_impl id2 k2 x) (ASN1.Pulse.AdbPrefixed.pt_val id2 k2 v) == asn1_terminal_rel k2 p x v)
= assert_norm (asn1_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_rel k2)

(* EXPLICIT-tagged terminals: the value of the inner terminal *)
[@@In.asn1_pulse_attr]
inline_for_extraction
fn mat_prefixed (id2: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k2: asn1_terminal_k)
  (defv: asn1_key_lit (ASN1_PREFIXED_TERMINAL id2 k2))
  (m: dmat k2 (key_of_lit k2 (In.prefixed_lit id2 k2 defv)))
: dmat (ASN1_PREFIXED_TERMINAL id2 k2) (key_of_lit (ASN1_PREFIXED_TERMINAL id2 k2) defv)
= (_: unit)
{
  In.key_of_lit_prefixed id2 k2 defv;
  let res = m ();
  unfold (dv_any_rel k2 (key_of_lit k2 (In.prefixed_lit id2 k2 defv)) res);
  with p . assert (asn1_terminal_rel k2 p res (key_of_lit k2 (In.prefixed_lit id2 k2 defv)));
  up_rel id2 k2 p res (key_of_lit k2 (In.prefixed_lit id2 k2 defv));
  rewrite (asn1_terminal_rel k2 p res (key_of_lit k2 (In.prefixed_lit id2 k2 defv)))
    as (asn1_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2) p (up_impl id2 k2 res) (key_of_lit (ASN1_PREFIXED_TERMINAL id2 k2) defv));
  fold (dv_any_rel (ASN1_PREFIXED_TERMINAL id2 k2) (key_of_lit (ASN1_PREFIXED_TERMINAL id2 k2) defv) (up_impl id2 k2 res));
  up_impl id2 k2 res
}

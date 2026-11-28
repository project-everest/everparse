module ASN1.Pulse.RawBytes

(* The bytes `rb k y` that the raw writer (`ASN1.Pulse.RawRel.raw_rel`)
   writes for a raw value `y: ASN1.Spec.Raw.asn1_raw_t k`, following the
   shape of `raw_rel`.

   For a well-formed supported schema, `rb k y` is the generic encoding of
   the sorted value `ASN1.Spec.Raw.Sorted.svalue true k y` (`rb_svalue`),
   and thus:
   - if the typed parser accepts exactly `rb k y`, then `check_ser k u y`
     is `Some x` (`rb_parse`);
   - if `check_ser k u y == Some x`, then `rb k y == asn1_enc k x`
     (`rb_check_ser`.) *)

open LowParse.Tot.Base
open ASN1.Bytes
open ASN1.Base
open ASN1.Spec.Value
open ASN1.Spec.Value.Enc
open ASN1.Spec.Content.Enc
open ASN1.Spec.Interpreter
open ASN1.Spec.Conformance
open ASN1.Spec.ToValue
open ASN1.Spec.Raw
open ASN1.Spec.Raw.Props
open ASN1.Spec.Raw.Value
open ASN1.Spec.Raw.Sorted

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module List = FStar.List.Tot
module SB = LowParse.Spec.Base
module W = LowParse.Pulse.R2L
module Str = ASN1.Spec.Conformance.Struct
module Set_ = ASN1.Spec.Set
module SI = ASN1.Pulse.SortedInsert
module RR = ASN1.Pulse.RawRel
module WA = ASN1.Pulse.WriteAdb
module In = ASN1.Pulse.Interpreter
module L = ASN1.Pulse.JitWriter.Lemmas
module PSL = ASN1.Pulse.ParseSequence.Lemmas
module IE = ASN1.Spec.IdentifierU32.Enc
module IdU = ASN1.Spec.IdentifierU32
module JK = ASN1.Pulse.JitAdbKey
module DE = ASN1.Pulse.DefaultEq
module Ser = ASN1.Spec.Serializer

(* The bytes *)

let rec rb_term (id: asn1_id_t) (k: asn1_terminal_k) (y: asn1_raw_terminal_t k) : Tot bytes (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_raw_terminal_t k2);
    enc_tlv id true (rb_term id2 k2 (coerce_eq #(asn1_raw_terminal_t k) #(asn1_raw_terminal_t k2) () y))
  | _ -> enc_tlv id true (raw_leaf_enc k y)

let rb_default (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k) (z: asn1_raw_terminal_t k) : GTot bytes =
  let c = rb_term id0 k z in
  if In.adb_key_supported k
  then (if FStar.IndefiniteDescription.strong_excluded_middle (c == WA.raw_key_enc id0 k defl) then Seq.empty else c)
  else c

let rec rb_content (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k) : GTot bytes (decreases %[k; 0]) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> rb_term id k' y
  | ASN1_TERMINAL k' -> rb_term id k' y
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    enc_tlv id true (rb_items false items y)
  | ASN1_SET _ items _ -> enc_tlv id true (rb_items true items y)
  | ASN1_SEQUENCE_OF _ k' -> enc_tlv id true (W.enc_list RR.id_enc (rb_list k' y))
  | ASN1_SET_OF _ k' -> enc_tlv id true (SI.sort_list SI.lt_lex RR.id_enc (rb_list k' y))
  | ASN1_PREFIXED k' -> enc_tlv id true (rb k' y)
  | ASN1_ANY_DEFINED_BY _ prefix kid key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      let sfx (s: make_gen_choice_type (raw_any_t_core key_k ls)) : GTot bytes =
        let (| key, y |) = s in
        rb_ls kid key_k ls key y
      in
      enc_tlv id true (rb_items_any prefix sfx y)
    | Some fb ->
      let (| _, fbitems |) = fb in
      let sfx (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : GTot bytes =
        let (| key, y |) = s in
        rb_ls_fb kid key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> rb_items false fbitems z) key y
      in
      enc_tlv id true (rb_items_any prefix sfx y)
    end

and rb_list (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k)) : GTot (list bytes) (decreases %[k; l]) =
  match l with
  | [] -> []
  | a :: q -> rb k a :: rb_list k q

and rb (#s: _) (k: asn1_k s) (y: asn1_raw_t k) : GTot bytes (decreases %[k; y]) =
  match k with
  | ASN1_ILC id k' -> rb_content id k' y
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let (| id, z |) = y' in
    rb_choice lc id z
  | ASN1_ANY_ILC -> asn1_value_enc y

and rb_choice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc)) : GTot bytes (decreases %[lc; 0]) =
  match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then rb_content id c y
    else rb_choice tl id y

and rb_ls (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_raw_terminal_t key_k) (y: idlookup_t key (raw_any_t_core key_k ls)) : GTot bytes (decreases %[ls; 0]) =
  match ls with
  | [] -> false_elim ()
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then WA.raw_key_enc kid key_k key' `Seq.append` rb_items false items y
    else rb_ls kid key_k tl key y

and rb_ls_fb (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: Type) (fbf: fb -> GTot bytes) (key: asn1_raw_terminal_t key_k) (y: idlookup_with_fallback_t key (raw_any_t_core key_k ls) fb) : GTot bytes (decreases %[ls; 0]) =
  match ls with
  | [] -> rb_term kid key_k key `Seq.append` fbf y
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then WA.raw_key_enc kid key_k key' `Seq.append` rb_items false items y
    else rb_ls_fb kid key_k tl fb fbf key y

and rb_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk) : GTot bytes (decreases %[dk; 0]) =
  match dk with
  | ASN1_PLAIN_ILC k -> rb k y
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    (match y' with None -> Seq.empty | Some z -> rb k z)
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with None -> Seq.empty | Some z -> rb_default id k defv_l z)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with None -> Seq.empty | Some z -> rb_default id k defv_l z)

and rb_items (srt: bool) (#ids: _) (items: asn1_gen_items_l ids) (y: raw_items_t items) : GTot bytes (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> Seq.empty
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> rb_dec dk y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, c) = y' in
    if srt
    then SI.ins SI.lt_tag (rb_dec dk a) (rb_items srt tl c)
    else rb_dec dk a `Seq.append` rb_items srt tl c

and rb_items_any (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (sfx: sfx_t -> GTot bytes) (y: raw_items_any_t items sfx_t) : GTot bytes (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> sfx y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & sfx_t = y in
    let (a, c) = y' in
    rb_dec dk a `Seq.append` sfx c
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, c) = y' in
    rb_dec dk a `Seq.append` rb_items_any tl sfx c

(* Generic lists of values *)

let rec vle_append (l1 l2: list asn1_value)
: Lemma (ensures (asn1_value_list_enc (List.append l1 l2) == Seq.append (asn1_value_list_enc l1) (asn1_value_list_enc l2))) (decreases l1)
= match l1 with
  | [] -> Seq.append_empty_l (asn1_value_list_enc l2)
  | a :: q -> vle_append q l2; Seq.append_assoc (asn1_value_enc a) (asn1_value_list_enc q) (asn1_value_list_enc l2)

let vle_single (v: asn1_value)
: Lemma (asn1_value_list_enc [v] == asn1_value_enc v)
= Seq.append_empty_r (asn1_value_enc v)

let enc_tlv_id (id: asn1_id_t) (ok: bool) (c rest: bytes)
: Lemma (SB.parse IdU.parse_asn1_identifier_U32 (Seq.append (enc_tlv id ok c) rest) == Some (id, Seq.length (IE.asn1_id_enc id)))
= let r1 = enc_hdr ok (Seq.length c) `Seq.append` c in
  Seq.append_assoc (IE.asn1_id_enc id) r1 rest;
  IE.parse_asn1_identifier_U32_enc id (Seq.append r1 rest)

let value_parse_id (v: asn1_value) (rest: bytes)
: Lemma (SI.parse_id (Seq.append (asn1_value_enc v) rest) == Some (value_id v))
= match v with
  | ASN1_VALUE_PRIMITIVE id b -> enc_tlv_id id (PRIMITIVE? id.f) b rest
  | ASN1_VALUE_CONSTRUCTED id l -> enc_tlv_id id (CONSTRUCTED? id.f) (asn1_value_list_enc l) rest

let hdr_bad_none (ok: bool) (n: nat) (rest: bytes)
: Lemma (requires (not ok \/ n >= 4294967296))
  (ensures (None? (parse ASN1.Spec.LengthU32.parse_asn1_length_u32_t (enc_hdr ok n `Seq.append` rest))))
= let b = enc_hdr ok n `Seq.append` rest in
  parse_len_consumed b;
  match parse ASN1.Spec.LengthU32.parse_asn1_length_u32_t b with
  | Some (y, c) ->
    enc_len_head y;
    assert (Seq.index (Seq.slice b 0 c) 0 == Seq.index b 0)
  | None -> ()

let frame_len_tlv (id: asn1_id_t) (ok: bool) (c rest: bytes)
: Lemma (SI.frame_len (Seq.append (enc_tlv id ok c) rest) ==
    (if ok && Seq.length c < 4294967296 then Seq.length (enc_tlv id ok c) else 0))
= let b = Seq.append (enc_tlv id ok c) rest in
  let ie = IE.asn1_id_enc id in
  let hdr = enc_hdr ok (Seq.length c) in
  let r1 = hdr `Seq.append` c in
  enc_tlv_id id ok c rest;
  Seq.append_assoc ie r1 rest;
  Seq.append_slices ie (Seq.append r1 rest);
  assert (Seq.slice b (Seq.length ie) (Seq.length b) == Seq.append r1 rest);
  L.frame_len_tlv_size b;
  if ok && Seq.length c < 4294967296
  then L.lc_size_tlv c rest
  else begin
    Seq.append_assoc hdr c rest;
    hdr_bad_none ok (Seq.length c) (Seq.append c rest)
  end

let frame_len_value (v: asn1_value) (rest: bytes)
: Lemma (SI.frame_len (Seq.append (asn1_value_enc v) rest) ==
    (if Str.hdr_ok v then Seq.length (asn1_value_enc v) else 0))
= match v with
  | ASN1_VALUE_PRIMITIVE id b -> frame_len_tlv id (PRIMITIVE? id.f) b rest
  | ASN1_VALUE_CONSTRUCTED id l -> frame_len_tlv id (CONSTRUCTED? id.f) (asn1_value_list_enc l) rest

let nat_le_zero (x: nat) : Lemma (requires x <= 0) (ensures x == 0) = ()

let frame_len_empty () : Lemma (SI.frame_len Seq.empty == 0) =
  SI.frame_len_le Seq.empty;
  nat_le_zero (SI.frame_len Seq.empty)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let rec vins_enc (lt: SI.lt_t) (vlt: vlt_t) (e l: list asn1_value)
: Lemma
  (requires (forall w . lt (asn1_value_enc w) (asn1_value_list_enc e) == vlt w e))
  (ensures (SI.ins lt (asn1_value_list_enc e) (asn1_value_list_enc l) == asn1_value_list_enc (vins vlt e l)))
  (decreases l)
= let ee = asn1_value_list_enc e in
  let r = asn1_value_list_enc l in
  SI.ins_unfold lt ee r;
  match l with
  | [] -> frame_len_empty (); Seq.append_empty_r ee
  | w :: q ->
    let rq = asn1_value_list_enc q in
    frame_len_value w rq;
    vle_append e l;
    if Str.hdr_ok w
    then begin
      Seq.append_slices (asn1_value_enc w) rq;
      assert (Seq.slice r 0 (Seq.length (asn1_value_enc w)) == asn1_value_enc w);
      assert (Seq.slice r (Seq.length (asn1_value_enc w)) (Seq.length r) == rq);
      if vlt w e
      then vins_enc lt vlt e q
      else ()
    end
    else ()
#pop-options

let parse_id_empty () : Lemma (SI.parse_id Seq.empty == None) =
  PSL.identifier_nonempty Seq.empty

let parse_id_value (w: asn1_value) : Lemma (SI.parse_id (asn1_value_enc w) == Some (value_id w)) =
  value_parse_id w Seq.empty;
  Seq.append_empty_r (asn1_value_enc w)

let lt_tag_values (w: asn1_value) (e: list asn1_value)
: Lemma (SI.lt_tag (asn1_value_enc w) (asn1_value_list_enc e) == vlt_tag w e)
= parse_id_value w;
  match e with
  | [] -> parse_id_empty ()
  | v :: q -> value_parse_id v (asn1_value_list_enc q)

let vins_tag_enc (e l: list asn1_value)
: Lemma (SI.ins SI.lt_tag (asn1_value_list_enc e) (asn1_value_list_enc l) == asn1_value_list_enc (vins vlt_tag e l))
= Classical.forall_intro (fun w -> lt_tag_values w e);
  vins_enc SI.lt_tag vlt_tag e l

let vins_lex_enc (e l: list asn1_value)
: Lemma (SI.ins SI.lt_lex (asn1_value_list_enc e) (asn1_value_list_enc l) == asn1_value_list_enc (vins vlt_lex e l))
= vins_enc SI.lt_lex vlt_lex e l

let rec vsacc_enc (acc l: list asn1_value)
: Lemma (ensures (SI.sort_acc SI.lt_lex RR.id_enc (asn1_value_list_enc acc) (List.map asn1_value_enc l) == asn1_value_list_enc (vsacc acc l)))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    vle_single a;
    vins_lex_enc [a] acc;
    vsacc_enc (vins vlt_lex [a] acc) q

let vsort_lex_enc (l: list asn1_value)
: Lemma (SI.sort_list SI.lt_lex RR.id_enc (List.map asn1_value_enc l) == asn1_value_list_enc (vsort_lex l))
= vsacc_enc [] l

let rec enc_list_values (l: list asn1_value)
: Lemma (ensures (W.enc_list RR.id_enc (List.map asn1_value_enc l) == asn1_value_list_enc l)) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> enc_list_values q

(* At most one value, inserted *)
let vsort_tag_cons (d r: list asn1_value)
: Lemma (requires (List.length d <= 1))
  (ensures (vsort_tag (List.append d r) == vins vlt_tag d (vsort_tag r)))
= match d with
  | [] -> vins_nil (vsort_tag r)
  | [_] -> ()

let vsort_tag_one (d: list asn1_value)
: Lemma (requires (List.length d <= 1)) (ensures (vsort_tag d == d))
= match d with
  | [] -> ()
  | [_] -> ()

(* Values of well-formed identifiers *)

let enc_mk_prim (id: asn1_id_t) (c: asn1_octetstring_t)
: Lemma (requires (asn1_any_id_valid id /\ PRIMITIVE? id.f))
  (ensures (asn1_value_enc (mk_prim id c) == enc_tlv id true c))
= ()

let enc_mk_cons (id: asn1_id_t) (l: list asn1_value)
: Lemma (requires (asn1_any_id_valid id /\ CONSTRUCTED? id.f))
  (ensures (asn1_value_enc (mk_cons id l) == enc_tlv id true (asn1_value_list_enc l)))
= ()

let enc_mk_encap (id: asn1_id_t) (w: asn1_value)
: Lemma (requires (asn1_any_id_valid id /\ encap_ok id))
  (ensures (asn1_value_enc (mk_encap id w) == enc_tlv id true (asn1_value_enc w)))
= vle_single w

(* Terminals *)

let rec rb_term_rterm (id: asn1_id_t) (k: asn1_terminal_k) (y: asn1_raw_terminal_t k)
: Lemma (requires (wf_terminal id k)) (ensures (rb_term id k y == asn1_value_enc (rterm id k y))) (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_raw_terminal_t k2);
    let y2 = coerce_eq #(asn1_raw_terminal_t k) #(asn1_raw_terminal_t k2) () y in
    rb_term_rterm id2 k2 y2;
    enc_mk_encap id (rterm id2 k2 y2)
  | _ -> ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let rec raw_key_enc_rb (id: asn1_id_t) (k: asn1_terminal_k) (l: asn1_key_lit k)
: Lemma (requires (In.adb_key_supported k)) (ensures (WA.raw_key_enc id k l == rb_term id k (raw_key_of_lit k l))) (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    raw_key_enc_rb id2 k2 (In.prefixed_lit id2 k2 l)
  | _ ->
    JK.raw_key_enc_c id k l;
    DE.leaf_key_c k l;
    raw_leaf_enc_forget k (key_of_lit k l)
#pop-options

let rb_default_eq (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k) (z: asn1_raw_terminal_t k)
: Lemma (requires (wf_terminal id0 k /\ In.adb_key_supported k))
  (ensures (rb_default id0 k defl z == (if z = raw_key_of_lit k defl then Seq.empty else rb_term id0 k z)))
= raw_key_enc_rb id0 k defl;
  rb_term_rterm id0 k z;
  rb_term_rterm id0 k (raw_key_of_lit k defl);
  rterm_forget id0 k (key_of_lit k defl);
  Classical.move_requires (asn1_value_enc_inj (rterm id0 k z)) (rterm id0 k (raw_key_of_lit k defl));
  Classical.move_requires (rterm_mixed id0 k z) (key_of_lit k defl)

let sdec_length (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk)
: Lemma (List.length (sdec true dk y) <= 1)
= match dk with
  | ASN1_PLAIN_ILC k -> ()
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    (match y' with None -> () | Some z -> ())
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with None -> () | Some z -> ())
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with None -> () | Some z -> ())

(* The bytes are the encoding of the sorted value *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec c_content (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k)
: Lemma (requires (wf_content id k /\ In.supported_content k))
  (ensures (rb_content id k y == asn1_value_enc (scontent true id k y))) (decreases %[k; 3])
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> rb_term_rterm id k' y
  | ASN1_TERMINAL k' -> rb_term_rterm id k' y
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    c_items_f items y;
    enc_mk_cons id (sitems true items y)
  | ASN1_SET _ items _ ->
    c_items_t items y;
    enc_mk_cons id (vsort_tag (sitems true items y))
  | ASN1_SEQUENCE_OF _ k' ->
    c_list k' y;
    enc_list_values (slist true k' y);
    enc_mk_cons id (slist true k' y)
  | ASN1_SET_OF _ k' ->
    c_list k' y;
    vsort_lex_enc (slist true k' y);
    enc_mk_cons id (vsort_lex (slist true k' y))
  | ASN1_PREFIXED k' ->
    c_value k' y;
    enc_mk_encap id (svalue true k' y)
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None ->
      let k = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf' in
      let ssfx (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key :: sls true key_k ls key y
      in
      let rsfx (s: make_gen_choice_type (raw_any_t_core key_k ls)) : GTot bytes =
        let (| key, y |) = s in
        rb_ls kid key_k ls key y
      in
      assert (scontent true id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y == mk_cons id (sitems_any true prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, y |) = s in rterm kid key_k key :: sls true key_k ls key y) <: list asn1_value) y))
        by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
      assert (rb_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y == enc_tlv id true (rb_items_any prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, y |) = s in rb_ls kid key_k ls key y) <: GTot bytes) y))
        by (FStar.Tactics.norm [delta_only [`%rb_content]; zeta; iota]; FStar.Tactics.trefl ());
      let prf (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Lemma (rsfx s == asn1_value_list_enc (ssfx s)) =
        let (| key, z |) = s in
        c_ls kid key_k ls key z
      in
      FStar.Classical.forall_intro prf;
      c_items_any prefix rsfx ssfx y;
      enc_mk_cons id (sitems_any true prefix ssfx y)
    | Some (| fbids, fbitems |) ->
      let k = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf' in
      fb_precedes k;
      let ssfx (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key ::
        sls_fb true key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> sitems true fbitems z) key y
      in
      let rsfx (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : GTot bytes =
        let (| key, y |) = s in
        rb_ls_fb kid key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> rb_items false fbitems z) key y
      in
      assert (scontent true id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == mk_cons id (sitems_any true prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, y |) = s in rterm kid key_k key :: sls_fb true key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> sitems true fbitems z) key y) <: list asn1_value) y))
        by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
      assert (rb_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == enc_tlv id true (rb_items_any prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, y |) = s in rb_ls_fb kid key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> rb_items false fbitems z) key y) <: GTot bytes) y))
        by (FStar.Tactics.norm [delta_only [`%rb_content]; zeta; iota]; FStar.Tactics.trefl ());
      let prf (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Lemma (rsfx s == asn1_value_list_enc (ssfx s)) =
        let (| key, z |) = s in
        c_ls_fb k kid key_k ls fbitems key z
      in
      FStar.Classical.forall_intro prf;
      c_items_any prefix rsfx ssfx y;
      enc_mk_cons id (sitems_any true prefix ssfx y)
    end

and c_list (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k))
: Lemma (requires (wf k /\ In.supported_k k))
  (ensures (rb_list k l == List.map asn1_value_enc (slist true k l))) (decreases %[k; 3; l])
= match l with
  | [] -> ()
  | a :: q -> c_value k a; c_list k q

and c_value (#s: _) (k: asn1_k s) (y: asn1_raw_t k)
: Lemma (requires (wf k /\ In.supported_k k))
  (ensures (rb k y == asn1_value_enc (svalue true k y))) (decreases %[k; 2])
= match k with
  | ASN1_ILC id k' -> c_content id k' y
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let (| id, z |) = y' in
    c_choice lc id z
  | ASN1_ANY_ILC -> ()

and c_choice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc))
: Lemma (requires (wf_lc lc /\ In.supported_lc lc))
  (ensures (rb_choice lc id y == asn1_value_enc (schoice true lc id y))) (decreases %[lc; 0])
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then c_content id c y
    else c_choice tl id y

and c_ls (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_raw_terminal_t key_k) (y: idlookup_t key (raw_any_t_core key_k ls))
: Lemma (requires (wf_terminal kid key_k /\ In.adb_key_supported key_k /\ wf_ls ls /\ In.supported_ls ls))
  (ensures (rb_ls kid key_k ls key y == asn1_value_list_enc (rterm kid key_k key :: sls true key_k ls key y))) (decreases %[ls; 0])
= match ls with
  | [] -> false_elim ()
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then begin
      raw_key_enc_rb kid key_k key';
      rb_term_rterm kid key_k key;
      c_items_f items y
    end
    else c_ls kid key_k tl key y

and c_ls_fb (k0: asn1_content_k) (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_raw_terminal_t key_k) (y: idlookup_with_fallback_t key (raw_any_t_core key_k ls) (raw_items_t fbitems))
: Lemma
  (requires (wf_terminal kid key_k /\ In.adb_key_supported key_k /\ wf_ls ls /\ In.supported_ls ls /\ wf_items fbitems /\ In.supported_items fbitems))
  (ensures (
    rb_ls_fb kid key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> rb_items false fbitems z) key y ==
    asn1_value_list_enc (rterm kid key_k key :: sls_fb true key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> sitems true fbitems z) key y)))
  (decreases %[k0; 1; ls])
= match ls with
  | [] -> rb_term_rterm kid key_k key; c_items_f fbitems y
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then begin
      raw_key_enc_rb kid key_k key';
      rb_term_rterm kid key_k key;
      c_items_f items y
    end
    else c_ls_fb k0 kid key_k tl fbitems key y

and c_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk)
: Lemma (requires (wf_dec dk /\ In.supported_dec dk))
  (ensures (rb_dec dk y == asn1_value_list_enc (sdec true dk y))) (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k -> c_value k y; vle_single (svalue true k y)
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    (match y' with None -> () | Some z -> c_value k z; vle_single (svalue true k z))
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with
     | None -> ()
     | Some z -> rb_default_eq id k defv_l z; rb_term_rterm id k z; vle_single (rterm id k z))
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with
     | None -> ()
     | Some z -> rb_default_eq id k defv_l z; rb_term_rterm id k z; vle_single (rterm id k z))

and c_items_f (#ids: _) (items: asn1_gen_items_l ids) (y: raw_items_t items)
: Lemma (requires (wf_items items /\ In.supported_items items))
  (ensures (rb_items false items y == asn1_value_list_enc (sitems true items y))) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> c_dec dk y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, c) = y' in
    c_dec dk a; c_items_f tl c;
    vle_append (sdec true dk a) (sitems true tl c)

and c_items_t (#ids: _) (items: asn1_gen_items_l ids) (y: raw_items_t items)
: Lemma (requires (wf_items items /\ In.supported_items items))
  (ensures (rb_items true items y == asn1_value_list_enc (vsort_tag (sitems true items y)))) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> c_dec dk y; sdec_length dk y; vsort_tag_one (sdec true dk y)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, c) = y' in
    c_dec dk a; c_items_t tl c;
    sdec_length dk a;
    vsort_tag_cons (sdec true dk a) (sitems true tl c);
    vins_tag_enc (sdec true dk a) (vsort_tag (sitems true tl c))

and c_items_any (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (sfx: sfx_t -> GTot bytes) (ssfx: sfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items sfx_t)
: Lemma
  (requires (wf_items items /\ In.supported_items items /\ (forall z . sfx z == asn1_value_list_enc (ssfx z))))
  (ensures (rb_items_any items sfx y == asn1_value_list_enc (sitems_any true items ssfx y))) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & sfx_t = y in
    let (a, c) = y' in
    c_dec dk a;
    vle_append (sdec true dk a) (ssfx c)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, c) = y' in
    c_dec dk a; c_items_any tl sfx ssfx c;
    vle_append (sdec true dk a) (sitems_any true tl ssfx c)
#pop-options

(* Correctness of the bytes w.r.t. `check_ser` *)

let raw_ok (#s: _) (k: asn1_k s) : prop = wf k /\ In.supported_k k

let kacc_conforms (#s: _) (k: asn1_k s) (v: asn1_value)
: Lemma (L.acc #asn1_strong_parser_kind (asn1_as_parser k) (asn1_value_enc v) <==> conforms k v == true)
= ()

(* If the bytes are accepted by the typed parser, then they are the
   encoding of the checked value *)
let rb_acc (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (y: asn1_raw_t k)
: Lemma
  (requires (L.acc #asn1_strong_parser_kind (asn1_as_parser k) (rb k y)))
  (ensures (Some? (check_ser k () y) /\ rb k y == Ser.asn1_enc k (Some?.v (check_ser k () y))))
= c_value k y;
  kacc_conforms k (svalue true k y);
  Str.vconf_correct k (svalue true k y);
  svalue_rvalue true k y;
  let b = asn1_value_enc (rvalue k y) in
  Ser.asn1_as_parser_consumed k b;
  let Some (x, _) = parse (asn1_as_parser k) b in
  rvalue_parse k () y x;
  rvalue_check_ser k () y (Some?.v (check_ser k () y))

(* Conversely, the checked value is encoded by the bytes, which are thus
   accepted by the typed parser *)
let rb_check_ser (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (y: asn1_raw_t k)
: Lemma
  (requires (Some? (check_ser k () y)))
  (ensures (rb k y == Ser.asn1_enc k (Some?.v (check_ser k () y)) /\ L.acc #asn1_strong_parser_kind (asn1_as_parser k) (rb k y)))
= let x = Some?.v (check_ser k () y) in
  rvalue_check_ser k () y x;
  Ser.encodable_conforms k x;
  asn1_value_enc_inj (rvalue k y) (to_value k x);
  f_value k y;
  Str.vconf_correct k (svalue false k y);
  svalue_rvalue false k y;
  c_value k y;
  kacc_conforms k (svalue true k y)

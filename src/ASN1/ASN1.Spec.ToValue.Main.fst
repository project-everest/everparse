module ASN1.Spec.ToValue.Main

(* Soundness of `to_value` w.r.t. the typed parsers: for every well-formed
   schema `k`, the bytes consumed by the typed parser `asn1_as_parser k` are
   exactly the generic encoding of the generic value of the parsed typed
   value (`top_lemma` below, restated as `asn1_as_parser_consumed` in
   ASN1.Spec.Serializer.) *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.List
open LowParse.Tot.VLGen
open LowParse.Tot.Defaultable

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.IdentifierU32.Enc
open ASN1.Spec.LengthU32
open ASN1.Spec.Value
open ASN1.Spec.Value.Enc
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.SetComponents
open ASN1.Spec.Any
open ASN1.Spec.Set
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Conformance
open ASN1.Spec.ToValue
open ASN1.Spec.ToValue.Sound
open ASN1.Spec.ToValue.Set

module U32 = FStar.UInt32
module Seq = FStar.Seq
module List = FStar.List.Tot
module RV = LowParse.Spec.RecursiveVLGen

(* Generic helpers *)

let filter_esound (#k: parser_kind) (#t: Type) (p: parser k t) (f: t -> Tot bool) (g: t -> GTot bytes)
: Lemma
  (requires (esound p g))
  (ensures (esound (parse_filter p f) (fun x -> g x)))
= let prf (b: bytes) : Lemma (match parse (parse_filter p f) b with
    | Some (x, n) -> Seq.slice b 0 n == g x
    | None -> True)
  = parse_filter_eq p f b
  in
  Classical.forall_intro prf

(* ANY, after its identifier *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let any_twin_v (id: asn1_id_t) (b: bytes)
: Lemma
  (match parse (parse_asn1_value_twin id) b with
   | Some (v, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_enc v
   | None -> True)
= if asn1_any_id_valid id
  then begin
    twin_eq id b;
    parse_len_consumed b;
    match parse parse_asn1_length_u32_t b with
    | None -> ()
    | Some (len, sz) ->
      if Seq.length b < sz + U32.v len
      then ()
      else begin
        let ct = Seq.slice b sz (sz + U32.v len) in
        rec_vlgen_body_eq id ct;
        assert (U32.uint_to_t (U32.v len) == len);
        Seq.lemma_eq_elim (Seq.slice b 0 (sz + U32.v len)) (Seq.slice b 0 sz `Seq.append` ct);
        assert (enc_hdr true (Seq.length ct) == enc_len len);
        if CONSTRUCTED? id.f
        then begin
          parse_asn1_value_list_consumed ct;
          match parse (tot_parse_list pv) ct with
          | Some (l, _) ->
            assert (synth_asn1_value_twin id (RV.RNode l) == ASN1_VALUE_CONSTRUCTED id l);
            assert (asn1_value_enc (ASN1_VALUE_CONSTRUCTED id l) == enc_tlv id true ct)
          | None -> ()
        end
        else begin
          assert (synth_asn1_value_twin id (RV.RLeaf ct) == ASN1_VALUE_PRIMITIVE id ct);
          assert (asn1_value_enc (ASN1_VALUE_PRIMITIVE id ct) == enc_tlv id true ct)
        end
      end
  end
#pop-options

let any_esound ()
: Lemma
  (esound parse_asn1_value asn1_value_enc /\ esound_twin parse_asn1_value_twin asn1_value_enc)
= Classical.forall_intro parse_asn1_value_consumed';
  Classical.forall_intro_2 any_twin_v

(* SET *)

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let set_content_esound (id: asn1_id_t) (ids: id_decs) (items: asn1_gen_items_l ids) (pf: squash (asn1_set_k_wf ids))
: Lemma
  (requires (wf_content id (ASN1_SET ids items pf) /\ items_esound (asn1_sequence_as_parser items)))
  (ensures (content_esound id (ASN1_SET ids items pf)))
= let k = ASN1_SET ids items pf in
  let its = asn1_sequence_as_parser items in
  items_tagged_intro items;
  set_parser_esound its;
  let prf (x: asn1_content_t k) : Lemma (content_enc id k x == asn1_value_list_enc (sort_by_tag (seq_values its x))) =
    items_seq_values items x;
    mk_cons_shape id (sort_by_tag (items_to_values items x))
  in
  Classical.forall_intro prf;
  esound_ext (asn1_content_as_parser k) (fun x -> asn1_value_list_enc (sort_by_tag (seq_values its x))) (content_enc id k)
#pop-options

(* Per-case lemmas *)

let esound_twin_ext (#k: parser_kind) (#t: Type) (fp: asn1_id_t -> parser k t) (g1 g2: t -> GTot bytes)
: Lemma
  (requires (esound_twin fp g1 /\ (forall x. g1 x == g2 x)))
  (ensures (esound_twin fp g2))
= ()

let top_esound (#s: _) (k: asn1_k s) : prop =
  esound (asn1_as_parser k) (fun x -> asn1_value_enc (to_value k x)) /\
  esound_twin (snd (asn1_as_parser_twin k)) (fun x -> asn1_value_enc (to_value k x))

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let terminal_content_esound (id: asn1_id_t) (k': asn1_terminal_k)
: Lemma
  (requires (wf_content id (ASN1_TERMINAL k')))
  (ensures (content_esound id (ASN1_TERMINAL k')))
= terminal_esound id k';
  let prf (x: asn1_terminal_t k') : Lemma (content_enc id (ASN1_TERMINAL k') x == tbytes id k' x) = () in
  Classical.forall_intro prf;
  esound_ext (asn1_terminal_as_parser k') (tbytes id k') (content_enc id (ASN1_TERMINAL k'))

let restricted_content_esound (id: asn1_id_t) (k': asn1_terminal_k) (r: asn1_restriction k')
: Lemma
  (requires (wf_content id (ASN1_RESTRICTED_TERMINAL k' r)))
  (ensures (content_esound id (ASN1_RESTRICTED_TERMINAL k' r)))
= terminal_esound id k';
  filter_esound (asn1_terminal_as_parser k') (restriction_pred r) (tbytes id k');
  let prf (x: asn1_content_t (ASN1_RESTRICTED_TERMINAL k' r)) : Lemma (content_enc id (ASN1_RESTRICTED_TERMINAL k' r) x == tbytes id k' x) = () in
  Classical.forall_intro prf;
  esound_ext (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k' r)) (fun x -> tbytes id k' x) (content_enc id (ASN1_RESTRICTED_TERMINAL k' r))

let sequence_content_esound (id: asn1_id_t) (ids: id_decs {asn1_sequence_k_wf ids}) (items: asn1_gen_items_l ids)
: Lemma
  (requires (wf_content id (ASN1_SEQUENCE (| ids, items |)) /\ items_esound (asn1_sequence_as_parser items)))
  (ensures (content_esound id (ASN1_SEQUENCE (| ids, items |))))
= let k = ASN1_SEQUENCE (| ids, items |) in
  seq_parser_esound (asn1_sequence_as_parser items);
  let prf (x: asn1_content_t k) : Lemma (content_enc id k x == asn1_value_list_enc (seq_values (asn1_sequence_as_parser items) x)) =
    items_seq_values items x;
    mk_cons_shape id (items_to_values items x)
  in
  Classical.forall_intro prf;
  esound_ext (asn1_content_as_parser k) (fun x -> asn1_value_list_enc (seq_values (asn1_sequence_as_parser items) x)) (content_enc id k)

let sequence_of_content_esound (id: asn1_id_t) (ne: bool) (#s: _) (k': asn1_k s)
: Lemma
  (requires (wf_content id (ASN1_SEQUENCE_OF ne k') /\ top_esound k'))
  (ensures (content_esound id (ASN1_SEQUENCE_OF ne k')))
= let k = ASN1_SEQUENCE_OF ne k' in
  sized_list_esound ne (asn1_as_parser k') (to_value k');
  let prf (x: asn1_content_t k) : Lemma (content_enc id k x == asn1_value_list_enc (list_values (to_value k') x)) =
    list_to_values_eq k' x;
    mk_cons_shape id (list_to_values k' x)
  in
  Classical.forall_intro prf;
  esound_ext (asn1_content_as_parser k) (fun l -> asn1_value_list_enc (list_values (to_value k') l)) (content_enc id k)

let set_of_content_esound (id: asn1_id_t) (ne: bool) (#s: _) (k': asn1_k s)
: Lemma
  (requires (wf_content id (ASN1_SET_OF ne k') /\ top_esound k'))
  (ensures (content_esound id (ASN1_SET_OF ne k')))
= let k = ASN1_SET_OF ne k' in
  sized_set_esound ne (asn1_as_parser k') (to_value k');
  let prf (x: asn1_content_t k) : Lemma (content_enc id k x == asn1_value_list_enc (list_values (to_value k') x)) =
    list_to_values_eq k' x;
    mk_cons_shape id (list_to_values k' x)
  in
  Classical.forall_intro prf;
  esound_ext (asn1_content_as_parser k) (fun l -> asn1_value_list_enc (list_values (to_value k') l)) (content_enc id k)

let prefixed_content_esound (id: asn1_id_t) (#s: _) (k': asn1_k s)
: Lemma
  (requires (wf_content id (ASN1_PREFIXED k') /\ top_esound k'))
  (ensures (content_esound id (ASN1_PREFIXED k')))
= let k = ASN1_PREFIXED k' in
  let prf (x: asn1_content_t k) : Lemma (content_enc id k x == asn1_value_enc (to_value k' x)) =
    mk_encap_shape id (to_value k' x)
  in
  Classical.forall_intro prf;
  esound_ext (asn1_content_as_parser k) (fun x -> asn1_value_enc (to_value k' x)) (content_enc id k)

let ilc_top_esound (id: asn1_id_t) (k': asn1_content_k)
: Lemma
  (requires (content_esound id k'))
  (ensures (top_esound (ASN1_ILC id k')))
= let k = ASN1_ILC id k' in
  let p = asn1_content_as_parser k' in
  ilc_esound id p (content_enc id k');
  lc_twin_esound id p (content_enc id k');
  let prf (x: asn1_t k) : Lemma (asn1_value_enc (to_value k x) == enc_tlv id true (content_enc id k' x)) =
    content_value_enc id k' x
  in
  Classical.forall_intro prf;
  assert (asn1_as_parser k == parse_asn1_ILC id p);
  assert (snd (asn1_as_parser_twin k) == parse_asn1_ILC_twin id p);
  esound_ext (asn1_as_parser k) (fun x -> enc_tlv id true (content_enc id k' x)) (fun x -> asn1_value_enc (to_value k x))
  ;esound_twin_ext (snd (asn1_as_parser_twin k)) (fun x -> enc_tlv id true (content_enc id k' x)) (fun x -> asn1_value_enc (to_value k x))

let to_value_choice (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.noRepeats (List.map fst lc))) (x: asn1_t (ASN1_CHOICE_ILC lc pf))
: Lemma (let x' : make_gen_choice_type (asn1_lc_t lc) = x in
    to_value (ASN1_CHOICE_ILC lc pf) x == choice_to_value lc (dfst x') (dsnd x'))
= ()

let choice_top_esound (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.noRepeats (List.map fst lc)))
: Lemma
  (requires (lc_esound lc))
  (ensures (top_esound (ASN1_CHOICE_ILC lc pf)))
= let k = ASN1_CHOICE_ILC lc pf in
  let lp = asn1_lc_as_parser lc in
  let prf1 (b: bytes) : Lemma (match parse (asn1_as_parser k) b with
    | Some (x, n) -> Seq.slice b 0 n == asn1_value_enc (to_value k x)
    | None -> True)
  = assert (asn1_as_parser k == make_asn1_choice_parser lc pf k lp);
    choice_v_at lc b;
    match parse (make_gen_choice_strong_parser parse_asn1_identifier_U32 lp) b with
    | Some (v, _) -> to_value_choice lc pf v
    | None -> ()
  in
  let prf2 (id: asn1_id_t) (b: bytes) : Lemma (match parse (snd (asn1_as_parser_twin k) id) b with
    | Some (x, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_enc (to_value k x)
    | None -> True)
  = assert (snd (asn1_as_parser_twin k) id == make_asn1_choice_parser_twin_cases lc pf k lp id);
    choice_twin_v lc id b;
    match parse (parse_tagged_union_payload (project_tags lp) (make_gen_choice_strong_payload_parser lp) id) b with
    | Some (v, _) -> to_value_choice lc pf v
    | None -> ()
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2;
  assert (esound (asn1_as_parser k) (fun x -> asn1_value_enc (to_value k x)));
  assert (esound_twin (snd (asn1_as_parser_twin k)) (fun x -> asn1_value_enc (to_value k x)))

let any_top_esound ()
: Lemma (top_esound ASN1_ANY_ILC)
= any_esound ();
  assert (asn1_as_parser ASN1_ANY_ILC == parse_asn1_value);
  assert (snd (asn1_as_parser_twin ASN1_ANY_ILC) == parse_asn1_value_twin)
    by (FStar.Tactics.norm [delta_only [`%asn1_as_parser_twin; `%parse_asn1_anyILC_twin; `%snd]; zeta; iota]; FStar.Tactics.trefl ());
  esound_ext parse_asn1_value asn1_value_enc (fun (x: asn1_t ASN1_ANY_ILC) -> asn1_value_enc (to_value ASN1_ANY_ILC x));
  esound_twin_ext parse_asn1_value_twin asn1_value_enc (fun (x: asn1_t ASN1_ANY_ILC) -> asn1_value_enc (to_value ASN1_ANY_ILC x))

let default_terminal_esound (id: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_terminal_t k)
: Lemma
  (requires (wf_terminal id k))
  (ensures (item_esound (asn1_decorated_as_parser_twin (ASN1_DEFAULT_TERMINAL id #k defv))))
= terminal_esound id k;
  let it = asn1_decorated_as_parser_twin (ASN1_DEFAULT_TERMINAL id #k defv) in
  let fp = parse_asn1_ILC_twin id #(ASN1_TERMINAL k) (asn1_terminal_as_parser k) in
  lc_twin_esound id #(ASN1_TERMINAL k) (asn1_terminal_as_parser k) (tbytes id k);
  assert (Mkgendcparser?.fp it == fp);
  let prf (x: asn1_terminal_t k) : Lemma (enc_tlv id true (tbytes id k x) == asn1_value_enc (pure_value it x)) =
    terminal_value_enc id k x
  in
  Classical.forall_intro prf;
  esound_twin_ext fp (fun x -> enc_tlv id true (tbytes id k x)) (fun x -> asn1_value_enc (pure_value it x))

let default_restricted_terminal_esound (id: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_terminal_t k {restriction_pred r defv = true})
: Lemma
  (requires (wf_terminal id k))
  (ensures (item_esound (asn1_decorated_as_parser_twin (ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv))))
= terminal_esound id k;
  filter_esound (asn1_terminal_as_parser k) (restriction_pred r) (tbytes id k);
  let it = asn1_decorated_as_parser_twin (ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv) in
  let p : asn1_weak_parser (asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) = weaken _ ((asn1_terminal_as_parser k) `parse_filter` (restriction_pred r)) in
  let fp = parse_asn1_ILC_twin id #(ASN1_RESTRICTED_TERMINAL k r) p in
  lc_twin_esound id #(ASN1_RESTRICTED_TERMINAL k r) p (fun x -> tbytes id k x);
  assert (Mkgendcparser?.fp it == fp);
  let prf (x: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) : Lemma (enc_tlv id true (tbytes id k x) == asn1_value_enc (pure_value it x)) =
    terminal_value_enc id k x
  in
  Classical.forall_intro prf;
  esound_twin_ext fp (fun x -> enc_tlv id true (tbytes id k x)) (fun x -> asn1_value_enc (pure_value it x))

let plain_esound (#s: _) (k: asn1_k s)
: Lemma
  (requires (top_esound k))
  (ensures (item_esound (asn1_decorated_as_parser_twin (ASN1_PLAIN_ILC k))))
= ()

let option_esound (#s: _) (k: asn1_k s)
: Lemma
  (requires (top_esound k))
  (ensures (item_esound (asn1_decorated_as_parser_twin (ASN1_OPTION_ILC k))))
= ()
#pop-options

(* The main lemma *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec content_lemma (id: asn1_id_t) (k: asn1_content_k)
: Lemma
  (requires (wf_content id k))
  (ensures (content_esound id k))
  (decreases k)
= match k with
  | ASN1_RESTRICTED_TERMINAL k' r -> restricted_content_esound id k' r
  | ASN1_TERMINAL k' -> terminal_content_esound id k'
  | ASN1_SEQUENCE gitems ->
    let (| ids, items |) = gitems in
    items_lemma items;
    sequence_content_esound id ids items
  | ASN1_SET ids items pf ->
    items_lemma items;
    set_content_esound id ids items pf
  | ASN1_SEQUENCE_OF ne k' ->
    top_lemma k';
    sequence_of_content_esound id ne k'
  | ASN1_SET_OF ne k' ->
    top_lemma k';
    set_of_content_esound id ne k'
  | ASN1_PREFIXED k' ->
    top_lemma k';
    prefixed_content_esound id k'
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    items_lemma prefix;
    ls_lemma (asn1_key_lit key_k) ls;
    begin match ofb with
    | None -> adb_content_esound id idp prefix kid key_k ls pf pf'
    | Some fb ->
      let (| fbids, fbitems |) = fb in
      items_lemma fbitems;
      adb_fb_content_esound id idp prefix kid key_k ls fbids fbitems pf pf'
    end

and ls_lemma (t: eqtype) (ls: list (t & asn1_gen_items_lk))
: Lemma
  (requires (wf_ls ls))
  (ensures (ls_esound ls))
  (decreases ls)
= match ls with
  | [] -> ()
  | h :: tl ->
    let (_, y) = h in
    items_lemma (dsnd y);
    ls_lemma t tl

and lc_lemma (lc: list (asn1_id_t & asn1_content_k))
: Lemma
  (requires (wf_lc lc))
  (ensures (lc_esound lc))
  (decreases lc)
= match lc with
  | [] -> ()
  | h :: tl ->
    let (x, y) = h in
    content_lemma x y;
    lc_lemma tl

and top_lemma (#s: _) (k: asn1_k s)
: Lemma
  (requires (wf k))
  (ensures (top_esound k))
  (decreases k)
= match k with
  | ASN1_ILC id k' ->
    content_lemma id k';
    ilc_top_esound id k'
  | ASN1_CHOICE_ILC lc pf ->
    lc_lemma lc;
    choice_top_esound lc pf
  | ASN1_ANY_ILC -> any_top_esound ()

and dec_lemma (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma
  (requires (wf_dec dk))
  (ensures (item_esound (asn1_decorated_as_parser_twin dk)))
  (decreases dk)
= match dk with
  | ASN1_PLAIN_ILC k -> top_lemma k; plain_esound k
  | ASN1_OPTION_ILC k -> top_lemma k; option_esound k
  | ASN1_DEFAULT_TERMINAL id defv -> default_terminal_esound id defv
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id r defv -> default_restricted_terminal_esound id r defv

and items_lemma (#ids: _) (ls: asn1_gen_items_l ids)
: Lemma
  (requires (wf_items ls))
  (ensures (items_esound (asn1_sequence_as_parser ls)))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    dec_lemma dk;
    items_lemma tl
#pop-options

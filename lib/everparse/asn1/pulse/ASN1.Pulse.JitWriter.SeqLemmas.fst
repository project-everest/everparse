module ASN1.Pulse.JitWriter.SeqLemmas

(* Lemmas for the exact JIT writers of SEQUENCE components
   (ASN1.Pulse.JitWriter) *)

open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Sequence
open ASN1.Pulse.JitWriter.Lemmas

module SB = LowParse.Spec.Base
module Sq = ASN1.Pulse.Sequence
module PSL = ASN1.Pulse.ParseSequence.Lemmas
module In = ASN1.Pulse.Interpreter

(* SEQUENCE: converses, from the well-formedness of the tags
   (`asn1_sequence_k_wf`) instead of runtime checks on identifiers. The
   raw bytes of a component other than ANY are either one TLV with one of
   its identifiers, or empty if the component is absent (`dfe`); and those
   of the components after an absent one do not start with any of its
   identifiers (`avoids`). *)

let avoids (s: FStar.Set.set asn1_id_t) (x: bytes) : prop =
  Seq.length x == 0 \/ (match pid x with Some (id, _) -> ~ (FStar.Set.mem id s) | None -> True)

let dfe (hd: gen_decorated_parser_twin) (x: bytes) : prop =
  framed (Sq.item_set hd) x \/
  (x == Seq.empty /\ ~ (PLAIN? (Sq.item_dec hd)) /\ Some? (generate_defaultable_item hd))

let hs (hd: gen_decorated_parser_twin) : FStar.Set.set asn1_id_t =
  if PLAIN? (Sq.item_dec hd) then FStar.Set.empty else Sq.item_set hd

let rec wf'_sub (l: id_decs) (s1 s2: FStar.Set.set asn1_id_t)
: Lemma (requires (asn1_sequence_k_wf' l s2 /\ FStar.Set.subset s1 s2)) (ensures (asn1_sequence_k_wf' l s1))
  (decreases l)
= match l with
  | [] -> ()
  | (s', d) :: tl ->
    if PLAIN? d then () else wf'_sub tl (FStar.Set.union s1 s') (FStar.Set.union s2 s')

let wf'_wf (l: id_decs) (s: FStar.Set.set asn1_id_t)
: Lemma (requires (asn1_sequence_k_wf' l s)) (ensures (asn1_sequence_k_wf l))
= match l with
  | [] -> ()
  | (s', d) :: tl ->
    if PLAIN? d then () else wf'_sub tl s' (FStar.Set.union s s')

let wf_tl (hd: FStar.Set.set asn1_id_t & asn1_decorator) (tl: id_decs)
: Lemma (requires (asn1_sequence_k_wf (hd :: tl))) (ensures (asn1_sequence_k_wf tl))
= let (s', d) = hd in
  if PLAIN? d then () else wf'_wf tl s'

let avoids_empty (s: FStar.Set.set asn1_id_t) (x: bytes)
: Lemma (requires (Seq.length x == 0)) (ensures (avoids s x))
= ()

let avoids_none (s: FStar.Set.set asn1_id_t) (x: bytes)
: Lemma (requires (forall id . ~ (FStar.Set.mem id s))) (ensures (avoids s x))
= ()

let avoids_sub (s1 s2: FStar.Set.set asn1_id_t) (x: bytes)
: Lemma (requires (avoids s2 x /\ FStar.Set.subset s1 s2)) (ensures (avoids s1 x))
= ()

let append_prefix (x1 x2: bytes)
: Lemma (Seq.slice (x1 `Seq.append` x2) 0 (Seq.length x1) == x1)
= assert (Seq.equal (Seq.slice (x1 `Seq.append` x2) 0 (Seq.length x1)) x1)

let avoids_framed (s s': FStar.Set.set asn1_id_t) (x1 x2: bytes)
: Lemma (requires (framed s' x1 /\ FStar.Set.disjoint s s')) (ensures (avoids s (x1 `Seq.append` x2)))
= framed_pid s' x1;
  append_prefix x1 x2;
  ident_prefix x1 (x1 `Seq.append` x2)

let avoids_cat_empty (s: FStar.Set.set asn1_id_t) (x1 x2: bytes)
: Lemma (requires (Seq.length x1 == 0 /\ avoids s x2)) (ensures (avoids s (x1 `Seq.append` x2)))
= assert (Seq.equal (x1 `Seq.append` x2) x2)

#push-options "--fuel 2 --ifuel 1"
let item_dec_twin (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (Sq.item_dec (In.twin_of dk) == d)
= ()
#pop-options

let dfe_framed (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: bytes)
: Lemma (requires (framed s x)) (ensures (dfe (In.twin_of dk) x))
= item_set_twin dk

let dfe_empty (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (requires (ASN1_OPTION_ILC? dk \/ ASN1_DEFAULT_TERMINAL? dk \/ ASN1_DEFAULT_RESTRICTED_TERMINAL? dk))
  (ensures (dfe (In.twin_of dk) Seq.empty))
= item_dec_twin dk;
  iacc_single_empty (In.twin_of dk);
  match dk with
  | ASN1_OPTION_ILC k -> iacc_option_none k
  | _ -> iacc_default_none dk

#push-options "--fuel 2 --ifuel 2"
let gdi_items_cons (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl })
: Lemma (requires (Some? (generate_defaultable_items (hd :: tl))))
  (ensures (Some? (generate_defaultable_item hd) /\ Some? (generate_defaultable_items tl)))
= ()

let gdi_items_cons_intro (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl })
: Lemma (requires (Some? (generate_defaultable_item hd) /\ Some? (generate_defaultable_items tl)))
  (ensures (Some? (generate_defaultable_items (hd :: tl))))
= ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 64"
let iacc_absent_head (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl }) (x2: bytes)
: Lemma (requires (~ (PLAIN? (Sq.item_dec hd)) /\ Some? (generate_defaultable_item hd) /\ avoids (Sq.item_set hd) x2))
  (ensures (iacc (hd :: tl) x2 <==> iacc tl x2))
= ident_empty ();
  Sq.seq_cons_none (hd :: tl) x2;
  Sq.seq_cons_none tl x2;
  if Seq.length x2 = 0
  then begin
    assert (Seq.equal x2 Seq.empty);
    Classical.move_requires (gdi_items_cons hd) tl;
    Classical.move_requires (gdi_items_cons_intro hd) tl
  end
  else match parse parse_asn1_identifier_U32 x2 with
  | None -> ()
  | Some (id, c1) -> Sq.seq_cons_cons_some hd tl id (Seq.slice x2 c1 (Seq.length x2))
#pop-options

let iacc_cons_inv_wf (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl })
  (x1 x2: bytes)
: Lemma
  (requires (dfe hd x1 /\ avoids (hs hd) x2 /\ PSL.item_shaped hd /\ iacc (hd :: tl) (x1 `Seq.append` x2)))
  (ensures (iacc [hd] x1 /\ iacc tl x2))
= if Seq.length x1 = 0
  then begin
    Classical.move_requires (framed_ne (Sq.item_set hd)) x1;
    assert (x1 == Seq.empty /\ ~ (PLAIN? (Sq.item_dec hd)) /\ Some? (generate_defaultable_item hd));
    Seq.append_empty_l x2;
    iacc_single_empty hd;
    iacc_absent_head hd tl x2
  end
  else iacc_cons_inv hd tl x1 x2

#push-options "--fuel 1 --ifuel 1 --z3rlimit 64"
let iacc_cons_wf (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl })
  (v: bytes) (p2 p1 p0: nat)
: Lemma
  (requires (p2 <= p1 /\ p1 <= p0 /\ p0 <= Seq.length v /\
    dfe hd (Seq.slice v p2 p1) /\ avoids (hs hd) (Seq.slice v p1 p0) /\
    iacc [hd] (Seq.slice v p2 p1) /\ iacc tl (Seq.slice v p1 p0)))
  (ensures (iacc (hd :: tl) (Seq.slice v p2 p0)))
= let xh = Seq.slice v p2 p1 in
  let xt = Seq.slice v p1 p0 in
  if p2 < p1
  then begin
    framed_pid (Sq.item_set hd) xh;
    let vr = Seq.slice v p2 (Seq.length v) in
    assert (Seq.equal (Seq.slice vr 0 (Seq.length xh)) xh);
    ident_prefix xh vr
  end
  else if p1 < p0
  then begin
    Classical.move_requires (framed_ne (Sq.item_set hd)) xh;
    ident_empty ();
    Sq.seq_cons_none tl xt;
    let vr = Seq.slice v p1 (Seq.length v) in
    assert (Seq.equal (Seq.slice vr 0 (Seq.length xt)) xt);
    ident_prefix xt vr
  end;
  iacc_cons hd tl v p2 p1 p0
#pop-options

let avoids_dfe (s: FStar.Set.set asn1_id_t) (hd: gen_decorated_parser_twin) (x: bytes)
: Lemma (requires (dfe hd x /\ FStar.Set.disjoint s (Sq.item_set hd))) (ensures (avoids s x))
= Classical.move_requires (framed_pid (Sq.item_set hd)) x

let avoids_dfe_cat (s: FStar.Set.set asn1_id_t) (hd: gen_decorated_parser_twin) (x1 x2: bytes)
: Lemma (requires (dfe hd x1 /\ FStar.Set.disjoint s (Sq.item_set hd) /\ (Seq.length x1 == 0 ==> avoids s x2)))
  (ensures (avoids s (x1 `Seq.append` x2)))
= if Seq.length x1 = 0
  then avoids_cat_empty s x1 x2
  else avoids_framed s (Sq.item_set hd) x1 x2

let dfe_plain_ne (hd: gen_decorated_parser_twin) (x: bytes)
: Lemma (requires (dfe hd x /\ PLAIN? (Sq.item_dec hd))) (ensures (Seq.length x > 0))
= Classical.move_requires (framed_ne (Sq.item_set hd)) x

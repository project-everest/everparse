module ASN1.Pulse.Parser
#lang-pulse

(* The zero-copy parser interpreter: from a validated ASN.1 DER schema
   value `k`, a parser from `asn1_as_parser k` to `asn1_rel k`. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.ILC
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
open ASN1.Pulse.Interpreter
open ASN1.Pulse.ParseChoice
open ASN1.Pulse.ParseSequence
open ASN1.Pulse.ParseSeqOf
open ASN1.Pulse.ParseAdb
open ASN1.Pulse.ParseSetAny.Lemmas
open ASN1.Pulse.ParseSetAny

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module ILC = ASN1.Pulse.ILC
module AL = ASN1.Pulse.ParseAdb.Lemmas
module SC = ASN1.Pulse.SetComp
module In = ASN1.Pulse.Interpreter
module Ser = ASN1.Spec.Serializer
module Conf = ASN1.Spec.Conformance

let ares (#t: Type0) (#u: Type0) (r: prel t u) (#k: SB.parser_kind) (p: SB.parser k u)
  (input: S.slice U8.t) (pm: perm) (w: Ghost.erased SB.bytes) (v: Ghost.erased u) : Type
= stt t
    (S.pts_to input #pm w ** pure (parsed p w v))
    (fun res -> r pm res v ** Trade.trade (r pm res v) (S.pts_to input #pm w))

let sares (#i: _) (#ls: asn1_gen_items_l i) (#sfxi: Type0) (#t: Type0) (dia: iadesc ls sfxi t) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (sfx: parser_twin asn1_weak_parser_kind sfxs)
  (input: S.slice U8.t) (pm: perm) (w: Ghost.erased SB.bytes) (v: Ghost.erased (asn1_sequence_any_t_core ls sfxs)) : Type
= stt t
    (S.pts_to input #pm w ** pure (seqa_parsed_core ls sfx w v /\ AL.sfx_shaped sfx))
    (fun res -> iarel true dia sfxr pm res v ** Trade.trade (iarel true dia sfxr pm res v) (S.pts_to input #pm w))

let ndres (key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t)
  (kc pin: S.slice U8.t) (pm: perm) (wk wp: Ghost.erased SB.bytes) (v: Ghost.erased (AL.ady key_k ls)) : Type
= stt t
    (S.pts_to kc #pm wk ** S.pts_to pin #pm wp ** pure (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk (dfst (Ghost.reveal v)) /\ AL.pl_parsed key_k ls wp v))
    (fun res -> sxrel true dsx pm res v ** Trade.trade (sxrel true dsx pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp))

let sdres (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (di: idesc ls t)
  (id: asn1_id_t) (e: S.slice U8.t) (pm: perm) (we: Ghost.erased SB.bytes) (st: dtuple di) (v: Ghost.erased (asn1_sequence_t_core ls)) : Type
= stt (dtuple di)
    (S.pts_to e #pm we ** partial_rel di pm st v ** pure (dpre ls id we (pres_of di st) v))
    (fun st' -> partial_rel di pm st' v ** Trade.trade (partial_rel di pm st' v) (partial_rel di pm st v ** S.pts_to e #pm we) **
      pure (forall (c: nat) . is_some ls (pres_of di st') c == (is_some ls (pres_of di st) c || SC.comp_of_id (In.twins_of ls) id = Some c)))

let fres (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (di: idesc ls t) (st: dtuple di) (pm: perm) (v: Ghost.erased (asn1_sequence_t_core ls)) : Type
= stt t
    (partial_rel di pm st v ** pure (fin_pre ls (pres_of di st) v))
    (fun res -> irel true di pm res v ** Trade.trade (irel true di pm res v) (partial_rel di pm st v))

let cres (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (ld: lcdesc lc t) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc)))
  (id: asn1_id_t) (input: S.slice U8.t) (pm: perm) (w: Ghost.erased SB.bytes) (v: Ghost.erased (make_gen_choice_type (asn1_lc_t lc))) : Type
= stt t
    (S.pts_to input #pm w ** pure (parsed #asn1_strong_parser_kind (asn1_as_parser (choice_k lc pf)) w v /\ dfst (Ghost.reveal v) == id))
    (fun res -> lcrel true ld pm res v ** Trade.trade (lcrel true ld pm res v) (S.pts_to input #pm w))

let fdres (key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb)
  (#ts: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts)
  (kc pin: S.slice U8.t) (pm: perm) (wk wp: Ghost.erased SB.bytes) (v: Ghost.erased (AL.ady_fb key_k ls fb)) : Type
= stt ts
    (S.pts_to kc #pm wk ** S.pts_to pin #pm wp ** pure (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk (dfst (Ghost.reveal v)) /\ AL.pl_fb_parsed key_k ls fb wp v))
    (fun res -> afb_rel fb dfb dfx pm res v ** Trade.trade (afb_rel fb dfb dfx pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp))

(* The subset of schemas currently supported *)

[@@asn1_pulse_attr]
let rec psupported_content (k: asn1_content_k) : Tot bool (decreases k) =
  match k with
  | ASN1_TERMINAL _ -> true
  | ASN1_RESTRICTED_TERMINAL _ _ -> true
  | ASN1_PREFIXED k' -> psupported_k k'
  | ASN1_SEQUENCE gitems -> psupported_items (dsnd gitems)
  | ASN1_SEQUENCE_OF _ k' -> psupported_k k'
  | ASN1_SET_OF _ k' -> psupported_k k'
  | ASN1_SET _ items _ -> psupported_items items
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    psupported_items prefix && adb_key_supported key_k && psupported_ls ls &&
    (match ofb with None -> true | Some fb -> psupported_items (dsnd fb))
  | _ -> false

and psupported_ls (#t: eqtype) (ls: list (t & asn1_gen_items_lk)) : Tot bool (decreases ls) =
  match ls with
  | [] -> true
  | (_, y) :: tl -> psupported_items (dsnd y) && psupported_ls tl

and psupported_items (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> psupported_dec dk && psupported_items tl

and psupported_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot bool (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> psupported_k k
  | ASN1_OPTION_ILC k -> psupported_k k
  | _ -> true

and psupported_lc (lc: list (asn1_id_t & asn1_content_k)) : Tot bool (decreases lc) =
  match lc with
  | [] -> true
  | (_, c) :: tl -> psupported_content c && psupported_lc tl

and psupported_k (#s: _) (k: asn1_k s) : Tot bool (decreases k) =
  match k with
  | ASN1_ILC _ k' -> psupported_content k'
  | ASN1_CHOICE_ILC lc _ -> psupported_lc lc
  | ASN1_ANY_ILC -> true
  | _ -> false

[@@asn1_pulse_attr]
inline_for_extraction
let parse_integer (bound: pos)
: aparser #(asn1_terminal_impl_t (ASN1_INTEGER bound)) #(asn1_terminal_t (ASN1_INTEGER bound)) (asn1_terminal_rel (ASN1_INTEGER bound)) #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_INTEGER bound))
= if small_integer bound
  then coerce_eq () (parse_small_integer bound)
  else coerce_eq () (parse_big_integer bound)

#push-options "--fuel 1 --ifuel 0"
private noextract
let prefixed_terminal_p (id: asn1_id_t) (k': asn1_terminal_k)
: Tot (p2: SB.parser asn1_weak_parser_kind (asn1_terminal_t k') {
    p2 == asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id k') /\
    (forall b . SB.parse (parse_asn1_ILC id #(ASN1_TERMINAL k') (asn1_terminal_as_parser k')) b == SB.parse p2 b) })
= assert_norm (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id k') == weaken asn1_weak_parser_kind (parse_asn1_ILC id #(ASN1_TERMINAL k') (asn1_terminal_as_parser k')));
  asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id k')
#pop-options

[@@asn1_pulse_attr]
inline_for_extraction
let parse_prefixed_terminal (id: asn1_id_t) (k': asn1_terminal_k)
  (f: aparser #(asn1_terminal_impl_t k') #(asn1_terminal_t k') (asn1_terminal_rel k') #asn1_weak_parser_kind (asn1_terminal_as_parser k'))
: aparser #(asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id k')) #(asn1_terminal_t (ASN1_PREFIXED_TERMINAL id k')) (asn1_terminal_rel (ASN1_PREFIXED_TERMINAL id k')) #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id k'))
= parse_ext #(asn1_terminal_impl_t k') #(asn1_terminal_t k') #(asn1_terminal_rel k') (parse_ilc id #(ASN1_TERMINAL k') #_ #_ #(asn1_terminal_as_parser k') f) #asn1_weak_parser_kind (prefixed_terminal_p id k')

[@@asn1_pulse_attr]
let rec parse_terminal ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k)
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_terminal_t k))
: Tot (ares (asn1_terminal_rel k) (asn1_terminal_as_parser k) input pm w v)
  (decreases k)
= [@inline_let] let vf : aparser #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) #asn1_weak_parser_kind (asn1_terminal_as_parser k) =
  (match k with
  | ASN1_BOOLEAN -> parse_boolean ()
  | ASN1_NULL -> parse_null ()
  | ASN1_INTEGER bound -> parse_integer bound
  | ASN1_BITSTRING -> parse_bitstring ()
  | ASN1_PREFIXED_TERMINAL id k' ->
    parse_prefixed_terminal id k' (fun input #pm #w #v -> parse_terminal k' input #pm #w #v)
  | ASN1_OCTETSTRING -> parse_slice_leaf k
  | ASN1_PRINTABLESTRING -> parse_slice_leaf k
  | ASN1_UTF8STRING -> parse_slice_leaf k
  | ASN1_IA5STRING -> parse_slice_leaf k
  | ASN1_VISIBLESTRING -> parse_slice_leaf k
  | ASN1_BMPSTRING -> parse_slice_leaf k
  | ASN1_UNIVERSALSTRING -> parse_slice_leaf k
  | ASN1_TELETEXSTRING -> parse_slice_leaf k
  | ASN1_NUMERICSTRING -> parse_slice_leaf k
  | ASN1_VIDEOTEXSTRING -> parse_slice_leaf k
  | ASN1_GRAPHICSTRING -> parse_slice_leaf k
  | ASN1_GENERALSTRING -> parse_slice_leaf k
  | ASN1_OBJECTDESCRIPTOR -> parse_slice_leaf k
  | ASN1_OID -> parse_slice_leaf k
  | ASN1_RELATIVE_OID -> parse_slice_leaf k
  | ASN1_OID_IRI -> parse_slice_leaf k
  | ASN1_RELATIVE_OID_IRI -> parse_slice_leaf k
  | ASN1_UTCTIME -> parse_slice_leaf k
  | ASN1_GENERALIZEDTIME -> parse_slice_leaf k
  | ASN1_DATE -> parse_slice_leaf k
  | ASN1_TIME_OF_DAY -> parse_slice_leaf k
  | ASN1_DATE_TIME -> parse_slice_leaf k)
  in vf input #pm #w #v

[@@asn1_pulse_attr]
inline_for_extraction
let parse_restricted (k: asn1_terminal_k) (r: asn1_restriction k)
: aparser #(asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r))
= parse_rel_ext
    (parse_ext (parse_filter #_ #_ #_ #_ #(asn1_terminal_as_parser k) (fun input #pm #w #v -> parse_terminal k input #pm #w #v) (restriction_pred r)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)))
    (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r))

(* Whether an identifier belongs to an item *)

[@@asn1_pulse_attr]
inline_for_extraction
let phas_id_k (#s: _) (k: asn1_k s) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
= match k with
  | ASN1_ILC id0 _ -> ILC.asn1_id_eq id id0
  | ASN1_CHOICE_ILC lc _ -> has_id_lc lc id
  | ASN1_ANY_ILC -> true

[@@asn1_pulse_attr]
inline_for_extraction
let phas_id_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
= match dk with
  | ASN1_PLAIN_ILC k -> phas_id_k k id
  | ASN1_OPTION_ILC k -> phas_id_k k id
  | ASN1_DEFAULT_TERMINAL id0 _ -> ILC.asn1_id_eq id id0
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 _ _ -> ILC.asn1_id_eq id id0

(* VIEW nodes: parse the underlying value, then build the view type *)

inline_for_extraction
fn parse_view
  (#t: Type0) (#u: Type0) (#r: prel t u) (#k: Ghost.erased SB.parser_kind) (#p: SB.parser k u)
  (f: aparser r p)
  (ty: Type0) (view: Ghost.erased (ty -> t)) (mk: t -> ty) (law: squash (view_law (Ghost.reveal view) mk))
  (r': prel ty u { forall pm x y . r' pm x y == r pm (Ghost.reveal view x) y })
: aparser #ty #u r' #k p
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  let x = f input #pm #w #v;
  let res = mk x;
  assert (pure (r' pm res v == r pm x v));
  rewrite (r pm x v) as (r' pm res v);
  rewrite (Trade.trade (r pm x v) (S.pts_to input #pm w)) as (Trade.trade (r' pm res v) (S.pts_to input #pm w));
  res
}

(* KEEP-BYTES nodes: parse the value from half of the input, and keep the
   other half as the bytes of the value *)

(* Every value returned by a parser is encodable, and its encoding is the
   parsed input, so parsing then writing round-trips. *)
let parsed_encodable_d (#s: _) (k: asn1_k s) (w: SB.bytes) (v: asn1_t k)
: Lemma
  (requires (Conf.wf k /\ parsed #asn1_strong_parser_kind (asn1_as_parser k) w v))
  (ensures (Ser.encodable k v /\ Ser.asn1_enc k v == w))
= Ser.parsed_encodable k w;
  Ser.asn1_as_parser_consumed k w;
  assert (Seq.equal (Seq.slice w 0 (Seq.length w)) w)

private let half_perm_pos (pm: perm) : Lemma (pm /. 2.0R >. 0.0R) [SMTPat (pm /. 2.0R)] = ()

inline_for_extraction
fn parse_keep
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (#r: prel t (asn1_t k))
  (wf: squash (Conf.wf k))
  (f: aparser r #asn1_strong_parser_kind (asn1_as_parser k))
  (r': prel (kept t) (asn1_t k) { forall pm x y . r' pm x y == (r (pm /. 2.0R) x.kval y ** keep_rel k (pm /. 2.0R) x.kraw y ** pure (Some? x.kraw)) })
: aparser #(kept t) #(asn1_t k) r' #asn1_strong_parser_kind (asn1_as_parser k)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  parsed_encodable_d k w v;
  half_perm_pos pm;
  S.share input;
  let x = f input #(pm /. 2.0R) #w #v;
  let res : kept t = { kval = x; kraw = Some input };
  fold (prel_slice_ser (Ser.asn1_enc k) (pm /. 2.0R) input v);
  fold (keep_rel k (pm /. 2.0R) (Some input) v);
  rewrite (r (pm /. 2.0R) x v ** keep_rel k (pm /. 2.0R) (Some input) v ** pure (Some? res.kraw)) as (r' pm res v);
  Pulse.Lib.Trade.intro_trade (r' pm res v) (S.pts_to input #pm w) (Trade.trade (r (pm /. 2.0R) x v) (S.pts_to input #(pm /. 2.0R) w) ** pure (Ser.asn1_enc k v == Ghost.reveal w)) fn _ {
    rewrite (r' pm res v) as (r (pm /. 2.0R) x v ** keep_rel k (pm /. 2.0R) (Some input) v ** pure (Some? res.kraw));
    Trade.elim_trade _ _;
    unfold (keep_rel k (pm /. 2.0R) (Some input) v);
    unfold (prel_slice_ser (Ser.asn1_enc k) (pm /. 2.0R) input v);
    S.gather input;
    half_eq pm;
    rewrite (S.pts_to input #(pm /. 2.0R +. pm /. 2.0R) w) as (S.pts_to input #pm w);
  };
  res
}

(* Absent items *)

[@@asn1_pulse_attr]
let rec dd_absent (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] d: _) (#[@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s d) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] dd: ddesc dk t)
  (pm: perm) (v: Ghost.erased (asn1_decorated_t_core dk))
: Tot (stt t (pure (absent_core dk v)) (fun res -> drel true dd pm res v ** pure (drel true dd pm res v == emp)))
  (decreases dd)
= [@inline_let] let vf : dabsent dd =
  (match dd with
  | DD_PLAIN da -> dec_plain_absent da
  | DD_OPTION da -> dec_option_absent da
  | DD_DEFAULT id0 #k defv -> dec_default_absent id0 #k defv
  | DD_DEFAULT_RESTRICTED id0 #k r defv -> dec_default_restricted_absent id0 #k r defv
  | DD_VIEW dd' ty view mk law -> dec_view_absent dd' ty view mk law (fun pm v -> dd_absent dd' pm v))
  in vf pm v

(* Filling the empty slots of a SET *)

[@@asn1_pulse_attr]
let rec parse_sfin (#[@@@FStar.Attributes.monomorphize] ids: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l ids) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] di: idesc ls t)
  (st: dtuple di) (#pm: perm) (#v: Ghost.erased (asn1_sequence_t_core ls))
: Tot (fres di st pm v)
  (decreases di)
= [@inline_let] let vf : fin_t di =
  (match di with
  | ID_NIL -> fin_nil ()
  | ID_SINGLE dd -> fin_single dd (fun pm v -> dd_absent dd pm v)
  | ID_CONS dd #_ #_ #dk2 #_ #tl2 dtl ->
    fin_cons dd dk2 tl2 dtl (fun pm v -> dd_absent dd pm v)
      (fun st #pm #v -> parse_sfin dtl st #pm #v))
  in vf st #pm #v

(* The parser interpreter over descriptors *)

let rec parse_cd (#[@@@FStar.Attributes.monomorphize] k: asn1_content_k) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] cd: cdesc k t) (u: squash (psupported_content k))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_content_t k))
: Tot (ares (crel true cd) (asn1_content_as_parser k) input pm w v)
  (decreases cd)
= [@inline_let] let vf : aparser #t #(asn1_content_t k) (crel true cd) #asn1_weak_parser_kind (asn1_content_as_parser k) =
  (match cd with
  | CD_TERMINAL k' ->
    parse_rel_ext (parse_ext (parse_terminal k') #asn1_weak_parser_kind (asn1_content_as_parser k)) (crel true cd)
  | CD_RESTRICTED k' r ->
    parse_rel_ext (parse_restricted k' r) (crel true cd)
  | CD_PREFIXED #_ #k' d' ->
    parse_ext #_ #_ #_ #_ #(asn1_as_parser k') (fun input #pm #w #v -> parse_d d' () input #pm #w #v) #asn1_weak_parser_kind (asn1_content_as_parser k)
  | CD_SEQUENCE gitems di ->
    seq_parser gitems di (fun input #pm #w #v -> parse_id di () input #pm #w #v)
  | CD_SEQUENCE_OF ne d' -> seq_of_parser ne d'
  | CD_SET_OF ne d' -> set_of_parser ne d'
  | CD_SET _ items pf di ->
    set_any_parser items pf di (dnone di)
      (fun id e #pm #we st #v -> parse_sdisp di () id e #pm #we st #v)
      (fun st #pm #v -> parse_sfin di st #pm #v)
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    adb_none_parser ipd prefix kid key_k ls pf pf' dsx dpre
      (fun input #pm #w #v -> parse_iad dpre () (sxrel true dsx) (sfx_none kid key_k ls)
        (sfx_none_parser kid key_k dsx (fun kc pin #pm #wk #wp #v -> parse_sx dsx () kc pin #pm #wk #wp #v))
        input #pm #w #v)
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre ->
    adb_some_parser ipd prefix kid key_k ls fb pf pf' dfb dfx dpre
      (fun input #pm #w #v -> parse_iad dpre () (afb_rel fb dfb dfx) (sfx_some kid key_k ls fb)
        (sfx_some_parser kid key_k fb dfb dfx (fun kc pin #pm #wk #wp #v ->
          parse_fx dfx () fb dfb (seq_parser fb dfb (fun input #pm #w #v -> parse_id dfb () input #pm #w #v)) kc pin #pm #wk #wp #v))
        input #pm #w #v)
  | CD_VIEW d' ty view mk law ->
    parse_view (fun input #pm #w #v -> parse_cd d' () input #pm #w #v) ty view mk law (crel true cd))
  in vf input #pm #w #v

and parse_iad (#[@@@FStar.Attributes.monomorphize] i: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (#[@@@FStar.Attributes.monomorphize] sfxi: Type0) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] dia: iadesc ls sfxi t) (u: squash (psupported_items ls))
  (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (sfx: Ghost.erased (parser_twin asn1_weak_parser_kind sfxs))
  ([@@@FStar.Attributes.monomorphize] psfx: aparser #sfxi #sfxs sfxr #asn1_weak_parser_kind (Mkparsertwin?.p (Ghost.reveal sfx)))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_any_t_core ls sfxs))
: Tot (sares dia sfxr sfx input pm w v)
  (decreases dia)
= [@inline_let] let vf : saparser dia sfxr sfx =
  (match dia with
  | IA_NIL -> seqa_nil psfx
  | IA_SINGLE #_ #_ #dk dd ->
    seqa_cons dd (IA_NIL #sfxi) (IA_SINGLE dd) (ia_single_prop dd sfxr) (phas_id_dec dk)
      (fun input #pm #w #v -> parse_dd dd () input #pm #w #v)
      (fun pm v -> dd_absent dd pm v)
      (seqa_nil psfx)
  | IA_CONS #_ #_ #dk dd dtl ->
    seqa_cons dd dtl (IA_CONS dd dtl) (ia_cons_cons_prop dd dtl sfxr) (phas_id_dec dk)
      (fun input #pm #w #v -> parse_dd dd () input #pm #w #v)
      (fun pm v -> dd_absent dd pm v)
      (fun input #pm #w #v -> parse_iad dtl () sfxr sfx psfx input #pm #w #v))
  in vf input #pm #w #v

and parse_sx (#[@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) (#[@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] dsx: sxdesc key_k ls t)
  (u: squash (adb_key_supported key_k /\ psupported_ls ls))
  (kc pin: S.slice U8.t) (#pm: perm) (#wk #wp: Ghost.erased SB.bytes) (#v: Ghost.erased (AL.ady key_k ls))
: Tot (ndres key_k dsx kc pin pm wk wp v)
  (decreases dsx)
= [@inline_let] let vf : ndisp key_k dsx =
  (match dsx with
  | SX_NIL _ -> ndisp_nil key_k
  | SX_SINGLE _ x y di ->
    ndisp_single key_k x y di (seq_parser y di (fun input #pm #w #v -> parse_id di () input #pm #w #v))
  | SX_CONS _ x y di dtl ->
    ndisp_cons key_k () x y di dtl
      (seq_parser y di (fun input #pm #w #v -> parse_id di () input #pm #w #v))
      (fun kc pin #pm #wk #wp #v -> parse_sx dtl () kc pin #pm #wk #wp #v))
  in vf kc pin #pm #wk #wp #v

and parse_fx (#[@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) (#[@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#[@@@FStar.Attributes.monomorphize] tfb: Type0) (#[@@@FStar.Attributes.monomorphize] ts: Type0)
  ([@@@FStar.Attributes.monomorphize] dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts)
  (u: squash (adb_key_supported key_k /\ psupported_ls ls))
  (fb: Ghost.erased asn1_gen_items_lk) (dfb: Ghost.erased (idesc (dsnd fb) tfb))
  ([@@@FStar.Attributes.monomorphize] pfb: items_parser fb dfb)
  (kc pin: S.slice U8.t) (#pm: perm) (#wk #wp: Ghost.erased SB.bytes) (#v: Ghost.erased (AL.ady_fb key_k ls fb))
: Tot (fdres key_k fb dfb dfx kc pin pm wk wp v)
  (decreases dfx)
= [@inline_let] let vf : fdisp key_k fb dfb dfx =
  (match dfx with
  | FX_NIL _ ->
    fdisp_nil key_k fb dfb (fun input #pm #w #v -> parse_terminal key_k input #pm #w #v) pfb
  | FX_SINGLE _ x y di ->
    fdisp_single key_k () x y di fb dfb
      (seq_parser y di (fun input #pm #w #v -> parse_id di () input #pm #w #v))
      (fun input #pm #w #v -> parse_terminal key_k input #pm #w #v)
      pfb
  | FX_CONS _ x y di dtl ->
    fdisp_cons key_k () x y di fb dfb dtl
      (seq_parser y di (fun input #pm #w #v -> parse_id di () input #pm #w #v))
      (fun kc pin #pm #wk #wp #v -> parse_fx dtl () fb dfb pfb kc pin #pm #wk #wp #v))
  in vf kc pin #pm #wk #wp #v

and parse_id (#[@@@FStar.Attributes.monomorphize] i: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] di: idesc ls t) (u: squash (psupported_items ls))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core ls))
: Tot (sres di input pm w v)
  (decreases di)
= [@inline_let] let vf : sparser di =
  (match di with
  | ID_NIL -> seq_nil ()
  | ID_SINGLE dd ->
    seq_single dd (fun input #pm #w #v -> parse_dd dd () input #pm #w #v) (fun pm v -> dd_absent dd pm v)
  | ID_CONS #_ #_ #dk dd #_ #_ #dk2 #_ #tl2 dtl ->
    seq_cons dd dk2 tl2 dtl (phas_id_dec dk)
      (fun input #pm #w #v -> parse_dd dd () input #pm #w #v)
      (fun pm v -> dd_absent dd pm v)
      (fun input #pm #w #v -> parse_id dtl () input #pm #w #v))
  in vf input #pm #w #v

and parse_sdisp (#[@@@FStar.Attributes.monomorphize] i: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] di: idesc ls t) (u: squash (psupported_items ls))
  (id: asn1_id_t) (e: S.slice U8.t) (#pm: perm) (#we: Ghost.erased SB.bytes) (st: dtuple di) (#v: Ghost.erased (asn1_sequence_t_core ls))
: Tot (sdres di id e pm we st v)
  (decreases di)
= [@inline_let] let vf : disp_t di =
  (match di with
  | ID_NIL -> disp_nil ()
  | ID_SINGLE dd ->
    disp_single dd (fun input #pm #w #v -> parse_dd dd () input #pm #w #v)
  | ID_CONS #_ #_ #dk dd #_ #_ #dk2 #_ #tl2 dtl ->
    disp_cons dd dk2 tl2 dtl (phas_id_dec dk)
      (fun input #pm #w #v -> parse_dd dd () input #pm #w #v)
      (fun id e #pm #we st #v -> parse_sdisp dtl () id e #pm #we st #v))
  in vf id e #pm #we st #v

and parse_dd (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] d: _) (#[@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s d) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] dd: ddesc dk t) (u: squash (psupported_dec dk))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_decorated_t_core dk))
: Tot (dres dd input pm w v)
  (decreases dd)
= [@inline_let] let vf : dpresent dd =
  (match dd with
  | DD_PLAIN da -> dec_plain_present da (fun input #pm #w #v -> parse_d da () input #pm #w #v)
  | DD_OPTION da -> dec_option_present da (fun input #pm #w #v -> parse_d da () input #pm #w #v)
  | DD_DEFAULT id0 #k defv -> dec_default_present id0 #k defv (fun input #pm #w #v -> parse_terminal k input #pm #w #v)
  | DD_DEFAULT_RESTRICTED id0 #k r defv -> dec_default_restricted_present id0 #k r defv (parse_restricted k r)
  | DD_VIEW dd' ty view mk law -> dec_view_present dd' ty view mk law (fun input #pm #w #v -> parse_dd dd' () input #pm #w #v))
  in vf input #pm #w #v

and parse_d (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] k: asn1_k s) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: adesc k t) (u: squash (psupported_k k))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_t k))
: Tot (ares (arel true d) (asn1_as_parser k) input pm w v)
  (decreases d)
= [@inline_let] let vf : aparser #t #(asn1_t k) (arel true d) #asn1_strong_parser_kind (asn1_as_parser k) =
  (match d with
  | D_ILC id #k' cd ->
    parse_rel_ext (parse_ilc id #k' #_ #_ #(asn1_content_as_parser k') (fun input #pm #w #v -> parse_cd cd () input #pm #w #v)) (arel true d)
  | D_CHOICE lc pf ld ->
    parse_rel_ext (choice_parser lc pf ld (fun id input #pm #w #v -> parse_lc ld pf () id input #pm #w #v)) (arel true d)
  | D_ANY ->
    parse_rel_ext (parse_ext (parse_any ()) #asn1_strong_parser_kind (asn1_as_parser k)) (arel true d)
  | D_VIEW d' ty view mk law ->
    parse_view (fun input #pm #w #v -> parse_d d' () input #pm #w #v) ty view mk law (arel true d)
  | D_KEEP d' wf ->
    parse_keep wf (fun input #pm #w #v -> parse_d d' () input #pm #w #v) (arel true d))
  in vf input #pm #w #v

and parse_lc (#[@@@FStar.Attributes.monomorphize] lc: list (asn1_id_t & asn1_content_k)) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] ld: lcdesc lc t) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (u: squash (psupported_lc lc))
  (id: asn1_id_t) (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (make_gen_choice_type (asn1_lc_t lc)))
: Tot (cres ld pf id input pm w v)
  (decreases ld)
= [@inline_let] let vf : cparser pf ld =
  (match ld with
  | LC_NIL -> choice_nil pf
  | LC_SINGLE id' #c cd ->
    choice_single id' cd pf (parse_ilc id' #c #_ #_ #(asn1_content_as_parser c) (fun input #pm #w #v -> parse_cd cd () input #pm #w #v))
  | LC_CONS id' #c cd dtl ->
    choice_cons id' cd dtl pf
      (parse_ilc id' #c #_ #_ #(asn1_content_as_parser c) (fun input #pm #w #v -> parse_cd cd () input #pm #w #v))
      (fun id input #pm #w #v -> parse_lc dtl () () id input #pm #w #v))
  in vf id input #pm #w #v

(* The legacy interpreters: nested pairs and `either` *)

[@@asn1_pulse_attr]
inline_for_extraction
let parse_k (#s: _) (k: asn1_k s) (u: squash (psupported_k k))
: aparser #(asn1_impl_t k) #(asn1_t k) (asn1_prel k) #asn1_strong_parser_kind (asn1_as_parser k)
= fun input #pm #w #v -> parse_d (legacy_adesc k) u input #pm #w #v

[@@asn1_pulse_attr]
inline_for_extraction
let parse_content (k: asn1_content_k) (u: squash (psupported_content k))
: aparser #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_prel k) #asn1_weak_parser_kind (asn1_content_as_parser k)
= fun input #pm #w #v -> parse_cd (legacy_cdesc k) u input #pm #w #v

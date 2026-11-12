module ASN1.Pulse.JitAdbKey
#lang-pulse
(* Exactness of the JIT writers of ANY DEFINED BY (ASN1.Pulse.JitWriter):
   a literal key, written as a TLV, selects exactly its own payload in the
   dispatch table, whenever its contents are shorter than 2^32 bytes, so
   that nothing needs to be read back from the output. *)
open Pulse.Lib.Pervasives
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.LengthU32
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc

module SB = LowParse.Spec.Base
module SCo = LowParse.Spec.Combinators
module SFL = LowParse.Spec.FLData
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module CE = ASN1.Spec.Content.Enc
module IE = ASN1.Spec.IdentifierU32.Enc
module C = ASN1.Spec.Conformance
module Sq = ASN1.Pulse.Sequence
module ILC = ASN1.Pulse.ILC
module In = ASN1.Pulse.Interpreter
module ADB = ASN1.Pulse.AnyDefinedBy
module WA = ASN1.Pulse.WriteAdb
module L = ASN1.Pulse.JitWriter.Lemmas
module JA = ASN1.Pulse.JitAdb

(* The contents of a key literal *)

let raw_key_c (key_k: asn1_terminal_k) (x: asn1_key_lit key_k) : Tot SB.bytes =
  match key_k with
  | ASN1_PREFIXED_TERMINAL id2 k2 -> WA.raw_key_enc id2 k2 (In.prefixed_lit id2 k2 x)
  | ASN1_OID -> let x' : asn1_oid_t = x in CE.list_enc CE.enc_arc (In.oid_enc x')
  | ASN1_RELATIVE_OID -> let x' : asn1_relative_oid_t = x in CE.list_enc CE.enc_arc x'
  | _ -> Seq.seq_of_list (WA.raw_key_list key_k x)

#push-options "--fuel 1 --ifuel 1"
let raw_key_enc_c (kid: asn1_id_t) (key_k: asn1_terminal_k) (x: asn1_key_lit key_k)
: Lemma (WA.raw_key_enc kid key_k x == enc_tlv kid true (raw_key_c key_k x))
= ()
#pop-options

[@@In.asn1_pulse_attr]
inline_for_extraction
let cw_raw_key_c ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) ([@@@FStar.Attributes.monomorphize] x: asn1_key_lit key_k)
: WA.cwriter (raw_key_c key_k x)
= match key_k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    WA.cw_ext (fun x' #xx out pos #v #p -> WA.cw_raw_key id2 k2 (In.prefixed_lit id2 k2 x) x' #xx out pos #v #p) (raw_key_c key_k x) ()
  | ASN1_OID ->
    [@inline_let] let x' : asn1_oid_t = x in
    WA.cw_ext (fun x0 #xx out pos #v #p -> WA.cw_arcs (In.oid_enc x') x0 #xx out pos #v #p) (raw_key_c key_k x) ()
  | ASN1_RELATIVE_OID ->
    [@inline_let] let x' : asn1_relative_oid_t = x in
    WA.cw_ext (fun x0 #xx out pos #v #p -> WA.cw_arcs x' x0 #xx out pos #v #p) (raw_key_c key_k x) ()
  | _ ->
    WA.cw_ext (fun x0 #xx out pos #v #p -> WA.cw_bytes (WA.raw_key_list key_k x) x0 #xx out pos #v #p) (raw_key_c key_k x) ()

(* Parsing a TLV *)

#push-options "--z3rlimit 64"
let parse_tlv (id: asn1_id_t) (#ack: asn1_content_k) (p: asn1_weak_parser (asn1_content_t ack)) (c: bytes)
: Lemma
  (requires (Seq.length c < 4294967296))
  (ensures (parse (parse_asn1_ILC id p) (enc_tlv id true c) == (
    match parse p c with
    | Some (v, n) -> if n = Seq.length c then Some (v, Seq.length (enc_tlv id true c)) else None
    | None -> None)))
= let n = U32.uint_to_t (Seq.length c) in
  let e = enc_len n in
  let rest = e `Seq.append` c in
  let b = enc_tlv id true c in
  assert (b == IE.asn1_id_enc id `Seq.append` rest);
  IE.parse_asn1_identifier_U32_enc id rest;
  ILC.ilc_eq id p b;
  let c1 = Seq.length (IE.asn1_id_enc id) in
  assert (Seq.equal (Seq.slice b c1 (Seq.length b)) rest);
  parse_enc_len n c;
  C.vlgen_eq p rest;
  assert (Seq.equal (Seq.slice rest (Seq.length e) (Seq.length e + Seq.length c)) c)
#pop-options

(* The identifier and length of a TLV followed by anything *)

#push-options "--z3rlimit 64"
let hdr_tlv (kid: asn1_id_t) (k c: bytes)
: Lemma (let w = Seq.append (enc_tlv kid true k) c in
    if Seq.length k < 4294967296
    then (Some? (JA.hdr kid w) /\ (let Some (h, l) = JA.hdr kid w in
      l == Seq.length k /\ h + l <= Seq.length w /\ Seq.slice w h (Seq.length w) == Seq.append k c))
    else None? (JA.hdr kid w))
= let hd = enc_hdr true (Seq.length k) in
  let rest = Seq.append hd (Seq.append k c) in
  let w = Seq.append (enc_tlv kid true k) c in
  Seq.append_assoc (IE.asn1_id_enc kid) (Seq.append hd k) c;
  Seq.append_assoc hd k c;
  assert (w == Seq.append (IE.asn1_id_enc kid) rest);
  IE.parse_asn1_identifier_U32_enc kid rest;
  let c1 = Seq.length (IE.asn1_id_enc kid) in
  Seq.append_slices (IE.asn1_id_enc kid) rest;
  assert (Seq.slice w c1 (Seq.length w) == rest);
  ILC.length_eq rest;
  if Seq.length k < 4294967296
  then begin
    let n = U32.uint_to_t (Seq.length k) in
    parse_enc_len n (Seq.append k c);
    Seq.append_slices hd (Seq.append k c);
    Seq.slice_slice w c1 (Seq.length w) (Seq.length hd) (Seq.length rest)
  end
  else L.hdr_big_none (Seq.length k) (Seq.append k c)
#pop-options

(* The contents of a supported key literal parse back to its value *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 32"
let raw_key_list_eq (k: asn1_terminal_k { In.adb_key_supported k /\ ~ (ASN1_OID? k) /\ ~ (ASN1_PREFIXED_TERMINAL? k) }) (x: asn1_key_lit k)
: Lemma (WA.raw_key_list k x == In.key_enc_list k x)
= ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec key_c_parse (key_k: asn1_terminal_k) (x: asn1_key_lit key_k)
: Lemma
  (requires (In.adb_key_supported key_k /\ Seq.length (raw_key_c key_k x) < 4294967296))
  (ensures (parse (asn1_terminal_as_parser key_k) (raw_key_c key_k x) == Some (key_of_lit key_k x, Seq.length (raw_key_c key_k x))))
  (decreases key_k)
= match key_k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    let x2 = In.prefixed_lit id2 k2 x in
    raw_key_enc_c id2 k2 x2;
    key_c_parse k2 x2;
    parse_tlv id2 #(ASN1_TERMINAL k2) (asn1_terminal_as_parser k2) (raw_key_c k2 x2);
    In.key_of_lit_prefixed id2 k2 x
  | ASN1_OID ->
    let x' : asn1_oid_t = x in
    WA.oid_arcs_enc x';
    CE.parse_leaf_enc ASN1_OID x'
  | _ ->
    raw_key_list_eq key_k x;
    In.key_enc_list_correct key_k x;
    CE.parse_leaf_enc key_k (key_of_lit key_k x)
#pop-options

(* The key filter of the dispatch accepts exactly the literal *)

#push-options "--z3rlimit 64"
let key_filter (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (x0: asn1_terminal_t key_k) (c: bytes)
: Lemma
  (requires (In.adb_key_supported key_k /\ Seq.length (raw_key_c key_k kx) < 4294967296))
  (ensures (let k = raw_key_c key_k kx in
    Sq.consumed (ADB.key_eq_fldata key_k x0 (Seq.length k)) (Seq.append k c) == (if x0 = key_of_lit key_k kx then Some (Seq.length k) else None)))
= let k = raw_key_c key_k kx in
  let b = Seq.append k c in
  let p = asn1_terminal_as_parser key_k in
  ADB.fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind p (ADB.key_eq x0)) (Seq.length k) b;
  Seq.append_slices k c;
  SCo.parse_filter_eq #asn1_weak_parser_kind p (ADB.key_eq x0) k;
  key_c_parse key_k kx
#pop-options

(* The dispatch selects the payload of the literal *)

let head_unique (#a: eqtype) (#b: Type) (k0: a) (y0: b) (tl: list (a & b)) (y: b)
: Lemma (requires (List.Tot.noRepeats (List.Tot.map fst ((k0, y0) :: tl)) /\ List.Tot.memP (k0, y) ((k0, y0) :: tl)))
  (ensures (y == y0))
= let aux () : Lemma (requires (List.Tot.memP (k0, y) tl)) (ensures False) =
    List.Tot.memP_map_intro fst (k0, y) tl;
    List.Tot.mem_memP k0 (List.Tot.map fst tl)
  in
  Classical.move_requires aux ()

let lit_sel (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (c: bytes) : GTot (option nat) =
  match Sq.consumed #asn1_weak_parser_kind (Mkgenparser?.p (ADB.adb_fb y)) c with
  | None -> None
  | Some n -> Some (Seq.length (raw_key_c key_k kx) + n)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 64"
let rec disp_lit (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk)
  (lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (c: bytes)
: Lemma
  (requires (In.adb_key_supported key_k /\ Seq.length (raw_key_c key_k kx) < 4294967296 /\
    List.Tot.memP (kx, y) lsf /\ List.Tot.noRepeats (List.Tot.map fst lsf)))
  (ensures (let k = raw_key_c key_k kx in
    Sq.consumed (ADB.choice_disp_p key_k (JA.lp key_k lsf) (Seq.length k)) (Seq.append k c) == lit_sel key_k kx y c))
  (decreases lsf)
= let k = raw_key_c key_k kx in
  let b = Seq.append k c in
  match lsf with
  | (k0, y0) :: tl ->
    JA.lp_cons key_k k0 y0 tl;
    ADB.choice_disp_cons key_k (key_of_lit key_k k0) (ADB.adb_fb y0) (JA.lp key_k tl) (Seq.length k) b;
    key_filter key_k kx (key_of_lit key_k k0) c;
    if key_of_lit key_k k0 = key_of_lit key_k kx
    then begin
      key_of_lit_inj key_k k0 kx;
      head_unique k0 y0 tl y;
      Seq.append_slices k c
    end
    else disp_lit key_k kx y tl c

let rec disp_fb_lit (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk)
  (lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: gen_parser asn1_weak_parser_kind) (c: bytes)
: Lemma
  (requires (In.adb_key_supported key_k /\ Seq.length (raw_key_c key_k kx) < 4294967296 /\
    List.Tot.memP (kx, y) lsf /\ List.Tot.noRepeats (List.Tot.map fst lsf)))
  (ensures (let k = raw_key_c key_k kx in
    Sq.consumed (ADB.choice_fb_disp_p key_k (JA.lp key_k lsf) fb (Seq.length k)) (Seq.append k c) == lit_sel key_k kx y c))
  (decreases lsf)
= let k = raw_key_c key_k kx in
  let b = Seq.append k c in
  match lsf with
  | (k0, y0) :: tl ->
    JA.lp_cons key_k k0 y0 tl;
    ADB.choice_fb_disp_cons key_k (key_of_lit key_k k0) (ADB.adb_fb y0) (JA.lp key_k tl) fb (Seq.length k) b;
    key_filter key_k kx (key_of_lit key_k k0) c;
    if key_of_lit key_k k0 = key_of_lit key_k kx
    then begin
      key_of_lit_inj key_k k0 kx;
      head_unique k0 y0 tl y;
      Seq.append_slices k c
    end
    else disp_fb_lit key_k kx y tl fb c
#pop-options

(* A literal key, followed by its payload, is accepted by the whole
   dispatch table exactly when the payload is, and the key contents are
   shorter than 2^32 bytes *)

let memP_mid (#a: Type) (pre: list a) (x: a) (tl: list a)
: Lemma (List.Tot.memP x (pre `List.Tot.append` (x :: tl)))
= List.Tot.append_memP pre (x :: tl) x

let lit_pre (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk)
  (pre tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) : prop =
  In.adb_key_supported key_k /\ List.Tot.noRepeats (List.Tot.map fst (pre `List.Tot.append` ((kx, y) :: tl)))

private
let acc_items_iff (y: asn1_gen_items_lk) (b: bytes)
: Lemma (L.acc #asn1_weak_parser_kind (Mkgenparser?.p (ADB.adb_fb y)) b <==> L.iacc (In.twins_of (dsnd y)) b)
= ()

private
let kd_hdr (kid: asn1_id_t) (#t: Type) (dp: (l: nat) -> SB.parser (ADB.disp_kind l) t) (w: bytes) (h l: nat)
: Lemma (requires (JA.hdr kid w == Some (h, l) /\ h <= Seq.length w))
  (ensures (JA.kd kid dp w <==> Sq.consumed (dp l) (Seq.slice w h (Seq.length w)) == Some (Seq.length w - h)))
= ()

private
let lit_sel_iff (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (c: bytes)
: Lemma ((lit_sel key_k kx y c == Some (Seq.length (raw_key_c key_k kx) + Seq.length c)) <==> L.iacc (In.twins_of (dsnd y)) c)
= acc_items_iff y c;
  match Sq.consumed #asn1_weak_parser_kind (Mkgenparser?.p (ADB.adb_fb y)) c with
  | None -> ()
  | Some n -> assert (lit_sel key_k kx y c == Some (Seq.length (raw_key_c key_k kx) + n))

#push-options "--fuel 0 --ifuel 1"
private
let lit_hdr (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (c: bytes)
: Lemma (requires (Seq.length (raw_key_c key_k kx) < 4294967296))
  (ensures (let w = Seq.append (WA.raw_key_enc kid key_k kx) c in
    let k = raw_key_c key_k kx in
    Some? (JA.hdr kid w) /\ (let Some (h, l) = JA.hdr kid w in
    l == Seq.length k /\ h <= Seq.length w /\ Seq.slice w h (Seq.length w) == Seq.append k c /\
    Seq.length w - h == Seq.length k + Seq.length c)))
= let k = raw_key_c key_k kx in
  raw_key_enc_c kid key_k kx;
  hdr_tlv kid k c;
  let w = Seq.append (WA.raw_key_enc kid key_k kx) c in
  assert (w == Seq.append (enc_tlv kid true k) c);
  let Some (h, l) = JA.hdr kid w in
  assert (Seq.slice w h (Seq.length w) == Seq.append k c);
  assert (Seq.length (Seq.slice w h (Seq.length w)) == Seq.length w - h)
#pop-options

#push-options "--fuel 0 --ifuel 1"
let lit_iff (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk)
  (pre tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (c: bytes)
: Lemma
  (requires (lit_pre key_k kx y pre tl))
  (ensures (JA.adbacc kid key_k (pre `List.Tot.append` ((kx, y) :: tl)) (Seq.append (WA.raw_key_enc kid key_k kx) c) <==>
    (Seq.length (raw_key_c key_k kx) < 4294967296 /\ L.iacc (In.twins_of (dsnd y)) c)))
= let lsf = pre `List.Tot.append` ((kx, y) :: tl) in
  memP_mid pre (kx, y) tl;
  let k = raw_key_c key_k kx in
  raw_key_enc_c kid key_k kx;
  hdr_tlv kid k c;
  if Seq.length k < 4294967296
  then begin
    let w = Seq.append (WA.raw_key_enc kid key_k kx) c in
    lit_hdr kid key_k kx c;
    let Some (h, l) = JA.hdr kid w in
    kd_hdr kid (ADB.choice_disp_p key_k (JA.lp key_k lsf)) w h l;
    disp_lit key_k kx y lsf c;
    lit_sel_iff key_k kx y c
  end
  else ()

let lit_fb_iff (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk)
  (pre tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (c: bytes)
: Lemma
  (requires (lit_pre key_k kx y pre tl))
  (ensures (JA.afbacc kid key_k (pre `List.Tot.append` ((kx, y) :: tl)) fb (Seq.append (WA.raw_key_enc kid key_k kx) c) <==>
    (Seq.length (raw_key_c key_k kx) < 4294967296 /\ L.iacc (In.twins_of (dsnd y)) c)))
= let lsf = pre `List.Tot.append` ((kx, y) :: tl) in
  memP_mid pre (kx, y) tl;
  let k = raw_key_c key_k kx in
  raw_key_enc_c kid key_k kx;
  hdr_tlv kid k c;
  if Seq.length k < 4294967296
  then begin
    let w = Seq.append (WA.raw_key_enc kid key_k kx) c in
    lit_hdr kid key_k kx c;
    let Some (h, l) = JA.hdr kid w in
    kd_hdr kid (ADB.choice_fb_disp_p key_k (JA.lp key_k lsf) (ADB.adb_fb fb)) w h l;
    disp_fb_lit key_k kx y lsf (ADB.adb_fb fb) c;
    lit_sel_iff key_k kx y c
  end
  else ()
#pop-options

(* The literal key, as a TLV whose contents are accepted by the parser of
   the key *)

let key_c_acc (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k)
: Lemma (requires (In.adb_key_supported key_k /\ Seq.length (raw_key_c key_k kx) < 4294967296))
  (ensures (L.acc #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (raw_key_c key_k kx)))
= key_c_parse key_k kx

(* Appending to the tail of the table *)

let lit_pre_tail (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk)
  (pre: list (asn1_key_lit key_k & asn1_gen_items_lk)) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Lemma (requires (lit_pre key_k kx y pre (hd2 :: tl2)))
  (ensures (lit_pre key_k (fst hd2) (snd hd2) (pre `List.Tot.append` [(kx, y)]) tl2 /\
    (pre `List.Tot.append` [(kx, y)]) `List.Tot.append` (hd2 :: tl2) == pre `List.Tot.append` ((kx, y) :: hd2 :: tl2)))
= List.Tot.append_assoc pre [(kx, y)] (hd2 :: tl2)

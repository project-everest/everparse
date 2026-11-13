module ASN1.Pulse.JitAdb
#lang-pulse
(* Lemmas for the just-in-time checked raw writers of ANY DEFINED BY
   (ASN1.Pulse.JitWriter): the prefix items and the payloads are written
   and checked as in a SEQUENCE; only the key, i.e. its identifier, length
   and contents, is read back from the output, to check that it selects the
   payload that was written. Acceptance of the whole content then follows
   structurally. *)
open Pulse.Lib.Pervasives
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Choice
open ASN1.Spec.Any
open ASN1.Spec.Sequence
open ASN1.Spec.Interpreter

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module SB = LowParse.Spec.Base
module SCo = LowParse.Spec.Combinators
module SFL = LowParse.Spec.FLData
module SDER = LowParse.Spec.DER
module T = LowParse.Tot.Combinators
module LPS = LowParse.Pulse.Base
module Sq = ASN1.Pulse.Sequence
module SA = ASN1.Pulse.SeqAny
module ADB = ASN1.Pulse.AnyDefinedBy
module ILC = ASN1.Pulse.ILC
module I = ASN1.Pulse.Identifier
module In = ASN1.Pulse.Interpreter
module L = ASN1.Pulse.JitWriter.Lemmas

(* The identifier and length of the key: the size of both, and the length
   of the key contents *)
let hdr (kid: asn1_id_t) (w: bytes) : GTot (option (nat & nat)) =
  match SB.parse parse_asn1_identifier_U32 w with
  | None -> None
  | Some (id, c1) ->
    if id = kid
    then match SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w c1 (Seq.length w)) with
      | None -> None
      | Some (len, c2) -> Some (c1 + c2, U32.v len)
    else None

(* The key, followed by the payload it selects, accepted by the dispatch
   `dp` on the length of the key contents *)
let kd (kid: asn1_id_t) (#t: Type) (dp: (l: nat) -> SB.parser (ADB.disp_kind l) t) (w: bytes) : prop =
  match hdr kid w with
  | None -> False
  | Some (h, l) -> h <= Seq.length w /\ Sq.consumed (dp l) (Seq.slice w h (Seq.length w)) == Some (Seq.length w - h)

let kd_nonempty (kid: asn1_id_t) (#t: Type) (dp: (l: nat) -> SB.parser (ADB.disp_kind l) t) (w: bytes)
: Lemma (requires (kd kid dp w)) (ensures (Seq.length w > 0))
= L.ident_empty ();
  if Seq.length w = 0
  then begin
    Seq.lemma_empty w;
    assert (hdr kid w == None)
  end

private
let opt_shift (o: option nat) (c1 c2 n: nat)
: Lemma ((c1 + c2 <= n /\ o == Some (n - (c1 + c2))) <==> (match o with None -> None | Some c3 -> Some (c1 + (c2 + c3))) == Some n)
= ()

private
let slice_tail2 (w: bytes) (c1: nat) (c2: nat)
: Lemma (requires (c1 <= Seq.length w /\ c2 <= Seq.length w - c1))
  (ensures (Seq.slice (Seq.slice w c1 (Seq.length w)) c2 (Seq.length w - c1) == Seq.slice w (c1 + c2) (Seq.length w)))
= Seq.slice_slice w c1 (Seq.length w) c2 (Seq.length w - c1)

#push-options "--z3rlimit 32"
let kd_tu
  (kid: asn1_id_t)
  (key_k: asn1_terminal_k)
  (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (w: bytes)
: Lemma (kd kid (ADB.disp_p key_k tag pl) w <==>
    Sq.consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (ADB.key_p kid key_k) tag pl) w == Some (Seq.length w))
= ADB.adb_eq kid key_k tag pl w;
  match SB.parse parse_asn1_identifier_U32 w with
  | None -> ()
  | Some (id, c1) ->
    if id = kid
    then begin
      let b1 = Seq.slice w c1 (Seq.length w) in
      match SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) b1 with
      | None -> ()
      | Some (len, c2) ->
        let l = U32.v len in
        let b2 = Seq.slice b1 c2 (Seq.length b1) in
        slice_tail2 w c1 c2;
        assert (hdr kid w == Some (c1 + c2, l));
        assert (kd kid (ADB.disp_p key_k tag pl) w <==>
          (c1 + c2 <= Seq.length w /\ Sq.consumed (ADB.disp_p key_k tag pl l) b2 == Some (Seq.length w - (c1 + c2))));
        opt_shift (Sq.consumed (ADB.disp_p key_k tag pl l) b2) c1 c2 (Seq.length w)
    end
    else ()
#pop-options

(* The suffix parser, when the identifier of the key has not been read
   yet, is the twin parser after reading it *)

let twin_ok_at (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (b: bytes) : prop =
  Sq.consumed #asn1_weak_parser_kind (SA.sfx_p sfx None) b == (
    match SB.parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id, c1) ->
      match Sq.consumed #asn1_weak_parser_kind (SA.sfx_p sfx (Some id)) (Seq.slice b c1 (Seq.length b)) with
      | None -> None
      | Some c2 -> Some (c1 + c2))

let twin_ok (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) : prop =
  forall (b: bytes) . twin_ok_at sfx b

#push-options "--z3rlimit 32"
let twin_tu
  (kid: asn1_id_t)
  (key_k: asn1_terminal_k)
  (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (b: bytes)
: Lemma (Sq.consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (ADB.key_p kid key_k) tag pl) b == (
    match SB.parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id, c1) ->
      match Sq.consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (ADB.key_fp kid key_k id) tag pl) (Seq.slice b c1 (Seq.length b)) with
      | None -> None
      | Some c2 -> Some (c1 + c2)))
= ADB.adb_eq kid key_k tag pl b;
  match SB.parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) -> ADB.adb_twin_eq kid key_k tag pl id (Seq.slice b c1 (Seq.length b))
#pop-options

let lp (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Tot (list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind)) =
  asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls

let twin_ok_none (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Lemma (twin_ok (ADB.adb_sfx_none kid key_k ls))
= let sfx = ADB.adb_sfx_none kid key_k ls in
  let aux (b: bytes) : Lemma (twin_ok_at sfx b) =
    let lp = lp key_k ls in
    ADB.adb_sfx_none_eq kid key_k ls None b;
    twin_tu kid key_k (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp) b;
    match SB.parse parse_asn1_identifier_U32 b with
    | None -> ()
    | Some (id, c1) -> ADB.adb_sfx_none_eq kid key_k ls (Some id) (Seq.slice b c1 (Seq.length b))
  in
  Classical.forall_intro aux

let twin_ok_some (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
: Lemma (twin_ok (ADB.adb_sfx_some kid key_k ls fb))
= let sfx = ADB.adb_sfx_some kid key_k ls fb in
  let aux (b: bytes) : Lemma (twin_ok_at sfx b) =
    let lp = lp key_k ls in
    ADB.adb_sfx_some_eq kid key_k ls fb None b;
    twin_tu kid key_k (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (ADB.adb_fb fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (ADB.adb_fb fb)) b;
    match SB.parse parse_asn1_identifier_U32 b with
    | None -> ()
    | Some (id, c1) -> ADB.adb_sfx_some_eq kid key_k ls fb (Some id) (Seq.slice b c1 (Seq.length b))
  in
  Classical.forall_intro aux

(* Prefix items, then the suffix *)

let aacc (items: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: bytes) : prop =
  L.acc #asn1_weak_parser_kind (SA.seqa_p items sfx None) w /\ Seq.length w > 0

let seqa_none (items: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (b: bytes)
: Lemma
  (requires (twin_ok sfx))
  (ensures (Sq.consumed #asn1_weak_parser_kind (SA.seqa_p items sfx None) b == (
    match SB.parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id, c1) ->
      match Sq.consumed #asn1_weak_parser_kind (SA.seqa_p items sfx (Some id)) (Seq.slice b c1 (Seq.length b)) with
      | None -> None
      | Some c2 -> Some (c1 + c2))))
= match items with
  | [] ->
    assert (twin_ok_at sfx b);
    SA.seqa_nil_eq sfx None b;
    begin match SB.parse parse_asn1_identifier_U32 b with
    | None -> ()
    | Some (id, c1) -> SA.seqa_nil_eq sfx (Some id) (Seq.slice b c1 (Seq.length b))
    end
  | _ ->
    SA.seqa_cons_eq items sfx None b;
    begin match SB.parse parse_asn1_identifier_U32 b with
    | None -> ()
    | Some (id, c1) -> SA.seqa_cons_eq items sfx (Some id) (Seq.slice b c1 (Seq.length b))
    end

#push-options "--fuel 1 --ifuel 1 --z3rlimit 128"
let aacc_cons
  (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin)
  (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t)
  (v: bytes) (p2 p1 p0: nat)
: Lemma
  (requires (twin_ok sfx /\ p2 <= p1 /\ p1 <= p0 /\ p0 <= Seq.length v /\
    L.iacc [hd] (Seq.slice v p2 p1) /\ aacc tl sfx (Seq.slice v p1 p0) /\
    (p2 < p1 ==> (match L.pid (Seq.slice v p2 (Seq.length v)) with
      | Some (id, _) -> FStar.Set.mem id (Sq.item_set hd)
      | None -> True)) /\
    ((p2 == p1 /\ p1 < p0) ==> (match L.pid (Seq.slice v p1 (Seq.length v)) with
      | Some (id, _) -> ~ (FStar.Set.mem id (Sq.item_set hd))
      | None -> True))))
  (ensures (aacc (hd :: tl) sfx (Seq.slice v p2 p0)))
= let x = Seq.slice v p2 p0 in
  let xh = Seq.slice v p2 p1 in
  let xt = Seq.slice v p1 p0 in
  L.ident_empty ();
  SA.seqa_cons_eq (hd :: tl) sfx None x;
  if p2 < p1
  then begin
    Sq.seq_cons_none [hd] xh;
    let Some (id, c1) = SB.parse parse_asn1_identifier_U32 xh in
    let rh = Seq.slice xh c1 (Seq.length xh) in
    Sq.seq_single_some hd id rh;
    assert (Seq.equal (Seq.slice x 0 (Seq.length xh)) xh);
    L.ident_prefix xh x;
    let vr = Seq.slice v p2 (Seq.length v) in
    assert (Seq.equal (Seq.slice vr 0 (Seq.length xh)) xh);
    L.ident_prefix xh vr;
    let r = Seq.slice x c1 (Seq.length x) in
    assert (Seq.equal (Seq.slice r 0 (Seq.length rh)) rh);
    L.strong_prefix (parse_asn1_sequence_item_twin hd id) rh r;
    SA.seqa_body_eq hd tl sfx id r;
    assert (Seq.equal (Seq.slice r (Seq.length rh) (Seq.length r)) xt)
  end
  else begin
    assert (Seq.equal x xt);
    L.iacc_single_empty hd;
    L.gdi_not_plain hd;
    seqa_none tl sfx xt;
    let Some (id, c1) = SB.parse parse_asn1_identifier_U32 xt in
    let vr = Seq.slice v p1 (Seq.length v) in
    assert (Seq.equal (Seq.slice vr 0 (Seq.length xt)) xt);
    L.ident_prefix xt vr;
    SA.seqa_body_eq hd tl sfx id (Seq.slice x c1 (Seq.length x))
  end
#pop-options

(* The dispatch tables *)

let adbacc (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (w: bytes) : prop =
  kd kid (ADB.choice_disp_p key_k (lp key_k ls)) w

let afbacc (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (w: bytes) : prop =
  kd kid (ADB.choice_fb_disp_p key_k (lp key_k ls) (ADB.adb_fb fb)) w

#push-options "--z3rlimit 32"
let aacc_nil_none (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (w: bytes)
: Lemma (requires (adbacc kid key_k ls w)) (ensures (aacc [] (ADB.adb_sfx_none kid key_k ls) w))
= let lp = lp key_k ls in
  kd_nonempty kid (ADB.choice_disp_p key_k lp) w;
  SA.seqa_nil_eq (ADB.adb_sfx_none kid key_k ls) None w;
  ADB.adb_sfx_none_eq kid key_k ls None w;
  kd_tu kid key_k (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp) w

let aacc_nil_some (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (w: bytes)
: Lemma (requires (afbacc kid key_k ls fb w)) (ensures (aacc [] (ADB.adb_sfx_some kid key_k ls fb) w))
= let lp = lp key_k ls in
  kd_nonempty kid (ADB.choice_fb_disp_p key_k lp (ADB.adb_fb fb)) w;
  SA.seqa_nil_eq (ADB.adb_sfx_some kid key_k ls fb) None w;
  ADB.adb_sfx_some_eq kid key_k ls fb None w;
  kd_tu kid key_k (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (ADB.adb_fb fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (ADB.adb_fb fb)) w
#pop-options

#push-options "--fuel 1 --ifuel 1"
let lp_cons (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Lemma (lp key_k ((kx, y) :: tl) == (key_of_lit key_k kx, ADB.adb_fb y) :: lp key_k tl)
= ()

let lp_nil (key_k: asn1_terminal_k)
: Lemma (lp key_k [] == [])
= ()

let acc_items (y: asn1_gen_items_lk) (b: bytes)
: Lemma (requires (L.iacc (In.twins_of (dsnd y)) b)) (ensures (L.acc #asn1_weak_parser_kind (Mkgenparser?.p (ADB.adb_fb y)) b))
= ()

let acc_key (kid: asn1_id_t) (key_k: asn1_terminal_k) (b: bytes)
: Lemma (requires (L.acc #asn1_strong_parser_kind (ASN1.Spec.ILC.parse_asn1_ILC kid (asn1_content_as_parser (ASN1_TERMINAL key_k))) b))
  (ensures (L.acc #asn1_strong_parser_kind (ADB.key_p kid key_k) b))
= ()

let ls_tail_ok (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (u: squash (In.supported_ls ((kx, y) :: tl)))
: Tot (squash (In.supported_items (dsnd y) /\ In.supported_ls tl))
= ()
#pop-options

(* A literal key, followed by its payload *)
let lit_ok (kid: asn1_id_t) (key_k: asn1_terminal_k) (x0: asn1_terminal_t key_k) (#k: parser_kind) (#t: Type) (pp: SB.parser k t) (w: bytes) : prop =
  match hdr kid w with
  | None -> False
  | Some (h, l) -> h + l <= Seq.length w /\
    Some? (Sq.consumed (ADB.key_eq_fldata key_k x0 l) (Seq.slice w h (Seq.length w))) /\
    L.acc pp (Seq.slice w (h + l) (Seq.length w))

(* A key that is not a given literal *)
let not_lit (kid: asn1_id_t) (key_k: asn1_terminal_k) (x0: asn1_terminal_t key_k) (w: bytes) : prop =
  match hdr kid w with
  | None -> False
  | Some (h, l) -> h <= Seq.length w /\
    None? (Sq.consumed (ADB.key_eq_fldata key_k x0 l) (Seq.slice w h (Seq.length w)))

#push-options "--z3rlimit 64"
let lit_disp (kid: asn1_id_t) (key_k: asn1_terminal_k) (x0: asn1_terminal_t key_k) (gp: gen_parser asn1_weak_parser_kind)
  (tl: list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind)) (w: bytes)
: Lemma (requires (lit_ok kid key_k x0 #asn1_weak_parser_kind (Mkgenparser?.p gp) w)) (ensures (kd kid (ADB.choice_disp_p key_k ((x0, gp) :: tl)) w))
= let Some (h, l) = hdr kid w in
  let b = Seq.slice w h (Seq.length w) in
  ADB.choice_disp_cons key_k x0 gp tl l b;
  ADB.fldata_eq (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (ADB.key_eq x0)) l b;
  Seq.slice_slice w h (Seq.length w) l (Seq.length b)

let lit_fb_disp (kid: asn1_id_t) (key_k: asn1_terminal_k) (x0: asn1_terminal_t key_k) (gp: gen_parser asn1_weak_parser_kind)
  (tl: list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind)) (fb: gen_parser asn1_weak_parser_kind) (w: bytes)
: Lemma (requires (lit_ok kid key_k x0 #asn1_weak_parser_kind (Mkgenparser?.p gp) w)) (ensures (kd kid (ADB.choice_fb_disp_p key_k ((x0, gp) :: tl) fb) w))
= let Some (h, l) = hdr kid w in
  let b = Seq.slice w h (Seq.length w) in
  ADB.choice_fb_disp_cons key_k x0 gp tl fb l b;
  ADB.fldata_eq (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (ADB.key_eq x0)) l b;
  Seq.slice_slice w h (Seq.length w) l (Seq.length b)

let skip_disp (kid: asn1_id_t) (key_k: asn1_terminal_k) (x0: asn1_terminal_t key_k) (gp: gen_parser asn1_weak_parser_kind)
  (tl: list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind)) (w: bytes)
: Lemma (requires (kd kid (ADB.choice_disp_p key_k tl) w /\ not_lit kid key_k x0 w)) (ensures (kd kid (ADB.choice_disp_p key_k ((x0, gp) :: tl)) w))
= let Some (h, l) = hdr kid w in
  ADB.choice_disp_cons key_k x0 gp tl l (Seq.slice w h (Seq.length w))

let skip_fb_disp (kid: asn1_id_t) (key_k: asn1_terminal_k) (x0: asn1_terminal_t key_k) (gp: gen_parser asn1_weak_parser_kind)
  (tl: list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind)) (fb: gen_parser asn1_weak_parser_kind) (w: bytes)
: Lemma (requires (kd kid (ADB.choice_fb_disp_p key_k tl fb) w /\ not_lit kid key_k x0 w)) (ensures (kd kid (ADB.choice_fb_disp_p key_k ((x0, gp) :: tl) fb) w))
= let Some (h, l) = hdr kid w in
  ADB.choice_fb_disp_cons key_k x0 gp tl fb l (Seq.slice w h (Seq.length w))
#pop-options

(* The same, on the dispatch tables of the schema *)

let lit_adb (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (w: bytes)
: Lemma (requires (lit_ok kid key_k (key_of_lit key_k kx) #asn1_weak_parser_kind (Mkgenparser?.p (ADB.adb_fb y)) w)) (ensures (adbacc kid key_k ((kx, y) :: tl) w))
= lp_cons key_k kx y tl;
  lit_disp kid key_k (key_of_lit key_k kx) (ADB.adb_fb y) (lp key_k tl) w

let lit_afb (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (w: bytes)
: Lemma (requires (lit_ok kid key_k (key_of_lit key_k kx) #asn1_weak_parser_kind (Mkgenparser?.p (ADB.adb_fb y)) w)) (ensures (afbacc kid key_k ((kx, y) :: tl) fb w))
= lp_cons key_k kx y tl;
  lit_fb_disp kid key_k (key_of_lit key_k kx) (ADB.adb_fb y) (lp key_k tl) (ADB.adb_fb fb) w

let adbacc_skip (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (w: bytes)
: Lemma (requires (adbacc kid key_k tl w /\ not_lit kid key_k (key_of_lit key_k kx) w)) (ensures (adbacc kid key_k ((kx, y) :: tl) w))
= lp_cons key_k kx y tl;
  skip_disp kid key_k (key_of_lit key_k kx) (ADB.adb_fb y) (lp key_k tl) w

let afbacc_skip (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (w: bytes)
: Lemma (requires (afbacc kid key_k tl fb w /\ not_lit kid key_k (key_of_lit key_k kx) w)) (ensures (afbacc kid key_k ((kx, y) :: tl) fb w))
= lp_cons key_k kx y tl;
  skip_fb_disp kid key_k (key_of_lit key_k kx) (ADB.adb_fb y) (lp key_k tl) (ADB.adb_fb fb) w

(* The fallback: the key, then the fallback payload *)
let fbacc (kid: asn1_id_t) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (w: bytes) : prop =
  afbacc kid key_k [] fb w

#push-options "--fuel 1 --ifuel 1"
let fb_pl_nil (#t: eqtype) (fb: gen_parser asn1_weak_parser_kind) (x: t) (b: bytes)
: Lemma (Sq.consumed #asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_payload_parser #t [] fb x) b == Sq.consumed #asn1_weak_parser_kind (Mkgenparser?.p fb) b)
= T.parse_synth_eq (Mkgenparser?.p fb) (attach_tag_with_fallback #t [] fb x) b
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 64"
let fbr_acc (kid: asn1_id_t) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (kt xp: bytes)
: Lemma
  (requires (L.acc #asn1_strong_parser_kind (ASN1.Spec.ILC.parse_asn1_ILC kid (asn1_content_as_parser (ASN1_TERMINAL key_k))) kt /\
    L.iacc (In.twins_of (dsnd fb)) xp))
  (ensures (fbacc kid key_k fb (Seq.append kt xp)))
= acc_key kid key_k kt;
  acc_items fb xp;
  lp_nil key_k;
  let w = Seq.append kt xp in
  let lc : list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind) = [] in
  let fb' = ADB.adb_fb fb in
  T.parse_tagged_union_eq (ADB.key_p kid key_k) (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb')) (make_gen_choice_with_fallback_weak_payload_parser lc fb') w;
  assert (Seq.equal (Seq.slice w 0 (Seq.length kt)) kt);
  L.strong_prefix (ADB.key_p kid key_k) kt w;
  let Some (x, c1) = SB.parse (ADB.key_p kid key_k) w in
  assert (c1 == Seq.length kt);
  assert (Seq.equal (Seq.slice w c1 (Seq.length w)) xp);
  fb_pl_nil fb' x xp;
  assert (Sq.consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (ADB.key_p kid key_k) (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb')) (make_gen_choice_with_fallback_weak_payload_parser lc fb')) w == Some (Seq.length w));
  kd_tu kid key_k (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb')) (make_gen_choice_with_fallback_weak_payload_parser lc fb') w;
  let Some (h, l) = hdr kid w in
  assert (ADB.choice_fb_disp_p key_k lc fb' l == ADB.disp_p key_k (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb')) (make_gen_choice_with_fallback_weak_payload_parser lc fb') l)
#pop-options

(* The whole content *)

let acc_content_none
  (ipd: id_decs) (prefix: asn1_gen_items_l ipd)
  (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (w: bytes)
: Lemma (requires (aacc (In.twins_of prefix) (ADB.adb_sfx_none kid key_k ls) w))
  (ensures (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls None pf pf')) w))
= ADB.adb_prefix_content_none ipd prefix kid key_k ls pf pf' w

let acc_content_some
  (ipd: id_decs) (prefix: asn1_gen_items_l ipd)
  (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (w: bytes)
: Lemma (requires (aacc (In.twins_of prefix) (ADB.adb_sfx_some kid key_k ls fb) w))
  (ensures (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some fb) pf pf')) w))
= ADB.adb_prefix_content_some ipd prefix kid key_k ls fb pf pf' w

(* Reading the key back from the output: its identifier, its length, and
   whether its contents are those of the literal `kx`. The result, if any,
   is the end of the key contents (meaningful only if they match) and
   whether they match. *)

let km_post (kid: asn1_id_t) (key_k: asn1_terminal_k) (x0: asn1_terminal_t key_k) (w: bytes) (p2: nat) (res: option (SZ.t & bool)) : prop =
  match res with
  | None -> True
  | Some (e, m) ->
    match hdr kid w with
    | None -> False
    | Some (h, l) -> h <= Seq.length w /\
      (m == true <==> Some? (Sq.consumed (ADB.key_eq_fldata key_k x0 l) (Seq.slice w h (Seq.length w)))) /\
      (m == true ==> (h + l <= Seq.length w /\ SZ.v e == p2 + h + l))

#push-options "--ifuel 2"
private
let vpc_some (#k: parser_kind) (#t: Type) (p: SB.parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t) (x: t)
: Lemma (requires (LowParse.PulseParse.VReader.vreader_postcond p offset v off (Some x)))
  (ensures (SZ.v offset <= SZ.v off /\ SZ.v off <= Seq.length v /\
    SB.parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off - SZ.v offset)))
= ()
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 32"
private
let km_intro (kid: asn1_id_t) (key_k: asn1_terminal_k) (x0: asn1_terminal_t key_k) (v: bytes) (p2 off1 off2 off3: SZ.t)
  (len: LowParse.Spec.BoundedInt.bounded_int32 0 ILC.asn1_length_max) (ok: bool)
: Lemma
  (requires (
    LowParse.PulseParse.VReader.vreader_postcond #asn1_strong_parser_kind parse_asn1_identifier_U32 p2 v off1 (Some kid) /\
    LowParse.PulseParse.VReader.vreader_postcond #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) off1 v off2 (Some len) /\
    U32.v len <= Seq.length v - SZ.v off2 /\
    LPS.validator_postcond (ADB.key_eq_fldata key_k x0 (U32.v len)) off2 v off3 ok))
  (ensures (km_post kid key_k x0 (Seq.slice v (SZ.v p2) (Seq.length v)) (SZ.v p2) (Some (off3, ok))))
= vpc_some #asn1_strong_parser_kind parse_asn1_identifier_U32 p2 v off1 kid;
  vpc_some #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) off1 v off2 len;
  let w = Seq.slice v (SZ.v p2) (Seq.length v) in
  let c1 = SZ.v off1 - SZ.v p2 in
  let c2 = SZ.v off2 - SZ.v off1 in
  let l = U32.v len in
  slice_tail2 v (SZ.v p2) c1;
  slice_tail2 v (SZ.v off1) c2;
  slice_tail2 v (SZ.v p2) (c1 + c2);
  assert (hdr kid w == Some (c1 + c2, l));
  let b2 = Seq.slice v (SZ.v off2) (Seq.length v) in
  assert (Seq.slice w (c1 + c2) (Seq.length w) == b2);
  ADB.fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (ADB.key_eq x0)) l b2
#pop-options

#push-options "--z3rlimit 64"
inline_for_extraction
fn key_match_in (kid: asn1_id_t) (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (kx: asn1_key_lit key_k)
  (input: S.slice U8.t) (p2: SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
requires S.pts_to input #pm v ** pure (SZ.v p2 <= Seq.length v)
returns res: option (SZ.t & bool)
ensures S.pts_to input #pm v ** pure (SZ.v p2 <= Seq.length v /\ km_post kid key_k (key_of_lit key_k kx) (Seq.slice v (SZ.v p2) (Seq.length v)) (SZ.v p2) res)
{
  S.pts_to_len input;
  let mut off = p2;
  let rid = I.vread_identifier input off;
  match rid {
    None -> {
      None #(SZ.t & bool)
    }
    Some id -> {
      if (ILC.asn1_id_eq id kid) {
        with off1 . assert (R.pts_to off off1);
        let rl = ILC.vread_length input off;
        match rl {
          None -> {
            None #(SZ.t & bool)
          }
          Some len -> {
            with off2 . assert (R.pts_to off off2);
            let o2 = !off;
            let rem = SZ.sub (S.len input) o2;
            if (LowParse.Pulse.SizeComparison.u32_lte_sizet len rem) {
              SZ.fits_lte (U32.v len) (SZ.v rem);
              let ok = In.validate_key_eq_fl key_k () kx (SZ.uint32_to_sizet len) input off;
              let e = !off;
              km_intro kid key_k (key_of_lit key_k kx) v p2 off1 off2 e len ok;
              Some (e, ok)
            } else {
              None #(SZ.t & bool)
            }
          }
        }
      } else {
        None #(SZ.t & bool)
      }
    }
  }
}
#pop-options

inline_for_extraction
fn key_match (kid: asn1_id_t) (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (kx: asn1_key_lit key_k)
  (out: S.slice U8.t) (p2 p0: SZ.t) (#v: Ghost.erased bytes)
requires pts_to out v ** pure (SZ.v p2 <= SZ.v p0 /\ SZ.v p0 <= Seq.length v)
returns res: option (SZ.t & bool)
ensures pts_to out v ** pure (SZ.v p2 <= SZ.v p0 /\ SZ.v p0 <= Seq.length v /\ km_post kid key_k (key_of_lit key_k kx) (Seq.slice v (SZ.v p2) (SZ.v p0)) (SZ.v p2) res)
{
  let sp = S.split out p0;
  match sp {
    Mktuple2 s1 s2 -> {
      Seq.slice_slice v 0 (SZ.v p0) (SZ.v p2) (SZ.v p0);
      assert (pure (Seq.slice (Seq.slice v 0 (SZ.v p0)) (SZ.v p2) (Seq.length (Seq.slice v 0 (SZ.v p0))) == Seq.slice v (SZ.v p2) (SZ.v p0)));
      let res = key_match_in kid key_k u kx s1 p2;
      S.join s1 s2 out;
      Seq.lemma_split v (SZ.v p0);
      rewrite (pts_to out (Seq.append (Seq.slice v 0 (SZ.v p0)) (Seq.slice v (SZ.v p0) (Seq.length v))))
        as (pts_to out v);
      res
    }
  }
}

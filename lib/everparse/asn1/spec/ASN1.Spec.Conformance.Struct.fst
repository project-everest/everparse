module ASN1.Spec.Conformance.Struct

(* Conformance of generic ASN.1 DER values to a schema, defined
   structurally on values.

   `ASN1.Spec.Conformance.conforms k v` runs the typed parser of `k` on the
   encoding of `v`. Here, `vconf k v` instead follows the structure of the
   schema `k` and of the value `v`: identifiers, primitive/constructed
   flags and lengths are checked on the value, the components of SEQUENCE,
   SET, SEQUENCE OF, SET OF and ANY DEFINED BY are checked recursively, and
   only the contents of primitive values (terminals) are checked by running
   the corresponding terminal parser. The DER order of SET OF elements is
   still defined on their encodings (X.690 11.6).

   For every well-formed schema `k` (`wf k`), `vconf k v == conforms k v`
   (`vconf_correct` below.) *)

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
open ASN1.Spec.Conformance

module RV = LowParse.Spec.RecursiveVLGen
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Seq = FStar.Seq
module L = FStar.List.Tot

(* Headers and contents of values *)

let vflag_ok (v: asn1_value) : Tot bool =
  match v with
  | ASN1_VALUE_PRIMITIVE id _ -> PRIMITIVE? id.f
  | ASN1_VALUE_CONSTRUCTED id _ -> CONSTRUCTED? id.f

let vcont (v: asn1_value) : Tot bytes =
  match v with
  | ASN1_VALUE_PRIMITIVE _ c -> c
  | ASN1_VALUE_CONSTRUCTED _ l -> asn1_value_list_enc l

(* Whether the header of the value is a DER length *)
let hdr_ok (v: asn1_value) : Tot bool =
  vflag_ok v && Seq.length (vcont v) < 4294967296

(* The encoding of a value, after its identifier *)
let vtl (v: asn1_value) : Tot bytes =
  enc_hdr (vflag_ok v) (Seq.length (vcont v)) `Seq.append` vcont v

(* Running a parser on the whole of some bytes *)
let tparse (#k: parser_kind) (#t: Type) (p: parser k t) (b: bytes) : Tot (option t) =
  match coerce_to_tot_bare_parser _ _ p b with
  | Some (x, n) -> if n = Seq.length b then Some x else None
  | None -> None

(* ANY: values accepted by the generic parser *)

let rec vok (v: asn1_value) : Tot bool (decreases v) =
  hdr_ok v &&
  (match v with
   | ASN1_VALUE_PRIMITIVE id c -> asn1_any_leaf_ok id c
   | ASN1_VALUE_CONSTRUCTED _ l -> vok_list l)

and vok_list (l: list asn1_value) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | v :: q -> vok v && vok_list q

(* SET OF: DER order of the encodings of the elements *)
let rec vsorted (l: list asn1_value) : Tot bool (decreases l) =
  match l with
  | a :: b :: q -> lex_byte_order (asn1_value_enc a) (asn1_value_enc b) && vsorted (b :: q)
  | _ -> true

let not_plain (d: asn1_decorator) : Tot bool =
  match d with
  | PLAIN -> false
  | _ -> true

let fb_precedes' (k: asn1_content_k)
: Lemma
  (requires (ASN1_ANY_DEFINED_BY? k /\ Some? (ASN1_ANY_DEFINED_BY?.fallback k)))
  (ensures (dsnd (Some?.v (ASN1_ANY_DEFINED_BY?.fallback k)) << k))
= match k with
  | ASN1_ANY_DEFINED_BY _ _ _ _ _ (Some fb) _ _ -> ()

let in_s (s: FStar.Set.set asn1_id_t) (v: asn1_value) : Tot bool = FStar.Set.mem (asn1_value_id v) s
let out_s (s: FStar.Set.set asn1_id_t) (v: asn1_value) : Tot bool = not (FStar.Set.mem (asn1_value_id v) s)

(* Structural conformance *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec cconf (k: asn1_content_k) (v: asn1_value) : Tot bool (decreases %[k; 3]) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' r ->
    begin match tparse (asn1_terminal_as_parser k') (vcont v) with
    | Some x -> restriction_pred r x
    | None -> false
    end
  | ASN1_TERMINAL k' -> Some? (tparse (asn1_terminal_as_parser k') (vcont v))
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    begin match v with
    | ASN1_VALUE_CONSTRUCTED _ l -> seqm items l
    | _ -> false
    end
  | ASN1_SET _ items _ ->
    begin match v with
    | ASN1_VALUE_CONSTRUCTED _ l -> value_ids_sorted l && setm items l
    | _ -> false
    end
  | ASN1_SEQUENCE_OF ne k' ->
    begin match v with
    | ASN1_VALUE_CONSTRUCTED _ l -> list_size_ok ne l && vconf_list k' l
    | _ -> false
    end
  | ASN1_SET_OF ne k' ->
    begin match v with
    | ASN1_VALUE_CONSTRUCTED _ l -> list_size_ok ne l && vsorted l && vconf_list k' l
    | _ -> false
    end
  | ASN1_PREFIXED k' ->
    begin match v with
    | ASN1_VALUE_CONSTRUCTED _ [w] -> vconf k' w
    | ASN1_VALUE_CONSTRUCTED _ _ -> false
    | ASN1_VALUE_PRIMITIVE _ c ->
      begin match tparse parse_asn1_value c with
      | Some w -> vconf k' w
      | None -> false
      end
    end
  | ASN1_ANY_DEFINED_BY _ prefix kid key_k ls ofb _ _ ->
    begin match v with
    | ASN1_VALUE_CONSTRUCTED _ l ->
      begin match pfxm prefix l with
      | Some (w :: r) ->
        asn1_value_id w = kid && hdr_ok w &&
        begin match tparse (asn1_terminal_as_parser key_k) (vcont w) with
        | Some x ->
          begin match ofb with
          | None -> lsm key_k ls x r
          | Some fb ->
            let (| _, fbitems |) = fb in
            fb_precedes' k;
            lsm_fb k key_k ls fbitems x r
          end
        | None -> false
        end
      | _ -> false
      end
    | _ -> false
    end

and lsm (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (x: asn1_terminal_t key_k) (r: list asn1_value) : Tot bool (decreases %[ls; 1]) =
  match ls with
  | [] -> false
  | (lit, it) :: tl ->
    let (| _, items |) = it in
    if x = key_of_lit key_k lit
    then seqm items r
    else lsm key_k tl x r

and lsm_fb (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (x: asn1_terminal_t key_k) (r: list asn1_value) : Tot bool (decreases %[k0; 1; ls]) =
  match ls with
  | [] -> seqm fbitems r
  | (lit, it) :: tl ->
    let (| _, items |) = it in
    if x = key_of_lit key_k lit
    then seqm items r
    else lsm_fb k0 key_k tl fbitems x r

and choice_conf (lc: list (asn1_id_t & asn1_content_k)) (v: asn1_value) : Tot bool (decreases %[lc; 0]) =
  match lc with
  | [] -> false
  | (x, c) :: tl ->
    if asn1_value_id v = x
    then cconf c v
    else choice_conf tl v

and vconf (#s: _) (k: asn1_k s) (v: asn1_value) : Tot bool (decreases %[k; 2]) =
  match k with
  | ASN1_ILC id k' -> asn1_value_id v = id && hdr_ok v && cconf k' v
  | ASN1_CHOICE_ILC lc _ -> hdr_ok v && choice_conf lc v
  | ASN1_ANY_ILC -> vok v

and vconf_list (#s: _) (k: asn1_k s) (l: list asn1_value) : Tot bool (decreases %[k; 4; l]) =
  match l with
  | [] -> true
  | v :: q -> vconf k v && vconf_list k q

and itemconf (#s: _) (#d: _) (dk: asn1_decorated_k s d) (v: asn1_value) : Tot bool (decreases %[dk; 0]) =
  match dk with
  | ASN1_PLAIN_ILC k -> vconf k v
  | ASN1_OPTION_ILC k -> vconf k v
  | ASN1_DEFAULT_TERMINAL id #k defv ->
    asn1_value_id v = id && hdr_ok v &&
    begin match tparse (asn1_terminal_as_parser k) (vcont v) with
    | Some x -> not (x = key_of_lit k defv)
    | None -> false
    end
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv ->
    asn1_value_id v = id && hdr_ok v &&
    begin match tparse (asn1_terminal_as_parser k) (vcont v) with
    | Some x -> restriction_pred r x && not (x = key_of_lit k defv)
    | None -> false
    end

(* SEQUENCE: components in declaration order; absent components must be
   OPTIONAL or DEFAULT *)
and seqm (#ids: _) (items: asn1_gen_items_l ids) (l: list asn1_value) : Tot bool (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> Nil? l
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    begin match l with
    | [] -> not_plain d && seqm tl []
    | v :: l' ->
      if FStar.Set.mem (asn1_value_id v) s
      then itemconf dk v && seqm tl l'
      else not_plain d && seqm tl l
    end

(* The prefix of ANY DEFINED BY: returns the remaining values *)
and pfxm (#ids: _) (items: asn1_gen_items_l ids) (l: list asn1_value) : Tot (option (list asn1_value)) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> Some l
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    begin match l with
    | [] -> None
    | v :: l' ->
      if FStar.Set.mem (asn1_value_id v) s
      then (if itemconf dk v then pfxm tl l' else None)
      else if not_plain d then pfxm tl l else None
    end

(* SET: each value belongs to the first component whose identifiers
   contain its identifier; each component appears at most once, and may be
   absent only if OPTIONAL or DEFAULT *)
and setm (#ids: _) (items: asn1_gen_items_l ids) (l: list asn1_value) : Tot bool (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> Nil? l
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    let h = L.filter (in_s s) l in
    let t = L.filter (out_s s) l in
    (match h with
     | [] -> not_plain d
     | [w] -> itemconf dk w
     | _ -> false) &&
    setm tl t
#pop-options

(* Basic lemmas on encodings *)

let enc_split (v: asn1_value)
: Lemma (asn1_value_enc v == asn1_id_enc (asn1_value_id v) `Seq.append` vtl v)
= match v with
  | ASN1_VALUE_PRIMITIVE _ _ -> ()
  | ASN1_VALUE_CONSTRUCTED _ _ -> ()

let list_enc_cons (v: asn1_value) (q: list asn1_value)
: Lemma (asn1_value_list_enc (v :: q) == asn1_value_enc v `Seq.append` asn1_value_list_enc q)
= ()

let exact (#k: parser_kind) (#t: Type) (p: parser k t) (b: bytes) : GTot bool =
  olen (parse p b) = Some (Seq.length b)

let tparse_exact (#k: parser_kind) (#t: Type) (p: parser k t) (b: bytes)
: Lemma (Some? (tparse p b) == exact p b /\
    (match parse p b with
     | Some (x, n) -> n == Seq.length b ==> tparse p b == Some x
     | None -> True))
= ()

private
let slice_append_mid (a c s: bytes)
: Lemma (Seq.slice ((a `Seq.append` c) `Seq.append` s) (Seq.length a) (Seq.length a + Seq.length c) == c)
= Seq.lemma_eq_elim (Seq.slice ((a `Seq.append` c) `Seq.append` s) (Seq.length a) (Seq.length a + Seq.length c)) c

private
let parse_hdr_ok (v: asn1_value) (s: bytes)
: Lemma
  (requires (hdr_ok v))
  (ensures (
    let b = vtl v `Seq.append` s in
    let y = U32.uint_to_t (Seq.length (vcont v)) in
    let sz = Seq.length (enc_len y) in
    vtl v == enc_len y `Seq.append` vcont v /\
    parse parse_asn1_length_u32_t b == Some (y, sz) /\
    sz + U32.v y == Seq.length (vtl v) /\
    Seq.slice b sz (sz + U32.v y) == vcont v))
= let c = vcont v in
  let n = Seq.length c in
  let b = vtl v `Seq.append` s in
  let y = U32.uint_to_t n in
  assert (vtl v == enc_len y `Seq.append` c);
  Seq.append_assoc (enc_len y) c s;
  parse_enc_len y (c `Seq.append` s);
  slice_append_mid (enc_len y) c s

private
let parse_len_ff (b: bytes)
: Lemma
  (requires (Seq.length b > 0 /\ Seq.index b 0 == 0xFFuy))
  (ensures (parse parse_asn1_length_u32_t b == None))
= parse_len_consumed b;
  match parse parse_asn1_length_u32_t b with
  | Some (y, sz) ->
    enc_len_head y;
    assert (Seq.index (Seq.slice b 0 sz) 0 == Seq.index b 0)
  | None -> ()

private
let vtl_not_ok_head (v: asn1_value) (s: bytes)
: Lemma
  (requires (hdr_ok v == false))
  (ensures (let b = vtl v `Seq.append` s in Seq.length b > 0 /\ Seq.index b 0 == 0xFFuy))
= let c = vcont v in
  let n = Seq.length c in
  let h = Seq.create 1 0xFFuy `Seq.append` (Seq.create 1 (if vflag_ok v then 0uy else 1uy) `Seq.append` enc_unary n) in
  assert (enc_hdr (vflag_ok v) n == h);
  Seq.append_assoc h c s;
  index_append_l (Seq.create 1 0xFFuy) (Seq.create 1 (if vflag_ok v then 0uy else 1uy) `Seq.append` enc_unary n) 0;
  index_append_l h (c `Seq.append` s) 0

let parse_hdr (v: asn1_value) (s: bytes)
: Lemma (
    let b = vtl v `Seq.append` s in
    match parse parse_asn1_length_u32_t b with
    | Some (y, sz) -> hdr_ok v /\ U32.v y == Seq.length (vcont v) /\ sz == Seq.length (enc_len y) /\
      Seq.slice b sz (sz + U32.v y) == vcont v /\ sz + U32.v y == Seq.length (vtl v)
    | None -> hdr_ok v == false)
= if hdr_ok v
  then parse_hdr_ok v s
  else begin
    vtl_not_ok_head v s;
    parse_len_ff (vtl v `Seq.append` s)
  end

let vlc (#k: parser_kind) (#t: Type) (p: parser k t) =
  LowParse.Tot.VLGen.parse_vlgen_weak 0 4294967295 parse_asn1_length_u32_t p

#push-options "--z3rlimit 64"
let lc_eq (#k: parser_kind) (#t: Type) (p: parser k t) (v: asn1_value) (s: bytes)
: Lemma (
    let b = vtl v `Seq.append` s in
    olen (parse (vlc p) b) == (if hdr_ok v && exact p (vcont v) then Some (Seq.length (vtl v)) else None) /\
    (match parse (vlc p) b with
     | Some (x, _) -> tparse p (vcont v) == Some x
     | None -> True))
= let b = vtl v `Seq.append` s in
  vlgen_eq p b;
  parse_hdr v s;
  tparse_exact p (vcont v)
#pop-options

let app_slice (a b: bytes)
: Lemma (Seq.slice (a `Seq.append` b) (Seq.length a) (Seq.length (a `Seq.append` b)) == b)
= Seq.lemma_eq_elim (Seq.slice (a `Seq.append` b) (Seq.length a) (Seq.length (a `Seq.append` b))) b

let exact_nondep (#k1 #k2: parser_kind) (#t1 #t2: Type) (p1: parser k1 t1) (p2: parser k2 t2) (b1 b2: bytes) (f: bool)
: Lemma
  (requires (olen (parse p1 (b1 `Seq.append` b2)) == (if f then Some (Seq.length b1) else None)))
  (ensures (exact (p1 `nondep_then` p2) (b1 `Seq.append` b2) == (f && exact p2 b2)))
= nondep_then_eq p1 p2 (b1 `Seq.append` b2);
  app_slice b1 b2

let id_split (v: asn1_value) (s: bytes)
: Lemma (
    let b = asn1_value_enc v `Seq.append` s in
    let n = Seq.length (asn1_id_enc (asn1_value_id v)) in
    parse parse_asn1_identifier_U32 b == Some (asn1_value_id v, n) /\
    Seq.slice b n (Seq.length b) == vtl v `Seq.append` s /\
    Seq.length b == n + Seq.length (vtl v `Seq.append` s) /\
    Seq.length (asn1_value_enc v) == n + Seq.length (vtl v) /\
    (match parse parse_asn1_any_identifier b with
     | Some (id, c) -> (id <: asn1_id_t) == asn1_value_id v /\ c == n
     | None -> False))
= let b = asn1_value_enc v `Seq.append` s in
  enc_split v;
  Seq.append_assoc (asn1_id_enc (asn1_value_id v)) (vtl v) s;
  parse_asn1_identifier_U32_enc (asn1_value_id v) (vtl v `Seq.append` s);
  app_slice (asn1_id_enc (asn1_value_id v)) (vtl v `Seq.append` s);
  parse_any_identifier_consumed b

(* ANY *)

private
let body_olen (id: asn1_any_id_t) (s: bytes) (len: nat) (n: nat) : GTot (option nat) =
  match parse (RV.rec_vlgen_body asn1_value_param pv id) s with
  | Some (_, c) -> if c = len then Some n else None
  | None -> None

private
let pv_hdr_eq (b: bytes) (id: asn1_any_id_t) (hs len: nat)
: Lemma
  (requires (RV.rec_vlgen_header asn1_value_param b == Some (id, hs, len)))
  (ensures (olen (parse pv b) == (if hs + len > Seq.length b then None else body_olen id (Seq.slice b hs (hs + len)) len (hs + len))))
= RV.parse_rec_vlgen_eq asn1_value_param b

private
let twin_len_eq (id: asn1_any_id_t) (b1: bytes) (len: U32.t) (c2: nat)
: Lemma
  (requires (c2 <= Seq.length b1 /\ parse parse_asn1_length_u32_t b1 == Some (len, c2)))
  (ensures (olen (parse (parse_asn1_value_twin id) b1) == (if Seq.length b1 < c2 + U32.v len then None else body_olen id (Seq.slice b1 c2 (c2 + U32.v len)) (U32.v len) (c2 + U32.v len))))
= twin_eq id b1

private
let shift_olen (c1: nat) (o: option nat) : Tot (option nat) =
  match o with Some n -> Some (c1 + n) | None -> None

private
let body_olen_shift (id: asn1_any_id_t) (s: bytes) (len c1 n: nat)
: Lemma (body_olen id s len (c1 + n) == shift_olen c1 (body_olen id s len n))
= ()

private
let pv_hdr_body (b: bytes) (id: asn1_any_id_t) (c1 c2 len: nat)
: Lemma
  (requires (c1 + c2 + len <= Seq.length b /\ RV.rec_vlgen_header asn1_value_param b == Some (id, c1 + c2, len)))
  (ensures (olen (parse pv b) == body_olen id (Seq.slice b (c1 + c2) (c1 + c2 + len)) len (c1 + (c2 + len))))
= pv_hdr_eq b id (c1 + c2) len

private
let pv_twin_body (b: bytes) (id: asn1_any_id_t) (c1 c2 len: nat)
: Lemma
  (requires (c1 + c2 + len <= Seq.length b /\ RV.rec_vlgen_header asn1_value_param b == Some (id, c1 + c2, len)))
  (ensures (olen (parse pv b) == shift_olen c1 (body_olen id (Seq.slice (Seq.slice b c1 (Seq.length b)) c2 (c2 + len)) len (c2 + len))))
= let s = Seq.slice b (c1 + c2) (c1 + c2 + len) in
  body_olen_shift id s len c1 (c2 + len);
  pv_hdr_body b id c1 c2 len;
  slice_slice_3 b c1 c2 len

private
let pv_twin_some (b: bytes) (id: asn1_any_id_t) (c1 c2: nat) (len: U32.t)
: Lemma
  (requires (c1 + c2 <= Seq.length b /\
    RV.rec_vlgen_header asn1_value_param b == Some (id, c1 + c2, U32.v len) /\
    parse parse_asn1_length_u32_t (Seq.slice b c1 (Seq.length b)) == Some (len, c2)))
  (ensures (olen (parse pv b) == shift_olen c1 (olen (parse (parse_asn1_value_twin id) (Seq.slice b c1 (Seq.length b))))))
= let b1 = Seq.slice b c1 (Seq.length b) in
  twin_len_eq id b1 len c2;
  if Seq.length b1 < c2 + U32.v len
  then pv_hdr_eq b id (c1 + c2) (U32.v len)
  else pv_twin_body b id c1 c2 (U32.v len)

let pv_twin (b: bytes) (id: asn1_any_id_t) (c1: nat)
: Lemma
  (requires (c1 <= Seq.length b /\ parse parse_asn1_any_identifier b == Some (id, c1)))
  (ensures (olen (parse pv b) == (match olen (parse (parse_asn1_value_twin id) (Seq.slice b c1 (Seq.length b))) with
    | Some n -> Some (c1 + n)
    | None -> None)))
= let b1 = Seq.slice b c1 (Seq.length b) in
  match parse parse_asn1_length_u32_t b1 with
  | None ->
    RV.parse_rec_vlgen_eq asn1_value_param b;
    twin_eq id b1
  | Some (len, c2) ->
    assert (RV.rec_vlgen_header asn1_value_param b == Some (id, c1 + c2, U32.v len));
    pv_twin_some b id c1 c2 len

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"
let rec any_twin (v: asn1_value) (s: bytes)
: Lemma
  (ensures (olen (parse (parse_asn1_value_twin (asn1_value_id v)) (vtl v `Seq.append` s)) == (if vok v then Some (Seq.length (vtl v)) else None)))
  (decreases %[v; 0])
= let id : asn1_any_id_t = match v with ASN1_VALUE_PRIMITIVE id _ -> id | ASN1_VALUE_CONSTRUCTED id _ -> id in
  let b = vtl v `Seq.append` s in
  twin_eq id b;
  parse_hdr v s;
  match parse parse_asn1_length_u32_t b with
  | None -> ()
  | Some (y, sz) ->
    rec_vlgen_body_eq id (vcont v);
    match v with
    | ASN1_VALUE_PRIMITIVE _ c -> ()
    | ASN1_VALUE_CONSTRUCTED _ l -> any_list l

and any_top (v: asn1_value) (s: bytes)
: Lemma
  (ensures (olen (parse pv (asn1_value_enc v `Seq.append` s)) == (if vok v then Some (Seq.length (asn1_value_enc v)) else None)))
  (decreases %[v; 1])
= let id : asn1_any_id_t = match v with ASN1_VALUE_PRIMITIVE id _ -> id | ASN1_VALUE_CONSTRUCTED id _ -> id in
  let b = asn1_value_enc v `Seq.append` s in
  let n = Seq.length (asn1_id_enc id) in
  id_split v s;
  any_twin v s;
  pv_twin b id n

and any_list (l: list asn1_value)
: Lemma
  (ensures (match parse (tot_parse_list pv) (asn1_value_list_enc l) with
    | Some (_, c) -> vok_list l == true /\ c == Seq.length (asn1_value_list_enc l)
    | None -> vok_list l == false))
  (decreases %[l; 2])
= let b = asn1_value_list_enc l in
  tot_parse_list_eq pv b;
  match l with
  | [] -> ()
  | w :: q ->
    asn1_value_enc_nonempty w;
    any_top w (asn1_value_list_enc q);
    app_slice (asn1_value_enc w) (asn1_value_list_enc q);
    any_list q
#pop-options

(* Identifier, then length-prefixed contents *)

#push-options "--z3rlimit 64"
let ilc_top (id: asn1_id_t) (#ack: asn1_content_k) (p: asn1_weak_parser (asn1_content_t ack)) (v: asn1_value) (s: bytes)
: Lemma (
    let b = asn1_value_enc v `Seq.append` s in
    olen (parse (parse_asn1_ILC id p) b) == (if asn1_value_id v = id && hdr_ok v && exact p (vcont v) then Some (Seq.length (asn1_value_enc v)) else None) /\
    (match parse (parse_asn1_ILC id p) b with
     | Some (x, _) -> tparse p (vcont v) == Some x
     | None -> True))
= let b = asn1_value_enc v `Seq.append` s in
  let pf = parse_asn1_identifier_U32 `parse_filter` (fun id' -> id' = id) in
  parse_synth_eq (pf `nondep_then` parse_asn1_LC p) snd b;
  nondep_then_eq pf (parse_asn1_LC p) b;
  parse_filter_eq parse_asn1_identifier_U32 (fun id' -> id' = id) b;
  id_split v s;
  lc_eq p v s

let ilc_twin (id: asn1_id_t) (#ack: asn1_content_k) (p: asn1_weak_parser (asn1_content_t ack)) (v: asn1_value) (s: bytes)
: Lemma (
    let b = vtl v `Seq.append` s in
    olen (parse (parse_asn1_ILC_twin id p (asn1_value_id v)) b) == (if asn1_value_id v = id && hdr_ok v && exact p (vcont v) then Some (Seq.length (vtl v)) else None) /\
    (match parse (parse_asn1_ILC_twin id p (asn1_value_id v)) b with
     | Some (x, _) -> tparse p (vcont v) == Some x
     | None -> True))
= lc_eq p v s
#pop-options

(* Goodness of parsers w.r.t. a predicate on values *)

let tgood (#k: parser_kind) (#t: Type) (fp: asn1_id_t -> parser k t) (f: asn1_value -> bool) : prop =
  forall (v: asn1_value) (s: bytes). olen (parse (fp (asn1_value_id v)) (vtl v `Seq.append` s)) == (if f v then Some (Seq.length (vtl v)) else None)

let pgood (#k: parser_kind) (#t: Type) (p: parser k t) (f: asn1_value -> bool) : prop =
  forall (v: asn1_value) (s: bytes). olen (parse p (asn1_value_enc v `Seq.append` s)) == (if f v then Some (Seq.length (asn1_value_enc v)) else None)

let cgood (id: asn1_id_t) (k: asn1_content_k) : prop =
  forall (v: asn1_value). (asn1_value_id v == id /\ hdr_ok v == true) ==> exact (asn1_content_as_parser k) (vcont v) == cconf k v

let rec lc_good (lc: list (asn1_id_t & asn1_content_k)) : Tot prop (decreases lc) =
  match lc with
  | [] -> True
  | (x, c) :: tl -> cgood x c /\ lc_good tl

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec choice_payload (lc: list (asn1_id_t & asn1_content_k)) (v: asn1_value) (s: bytes)
: Lemma
  (requires (lc_good lc))
  (ensures (olen (parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) (asn1_value_id v)) (vtl v `Seq.append` s)) == (if hdr_ok v && choice_conf lc v then Some (Seq.length (vtl v)) else None)))
  (decreases lc)
= match lc with
  | [] -> ()
  | (x, c) :: tl ->
    if asn1_value_id v = x
    then begin
      lc_eq (asn1_content_as_parser c) v s;
      tparse_exact (asn1_content_as_parser c) (vcont v)
    end
    else choice_payload tl v s
#pop-options

let kpre (#s: _) (k: asn1_k s) : prop =
  match k with
  | ASN1_ILC id k' -> cgood id k'
  | ASN1_CHOICE_ILC lc _ -> lc_good lc
  | ASN1_ANY_ILC -> True

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let k_twin (#s: _) (k: asn1_k s) (v: asn1_value) (sfx: bytes)
: Lemma
  (requires (kpre k))
  (ensures (olen (parse (snd (asn1_as_parser_twin k) (asn1_value_id v)) (vtl v `Seq.append` sfx)) == (if vconf k v then Some (Seq.length (vtl v)) else None)))
= let id = asn1_value_id v in
  let b = vtl v `Seq.append` sfx in
  match k with
  | ASN1_ILC id0 k' ->
    ilc_twin id0 (asn1_content_as_parser k') v sfx;
    tparse_exact (asn1_content_as_parser k') (vcont v)
  | ASN1_CHOICE_ILC lc pf ->
    let lp = asn1_lc_as_parser lc in
    assert (snd (asn1_as_parser_twin k) id == make_asn1_choice_parser_twin_cases lc pf k lp id);
    LowParse.Spec.Combinators.parse_synth_eq #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser lp id) (synth_tagged_union_data (project_tags lp) id) b;
    choice_payload lc v sfx
  | ASN1_ANY_ILC ->
    assert (snd (asn1_as_parser_twin k) id == parse_asn1_value_twin id);
    any_twin v sfx

let k_top (#s: _) (k: asn1_k s) (v: asn1_value) (sfx: bytes)
: Lemma
  (requires (kpre k))
  (ensures (olen (parse (asn1_as_parser k) (asn1_value_enc v `Seq.append` sfx)) == (if vconf k v then Some (Seq.length (asn1_value_enc v)) else None)))
= let id = asn1_value_id v in
  let b = asn1_value_enc v `Seq.append` sfx in
  match k with
  | ASN1_ILC id0 k' ->
    ilc_top id0 (asn1_content_as_parser k') v sfx;
    tparse_exact (asn1_content_as_parser k') (vcont v)
  | ASN1_CHOICE_ILC lc pf ->
    let lp = asn1_lc_as_parser lc in
    id_split v sfx;
    parse_tagged_union_eq parse_asn1_identifier_U32 (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_strong_payload_parser lp) b;
    choice_payload lc v sfx
  | ASN1_ANY_ILC -> any_top v sfx
#pop-options

(* SEQUENCE items *)

private
let asn1_id_enc_nonempty (id: asn1_id_t)
: Lemma (Seq.length (asn1_id_enc id) > 0)
= let MK_ASN1_ID _ _ n = id in
  if U32.v n < 31
  then assert (Seq.length (asn1_id_enc id) == 1)
  else assert (Seq.length (asn1_id_enc id) == 1 + Seq.length (enc_long n))

let id_empty (b: bytes)
: Lemma (requires (Seq.length b == 0)) (ensures (parse parse_asn1_identifier_U32 b == None))
= parse_asn1_identifier_U32_consumed b;
  match parse parse_asn1_identifier_U32 b with
  | Some (id, c) ->
    asn1_id_enc_nonempty id;
    assert (Seq.length (Seq.slice b 0 c) == 0)
  | None -> ()

let list_enc_empty (l: list asn1_value)
: Lemma (Seq.length (asn1_value_list_enc l) == 0 <==> Nil? l)
= match l with
  | [] -> ()
  | w :: _ -> asn1_value_enc_nonempty w

let exact_ret_nondep (#t1: Type) (x: t1) (#k2: parser_kind) (#t2: Type) (p2: parser k2 t2) (b: bytes)
: Lemma (exact (weaken asn1_strong_parser_kind (parse_ret x) `nondep_then` p2) b == exact p2 b)
= nondep_then_eq (weaken asn1_strong_parser_kind (parse_ret x)) p2 b;
  Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b))

let exact_shift (o1 o2: option nat) (n lb lr: nat)
: Lemma
  (requires (o1 == (match o2 with None -> None | Some m -> Some (n + m)) /\ lb == n + lr))
  (ensures ((o1 = Some lb) == (o2 = Some lr)))
= ()

let and_then_olen (#k: parser_kind) (#t: Type) (p: parser k t) (#k': parser_kind) (#t': Type) (p': (t -> Tot (parser k' t'))) (b: bytes)
: Lemma
  (requires ((and_then_kind k k').parser_kind_injective ==> and_then_cases_injective p'))
  (ensures (olen (parse (p `and_then` p') b) == (match parse p b with
    | None -> None
    | Some (x, n) -> (match olen (parse (p' x) (Seq.slice b n (Seq.length b))) with None -> None | Some m -> Some (n + m)))))
= and_then_eq p p' b

let item_good (#s: _) (#d: _) (dk: asn1_decorated_k s d) : prop =
  tgood (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk)) (itemconf dk) /\
  (forall (v: asn1_value). itemconf dk v == true ==> FStar.Set.mem (asn1_value_id v) s)

let rec items_good (#ids: _) (items: asn1_gen_items_l ids) : Tot prop (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> True
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> item_good dk /\ items_good tl

#push-options "--fuel 2 --ifuel 2"
let rec seqm_nil (#ids: _) (items: asn1_gen_items_l ids)
: Lemma
  (requires (ASN1_GEN_ITEMS_CONS? items))
  (ensures (seqm items [] == Some? (generate_defaultable_items (asn1_sequence_as_parser items))))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    match tl with
    | ASN1_GEN_ITEMS_NIL -> ()
    | _ -> seqm_nil tl
#pop-options

let item_at (#s: _) (#d: _) (dk: asn1_decorated_k s d) (v: asn1_value) (sfx: bytes)
: Lemma
  (requires (item_good dk))
  (ensures (olen (parse (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) (asn1_value_id v)) (vtl v `Seq.append` sfx)) == (if itemconf dk v then Some (Seq.length (vtl v)) else None) /\
    (itemconf dk v == true ==> FStar.Set.mem (asn1_value_id v) s)))
= ()

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let rec seq_none (#ids: _) (items: asn1_gen_items_l ids) (l: list asn1_value)
: Lemma
  (requires (items_good items))
  (ensures (exact (make_asn1_sequence_parser' (asn1_sequence_as_parser items) None) (asn1_value_list_enc l) == seqm items l))
  (decreases %[items; 1])
= let its = asn1_sequence_as_parser items in
  let b = asn1_value_list_enc l in
  seq'_parse its None b;
  list_enc_empty l;
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
    seqm_nil items;
    seq''_parse its None b;
    let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
    let k = glb asn1_strong_parser_kind parse_ret_kind in
    and_then_eq (weaken k parse_asn1_identifier_U32) pbt b;
    match l with
    | [] -> id_empty b
    | w :: q ->
      assert (b == asn1_value_enc w `Seq.append` asn1_value_list_enc q);
      id_split w (asn1_value_list_enc q);
      seq_twin items w q;
      assert (parse (weaken k parse_asn1_identifier_U32) b == parse parse_asn1_identifier_U32 b);
      assert (olen (parse (make_asn1_sequence_parser' its None) b) == olen (parse (weaken k parse_asn1_identifier_U32 `and_then` pbt) b));
      let n = Seq.length (asn1_id_enc (asn1_value_id w)) in
      let r = vtl w `Seq.append` asn1_value_list_enc q in
      and_then_olen (weaken k parse_asn1_identifier_U32) pbt b;
      assert (olen (parse (weaken k parse_asn1_identifier_U32 `and_then` pbt) b) == (match olen (parse (pbt (asn1_value_id w)) r) with None -> None | Some m -> Some (n + m)));
      exact_shift (olen (parse (make_asn1_sequence_parser' its None) b)) (olen (parse (pbt (asn1_value_id w)) r)) n (Seq.length b) (Seq.length r)

and seq_some (#ids: _) (items: asn1_gen_items_l ids) (v: asn1_value) (l: list asn1_value)
: Lemma
  (requires (items_good items))
  (ensures (exact (make_asn1_sequence_parser' (asn1_sequence_as_parser items) (Some (asn1_value_id v))) (vtl v `Seq.append` asn1_value_list_enc l) == seqm items (v :: l)))
  (decreases %[items; 1])
= let its = asn1_sequence_as_parser items in
  let id = asn1_value_id v in
  let b = vtl v `Seq.append` asn1_value_list_enc l in
  seq'_parse its (Some id) b;
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
    seq''_parse its (Some id) b;
    let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
    let k = glb asn1_strong_parser_kind parse_ret_kind in
    and_then_olen (weaken k (parse_ret id)) pbt b;
    Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
    assert (olen (parse (make_asn1_sequence_parser' its (Some id)) b) == olen (parse (pbt id) b));
    seq_twin items v l

and seq_twin (#ids: _) (items: asn1_gen_items_l ids) (v: asn1_value) (l: list asn1_value)
: Lemma
  (requires (ASN1_GEN_ITEMS_CONS? items /\ items_good items))
  (ensures (exact (make_asn1_sequence_parser_body_twin (asn1_sequence_as_parser items) make_asn1_sequence_parser' (asn1_value_id v)) (vtl v `Seq.append` asn1_value_list_enc l) == seqm items (v :: l)))
  (decreases %[items; 0])
= let its = asn1_sequence_as_parser items in
  let id = asn1_value_id v in
  let b = vtl v `Seq.append` asn1_value_list_enc l in
  body_twin_eq its id b;
  list_enc_empty l;
  match items with
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    let hd = asn1_decorated_as_parser_twin dk in
    item_at dk v (asn1_value_list_enc l);
    assert (its == hd :: asn1_sequence_as_parser tl);
    match tl with
    | ASN1_GEN_ITEMS_NIL -> ()
    | _ ->
      if FStar.Set.mem id s
      then begin
        exact_nondep (parse_asn1_sequence_item_twin hd id) (make_asn1_sequence_parser' (asn1_sequence_as_parser tl) None) (vtl v) (asn1_value_list_enc l) (itemconf dk v);
        seq_none tl l
      end
      else match d with
      | PLAIN -> ()
      | _ ->
        let Some defv = generate_defaultable_item hd in
        exact_ret_nondep defv (make_asn1_sequence_parser' (asn1_sequence_as_parser tl) (Some id)) b;
        seq_some tl v l
#pop-options

(* Items *)

let rec mem_as_set'' (#a: eqtype) (x: a) (l: list a)
: Lemma (ensures (FStar.Set.mem x (FStar.Set.as_set' l) <==> L.mem x l)) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> mem_as_set'' x q

let rec choice_conf_mem (lc: list (asn1_id_t & asn1_content_k)) (v: asn1_value)
: Lemma (ensures (choice_conf lc v ==> L.mem (asn1_value_id v) (L.map fst lc))) (decreases lc)
= match lc with
  | [] -> ()
  | _ :: tl -> choice_conf_mem tl v

let k_mem (#s: _) (k: asn1_k s) (v: asn1_value)
: Lemma (vconf k v ==> FStar.Set.mem (asn1_value_id v) s)
= match k with
  | ASN1_ILC _ _ -> ()
  | ASN1_CHOICE_ILC lc _ ->
    choice_conf_mem lc v;
    mem_as_set'' (asn1_value_id v) (L.map fst lc)
  | ASN1_ANY_ILC -> ()

let dkpre (#s: _) (#d: _) (dk: asn1_decorated_k s d) : prop =
  match dk with
  | ASN1_PLAIN_ILC k -> kpre k
  | ASN1_OPTION_ILC k -> kpre k
  | _ -> True

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let dec_at (#s: _) (#d: _) (dk: asn1_decorated_k s d) (v: asn1_value) (sfx: bytes)
: Lemma
  (requires (dkpre dk))
  (ensures (olen (parse (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) (asn1_value_id v)) (vtl v `Seq.append` sfx)) == (if itemconf dk v then Some (Seq.length (vtl v)) else None) /\
    (itemconf dk v == true ==> FStar.Set.mem (asn1_value_id v) s)))
= let item = asn1_decorated_as_parser_twin dk in
  let id = asn1_value_id v in
  let b = vtl v `Seq.append` sfx in
  match dk with
  | ASN1_PLAIN_ILC k -> k_twin k v sfx; k_mem k v
  | ASN1_OPTION_ILC k ->
    k_twin k v sfx; k_mem k v;
    parse_synth_eq (Mkgendcparser?.fp item id) Some b
  | ASN1_DEFAULT_TERMINAL id0 #k defv_l ->
    let defv = key_of_lit k defv_l in
    let fp = Mkgendcparser?.fp item in
    let p = asn1_terminal_as_parser k in
    ilc_twin id0 #(ASN1_TERMINAL k) p v sfx;
    tparse_exact p (vcont v);
    parse_synth_eq ((fp id) `parse_filter` (defaultv_filter defv)) (defaultv_synth defv) b;
    parse_filter_eq (fp id) (defaultv_filter defv) b
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv_l ->
    let defv : parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let fp = Mkgendcparser?.fp item in
    let d = Mkgendcparser?.d item in
    let p0 = asn1_terminal_as_parser k in
    let p : asn1_weak_parser (asn1_decorated_pure_t d) = weaken _ (p0 `parse_filter` (restriction_pred r)) in
    ilc_twin id0 #(ASN1_RESTRICTED_TERMINAL k r) p v sfx;
    tparse_exact p (vcont v);
    tparse_exact p0 (vcont v);
    parse_filter_eq p0 (restriction_pred r) (vcont v);
    parse_synth_eq (((fp id) `parse_filter` (restriction_pred r)) `parse_filter` (defaultv_filter #(asn1_decorated_pure_t d) defv)) (defaultv_synth #(asn1_decorated_pure_t d) defv) b;
    parse_filter_eq ((fp id) `parse_filter` (restriction_pred r)) (defaultv_filter #(asn1_decorated_pure_t d) defv) b;
    parse_filter_eq (fp id) (restriction_pred r) b
#pop-options

let dec_good (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (requires (dkpre dk)) (ensures (item_good dk))
= let f (v: asn1_value) (sfx: bytes) : Lemma
    (olen (parse (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin dk) (asn1_value_id v)) (vtl v `Seq.append` sfx)) == (if itemconf dk v then Some (Seq.length (vtl v)) else None))
  = dec_at dk v sfx
  in
  let g (v: asn1_value) : Lemma (itemconf dk v == true ==> FStar.Set.mem (asn1_value_id v) s)
  = dec_at dk v Seq.empty
  in
  Classical.forall_intro_2 f;
  Classical.forall_intro g

(* SEQUENCE OF, SET OF *)

let rec lall (f: asn1_value -> bool) (l: list asn1_value) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | v :: q -> f v && lall f q

let rec vsorted_from (prev: bytes) (l: list asn1_value) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | a :: q -> lex_byte_order prev (asn1_value_enc a) && vsorted_from (asn1_value_enc a) q

let rec vsorted_from_eq (a: asn1_value) (q: list asn1_value)
: Lemma (ensures (vsorted (a :: q) == vsorted_from (asn1_value_enc a) q)) (decreases q)
= match q with
  | [] -> ()
  | b :: q' -> vsorted_from_eq b q'

let pgood_at (#t: Type) (p: asn1_strong_parser t) (f: asn1_value -> bool) (w: asn1_value) (q: list asn1_value)
: Lemma
  (requires (pgood p f))
  (ensures (
    let b = asn1_value_list_enc (w :: q) in
    let n = Seq.length (asn1_value_enc w) in
    Seq.length b > 0 /\
    olen (parse p b) == (if f w then Some n else None) /\
    n <= Seq.length b /\
    Seq.slice b 0 n == asn1_value_enc w /\
    Seq.slice b n (Seq.length b) == asn1_value_list_enc q))
= let b = asn1_value_list_enc (w :: q) in
  asn1_value_enc_nonempty w;
  app_slice (asn1_value_enc w) (asn1_value_list_enc q);
  Seq.lemma_eq_elim (Seq.slice b 0 (Seq.length (asn1_value_enc w))) (asn1_value_enc w)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"
let rec list_good (#t: Type) (p: asn1_strong_parser t) (f: asn1_value -> bool) (l: list asn1_value)
: Lemma
  (requires (pgood p f))
  (ensures (match parse (parse_list p) (asn1_value_list_enc l) with
    | Some (xs, c) -> lall f l == true /\ c == Seq.length (asn1_value_list_enc l) /\ L.length xs == L.length l
    | None -> lall f l == false))
  (decreases l)
= let b = asn1_value_list_enc l in
  assert (parse (parse_list p) b == parse (tot_parse_list p) b);
  tot_parse_list_eq p b;
  match l with
  | [] -> ()
  | w :: q ->
    pgood_at p f w q; list_good p f q;
    let bq = asn1_value_list_enc q in
    assert (parse (parse_list p) bq == parse (tot_parse_list p) bq);
    match parse p b, parse (tot_parse_list p) bq with
    | Some (x, n), Some (xs, n') ->
      assert (parse (tot_parse_list p) b == Some (x :: xs, n + n'))
    | _ -> ()

let rec sorted_aux_good (ord: bytes -> bytes -> bool) (#t: Type) (p: asn1_strong_parser t) (f: asn1_value -> bool) (prev: bytes) (l: list asn1_value)
: Lemma
  (requires (pgood p f /\ (forall x y. ord x y == lex_byte_order x y)))
  (ensures (match tot_parse_byte_sorted_list_aux ord p prev (asn1_value_list_enc l) with
    | Some (xs, c) -> lall f l == true /\ vsorted_from prev l == true /\ c == Seq.length (asn1_value_list_enc l) /\ L.length xs == L.length l
    | None -> (lall f l && vsorted_from prev l) == false))
  (decreases l)
= match l with
  | [] -> ()
  | w :: q ->
    pgood_at p f w q; sorted_aux_good ord p f (asn1_value_enc w) q;
    let b = asn1_value_list_enc l in
    let bq = asn1_value_list_enc q in
    assert (parse p b == p b);
    match p b with
    | None -> assert (tot_parse_byte_sorted_list_aux ord p prev b == None)
    | Some (x, n) ->
      assert (Seq.slice b 0 n == asn1_value_enc w);
      assert (Seq.slice b n (Seq.length b) == bq);
      match tot_parse_byte_sorted_list_aux ord p (asn1_value_enc w) bq with
      | None -> assert (tot_parse_byte_sorted_list_aux ord p prev b == None)
      | Some (xs, n') ->
        assert (tot_parse_byte_sorted_list_aux ord p prev b == (if ord prev (asn1_value_enc w) then Some (x :: xs, n + n') else None))

let sorted_good (ord: bytes -> bytes -> bool) (#t: Type) (p: asn1_strong_parser t) (f: asn1_value -> bool) (l: list asn1_value)
: Lemma
  (requires (pgood p f /\ (forall x y. ord x y == lex_byte_order x y)))
  (ensures (match tot_parse_byte_sorted_list_bare ord p (asn1_value_list_enc l) with
    | Some (xs, c) -> lall f l == true /\ vsorted l == true /\ c == Seq.length (asn1_value_list_enc l) /\ L.length xs == L.length l
    | None -> (lall f l && vsorted l) == false))
= match l with
  | [] -> ()
  | w :: q ->
    pgood_at p f w q; vsorted_from_eq w q; sorted_aux_good ord p f (asn1_value_enc w) q;
    let b = asn1_value_list_enc l in
    let bq = asn1_value_list_enc q in
    assert (parse p b == p b);
    match p b with
    | None -> ()
    | Some (x, n) ->
      assert (Seq.slice b 0 n == asn1_value_enc w);
      assert (Seq.slice b n (Seq.length b) == bq);
      match tot_parse_byte_sorted_list_aux ord p (asn1_value_enc w) bq with
      | None -> assert (tot_parse_byte_sorted_list_bare ord p b == None)
      | Some (xs, n') ->
        assert (tot_parse_byte_sorted_list_bare ord p b == Some (x :: xs, n + n'))
#pop-options

let size_ok_len (#t1 #t2: Type) (ne: bool) (l1: list t1) (l2: list t2)
: Lemma (requires (L.length l1 == L.length l2)) (ensures (list_size_ok ne l1 == list_size_ok ne l2))
= ()

let seq_of_good (ne: bool) (#t: Type) (p: asn1_strong_parser t) (f: asn1_value -> bool) (l: list asn1_value)
: Lemma
  (requires (pgood p f))
  (ensures (exact (parse_sized_list ne p) (asn1_value_list_enc l) == (list_size_ok ne l && lall f l)))
= let b = asn1_value_list_enc l in
  parse_filter_eq (parse_list p) (list_size_ok ne) b;
  list_good p f l;
  match parse (parse_list p) b with
  | Some (xs, _) -> size_ok_len ne xs l
  | None -> ()

let set_of_good (ne: bool) (#t: Type) (p: asn1_strong_parser t) (f: asn1_value -> bool) (l: list asn1_value)
: Lemma
  (requires (pgood p f))
  (ensures (exact (parse_sized_set ne p) (asn1_value_list_enc l) == (list_size_ok ne l && vsorted l && lall f l)))
= let b = asn1_value_list_enc l in
  let tord : (x: bytes -> y: bytes -> Pure bool True (fun z -> z == true <==> prop_order_of_bool_order lex_byte_order x y)) =
    fun x1 x2 -> lex_byte_order x1 x2 in
  let ord : bytes -> bytes -> bool = tord in
  parse_filter_eq (parse_asn1_set_of p) (list_size_ok ne) b;
  tot_parse_byte_sorted_list_correct (prop_order_of_bool_order lex_byte_order) tord p b;
  let q = tot_parse_byte_sorted_list lex_byte_order p in
  assert (parse (parse_asn1_set_of p) b == parse q b);
  assert (parse q b == q b);
  assert (q b == LowParse.Spec.Base.parse (parse_byte_sorted_list (prop_order_of_bool_order lex_byte_order) #_ #asn1_strong_parser_kind p) b);
  assert (parse (parse_asn1_set_of p) b == tot_parse_byte_sorted_list_bare ord p b);
  sorted_good ord p f l;
  match parse (parse_asn1_set_of p) b with
  | Some (xs, _) -> size_ok_len ne xs l
  | None -> ()

let rec vconf_list_lall (#s: _) (k: asn1_k s) (l: list asn1_value)
: Lemma (ensures (vconf_list k l == lall (vconf k) l)) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> vconf_list_lall k q

let k_pgood (#s: _) (k: asn1_k s)
: Lemma (requires (kpre k)) (ensures (pgood (asn1_as_parser k) (vconf k)))
= Classical.forall_intro_2 (k_top k)

(* PREFIXED *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let prefixed_good (#s: _) (k': asn1_k s) (v: asn1_value)
: Lemma
  (requires (kpre k' /\ sound (asn1_as_parser k')))
  (ensures (exact (asn1_as_parser k') (vcont v) == cconf (ASN1_PREFIXED k') v))
= let p = asn1_as_parser k' in
  let c = vcont v in
  let no_value () : Lemma
    (requires (match parse pv c with Some (_, n) -> n <> Seq.length c | None -> True))
    (ensures (exact p c == false))
  = match parse p c with
    | Some (_, n) -> assert (value_at c n == true)
    | None -> ()
  in
  match v with
  | ASN1_VALUE_CONSTRUCTED _ l ->
    begin match l with
    | [] ->
      begin match parse p c with
      | Some (_, n) -> assert (value_at c n == true); value_at_pos c n
      | None -> ()
      end
    | [w] ->
      k_top k' w Seq.empty;
      Seq.append_empty_r (asn1_value_enc w)
    | w :: w2 :: r ->
      k_top k' w (asn1_value_list_enc (w2 :: r));
      asn1_value_enc_nonempty w2
    end
  | ASN1_VALUE_PRIMITIVE _ _ ->
    parse_asn1_value_consumed c;
    assert (parse parse_asn1_value c == parse pv c);
    match parse pv c with
    | Some (w, n) ->
      if n = Seq.length c
      then begin
        Seq.lemma_eq_elim (Seq.slice c 0 n) c;
        k_top k' w Seq.empty;
        Seq.append_empty_r (asn1_value_enc w)
      end
      else no_value ()
    | None -> no_value ()
#pop-options

(* ANY DEFINED BY: the prefix machine, parametric in the suffix *)

let sfx_good (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sf: list asn1_value -> bool) : prop =
  (forall (l: list asn1_value). exact (Mkparsertwin?.p sfx) (asn1_value_list_enc l) == sf l) /\
  (forall (v: asn1_value) (l: list asn1_value). exact (Mkparsertwin?.fp sfx (asn1_value_id v)) (vtl v `Seq.append` asn1_value_list_enc l) == sf (v :: l))

let pfx_res (#ids: _) (items: asn1_gen_items_l ids) (sf: list asn1_value -> bool) (l: list asn1_value) : Tot bool =
  match pfxm items l with
  | Some r -> sf r
  | None -> false

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let rec any_none (#ids: _) (items: asn1_gen_items_l ids) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sf: list asn1_value -> bool) (l: list asn1_value)
: Lemma
  (requires (items_good items /\ sfx_good sfx sf))
  (ensures (exact (make_asn1_sequence_any_parser' (asn1_sequence_as_parser items) sfx None) (asn1_value_list_enc l) == pfx_res items sf l))
  (decreases %[items; 1])
= let its = asn1_sequence_as_parser items in
  let b = asn1_value_list_enc l in
  any'_parse its sfx None b;
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
    let pb = make_asn1_sequence_any_parser'' its sfx in
    and_then_olen (any_guard_p None) pb b;
    assert (parse (any_guard_p None) b == parse parse_asn1_identifier_U32 b);
    match l with
    | [] -> id_empty b
    | w :: q ->
      assert (b == asn1_value_enc w `Seq.append` asn1_value_list_enc q);
      id_split w (asn1_value_list_enc q);
      let n = Seq.length (asn1_id_enc (asn1_value_id w)) in
      let r = vtl w `Seq.append` asn1_value_list_enc q in
      assert (olen (parse (make_asn1_sequence_any_parser' its sfx None) b) == (match olen (parse (pb (asn1_value_id w)) r) with None -> None | Some m -> Some (n + m)));
      exact_shift (olen (parse (make_asn1_sequence_any_parser' its sfx None) b)) (olen (parse (pb (asn1_value_id w)) r)) n (Seq.length b) (Seq.length r);
      any_tw items sfx sf w q

and any_some (#ids: _) (items: asn1_gen_items_l ids) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sf: list asn1_value -> bool) (v: asn1_value) (l: list asn1_value)
: Lemma
  (requires (items_good items /\ sfx_good sfx sf))
  (ensures (exact (make_asn1_sequence_any_parser' (asn1_sequence_as_parser items) sfx (Some (asn1_value_id v))) (vtl v `Seq.append` asn1_value_list_enc l) == pfx_res items sf (v :: l)))
  (decreases %[items; 1])
= let its = asn1_sequence_as_parser items in
  let id = asn1_value_id v in
  let b = vtl v `Seq.append` asn1_value_list_enc l in
  any'_parse its sfx (Some id) b;
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
    let pb = make_asn1_sequence_any_parser'' its sfx in
    and_then_olen (any_guard_p (Some id)) pb b;
    assert (parse (any_guard_p (Some id)) b == parse (parse_ret id) b);
    Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
    assert (olen (parse (make_asn1_sequence_any_parser' its sfx (Some id)) b) == olen (parse (pb id) b));
    any_tw items sfx sf v l

and any_tw (#ids: _) (items: asn1_gen_items_l ids) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sf: list asn1_value -> bool) (v: asn1_value) (l: list asn1_value)
: Lemma
  (requires (ASN1_GEN_ITEMS_CONS? items /\ items_good items /\ sfx_good sfx sf))
  (ensures (exact (make_asn1_sequence_any_parser'' (asn1_sequence_as_parser items) sfx (asn1_value_id v)) (vtl v `Seq.append` asn1_value_list_enc l) == pfx_res items sf (v :: l)))
  (decreases %[items; 0])
= let its = asn1_sequence_as_parser items in
  let id = asn1_value_id v in
  let b = vtl v `Seq.append` asn1_value_list_enc l in
  any''_parse its sfx id b;
  match items with
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    let hd = asn1_decorated_as_parser_twin dk in
    item_at dk v (asn1_value_list_enc l);
    assert (its == hd :: asn1_sequence_as_parser tl);
    if FStar.Set.mem id s
    then begin
      exact_nondep (parse_asn1_sequence_item_twin hd id) (make_asn1_sequence_any_parser' (asn1_sequence_as_parser tl) sfx None) (vtl v) (asn1_value_list_enc l) (itemconf dk v);
      any_none tl sfx sf l
    end
    else match d with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      exact_ret_nondep defv (make_asn1_sequence_any_parser' (asn1_sequence_as_parser tl) sfx (Some id)) b;
      any_some tl sfx sf v l
#pop-options

(* ANY DEFINED BY: the suffix *)

let ilc_empty (id: asn1_id_t) (#ack: asn1_content_k) (p: asn1_weak_parser (asn1_content_t ack)) (b: bytes)
: Lemma (requires (Seq.length b == 0)) (ensures (parse (parse_asn1_ILC id p) b == None))
= let pf = parse_asn1_identifier_U32 `parse_filter` (fun id' -> id' = id) in
  parse_synth_eq (pf `nondep_then` parse_asn1_LC p) snd b;
  nondep_then_eq pf (parse_asn1_LC p) b;
  parse_filter_eq parse_asn1_identifier_U32 (fun id' -> id' = id) b;
  id_empty b

let sfm (kid: asn1_id_t) (key_k: asn1_terminal_k) (pm: asn1_terminal_t key_k -> list asn1_value -> bool) (r: list asn1_value) : Tot bool =
  match r with
  | [] -> false
  | w :: r' ->
    asn1_value_id w = kid && hdr_ok w &&
    (match tparse (asn1_terminal_as_parser key_k) (vcont w) with
     | Some x -> pm x r'
     | None -> false)

let pay_good (#key_k: asn1_terminal_k) (#data_t: Type) (#tag: data_t -> asn1_terminal_t key_k) (#k: parser_kind)
  (pay: (x: asn1_terminal_t key_k) -> parser k (refine_with_tag tag x)) (pm: asn1_terminal_t key_k -> list asn1_value -> bool) : prop =
  forall (x: asn1_terminal_t key_k) (r: list asn1_value). exact (pay x) (asn1_value_list_enc r) == pm x r

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let tu_top (kid: asn1_id_t) (key_k: asn1_terminal_k) (#data_t: Type) (tag: data_t -> asn1_terminal_t key_k) (#k: parser_kind)
  (pay: (x: asn1_terminal_t key_k) -> parser k (refine_with_tag tag x)) (pm: asn1_terminal_t key_k -> list asn1_value -> bool) (l: list asn1_value)
: Lemma
  (requires (pay_good pay pm))
  (ensures (exact (parse_tagged_union (parse_asn1_ILC kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k)) tag pay) (asn1_value_list_enc l) == sfm kid key_k pm l))
= let tp = asn1_terminal_as_parser key_k in
  let kp = parse_asn1_ILC kid #(ASN1_TERMINAL key_k) tp in
  let b = asn1_value_list_enc l in
  parse_tagged_union_eq kp tag pay b;
  match l with
  | [] -> ilc_empty kid #(ASN1_TERMINAL key_k) tp b
  | w :: r ->
    ilc_top kid #(ASN1_TERMINAL key_k) tp w (asn1_value_list_enc r);
    tparse_exact tp (vcont w);
    app_slice (asn1_value_enc w) (asn1_value_list_enc r)

let tu_twin (kid: asn1_id_t) (key_k: asn1_terminal_k) (#data_t: Type) (tag: data_t -> asn1_terminal_t key_k) (#k: parser_kind)
  (pay: (x: asn1_terminal_t key_k) -> parser k (refine_with_tag tag x)) (pm: asn1_terminal_t key_k -> list asn1_value -> bool) (v: asn1_value) (l: list asn1_value)
: Lemma
  (requires (pay_good pay pm))
  (ensures (exact (parse_tagged_union (parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k) (asn1_value_id v)) tag pay) (vtl v `Seq.append` asn1_value_list_enc l) == sfm kid key_k pm (v :: l)))
= let tp = asn1_terminal_as_parser key_k in
  let kp = parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) tp (asn1_value_id v) in
  let b = vtl v `Seq.append` asn1_value_list_enc l in
  parse_tagged_union_eq kp tag pay b;
  ilc_twin kid #(ASN1_TERMINAL key_k) tp v (asn1_value_list_enc l);
  tparse_exact tp (vcont v);
  app_slice (vtl v) (asn1_value_list_enc l)
#pop-options

let rec ls_good (#t: eqtype) (ls: list (t & asn1_gen_items_lk)) : Tot prop (decreases ls) =
  match ls with
  | [] -> True
  | (_, it) :: tl -> items_good (dsnd it) /\ ls_good tl

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec pay_at (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (x: asn1_terminal_t key_k) (r: list asn1_value)
: Lemma
  (requires (ls_good ls))
  (ensures (exact (make_gen_choice_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) x) (asn1_value_list_enc r) == lsm key_k ls x r))
  (decreases ls)
= let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  let b = asn1_value_list_enc r in
  match ls with
  | [] -> ()
  | (lit, it) :: tl ->
    let (| _, items |) = it in
    let gp = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser items)) in
    assert (lp == (key_of_lit key_k lit, gp) :: asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) tl);
    if x = key_of_lit key_k lit
    then begin
      parse_synth_eq (Mkgenparser?.p gp) (attach_tag lp x) b;
      seq_none items r
    end
    else begin
      pay_at key_k tl x r;
      parse_synth_eq (make_gen_choice_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) tl) x) (fun y -> lemma_choice_cast (fst (key_of_lit key_k lit, gp), Mkgenparser?.t gp) (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) tl)) x y) b
    end

let rec pay_fb_at (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (x: asn1_terminal_t key_k) (r: list asn1_value)
: Lemma
  (requires (ls_good ls /\ items_good fbitems))
  (ensures (exact (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser fbitems))) x) (asn1_value_list_enc r) == lsm_fb k0 key_k ls fbitems x r))
  (decreases ls)
= let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  let fb = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser fbitems)) in
  let b = asn1_value_list_enc r in
  match ls with
  | [] ->
    parse_synth_eq (Mkgenparser?.p fb) (attach_tag_with_fallback lp fb x) b;
    seq_none fbitems r
  | (lit, it) :: tl ->
    let (| _, items |) = it in
    let gp = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser items)) in
    assert (lp == (key_of_lit key_k lit, gp) :: asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) tl);
    if x = key_of_lit key_k lit
    then begin
      parse_synth_eq (Mkgenparser?.p gp) (attach_tag_with_fallback lp fb x) b;
      seq_none items r
    end
    else begin
      pay_fb_at k0 key_k tl fbitems x r;
      parse_synth_eq (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) tl) fb x) (fun y -> lemma_choice_with_fallback_cast (fst (key_of_lit key_k lit, gp), Mkgenparser?.t gp) (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) tl)) (Mkgenparser?.t fb) x y) b
    end
#pop-options

(* SET *)

let rec elem_ok (#ids: _) (items: asn1_gen_items_l ids) (v: asn1_value) : Tot bool (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> false
  | ASN1_GEN_ITEMS_CONS s _ dk _ tl -> if in_s s v then itemconf dk v else elem_ok tl v

let rec comp_idx (#ids: _) (items: asn1_gen_items_l ids) (id: asn1_id_t) : Tot nat (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> 0
  | ASN1_GEN_ITEMS_CONS s _ _ _ tl -> if FStar.Set.mem id s then 0 else 1 + comp_idx tl id

let rec elem_idx (its: list gen_decorated_parser_twin) (e: set_elem_t its) : Tot nat (decreases its) =
  match its with
  | hd :: tl ->
    let e0 : either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl) = e in
    match e0 with
    | Inl _ -> 0
    | Inr e' -> 1 + elem_idx tl e'

let erel (#ids: _) (items: asn1_gen_items_l ids) (e: set_elem_t (asn1_sequence_as_parser items)) (v: asn1_value) : Tot bool =
  elem_idx _ e = comp_idx items (asn1_value_id v) && elem_tag _ e = Some (asn1_value_id v)

let rec rrel (#b: Type) (rb: b -> asn1_value -> bool) (ys: list b) (l: list asn1_value) : Tot bool (decreases ys) =
  match ys, l with
  | [], [] -> true
  | y :: ys', v :: l' -> rb y v && rrel rb ys' l'
  | _ -> false

let rec prel (#a #b: Type) (s: FStar.Set.set asn1_id_t) (rb: b -> asn1_value -> bool) (xs: list (either a b)) (l: list asn1_value) : Tot bool (decreases xs) =
  match xs, l with
  | [], [] -> true
  | Inl _ :: xs', v :: l' -> in_s s v && prel s rb xs' l'
  | Inr y :: xs', v :: l' -> out_s s v && rb y v && prel s rb xs' l'
  | _ -> false

let rec ht_gen (#a #b: Type) (s: FStar.Set.set asn1_id_t) (rb: b -> asn1_value -> bool) (xs: list (either a b)) (l: list asn1_value)
: Lemma
  (requires (prel s rb xs l))
  (ensures (L.length (heads xs) == L.length (L.filter (in_s s) l) /\ rrel rb (tails xs) (L.filter (out_s s) l)))
  (decreases xs)
= match xs, l with
  | [], [] -> ()
  | _ :: xs', _ :: l' -> ht_gen s rb xs' l'

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec rrel_prel (#ids: _) (items: asn1_gen_items_l ids { ASN1_GEN_ITEMS_CONS? items }) (xs: list (set_elem_t (asn1_sequence_as_parser items))) (l: list asn1_value)
: Lemma
  (requires (rrel (erel items) xs l))
  (ensures (
    let ASN1_GEN_ITEMS_CONS s _ dk _ tl = items in
    let hd = asn1_decorated_as_parser_twin dk in
    let xs' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t (asn1_sequence_as_parser tl))) = xs in
    prel s (erel tl) xs' l))
  (decreases xs)
= match xs, l with
  | [], [] -> ()
  | _ :: xs', _ :: l' -> rrel_prel items xs' l'
#pop-options

let rec lall_filter_split (s: FStar.Set.set asn1_id_t) (#d: _) (dk: asn1_decorated_k s d) (#ids': _) (tl: asn1_gen_items_l ids') (l: list asn1_value)
: Lemma
  (ensures (lall (elem_ok (ASN1_GEN_ITEMS_CONS s d dk ids' tl)) l == (lall (itemconf dk) (L.filter (in_s s) l) && lall (elem_ok tl) (L.filter (out_s s) l))))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> lall_filter_split s dk tl q

let not_plain_gen (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (Some? (generate_defaultable_item (asn1_decorated_as_parser_twin dk)) == not_plain d)
= ()

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let rec comps_setm (#ids: _) (items: asn1_gen_items_l ids) (xs: list (set_elem_t (asn1_sequence_as_parser items))) (l: list asn1_value)
: Lemma
  (requires (rrel (erel items) xs l))
  (ensures (comps_ok (asn1_sequence_as_parser items) xs == (setm items l && lall (elem_ok items) l) \/ (lall (elem_ok items) l == false /\ setm items l == false)))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL ->
    begin match xs with
    | [] -> ()
    | x :: _ -> let x' : False = x in ()
    end
  | ASN1_GEN_ITEMS_CONS s d dk ids' tl ->
    let hd = asn1_decorated_as_parser_twin dk in
    let xs' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t (asn1_sequence_as_parser tl))) = xs in
    rrel_prel items xs l;
    ht_gen s (erel tl) xs' l;
    lall_filter_split s dk tl l;
    not_plain_gen dk;
    comps_setm tl (tails xs') (L.filter (out_s s) l);
    assert (comps_ok (asn1_sequence_as_parser items) xs == (comp_ok hd (heads xs') && comps_ok (asn1_sequence_as_parser tl) (tails xs')))
#pop-options

let rec setm_lall (#ids: _) (items: asn1_gen_items_l ids) (l: list asn1_value)
: Lemma
  (requires (setm items l == true))
  (ensures (lall (elem_ok items) l == true))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    lall_filter_split s dk tl l;
    setm_lall tl (L.filter (out_s s) l)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec set_twin_idx (#ids: _) (items: asn1_gen_items_l ids) (v: asn1_value) (sfx: bytes)
: Lemma
  (requires (items_good items))
  (ensures (
    let its = asn1_sequence_as_parser items in
    match parse (parse_set_elem_twin its (asn1_value_id v)) (vtl v `Seq.append` sfx) with
    | Some (e, n) -> elem_ok items v == true /\ n == Seq.length (vtl v) /\ elem_idx its e == comp_idx items (asn1_value_id v)
    | None -> elem_ok items v == false))
  (decreases items)
= let id = asn1_value_id v in
  let b = vtl v `Seq.append` sfx in
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    let hd = asn1_decorated_as_parser_twin dk in
    let its = asn1_sequence_as_parser items in
    assert (its == hd :: asn1_sequence_as_parser tl);
    if FStar.Set.mem id s
    then begin
      item_at dk v sfx;
      parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t (asn1_sequence_as_parser tl))) b
    end
    else begin
      set_twin_idx tl v sfx;
      parse_synth_eq (parse_set_elem_twin (asn1_sequence_as_parser tl) id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b
    end
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_elem_at (#ids: _) (items: asn1_gen_items_l ids) (v: asn1_value) (sfx: bytes)
: Lemma
  (requires (items_good items))
  (ensures (
    let its = asn1_sequence_as_parser items in
    match parse (parse_set_elem its) (asn1_value_enc v `Seq.append` sfx) with
    | Some (e, n) -> elem_ok items v == true /\ n == Seq.length (asn1_value_enc v) /\ erel items e v == true
    | None -> elem_ok items v == false))
= let its = asn1_sequence_as_parser items in
  let id = asn1_value_id v in
  let b = asn1_value_enc v `Seq.append` sfx in
  let n = Seq.length (asn1_id_enc id) in
  let r = vtl v `Seq.append` sfx in
  id_split v sfx;
  parse_set_elem_twin_cases_injective its;
  and_then_eq parse_asn1_identifier_U32 (parse_set_elem_twin its) b;
  set_twin_idx items v sfx;
  items_tagged_intro items;
  set_elem_twin_tag its id r;
  assert (parse (parse_set_elem its) b == parse (parse_asn1_identifier_U32 `and_then` parse_set_elem_twin its) b)
#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"
let rec set_list (#ids: _) (items: asn1_gen_items_l ids) (l: list asn1_value)
: Lemma
  (requires (items_good items))
  (ensures (
    let its = asn1_sequence_as_parser items in
    match parse (parse_list (parse_set_elem its)) (asn1_value_list_enc l) with
    | Some (xs, c) -> lall (elem_ok items) l == true /\ c == Seq.length (asn1_value_list_enc l) /\ rrel (erel items) xs l == true
    | None -> lall (elem_ok items) l == false))
  (decreases l)
= let its = asn1_sequence_as_parser items in
  let p = parse_set_elem its in
  let b = asn1_value_list_enc l in
  assert (parse (parse_list p) b == parse (tot_parse_list p) b);
  tot_parse_list_eq p b;
  match l with
  | [] -> ()
  | w :: q ->
    let bq = asn1_value_list_enc q in
    set_elem_at items w bq;
    asn1_value_enc_nonempty w;
    app_slice (asn1_value_enc w) bq;
    set_list items q;
    assert (parse (parse_list p) bq == parse (tot_parse_list p) bq);
    match parse p b, parse (tot_parse_list p) bq with
    | Some (x, n), Some (xs, n') ->
      assert (parse (tot_parse_list p) b == Some (x :: xs, n + n'))
    | _ -> ()
#pop-options

let rec tags_sorted_rrel (#ids: _) (items: asn1_gen_items_l ids) (xs: list (set_elem_t (asn1_sequence_as_parser items))) (l: list asn1_value)
: Lemma
  (requires (rrel (erel items) xs l == true))
  (ensures (tags_sorted (elem_tag (asn1_sequence_as_parser items)) xs == value_ids_sorted l))
  (decreases l)
= match xs, l with
  | _ :: y :: q, _ :: v :: r -> tags_sorted_rrel items (y :: q) (v :: r)
  | _ -> ()

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_good (#ids: _) (items: asn1_gen_items_l ids) (l: list asn1_value)
: Lemma
  (requires (items_good items))
  (ensures (exact (make_asn1_set_parser (asn1_sequence_as_parser items)) (asn1_value_list_enc l) == (value_ids_sorted l && setm items l)))
= let its = asn1_sequence_as_parser items in
  let b = asn1_value_list_enc l in
  set_to_tuple_injective its;
  let pl = parse_list (parse_set_elem its) in
  let pf = pl `parse_filter` set_ok its in
  parse_synth_eq pf (set_to_tuple its) b;
  parse_filter_eq pl (set_ok its) b;
  set_list items l;
  Classical.move_requires (setm_lall items) l;
  match parse pl b with
  | Some (xs, _) ->
    tags_sorted_rrel items xs l;
    comps_setm items xs l
  | None -> ()
#pop-options

(* ANY DEFINED BY: content *)

let pfx_all (#ids: _) (prefix: asn1_gen_items_l ids) (sf: list asn1_value -> bool) (t: Type)
: Lemma
  (requires (items_good prefix))
  (ensures (forall (sfx: parser_twin asn1_weak_parser_kind t) . {:pattern (make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) sfx)}
    sfx_good sfx sf ==> (forall (l: list asn1_value) . exact (make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) sfx) (asn1_value_list_enc l) == pfx_res prefix sf l)))
= let prf (sfx: parser_twin asn1_weak_parser_kind t) (l: list asn1_value)
  : Lemma (sfx_good sfx sf ==> exact (make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) sfx) (asn1_value_list_enc l) == pfx_res prefix sf l)
  = Classical.move_requires (any_none prefix sfx sf) l
  in
  Classical.forall_intro_2 prf

let any_conf (k: asn1_content_k { ASN1_ANY_DEFINED_BY? k }) (pm: asn1_terminal_t (ASN1_ANY_DEFINED_BY?.key_k k) -> list asn1_value -> bool) : prop =
  match k with
  | ASN1_ANY_DEFINED_BY _ prefix kid key_k _ _ _ _ ->
    forall (l: list asn1_value) . exact (asn1_content_as_parser k) (asn1_value_list_enc l) == pfx_res prefix (sfm kid key_k pm) l

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let sfx_none_p (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (l: list asn1_value)
: Lemma
  (requires (ls_good ls))
  (ensures (
    let tp = asn1_terminal_as_parser key_k in
    let key_p = parse_asn1_ILC kid #(ASN1_TERMINAL key_k) tp in
    let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    exact (weaken asn1_weak_parser_kind (make_gen_choice_weak_parser key_p supported_p)) (asn1_value_list_enc l) == sfm kid key_k (lsm key_k ls) l))
= let tp = asn1_terminal_as_parser key_k in
  let key_p = parse_asn1_ILC kid #(ASN1_TERMINAL key_k) tp in
  let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  let pay = make_gen_choice_weak_payload_parser supported_p in
  Classical.forall_intro_2 (pay_at key_k ls);
  assert (pay_good pay (lsm key_k ls));
  tu_top kid key_k (project_tags supported_p) pay (lsm key_k ls) l;
  assert (make_gen_choice_weak_parser key_p supported_p == parse_tagged_union key_p (project_tags supported_p) (make_gen_choice_weak_payload_parser supported_p)) by (FStar.Tactics.norm [delta_only [`%make_gen_choice_weak_parser; `%project_tags; `%asn1_content_t]; zeta; iota]; FStar.Tactics.trefl ())

let sfx_none_fp (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (v: asn1_value) (l: list asn1_value)
: Lemma
  (requires (ls_good ls))
  (ensures (
    let tp = asn1_terminal_as_parser key_k in
    parser_asn1_ILC_twin_case_injective kid #(ASN1_TERMINAL key_k) tp;
    let key_fp = parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) tp in
    let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    exact (weaken asn1_weak_parser_kind (make_gen_choice_weak_parser_twin key_fp supported_p (asn1_value_id v))) (vtl v `Seq.append` asn1_value_list_enc l) == sfm kid key_k (lsm key_k ls) (v :: l)))
= let tp = asn1_terminal_as_parser key_k in
  parser_asn1_ILC_twin_case_injective kid #(ASN1_TERMINAL key_k) tp;
  let key_fp = parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) tp in
  let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  let pay = make_gen_choice_weak_payload_parser supported_p in
  Classical.forall_intro_2 (pay_at key_k ls);
  assert (pay_good pay (lsm key_k ls));
  tu_twin kid key_k (project_tags supported_p) pay (lsm key_k ls) v l;
  assert (make_gen_choice_weak_parser_twin key_fp supported_p (asn1_value_id v) == parse_tagged_union (key_fp (asn1_value_id v)) (project_tags supported_p) (make_gen_choice_weak_payload_parser supported_p)) by (FStar.Tactics.norm [delta_only [`%make_gen_choice_weak_parser; `%make_gen_choice_weak_parser_twin; `%make_gen_choice_with_fallback_weak_parser; `%make_gen_choice_with_fallback_weak_parser_twin; `%project_tags; `%project_tags_with_fallback; `%asn1_content_t]; zeta; iota]; FStar.Tactics.trefl ())

let sfx_fb_p (k0: asn1_content_k) (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (l: list asn1_value)
: Lemma
  (requires (ls_good ls /\ items_good fbitems))
  (ensures (
    let tp = asn1_terminal_as_parser key_k in
    let key_p = parse_asn1_ILC kid #(ASN1_TERMINAL key_k) tp in
    let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    let fallback_p = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser fbitems)) in
    exact (weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser key_p supported_p fallback_p)) (asn1_value_list_enc l) == sfm kid key_k (lsm_fb k0 key_k ls fbitems) l))
= let tp = asn1_terminal_as_parser key_k in
  let key_p = parse_asn1_ILC kid #(ASN1_TERMINAL key_k) tp in
  let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  let fallback_p = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser fbitems)) in
  let pay = make_gen_choice_with_fallback_weak_payload_parser supported_p fallback_p in
  Classical.forall_intro_2 (pay_fb_at k0 key_k ls fbitems);
  assert (pay_good pay (lsm_fb k0 key_k ls fbitems));
  tu_top kid key_k (project_tags_with_fallback supported_p fallback_p) pay (lsm_fb k0 key_k ls fbitems) l;
  assert (make_gen_choice_with_fallback_weak_parser key_p supported_p fallback_p == parse_tagged_union key_p (project_tags_with_fallback supported_p fallback_p) (make_gen_choice_with_fallback_weak_payload_parser supported_p fallback_p)) by (FStar.Tactics.norm [delta_only [`%make_gen_choice_weak_parser; `%make_gen_choice_weak_parser_twin; `%make_gen_choice_with_fallback_weak_parser; `%make_gen_choice_with_fallback_weak_parser_twin; `%project_tags; `%project_tags_with_fallback; `%asn1_content_t]; zeta; iota]; FStar.Tactics.trefl ())

let sfx_fb_fp (k0: asn1_content_k) (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (v: asn1_value) (l: list asn1_value)
: Lemma
  (requires (ls_good ls /\ items_good fbitems))
  (ensures (
    let tp = asn1_terminal_as_parser key_k in
    parser_asn1_ILC_twin_case_injective kid #(ASN1_TERMINAL key_k) tp;
    let key_fp = parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) tp in
    let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    let fallback_p = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser fbitems)) in
    exact (weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser_twin key_fp supported_p fallback_p (asn1_value_id v))) (vtl v `Seq.append` asn1_value_list_enc l) == sfm kid key_k (lsm_fb k0 key_k ls fbitems) (v :: l)))
= let tp = asn1_terminal_as_parser key_k in
  parser_asn1_ILC_twin_case_injective kid #(ASN1_TERMINAL key_k) tp;
  let key_fp = parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) tp in
  let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  let fallback_p = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser fbitems)) in
  let pay = make_gen_choice_with_fallback_weak_payload_parser supported_p fallback_p in
  Classical.forall_intro_2 (pay_fb_at k0 key_k ls fbitems);
  assert (pay_good pay (lsm_fb k0 key_k ls fbitems));
  tu_twin kid key_k (project_tags_with_fallback supported_p fallback_p) pay (lsm_fb k0 key_k ls fbitems) v l;
  assert (make_gen_choice_with_fallback_weak_parser_twin key_fp supported_p fallback_p (asn1_value_id v) == parse_tagged_union (key_fp (asn1_value_id v)) (project_tags_with_fallback supported_p fallback_p) (make_gen_choice_with_fallback_weak_payload_parser supported_p fallback_p)) by (FStar.Tactics.norm [delta_only [`%make_gen_choice_weak_parser; `%make_gen_choice_weak_parser_twin; `%make_gen_choice_with_fallback_weak_parser; `%make_gen_choice_with_fallback_weak_parser_twin; `%project_tags; `%project_tags_with_fallback; `%asn1_content_t]; zeta; iota]; FStar.Tactics.trefl ())
#pop-options

#push-options "--z3rlimit 128 --fuel 1 --ifuel 1"
let any_content_good
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (ofb: option asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) idp))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma
  (requires (items_good prefix /\ ls_good ls /\ (match ofb with None -> True | Some gitems -> items_good (dsnd gitems))))
  (ensures (
    let k = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' in
    match ofb with
    | None -> any_conf k (lsm key_k ls)
    | Some gitems -> fb_precedes' k; any_conf k (lsm_fb k key_k ls (dsnd gitems))))
= let k = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' in
  let tp = asn1_terminal_as_parser key_k in
  let key_p = parse_asn1_ILC kid #(ASN1_TERMINAL key_k) tp in
  parser_asn1_ILC_twin_case_injective kid #(ASN1_TERMINAL key_k) tp;
  let key_fp = parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) tp in
  let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  match ofb with
  | None ->
    let pm = lsm key_k ls in
    let sf = sfm kid key_k pm in
    Classical.forall_intro (sfx_none_p kid key_k ls);
    Classical.forall_intro_2 (sfx_none_fp kid key_k ls);
    make_gen_choice_weak_parser_twin_and_then_cases_injective key_fp supported_p;
    assert (forall (l: list asn1_value) . exact (weaken asn1_weak_parser_kind (make_gen_choice_weak_parser key_p supported_p)) (asn1_value_list_enc l) == sf l);
    assert (forall (v: asn1_value) (l: list asn1_value) . exact (weaken asn1_weak_parser_kind (make_gen_choice_weak_parser_twin key_fp supported_p (asn1_value_id v))) (vtl v `Seq.append` asn1_value_list_enc l) == sf (v :: l));
    pfx_all prefix sf (make_gen_choice_type (extract_types supported_p));
    assert (any_conf k pm) by (FStar.Tactics.norm [delta_only [`%asn1_content_as_parser; `%any_conf]; zeta; iota])
  | Some gitems ->
    fb_precedes' k;
    let fbitems = dsnd gitems in
    let fallback_p = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser fbitems)) in
    let pm = lsm_fb k key_k ls fbitems in
    let sf = sfm kid key_k pm in
    Classical.forall_intro (sfx_fb_p k kid key_k ls fbitems);
    Classical.forall_intro_2 (sfx_fb_fp k kid key_k ls fbitems);
    make_gen_choice_with_fallback_weak_parser_twin_and_then_cases_injective key_fp supported_p fallback_p;
    assert (forall (l: list asn1_value) . exact (weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser key_p supported_p fallback_p)) (asn1_value_list_enc l) == sf l);
    assert (forall (v: asn1_value) (l: list asn1_value) . exact (weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser_twin key_fp supported_p fallback_p (asn1_value_id v))) (vtl v `Seq.append` asn1_value_list_enc l) == sf (v :: l));
    pfx_all prefix sf (make_gen_choice_type_with_fallback (extract_types supported_p) (Mkgenparser?.t fallback_p));
    assert (any_conf k pm) by (FStar.Tactics.norm [delta_only [`%asn1_content_as_parser; `%any_conf]; zeta; iota])
#pop-options

(* Main induction *)

let restricted_good (k': asn1_terminal_k) (r: _) (v: asn1_value)
: Lemma (exact (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k' r)) (vcont v) == cconf (ASN1_RESTRICTED_TERMINAL k' r) v)
= let tp = asn1_terminal_as_parser k' in
  parse_filter_eq tp (restriction_pred r) (vcont v);
  tparse_exact tp (vcont v)

let terminal_good (k': asn1_terminal_k) (v: asn1_value)
: Lemma (exact (asn1_content_as_parser (ASN1_TERMINAL k')) (vcont v) == cconf (ASN1_TERMINAL k') v)
= tparse_exact (asn1_terminal_as_parser k') (vcont v)

let cons_of_flag (id: asn1_id_t) (v: asn1_value)
: Lemma
  (requires (CONSTRUCTED? id.f /\ asn1_value_id v == id /\ hdr_ok v == true))
  (ensures (ASN1_VALUE_CONSTRUCTED? v))
= ()

let any_cconf (k: asn1_content_k { ASN1_ANY_DEFINED_BY? k }) (pm: asn1_terminal_t (ASN1_ANY_DEFINED_BY?.key_k k) -> list asn1_value -> bool) (id: asn1_any_id_t) (l: list asn1_value)
: Lemma
  (requires (
    match k with
    | ASN1_ANY_DEFINED_BY _ _ _ key_k ls ofb _ _ ->
      (match ofb with
       | None -> pm == lsm key_k ls
       | Some fb -> fb_precedes' k; pm == lsm_fb k key_k ls (dsnd fb))))
  (ensures (
    match k with
    | ASN1_ANY_DEFINED_BY _ prefix kid key_k _ _ _ _ ->
      pfx_res prefix (sfm kid key_k pm) l == cconf k (ASN1_VALUE_CONSTRUCTED id l)))
= ()

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec content_good (id: asn1_id_t) (k: asn1_content_k)
: Lemma
  (requires (wf_content id k))
  (ensures (cgood id k))
  (decreases k)
= match k with
  | ASN1_RESTRICTED_TERMINAL k' r -> Classical.forall_intro (restricted_good k' r)
  | ASN1_TERMINAL k' -> Classical.forall_intro (terminal_good k')
  | ASN1_SEQUENCE gitems ->
    items_good_intro (dsnd gitems);
    let prf (v: asn1_value) : Lemma ((asn1_value_id v == id /\ hdr_ok v == true) ==> exact (asn1_content_as_parser k) (vcont v) == cconf k v)
    = match v with
      | ASN1_VALUE_CONSTRUCTED _ l -> seq_none (dsnd gitems) l
      | _ -> ()
    in
    Classical.forall_intro prf
  | ASN1_SET _ items _ ->
    items_good_intro items;
    let prf (v: asn1_value) : Lemma ((asn1_value_id v == id /\ hdr_ok v == true) ==> exact (asn1_content_as_parser k) (vcont v) == cconf k v)
    = match v with
      | ASN1_VALUE_CONSTRUCTED _ l -> set_good items l
      | _ -> ()
    in
    Classical.forall_intro prf
  | ASN1_SEQUENCE_OF ne k' ->
    top_kpre k';
    k_pgood k';
    let prf (v: asn1_value) : Lemma ((asn1_value_id v == id /\ hdr_ok v == true) ==> exact (asn1_content_as_parser k) (vcont v) == cconf k v)
    = match v with
      | ASN1_VALUE_CONSTRUCTED _ l ->
        seq_of_good ne (asn1_as_parser k') (vconf k') l;
        vconf_list_lall k' l
      | _ -> ()
    in
    Classical.forall_intro prf
  | ASN1_SET_OF ne k' ->
    top_kpre k';
    k_pgood k';
    let prf (v: asn1_value) : Lemma ((asn1_value_id v == id /\ hdr_ok v == true) ==> exact (asn1_content_as_parser k) (vcont v) == cconf k v)
    = match v with
      | ASN1_VALUE_CONSTRUCTED _ l ->
        set_of_good ne (asn1_as_parser k') (vconf k') l;
        vconf_list_lall k' l
      | _ -> ()
    in
    Classical.forall_intro prf
  | ASN1_PREFIXED k' ->
    top_kpre k';
    top_lemma k';
    Classical.forall_intro (prefixed_good k')
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    items_good_intro prefix;
    ls_good_intro ls;
    (match ofb with None -> () | Some gitems -> items_good_intro (dsnd gitems));
    any_content_good idp prefix kid key_k ls ofb pf pf';
    let prf (v: asn1_value) : Lemma ((asn1_value_id v == id /\ hdr_ok v == true) ==> exact (asn1_content_as_parser k) (vcont v) == cconf k v)
    = match v with
      | ASN1_VALUE_CONSTRUCTED vid l ->
        (match ofb with
         | None -> any_cconf k (lsm key_k ls) vid l
         | Some fb -> fb_precedes' k; any_cconf k (lsm_fb k key_k ls (dsnd fb)) vid l)
      | _ -> ()
    in
    Classical.forall_intro prf

and lc_good_intro (lc: list (asn1_id_t & asn1_content_k))
: Lemma
  (requires (wf_lc lc))
  (ensures (lc_good lc))
  (decreases lc)
= match lc with
  | [] -> ()
  | h :: tl -> let (x, y) = h in content_good x y; lc_good_intro tl

and top_kpre (#s: _) (k: asn1_k s)
: Lemma
  (requires (wf k))
  (ensures (kpre k))
  (decreases k)
= match k with
  | ASN1_ILC id k' -> content_good id k'
  | ASN1_CHOICE_ILC lc _ -> lc_good_intro lc
  | ASN1_ANY_ILC -> ()

and dec_intro (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma
  (requires (wf_dec dk))
  (ensures (item_good dk))
  (decreases dk)
= match dk with
  | ASN1_PLAIN_ILC k -> top_kpre k; dec_good dk
  | ASN1_OPTION_ILC k -> top_kpre k; dec_good dk
  | _ -> dec_good dk

and items_good_intro (#ids: _) (ls: asn1_gen_items_l ids)
: Lemma
  (requires (wf_items ls))
  (ensures (items_good ls))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> dec_intro dk; items_good_intro tl

and ls_good_intro (#t: eqtype) (ls: list (t & asn1_gen_items_lk))
: Lemma
  (requires (wf_ls ls))
  (ensures (ls_good ls))
  (decreases ls)
= match ls with
  | [] -> ()
  | h :: tl -> let (_, it) = h in items_good_intro (dsnd it); ls_good_intro tl
#pop-options

(* Main theorem *)

let vconf_correct (#s: _) (k: asn1_k s) (v: asn1_value)
: Lemma
  (requires (wf k))
  (ensures (vconf k v == conforms k v))
= top_kpre k;
  k_top k v Seq.empty;
  Seq.append_empty_r (asn1_value_enc v)

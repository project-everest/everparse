module ASN1.Spec.ToValue.Sound

(* Soundness of `to_value` w.r.t. the typed parsers: building blocks.
   For every well-formed schema `k`, the bytes consumed by the typed parser
   `asn1_as_parser k` are exactly the generic encoding of the generic value
   of the parsed typed value: see `top_lemma` in ASN1.Spec.ToValue.Main and
   `asn1_as_parser_consumed` in ASN1.Spec.Serializer. *)

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

module U32 = FStar.UInt32
module Seq = FStar.Seq
module List = FStar.List.Tot

(* Parsers whose consumed bytes are the encoding of their result *)

let esound (#k: parser_kind) (#t: Type) (p: parser k t) (g: t -> GTot bytes) : prop =
  forall b. match parse p b with
  | Some (x, n) -> Seq.slice b 0 n == g x
  | None -> True

(* After an identifier has been read *)
let esound_twin (#k: parser_kind) (#t: Type) (fp: asn1_id_t -> parser k t) (g: t -> GTot bytes) : prop =
  forall id b. match parse (fp id) b with
  | Some (x, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == g x
  | None -> True

(* Generic values *)

let value_ok (v: asn1_value) : Tot bool =
  match v with
  | ASN1_VALUE_PRIMITIVE id _ -> PRIMITIVE? id.f
  | ASN1_VALUE_CONSTRUCTED id _ -> CONSTRUCTED? id.f

let value_contents (v: asn1_value) : Tot bytes =
  match v with
  | ASN1_VALUE_PRIMITIVE _ c -> c
  | ASN1_VALUE_CONSTRUCTED _ l -> asn1_value_list_enc l

let value_enc_eq (v: asn1_value)
: Lemma (asn1_value_enc v == enc_tlv (value_id v) (value_ok v) (value_contents v))
= ()

let list_enc_append (l1 l2: list asn1_value)
: Lemma
  (ensures (asn1_value_list_enc (l1 `List.append` l2) == asn1_value_list_enc l1 `Seq.append` asn1_value_list_enc l2))
  (decreases l1)
= let rec aux (l1: list asn1_value) : Lemma
    (ensures (asn1_value_list_enc (l1 `List.append` l2) == asn1_value_list_enc l1 `Seq.append` asn1_value_list_enc l2))
    (decreases l1)
  = match l1 with
    | [] -> Seq.lemma_eq_elim (asn1_value_list_enc l2) (Seq.empty `Seq.append` asn1_value_list_enc l2)
    | v :: q ->
      aux q;
      Seq.append_assoc (asn1_value_enc v) (asn1_value_list_enc q) (asn1_value_list_enc l2)
  in
  aux l1

let list_enc_single (v: asn1_value)
: Lemma (asn1_value_list_enc [v] == asn1_value_enc v)
= Seq.append_empty_r (asn1_value_enc v)

(* Shapes of the values of well-formed schemas *)

let mk_prim_shape (id: asn1_id_t) (c: bytes)
: Lemma
  (requires (asn1_any_id_valid id /\ PRIMITIVE? id.f))
  (ensures (value_id (mk_prim id c) == id /\ value_ok (mk_prim id c) == true /\ value_contents (mk_prim id c) == c))
= ()

let mk_cons_shape (id: asn1_id_t) (l: list asn1_value)
: Lemma
  (requires (asn1_any_id_valid id /\ CONSTRUCTED? id.f))
  (ensures (value_id (mk_cons id l) == id /\ value_ok (mk_cons id l) == true /\ value_contents (mk_cons id l) == asn1_value_list_enc l))
= ()

let mk_encap_shape (id: asn1_id_t) (w: asn1_value)
: Lemma
  (requires (asn1_any_id_valid id))
  (ensures (value_id (mk_encap id w) == id /\ value_ok (mk_encap id w) == true /\ value_contents (mk_encap id w) == asn1_value_enc w))
= list_enc_single w

let rec terminal_shape (id: asn1_id_t) (k: asn1_terminal_k) (x: asn1_terminal_t k)
: Lemma
  (requires (wf_terminal id k))
  (ensures (value_id (terminal_to_value id k x) == id /\ value_ok (terminal_to_value id k x) == true))
  (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    let x' : asn1_terminal_t k2 = FStar.Pervasives.coerce_eq #(asn1_terminal_t k) #(asn1_terminal_t k2) () x in
    mk_encap_shape id (terminal_to_value id2 k2 x')
  | _ -> ()

let content_shape (id: asn1_id_t) (k: asn1_content_k) (x: asn1_content_t k)
: Lemma
  (requires (wf_content id k))
  (ensures (value_id (content_to_value id k x) == id /\ value_ok (content_to_value id k x) == true))
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> terminal_shape id k' x
  | ASN1_TERMINAL k' -> terminal_shape id k' x
  | ASN1_PREFIXED k' -> mk_encap_shape id (to_value k' x)
  | _ -> ()

(* Identifier, then length-prefixed contents *)

#push-options "--z3rlimit 64"
let lc_at
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (g: asn1_content_t ack -> GTot bytes)
  (b: bytes)
: Lemma
  (requires (esound p g))
  (ensures (match parse (parse_asn1_LC p) b with
    | Some (x, n) -> Seq.slice b 0 n == enc_hdr true (Seq.length (g x)) `Seq.append` g x
    | None -> True))
= vlgen_eq p b;
  parse_len_consumed b;
  match parse parse_asn1_length_u32_t b with
  | None -> ()
  | Some (len, sz) ->
    if Seq.length b < sz + U32.v len
    then ()
    else begin
      let ct = Seq.slice b sz (sz + U32.v len) in
      match parse p ct with
      | Some (x, m) ->
        if m = U32.v len
        then begin
          assert (Seq.slice ct 0 m == g x);
          Seq.lemma_eq_elim ct (Seq.slice ct 0 m);
          Seq.lemma_eq_elim (Seq.slice b 0 (sz + U32.v len)) (Seq.slice b 0 sz `Seq.append` ct)
        end
      | None -> ()
    end
#pop-options

let lc_twin_esound
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (g: asn1_content_t ack -> GTot bytes)
: Lemma
  (requires (esound p g))
  (ensures (esound_twin (parse_asn1_ILC_twin id p) (fun x -> enc_tlv id true (g x))))
= let prf (id': asn1_id_t) (b: bytes) : Lemma (match parse (parse_asn1_ILC_twin id p id') b with
    | Some (x, n) -> asn1_id_enc id' `Seq.append` Seq.slice b 0 n == enc_tlv id true (g x)
    | None -> True)
  = if id = id' then lc_at p g b
  in
  Classical.forall_intro_2 prf

let slice_split (b: bytes) (c1 n2: nat)
: Lemma
  (requires (c1 + n2 <= Seq.length b))
  (ensures (Seq.slice b 0 (c1 + n2) == Seq.slice b 0 c1 `Seq.append` Seq.slice (Seq.slice b c1 (Seq.length b)) 0 n2))
= Seq.lemma_eq_elim (Seq.slice b 0 (c1 + n2)) (Seq.slice b 0 c1 `Seq.append` Seq.slice (Seq.slice b c1 (Seq.length b)) 0 n2)

#push-options "--z3rlimit 64"
let ilc_at
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (g: asn1_content_t ack -> GTot bytes)
  (b: bytes)
: Lemma
  (requires (esound p g))
  (ensures (match parse (parse_asn1_ILC id p) b with
    | Some (x, n) -> Seq.slice b 0 n == enc_tlv id true (g x)
    | None -> True))
= let pf = parse_asn1_identifier_U32 `parse_filter` (fun id' -> id' = id) in
  parse_synth_eq (pf `nondep_then` parse_asn1_LC p) snd b;
  nondep_then_eq pf (parse_asn1_LC p) b;
  parse_filter_eq parse_asn1_identifier_U32 (fun id' -> id' = id) b;
  parse_asn1_identifier_U32_consumed b;
  match parse parse_asn1_identifier_U32 b with
  | Some (id', c1) ->
    if id' = id
    then begin
      let b1 = Seq.slice b c1 (Seq.length b) in
      lc_at p g b1;
      match parse (parse_asn1_LC p) b1 with
      | Some (_, n2) ->
        slice_split b c1 n2
      | None -> ()
    end
  | None -> ()
#pop-options

let ilc_esound
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (g: asn1_content_t ack -> GTot bytes)
: Lemma
  (requires (esound p g))
  (ensures (esound (parse_asn1_ILC id p) (fun x -> enc_tlv id true (g x))))
= Classical.forall_intro (Classical.move_requires (ilc_at id p g))

(* Terminals *)

let tbytes (id: asn1_id_t) (k: asn1_terminal_k) (x: asn1_terminal_t k) : GTot bytes =
  value_contents (terminal_to_value id k x)

let terminal_value_enc (id: asn1_id_t) (k: asn1_terminal_k) (x: asn1_terminal_t k)
: Lemma
  (requires (wf_terminal id k))
  (ensures (asn1_value_enc (terminal_to_value id k x) == enc_tlv id true (tbytes id k x)))
= terminal_shape id k x

private
let leaf_tbytes (id: asn1_id_t) (k: leaf_k) (x: asn1_terminal_t k)
: Lemma (tbytes id k x == leaf_enc k x)
= ()

private
let leaf_esound_at (id: asn1_id_t) (k: leaf_k) (b: bytes)
: Lemma (match parse (asn1_terminal_as_parser k) b with
    | Some (x, n) -> Seq.slice b 0 n == tbytes id k x
    | None -> True)
= leaf_enc_consumed k b;
  match parse (asn1_terminal_as_parser k) b with
  | Some (x, _) -> leaf_tbytes id k x
  | None -> ()

private
let prefixed_tbytes (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (x: asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2))
: Lemma
  (requires (wf_terminal id (ASN1_PREFIXED_TERMINAL id2 k2)))
  (ensures (tbytes id (ASN1_PREFIXED_TERMINAL id2 k2) x == enc_tlv id2 true (tbytes id2 k2 (FStar.Pervasives.coerce_eq #(asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2)) #(asn1_terminal_t k2) () x))))
= let x' : asn1_terminal_t k2 = FStar.Pervasives.coerce_eq #(asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2)) #(asn1_terminal_t k2) () x in
  mk_encap_shape id (terminal_to_value id2 k2 x');
  terminal_value_enc id2 k2 x'

#push-options "--fuel 1 --ifuel 0"
private
let prefixed_parse_eq (id2: asn1_id_t) (k2: asn1_terminal_k) (b: bytes)
: Lemma (match parse (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) b with
    | Some (x, n) -> (match parse (parse_asn1_ILC id2 #(ASN1_TERMINAL k2) (asn1_terminal_as_parser k2)) b with
      | Some (x', n') -> n == n' /\ (FStar.Pervasives.coerce_eq #(asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2)) #(asn1_terminal_t k2) () x) == x'
      | None -> False)
    | None -> True)
= ()
#pop-options

private
let prefixed_esound_some (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (b: bytes) (x: asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2)) (x': asn1_terminal_t k2) (n: nat)
: Lemma
  (requires (wf_terminal id (ASN1_PREFIXED_TERMINAL id2 k2) /\ n <= Seq.length b /\
    (FStar.Pervasives.coerce_eq #(asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2)) #(asn1_terminal_t k2) () x) == x' /\ Seq.slice b 0 n == enc_tlv id2 true (tbytes id2 k2 x')))
  (ensures (Seq.slice b 0 n == tbytes id (ASN1_PREFIXED_TERMINAL id2 k2) x))
= prefixed_tbytes id id2 k2 x

private
let prefixed_esound_at (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (b: bytes)
: Lemma
  (requires (wf_terminal id (ASN1_PREFIXED_TERMINAL id2 k2) /\ esound (asn1_terminal_as_parser k2) (tbytes id2 k2)))
  (ensures (match parse (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) b with
    | Some (x, n) -> Seq.slice b 0 n == tbytes id (ASN1_PREFIXED_TERMINAL id2 k2) x
    | None -> True))
= ilc_at id2 #(ASN1_TERMINAL k2) (asn1_terminal_as_parser k2) (tbytes id2 k2) b;
  prefixed_parse_eq id2 k2 b;
  match parse (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) b with
  | Some (x, n) ->
    begin match parse (parse_asn1_ILC id2 #(ASN1_TERMINAL k2) (asn1_terminal_as_parser k2)) b with
    | Some (x', _) -> prefixed_esound_some id id2 k2 b x x' n
    | None -> ()
    end
  | None -> ()

let rec terminal_esound (id: asn1_id_t) (k: asn1_terminal_k)
: Lemma
  (requires (wf_terminal id k))
  (ensures (esound (asn1_terminal_as_parser k) (tbytes id k)))
  (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    terminal_esound id2 k2;
    Classical.forall_intro (Classical.move_requires (prefixed_esound_at id id2 k2))
  | _ -> Classical.forall_intro (leaf_esound_at id k)

(* SEQUENCE OF, SET OF *)

let rec list_values (#t: Type) (f: t -> GTot asn1_value) (l: list t) : GTot (list asn1_value) =
  match l with
  | [] -> []
  | a :: q -> f a :: list_values f q

let rec list_esound_at (#t: Type) (p: asn1_strong_parser t) (f: t -> GTot asn1_value) (b: bytes)
: Lemma
  (requires (esound p (fun x -> asn1_value_enc (f x))))
  (ensures (match parse (parse_list p) b with
    | Some (l, n) -> Seq.slice b 0 n == asn1_value_list_enc (list_values f l)
    | None -> True))
  (decreases (Seq.length b))
= (if Seq.length b > 0
   then match parse p b with
   | Some (_, c) ->
     if c > 0 then list_esound_at p f (Seq.slice b c (Seq.length b))
   | None -> ());
  tot_parse_list_eq p b;
  if Seq.length b = 0
  then Seq.lemma_eq_elim (Seq.slice b 0 0) Seq.empty
  else match parse p b with
  | Some (_, c) ->
    if c > 0 then
    begin match parse (parse_list p) (Seq.slice b c (Seq.length b)) with
    | Some (_, n2) ->
      slice_split b c n2
    | None -> ()
    end
  | None -> ()

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let rec sorted_list_aux_esound
  (ord: (bytes -> bytes -> bool))
  (#t: Type) (p: asn1_strong_parser t) (f: t -> GTot asn1_value)
  (prev: bytes) (b: bytes)
: Lemma
  (requires (esound p (fun x -> asn1_value_enc (f x))))
  (ensures (match tot_parse_byte_sorted_list_aux ord p prev b with
    | Some (l, n) -> Seq.slice b 0 n == asn1_value_list_enc (list_values f l)
    | None -> True))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then Seq.lemma_eq_elim (Seq.slice b 0 0) Seq.empty
  else match parse p b with
  | None -> ()
  | Some (_, c) ->
    if c = 0 then ()
    else begin
      let b' = Seq.slice b c (Seq.length b) in
      sorted_list_aux_esound ord p f (Seq.slice b 0 c) b';
      match tot_parse_byte_sorted_list_aux ord p (Seq.slice b 0 c) b' with
      | Some (_, n2) ->
        slice_split b c n2
      | None -> ()
    end

let sorted_list_esound
  (ord: (bytes -> bytes -> bool))
  (#t: Type) (p: asn1_strong_parser t) (f: t -> GTot asn1_value)
  (b: bytes)
: Lemma
  (requires (esound p (fun x -> asn1_value_enc (f x))))
  (ensures (match tot_parse_byte_sorted_list_bare ord p b with
    | Some (l, n) -> Seq.slice b 0 n == asn1_value_list_enc (list_values f l)
    | None -> True))
= if Seq.length b = 0
  then Seq.lemma_eq_elim (Seq.slice b 0 0) Seq.empty
  else match parse p b with
  | None -> ()
  | Some (_, c) ->
    if c = 0 then ()
    else begin
      let b' = Seq.slice b c (Seq.length b) in
      sorted_list_aux_esound ord p f (Seq.slice b 0 c) b';
      match tot_parse_byte_sorted_list_aux ord p (Seq.slice b 0 c) b' with
      | Some (_, n2) ->
        slice_split b c n2
      | None -> ()
    end
#pop-options

let sized_list_esound (ne: bool) (#t: Type) (p: asn1_strong_parser t) (f: t -> GTot asn1_value)
: Lemma
  (requires (esound p (fun x -> asn1_value_enc (f x))))
  (ensures (esound (parse_sized_list ne p) (fun l -> asn1_value_list_enc (list_values f l))))
= let prf (b: bytes) : Lemma (match parse (parse_sized_list ne p) b with
    | Some (l, n) -> Seq.slice b 0 n == asn1_value_list_enc (list_values f l)
    | None -> True)
  = parse_filter_eq (parse_list p) (list_size_ok ne) b;
    list_esound_at p f b
  in
  Classical.forall_intro prf

let sized_set_esound (ne: bool) (#t: Type) (p: asn1_strong_parser t) (f: t -> GTot asn1_value)
: Lemma
  (requires (esound p (fun x -> asn1_value_enc (f x))))
  (ensures (esound (parse_sized_set ne p) (fun l -> asn1_value_list_enc (list_values f l))))
= let prf (b: bytes) : Lemma (match parse (parse_sized_set ne p) b with
    | Some (l, n) -> Seq.slice b 0 n == asn1_value_list_enc (list_values f l)
    | None -> True)
  = parse_filter_eq (parse_asn1_set_of p) (list_size_ok ne) b;
    Classical.forall_intro (fun ord -> Classical.move_requires (sorted_list_esound ord p f) b)
  in
  Classical.forall_intro prf

let rec list_to_values_eq (#s: _) (k: asn1_k s) (l: list (asn1_t k))
: Lemma (ensures (list_to_values k l == list_values (to_value k) l)) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> list_to_values_eq k q

(* SEQUENCE items *)

let pure_value (it: gen_decorated_parser_twin) (x: asn1_decorated_pure_t (Mkgendcparser?.d it)) : GTot asn1_value =
  match it with
  | Mkgendcparser d _ _ ->
    let (| _, _, dk |) = d in
    match dk with
    | ASN1_PLAIN_ILC k -> to_value k x
    | ASN1_OPTION_ILC k -> to_value k x
    | ASN1_DEFAULT_TERMINAL id #k _ -> terminal_to_value id k x
    | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k _ _ -> terminal_to_value id k x

let item_values (it: gen_decorated_parser_twin) (x: asn1_decorated_t (Mkgendcparser?.d it)) : GTot (list asn1_value) =
  match it with
  | Mkgendcparser d _ _ ->
    let (| _, _, dk |) = d in
    dec_to_values dk x

let item_esound (it: gen_decorated_parser_twin) : prop =
  esound_twin (Mkgendcparser?.fp it) (fun x -> asn1_value_enc (pure_value it x))

let rec items_esound (its: list gen_decorated_parser_twin) : Tot prop (decreases its) =
  match its with
  | [] -> True
  | hd :: tl -> item_esound hd /\ items_esound tl

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let item_twin_v (it: gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (item_esound it))
  (ensures (match parse (parse_asn1_sequence_item_twin it id) b with
    | Some (x, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_list_enc (item_values it x)
    | None -> True))
= Classical.forall_intro list_enc_single;
  match it with
  | Mkgendcparser d p fp ->
    let (| _, _, dk |) = d in
    assert (match parse (fp id) b with
      | Some (x, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_enc (pure_value it x)
      | None -> True);
    match dk with
    | ASN1_PLAIN_ILC _ -> ()
    | ASN1_OPTION_ILC _ -> parse_synth_eq (fp id) Some b
    | ASN1_DEFAULT_TERMINAL _ #k_dl defv_l ->
      let defv = key_of_lit k_dl defv_l in
      parse_synth_eq (fp id `parse_filter` defaultv_filter defv) (defaultv_synth defv) b;
      parse_filter_eq (fp id) (defaultv_filter defv) b
    | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k_dl r defv_l ->
      let defv : parse_filter_refine (restriction_pred r) = key_of_lit k_dl defv_l in
      let p1 = fp id `parse_filter` restriction_pred r in
      parse_synth_eq (p1 `parse_filter` defaultv_filter #(asn1_decorated_pure_t d) defv) (defaultv_synth #(asn1_decorated_pure_t d) defv) b;
      parse_filter_eq p1 (defaultv_filter #(asn1_decorated_pure_t d) defv) b;
      parse_filter_eq (fp id) (restriction_pred r) b
#pop-options

let rec seq_values (its: list gen_decorated_parser_twin) (x: asn1_sequence_t (List.map Mkgendcparser?.d its)) : GTot (list asn1_value) (decreases its) =
  match its with
  | [] -> []
  | [hd] -> item_values hd x
  | hd :: tl ->
    let x' : asn1_decorated_t (Mkgendcparser?.d hd) & asn1_sequence_t (List.map Mkgendcparser?.d tl) = x in
    item_values hd (fst x') `List.append` seq_values tl (snd x')

let item_default_values (it: gen_decorated_parser_twin)
: Lemma (match generate_defaultable_item it with
    | Some v -> item_values it v == []
    | None -> True)
= ()

let rec seq_default_values (its: list gen_decorated_parser_twin)
: Lemma
  (ensures (match generate_defaultable_items its with
    | Some v -> seq_values its v == []
    | None -> True))
  (decreases its)
= match its with
  | [] -> ()
  | [hd] -> item_default_values hd
  | hd :: tl -> item_default_values hd; seq_default_values tl

(* Value-level unfolding of the SEQUENCE machine *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 64"
let seq'_veq (its: list gen_decorated_parser_twin {Cons? its}) (st: option asn1_id_t) (b: bytes)
: Lemma (parse (make_asn1_sequence_parser' its st) b == (
    if None? st && Some? (generate_defaultable_items its) && Seq.length b = 0
    then Some (Some?.v (generate_defaultable_items its), 0)
    else parse (make_asn1_sequence_parser'' its st) b))
= seq'_unfold its st;
  let defv = match st with None -> generate_defaultable_items its | Some _ -> None in
  let p = make_asn1_sequence_parser'' its st in
  assert (parse (make_asn1_sequence_parser_guard its make_asn1_sequence_parser'' st) b == parse (parse_defaultable defv p) b)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_guard]; zeta; iota]);
  parse_defaultable_eq #asn1_weak_parser_kind defv p b

let seq''_veq (its: list gen_decorated_parser_twin {Cons? its}) (st: option asn1_id_t) (b: bytes)
: Lemma (
    make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
    let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
    let k = glb asn1_strong_parser_kind parse_ret_kind in
    let p = match st with None -> weaken k parse_asn1_identifier_U32 | Some id -> weaken k (parse_ret id) in
    and_then_cases_injective pbt /\
    parse (make_asn1_sequence_parser'' its st) b == parse (p `and_then` pbt) b)
= make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
  seq''_unfold its st;
  let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  let p = match st with None -> weaken k parse_asn1_identifier_U32 | Some id -> weaken k (parse_ret id) in
  assert (parse (make_asn1_sequence_parser_body pbt st) b == parse (p `and_then` pbt) b)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body]; zeta; iota])

#push-options "--fuel 2"
let body_twin_veq_single (hd: gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma (parse (make_asn1_sequence_parser_body_twin [hd] make_asn1_sequence_parser' id) b == parse (parse_asn1_sequence_item_twin hd id) b)
= assert (parse (make_asn1_sequence_parser_body_twin [hd] make_asn1_sequence_parser' id) b == parse (parse_asn1_sequence_item_twin hd id) b)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body_twin]; zeta; iota])
#pop-options

let body_twin_veq_cons (hd hd': gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma (
    let pbt = make_asn1_sequence_parser_body_twin (hd :: hd' :: tl) make_asn1_sequence_parser' in
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    if FStar.Set.mem id s
    then parse (pbt id) b == parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_parser' (hd' :: tl) None) b
    else match de with
    | PLAIN -> parse (pbt id) b == None
    | _ -> (match generate_defaultable_item hd with
      | Some defv -> parse (pbt id) b == parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_parser' (hd' :: tl) (Some id)) b
      | None -> False))
= let pbt = make_asn1_sequence_parser_body_twin (hd :: hd' :: tl) make_asn1_sequence_parser' in
  let Mkgendcparser d _ _ = hd in
  let (| s, de, _ |) = d in
  if FStar.Set.mem id s
  then
    assert (parse (pbt id) b == parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_parser' (hd' :: tl) None) b)
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body_twin]; zeta; iota])
  else match de with
  | PLAIN ->
    assert (parse (pbt id) b == parse (fail_parser asn1_strong_parser_kind (asn1_decorated_t d) `nondep_then` make_asn1_sequence_parser' (hd' :: tl) None) b)
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body_twin]; zeta; iota]);
    nondep_then_eq (fail_parser asn1_strong_parser_kind (asn1_decorated_t d)) (make_asn1_sequence_parser' (hd' :: tl) None) b
  | _ ->
    let Some defv = generate_defaultable_item hd in
    assert (parse (pbt id) b == parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_parser' (hd' :: tl) (Some id)) b)
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body_twin]; zeta; iota])
#pop-options

(* The SEQUENCE machine, at the level of values *)

let seq_vpost (its: list gen_decorated_parser_twin) (st: option asn1_id_t) (b: bytes) (n: nat) (x: asn1_sequence_t (List.map Mkgendcparser?.d its)) : GTot prop =
  n <= Seq.length b /\
  (match st with
   | None -> Seq.slice b 0 n == asn1_value_list_enc (seq_values its x)
   | Some id -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_list_enc (seq_values its x))

let id_append_split (i: bytes) (b: bytes) (c n2: nat)
: Lemma
  (requires (c + n2 <= Seq.length b))
  (ensures (i `Seq.append` Seq.slice b 0 (c + n2) == (i `Seq.append` Seq.slice b 0 c) `Seq.append` Seq.slice (Seq.slice b c (Seq.length b)) 0 n2))
= slice_split b c n2;
  Seq.append_assoc i (Seq.slice b 0 c) (Seq.slice (Seq.slice b c (Seq.length b)) 0 n2)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let rec seq_vmachine (its: list gen_decorated_parser_twin) (st: option asn1_id_t) (b: bytes)
: Lemma
  (requires (items_esound its))
  (ensures (match parse (make_asn1_sequence_parser' its st) b with
    | Some (x, n) -> seq_vpost its st b n x
    | None -> True))
  (decreases %[its; 2])
= match its with
  | [] ->
    seq'_parse its st b;
    Seq.lemma_eq_elim (Seq.slice b 0 0) Seq.empty
  | _ ->
    seq'_veq its st b;
    seq_default_values its;
    seq_vbody its st b;
    if Seq.length b = 0 then Seq.lemma_eq_elim (Seq.slice b 0 0) Seq.empty

and seq_vbody (its: list gen_decorated_parser_twin) (st: option asn1_id_t) (b: bytes)
: Lemma
  (requires (Cons? its /\ items_esound its))
  (ensures (match parse (make_asn1_sequence_parser'' its st) b with
    | Some (x, n) -> seq_vpost its st b n x
    | None -> True))
  (decreases %[its; 1])
= seq''_veq its st b;
  let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  match st with
  | None ->
    and_then_eq (weaken k parse_asn1_identifier_U32) pbt b;
    parse_asn1_identifier_U32_consumed b;
    begin match parse parse_asn1_identifier_U32 b with
    | None -> ()
    | Some (id, c1) ->
      let b1 = Seq.slice b c1 (Seq.length b) in
      seq_vtwin its id b1;
      match parse (pbt id) b1 with
      | None -> ()
      | Some (_, n1) -> slice_split b c1 n1
    end
  | Some id ->
    and_then_eq (weaken k (parse_ret id)) pbt b;
    Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
    seq_vtwin its id b

and seq_vtwin (its: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (Cons? its /\ items_esound its))
  (ensures (match parse (make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' id) b with
    | Some (x, n) -> seq_vpost its (Some id) b n x
    | None -> True))
  (decreases %[its; 0])
= match its with
  | [hd] ->
    body_twin_veq_single hd id b;
    item_twin_v hd id b
  | hd :: hd' :: tl ->
    body_twin_veq_cons hd hd' tl id b;
    let Mkgendcparser d _ _ = hd in
    let (| s, de, dk |) = d in
    if FStar.Set.mem id s
    then begin
      let p1 = parse_asn1_sequence_item_twin hd id in
      let p2 = make_asn1_sequence_parser' (hd' :: tl) None in
      nondep_then_eq p1 p2 b;
      item_twin_v hd id b;
      match parse p1 b with
      | None -> ()
      | Some (x1, c) ->
        let b' = Seq.slice b c (Seq.length b) in
        seq_vmachine (hd' :: tl) None b';
        match parse p2 b' with
        | None -> ()
        | Some (x2, n2) ->
          id_append_split (asn1_id_enc id) b c n2;
          list_enc_append (item_values hd x1) (seq_values (hd' :: tl) x2)
    end
    else match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      item_default_values hd;
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_parser' (hd' :: tl) (Some id) in
      nondep_then_eq p1 p2 b;
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      seq_vmachine (hd' :: tl) (Some id) b
#pop-options

let seq_parser_esound (its: list gen_decorated_parser_twin)
: Lemma
  (requires (items_esound its))
  (ensures (esound (make_asn1_sequence_parser its) (fun x -> asn1_value_list_enc (seq_values its x))))
= Classical.forall_intro (Classical.move_requires (seq_vmachine its None))

(* The ANY DEFINED BY machine, at the level of values *)

let rec any_values (its: list gen_decorated_parser_twin) (#t: Type) (sv: t -> GTot (list asn1_value)) (x: asn1_sequence_any_t (List.map Mkgendcparser?.d its) t) : GTot (list asn1_value) (decreases its) =
  match its with
  | [] -> sv x
  | [hd] ->
    let x' : asn1_decorated_t (Mkgendcparser?.d hd) & t = x in
    item_values hd (fst x') `List.append` sv (snd x')
  | hd :: tl ->
    let x' : asn1_decorated_t (Mkgendcparser?.d hd) & asn1_sequence_any_t (List.map Mkgendcparser?.d tl) t = x in
    item_values hd (fst x') `List.append` any_values tl sv (snd x')

let sfx_esound (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sv: t -> GTot (list asn1_value)) : prop =
  esound (Mkparsertwin?.p sfx) (fun x -> asn1_value_list_enc (sv x)) /\
  esound_twin (Mkparsertwin?.fp sfx) (fun x -> asn1_value_list_enc (sv x))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let any'_veq_nil (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (st: option asn1_id_t) (b: bytes)
: Lemma (parse (make_asn1_sequence_any_parser' [] sfx st) b == parse (match st with Some id -> Mkparsertwin?.fp sfx id | None -> Mkparsertwin?.p sfx) b)
= assert (parse (make_asn1_sequence_any_parser' [] sfx st) b == parse (match st with Some id -> Mkparsertwin?.fp sfx id | None -> Mkparsertwin?.p sfx) b)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser']; zeta; iota])

let any'_veq_cons (its: list gen_decorated_parser_twin {Cons? its}) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (st: option asn1_id_t) (b: bytes)
: Lemma (
    and_then_cases_injective (make_asn1_sequence_any_parser'' its sfx) /\
    parse (make_asn1_sequence_any_parser' its sfx st) b == parse (any_guard_p st `and_then` make_asn1_sequence_any_parser'' its sfx) b)
= assert (parse (make_asn1_sequence_any_parser' its sfx st) b == parse (make_asn1_sequence_any_parser_guard its (make_asn1_sequence_any_parser'' its sfx) st) b)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser']; zeta; iota]);
  assert (parse (make_asn1_sequence_any_parser_guard its (make_asn1_sequence_any_parser'' its sfx) st) b == parse (any_guard_p st `and_then` make_asn1_sequence_any_parser'' its sfx) b)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_guard; `%any_guard_p]; zeta; iota])

let any''_veq (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (id: asn1_id_t) (b: bytes)
: Lemma (
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    let pb = make_asn1_sequence_any_parser'' (hd :: tl) sfx id in
    pb == make_asn1_sequence_any_parser_body (hd :: tl) (make_asn1_sequence_any_parser' tl sfx) id /\
    (if FStar.Set.mem id s
    then True
    else match de with
    | PLAIN -> parse pb b == None
    | _ -> Some? (generate_defaultable_item hd)))
= let Mkgendcparser d _ _ = hd in
  let (| s, de, _ |) = d in
  let pb = make_asn1_sequence_any_parser'' (hd :: tl) sfx id in
  assert (make_asn1_sequence_any_parser'' (hd :: tl) sfx id == make_asn1_sequence_any_parser_body (hd :: tl) (make_asn1_sequence_any_parser' tl sfx) id)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser''; `%List.Tot.tl; `%List.Tot.Base.tl]; zeta; iota]; FStar.Tactics.trefl ());
  if FStar.Set.mem id s
  then ()
  else match de with
  | PLAIN ->
    assert (parse pb b == parse (fail_parser asn1_strong_parser_kind (asn1_decorated_t d) `nondep_then` make_asn1_sequence_any_parser' tl sfx None) b)
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_body]; zeta; iota]);
    nondep_then_eq (fail_parser asn1_strong_parser_kind (asn1_decorated_t d)) (make_asn1_sequence_any_parser' tl sfx None) b
  | _ -> ()

let any_body_veq_single (hd: gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (id: asn1_id_t) (b: bytes)
: Lemma (
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    let pb = make_asn1_sequence_any_parser_body [hd] (make_asn1_sequence_any_parser' [] sfx) id in
    if FStar.Set.mem id s
    then parse pb b == parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_any_parser' [] sfx None) b
    else match de with
    | PLAIN -> True
    | _ -> (match generate_defaultable_item hd with
      | Some defv -> parse pb b == parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_any_parser' [] sfx (Some id)) b
      | None -> True))
= let Mkgendcparser d _ _ = hd in
  let (| s, de, _ |) = d in
  let pb = make_asn1_sequence_any_parser_body [hd] (make_asn1_sequence_any_parser' [] sfx) id in
  if FStar.Set.mem id s
  then
    assert (parse pb b == parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_any_parser' [] sfx None) b)
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_body]; zeta; iota])
  else match de with
  | PLAIN -> ()
  | _ ->
    match generate_defaultable_item hd with
    | Some defv ->
      assert (parse pb b == parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_any_parser' [] sfx (Some id)) b)
        by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_body]; zeta; iota])
    | None -> ()

let any_body_veq_cons (hd hd': gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (id: asn1_id_t) (b: bytes)
: Lemma (
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    let pb = make_asn1_sequence_any_parser_body (hd :: hd' :: tl) (make_asn1_sequence_any_parser' (hd' :: tl) sfx) id in
    if FStar.Set.mem id s
    then parse pb b == parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_any_parser' (hd' :: tl) sfx None) b
    else match de with
    | PLAIN -> True
    | _ -> (match generate_defaultable_item hd with
      | Some defv -> parse pb b == parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_any_parser' (hd' :: tl) sfx (Some id)) b
      | None -> True))
= let Mkgendcparser d _ _ = hd in
  let (| s, de, _ |) = d in
  let pb = make_asn1_sequence_any_parser_body (hd :: hd' :: tl) (make_asn1_sequence_any_parser' (hd' :: tl) sfx) id in
  if FStar.Set.mem id s
  then
    assert (parse pb b == parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_any_parser' (hd' :: tl) sfx None) b)
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_body]; zeta; iota])
  else match de with
  | PLAIN -> ()
  | _ ->
    match generate_defaultable_item hd with
    | Some defv ->
      assert (parse pb b == parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_any_parser' (hd' :: tl) sfx (Some id)) b)
        by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_body]; zeta; iota])
    | None -> ()
#pop-options

let any_vpost (its: list gen_decorated_parser_twin) (#t: Type) (sv: t -> GTot (list asn1_value)) (st: option asn1_id_t) (b: bytes) (n: nat) (x: asn1_sequence_any_t (List.map Mkgendcparser?.d its) t) : GTot prop =
  n <= Seq.length b /\
  (match st with
   | None -> Seq.slice b 0 n == asn1_value_list_enc (any_values its sv x)
   | Some id -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_list_enc (any_values its sv x))

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let rec any_vmachine (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sv: t -> GTot (list asn1_value)) (st: option asn1_id_t) (b: bytes)
: Lemma
  (requires (items_esound its /\ sfx_esound sfx sv))
  (ensures (match parse (make_asn1_sequence_any_parser' its sfx st) b with
    | Some (x, n) -> any_vpost its sv st b n x
    | None -> True))
  (decreases %[its; 1])
= match its with
  | [] -> any'_veq_nil sfx st b
  | _ ->
    any'_veq_cons its sfx st b;
    let pb = make_asn1_sequence_any_parser'' its sfx in
    match st with
    | None ->
      and_then_eq (any_guard_p None) pb b;
      parse_asn1_identifier_U32_consumed b;
      begin match parse parse_asn1_identifier_U32 b with
      | None -> ()
      | Some (id, c1) ->
        let b1 = Seq.slice b c1 (Seq.length b) in
        any_vtwin its sfx sv id b1;
        match parse (pb id) b1 with
        | None -> ()
        | Some (_, n1) -> slice_split b c1 n1
      end
    | Some id ->
      and_then_eq (any_guard_p st) pb b;
      assert (parse (any_guard_p st) b == Some (id, 0));
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      assert (parse (make_asn1_sequence_any_parser' its sfx st) b == parse (pb id) b);
      any_vtwin its sfx sv id b

and any_vtwin (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sv: t -> GTot (list asn1_value)) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (Cons? its /\ items_esound its /\ sfx_esound sfx sv))
  (ensures (match parse (make_asn1_sequence_any_parser'' its sfx id) b with
    | Some (x, n) -> any_vpost its sv (Some id) b n x
    | None -> True))
  (decreases %[its; 0])
= let hd :: tl = its in
  any''_veq hd tl sfx id b;
  let Mkgendcparser d _ _ = hd in
  let (| s, de, dk |) = d in
  match tl with
  | [] ->
    any_body_veq_single hd sfx id b;
    if FStar.Set.mem id s
    then begin
      let p1 = parse_asn1_sequence_item_twin hd id in
      let p2 = make_asn1_sequence_any_parser' [] sfx None in
      nondep_then_eq p1 p2 b;
      item_twin_v hd id b;
      match parse p1 b with
      | None -> ()
      | Some (x1, c) ->
        let b' = Seq.slice b c (Seq.length b) in
        any_vmachine [] sfx sv None b';
        match parse p2 b' with
        | None -> ()
        | Some (x2, n2) ->
          id_append_split (asn1_id_enc id) b c n2;
          list_enc_append (item_values hd x1) (sv x2)
    end
    else begin match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      item_default_values hd;
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_any_parser' [] sfx (Some id) in
      nondep_then_eq p1 p2 b;
      assert (parse p1 b == Some (defv, 0));
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      any_vmachine [] sfx sv (Some id) b
    end
  | hd' :: tl' ->
    any_body_veq_cons hd hd' tl' sfx id b;
    if FStar.Set.mem id s
    then begin
      let p1 = parse_asn1_sequence_item_twin hd id in
      let p2 = make_asn1_sequence_any_parser' tl sfx None in
      nondep_then_eq p1 p2 b;
      item_twin_v hd id b;
      match parse p1 b with
      | None -> ()
      | Some (x1, c) ->
        let b' = Seq.slice b c (Seq.length b) in
        any_vmachine tl sfx sv None b';
        match parse p2 b' with
        | None -> ()
        | Some (x2, n2) ->
          id_append_split (asn1_id_enc id) b c n2;
          list_enc_append (item_values hd x1) (any_values tl sv x2)
    end
    else begin match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      item_default_values hd;
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_any_parser' tl sfx (Some id) in
      nondep_then_eq p1 p2 b;
      assert (parse p1 b == Some (defv, 0));
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      any_vmachine tl sfx sv (Some id) b
    end
#pop-options

let any_parser_esound (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sv: t -> GTot (list asn1_value))
: Lemma
  (requires (items_esound its /\ sfx_esound sfx sv))
  (ensures (esound (make_asn1_sequence_any_parser its sfx) (fun x -> asn1_value_list_enc (any_values its sv x))))
= Classical.forall_intro (Classical.move_requires (any_vmachine its sfx sv None))

(* CHOICE *)

let content_enc (id: asn1_id_t) (k: asn1_content_k) (x: asn1_content_t k) : GTot bytes =
  value_contents (content_to_value id k x)

let content_esound (id: asn1_id_t) (k: asn1_content_k) : prop =
  wf_content id k /\
  esound (asn1_content_as_parser k) (content_enc id k)

let esound_ext (#k: parser_kind) (#t: Type) (p: parser k t) (g1 g2: t -> GTot bytes)
: Lemma
  (requires (esound p g1 /\ (forall x. g1 x == g2 x)))
  (ensures (esound p g2))
= ()

let rec lc_esound (lc: list (asn1_id_t & asn1_content_k)) : Tot prop (decreases lc) =
  match lc with
  | [] -> True
  | (x, y) :: tl -> content_esound x y /\ lc_esound tl

let content_value_enc (id: asn1_id_t) (k: asn1_content_k) (x: asn1_content_t k)
: Lemma
  (requires (wf_content id k))
  (ensures (asn1_value_enc (content_to_value id k x) == enc_tlv id true (value_contents (content_to_value id k x))))
= content_shape id k x

let synth_eq_pat
  (#k: parser_kind) (#t1 #t2: Type) (p: parser k t1) (f: t1 -> Tot t2) (b: bytes)
: Lemma
  (requires (synth_injective f))
  (ensures (parse (parse_synth p f) b == (match parse p b with
    | Some (x, n) -> Some (f x, n)
    | None -> None)))
  [SMTPat (parse (parse_synth p f) b)]
= parse_synth_eq p f b

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let choice_payload_unfold
  (#t: eqtype)
  (hd: t & gen_parser asn1_strong_parser_kind)
  (tl: list (t & gen_parser asn1_strong_parser_kind))
  (id: t)
  (b: bytes)
: Lemma
  (requires (id <> fst hd))
  (ensures (
    match parse (make_gen_choice_strong_payload_parser (hd :: tl) id) b, parse (make_gen_choice_strong_payload_parser tl id) b with
    | Some (v, n), Some (v', n') -> n == n' /\ dfst v == dfst v' /\ v == lemma_choice_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) id v'
    | None, None -> True
    | _ -> False))
= assert (extract_types (hd :: tl) == (fst hd, Mkgenparser?.t (snd hd)) :: extract_types tl);
  assert_norm (project_tags (hd :: tl) == tag_of_gen_choice_type (extract_types (hd :: tl)));
  assert (make_gen_choice_strong_payload_parser (hd :: tl) id == parse_synth (make_gen_choice_strong_payload_parser tl id) (fun x -> lemma_choice_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) id x))
    by (FStar.Tactics.norm [delta_only [`%make_gen_choice_strong_payload_parser]; zeta; iota]; FStar.Tactics.smt ());
  parse_synth_eq (make_gen_choice_strong_payload_parser tl id) (fun x -> lemma_choice_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) id x) b

let choice_payload_step
  (x: asn1_id_t) (y: asn1_content_k)
  (tl: list (asn1_id_t & asn1_content_k))
  (id: asn1_id_t)
  (b: bytes)
: Lemma
  (requires (id <> x))
  (ensures (
    match parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser ((x, y) :: tl)) id) b, parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser tl) id) b with
    | Some (v, n), Some (v', n') -> n == n' /\ choice_to_value ((x, y) :: tl) (dfst v) (dsnd v) == choice_to_value tl (dfst v') (dsnd v')
    | None, None -> True
    | _ -> False))
= let hdp = (x, Mkgenparser (asn1_content_t y) (parse_asn1_LC (asn1_content_as_parser y))) in
  assert (asn1_lc_as_parser ((x, y) :: tl) == hdp :: asn1_lc_as_parser tl) by (FStar.Tactics.norm [delta_only [`%asn1_lc_as_parser; `%dasn1_lc_as_parser]; zeta; iota]; FStar.Tactics.smt ());
  choice_payload_unfold hdp (asn1_lc_as_parser tl) id b;
  match parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser tl) id) b with
  | Some (v', _) ->
    let (| i, z |) = v' in
    assert (lemma_choice_cast (fst hdp, Mkgenparser?.t (snd hdp)) (extract_types (asn1_lc_as_parser tl)) id (| i, z |) == (| i, z |)) by (FStar.Tactics.norm [delta_only [`%lemma_choice_cast]; zeta; iota]; FStar.Tactics.smt ())
  | None -> ()
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec choice_payload_v
  (lc: list (asn1_id_t & asn1_content_k))
  (id: asn1_id_t)
  (b: bytes)
: Lemma
  (requires (lc_esound lc))
  (ensures (match parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) b with
    | Some (v, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_enc (choice_to_value lc (dfst v) (dsnd v))
    | None -> True))
  (decreases lc)
= let lp = asn1_lc_as_parser lc in
  match lc with
  | [] -> ()
  | (x, y) :: tl ->
    if id = x
    then begin
      let p = parse_asn1_LC (asn1_content_as_parser y) in
      parse_synth_eq p (attach_tag lp id) b;
      lc_at (asn1_content_as_parser y) (content_enc x y) b;
      match parse p b with
      | Some (c, _) -> content_value_enc x y c
      | None -> ()
    end
    else begin
      choice_payload_v tl id b;
      choice_payload_step x y tl id b
    end
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let choice_v_at (lc: list (asn1_id_t & asn1_content_k)) (b: bytes)
: Lemma
  (requires (lc_esound lc))
  (ensures (match parse (make_gen_choice_strong_parser parse_asn1_identifier_U32 (asn1_lc_as_parser lc)) b with
    | Some (v, n) -> Seq.slice b 0 n == asn1_value_enc (choice_to_value lc (dfst v) (dsnd v))
    | None -> True))
= let lp = asn1_lc_as_parser lc in
  parse_tagged_union_eq parse_asn1_identifier_U32 (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_strong_payload_parser lp) b;
  parse_asn1_identifier_U32_consumed b;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    choice_payload_v lc id b1;
    match parse (make_gen_choice_strong_payload_parser lp id) b1 with
    | None -> ()
    | Some (_, n2) -> slice_split b c1 n2

let choice_twin_v (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (lc_esound lc))
  (ensures (match parse (parse_tagged_union_payload (project_tags (asn1_lc_as_parser lc)) (make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc)) id) b with
    | Some (v, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_enc (choice_to_value lc (dfst v) (dsnd v))
    | None -> True))
= let lp = asn1_lc_as_parser lc in
  parse_synth_eq (make_gen_choice_strong_payload_parser lp id) (synth_tagged_union_data (project_tags lp) id) b;
  choice_payload_v lc id b
#pop-options

(* Bridges between the schema-level and the parser-level value functions *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec items_seq_values (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items)
: Lemma
  (ensures (
    asn1_sequence_t_core_equiv items;
    items_to_values items x == seq_values (asn1_sequence_as_parser items) x))
  (decreases items)
= asn1_sequence_t_core_equiv items;
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    items_seq_values tl (snd x')

let rec items_any_values (#ids: _) (items: asn1_gen_items_l ids) (#t: Type) (sfx: t -> Tot (list asn1_value)) (x: asn1_sequence_any_t_core items t)
: Lemma
  (ensures (
    asn1_sequence_any_t_equiv items t;
    items_any_to_values items sfx x == any_values (asn1_sequence_as_parser items) sfx x))
  (decreases items)
= asn1_sequence_any_t_equiv items t;
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl t = x in
    items_any_values tl sfx (snd x')
#pop-options

let rec any_values_ext (its: list gen_decorated_parser_twin) (#t: Type) (sv1 sv2: t -> GTot (list asn1_value)) (x: asn1_sequence_any_t (List.map Mkgendcparser?.d its) t)
: Lemma
  (requires (forall s. sv1 s == sv2 s))
  (ensures (any_values its sv1 x == any_values its sv2 x))
  (decreases its)
= match its with
  | [] -> ()
  | [hd] -> ()
  | hd :: tl ->
    let x' : asn1_decorated_t (Mkgendcparser?.d hd) & asn1_sequence_any_t (List.map Mkgendcparser?.d tl) t = x in
    any_values_ext tl sv1 sv2 (snd x')

(* ANY DEFINED BY: the supported payloads *)

let rec ls_esound (#t: eqtype) (ls: list (t & asn1_gen_items_lk)) : Tot prop (decreases ls) =
  match ls with
  | [] -> True
  | (_, y) :: tl -> items_esound (asn1_sequence_as_parser (dsnd y)) /\ ls_esound tl

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let weak_payload_unfold
  (#t: eqtype)
  (hd: t & gen_parser asn1_weak_parser_kind)
  (tl: list (t & gen_parser asn1_weak_parser_kind))
  (id: t)
  (b: bytes)
: Lemma
  (requires (id <> fst hd))
  (ensures (
    match parse (make_gen_choice_weak_payload_parser (hd :: tl) id) b, parse (make_gen_choice_weak_payload_parser tl id) b with
    | Some (v, n), Some (v', n') -> n == n' /\ dfst v == dfst v' /\ v == lemma_choice_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) id v'
    | None, None -> True
    | _ -> False))
= assert (extract_types (hd :: tl) == (fst hd, Mkgenparser?.t (snd hd)) :: extract_types tl);
  assert_norm (project_tags (hd :: tl) == tag_of_gen_choice_type (extract_types (hd :: tl)));
  assert (make_gen_choice_weak_payload_parser (hd :: tl) id == parse_synth (make_gen_choice_weak_payload_parser tl id) (fun x -> lemma_choice_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) id x))
    by (FStar.Tactics.norm [delta_only [`%make_gen_choice_weak_payload_parser]; zeta; iota]; FStar.Tactics.smt ());
  parse_synth_eq (make_gen_choice_weak_payload_parser tl id) (fun x -> lemma_choice_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) id x) b

let weak_payload_fb_unfold
  (#t: eqtype)
  (hd: t & gen_parser asn1_weak_parser_kind)
  (tl: list (t & gen_parser asn1_weak_parser_kind))
  (fb: gen_parser asn1_weak_parser_kind)
  (id: t)
  (b: bytes)
: Lemma
  (requires (id <> fst hd))
  (ensures (
    match parse (make_gen_choice_with_fallback_weak_payload_parser (hd :: tl) fb id) b, parse (make_gen_choice_with_fallback_weak_payload_parser tl fb id) b with
    | Some (v, n), Some (v', n') -> n == n' /\ dfst v == dfst v' /\ v == lemma_choice_with_fallback_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) (Mkgenparser?.t fb) id v'
    | None, None -> True
    | _ -> False))
= assert (extract_types (hd :: tl) == (fst hd, Mkgenparser?.t (snd hd)) :: extract_types tl);
  assert_norm (project_tags_with_fallback (hd :: tl) fb == tag_of_gen_choice_type_with_fallback (extract_types (hd :: tl)) (Mkgenparser?.t fb));
  assert (make_gen_choice_with_fallback_weak_payload_parser (hd :: tl) fb id == parse_synth (make_gen_choice_with_fallback_weak_payload_parser tl fb id) (fun x -> lemma_choice_with_fallback_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) (Mkgenparser?.t fb) id x))
    by (FStar.Tactics.norm [delta_only [`%make_gen_choice_with_fallback_weak_payload_parser]; zeta; iota]; FStar.Tactics.smt ());
  parse_synth_eq (make_gen_choice_with_fallback_weak_payload_parser tl fb id) (fun x -> lemma_choice_with_fallback_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) (Mkgenparser?.t fb) id x) b

let ls_hd (#t: eqtype) (x: t) (y: asn1_gen_items_lk) : Tot (t & gen_parser asn1_weak_parser_kind) =
  (x, Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd y))))

let ls_as_parser_cons (#lt: eqtype) (t: eqtype) (f: lt -> Tot t) (x: lt) (y: asn1_gen_items_lk) (tl: list (lt & asn1_gen_items_lk))
: Lemma (asn1_ls_as_parser t f ((x, y) :: tl) == ls_hd (f x) y :: asn1_ls_as_parser t f tl)
= assert (asn1_ls_as_parser t f ((x, y) :: tl) == ls_hd (f x) y :: asn1_ls_as_parser t f tl)
    by (FStar.Tactics.norm [delta_only [`%asn1_ls_as_parser; `%ls_hd]; zeta; iota]; FStar.Tactics.smt ())

let ls_payload_step (#lt: eqtype) (t: eqtype) (f: lt -> Tot t) (x: lt) (y: asn1_gen_items_lk) (tl: list (lt & asn1_gen_items_lk)) (key: t) (b: bytes)
: Lemma
  (requires (key <> f x))
  (ensures (
    match parse (make_gen_choice_weak_payload_parser (asn1_ls_as_parser t f ((x, y) :: tl)) key) b, parse (make_gen_choice_weak_payload_parser (asn1_ls_as_parser t f tl) key) b with
    | Some (v, n), Some (v', n') -> n == n' /\ ls_to_values f ((x, y) :: tl) (dfst v) (dsnd v) == ls_to_values f tl (dfst v') (dsnd v')
    | None, None -> True
    | _ -> False))
= let hdp = ls_hd (f x) y in
  ls_as_parser_cons t f x y tl;
  weak_payload_unfold hdp (asn1_ls_as_parser t f tl) key b;
  match parse (make_gen_choice_weak_payload_parser (asn1_ls_as_parser t f tl) key) b with
  | Some (v', _) ->
    let (| i, z |) = v' in
    assert (lemma_choice_cast (fst hdp, Mkgenparser?.t (snd hdp)) (extract_types (asn1_ls_as_parser t f tl)) key (| i, z |) == (| i, z |)) by (FStar.Tactics.norm [delta_only [`%lemma_choice_cast]; zeta; iota]; FStar.Tactics.smt ())
  | None -> ()

let rec ls_payload_v (#lt: eqtype) (t: eqtype) (f: lt -> Tot t) (ls: list (lt & asn1_gen_items_lk)) (key: t) (b: bytes)
: Lemma
  (requires (ls_esound ls))
  (ensures (match parse (make_gen_choice_weak_payload_parser (asn1_ls_as_parser t f ls) key) b with
    | Some (v, n) -> Seq.slice b 0 n == asn1_value_list_enc (ls_to_values f ls (dfst v) (dsnd v))
    | None -> True))
  (decreases ls)
= let lp = asn1_ls_as_parser t f ls in
  match ls with
  | [] -> ()
  | (x, y) :: tl ->
    if key = f x
    then begin
      let items = dsnd y in
      let p = make_asn1_sequence_parser (asn1_sequence_as_parser items) in
      ls_as_parser_cons t f x y tl;
      parse_synth_eq p (attach_tag lp key) b;
      seq_parser_esound (asn1_sequence_as_parser items);
      match parse p b with
      | Some (c, _) -> items_seq_values items c
      | None -> ()
    end
    else begin
      ls_payload_v t f tl key b;
      ls_payload_step t f x y tl key b
    end
#pop-options

let fb_gp (fb: asn1_gen_items_lk) : Tot (gen_parser asn1_weak_parser_kind) =
  Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd fb)))

let fb_values (fb: asn1_gen_items_lk) (z: asn1_sequence_t_core (dsnd fb)) : Tot (list asn1_value) =
  items_to_values (dsnd fb) z

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let ls_fb_payload_step (#lt: eqtype) (t: eqtype) (f: lt -> Tot t) (x: lt) (y: asn1_gen_items_lk) (tl: list (lt & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (key: t) (b: bytes)
: Lemma
  (requires (key <> f x))
  (ensures (
    match parse (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser t f ((x, y) :: tl)) (fb_gp fb) key) b, parse (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser t f tl) (fb_gp fb) key) b with
    | Some (v, n), Some (v', n') -> n == n' /\ ls_fb_to_values f ((x, y) :: tl) _ (fb_values fb) (dfst v) (dsnd v) == ls_fb_to_values f tl _ (fb_values fb) (dfst v') (dsnd v')
    | None, None -> True
    | _ -> False))
= let hdp = ls_hd (f x) y in
  ls_as_parser_cons t f x y tl;
  weak_payload_fb_unfold hdp (asn1_ls_as_parser t f tl) (fb_gp fb) key b;
  match parse (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser t f tl) (fb_gp fb) key) b with
  | Some (v', _) ->
    let (| i, z |) = v' in
    assert (lemma_choice_with_fallback_cast (fst hdp, Mkgenparser?.t (snd hdp)) (extract_types (asn1_ls_as_parser t f tl)) (Mkgenparser?.t (fb_gp fb)) key (| i, z |) == (| i, z |)) by (FStar.Tactics.norm [delta_only [`%lemma_choice_with_fallback_cast]; zeta; iota]; FStar.Tactics.smt ())
  | None -> ()

let rec ls_fb_payload_v (#lt: eqtype) (t: eqtype) (f: lt -> Tot t) (ls: list (lt & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (key: t) (b: bytes)
: Lemma
  (requires (ls_esound ls /\ items_esound (asn1_sequence_as_parser (dsnd fb))))
  (ensures (match parse (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser t f ls) (fb_gp fb) key) b with
    | Some (v, n) -> Seq.slice b 0 n == asn1_value_list_enc (ls_fb_to_values f ls _ (fb_values fb) (dfst v) (dsnd v))
    | None -> True))
  (decreases ls)
= let lp = asn1_ls_as_parser t f ls in
  match ls with
  | [] ->
    let p = make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd fb)) in
    parse_synth_eq p (attach_tag_with_fallback lp (fb_gp fb) key) b;
    seq_parser_esound (asn1_sequence_as_parser (dsnd fb));
    begin match parse p b with
    | Some (c, _) -> items_seq_values (dsnd fb) c
    | None -> ()
    end
  | (x, y) :: tl ->
    if key = f x
    then begin
      let items = dsnd y in
      let p = make_asn1_sequence_parser (asn1_sequence_as_parser items) in
      ls_as_parser_cons t f x y tl;
      parse_synth_eq p (attach_tag_with_fallback lp (fb_gp fb) key) b;
      seq_parser_esound (asn1_sequence_as_parser items);
      match parse p b with
      | Some (c, _) -> items_seq_values items c
      | None -> ()
    end
    else begin
      ls_fb_payload_v t f tl fb key b;
      ls_fb_payload_step t f x y tl fb key b
    end
#pop-options

(* ANY DEFINED BY: the suffix (key, then payload) *)

let adb_key_p (kid: asn1_id_t) (key_k: asn1_terminal_k) =
  parse_asn1_ILC kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k)

let adb_key_fp (kid: asn1_id_t) (key_k: asn1_terminal_k) =
  parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k)

let adb_sv (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (s: make_gen_choice_type (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls)))
: GTot (list asn1_value)
= terminal_to_value kid key_k (dfst s) :: ls_to_values (key_of_lit key_k) ls (dfst s) (dsnd s)

let adb_fb_sv (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (s: make_gen_choice_type_with_fallback (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls)) (Mkgenparser?.t (fb_gp fb)))
: GTot (list asn1_value)
= terminal_to_value kid key_k (dfst s) :: ls_fb_to_values (key_of_lit key_k) ls _ (fb_values fb) (dfst s) (dsnd s)

let adb_key_at (kid: asn1_id_t) (key_k: asn1_terminal_k) (b: bytes)
: Lemma
  (requires (wf_terminal kid key_k))
  (ensures (match parse (adb_key_p kid key_k) b with
    | Some (key, c) -> Seq.slice b 0 c == asn1_value_enc (terminal_to_value kid key_k key)
    | None -> True))
= terminal_esound kid key_k;
  ilc_at kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k) (tbytes kid key_k) b;
  match parse (adb_key_p kid key_k) b with
  | Some (key, _) -> terminal_value_enc kid key_k key
  | None -> ()

let adb_key_twin_at (kid: asn1_id_t) (key_k: asn1_terminal_k) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (wf_terminal kid key_k))
  (ensures (match parse (adb_key_fp kid key_k id) b with
    | Some (key, c) -> asn1_id_enc id `Seq.append` Seq.slice b 0 c == asn1_value_enc (terminal_to_value kid key_k key)
    | None -> True))
= terminal_esound kid key_k;
  lc_twin_esound kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k) (tbytes kid key_k);
  match parse (adb_key_fp kid key_k id) b with
  | Some (key, _) -> terminal_value_enc kid key_k key
  | None -> ()

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"
let adb_suffix_at (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (b: bytes)
: Lemma
  (requires (wf_terminal kid key_k /\ ls_esound ls))
  (ensures (match parse (make_gen_choice_weak_parser (adb_key_p kid key_k) (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls)) b with
    | Some (v, n) -> Seq.slice b 0 n == asn1_value_list_enc (adb_sv kid key_k ls v)
    | None -> True))
= let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  parse_tagged_union_eq (adb_key_p kid key_k) (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp) b;
  adb_key_at kid key_k b;
  match parse (adb_key_p kid key_k) b with
  | None -> ()
  | Some (key, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    ls_payload_v (asn1_terminal_t key_k) (key_of_lit key_k) ls key b1;
    match parse (make_gen_choice_weak_payload_parser lp key) b1 with
    | None -> ()
    | Some (_, n2) -> slice_split b c1 n2

let adb_suffix_twin_at (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (wf_terminal kid key_k /\ ls_esound ls))
  (ensures (let r = parse (parse_tagged_union (adb_key_fp kid key_k id) (tag_of_gen_choice_type (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls))) (make_gen_choice_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls))) b in
    Some? r ==> asn1_id_enc id `Seq.append` Seq.slice b 0 (snd (Some?.v r)) == asn1_value_list_enc (adb_sv kid key_k ls (fst (Some?.v r)))))
= let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  parse_tagged_union_eq (adb_key_fp kid key_k id) (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp) b;
  adb_key_twin_at kid key_k id b;
  match parse (adb_key_fp kid key_k id) b with
  | None -> ()
  | Some (key, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    ls_payload_v (asn1_terminal_t key_k) (key_of_lit key_k) ls key b1;
    match parse (make_gen_choice_weak_payload_parser lp key) b1 with
    | None -> ()
    | Some (_, n2) -> id_append_split (asn1_id_enc id) b c1 n2

let adb_fb_suffix_at (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (b: bytes)
: Lemma
  (requires (wf_terminal kid key_k /\ ls_esound ls /\ items_esound (asn1_sequence_as_parser (dsnd fb))))
  (ensures (match parse (make_gen_choice_with_fallback_weak_parser (adb_key_p kid key_k) (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (fb_gp fb)) b with
    | Some (v, n) -> Seq.slice b 0 n == asn1_value_list_enc (adb_fb_sv kid key_k ls fb v)
    | None -> True))
= let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  parse_tagged_union_eq (adb_key_p kid key_k) (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (fb_gp fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (fb_gp fb)) b;
  adb_key_at kid key_k b;
  match parse (adb_key_p kid key_k) b with
  | None -> ()
  | Some (key, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    ls_fb_payload_v (asn1_terminal_t key_k) (key_of_lit key_k) ls fb key b1;
    match parse (make_gen_choice_with_fallback_weak_payload_parser lp (fb_gp fb) key) b1 with
    | None -> ()
    | Some (_, n2) -> slice_split b c1 n2

let adb_fb_suffix_twin_at (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (wf_terminal kid key_k /\ ls_esound ls /\ items_esound (asn1_sequence_as_parser (dsnd fb))))
  (ensures (let r = parse (parse_tagged_union (adb_key_fp kid key_k id) (tag_of_gen_choice_type_with_fallback (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls)) (Mkgenparser?.t (fb_gp fb))) (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (fb_gp fb))) b in
    Some? r ==> asn1_id_enc id `Seq.append` Seq.slice b 0 (snd (Some?.v r)) == asn1_value_list_enc (adb_fb_sv kid key_k ls fb (fst (Some?.v r)))))
= let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  parse_tagged_union_eq (adb_key_fp kid key_k id) (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (fb_gp fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (fb_gp fb)) b;
  adb_key_twin_at kid key_k id b;
  match parse (adb_key_fp kid key_k id) b with
  | None -> ()
  | Some (key, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    ls_fb_payload_v (asn1_terminal_t key_k) (key_of_lit key_k) ls fb key b1;
    match parse (make_gen_choice_with_fallback_weak_payload_parser lp (fb_gp fb) key) b1 with
    | None -> ()
    | Some (_, n2) -> id_append_split (asn1_id_enc id) b c1 n2
#pop-options

(* The suffix closures of `content_to_value` *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let adb_content_value (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) idp))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (x: asn1_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'))
: Lemma
  (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x ==
    mk_cons id (any_values (asn1_sequence_as_parser prefix) (adb_sv kid key_k ls) x))
= let clo (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) : Tot (list asn1_value) =
    let (| key, y |) = s in
    terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key y
  in
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) -> (let (| key, y |) = s in terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key y) <: list asn1_value) x))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  items_any_values prefix clo x;
  any_values_ext (asn1_sequence_as_parser prefix) clo (adb_sv kid key_k ls) x
#pop-options

let rec ls_fb_to_values_ext (#lt #t: eqtype) (f: lt -> Tot t) (ls: list (lt & asn1_gen_items_lk)) (fb: Type) (f1 f2: fb -> Tot (list asn1_value)) (key: t) (y: idlookup_with_fallback_t key (asn1_any_t_core t f ls) fb)
: Lemma
  (requires (forall z. f1 z == f2 z))
  (ensures (ls_fb_to_values f ls fb f1 key y == ls_fb_to_values f ls fb f2 key y))
  (decreases ls)
= match ls with
  | [] -> ()
  | (key', _) :: tl -> if key = f key' then () else ls_fb_to_values_ext f tl fb f1 f2 key y

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let adb_fb_content_value (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbids: id_decs {asn1_sequence_k_wf fbids}) (fbitems: asn1_gen_items_l fbids)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) idp))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (x: asn1_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'))
: Lemma
  (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x ==
    mk_cons id (any_values (asn1_sequence_as_parser prefix) (adb_fb_sv kid key_k ls (| fbids, fbitems |)) x))
= let clo (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) : Tot (list asn1_value) =
    let (| key, y |) = s in
    terminal_to_value kid key_k key ::
    ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (z: asn1_sequence_t_core fbitems) -> items_to_values fbitems z) key y
  in
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) -> (let (| key, y |) = s in terminal_to_value kid key_k key :: ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (z: asn1_sequence_t_core fbitems) -> items_to_values fbitems z) key y) <: list asn1_value) x))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  items_any_values prefix clo x;
  let prf (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems))
  : Lemma (clo s == adb_fb_sv kid key_k ls (| fbids, fbitems |) s)
  = ls_fb_to_values_ext (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (z: asn1_sequence_t_core fbitems) -> items_to_values fbitems z) (fb_values (| fbids, fbitems |)) (dfst s) (dsnd s)
  in
  Classical.forall_intro prf;
  any_values_ext (asn1_sequence_as_parser prefix) clo (adb_fb_sv kid key_k ls (| fbids, fbitems |)) x
#pop-options

(* ANY DEFINED BY contents *)

let any_enc (its: list gen_decorated_parser_twin) (#t: Type) (sv: t -> GTot (list asn1_value)) (x: asn1_sequence_any_t (List.map Mkgendcparser?.d its) t) : GTot bytes =
  asn1_value_list_enc (any_values its sv x)

let adb_lp (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) =
  asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls

let adb_sfx (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Tot (parser_twin asn1_weak_parser_kind (make_gen_choice_type (extract_types (adb_lp key_k ls))))
= assert_norm (asn1_weak_parser_kind `is_weaker_than` (and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind));
  Mkparsertwin #asn1_weak_parser_kind #(make_gen_choice_type (extract_types (adb_lp key_k ls)))
    (weaken asn1_weak_parser_kind (make_gen_choice_weak_parser (adb_key_p kid key_k) (adb_lp key_k ls)))
    (let _ = make_gen_choice_weak_parser_twin_and_then_cases_injective (adb_key_fp kid key_k) (adb_lp key_k ls) in
     fun id -> weaken asn1_weak_parser_kind (make_gen_choice_weak_parser_twin (adb_key_fp kid key_k) (adb_lp key_k ls) id))

let adb_fb_sfx (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
: Tot (parser_twin asn1_weak_parser_kind (make_gen_choice_type_with_fallback (extract_types (adb_lp key_k ls)) (Mkgenparser?.t (fb_gp fb))))
= assert_norm (asn1_weak_parser_kind `is_weaker_than` (and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind));
  Mkparsertwin #asn1_weak_parser_kind #(make_gen_choice_type_with_fallback (extract_types (adb_lp key_k ls)) (Mkgenparser?.t (fb_gp fb)))
    (weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser (adb_key_p kid key_k) (adb_lp key_k ls) (fb_gp fb)))
    (let _ = make_gen_choice_with_fallback_weak_parser_twin_and_then_cases_injective (adb_key_fp kid key_k) (adb_lp key_k ls) (fb_gp fb) in
     fun id -> weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser_twin (adb_key_fp kid key_k) (adb_lp key_k ls) (fb_gp fb) id))

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let adb_sfx_esound (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Lemma
  (requires (wf_terminal kid key_k /\ ls_esound ls))
  (ensures (sfx_esound (adb_sfx kid key_k ls) (adb_sv kid key_k ls)))
= let prf1 (b: bytes) : Lemma (match parse (Mkparsertwin?.p (adb_sfx kid key_k ls)) b with
    | Some (x, n) -> Seq.slice b 0 n == asn1_value_list_enc (adb_sv kid key_k ls x)
    | None -> True)
  = adb_suffix_at kid key_k ls b
  in
  let prf2 (id: asn1_id_t) (b: bytes) : Lemma (match parse (Mkparsertwin?.fp (adb_sfx kid key_k ls) id) b with
    | Some (x, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_list_enc (adb_sv kid key_k ls x)
    | None -> True)
  = assert (parse (Mkparsertwin?.fp (adb_sfx kid key_k ls) id) b == parse (weaken asn1_weak_parser_kind (parse_tagged_union (adb_key_fp kid key_k id) (tag_of_gen_choice_type (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls))) (make_gen_choice_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls)))) b)
      by (FStar.Tactics.norm [delta_only [`%adb_sfx; `%Mkparsertwin?.fp; `%make_gen_choice_weak_parser_twin; `%adb_lp; `%asn1_content_t]; zeta; iota]; FStar.Tactics.trefl ());
    adb_suffix_twin_at kid key_k ls id b
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2

let adb_fb_sfx_esound (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
: Lemma
  (requires (wf_terminal kid key_k /\ ls_esound ls /\ items_esound (asn1_sequence_as_parser (dsnd fb))))
  (ensures (sfx_esound (adb_fb_sfx kid key_k ls fb) (adb_fb_sv kid key_k ls fb)))
= let prf1 (b: bytes) : Lemma (match parse (Mkparsertwin?.p (adb_fb_sfx kid key_k ls fb)) b with
    | Some (x, n) -> Seq.slice b 0 n == asn1_value_list_enc (adb_fb_sv kid key_k ls fb x)
    | None -> True)
  = adb_fb_suffix_at kid key_k ls fb b
  in
  let prf2 (id: asn1_id_t) (b: bytes) : Lemma (match parse (Mkparsertwin?.fp (adb_fb_sfx kid key_k ls fb) id) b with
    | Some (x, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_list_enc (adb_fb_sv kid key_k ls fb x)
    | None -> True)
  = assert (parse (Mkparsertwin?.fp (adb_fb_sfx kid key_k ls fb) id) b == parse (weaken asn1_weak_parser_kind (parse_tagged_union (adb_key_fp kid key_k id) (tag_of_gen_choice_type_with_fallback (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls)) (Mkgenparser?.t (fb_gp fb))) (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (fb_gp fb)))) b)
      by (FStar.Tactics.norm [delta_only [`%adb_fb_sfx; `%Mkparsertwin?.fp; `%make_gen_choice_with_fallback_weak_parser_twin; `%adb_lp; `%asn1_content_t]; zeta; iota]; FStar.Tactics.trefl ());
    adb_fb_suffix_twin_at kid key_k ls fb id b
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let adb_content_esound (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) idp))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma
  (requires (wf_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') /\
    items_esound (asn1_sequence_as_parser prefix) /\ ls_esound ls))
  (ensures (content_esound id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf')))
= adb_sfx_esound kid key_k ls;
  any_parser_esound (asn1_sequence_as_parser prefix) (adb_sfx kid key_k ls) (adb_sv kid key_k ls);
  assert (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') == make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (adb_sfx kid key_k ls))
    by (FStar.Tactics.norm [delta_only [`%asn1_content_as_parser; `%adb_sfx; `%adb_lp; `%adb_key_p; `%adb_key_fp; `%asn1_content_t]; zeta; iota]; FStar.Tactics.trefl ());
  Classical.forall_intro (adb_content_value id idp prefix kid key_k ls pf pf');
  esound_ext (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf')) (any_enc (asn1_sequence_as_parser prefix) (adb_sv kid key_k ls)) (content_enc id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'))

let adb_fb_content_esound (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbids: id_decs {asn1_sequence_k_wf fbids}) (fbitems: asn1_gen_items_l fbids)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) idp))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma
  (requires (wf_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') /\
    items_esound (asn1_sequence_as_parser prefix) /\ ls_esound ls /\ items_esound (asn1_sequence_as_parser fbitems)))
  (ensures (content_esound id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf')))
= adb_fb_sfx_esound kid key_k ls (| fbids, fbitems |);
  any_parser_esound (asn1_sequence_as_parser prefix) (adb_fb_sfx kid key_k ls (| fbids, fbitems |)) (adb_fb_sv kid key_k ls (| fbids, fbitems |));
  assert (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') == make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (adb_fb_sfx kid key_k ls (| fbids, fbitems |)))
    by (FStar.Tactics.norm [delta_only [`%asn1_content_as_parser; `%adb_fb_sfx; `%adb_lp; `%adb_key_p; `%adb_key_fp; `%fb_gp; `%asn1_content_t]; zeta; iota]; FStar.Tactics.trefl ());
  Classical.forall_intro (adb_fb_content_value id idp prefix kid key_k ls fbids fbitems pf pf');
  esound_ext (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf')) (any_enc (asn1_sequence_as_parser prefix) (adb_fb_sv kid key_k ls (| fbids, fbitems |))) (content_enc id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'))
#pop-options

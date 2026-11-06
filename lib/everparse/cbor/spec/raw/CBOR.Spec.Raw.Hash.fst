module CBOR.Spec.Raw.Hash
include CBOR.Spec.Raw.Canonical
open CBOR.Spec.Util

(* A keyed hash of raw CBOR data items, compatible with the canonical
   order `cc`: items comparing equal with `cc` have the same hash. Used
   to check map key duplicates by sorting map keys by hash first.

   The hash is SipHash-1-3 over a stream of 64-bit words: each item
   contributes its head (major type, argument value), then, for
   strings, its bytes packed into little-endian words (zero-padded),
   for arrays and tags, its children. Since map entries are not
   ordered, a map contributes the (modular) sum of the hashes of its
   entries, each entry hashed from the hashes of its key and value. *)

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* SipHash-1-3 over 64-bit words *)

noeq
type sip = {
  v0: U64.t;
  v1: U64.t;
  v2: U64.t;
  v3: U64.t;
  nw: U64.t;
}

inline_for_extraction
let rotl (x: U64.t) (r: U32.t { 0 < U32.v r /\ U32.v r < 64 }) : Tot U64.t =
  U64.logor (U64.shift_left x r) (U64.shift_right x (U32.sub 64ul r))

inline_for_extraction
[@@"opaque_to_smt"]
let sip_round (s: sip) : Tot sip =
  let v0 = U64.add_mod s.v0 s.v1 in
  let v1 = rotl s.v1 13ul in
  let v1 = U64.logxor v1 v0 in
  let v0 = rotl v0 32ul in
  let v2 = U64.add_mod s.v2 s.v3 in
  let v3 = rotl s.v3 16ul in
  let v3 = U64.logxor v3 v2 in
  let v0 = U64.add_mod v0 v3 in
  let v3 = rotl v3 21ul in
  let v3 = U64.logxor v3 v0 in
  let v2 = U64.add_mod v2 v1 in
  let v1 = rotl v1 17ul in
  let v1 = U64.logxor v1 v2 in
  let v2 = rotl v2 32ul in
  { v0 = v0; v1 = v1; v2 = v2; v3 = v3; nw = s.nw }

inline_for_extraction
[@@"opaque_to_smt"]
let sip_init (k0 k1: U64.t) : Tot sip = {
  v0 = U64.logxor k0 0x736f6d6570736575uL;
  v1 = U64.logxor k1 0x646f72616e646f6duL;
  v2 = U64.logxor k0 0x6c7967656e657261uL;
  v3 = U64.logxor k1 0x7465646279746573uL;
  nw = 0uL;
}

inline_for_extraction
[@@"opaque_to_smt"]
let sip_absorb (s: sip) (m: U64.t) : Tot sip =
  let s1 = sip_round ({ s with v3 = U64.logxor s.v3 m }) in
  { s1 with v0 = U64.logxor s1.v0 m; nw = U64.add_mod s.nw 1uL }

inline_for_extraction
[@@"opaque_to_smt"]
let sip_fin (s: sip) : Tot U64.t =
  (* the length byte of the RFC for a message of 8 * nw bytes *)
  let m = U64.shift_left s.nw 59ul in
  let s1 = sip_round ({ s with v3 = U64.logxor s.v3 m }) in
  let s2 = { s1 with v0 = U64.logxor s1.v0 m; v2 = U64.logxor s1.v2 0xffuL } in
  let s3 = sip_round (sip_round (sip_round s2)) in
  U64.logxor (U64.logxor s3.v0 s3.v1) (U64.logxor s3.v2 s3.v3)

(* Bytes as little-endian words *)

let rec le_word (s: Seq.seq U8.t) : Tot U64.t (decreases (Seq.length s)) =
  if Seq.length s = 0
  then 0uL
  else U64.logor (FStar.Int.Cast.uint8_to_uint64 (Seq.index s 0)) (U64.shift_left (le_word (Seq.tail s)) 8ul)

let rec absorb_bytes (s: sip) (b: Seq.seq U8.t) : Tot sip (decreases (Seq.length b)) =
  if Seq.length b = 0
  then s
  else begin
    let c = if Seq.length b < 8 then Seq.length b else 8 in
    absorb_bytes (sip_absorb s (le_word (Seq.slice b 0 c))) (Seq.slice b c (Seq.length b))
  end

(* Hashing items *)

inline_for_extraction
let rh_head (s: sip) (mt: U8.t) (v: U64.t) : Tot sip =
  sip_absorb (sip_absorb s (FStar.Int.Cast.uint8_to_uint64 mt)) v

inline_for_extraction
let ehash (k0 k1: U64.t) (hk hv: U64.t) : Tot U64.t =
  sip_fin (sip_absorb (sip_absorb (sip_init k0 k1) hk) hv)

let rec rh_feed (k0 k1: U64.t) (s: sip) (x: raw_data_item) : Tot sip (decreases x) =
  match x with
  | Simple v -> rh_head s cbor_major_type_simple_value (FStar.Int.Cast.uint8_to_uint64 v)
  | Int64 ty v -> rh_head s ty v.value
  | String ty len v -> absorb_bytes (rh_head s ty len.value) v
  | Tagged tag v -> rh_feed k0 k1 (rh_head s cbor_major_type_tagged tag.value) v
  | Array len v -> rh_feed_list k0 k1 (rh_head s cbor_major_type_array len.value) v
  | Map len v -> sip_absorb (rh_head s cbor_major_type_map len.value) (msum k0 k1 v)

and rh_feed_list (k0 k1: U64.t) (s: sip) (l: list raw_data_item) : Tot sip (decreases l) =
  match l with
  | [] -> s
  | a :: q -> rh_feed_list k0 k1 (rh_feed k0 k1 s a) q

and msum (k0 k1: U64.t) (v: list (raw_data_item & raw_data_item)) : Tot U64.t (decreases v) =
  match v with
  | [] -> 0uL
  | (a, b) :: q ->
    U64.add_mod
      (ehash k0 k1 (sip_fin (rh_feed k0 k1 (sip_init k0 k1) a)) (sip_fin (rh_feed k0 k1 (sip_init k0 k1) b)))
      (msum k0 k1 q)

let rh (k0 k1: U64.t) (x: raw_data_item) : Tot U64.t =
  sip_fin (rh_feed k0 k1 (sip_init k0 k1) x)

let ent (k0 k1: U64.t) (e: (raw_data_item & raw_data_item)) : Tot U64.t =
  ehash k0 k1 (rh k0 k1 (fst e)) (rh k0 k1 (snd e))

let rec lsum (l: list U64.t) : Tot U64.t =
  match l with
  | [] -> 0uL
  | a :: q -> U64.add_mod a (lsum q)

let rec msum_eq (k0 k1: U64.t) (v: list (raw_data_item & raw_data_item)) : Lemma
  (ensures msum k0 k1 v == lsum (List.Tot.map (ent k0 k1) v))
  (decreases v)
= match v with
  | [] -> ()
  | _ :: q -> msum_eq k0 k1 q

(* Sums of hashes do not depend on the order of the entries *)

let add_mod_comm (a b: U64.t) : Lemma (U64.add_mod a b == U64.add_mod b a) = ()

let add_mod_assoc (a b c: U64.t) : Lemma
  (U64.add_mod a (U64.add_mod b c) == U64.add_mod (U64.add_mod a b) c)
= FStar.Math.Lemmas.lemma_mod_plus_distr_r (U64.v a) (U64.v b + U64.v c) (pow2 64);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v a + U64.v b) (U64.v c) (pow2 64);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (U64.v a) (U64.v b) (pow2 64);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v a) (U64.v b) (pow2 64);
  FStar.Math.Lemmas.lemma_mod_add_distr (U64.v a) (U64.v b + U64.v c) (pow2 64);
  FStar.Math.Lemmas.lemma_mod_add_distr (U64.v c) (U64.v a + U64.v b) (pow2 64)

let rec lremove (#t: eqtype) (x: t) (l: list t) : Tot (list t) =
  match l with
  | [] -> []
  | a :: q -> if a = x then q else a :: lremove x q

let rec lremove_sum (#t: eqtype) (f: t -> U64.t) (x: t) (l: list t) : Lemma
  (requires List.Tot.memP x l)
  (ensures lsum (List.Tot.map f l) == U64.add_mod (f x) (lsum (List.Tot.map f (lremove x l))))
= match l with
  | a :: q ->
    if a = x then ()
    else begin
      lremove_sum f x q;
      add_mod_assoc (f a) (f x) (lsum (List.Tot.map f (lremove x q)));
      add_mod_assoc (f x) (f a) (lsum (List.Tot.map f (lremove x q)));
      add_mod_comm (f a) (f x)
    end

let rec lremove_mem (#t: eqtype) (x: t) (l: list t) (y: t) : Lemma
  (requires List.Tot.no_repeats_p l)
  (ensures List.Tot.memP y (lremove x l) <==> (List.Tot.memP y l /\ y <> x))
= match l with
  | [] -> ()
  | a :: q -> if a = x then () else lremove_mem x q y

let rec lremove_no_repeats (#t: eqtype) (x: t) (l: list t) : Lemma
  (requires List.Tot.no_repeats_p l)
  (ensures List.Tot.no_repeats_p (lremove x l))
= match l with
  | [] -> ()
  | a :: q ->
    if a = x then ()
    else begin
      lremove_no_repeats x q;
      lremove_mem x q a
    end

let rec lsum_perm (#t: eqtype) (f: t -> U64.t) (l1 l2: list t) : Lemma
  (requires
    List.Tot.no_repeats_p l1 /\
    List.Tot.no_repeats_p l2 /\
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2))
  (ensures lsum (List.Tot.map f l1) == lsum (List.Tot.map f l2))
  (decreases l1)
= match l1 with
  | [] ->
    begin match l2 with
    | [] -> ()
    | a :: _ -> assert (List.Tot.memP a l2)
    end
  | a :: q ->
    lremove_sum f a l2;
    lremove_no_repeats a l2;
    Classical.forall_intro (Classical.move_requires (lremove_mem a l2));
    lsum_perm f q (lremove a l2)

let rec no_repeats_fst (#t1 #t2: eqtype) (l: list (t1 & t2)) : Lemma
  (requires List.Tot.no_repeats_p (List.Tot.map fst l))
  (ensures List.Tot.no_repeats_p l)
= match l with
  | [] -> ()
  | a :: q ->
    no_repeats_fst q;
    Classical.move_requires (FStar.List.Tot.Properties.memP_map_intro fst a) q

let rec noRepeats_p (#t: eqtype) (l: list t) : Lemma
  (List.Tot.noRepeats l <==> List.Tot.no_repeats_p l)
= match l with
  | [] -> ()
  | a :: q -> FStar.List.Tot.Properties.mem_memP a q; noRepeats_p q

(* The hash is invariant under canonicalization *)

let rec rh_canon (k0 k1: U64.t) (s: sip) (x: raw_data_item) : Lemma
  (ensures rh_feed k0 k1 s (canon x) == rh_feed k0 k1 s x)
  (decreases %[x; 0])
= canon_eq x;
  match x with
  | Tagged tag v -> rh_canon k0 k1 (rh_head s cbor_major_type_tagged tag.value) v
  | Array len v -> rh_canon_list k0 k1 (rh_head s cbor_major_type_array len.value) v
  | Map len v -> msum_canon k0 k1 v
  | _ -> ()

and rh_canon_list (k0 k1: U64.t) (s: sip) (l: list raw_data_item) : Lemma
  (ensures rh_feed_list k0 k1 s (List.Tot.map canon l) == rh_feed_list k0 k1 s l)
  (decreases %[l; 0])
= match l with
  | [] -> ()
  | a :: q ->
    rh_canon k0 k1 s a;
    rh_canon_list k0 k1 (rh_feed k0 k1 s a) q

and msum_canon (k0 k1: U64.t) (v: list (raw_data_item & raw_data_item)) : Lemma
  (ensures msum k0 k1 (canon_map_entries v) == msum k0 k1 v)
  (decreases %[v; 1])
= msum_map_canon k0 k1 v;
  let l = List.Tot.map (apply_on_pair canon) v in
  cbor_map_sort_failsafe_correct canon_order canon_compare l;
  if List.Tot.noRepeats (List.Tot.map fst l)
  then begin
    let l' = canon_map_entries v in
    noRepeats_p (List.Tot.map fst l);
    no_repeats_fst l;
    no_repeats_fst l';
    msum_eq k0 k1 l;
    msum_eq k0 k1 l';
    lsum_perm (ent k0 k1) l' l
  end
  else ()

and msum_map_canon (k0 k1: U64.t) (v: list (raw_data_item & raw_data_item)) : Lemma
  (ensures msum k0 k1 (List.Tot.map (apply_on_pair canon) v) == msum k0 k1 v)
  (decreases %[v; 0])
= match v with
  | [] -> ()
  | (a, b) :: q ->
    rh_canon k0 k1 (sip_init k0 k1) a;
    rh_canon k0 k1 (sip_init k0 k1) b;
    msum_map_canon k0 k1 q

let cc_hash (k0 k1: U64.t) (a b: raw_data_item) : Lemma
  (requires cc a b == 0)
  (ensures rh k0 k1 a == rh k0 k1 b)
= cbor_compare_props;
  rh_canon k0 k1 (sip_init k0 k1) a;
  rh_canon k0 k1 (sip_init k0 k1) b

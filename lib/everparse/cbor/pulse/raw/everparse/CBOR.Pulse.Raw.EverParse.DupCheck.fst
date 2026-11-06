module CBOR.Pulse.Raw.EverParse.DupCheck
#lang-pulse
open CBOR.Spec.Raw.EverParse.DupCheck
open CBOR.Pulse.Raw.EverParse.Format
open LowParse.Spec.Base
open LowParse.Pulse.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.Util

(* An offset-based, sort-based map key duplicate check over a buffer
   holding a well-formed (but not necessarily valid) CBOR raw data item,
   with map depth and map length bounds. Map keys are compared with the
   canonical order `cc` (which coincides with the basic data model
   equivalence on valid items.) Maps in keys are compared by sorting
   their entries in caller-provided scratch space, so this check
   allocates nothing. *)

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module I16 = FStar.Int16
module MS = LowParse.Pulse.MergeSort
module SP = FStar.Seq.Properties
module CB = CBOR.Pulse.Raw.Compare.Bytes
module Trade = Pulse.Lib.Trade.Util
module H = CBOR.Spec.Raw.EverParse.DupCheck.Hash

let jump_item_end (b: bytes) (o r: SZ.t) : Lemma
  (requires validator_success parse_raw_data_item o b r)
  (ensures SZ.v r == item_end b (SZ.v o))
= item_at_eq b (SZ.v o)

(* Comparing the heads of two items with the same major type *)

inline_for_extraction
let u64_cmp (x y: U64.t) : Tot (r: I16.t {
  (I16.v r < 0 <==> U64.v x < U64.v y) /\
  (I16.v r == 0 <==> U64.v x == U64.v y)
}) =
  if U64.lt x y then (-1s) else if U64.gt x y then 1s else 0s

inline_for_extraction
let u8_cmp (x y: U8.t) : Tot (r: I16.t {
  (I16.v r < 0 <==> U8.v x < U8.v y) /\
  (I16.v r == 0 <==> U8.v x == U8.v y)
}) =
  if U8.lt x y then (-1s) else if U8.gt x y then 1s else 0s

inline_for_extraction
let impl_head_cmp (a1 a2: Ghost.erased raw_data_item) (h1 h2: header) : Pure I16.t
  (requires
    h1 == get_raw_data_item_header a1 /\
    h2 == get_raw_data_item_header a2 /\
    get_major_type a1 == get_major_type a2
  )
  (ensures fun r -> MS.same_sign (I16.v r) (head_compare a1 a2))
= header_major_type a1;
  header_major_type a2;
  let mt = get_header_major_type h1 in
  if mt = cbor_major_type_simple_value
  then u8_cmp (get_simple_value a1 h1) (get_simple_value a2 h2)
  else if mt = cbor_major_type_uint64 || mt = cbor_major_type_neg_int64
  then u64_cmp (get_int64_value a1 h1).value (get_int64_value a2 h2).value
  else if mt = cbor_major_type_byte_string || mt = cbor_major_type_text_string
  then u64_cmp (get_string_length a1 h1).value (get_string_length a2 h2).value
  else if mt = cbor_major_type_tagged
  then u64_cmp (get_tagged_tag a1 h1).value (get_tagged_tag a2 h2).value
  else if mt = cbor_major_type_array
  then u64_cmp (get_array_length a1 h1).value (get_array_length a2 h2).value
  else u64_cmp (get_map_length a1 h1).value (get_map_length a2 h2).value

(* Filling a slice with the offsets of the entries of a map *)

#push-options "--z3rlimit 32"

fn fill_offsets
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (ks: S.slice SZ.t)
  (o0: SZ.t)
  (v: Ghost.erased (list (raw_data_item & raw_data_item)))
  (m: Ghost.erased nat)
  (q: Ghost.erased (list raw_data_item))
  (#s0: Ghost.erased (Seq.seq SZ.t))
requires
  pts_to b #p bB ** pts_to ks s0 ** pure (
    Seq.length s0 == List.Tot.length v /\
    items_at bB (SZ.v o0) (2 * List.Tot.length v + m) (List.Tot.append (list_of_pair_list v) q)
  )
returns o' : SZ.t
ensures exists* s . pts_to b #p bB ** pts_to ks s ** pure (
  Seq.length s == List.Tot.length v /\
  offsets_match bB s (Seq.length s) v /\
  (forall (j: nat) . j < Seq.length s ==> entry_struct bB (Seq.index s j)) /\
  items_at bB (SZ.v o') m q
)
{
  S.pts_to_len ks;
  let k = S.len ks;
  let mut pi = 0sz;
  let mut po = o0;
  fill_inv_init bB s0 (SZ.v o0) v m q;
  while (
    let i = !pi;
    SZ.lt i k
  )
  invariant exists* i o s . pts_to pi i ** pts_to po o ** pts_to ks s ** pts_to b #p bB ** pure (
    SZ.v i <= SZ.v k /\
    fill_inv bB s (SZ.v i) (SZ.v o) v m q
  )
  decreases (SZ.v k - SZ.v !pi)
  {
    let i = !pi;
    let o = !po;
    with s . assert (pts_to ks s);
    S.pts_to_len ks;
    assert (pure (SZ.v i < SZ.v k));
    fill_inv_step bB s (SZ.v i) o v m q;
    S.op_Dot_Lparen_Rparen_Less_Minus ks i o;
    let o1 = jump_raw_data_item () b o;
    jump_item_end bB o o1;
    let o2 = jump_raw_data_item () b o1;
    jump_item_end bB o1 o2;
    pi := SZ.add i 1sz;
    po := o2;
  };
  with s o . assert (pts_to ks s ** pts_to po o);
  fill_inv_end bB s (SZ.v o) v m q;
  !po
}

#pop-options

(* Comparing two byte strings of the same length within the input *)

let same_sign_cb (x y: int) : Lemma
  (requires CBOR.Pulse.Raw.Compare.Base.same_sign x y)
  (ensures MS.same_sign x y)
= ()

fn cmp_str
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (o1 o2 len: SZ.t)
requires
  pts_to b #p bB ** pure (
    SZ.v o1 + SZ.v len <= Seq.length bB /\
    SZ.v o2 + SZ.v len <= Seq.length bB
  )
returns r: I16.t
ensures
  pts_to b #p bB ** pure (
    SZ.v o1 + SZ.v len <= Seq.length bB /\
    SZ.v o2 + SZ.v len <= Seq.length bB /\
    MS.same_sign (I16.v r) (CBOR.Spec.Raw.Format.bytes_lex_compare
      (Seq.slice bB (SZ.v o1) (SZ.v o1 + SZ.v len))
      (Seq.slice bB (SZ.v o2) (SZ.v o2 + SZ.v len)))
  )
{
  S.pts_to_len b;
  S.share b;
  let s1 = Pulse.Lib.Slice.Util.subslice_trade b o1 (SZ.add o1 len);
  let s2 = Pulse.Lib.Slice.Util.subslice_trade b o2 (SZ.add o2 len);
  let r = CB.lex_compare_bytes s1 s2;
  same_sign_cb (I16.v r) (CBOR.Spec.Raw.Format.bytes_lex_compare
      (Seq.slice bB (SZ.v o1) (SZ.v o1 + SZ.v len))
      (Seq.slice bB (SZ.v o2) (SZ.v o2 + SZ.v len)));
  Trade.elim (pts_to s1 #(p /. 2.0R) (Seq.slice bB (SZ.v o1) (SZ.v (SZ.add o1 len)))) (pts_to b #(p /. 2.0R) bB);
  Trade.elim (pts_to s2 #(p /. 2.0R) (Seq.slice bB (SZ.v o2) (SZ.v (SZ.add o2 len)))) (pts_to b #(p /. 2.0R) bB);
  S.gather b;
  r
}

(* The resources of the comparison: the input and the scratch space *)

let cinv (b: S.slice U8.t) (p: perm) (bB: Ghost.erased bytes) (sc: S.slice SZ.t) : slprop =
  pts_to b #p bB ** (exists* s . pts_to sc s)

inline_for_extraction
let rec_cmp_t (b: S.slice U8.t) (p: perm) (bB: Ghost.erased bytes) (n f: Ghost.erased nat) =
  (sc: S.slice SZ.t) ->
  MS.impl_cmp_t #SZ.t (cinv b p bB sc) (cmp_pre bB n f (SZ.v (S.len sc))) (key_cmp_g bB)

(* Comparing the sorted entries of two maps, in lockstep *)

let key_cmp_g_eq (b: Ghost.erased bytes) (x y: SZ.t) : Lemma
  (Ghost.reveal (key_cmp_g b) x y == key_cmp b x y)
= ()

#push-options "--z3rlimit 64"

inline_for_extraction
fn lockstep
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (n f: Ghost.erased nat)
  (rec_cmp: rec_cmp_t b p bB n f)
  (rest: S.slice SZ.t)
  (ks1 ks2: S.slice SZ.t)
  (#s1 #s2: Ghost.erased (Seq.seq SZ.t))
requires
  cinv b p bB rest ** pts_to ks1 s1 ** pts_to ks2 s2 ** pure (
    Seq.length s1 == Seq.length s2 /\
    entries_ok bB n f s1 /\
    entries_ok bB n f s2 /\
    SZ.v (S.len rest) >= 3 * n * f
  )
returns r: I16.t
ensures
  cinv b p bB rest ** pts_to ks1 s1 ** pts_to ks2 s2 ** pure (
    Seq.length s1 == Seq.length s2 /\
    MS.same_sign (I16.v r) (cc_entries (entries_of bB s1) (entries_of bB s2))
  )
{
  S.pts_to_len ks1;
  S.pts_to_len ks2;
  let k = S.len ks1;
  let mut pi = 0sz;
  let mut pr = 0s;
  cc_entries_init bB s1 s2;
  while (
    let i = !pi;
    let r = !pr;
    (r = 0s && SZ.lt i k)
  )
  invariant exists* i r .
    cinv b p bB rest ** pts_to ks1 s1 ** pts_to ks2 s2 **
    pts_to pi i ** pts_to pr r ** pure (
      SZ.v i <= SZ.v k /\
      (I16.v r == 0 ==> cc_entries (entries_of bB s1) (entries_of bB s2) ==
        cc_entries (entries_of bB (Seq.slice s1 (SZ.v i) (SZ.v k))) (entries_of bB (Seq.slice s2 (SZ.v i) (SZ.v k)))) /\
      (I16.v r <> 0 ==> MS.same_sign (I16.v r) (cc_entries (entries_of bB s1) (entries_of bB s2)))
    )
  decreases (SZ.v k - SZ.v !pi)
  {
    let i = !pi;
    let x1 = S.op_Dot_Lparen_Rparen ks1 i;
    let x2 = S.op_Dot_Lparen_Rparen ks2 i;
    entries_ok_index bB n f s1 (SZ.v i);
    entries_ok_index bB n f s2 (SZ.v i);
    entry_pre_elim bB n f x1;
    entry_pre_elim bB n f x2;
    cc_entries_step bB s1 s2 (SZ.v i);
    key_cmp_g_eq bB x1 x2;
    let rk = rec_cmp rest x1 x2;
    if (rk = 0s) {
      unfold (cinv b p bB rest);
      items_at_step bB (SZ.v x1) 1 [item_at bB (SZ.v x1)];
      items_at_step bB (SZ.v x2) 1 [item_at bB (SZ.v x2)];
      let v1 = jump_raw_data_item () b x1;
      jump_item_end bB x1 v1;
      let v2 = jump_raw_data_item () b x2;
      jump_item_end bB x2 v2;
      fold (cinv b p bB rest);
      key_cmp_g_eq bB v1 v2;
      let rv = rec_cmp rest v1 v2;
      pr := rv;
      pi := SZ.add i 1sz;
    } else {
      pr := rk;
      pi := SZ.add i 1sz;
    }
  };
  let r = !pr;
  with i . assert (pts_to pi i);
  if (r = 0s) {
    cc_entries_end bB s1 s2;
    r
  } else {
    r
  }
}

#pop-options

(* Comparing two maps with equal heads, by sorting their entries *)

let map_entries (a: raw_data_item) : Tot (list (raw_data_item & raw_data_item)) =
  match a with
  | Map _ v -> v
  | _ -> []

let map_facts (n f: nat) (a: raw_data_item) : Lemma
  (requires Map? a /\ item_ok n f a)
  (ensures
    f >= 1 /\
    List.Tot.length (map_entries a) <= n /\
    List.Tot.for_all (item_ok n (f - 1)) (list_of_pair_list (map_entries a)) /\
    no_cc_dup (List.Tot.map fst (map_entries a)) == true
  )
= let Map len v = a in
  item_ok_map n f len v

let scratch_split (len n f f' k: nat) : Lemma
  (requires f == f' + 1 /\ len >= 3 * n * f /\ k <= n)
  (ensures 3 * k <= len /\ len - 3 * k >= 3 * n * f')
= assert (3 * n * f == 3 * n * f' + 3 * n)

let map_sort_ok
  (b: bytes) (n f: nat) (a: raw_data_item) (s0 s1: Seq.seq SZ.t) (res: bool)
: Lemma
  (requires
    Map? a /\ item_ok n f a /\
    offsets_match b s0 (Seq.length s0) (map_entries a) /\
    Seq.length s0 == List.Tot.length (map_entries a) /\
    MS.sort_post (key_cmp b) s0 s1 res
  )
  (ensures res == true)
= map_facts n f a;
  offsets_sort_ok b s0 (map_entries a)

let map_entries_ok
  (b: bytes) (n f f': nat) (a: raw_data_item) (s: Seq.seq SZ.t)
: Lemma
  (requires
    f == f' + 1 /\
    Map? a /\ item_ok n f a /\
    offsets_match b s (Seq.length s) (map_entries a) /\
    Seq.length s == List.Tot.length (map_entries a) /\
    (forall (j: nat) . j < Seq.length s ==> entry_struct b (Seq.index s j))
  )
  (ensures entries_ok b n f' s)
= map_facts n f a;
  fill_entries_ok b n f' s (map_entries a)

[@@"opaque_to_smt"]
let map_side (b: bytes) (n f: nat) (oh: nat) (a: raw_data_item) (m: nat) (q: list raw_data_item) : prop =
  Map? a /\ item_ok n f a /\
  items_at b oh (2 * List.Tot.length (map_entries a) + m) (List.Tot.append (list_of_pair_list (map_entries a)) q)

let map_side_elim (b: bytes) (n f: nat) (oh: nat) (a: raw_data_item) (m: nat) (q: list raw_data_item) : Lemma
  (requires map_side b n f oh a m q)
  (ensures
    Map? a /\ item_ok n f a /\
    items_at b oh (2 * List.Tot.length (map_entries a) + m) (List.Tot.append (list_of_pair_list (map_entries a)) q))
= reveal_opaque (`%map_side) (map_side b n f oh a m q)

let map_side_intro (b: bytes) (n f: nat) (oh: nat) (a: raw_data_item) (m: nat) (q: list raw_data_item) : Lemma
  (requires
    Map? a /\ item_ok n f a /\
    items_at b oh (2 * List.Tot.length (map_entries a) + m) (List.Tot.append (list_of_pair_list (map_entries a)) q))
  (ensures map_side b n f oh a m q)
= reveal_opaque (`%map_side) (map_side b n f oh a m q)

let map_side_facts (b: bytes) (n f: nat) (oh: nat) (a: raw_data_item) (m: nat) (q: list raw_data_item) : Lemma
  (requires map_side b n f oh a m q)
  (ensures f >= 1 /\ List.Tot.length (map_entries a) <= n)
= map_side_elim b n f oh a m q;
  map_facts n f a

let sorted_offsets (b: bytes) (n f': nat) (a: raw_data_item) (s1: Seq.seq SZ.t) : prop =
  entries_ok b n f' s1 /\
  (exists (s0: Seq.seq SZ.t) .
    offsets_match b s0 (Seq.length s0) (map_entries a) /\
    Seq.length s0 == List.Tot.length (map_entries a) /\
    MS.sort_post (key_cmp b) s0 s1 true)

let sorted_offsets_intro
  (b: bytes) (n f': nat) (a: raw_data_item) (s0 s1: Seq.seq SZ.t)
: Lemma
  (requires
    entries_ok b n f' s1 /\
    offsets_match b s0 (Seq.length s0) (map_entries a) /\
    Seq.length s0 == List.Tot.length (map_entries a) /\
    MS.sort_post (key_cmp b) s0 s1 true)
  (ensures sorted_offsets b n f' a s1)
= ()

let cc_map_sorted_items
  (b: bytes) (n f f': nat) (a1 a2: raw_data_item) (s1 s2: Seq.seq SZ.t)
  (oh1 oh2 m: nat) (q1 q2: list raw_data_item)
: Lemma
  (requires
    map_side b n f oh1 a1 m q1 /\
    map_side b n f oh2 a2 m q2 /\
    List.Tot.length (map_entries a1) == List.Tot.length (map_entries a2) /\
    sorted_offsets b n f' a1 s1 /\
    sorted_offsets b n f' a2 s2
  )
  (ensures
    Seq.length s1 == Seq.length s2 /\
    entries_ok b n f' s1 /\
    entries_ok b n f' s2 /\
    cc a1 a2 == cc_entries (entries_of b s1) (entries_of b s2)
  )
= map_side_elim b n f oh1 a1 m q1;
  map_side_elim b n f oh2 a2 m q2;
  let Map len1 v1 = a1 in
  let Map len2 v2 = a2 in
  U64.v_inj len1.value len2.value;
  eliminate exists (s01: Seq.seq SZ.t) .
    offsets_match b s01 (Seq.length s01) (map_entries a1) /\
    Seq.length s01 == List.Tot.length (map_entries a1) /\
    MS.sort_post (key_cmp b) s01 s1 true
  with eliminate exists (s02: Seq.seq SZ.t) .
    offsets_match b s02 (Seq.length s02) (map_entries a2) /\
    Seq.length s02 == List.Tot.length (map_entries a2) /\
    MS.sort_post (key_cmp b) s02 s2 true
  with cc_map_sorted b n f len1 v1 s01 s1 len2 v2 s02 s2

let key_cmp_props_g (b: Ghost.erased bytes) : Lemma
  (MS.compare_props (Ghost.reveal (key_cmp_g b)))
= key_cmp_props b

let seq_pre_cmp_pre (b: Ghost.erased bytes) (n f: Ghost.erased nat) (scl: nat) (s: Seq.seq SZ.t) : Lemma
  (requires forall x . SP.mem x s ==> cmp_pre b n f scl x)
  (ensures MS.seq_pre (Ghost.reveal (Ghost.hide (cmp_pre b n f scl))) s)
= ()

#push-options "--z3rlimit 64"

inline_for_extraction
fn fill_sort
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (n f f': Ghost.erased nat)
  (rec_cmp: rec_cmp_t b p bB n f')
  (rest: S.slice SZ.t)
  (ks tmp: S.slice SZ.t)
  (oh: SZ.t)
  (a: Ghost.erased raw_data_item)
  (m: Ghost.erased nat)
  (q: Ghost.erased (list raw_data_item))
  (#s: Ghost.erased (Seq.seq SZ.t))
  (#st: Ghost.erased (Seq.seq SZ.t))
requires
  cinv b p bB rest ** pts_to ks s ** pts_to tmp st ** pure (
    Ghost.reveal f == Ghost.reveal f' + 1 /\
    SZ.v (S.len rest) >= 3 * n * f' /\
    Seq.length s == List.Tot.length (map_entries a) /\
    Seq.length st == Seq.length s /\
    map_side bB n f (SZ.v oh) a m q
  )
returns o' : SZ.t
ensures
  cinv b p bB rest ** (exists* s1 st1 . pts_to ks s1 ** pts_to tmp st1 ** pure (
    Seq.length s1 == Seq.length s /\
    Seq.length st1 == Seq.length s /\
    sorted_offsets bB n f' a s1 /\
    items_at bB (SZ.v o') m q
  ))
{
  S.pts_to_len tmp;
  S.pts_to_len ks;
  map_side_elim bB n f (SZ.v oh) a m q;
  unfold (cinv b p bB rest);
  let o' = fill_offsets b ks oh (map_entries a) m q;
  fold (cinv b p bB rest);
  with s0 . assert (pts_to ks s0);
  map_entries_ok bB n f f' a s0;
  entries_ok_cmp_pre bB n f' (SZ.v (S.len rest)) s0;
  key_cmp_props_g bB;
  seq_pre_cmp_pre bB n f' (SZ.v (S.len rest)) s0;
  let ok = MS.sort #SZ.t #(cinv b p bB rest) #(Ghost.hide (cmp_pre bB n f' (SZ.v (S.len rest)))) #(key_cmp_g bB) (rec_cmp rest) ks tmp;
  with s1 . assert (pts_to ks s1);
  map_sort_ok bB n f a s0 s1 ok;
  entries_ok_perm bB n f' s0 s1;
  sorted_offsets_intro bB n f' a s0 s1;
  S.pts_to_len tmp;
  o'
}

#pop-options

#push-options "--z3rlimit 64"

inline_for_extraction
fn cmp_maps
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (n f f': Ghost.erased nat)
  (rec_cmp: rec_cmp_t b p bB n f')
  (sc: S.slice SZ.t)
  (k: SZ.t)
  (oh1 oh2: SZ.t)
  (a1 a2: Ghost.erased raw_data_item)
  (m: Ghost.erased nat)
  (q1 q2: Ghost.erased (list raw_data_item))
  (po1 po2: ref SZ.t)
requires
  pts_to b #p bB ** (exists* s . pts_to sc s) **
  (exists* o1 o2 . pts_to po1 o1 ** pts_to po2 o2) ** pure (
    Ghost.reveal f == Ghost.reveal f' + 1 /\
    SZ.v (S.len sc) >= 3 * n * f /\
    SZ.v k == List.Tot.length (map_entries a1) /\
    SZ.v k == List.Tot.length (map_entries a2) /\
    map_side bB n f (SZ.v oh1) a1 m q1 /\
    map_side bB n f (SZ.v oh2) a2 m q2
  )
returns r: I16.t
ensures
  pts_to b #p bB ** (exists* s . pts_to sc s) **
  (exists* o1 o2 . pts_to po1 o1 ** pts_to po2 o2 ** pure (
    items_at bB (SZ.v o1) m q1 /\
    items_at bB (SZ.v o2) m q2 /\
    MS.same_sign (I16.v r) (cc a1 a2)
  ))
{
  S.pts_to_len sc;
  map_side_facts bB n f (SZ.v oh1) a1 m q1;
  scratch_split (SZ.v (S.len sc)) n f f' (SZ.v k);
  let ks1, r1 = S.split sc k;
  S.pts_to_len r1;
  let ks2, r2 = S.split r1 k;
  S.pts_to_len r2;
  let tmp, rest = S.split r2 k;
  S.pts_to_len ks1;
  S.pts_to_len ks2;
  S.pts_to_len tmp;
  S.pts_to_len rest;
  with v1 . assert (pts_to ks1 v1);
  with v2 . assert (pts_to ks2 v2);
  with vt . assert (pts_to tmp vt);
  assert (pure (Seq.length v1 == SZ.v k));
  assert (pure (Seq.length v2 == SZ.v k));
  assert (pure (Seq.length vt == SZ.v k));
  assert (pure (SZ.v (S.len rest) == SZ.v (S.len sc) - 3 * SZ.v k));
  assert (pure (SZ.v (S.len rest) >= 3 * n * f'));
  fold (cinv b p bB rest);
  let o1 = fill_sort b n f f' rec_cmp rest ks1 tmp oh1 a1 m q1;
  let o2 = fill_sort b n f f' rec_cmp rest ks2 tmp oh2 a2 m q2;
  with s1 . assert (pts_to ks1 s1);
  with s2 . assert (pts_to ks2 s2);
  cc_map_sorted_items bB n f f' a1 a2 s1 s2 (SZ.v oh1) (SZ.v oh2) m q1 q2;
  let r = lockstep b n f' rec_cmp rest ks1 ks2;
  unfold (cinv b p bB rest);
  S.join tmp rest r2;
  S.join ks2 r2 r1;
  S.join ks1 r1 sc;
  po1 := o1;
  po2 := o2;
  r
}

#pop-options

(* One step of the comparison of two items *)

let lhd (l: list raw_data_item) : Tot raw_data_item =
  match l with
  | a :: _ -> a
  | [] -> dummy

let ltl (l: list raw_data_item) : Tot (list raw_data_item) =
  match l with
  | _ :: q -> q
  | [] -> []

let major_type_facts (a: raw_data_item) : Lemma
  ((String? a <==> (get_major_type a = cbor_major_type_byte_string || get_major_type a = cbor_major_type_text_string)) /\
   (Map? a <==> get_major_type a = cbor_major_type_map))
= ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 64"
let cmp_map_pre
  (b: bytes) (n f: nat) (x y: SZ.t) (o1 o2 c: nat) (l1 l2: list raw_data_item) (oh1 oh2: nat)
: Lemma
  (requires
    cmp_inv b n f x y o1 o2 c l1 l2 0 /\ Cons? l1 /\ Cons? l2 /\ c >= 1 /\ (
    let a1 = lhd l1 in
    let a2 = lhd l2 in
    Map? a1 /\
    get_major_type a1 == get_major_type a2 /\
    head_compare a1 a2 == 0 /\
    items_at b (oh1 + CBOR.Spec.Raw.EverParse.Items.leaf_size (get_raw_data_item_header a1)) (remaining_data_items_header (get_raw_data_item_header a1) + (c - 1)) (List.Tot.append (children a1) (ltl l1)) /\
    items_at b (oh2 + CBOR.Spec.Raw.EverParse.Items.leaf_size (get_raw_data_item_header a2)) (remaining_data_items_header (get_raw_data_item_header a2) + (c - 1)) (List.Tot.append (children a2) (ltl l2))
  ))
  (ensures (
    let a1 = lhd l1 in
    let a2 = lhd l2 in
    Map? a1 /\ Map? a2 /\
    f >= 1 /\ c >= 1 /\
    map_side b n f oh1 a1 (c - 1) (ltl l1) /\
    map_side b n f oh2 a2 (c - 1) (ltl l2) /\
    List.Tot.length (map_entries a1) == List.Tot.length (map_entries a2) /\
    U64.v (Map?.len a1).value == List.Tot.length (map_entries a1) /\
    oh1 + 2 * List.Tot.length (map_entries a1) <= Seq.length b
  ))
= let a1 :: q1 = l1 in
  let a2 :: q2 = l2 in
  assert (c >= 1);
  let c1 : nat = c - 1 in
  let k1 : nat = List.Tot.length (map_entries a1) in
  let m1 : nat = 2 * k1 + c1 in
  same_major_type a1 a2;
  cc_head a1 a2;
  item_ok_map_hd n f a1 q1;
  item_ok_map_hd n f a2 q2;
  map_layout b oh1 c a1 q1;
  map_layout b oh2 c a2 q2;
  items_at_bound b oh1 m1 (List.Tot.append (list_of_pair_list (map_entries a1)) q1);
  map_side_intro b n f oh1 a1 c1 q1;
  map_side_intro b n f oh2 a2 c1 q2
#pop-options

let cmp_map_post
  (b: bytes) (n f: nat) (x y: SZ.t) (o1 o2 c: nat) (l1 l2: list raw_data_item) (o1' o2': nat) (r: int)
: Lemma
  (requires
    cmp_inv b n f x y o1 o2 c l1 l2 0 /\ Cons? l1 /\ Cons? l2 /\ c >= 1 /\
    items_at b o1' (c - 1) (ltl l1) /\
    items_at b o2' (c - 1) (ltl l2) /\
    MS.same_sign r (cc (lhd l1) (lhd l2))
  )
  (ensures
    (r <> 0 ==> cmp_inv b n f x y o1 o2 c l1 l2 r) /\
    (r == 0 ==> (
      cmp_inv b n f x y o1' o2' (c - 1) (ltl l1) (ltl l2) 0 /\
      list_sum raw_data_item_size (ltl l1) < list_sum raw_data_item_size l1
    ))
  )
= if r <> 0
  then cmp_inv_stop b n f x y o1 o2 c l1 l2 r
  else cmp_inv_cont_map b n f x y o1 o2 c l1 l2 o1' o2'

let cmp_nonmap
  (b: bytes) (n f: nat) (x y: SZ.t) (o1 o2 c: nat) (l1 l2: list raw_data_item) (oh1 oh2: nat) (leaf: nat) (rs: int)
: Lemma
  (requires
    cmp_inv b n f x y o1 o2 c l1 l2 0 /\ Cons? l1 /\ Cons? l2 /\ (
    let a1 = lhd l1 in
    let a2 = lhd l2 in
    let h1 = get_raw_data_item_header a1 in
    let h2 = get_raw_data_item_header a2 in
    get_major_type a1 == get_major_type a2 /\
    ~ (Map? a1) /\
    head_compare a1 a2 == 0 /\
    leaf == (match a1 with String _ len _ -> U64.v len.value | _ -> 0) /\
    oh1 + CBOR.Spec.Raw.EverParse.Items.leaf_size h1 <= Seq.length b /\
    oh2 + CBOR.Spec.Raw.EverParse.Items.leaf_size h2 <= Seq.length b /\
    (String? a1 ==> Seq.slice b oh1 (oh1 + CBOR.Spec.Raw.EverParse.Items.leaf_size h1) == String?.v a1) /\
    (String? a2 ==> Seq.slice b oh2 (oh2 + CBOR.Spec.Raw.EverParse.Items.leaf_size h2) == String?.v a2) /\
    (String? a1 ==> (
      oh1 + leaf <= Seq.length b /\
      oh2 + leaf <= Seq.length b /\
      MS.same_sign rs (CBOR.Spec.Raw.Format.bytes_lex_compare (Seq.slice b oh1 (oh1 + leaf)) (Seq.slice b oh2 (oh2 + leaf))))) /\
    (~ (String? a1) ==> rs == 0) /\
    items_at b (oh1 + CBOR.Spec.Raw.EverParse.Items.leaf_size h1) (remaining_data_items_header h1 + (c - 1)) (List.Tot.append (children a1) (ltl l1)) /\
    items_at b (oh2 + CBOR.Spec.Raw.EverParse.Items.leaf_size h2) (remaining_data_items_header h2 + (c - 1)) (List.Tot.append (children a2) (ltl l2))
  ))
  (ensures (
    let a1 = lhd l1 in
    let a2 = lhd l2 in
    let h1 = get_raw_data_item_header a1 in
    let h2 = get_raw_data_item_header a2 in
    CBOR.Spec.Raw.EverParse.Items.leaf_size h1 == leaf /\
    CBOR.Spec.Raw.EverParse.Items.leaf_size h2 == leaf /\
    (rs <> 0 ==> cmp_inv b n f x y o1 o2 c l1 l2 rs) /\
    (rs == 0 ==> (
      let c' = remaining_data_items_header h1 + (c - 1) in
      oh1 + leaf + c' <= Seq.length b /\
      cmp_inv b n f x y (oh1 + leaf) (oh2 + leaf) c' (List.Tot.append (children a1) (ltl l1)) (List.Tot.append (children a2) (ltl l2)) 0 /\
      list_sum raw_data_item_size (List.Tot.append (children a1) (ltl l1)) < list_sum raw_data_item_size l1
    ))
  ))
= let a1 :: q1 = l1 in
  let a2 :: q2 = l2 in
  same_major_type a1 a2;
  cc_head a1 a2;
  leaf_size_eq a1;
  leaf_size_eq a2;
  let h1 = get_raw_data_item_header a1 in
  items_at_bound b (oh1 + CBOR.Spec.Raw.EverParse.Items.leaf_size h1) (remaining_data_items_header h1 + (c - 1)) (List.Tot.append (children a1) q1);
  if rs <> 0
  then cmp_inv_stop b n f x y o1 o2 c l1 l2 rs
  else cmp_inv_cont_nonmap b n f x y o1 o2 c l1 l2 (oh1 + leaf) (oh2 + leaf)

fn cmp_leaf
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (is_string: bool)
  (o1 o2 len: SZ.t)
requires
  pts_to b #p bB ** pure (
    is_string ==> (
      SZ.v o1 + SZ.v len <= Seq.length bB /\
      SZ.v o2 + SZ.v len <= Seq.length bB
    )
  )
returns r: I16.t
ensures
  pts_to b #p bB ** pure (
    (is_string ==> (
      SZ.v o1 + SZ.v len <= Seq.length bB /\
      SZ.v o2 + SZ.v len <= Seq.length bB /\
      MS.same_sign (I16.v r) (CBOR.Spec.Raw.Format.bytes_lex_compare
        (Seq.slice bB (SZ.v o1) (SZ.v o1 + SZ.v len))
        (Seq.slice bB (SZ.v o2) (SZ.v o2 + SZ.v len))))) /\
    (is_string == false ==> r == 0s)
  )
{
  if is_string {
    cmp_str b o1 o2 len
  } else {
    0s
  }
}

(* Comparing two items at offsets, using scratch space for maps in keys *)

let cmp_end
  (b: bytes) (n f: nat) (x y: SZ.t) (o1 o2: nat) (c: nat)
  (l1 l2: list raw_data_item) (r: I16.t)
: Lemma
  (requires cmp_inv b n f x y o1 o2 c l1 l2 (I16.v r) /\ not (r = 0s && c > 0))
  (ensures MS.same_sign (I16.v r) (key_cmp b x y))
= cmp_inv_end b n f x y o1 o2 c l1 l2 (I16.v r)

#push-options "--z3rlimit 128"

fn rec cmp_one
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (n f: Ghost.erased nat)
  (sc: S.slice SZ.t)
  (x y: SZ.t)
requires
  cinv b p bB sc ** pure (cmp_pre bB n f (SZ.v (S.len sc)) x /\ cmp_pre bB n f (SZ.v (S.len sc)) y)
returns r: I16.t
ensures
  cinv b p bB sc ** pure (MS.same_sign (I16.v r) (Ghost.reveal (key_cmp_g bB) x y))
decreases (Ghost.reveal f)
{
  unfold (cinv b p bB sc);
  S.pts_to_len b;
  cmp_inv_init bB n f (SZ.v (S.len sc)) x y;
  let mut po1 = x;
  let mut po2 = y;
  let mut pc = 1sz;
  let mut pres = 0s;
  let mut pl1 : Ghost.erased (list raw_data_item) = Ghost.hide [item_at bB (SZ.v x)];
  let mut pl2 : Ghost.erased (list raw_data_item) = Ghost.hide [item_at bB (SZ.v y)];
  while (
    let r = !pres;
    let c = !pc;
    (r = 0s && SZ.gt c 0sz)
  )
  invariant exists* o1 o2 c r (l1 l2: Ghost.erased (list raw_data_item)) .
    pts_to b #p bB ** (exists* s . pts_to sc s) **
    pts_to po1 o1 ** pts_to po2 o2 ** pts_to pc c ** pts_to pres r **
    pts_to pl1 l1 ** pts_to pl2 l2 **
    pure (
      cmp_inv bB n f x y (SZ.v o1) (SZ.v o2) (SZ.v c) l1 l2 (I16.v r)
    )
  decreases %[(if I16.v !pres = 0 then 1 else 0); list_sum raw_data_item_size (Ghost.reveal !pl1)]
  {
    let o1 = !po1;
    let o2 = !po2;
    let c = !pc;
    let l1 = !pl1;
    let l2 = !pl2;
    items_at_step bB (SZ.v o1) (SZ.v c) l1;
    items_at_step bB (SZ.v o2) (SZ.v c) l2;
    items_at_bound bB (SZ.v o1) (SZ.v c) l1;
    let oh1 = jump_header () b o1;
    let h1 = read_from_validator_success (read_header ()) b o1 oh1;
    let oh2 = jump_header () b o2;
    let h2 = read_from_validator_success (read_header ()) b o2 oh2;
    items_at_header bB (SZ.v o1) (SZ.v c) l1 h1 (SZ.v oh1);
    items_at_header bB (SZ.v o2) (SZ.v c) l2 h2 (SZ.v oh2);
    major_type_facts (lhd l1);
    major_type_facts (lhd l2);
    let mt1 = get_header_major_type h1;
    let mt2 = get_header_major_type h2;
    if (mt1 <> mt2) {
      cc_major_type_diff (lhd l1) (lhd l2);
      let r : I16.t = (if U8.lt mt1 mt2 then (-1s) else 1s);
      cmp_inv_stop bB n f x y (SZ.v o1) (SZ.v o2) (SZ.v c) l1 l2 (I16.v r);
      pres := r;
    } else {
      let hc = impl_head_cmp (Ghost.hide (lhd l1)) (Ghost.hide (lhd l2)) h1 h2;
      cc_head (lhd l1) (lhd l2);
      if (hc <> 0s) {
        cmp_inv_stop bB n f x y (SZ.v o1) (SZ.v o2) (SZ.v c) l1 l2 (I16.v hc);
        pres := hc;
      } else if (mt1 = cbor_major_type_map) {
        cmp_map_pre bB n f x y (SZ.v o1) (SZ.v o2) (SZ.v c) l1 l2 (SZ.v oh1) (SZ.v oh2);
        let k = SZ.uint64_to_sizet (get_map_length (Ghost.hide (lhd l1)) h1).value;
        let f' : Ghost.erased nat = Ghost.hide (Ghost.reveal f - 1);
        let r = cmp_maps b n f f' (cmp_one b #p #bB n f') sc k oh1 oh2 (Ghost.hide (lhd l1)) (Ghost.hide (lhd l2)) (Ghost.hide (SZ.v c - 1)) (Ghost.hide (ltl l1)) (Ghost.hide (ltl l2)) po1 po2;
        with o1' . assert (pts_to po1 o1');
        with o2' . assert (pts_to po2 o2');
        cmp_map_post bB n f x y (SZ.v o1) (SZ.v o2) (SZ.v c) l1 l2 (SZ.v o1') (SZ.v o2') (I16.v r);
        if (r <> 0s) {
          po1 := o1;
          po2 := o2;
          pres := r;
        } else {
          pc := SZ.sub c 1sz;
          pl1 := Ghost.hide (ltl l1);
          pl2 := Ghost.hide (ltl l2);
        }
      } else {
        let is_string = (mt1 = cbor_major_type_byte_string || mt1 = cbor_major_type_text_string);
        leaf_size_eq (lhd l1);
        let leaf : SZ.t = (if is_string then SZ.uint64_to_sizet (get_string_length (Ghost.hide (lhd l1)) h1).value else 0sz);
        let rs = cmp_leaf b is_string oh1 oh2 leaf;
        cmp_nonmap bB n f x y (SZ.v o1) (SZ.v o2) (SZ.v c) l1 l2 (SZ.v oh1) (SZ.v oh2) (SZ.v leaf) (I16.v rs);
        if (rs <> 0s) {
          pres := rs;
        } else {
          let rem = impl_remaining_data_items_header (Ghost.hide (S.len b)) h1;
          po1 := SZ.add oh1 leaf;
          po2 := SZ.add oh2 leaf;
          pc := SZ.add rem (SZ.sub c 1sz);
          pl1 := Ghost.hide (List.Tot.append (children (lhd l1)) (ltl l1));
          pl2 := Ghost.hide (List.Tot.append (children (lhd l2)) (ltl l2));
        }
      }
    }
  };
  with o1 o2 c l1 l2 . assert (pts_to po1 o1 ** pts_to po2 o2 ** pts_to pc c ** pts_to pl1 l1 ** pts_to pl2 l2);
  let r = !pres;
  cmp_end bB n f x y (SZ.v o1) (SZ.v o2) (SZ.v c) l1 l2 r;
  fold (cinv b p bB sc);
  r
}

#pop-options

(* Checking the map keys of a map whose entries are valid *)

let scratch_split_walk (len n f f' k: nat) : Lemma
  (requires f == f' + 1 /\ len >= 3 * n * f /\ k <= n)
  (ensures 2 * k <= len /\ len - 2 * k >= 3 * n * f')
= assert (3 * n * f == 3 * n * f' + 3 * n)

#push-options "--z3rlimit 64"

inline_for_extraction
fn sort_map_keys
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (n f': Ghost.erased nat)
  (rec_cmp: rec_cmp_t b p bB n f')
  (rest: S.slice SZ.t)
  (ks tmp: S.slice SZ.t)
  (v: Ghost.erased (list (raw_data_item & raw_data_item)))
  (#s0: Ghost.erased (Seq.seq SZ.t))
  (#st: Ghost.erased (Seq.seq SZ.t))
requires
  cinv b p bB rest ** pts_to ks s0 ** pts_to tmp st ** pure (
    SZ.v (S.len rest) >= 3 * n * f' /\
    Seq.length s0 == List.Tot.length v /\
    Seq.length st == Seq.length s0 /\
    offsets_match bB s0 (Seq.length s0) v /\
    (forall (j: nat) . j < Seq.length s0 ==> entry_struct bB (Seq.index s0 j)) /\
    List.Tot.for_all (item_ok n f') (list_of_pair_list v)
  )
returns res: bool
ensures
  cinv b p bB rest ** (exists* s1 st1 . pts_to ks s1 ** pts_to tmp st1 ** pure (
    Seq.length s1 == Seq.length s0 /\
    Seq.length st1 == Seq.length s0 /\
    res == no_cc_dup (List.Tot.map fst v)
  ))
{
  S.pts_to_len tmp;
  S.pts_to_len ks;
  fill_entries_ok bB n f' s0 v;
  entries_ok_cmp_pre bB n f' (SZ.v (S.len rest)) s0;
  key_cmp_props_g bB;
  seq_pre_cmp_pre bB n f' (SZ.v (S.len rest)) s0;
  let ok = MS.sort #SZ.t #(cinv b p bB rest) #(Ghost.hide (cmp_pre bB n f' (SZ.v (S.len rest)))) #(key_cmp_g bB) (rec_cmp rest) ks tmp;
  with s1 . assert (pts_to ks s1);
  S.pts_to_len tmp;
  if ok {
    offsets_sort_success bB s0 s1 v;
    ok
  } else {
    offsets_sort_fail bB s0 v;
    ok
  }
}

#pop-options

(* The walker over a list of items, checking all maps for duplicate keys *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 64"

let walk_step
  (b: bytes) (n f: nat) (o: nat) (c: pos) (m: nat) (lw q: list raw_data_item) (h: header) (oh: nat)
: Lemma
  (requires
    List.Tot.length lw == c /\
    items_at b o (c + m) (List.Tot.append lw q) /\
    List.Tot.for_all (item_bnd n f) lw /\
    (match parse parse_header (Seq.slice b o (Seq.length b)) with
     | Some (h', l) -> h' == h /\ oh == o + l
     | None -> False))
  (ensures (
    Cons? lw /\ (
    let a = lhd lw in
    let tl = ltl lw in
    h == get_raw_data_item_header a /\
    get_header_major_type h == get_major_type a /\
    oh + CBOR.Spec.Raw.EverParse.Items.leaf_size h <= Seq.length b /\
    CBOR.Spec.Raw.EverParse.Items.leaf_size h == (match a with String _ len _ -> U64.v len.value | _ -> 0) /\
    List.Tot.for_all (item_bnd n f) tl /\
    List.Tot.length tl == c - 1 /\
    list_sum raw_data_item_size tl < list_sum raw_data_item_size lw /\
    (Map? a ==> (
      let k = List.Tot.length (Map?.v a) in
      f >= 1 /\ k <= n /\ k == U64.v (Map?.len a).value /\
      List.Tot.length (children a) == 2 * k /\
      children a == list_of_pair_list (Map?.v a) /\
      List.Tot.for_all (item_bnd n (f - 1)) (children a) /\
      oh + 2 * k + (c - 1) + m <= Seq.length b /\
      items_end b o c == items_end b (items_end b oh (2 * k)) (c - 1) /\
      items_at b oh (2 * k + ((c - 1) + m)) (List.Tot.append (children a) (List.Tot.append tl q)))) /\
    (~ (Map? a) ==> (
      let l' = List.Tot.append (children a) tl in
      List.Tot.length l' == remaining_data_items_header h + (c - 1) /\
      oh + CBOR.Spec.Raw.EverParse.Items.leaf_size h + List.Tot.length l' + m <= Seq.length b /\
      items_at b (oh + CBOR.Spec.Raw.EverParse.Items.leaf_size h) (List.Tot.length l' + m) (List.Tot.append l' q) /\
      items_end b o c == items_end b (oh + CBOR.Spec.Raw.EverParse.Items.leaf_size h) (List.Tot.length l') /\
      List.Tot.for_all (item_bnd n f) l' /\
      check_dups lw == check_dups l' /\
      list_sum raw_data_item_size l' < list_sum raw_data_item_size lw))
  )))
= let a :: tl = lw in
  items_at_header b o (c + m) (List.Tot.append lw q) h oh;
  leaf_size_eq a;
  remaining_children_length a;
  list_sum_size_cons a tl;
  check_dups_cons a tl;
  List.Tot.append_assoc (children a) tl q;
  List.Tot.append_length (children a) tl;
  let o1 = oh + CBOR.Spec.Raw.EverParse.Items.leaf_size h in
  let r = remaining_data_items_header h in
  items_at_bound b o1 (r + (c + m - 1)) (List.Tot.append (children a) (List.Tot.append tl q));
  items_end_header b o c m (List.Tot.append lw q) h oh;
  if Map? a
  then begin
    item_bnd_map_hd n f a tl;
    children_map_length a;
    items_end_add b oh (2 * List.Tot.length (Map?.v a)) (c - 1)
  end
  else item_bnd_cons_children n f a tl

let walk_map_res (n f: nat) (a: raw_data_item) (tl: list raw_data_item) (res: bool) : Lemma
  (requires
    Map? a /\
    res == (check_dups (children a) && no_cc_dup (List.Tot.map fst (Map?.v a)))
  )
  (ensures
    (res == true ==> check_dups (a :: tl) == check_dups tl) /\
    (res == false ==> check_dups (a :: tl) == false)
  )
= children_map_length a;
  check_dups_cons a tl

let bnd_ok_list (n f: nat) (l: list raw_data_item) : Lemma
  (requires List.Tot.for_all (item_bnd n f) l /\ check_dups l == true)
  (ensures List.Tot.for_all (item_ok n f) l)
= check_dups_correct l;
  List.Tot.for_all_mem (item_bnd n f) l;
  List.Tot.for_all_mem valid_raw_data_item l;
  List.Tot.for_all_mem (item_ok n f) l

let walk_end (b: bytes) (o: nat) (m: nat) (lw q: list raw_data_item) : Lemma
  (requires List.Tot.length lw == 0 /\ items_at b o (0 + m) (List.Tot.append lw q))
  (ensures check_dups lw == true /\ items_at b o m q /\ items_end b o 0 == o)
= ()

#pop-options

(* Hashing items with a keyed hash compatible with `cc` *)

inline_for_extraction
let impl_head_value (a: Ghost.erased raw_data_item) (h: header) : Pure U64.t
  (requires h == get_raw_data_item_header a)
  (ensures fun r -> r == H.head_value a)
= header_major_type a;
  let mt = get_header_major_type h in
  (* intermediate results are let-bound to work around a Rust code
     generation issue with casts and field projections of `match`es *)
  if mt = cbor_major_type_simple_value
  then begin
    let v : U8.t = get_simple_value a h in
    FStar.Int.Cast.uint8_to_uint64 v
  end
  else if mt = cbor_major_type_uint64 || mt = cbor_major_type_neg_int64
  then begin
    let v : raw_uint64 = get_int64_value a h in
    v.value
  end
  else if mt = cbor_major_type_byte_string || mt = cbor_major_type_text_string
  then begin
    let v : raw_uint64 = get_string_length a h in
    v.value
  end
  else if mt = cbor_major_type_tagged
  then begin
    let v : raw_uint64 = get_tagged_tag a h in
    v.value
  end
  else if mt = cbor_major_type_array
  then begin
    let v : raw_uint64 = get_array_length a h in
    v.value
  end
  else begin
    let v : raw_uint64 = get_map_length a h in
    v.value
  end

fn hash_word
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (x c: SZ.t)
requires
  pts_to b #p bB ** pure (SZ.v x + SZ.v c <= Seq.length bB)
returns w: U64.t
ensures
  pts_to b #p bB ** pure (
    SZ.v x + SZ.v c <= Seq.length bB /\
    w == H.le_word (Seq.slice bB (SZ.v x) (SZ.v x + SZ.v c))
  )
{
  S.pts_to_len b;
  let mut pj = c;
  let mut pw = 0uL;
  H.le_word_nil bB (SZ.v x + SZ.v c);
  while (
    let j = !pj;
    SZ.gt j 0sz
  )
  invariant exists* j w . pts_to pj j ** pts_to pw w ** pts_to b #p bB ** pure (
    SZ.v j <= SZ.v c /\
    w == H.le_word (Seq.slice bB (SZ.v x + SZ.v j) (SZ.v x + SZ.v c))
  )
  decreases (SZ.v !pj)
  {
    let j = !pj;
    let w = !pw;
    let j' = SZ.sub j 1sz;
    let y = S.op_Dot_Lparen_Rparen b (SZ.add x j');
    H.le_word_step bB (SZ.v x + SZ.v j') (SZ.v x + SZ.v c);
    pw := U64.logor (FStar.Int.Cast.uint8_to_uint64 y) (U64.shift_left w 8ul);
    pj := j';
  };
  !pw
}

let hash_bytes_step (bB: bytes) (st0 st: H.sip) (o len i c: nat) (w: U64.t) : Lemma
  (requires
    i < len /\ o + len <= Seq.length bB /\
    c == (if len - i < 8 then len - i else 8) /\
    w == H.le_word (Seq.slice bB (o + i) (o + i + c)) /\
    H.absorb_bytes st0 (Seq.slice bB o (o + len)) == H.absorb_bytes st (Seq.slice bB (o + i) (o + len)))
  (ensures
    i + c <= len /\
    H.absorb_bytes st0 (Seq.slice bB o (o + len)) == H.absorb_bytes (H.sip_absorb st w) (Seq.slice bB (o + (i + c)) (o + len)))
= H.absorb_bytes_step st bB (o + i) (o + len)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 32"

fn hash_bytes
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (st0: H.sip)
  (o len: SZ.t)
requires
  pts_to b #p bB ** pure (SZ.v o + SZ.v len <= Seq.length bB)
returns st: H.sip
ensures
  pts_to b #p bB ** pure (
    SZ.v o + SZ.v len <= Seq.length bB /\
    st == H.absorb_bytes st0 (Seq.slice bB (SZ.v o) (SZ.v o + SZ.v len))
  )
{
  S.pts_to_len b;
  let mut pi = 0sz;
  let mut pst = st0;
  while (
    let i = !pi;
    SZ.lt i len
  )
  invariant exists* i st . pts_to pi i ** pts_to pst st ** pts_to b #p bB ** pure (
    SZ.v i <= SZ.v len /\
    H.absorb_bytes st0 (Seq.slice bB (SZ.v o) (SZ.v o + SZ.v len)) ==
      H.absorb_bytes st (Seq.slice bB (SZ.v o + SZ.v i) (SZ.v o + SZ.v len))
  )
  decreases (SZ.v len - SZ.v !pi)
  {
    let i = !pi;
    let st = !pst;
    let rem = SZ.sub len i;
    let c = (if SZ.lt rem 8sz then rem else 8sz);
    let x = SZ.add o i;
    let w = hash_word b x c;
    hash_bytes_step bB st0 st (SZ.v o) (SZ.v len) (SZ.v i) (SZ.v c) w;
    pst := H.sip_absorb st w;
    pi := SZ.add i c;
  };
  with i . assert (pts_to pi i);
  H.absorb_bytes_nil (Ghost.reveal !pst) bB (SZ.v o + SZ.v len);
  !pst
}

#pop-options

fn hash_leaf
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (is_string: bool)
  (st0: H.sip)
  (o len: SZ.t)
requires
  pts_to b #p bB ** pure (is_string ==> SZ.v o + SZ.v len <= Seq.length bB)
returns st: H.sip
ensures
  pts_to b #p bB ** pure (
    (is_string ==> (
      SZ.v o + SZ.v len <= Seq.length bB /\
      st == H.absorb_bytes st0 (Seq.slice bB (SZ.v o) (SZ.v o + SZ.v len)))) /\
    (is_string == false ==> st == st0)
  )
{
  if is_string {
    hash_bytes b st0 o len
  } else {
    st0
  }
}

let hwalk_inv
  (b: bytes) (k0 k1: U64.t) (n f: nat) (st0: H.sip) (l0: list raw_data_item) (e: nat)
  (o c m: nat) (lw q: list raw_data_item) (st: H.sip)
: prop
= List.Tot.length lw == c /\
  items_at b o (c + m) (List.Tot.append lw q) /\
  List.Tot.for_all (item_bnd n f) lw /\
  H.rh_feed_list k0 k1 st0 l0 == H.rh_feed_list k0 k1 st lw /\
  items_end b o c == e

let hash_items_pre (bB: bytes) (n f: nat) (o0 c0: nat) (l0 q: list raw_data_item) (m: nat) : prop =
  List.Tot.length l0 == c0 /\
  items_at bB o0 (c0 + m) (List.Tot.append l0 q) /\
  List.Tot.for_all (item_bnd n f) l0

let hash_items_post (bB: bytes) (k0 k1: U64.t) (st0: H.sip) (o0 c0: nat) (l0 q: list raw_data_item) (m: nat) (st: H.sip) (o: nat) : prop =
  st == H.rh_feed_list k0 k1 st0 l0 /\
  items_at bB o m q /\
  o == items_end bB o0 c0

#push-options "--fuel 2 --ifuel 1 --z3rlimit 64"

let hash_step_nonmap
  (b: bytes) (k0 k1: U64.t) (n f: nat) (st0: H.sip) (l0: list raw_data_item) (e: nat)
  (o: nat) (c: pos) (m: nat) (lw q: list raw_data_item) (st: H.sip) (h: header) (oh: nat) (st1: H.sip)
: Lemma
  (requires
    hwalk_inv b k0 k1 n f st0 l0 e o c m lw q st /\
    (match parse parse_header (Seq.slice b o (Seq.length b)) with
     | Some (h', l) -> h' == h /\ oh == o + l
     | None -> False) /\
    Cons? lw /\ ~ (Map? (lhd lw)) /\
    oh + CBOR.Spec.Raw.EverParse.Items.leaf_size h <= Seq.length b /\
    (String? (lhd lw) ==> st1 == H.absorb_bytes (H.rh_head st (get_major_type (lhd lw)) (H.head_value (lhd lw))) (Seq.slice b oh (oh + CBOR.Spec.Raw.EverParse.Items.leaf_size h))) /\
    (~ (String? (lhd lw)) ==> st1 == H.rh_head st (get_major_type (lhd lw)) (H.head_value (lhd lw))))
  (ensures (
    let a = lhd lw in
    let l' = List.Tot.append (children a) (ltl lw) in
    List.Tot.length l' == remaining_data_items_header h + (c - 1) /\
    hwalk_inv b k0 k1 n f st0 l0 e (oh + CBOR.Spec.Raw.EverParse.Items.leaf_size h) (List.Tot.length l') m l' q st1 /\
    list_sum raw_data_item_size l' < list_sum raw_data_item_size lw))
= walk_step b n f o c m lw q h oh;
  items_at_header b o (c + m) (List.Tot.append lw q) h oh;
  H.rh_step_nonmap k0 k1 st (lhd lw) (ltl lw)

let hash_step_map
  (b: bytes) (k0 k1: U64.t) (n f: nat) (st0: H.sip) (l0: list raw_data_item) (e: nat)
  (o: nat) (c: pos) (m: nat) (lw q: list raw_data_item) (st: H.sip) (h: header) (oh: nat)
  (e': nat) (acc: U64.t)
: Lemma
  (requires
    hwalk_inv b k0 k1 n f st0 l0 e o c m lw q st /\
    (match parse parse_header (Seq.slice b o (Seq.length b)) with
     | Some (h', l) -> h' == h /\ oh == o + l
     | None -> False) /\
    Cons? lw /\ Map? (lhd lw) /\
    items_at b e' ((c - 1) + m) (List.Tot.append (ltl lw) q) /\
    e' == items_end b oh (2 * List.Tot.length (Map?.v (lhd lw))) /\
    H.msum k0 k1 (Map?.v (lhd lw)) == acc)
  (ensures
    hwalk_inv b k0 k1 n f st0 l0 e e' (c - 1) m (ltl lw) q
      (H.sip_absorb (H.rh_head st cbor_major_type_map (H.head_value (lhd lw))) acc) /\
    list_sum raw_data_item_size (ltl lw) < list_sum raw_data_item_size lw)
= walk_step b n f o c m lw q h oh;
  H.rh_step_map k0 k1 st (lhd lw) (ltl lw)

let hash_end
  (b: bytes) (k0 k1: U64.t) (n f: nat) (st0: H.sip) (o0 c0: nat) (l0: list raw_data_item)
  (o: nat) (m: nat) (lw q: list raw_data_item) (st: H.sip)
: Lemma
  (requires hwalk_inv b k0 k1 n f st0 l0 (items_end b o0 c0) o 0 m lw q st)
  (ensures hash_items_post b k0 k1 st0 o0 c0 l0 q m st o)
= ()

let hash_init
  (b: bytes) (k0 k1: U64.t) (n f: nat) (st0: H.sip) (o0 c0: nat) (l0 q: list raw_data_item) (m: nat)
: Lemma
  (requires hash_items_pre b n f o0 c0 l0 q m)
  (ensures hwalk_inv b k0 k1 n f st0 l0 (items_end b o0 c0) o0 c0 m l0 q st0)
= ()

#pop-options

#push-options "--z3rlimit 128"

fn rec hash_items
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (k0 k1: U64.t)
  (n f: Ghost.erased nat)
  (st0: H.sip)
  (o0 c0: SZ.t)
  (l0 q: Ghost.erased (list raw_data_item))
  (m: Ghost.erased nat)
  (pout: ref SZ.t)
requires
  pts_to b #p bB ** (exists* o . pts_to pout o) **
    pure (hash_items_pre bB n f (SZ.v o0) (SZ.v c0) l0 q m)
returns st: H.sip
ensures
  pts_to b #p bB ** (exists* o . pts_to pout o **
    pure (hash_items_post bB k0 k1 st0 (SZ.v o0) (SZ.v c0) l0 q m st (SZ.v o)))
decreases (Ghost.reveal f)
{
  S.pts_to_len b;
  hash_init bB k0 k1 n f st0 (SZ.v o0) (SZ.v c0) l0 q m;
  let mut po = o0;
  let mut pc = c0;
  let mut pst = st0;
  let mut pl : Ghost.erased (list raw_data_item) = l0;
  while (
    let c = !pc;
    SZ.gt c 0sz
  )
  invariant exists* o c st (lw: Ghost.erased (list raw_data_item)) .
    pts_to b #p bB ** (exists* o . pts_to pout o) **
    pts_to po o ** pts_to pc c ** pts_to pst st ** pts_to pl lw **
    pure (hwalk_inv bB k0 k1 n f st0 l0 (items_end bB (SZ.v o0) (SZ.v c0)) (SZ.v o) (SZ.v c) m lw q st)
  decreases (list_sum raw_data_item_size (Ghost.reveal !pl))
  {
    let o = !po;
    let c = !pc;
    let st = !pst;
    let lw = !pl;
    items_at_step bB (SZ.v o) (SZ.v c + m) (List.Tot.append lw q);
    let oh = jump_header () b o;
    let h = read_from_validator_success (read_header ()) b o oh;
    walk_step bB n f (SZ.v o) (SZ.v c) m lw q h (SZ.v oh);
    major_type_facts (lhd lw);
    let mt = get_header_major_type h;
    let hval = impl_head_value (Ghost.hide (lhd lw)) h;
    let st1 = H.rh_head st mt hval;
    if (mt = cbor_major_type_map) {
      let k = SZ.uint64_to_sizet (get_map_length (Ghost.hide (lhd lw)) h).value;
      let f' : Ghost.erased nat = Ghost.hide (Ghost.reveal f - 1);
      let v : Ghost.erased (list (raw_data_item & raw_data_item)) = Ghost.hide (Map?.v (lhd lw));
      let m' : Ghost.erased nat = Ghost.hide (SZ.v c - 1 + m);
      let q' : Ghost.erased (list raw_data_item) = Ghost.hide (List.Tot.append (ltl lw) q);
      assert (pure (SZ.v k == List.Tot.length v));
      assert (pure (List.Tot.for_all (item_bnd n f') (list_of_pair_list v)));
      H.hent_init bB k0 k1 (SZ.v oh) v m' q';
      let mut pi = 0sz;
      let mut pe = oh;
      let mut pacc = 0uL;
      while (
        let i = !pi;
        SZ.lt i k
      )
      invariant exists* i e acc .
        pts_to pi i ** pts_to pe e ** pts_to pacc acc **
        pts_to b #p bB ** (exists* o . pts_to pout o) **
        pure (SZ.v i <= SZ.v k /\ H.hent_inv bB k0 k1 (SZ.v oh) v m' q' (SZ.v i) (SZ.v e) acc)
      decreases (SZ.v k - SZ.v !pi)
      {
        let i = !pi;
        let e = !pe;
        let acc = !pacc;
        H.hent_pre bB k0 k1 n f' (SZ.v oh) v m' q' (SZ.v i) (SZ.v e) acc;
        let sk = hash_items b k0 k1 n f' (H.sip_init k0 k1) e 1sz
          (Ghost.hide [fst (List.Tot.index v (SZ.v i))])
          (Ghost.hide (List.Tot.append [snd (List.Tot.index v (SZ.v i))] (H.hent_qv v (SZ.v i) q')))
          (Ghost.hide (1 + H.hent_mk v (SZ.v i) m'))
          pout;
        let o1 = !pout;
        let sv = hash_items b k0 k1 n f' (H.sip_init k0 k1) o1 1sz
          (Ghost.hide [snd (List.Tot.index v (SZ.v i))])
          (H.hent_qv v (SZ.v i) q')
          (Ghost.hide (H.hent_mk v (SZ.v i) m'))
          pout;
        let o2 = !pout;
        H.hent_step bB k0 k1 (SZ.v oh) v m' q' (SZ.v i) (SZ.v e) acc (SZ.v o1) (SZ.v o2) sk sv;
        pacc := U64.add_mod acc (H.ehash k0 k1 (H.sip_fin sk) (H.sip_fin sv));
        pe := o2;
        pi := SZ.add i 1sz;
      };
      with i e acc . assert (pts_to pi i ** pts_to pe e ** pts_to pacc acc);
      H.hent_end bB k0 k1 (SZ.v oh) v m' q' (SZ.v e) acc;
      hash_step_map bB k0 k1 n f st0 l0 (items_end bB (SZ.v o0) (SZ.v c0)) (SZ.v o) (SZ.v c) m lw q st h (SZ.v oh) (SZ.v e) acc;
      let e = !pe;
      let acc = !pacc;
      pst := H.sip_absorb st1 acc;
      po := e;
      pc := SZ.sub c 1sz;
      pl := Ghost.hide (ltl lw);
    } else {
      let is_string = (mt = cbor_major_type_byte_string || mt = cbor_major_type_text_string);
      let leaf : SZ.t = (if is_string then SZ.uint64_to_sizet (get_string_length (Ghost.hide (lhd lw)) h).value else 0sz);
      let st2 = hash_leaf b is_string st1 oh leaf;
      hash_step_nonmap bB k0 k1 n f st0 l0 (items_end bB (SZ.v o0) (SZ.v c0)) (SZ.v o) (SZ.v c) m lw q st h (SZ.v oh) st2;
      let rem = impl_remaining_data_items_header (Ghost.hide (S.len b)) h;
      pst := st2;
      po := SZ.add oh leaf;
      pc := SZ.add rem (SZ.sub c 1sz);
      pl := Ghost.hide (List.Tot.append (children (lhd lw)) (ltl lw));
    }
  };
  with o c st lw . assert (pts_to po o ** pts_to pc c ** pts_to pst st ** pts_to pl lw);
  hash_end bB k0 k1 n f st0 (SZ.v o0) (SZ.v c0) l0 (SZ.v o) m lw q st;
  let o = !po;
  pout := o;
  !pst
}

#pop-options

(* Sorting the keys of a map by hash first *)

let hcinv
  (b: S.slice U8.t) (p: perm) (bB: Ghost.erased bytes) (n f: Ghost.erased nat)
  (rest ks: S.slice SZ.t) (sks: Ghost.erased (Seq.seq SZ.t))
  (hv: S.slice U64.t) (shv: Ghost.erased (Seq.seq U64.t))
: slprop
= cinv b p bB rest ** pts_to ks sks ** pts_to hv shv ** pure (
    Seq.length shv == Seq.length sks /\
    (forall (j: nat) . j < Seq.length sks ==> cmp_pre bB n f (SZ.v (S.len rest)) (Seq.index sks j))
  )

inline_for_extraction
fn hcmp
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (n f: Ghost.erased nat)
  (rec_cmp: rec_cmp_t b p bB n f)
  (rest ks: S.slice SZ.t) (hv: S.slice U64.t)
  (sks: Ghost.erased (Seq.seq SZ.t)) (shv: Ghost.erased (Seq.seq U64.t))
  (i j: SZ.t)
requires
  hcinv b p bB n f rest ks sks hv shv ** pure (H.ipre (Seq.length sks) i /\ H.ipre (Seq.length sks) j)
returns r: I16.t
ensures
  hcinv b p bB n f rest ks sks hv shv ** pure (MS.same_sign (I16.v r) (Ghost.reveal (H.icmp_g bB sks shv) i j))
{
  unfold (hcinv b p bB n f rest ks sks hv shv);
  S.pts_to_len hv;
  S.pts_to_len ks;
  let hi = S.op_Dot_Lparen_Rparen hv i;
  let hj = S.op_Dot_Lparen_Rparen hv j;
  if (U64.lt hi hj) {
    fold (hcinv b p bB n f rest ks sks hv shv);
    (-1s)
  } else if (U64.lt hj hi) {
    fold (hcinv b p bB n f rest ks sks hv shv);
    1s
  } else {
    let xi = S.op_Dot_Lparen_Rparen ks i;
    let xj = S.op_Dot_Lparen_Rparen ks j;
    key_cmp_g_eq bB xi xj;
    let r = rec_cmp rest xi xj;
    fold (hcinv b p bB n f rest ks sks hv shv);
    r
  }
}

let entries_cmp_pre_index (b: Ghost.erased bytes) (n f: Ghost.erased nat) (scl: nat) (s: Seq.seq SZ.t) : Lemma
  (requires entries_ok b n f s /\ scl >= 3 * n * f)
  (ensures forall (j: nat) . j < Seq.length s ==> cmp_pre b n f scl (Seq.index s j))
= let prf (j: nat) : Lemma
    (requires j < Seq.length s)
    (ensures j < Seq.length s /\ cmp_pre b n f scl (Seq.index s j))
  = entries_ok_index b n f s j;
    entry_pre_cmp_pre b n f scl (Seq.index s j)
  in
  Classical.forall_intro (Classical.move_requires prf)

let hash_key_pre (bB: bytes) (n f: nat) (x: SZ.t) : Lemma
  (requires items_at bB (SZ.v x) 1 [item_at bB (SZ.v x)] /\ item_ok n f (item_at bB (SZ.v x)))
  (ensures hash_items_pre bB n f (SZ.v x) 1 [item_at bB (SZ.v x)] [] 0)
= items_at_append_nil bB (SZ.v x) 1 [item_at bB (SZ.v x)]

let hash_key_post (bB: bytes) (k0 k1: U64.t) (x: SZ.t) (st: H.sip) (o: nat) : Lemma
  (requires hash_items_post bB k0 k1 (H.sip_init k0 k1) (SZ.v x) 1 [item_at bB (SZ.v x)] [] 0 st o)
  (ensures H.sip_fin st == H.key_hash bB k0 k1 x)
= H.rh_single k0 k1 (item_at bB (SZ.v x));
  H.key_hash_eq bB k0 k1 x

let iota_seq_pre (s: Seq.seq SZ.t) (k: nat) : Lemma
  (requires H.is_iota s (Seq.length s) /\ Seq.length s == k)
  (ensures MS.seq_pre (H.ipre k) s /\ MS.seq_distinct s)
= H.iota_pre s

#push-options "--z3rlimit 64"

inline_for_extraction
fn hash_map_keys
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (n f': Ghost.erased nat)
  (rec_cmp: rec_cmp_t b p bB n f')
  (rest: S.slice SZ.t)
  (k0 k1: U64.t)
  (ks tmp: S.slice SZ.t)
  (hv: S.slice U64.t)
  (idx: S.slice SZ.t)
  (v: Ghost.erased (list (raw_data_item & raw_data_item)))
  (#s0: Ghost.erased (Seq.seq SZ.t))
  (#st: Ghost.erased (Seq.seq SZ.t))
  (#shv0: Ghost.erased (Seq.seq U64.t))
  (#sidx0: Ghost.erased (Seq.seq SZ.t))
requires
  cinv b p bB rest ** pts_to ks s0 ** pts_to tmp st ** pts_to hv shv0 ** pts_to idx sidx0 ** pure (
    SZ.v (S.len rest) >= 3 * n * f' /\
    Seq.length s0 == List.Tot.length v /\
    Seq.length st == Seq.length s0 /\
    Seq.length shv0 == Seq.length s0 /\
    Seq.length sidx0 == Seq.length s0 /\
    offsets_match bB s0 (Seq.length s0) v /\
    (forall (j: nat) . j < Seq.length s0 ==> entry_struct bB (Seq.index s0 j)) /\
    List.Tot.for_all (item_ok n f') (list_of_pair_list v)
  )
returns res: bool
ensures
  cinv b p bB rest ** pts_to ks s0 ** (exists* st1 shv1 sidx1 .
    pts_to tmp st1 ** pts_to hv shv1 ** pts_to idx sidx1 ** pure (
    Seq.length st1 == Seq.length s0 /\
    Seq.length shv1 == Seq.length s0 /\
    Seq.length sidx1 == Seq.length s0
  )) ** pure (
    res == no_cc_dup (List.Tot.map fst v)
  )
{
  S.pts_to_len ks;
  S.pts_to_len tmp;
  S.pts_to_len hv;
  S.pts_to_len idx;
  fill_entries_ok bB n f' s0 v;
  entries_cmp_pre_index bB n f' (SZ.v (S.len rest)) s0;
  let k = S.len ks;
  let mut pi = 0sz;
  let mut po = 0sz;
  while (
    let i = !pi;
    SZ.lt i k
  )
  invariant exists* i shv sidx .
    pts_to pi i ** pts_to hv shv ** pts_to idx sidx ** (exists* o . pts_to po o) **
    cinv b p bB rest ** pts_to ks s0 ** pure (
    SZ.v i <= SZ.v k /\
    H.hv_ok bB k0 k1 s0 shv (SZ.v i) /\
    Seq.length sidx == SZ.v k /\
    H.is_iota sidx (SZ.v i)
  )
  decreases (SZ.v k - SZ.v !pi)
  {
    let i = !pi;
    S.pts_to_len hv;
    S.pts_to_len idx;
    let x = S.op_Dot_Lparen_Rparen ks i;
    entries_ok_index bB n f' s0 (SZ.v i);
    entry_pre_elim bB n f' x;
    hash_key_pre bB n f' x;
    unfold (cinv b p bB rest);
    let sh = hash_items b k0 k1 n f' (H.sip_init k0 k1) x 1sz
      (Ghost.hide [item_at bB (SZ.v x)]) (Ghost.hide []) (Ghost.hide 0) po;
    fold (cinv b p bB rest);
    with o . assert (pts_to po o);
    hash_key_post bB k0 k1 x sh (SZ.v o);
    let h = H.sip_fin sh;
    with shv . assert (pts_to hv shv);
    with sidx . assert (pts_to idx sidx);
    H.hv_ok_step bB k0 k1 s0 shv (SZ.v i) h;
    H.is_iota_step sidx (SZ.v i) i;
    S.op_Dot_Lparen_Rparen_Less_Minus hv i h;
    S.op_Dot_Lparen_Rparen_Less_Minus idx i i;
    pi := SZ.add i 1sz;
  };
  with shv . assert (pts_to hv shv);
  with sidx . assert (pts_to idx sidx);
  H.icmp_props bB s0 shv;
  iota_seq_pre sidx (Seq.length s0);
  fold (hcinv b p bB n f' rest ks s0 hv shv);
  let ok = MS.sort #SZ.t #(hcinv b p bB n f' rest ks s0 hv shv) #(Ghost.hide (H.ipre (Seq.length s0))) #(H.icmp_g bB s0 shv)
    (hcmp b n f' rec_cmp rest ks hv s0 shv) idx tmp;
  unfold (hcinv b p bB n f' rest ks s0 hv shv);
  with s1 . assert (pts_to idx s1);
  S.pts_to_len idx;
  S.pts_to_len tmp;
  H.hash_sort_result bB k0 k1 s0 shv sidx s1 v ok;
  ok
}

#pop-options

let walk_inv
  (b: bytes) (n f: nat) (l0: list raw_data_item) (e: nat) (o c m: nat) (lw q: list raw_data_item) (res: bool)
: prop
= List.Tot.length lw == c /\
  items_at b o (c + m) (List.Tot.append lw q) /\
  List.Tot.for_all (item_bnd n f) lw /\
  (res == true ==> (check_dups l0 == check_dups lw /\ items_end b o c == e)) /\
  (res == false ==> check_dups l0 == false)

let check_items_pre (bB: bytes) (n f: nat) (sc_len: nat) (o0 c0: nat) (l0 q: list raw_data_item) (m: nat) : prop =
  sc_len >= 3 * n * f /\
  List.Tot.length l0 == c0 /\
  items_at bB o0 (c0 + m) (List.Tot.append l0 q) /\
  List.Tot.for_all (item_bnd n f) l0

let check_items_post (bB: bytes) (o0 c0: nat) (l0 q: list raw_data_item) (m: nat) (res: bool) (o: nat) : prop =
  res == check_dups l0 /\
  (res == true ==> (items_at bB o m q /\ o == items_end bB o0 c0))

let mrest (len i m: nat) : nat =
  if i < len then 2 * (len - (i + 1)) + m else m

let mrest_eq (len i m: nat) : Lemma
  (requires i < len)
  (ensures mrest len i m == 2 * (len - (i + 1)) + m)
= ()

[@@"opaque_to_smt"]
let ment_inv_o
  (b: bytes) (s: Seq.seq SZ.t) (i o oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item) (res: bool)
: prop
= ment_inv b s i o oh v m q res

let ment_init_o
  (b: bytes) (s: Seq.seq SZ.t) (oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
: Lemma
  (requires
    Seq.length s == List.Tot.length v /\
    items_at b oh (2 * List.Tot.length v + m) (List.Tot.append (list_of_pair_list v) q))
  (ensures ment_inv_o b s 0 oh oh v m q true)
= ment_init b s oh v m q;
  reveal_opaque (`%ment_inv_o) ment_inv_o

let ment_inv_o_len
  (b: bytes) (s: Seq.seq SZ.t) (i o oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item) (res: bool)
: Lemma
  (requires ment_inv_o b s i o oh v m q res)
  (ensures Seq.length s == List.Tot.length v)
= reveal_opaque (`%ment_inv_o) ment_inv_o

let ment_step_ok_o
  (b: bytes) (s: Seq.seq SZ.t) (i: nat) (x: SZ.t) (o' oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item) (res: bool)
: Lemma
  (requires (
    i < List.Tot.length v /\
    Seq.length s == List.Tot.length v /\ (
    let e = List.Tot.index v i in
    ment_inv_o b s i (SZ.v x) oh v m q true /\
    check_items_post b (SZ.v x) 2 [fst e; snd e] (List.Tot.append (list_of_pair_list (ldrop (i + 1) v)) q) (mrest (List.Tot.length v) i m) res o')))
  (ensures
    (res == true ==> ment_inv_o b (Seq.upd s i x) (i + 1) o' oh v m q true) /\
    (res == false ==> ment_inv_o b s i (SZ.v x) oh v m q false))
= reveal_opaque (`%ment_inv_o) ment_inv_o;
  if res
  then ment_step_ok b s i x o' oh v m q
  else ment_step_fail b s i (SZ.v x) oh v m q

let ci_pre_entry
  (bB: bytes) (n f: nat) (sclen: nat) (s1: Seq.seq SZ.t) (i e oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
: Lemma
  (requires
    sclen >= 3 * n * f /\
    i < List.Tot.length v /\
    ment_inv_o bB s1 i e oh v m q true /\
    List.Tot.for_all (item_bnd n f) (list_of_pair_list v))
  (ensures
    check_items_pre bB n f sclen e 2
      [fst (List.Tot.index v i); snd (List.Tot.index v i)]
      (List.Tot.append (list_of_pair_list (ldrop (i + 1) v)) q)
      (mrest (List.Tot.length v) i m))
= reveal_opaque (`%ment_inv_o) ment_inv_o;
  ment_pre bB n f s1 i e oh v m q;
  mrest_eq (List.Tot.length v) i m

let ment_measure (k i: nat) (r: bool) : nat =
  if r && i < k then k - i else 0

#push-options "--z3rlimit 128"

(* Sorting the keys of a map after walking its entries *)

inline_for_extraction
fn walk_map_finish
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (n f': Ghost.erased nat)
  (rec_cmp: rec_cmp_t b p bB n f')
  (rest: S.slice SZ.t)
  (k0 k1: U64.t)
  (hv: S.slice U64.t)
  (idx: S.slice SZ.t)
  (ks tmp: S.slice SZ.t)
  (oh: SZ.t)
  (v: Ghost.erased (list (raw_data_item & raw_data_item)))
  (m: Ghost.erased nat)
  (q: Ghost.erased (list raw_data_item))
  (pout: ref SZ.t)
  (r: bool)
  (i o: SZ.t)
  (#s1: Ghost.erased (Seq.seq SZ.t))
  (#st: Ghost.erased (Seq.seq SZ.t))
requires
  pts_to b #p bB ** pts_to ks s1 ** pts_to tmp st ** (exists* s . pts_to rest s) ** (exists* o . pts_to pout o) **
  (exists* s . pts_to hv s) ** (exists* s . pts_to idx s) ** pure (
    SZ.v (S.len rest) >= 3 * n * f' /\
    Seq.length st == Seq.length s1 /\
    ment_inv_o bB s1 (SZ.v i) (SZ.v o) (SZ.v oh) v m q r /\
    (r == true ==> SZ.v i == List.Tot.length v) /\
    List.Tot.for_all (item_bnd n f') (list_of_pair_list v)
  )
returns res: bool
ensures
  pts_to b #p bB ** (exists* s . pts_to rest s) ** (exists* s . pts_to hv s) ** (exists* s . pts_to idx s) ** (exists* s2 st2 . pts_to ks s2 ** pts_to tmp st2 ** pure (
    Seq.length s2 == Seq.length s1 /\
    Seq.length st2 == Seq.length s1
  )) ** (exists* o' . pts_to pout o' ** pure (
    res == (check_dups (list_of_pair_list v) && no_cc_dup (List.Tot.map fst v)) /\
    (res == true ==> (items_at bB (SZ.v o') m q /\ SZ.v o' == items_end bB (SZ.v oh) (2 * List.Tot.length v)))
  ))
{
  reveal_opaque (`%ment_inv_o) ment_inv_o;
  if r {
    ment_end bB s1 (SZ.v o) (SZ.v oh) v m q;
    bnd_ok_list n f' (list_of_pair_list v);
    pout := o;
    fold (cinv b p bB rest);
    S.pts_to_len ks;
    S.pts_to_len tmp;
    let k = S.len ks;
    with shv . assert (pts_to hv shv);
    with sidx . assert (pts_to idx sidx);
    S.pts_to_len hv;
    S.pts_to_len idx;
    if (SZ.lte k (S.len hv) && SZ.lte k (S.len idx)) {
      let hv1, hv2 = S.split hv k;
      let idx1, idx2 = S.split idx k;
      S.pts_to_len hv1;
      S.pts_to_len idx1;
      let ok = hash_map_keys b n f' rec_cmp rest k0 k1 ks tmp hv1 idx1 v;
      S.join hv1 hv2 hv;
      S.join idx1 idx2 idx;
      unfold (cinv b p bB rest);
      ok
    } else {
      let ok = sort_map_keys b n f' rec_cmp rest ks tmp v;
      unfold (cinv b p bB rest);
      ok
    }
  } else {
    false
  }
}

#pop-options

#push-options "--z3rlimit 128"

fn rec check_items
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (n f: Ghost.erased nat)
  (sc: S.slice SZ.t)
  (k0 k1: U64.t)
  (hv: S.slice U64.t)
  (idx: S.slice SZ.t)
  (o0 c0: SZ.t)
  (l0 q: Ghost.erased (list raw_data_item))
  (m: Ghost.erased nat)
  (pout: ref SZ.t)
requires
  pts_to b #p bB ** (exists* s . pts_to sc s) ** (exists* o . pts_to pout o) **
    (exists* s . pts_to hv s) ** (exists* s . pts_to idx s) **
    pure (check_items_pre bB n f (SZ.v (S.len sc)) (SZ.v o0) (SZ.v c0) l0 q m)
returns res: bool
ensures
  pts_to b #p bB ** (exists* s . pts_to sc s) **
  (exists* s . pts_to hv s) ** (exists* s . pts_to idx s) ** (exists* o . pts_to pout o **
    pure (check_items_post bB (SZ.v o0) (SZ.v c0) l0 q m res (SZ.v o)))
decreases (Ghost.reveal f)
{
  S.pts_to_len b;
  let mut po = o0;
  let mut pc = c0;
  let mut pres = true;
  let mut pl : Ghost.erased (list raw_data_item) = l0;
  while (
    let r = !pres;
    let c = !pc;
    (r && SZ.gt c 0sz)
  )
  invariant exists* o c r (lw: Ghost.erased (list raw_data_item)) .
    pts_to b #p bB ** (exists* s . pts_to sc s) ** (exists* o . pts_to pout o) **
    (exists* s . pts_to hv s) ** (exists* s . pts_to idx s) **
    pts_to po o ** pts_to pc c ** pts_to pres r ** pts_to pl lw **
    pure (walk_inv bB n f l0 (items_end bB (SZ.v o0) (SZ.v c0)) (SZ.v o) (SZ.v c) m lw q r)
  decreases %[(if !pres then 1 else 0); list_sum raw_data_item_size (Ghost.reveal !pl)]
  {
    let o = !po;
    let c = !pc;
    let lw = !pl;
    items_at_step bB (SZ.v o) (SZ.v c + m) (List.Tot.append lw q);
    let oh = jump_header () b o;
    let h = read_from_validator_success (read_header ()) b o oh;
    walk_step bB n f (SZ.v o) (SZ.v c) m lw q h (SZ.v oh);
    major_type_facts (lhd lw);
    let mt = get_header_major_type h;
    if (mt = cbor_major_type_map) {
      let k = SZ.uint64_to_sizet (get_map_length (Ghost.hide (lhd lw)) h).value;
      let f' : Ghost.erased nat = Ghost.hide (Ghost.reveal f - 1);
      with s . assert (pts_to sc s);
      S.pts_to_len sc;
      scratch_split_walk (SZ.v (S.len sc)) n f f' (SZ.v k);
      let ks, r1 = S.split sc k;
      S.pts_to_len r1;
      let tmp, rest = S.split r1 k;
      S.pts_to_len ks;
      S.pts_to_len tmp;
      S.pts_to_len rest;
      with vk . assert (pts_to ks vk);
      let v : Ghost.erased (list (raw_data_item & raw_data_item)) = Ghost.hide (Map?.v (lhd lw));
      let m' : Ghost.erased nat = Ghost.hide (SZ.v c - 1 + m);
      let q' : Ghost.erased (list raw_data_item) = Ghost.hide (List.Tot.append (ltl lw) q);
      assert (pure (SZ.v (S.len rest) >= 3 * n * f'));
      assert (pure (SZ.v k == List.Tot.length v));
      assert (pure (List.Tot.for_all (item_bnd n f') (list_of_pair_list v)));
      with vt . assert (pts_to tmp vt);
      assert (pure (Seq.length vt == SZ.v k));
      assert (pure (Seq.length vk == SZ.v k));
      ment_init_o bB vk (SZ.v oh) v m' q';
      let mut pi = 0sz;
      let mut pe = oh;
      let mut pr = true;
      while (
        let r = !pr;
        let i = !pi;
        (r && SZ.lt i k)
      )
      invariant exists* i e r s1 .
        pts_to pi i ** pts_to pe e ** pts_to pr r ** pts_to ks s1 **
        pts_to b #p bB ** (exists* s . pts_to rest s) ** (exists* o . pts_to pout o) **
        (exists* s . pts_to hv s) ** (exists* s . pts_to idx s) **
        pure (SZ.v i <= SZ.v k /\ ment_inv_o bB s1 (SZ.v i) (SZ.v e) (SZ.v oh) v m' q' r)
      decreases (ment_measure (SZ.v k) (SZ.v !pi) !pr)
      {
        let i = !pi;
        let e = !pe;
        with s1 . assert (pts_to ks s1);
        S.pts_to_len ks;
        ment_inv_o_len bB s1 (SZ.v i) (SZ.v e) (SZ.v oh) v m' q' true;
        ci_pre_entry bB n f' (SZ.v (S.len rest)) s1 (SZ.v i) (SZ.v e) (SZ.v oh) v m' q';
        let ok = check_items b n f' rest k0 k1 hv idx e 2sz
          (Ghost.hide [fst (List.Tot.index v (SZ.v i)); snd (List.Tot.index v (SZ.v i))])
          (Ghost.hide (List.Tot.append (list_of_pair_list (ldrop (SZ.v i + 1) v)) q'))
          (Ghost.hide (mrest (List.Tot.length v) (SZ.v i) m'))
          pout;
        with o' . assert (pts_to pout o');
        ment_step_ok_o bB s1 (SZ.v i) e (SZ.v o') (SZ.v oh) v m' q' ok;
        if ok {
          let o' = !pout;
          S.op_Dot_Lparen_Rparen_Less_Minus ks i e;
          pi := SZ.add i 1sz;
          pe := o';
        } else {
          pr := false;
        }
      };
      let r = !pr;
      let i = !pi;
      let e = !pe;
      with s1 . assert (pts_to ks s1);
      S.pts_to_len ks;
      assert (pure (Seq.length s1 == Seq.length vt));
      let ok = walk_map_finish b n f' (cmp_one b #p #bB n f') rest k0 k1 hv idx ks tmp oh v m' q' pout r i e #s1 #vt;
      S.join tmp rest r1;
      S.join ks r1 sc;
      walk_map_res n f (lhd lw) (ltl lw) ok;
      if ok {
        with o' . assert (pts_to pout o');
        let o' = !pout;
        po := o';
        pc := SZ.sub c 1sz;
        pl := Ghost.hide (ltl lw);
      } else {
        pres := false;
      }
    } else {
      let is_string = (mt = cbor_major_type_byte_string || mt = cbor_major_type_text_string);
      let leaf : SZ.t = (if is_string then SZ.uint64_to_sizet (get_string_length (Ghost.hide (lhd lw)) h).value else 0sz);
      let rem = impl_remaining_data_items_header (Ghost.hide (S.len b)) h;
      po := SZ.add oh leaf;
      pc := SZ.add rem (SZ.sub c 1sz);
      pl := Ghost.hide (List.Tot.append (children (lhd lw)) (ltl lw));
    }
  };
  with o c lw . assert (pts_to po o ** pts_to pc c ** pts_to pl lw);
  let r = !pres;
  if r {
    walk_end bB (SZ.v o) m lw q;
    let o = !po;
    pout := o;
    r
  } else {
    r
  }
}

#pop-options

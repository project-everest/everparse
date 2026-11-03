module ASN1.Pulse.RawValueRel
#lang-pulse

(* The relation `asn1_raw_rel k pm impl r` between the Pulse
   representations `asn1_impl_t k` (the same as for typed values, see
   `ASN1.Pulse.Rel`) and the raw values `r: ASN1.Spec.Raw.asn1_raw_t k`,
   i.e. values without value conditions.

   Byte-carrying leaves hold the raw leaf encoding `raw_leaf_enc`, which
   agrees with `leaf_enc` on typed values (`raw_leaf_enc_forget`). The
   elements of a SEQUENCE OF / SET OF are related to the raw element parser
   `parse_raw`, i.e. the typed parser followed by `forget`.

   `asn1_rel_to_raw` turns `asn1_rel k pm impl x` into
   `asn1_raw_rel k pm impl (forget k x)`, with a trade back. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Spec.Raw
open ASN1.Spec.Raw.Props

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module I64 = FStar.Int64
module SB = LowParse.Spec.Base
module It = LowParse.PulseParse.Iterator
module ItR = LowParse.PulseParse.Iterator.Rel
module PS = ASN1.Pulse.ParseSequence
module PA = ASN1.Pulse.ParseAdb
module AL = ASN1.Pulse.ParseAdb.Lemmas
module RS = ASN1.Pulse.RelShare
module T = FStar.Tactics
module Trade = Pulse.Lib.Trade

(* Leaves *)

let raw_small_int_rel (_: perm) (x: I64.t) (y: int) : slprop = pure (I64.v x == y)

let raw_int_rel (bound: pos) (pm: perm) (x: asn1_int_impl) (y: int) : slprop =
  match x with
  | Small i -> pure (I64.v i == y)
  | Big s -> prel_slice_ser (raw_leaf_enc (ASN1_INTEGER bound)) pm s y ** pure (~ (fits_i64 y))

let raw_bitstring_rel (pm: perm) (x: asn1_bitstring_impl) (y: U8.t & ASN1.Bytes.asn1_bytes) : slprop =
  exists* w . S.pts_to x.bytes #pm w ** pure (x.unused == fst y /\ w == snd y)

let rec asn1_raw_terminal_rel (k: asn1_terminal_k) : Tot (prel (asn1_terminal_impl_t k) (asn1_raw_terminal_t k)) (decreases k) =
  match k returns prel (asn1_terminal_impl_t k) (asn1_raw_terminal_t k) with
  | ASN1_BOOLEAN -> prel_eq bool
  | ASN1_NULL -> prel_emp unit unit
  | ASN1_INTEGER bound ->
    if small_integer bound
    then raw_small_int_rel
    else raw_int_rel bound
  | ASN1_BITSTRING -> raw_bitstring_rel
  | ASN1_PREFIXED_TERMINAL _ k' -> asn1_raw_terminal_rel k'
  | ASN1_OCTETSTRING -> prel_slice_ser (raw_leaf_enc ASN1_OCTETSTRING)
  | ASN1_PRINTABLESTRING -> prel_slice_ser (raw_leaf_enc ASN1_PRINTABLESTRING)
  | ASN1_UTF8STRING -> prel_slice_ser (raw_leaf_enc ASN1_UTF8STRING)
  | ASN1_IA5STRING -> prel_slice_ser (raw_leaf_enc ASN1_IA5STRING)
  | ASN1_VISIBLESTRING -> prel_slice_ser (raw_leaf_enc ASN1_VISIBLESTRING)
  | ASN1_BMPSTRING -> prel_slice_ser (raw_leaf_enc ASN1_BMPSTRING)
  | ASN1_UNIVERSALSTRING -> prel_slice_ser (raw_leaf_enc ASN1_UNIVERSALSTRING)
  | ASN1_TELETEXSTRING -> prel_slice_ser (raw_leaf_enc ASN1_TELETEXSTRING)
  | ASN1_NUMERICSTRING -> prel_slice_ser (raw_leaf_enc ASN1_NUMERICSTRING)
  | ASN1_VIDEOTEXSTRING -> prel_slice_ser (raw_leaf_enc ASN1_VIDEOTEXSTRING)
  | ASN1_GRAPHICSTRING -> prel_slice_ser (raw_leaf_enc ASN1_GRAPHICSTRING)
  | ASN1_GENERALSTRING -> prel_slice_ser (raw_leaf_enc ASN1_GENERALSTRING)
  | ASN1_OBJECTDESCRIPTOR -> prel_slice_ser (raw_leaf_enc ASN1_OBJECTDESCRIPTOR)
  | ASN1_OID -> prel_slice_ser (raw_leaf_enc ASN1_OID)
  | ASN1_RELATIVE_OID -> prel_slice_ser (raw_leaf_enc ASN1_RELATIVE_OID)
  | ASN1_OID_IRI -> prel_slice_ser (raw_leaf_enc ASN1_OID_IRI)
  | ASN1_RELATIVE_OID_IRI -> prel_slice_ser (raw_leaf_enc ASN1_RELATIVE_OID_IRI)
  | ASN1_UTCTIME -> prel_slice_ser (raw_leaf_enc ASN1_UTCTIME)
  | ASN1_GENERALIZEDTIME -> prel_slice_ser (raw_leaf_enc ASN1_GENERALIZEDTIME)
  | ASN1_DATE -> prel_slice_ser (raw_leaf_enc ASN1_DATE)
  | ASN1_TIME_OF_DAY -> prel_slice_ser (raw_leaf_enc ASN1_TIME_OF_DAY)
  | ASN1_DATE_TIME -> prel_slice_ser (raw_leaf_enc ASN1_DATE_TIME)

(* The relation, mirroring `asn1_rel` *)

let rec asn1_raw_content_rel (k: asn1_content_k) (pm: perm) (x: asn1_content_impl_t k) (y: asn1_raw_content_t k) : Tot slprop (decreases k) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> asn1_raw_terminal_rel k' pm x y
  | ASN1_TERMINAL k' -> asn1_raw_terminal_rel k' pm x y
  | ASN1_SEQUENCE gitems -> asn1_raw_items_rel (dsnd gitems) pm x y
  | ASN1_SET _ items _ -> asn1_raw_items_rel items pm x y
  | ASN1_SEQUENCE_OF _ k' -> It.mixed_list_match (asn1_raw_rel k') ml_ops #asn1_strong_parser_kind (parse_raw k') pm x y
  | ASN1_SET_OF _ k' -> It.mixed_list_match (asn1_raw_rel k') ml_ops #asn1_strong_parser_kind (parse_raw k') pm x y
  | ASN1_PREFIXED k' -> asn1_raw_rel k' pm x y
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      asn1_raw_items_any_rel prefix
        #(asn1_adb_suffix_impl_t key_k ls None)
        #(make_gen_choice_type (raw_any_t_core key_k ls))
        (asn1_raw_adb_rel key_k ls)
        pm x y
    | Some fb ->
      let fbt = asn1_terminal_impl_t key_k & asn1_items_impl_t (dsnd fb) in
      asn1_raw_items_any_rel prefix
        #(asn1_adb_suffix_impl_t key_k ls (Some fbt))
        #(make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t (dsnd fb)))
        (asn1_raw_adb_fb_rel key_k ls fbt (raw_items_t (dsnd fb))
          (fun pm (z: asn1_terminal_impl_t key_k & asn1_items_impl_t (dsnd fb)) key (v: raw_items_t (dsnd fb)) ->
            asn1_raw_terminal_rel key_k pm (fst z) key ** asn1_raw_items_rel (dsnd fb) pm (snd z) v))
        pm x y
    end

and asn1_raw_adb_rel (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (x: asn1_adb_suffix_impl_t key_k ls None) (y: make_gen_choice_type (raw_any_t_core key_k ls))
: Tot slprop (decreases ls)
= match ls with
  | [] -> pure False
  | [(key', it)] ->
    let (| key, v |) = y in
    if key = raw_key_of_lit key_k key'
    then asn1_raw_items_rel (dsnd it) pm x v
    else pure False
  | (key', it) :: tl ->
    let (| key, v |) = y in
    let x' : either (asn1_items_impl_t (dsnd it)) (asn1_adb_suffix_impl_t key_k tl None) = x in
    begin match x' with
    | Inl a -> if key = raw_key_of_lit key_k key' then asn1_raw_items_rel (dsnd it) pm a v else pure False
    | Inr b -> if key = raw_key_of_lit key_k key' then pure False else asn1_raw_adb_rel key_k tl pm b (| key, v |)
    end

and asn1_raw_adb_fb_rel (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbt: Type0) (fbs: Type) (fbr: perm -> fbt -> asn1_raw_terminal_t key_k -> fbs -> slprop)
  (pm: perm) (x: asn1_adb_suffix_impl_t key_k ls (Some fbt)) (y: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) fbs)
: Tot slprop (decreases ls)
= match ls with
  | [] ->
    let (| key, v |) = y in
    fbr pm x key v
  | [(key', it)] ->
    let (| key, v |) = y in
    let x' : either (asn1_items_impl_t (dsnd it)) fbt = x in
    begin match x' with
    | Inl a -> if key = raw_key_of_lit key_k key' then asn1_raw_items_rel (dsnd it) pm a v else pure False
    | Inr b -> if key = raw_key_of_lit key_k key' then pure False else fbr pm b key v
    end
  | (key', it) :: tl ->
    let (| key, v |) = y in
    let x' : either (asn1_items_impl_t (dsnd it)) (asn1_adb_suffix_impl_t key_k tl (Some fbt)) = x in
    begin match x' with
    | Inl a -> if key = raw_key_of_lit key_k key' then asn1_raw_items_rel (dsnd it) pm a v else pure False
    | Inr b -> if key = raw_key_of_lit key_k key' then pure False else asn1_raw_adb_fb_rel key_k tl fbt fbs fbr pm b (| key, v |)
    end

and asn1_raw_lc_rel (lc: list (asn1_id_t & asn1_content_k)) (pm: perm) (x: asn1_lc_impl_t lc) (y: make_gen_choice_type (raw_lc_t lc)) : Tot slprop (decreases lc) =
  match lc with
  | [] -> pure False
  | [(id', c)] ->
    let (| id, v |) = y in
    if id = id'
    then asn1_raw_content_rel c pm x v
    else pure False
  | (id', c) :: tl ->
    let (| id, v |) = y in
    let x' : either (asn1_content_impl_t c) (asn1_lc_impl_t tl) = x in
    begin match x' with
    | Inl a -> if id = id' then asn1_raw_content_rel c pm a v else pure False
    | Inr b -> if id = id' then pure False else asn1_raw_lc_rel tl pm b (| id, v |)
    end

and asn1_raw_rel (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_impl_t k) (y: asn1_raw_t k) : Tot slprop (decreases k) =
  match k with
  | ASN1_ILC _ k' -> asn1_raw_content_rel k' pm x y
  | ASN1_CHOICE_ILC lc _ -> asn1_raw_lc_rel lc pm x y
  | ASN1_ANY_ILC -> prel_slice_ser asn1_value_enc pm x y

and asn1_raw_decorated_rel (#s: _) (#d: _) (dk: asn1_decorated_k s d) (pm: perm) (x: asn1_decorated_impl_t dk) (y: raw_dec_t dk) : Tot slprop (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> asn1_raw_rel k pm x y
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_impl_t k) = x in
    let y' : option (asn1_raw_t k) = y in
    begin match x', y' with
    | None, None -> emp
    | Some a, Some b -> asn1_raw_rel k pm a b
    | _ -> pure False
    end
  | ASN1_DEFAULT_TERMINAL _ #k _ ->
    let x' : option (asn1_terminal_impl_t k) = x in
    let y' : option (asn1_raw_terminal_t k) = y in
    begin match x', y' with
    | None, None -> emp
    | Some a, Some b -> asn1_raw_terminal_rel k pm a b
    | _ -> pure False
    end
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k _ _ ->
    let x' : option (asn1_terminal_impl_t k) = x in
    let y' : option (asn1_raw_terminal_t k) = y in
    begin match x', y' with
    | None, None -> emp
    | Some a, Some b -> asn1_raw_terminal_rel k pm a b
    | _ -> pure False
    end

and asn1_raw_items_rel (#ids: _) (items: asn1_gen_items_l ids) (pm: perm) (x: asn1_items_impl_t items) (y: raw_items_t items) : Tot slprop (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> emp
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> asn1_raw_decorated_rel dk pm x y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_impl_t dk & asn1_items_impl_t tl = x in
    let y' : raw_dec_t dk & raw_items_t tl = y in
    asn1_raw_decorated_rel dk pm (fst x') (fst y') ** asn1_raw_items_rel tl pm (snd x') (snd y')

and asn1_raw_items_any_rel (#ids: _) (items: asn1_gen_items_l ids) (#sfxi: Type0) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (pm: perm) (x: asn1_items_any_impl_t items sfxi) (y: raw_items_any_t items sfxs) : Tot slprop (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> sfxr pm x y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : asn1_decorated_impl_t dk & sfxi = x in
    let y' : raw_dec_t dk & sfxs = y in
    asn1_raw_decorated_rel dk pm (fst x') (fst y') ** sfxr pm (snd x') (snd y')
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_impl_t dk & asn1_items_any_impl_t tl sfxi = x in
    let y' : raw_dec_t dk & raw_items_any_t tl sfxs = y in
    asn1_raw_decorated_rel dk pm (fst x') (fst y') ** asn1_raw_items_any_rel tl sfxr pm (snd x') (snd y')

(* Leaves: the typed and raw relations are equal, through `forget` *)

let slice_bytes (pm: perm) (s: S.slice U8.t) (v: SB.bytes) : slprop =
  exists* w . S.pts_to s #pm w ** pure (w == v)

let slice_ser_bytes (#u: Type) (enc: u -> GTot SB.bytes) (pm: perm) (s: S.slice U8.t) (x: u)
: Lemma (prel_slice_ser enc pm s x == slice_bytes pm s (enc x))
= assert (prel_slice_ser enc pm s x == slice_bytes pm s (enc x))
    by (T.norm [delta_only [`%prel_slice_ser; `%slice_bytes]]; T.trefl ())

let slice_ser_conv (#u1 #u2: Type) (e1: u1 -> GTot SB.bytes) (e2: u2 -> GTot SB.bytes) (pm: perm) (s: S.slice U8.t) (y1: u1) (y2: u2)
: Lemma (requires (e1 y1 == e2 y2)) (ensures (prel_slice_ser e1 pm s y1 == prel_slice_ser e2 pm s y2))
= slice_ser_bytes e1 pm s y1;
  slice_ser_bytes e2 pm s y2

let bitstring_rel_forget (pm: perm) (x: asn1_bitstring_impl) (y: asn1_bitstring_t)
: Lemma (asn1_bitstring_rel pm x y == raw_bitstring_rel pm x (BYTES_WITH_UNUSEDBITS?.unused y, BYTES_WITH_UNUSEDBITS?.b y))
= assert (asn1_bitstring_rel pm x y == raw_bitstring_rel pm x (BYTES_WITH_UNUSEDBITS?.unused y, BYTES_WITH_UNUSEDBITS?.b y))
    by (T.norm [delta_only [`%asn1_bitstring_rel; `%raw_bitstring_rel; `%fst; `%snd]; iota]; T.trefl ())

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let leaf_rel_forget (k: leaf_k) (pm: perm) (x: asn1_terminal_impl_t k) (y: asn1_terminal_t k)
: Lemma
  (requires (~ (ASN1_BOOLEAN? k \/ ASN1_NULL? k \/ ASN1_INTEGER? k \/ ASN1_BITSTRING? k)))
  (ensures (asn1_terminal_rel k pm x y == asn1_raw_terminal_rel k pm x (forget_terminal k y)))
= asn1_terminal_rel_leaf_eq k pm x y;
  assert (asn1_raw_terminal_rel k == prel_slice_ser (raw_leaf_enc k));
  raw_leaf_enc_forget k y;
  slice_ser_conv (leaf_enc k) (raw_leaf_enc k) pm x y (forget_terminal k y)

let rec terminal_rel_forget (k: asn1_terminal_k) (pm: perm) (x: asn1_terminal_impl_t k) (y: asn1_terminal_t k)
: Lemma (ensures (asn1_terminal_rel k pm x y == asn1_raw_terminal_rel k pm x (forget_terminal k y))) (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id k' ->
    assert_norm (asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id k') == asn1_terminal_impl_t k');
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id k') == asn1_terminal_t k');
    assert_norm (asn1_terminal_rel (ASN1_PREFIXED_TERMINAL id k') == asn1_terminal_rel k');
    assert_norm (asn1_raw_terminal_rel (ASN1_PREFIXED_TERMINAL id k') == asn1_raw_terminal_rel k');
    let x' : asn1_terminal_impl_t k' = coerce_eq () x in
    let y' : asn1_terminal_t k' = coerce_eq () y in
    assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id k') == asn1_raw_terminal_t k');
    assert_norm (forget_terminal (ASN1_PREFIXED_TERMINAL id k') y == coerce_eq #(asn1_raw_terminal_t k') #(asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id k')) () (forget_terminal k' y'));
    terminal_rel_forget k' pm x' y'
  | ASN1_BOOLEAN -> ()
  | ASN1_NULL -> ()
  | ASN1_INTEGER bound ->
    if small_integer bound then ()
    else begin
      let x' : asn1_int_impl = x in
      match x' with
      | Small _ -> ()
      | Big s ->
        raw_leaf_enc_forget (ASN1_INTEGER bound) y;
        slice_ser_conv (integer_enc bound) (raw_leaf_enc (ASN1_INTEGER bound)) pm s y y
    end
  | ASN1_BITSTRING -> bitstring_rel_forget pm x y
  | _ -> leaf_rel_forget k pm x y
#pop-options

(* Conversions between a typed relation `r1` and a raw relation `r2` along
   `f`, in direction `b` (`true`: from typed to raw) *)

let cv (b: bool) (p q: slprop) : slprop = if b then p else q

let cv_star (b: bool) (p1 p2 q1 q2: slprop)
: Lemma (cv b (p1 ** p2) (q1 ** q2) == (cv b p1 q1 ** cv b p2 q2))
= ()

let conv_t (b: bool) (#t: Type0) (#u1 #u2: Type0) (r1: prel t u1) (r2: prel t u2) (f: u1 -> u2) : Type =
  (pm: perm) -> (x: t) -> (y: u1) ->
  stt_ghost unit emp_inames (cv b (r1 pm x y) (r2 pm x (f y))) (fun _ -> cv b (r2 pm x (f y)) (r1 pm x y))

let pequiv (#t: Type0) (#u: Type0) (r1 r2: prel t u) : prop =
  forall pm x y . r1 pm x y == r2 pm x y

ghost
fn conv_eq (b: bool) (#t: Type0) (#u1 #u2: Type0) (r1: prel t u1) (r2: prel t u2) (f: u1 -> u2)
  (lem: (pm: perm) -> (x: t) -> (y: u1) -> Lemma (r1 pm x y == r2 pm x (f y)))
: conv_t b r1 r2 f
= (pm: perm) (x: t) (y: u1)
{
  lem pm x y;
  rewrite (cv b (r1 pm x y) (r2 pm x (f y))) as (cv b (r2 pm x (f y)) (r1 pm x y))
}

ghost
fn conv_ext (b: bool) (#t: Type0) (#u1 #u2: Type0) (r1 r1': prel t u1) (r2 r2': prel t u2) (f f': u1 -> u2)
  (sq: squash (pequiv r1 r1' /\ pequiv r2 r2' /\ (forall y . f y == f' y)))
  (c: conv_t b r1 r2 f)
: conv_t b r1' r2' f'
= (pm: perm) (x: t) (y: u1)
{
  rewrite (cv b (r1' pm x y) (r2' pm x (f' y))) as (cv b (r1 pm x y) (r2 pm x (f y)));
  c pm x y;
  rewrite (cv b (r2 pm x (f y)) (r1 pm x y)) as (cv b (r2' pm x (f' y)) (r1' pm x y))
}

let pair_map (#a1 #a2 #b1 #b2: Type0) (f1: a1 -> a2) (f2: b1 -> b2) (y: a1 & b1) : (a2 & b2) =
  (f1 (fst y), f2 (snd y))

ghost
fn conv_pair (b: bool) (#t1 #t2: Type0) (#u1 #u2 #v1 #v2: Type0)
  (ra: prel t1 u1) (ra': prel t1 u2) (fa: u1 -> u2)
  (rb: prel t2 v1) (rb': prel t2 v2) (fb: v1 -> v2)
  (ca: conv_t b ra ra' fa) (cb: conv_t b rb rb' fb)
: conv_t b (prel_pair ra rb) (prel_pair ra' rb') (pair_map fa fb)
= (pm: perm) (x: (t1 & t2)) (y: (u1 & v1))
{
  cv_star b (ra pm (fst x) (fst y)) (rb pm (snd x) (snd y)) (ra' pm (fst x) (fa (fst y))) (rb' pm (snd x) (fb (snd y)));
  rewrite (cv b (prel_pair ra rb pm x y) (prel_pair ra' rb' pm x (pair_map fa fb y)))
    as (cv b (ra pm (fst x) (fst y)) (ra' pm (fst x) (fa (fst y))) ** cv b (rb pm (snd x) (snd y)) (rb' pm (snd x) (fb (snd y))));
  ca pm (fst x) (fst y);
  cb pm (snd x) (snd y);
  cv_star b (ra' pm (fst x) (fa (fst y))) (rb' pm (snd x) (fb (snd y))) (ra pm (fst x) (fst y)) (rb pm (snd x) (snd y));
  rewrite (cv b (ra' pm (fst x) (fa (fst y))) (ra pm (fst x) (fst y)) ** cv b (rb' pm (snd x) (fb (snd y))) (rb pm (snd x) (snd y)))
    as (cv b (prel_pair ra' rb' pm x (pair_map fa fb y)) (prel_pair ra rb pm x y))
}

let omap (#a #b: Type0) (f: a -> b) (x: option a) : option b =
  match x with
  | None -> None
  | Some y -> Some (f y)

ghost
fn conv_option (b: bool) (#t: Type0) (#u1 #u2: Type0) (r1: prel t u1) (r2: prel t u2) (f: u1 -> u2) (c: conv_t b r1 r2 f)
: conv_t b (prel_option r1) (prel_option r2) (omap f)
= (pm: perm) (x: option t) (y: option u1)
{
  match x {
    None -> {
      match y {
        None -> {
          rewrite (cv b (prel_option r1 pm x y) (prel_option r2 pm x (omap f y)))
            as (cv b (prel_option r2 pm x (omap f y)) (prel_option r1 pm x y))
        }
        Some _ -> {
          rewrite (cv b (prel_option r1 pm x y) (prel_option r2 pm x (omap f y))) as pure False;
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        None -> {
          rewrite (cv b (prel_option r1 pm x y) (prel_option r2 pm x (omap f y))) as pure False;
          unreachable ()
        }
        Some v -> {
          rewrite (cv b (prel_option r1 pm x y) (prel_option r2 pm x (omap f y))) as (cv b (r1 pm a v) (r2 pm a (f v)));
          c pm a v;
          rewrite (cv b (r2 pm a (f v)) (r1 pm a v)) as (cv b (prel_option r2 pm x (omap f y)) (prel_option r1 pm x y))
        }
      }
    }
  }
}

let dmap (#u: eqtype) (#defv: u) (#v: Type0) (f: u -> v) (x: default_tv defv) : option v =
  match x with
  | Default -> None
  | Nondefault y -> Some (f y)

ghost
fn conv_default (b: bool) (#t: Type0) (#u: eqtype) (#v: Type0) (r1: prel t u) (defv: u) (r2: prel t v) (f: u -> v) (c: conv_t b r1 r2 f)
: conv_t b (RS.prel_default r1 defv) (prel_option r2) (dmap #u #defv f)
= (pm: perm) (x: option t) (y: default_tv defv)
{
  match x {
    None -> {
      match y {
        Default -> {
          rewrite (cv b (RS.prel_default r1 defv pm x y) (prel_option r2 pm x (dmap #u #defv f y)))
            as (cv b (prel_option r2 pm x (dmap #u #defv f y)) (RS.prel_default r1 defv pm x y))
        }
        Nondefault _ -> {
          rewrite (cv b (RS.prel_default r1 defv pm x y) (prel_option r2 pm x (dmap #u #defv f y))) as pure False;
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        Default -> {
          rewrite (cv b (RS.prel_default r1 defv pm x y) (prel_option r2 pm x (dmap #u #defv f y))) as pure False;
          unreachable ()
        }
        Nondefault w -> {
          rewrite (cv b (RS.prel_default r1 defv pm x y) (prel_option r2 pm x (dmap #u #defv f y))) as (cv b (r1 pm a w) (r2 pm a (f w)));
          c pm a w;
          rewrite (cv b (r2 pm a (f w)) (r1 pm a w)) as (cv b (prel_option r2 pm x (dmap #u #defv f y)) (RS.prel_default r1 defv pm x y))
        }
      }
    }
  }
}

(* Terminals *)

let conv_terminal (b: bool) (k: asn1_terminal_k) : conv_t b (asn1_terminal_rel k) (asn1_raw_terminal_rel k) (forget_terminal k) =
  conv_eq b (asn1_terminal_rel k) (asn1_raw_terminal_rel k) (forget_terminal k) (terminal_rel_forget k)

(* Equivalences for the raw relation, mirroring those of `ASN1.Pulse.RelShare` *)

let raw_content_terminal_equiv (k: asn1_terminal_k)
: Lemma (pequiv #(asn1_terminal_impl_t k) #(asn1_raw_terminal_t k) (asn1_raw_terminal_rel k) (asn1_raw_content_rel (ASN1_TERMINAL k)))
= assert_norm (pequiv #(asn1_terminal_impl_t k) #(asn1_raw_terminal_t k) (asn1_raw_terminal_rel k) (asn1_raw_content_rel (ASN1_TERMINAL k)))

let raw_content_restricted_equiv (k: asn1_terminal_k) (r: asn1_restriction k)
: Lemma (pequiv #(asn1_terminal_impl_t k) #(asn1_raw_terminal_t k) (asn1_raw_terminal_rel k) (asn1_raw_content_rel (ASN1_RESTRICTED_TERMINAL k r)))
= assert_norm (pequiv #(asn1_terminal_impl_t k) #(asn1_raw_terminal_t k) (asn1_raw_terminal_rel k) (asn1_raw_content_rel (ASN1_RESTRICTED_TERMINAL k r)))

let raw_content_prefixed_equiv (#s: _) (k: asn1_k s)
: Lemma (pequiv #(asn1_impl_t k) #(asn1_raw_t k) (asn1_raw_rel k) (asn1_raw_content_rel (ASN1_PREFIXED k)))
= assert_norm (pequiv #(asn1_impl_t k) #(asn1_raw_t k) (asn1_raw_rel k) (asn1_raw_content_rel (ASN1_PREFIXED k)))

let raw_content_sequence_equiv (gitems: asn1_gen_items_lk)
: Lemma (pequiv #(asn1_items_impl_t (dsnd gitems)) #(raw_items_t (dsnd gitems)) (asn1_raw_items_rel (dsnd gitems)) (asn1_raw_content_rel (ASN1_SEQUENCE gitems)))
= assert_norm (pequiv #(asn1_items_impl_t (dsnd gitems)) #(raw_items_t (dsnd gitems)) (asn1_raw_items_rel (dsnd gitems)) (asn1_raw_content_rel (ASN1_SEQUENCE gitems)))

let raw_content_set_equiv (ids: _) (items: asn1_gen_items_l ids) (pf: _)
: Lemma (pequiv #(asn1_items_impl_t items) #(raw_items_t items) (asn1_raw_items_rel items) (asn1_raw_content_rel (ASN1_SET ids items pf)))
= assert_norm (pequiv #(asn1_items_impl_t items) #(raw_items_t items) (asn1_raw_items_rel items) (asn1_raw_content_rel (ASN1_SET ids items pf)))

let raw_rel_ilc_equiv (id: asn1_id_t) (k: asn1_content_k)
: Lemma (pequiv #(asn1_content_impl_t k) #(asn1_raw_content_t k) (asn1_raw_content_rel k) (asn1_raw_rel (ASN1_ILC id k)))
= assert_norm (pequiv #(asn1_content_impl_t k) #(asn1_raw_content_t k) (asn1_raw_content_rel k) (asn1_raw_rel (ASN1_ILC id k)))

let raw_rel_any_equiv (_: unit)
: Lemma (pequiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (asn1_raw_rel ASN1_ANY_ILC))
= assert_norm (pequiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (asn1_raw_rel ASN1_ANY_ILC))

let raw_rel_choice_equiv (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc)))
: Lemma (pequiv #(asn1_lc_impl_t lc) #(make_gen_choice_type (raw_lc_t lc)) (asn1_raw_lc_rel lc) (asn1_raw_rel (ASN1_CHOICE_ILC lc pf)))
= assert_norm (pequiv #(asn1_lc_impl_t lc) #(make_gen_choice_type (raw_lc_t lc)) (asn1_raw_lc_rel lc) (asn1_raw_rel (ASN1_CHOICE_ILC lc pf)))

let raw_dec_plain_equiv (#s: _) (k: asn1_k s)
: Lemma (pequiv #(asn1_impl_t k) #(asn1_raw_t k) (asn1_raw_rel k) (asn1_raw_decorated_rel (ASN1_PLAIN_ILC k)))
= assert_norm (pequiv #(asn1_impl_t k) #(asn1_raw_t k) (asn1_raw_rel k) (asn1_raw_decorated_rel (ASN1_PLAIN_ILC k)))

let raw_dec_option_equiv (#s: _) (k: asn1_k s)
: Lemma (pequiv #(option (asn1_impl_t k)) #(option (asn1_raw_t k)) (prel_option (asn1_raw_rel k)) (asn1_raw_decorated_rel (ASN1_OPTION_ILC k)))
= assert_norm (pequiv #(option (asn1_impl_t k)) #(option (asn1_raw_t k)) (prel_option (asn1_raw_rel k)) (asn1_raw_decorated_rel (ASN1_OPTION_ILC k)))

let raw_dec_default_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k)
: Lemma (pequiv #(option (asn1_terminal_impl_t k)) #(option (asn1_raw_terminal_t k)) (prel_option (asn1_raw_terminal_rel k)) (asn1_raw_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)))
= assert_norm (pequiv #(option (asn1_terminal_impl_t k)) #(option (asn1_raw_terminal_t k)) (prel_option (asn1_raw_terminal_rel k)) (asn1_raw_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)))

let raw_dec_default_restricted_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) })
: Lemma (pequiv #(option (asn1_terminal_impl_t k)) #(option (asn1_raw_terminal_t k)) (prel_option (asn1_raw_terminal_rel k)) (asn1_raw_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)))
= assert_norm (pequiv #(option (asn1_terminal_impl_t k)) #(option (asn1_raw_terminal_t k)) (prel_option (asn1_raw_terminal_rel k)) (asn1_raw_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)))

let raw_items_nil_equiv (_: unit)
: Lemma (pequiv #unit #unit (prel_emp unit unit) (asn1_raw_items_rel ASN1_GEN_ITEMS_NIL))
= assert_norm (pequiv #unit #unit (prel_emp unit unit) (asn1_raw_items_rel ASN1_GEN_ITEMS_NIL))

let raw_items_single_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (pequiv #(asn1_decorated_impl_t dk) #(raw_dec_t dk) (asn1_raw_decorated_rel dk) (asn1_raw_items_rel (PS.single dk)))
= assert_norm (pequiv #(asn1_decorated_impl_t dk) #(raw_dec_t dk) (asn1_raw_decorated_rel dk) (asn1_raw_items_rel (PS.single dk)))

let raw_items_cons_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
: Lemma (pequiv
    #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    #(raw_dec_t dk & raw_items_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    (prel_pair (asn1_raw_decorated_rel dk) (asn1_raw_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
    (asn1_raw_items_rel (PS.cons2 dk dk2 tl2)))
= assert_norm (pequiv
    #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    #(raw_dec_t dk & raw_items_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    (prel_pair (asn1_raw_decorated_rel dk) (asn1_raw_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
    (asn1_raw_items_rel (PS.cons2 dk dk2 tl2)))

let raw_items_any_nil_equiv (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (pequiv #sfxi #sfxs sfxr (asn1_raw_items_any_rel ASN1_GEN_ITEMS_NIL sfxr))
= assert_norm (pequiv #sfxi #sfxs sfxr (asn1_raw_items_any_rel ASN1_GEN_ITEMS_NIL sfxr))

let raw_items_any_single_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (pequiv #(asn1_decorated_impl_t dk & sfxi) #(raw_dec_t dk & sfxs) (prel_pair (asn1_raw_decorated_rel dk) sfxr) (asn1_raw_items_any_rel (PS.single dk) sfxr))
= assert_norm (pequiv #(asn1_decorated_impl_t dk & sfxi) #(raw_dec_t dk & sfxs) (prel_pair (asn1_raw_decorated_rel dk) sfxr) (asn1_raw_items_any_rel (PS.single dk) sfxr))

let raw_items_any_cons_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (pequiv
    #(asn1_decorated_impl_t dk & asn1_items_any_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi)
    #(raw_dec_t dk & raw_items_any_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs)
    (prel_pair (asn1_raw_decorated_rel dk) (asn1_raw_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr))
    (asn1_raw_items_any_rel (PS.cons2 dk dk2 tl2) sfxr))
= assert_norm (pequiv
    #(asn1_decorated_impl_t dk & asn1_items_any_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi)
    #(raw_dec_t dk & raw_items_any_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs)
    (prel_pair (asn1_raw_decorated_rel dk) (asn1_raw_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr))
    (asn1_raw_items_any_rel (PS.cons2 dk dk2 tl2) sfxr))

(* `forget`, case by case *)

let lc_forget (lc: list (asn1_id_t & asn1_content_k)) (v: make_gen_choice_type (asn1_lc_t lc)) : Tot (make_gen_choice_type (raw_lc_t lc)) =
  (| dfst v, forget_choice lc (dfst v) (dsnd v) |)

let restricted_forget (k: asn1_terminal_k) (r: asn1_restriction k) (y: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) : Tot (asn1_raw_terminal_t k) =
  forget_terminal k (RS.restricted_up k r y)

let items_any_forget (#ids: _) (items: asn1_gen_items_l ids) (#sfxs #rsfx: Type0) (fs: sfxs -> rsfx) (x: asn1_sequence_any_t_core items sfxs) : Tot (raw_items_any_t items rsfx) =
  forget_items_any items x (fs (items_any_sfx items x))

#push-options "--fuel 2 --ifuel 1"
let forget_content_terminal (k: asn1_terminal_k)
: Lemma (forall y . forget_content (ASN1_TERMINAL k) y == forget_terminal k y)
= ()

let forget_content_restricted (k: asn1_terminal_k) (r: asn1_restriction k)
: Lemma (forall y . forget_content (ASN1_RESTRICTED_TERMINAL k r) y == restricted_forget k r y)
= ()

let forget_content_prefixed (#s: _) (k: asn1_k s)
: Lemma (forall y . forget_content (ASN1_PREFIXED k) y == forget k y)
= ()

let forget_content_sequence (gitems: asn1_gen_items_lk)
: Lemma (forall y . forget_content (ASN1_SEQUENCE gitems) y == forget_items (dsnd gitems) y)
= ()

let forget_content_set (ids: _) (items: asn1_gen_items_l ids) (pf: _)
: Lemma (forall y . forget_content (ASN1_SET ids items pf) y == forget_items items y)
= ()

let forget_ilc (id: asn1_id_t) (k: asn1_content_k)
: Lemma (forall y . forget (ASN1_ILC id k) y == forget_content k y)
= ()

let forget_any (_: unit)
: Lemma (forall y . forget ASN1_ANY_ILC y == y)
= ()

let forget_choice_ilc_1 (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (y: make_gen_choice_type (asn1_lc_t lc))
: Lemma (forget (ASN1_CHOICE_ILC lc pf) y == lc_forget lc y)
= let (| id, w |) = y in
  assert_norm (forget (ASN1_CHOICE_ILC lc pf) (| id, w |) == lc_forget lc (| id, w |))

let forget_choice_ilc (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc)))
: Lemma (forall (y: make_gen_choice_type (asn1_lc_t lc)) . forget (ASN1_CHOICE_ILC lc pf) y == lc_forget lc y)
= Classical.forall_intro (forget_choice_ilc_1 lc pf)

let forget_dec_plain (#s: _) (k: asn1_k s)
: Lemma (forall y . forget_dec (ASN1_PLAIN_ILC k) y == forget k y)
= ()

let forget_dec_option (#s: _) (k: asn1_k s)
: Lemma (forall y . forget_dec (ASN1_OPTION_ILC k) y == omap (forget k) y)
= ()

let forget_dec_default (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k)
: Lemma (forall y . forget_dec (ASN1_DEFAULT_TERMINAL id0 #k defv) y == dmap #(asn1_terminal_t k) #(key_of_lit k defv) (forget_terminal k) y)
= ()

let forget_dec_default_restricted (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) })
: Lemma (forall y . forget_dec (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv) y == dmap #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) #(key_of_lit k defv) (restricted_forget k r) y)
= ()

let forget_items_nil (_: unit)
: Lemma (forall y . forget_items ASN1_GEN_ITEMS_NIL y == y)
= ()

let forget_items_single (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (forall y . forget_items (PS.single dk) y == forget_dec dk y)
= ()

let forget_items_cons (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
: Lemma (forall y . forget_items (PS.cons2 dk dk2 tl2) y == pair_map (forget_dec dk) (forget_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) y)
= ()

let forget_items_any_nil (#sfxs #rsfx: Type0) (fs: sfxs -> rsfx)
: Lemma (forall y . items_any_forget ASN1_GEN_ITEMS_NIL fs y == fs y)
= ()

let forget_items_any_single (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#sfxs #rsfx: Type0) (fs: sfxs -> rsfx)
: Lemma (forall y . items_any_forget (PS.single dk) fs y == pair_map (forget_dec dk) fs y)
= ()

let forget_items_any_cons (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2) (#sfxs #rsfx: Type0) (fs: sfxs -> rsfx)
: Lemma (forall y . items_any_forget (PS.cons2 dk dk2 tl2) fs y == pair_map (forget_dec dk) (items_any_forget (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) fs) y)
= ()
#pop-options

(* SEQUENCE OF / SET OF *)

let fwd_r (#s: _) (k: asn1_k s) (a: asn1_t k) (b: asn1_raw_t k) : prop = b == forget k a
let bwd_r (#s: _) (k: asn1_k s) (a: asn1_raw_t k) (b: asn1_t k) : prop = a == forget k b

#push-options "--fuel 2 --ifuel 1"
let rec list_rel_fwd (#s: _) (k: asn1_k s) (l: list (asn1_t k))
: Lemma (ensures (ItR.list_rel (fwd_r k) l (forget_list k l))) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> list_rel_fwd k q

let rec list_rel_bwd (#s: _) (k: asn1_k s) (l: list (asn1_t k))
: Lemma (ensures (ItR.list_rel (bwd_r k) (forget_list k l) l)) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> list_rel_bwd k q
#pop-options

let parsers_fwd (#s: _) (k: asn1_k s)
: Lemma (ItR.parsers_rel #asn1_strong_parser_kind (asn1_as_parser k) (parse_raw k) (fwd_r k) /\ ItR.rel_functional (fwd_r k))
= Classical.forall_intro (parse_raw_eq k)

let parsers_bwd (#s: _) (k: asn1_k s)
: Lemma (ItR.parsers_rel #asn1_strong_parser_kind (parse_raw k) (asn1_as_parser k) (bwd_r k) /\ ItR.rel_functional (bwd_r k))
= Classical.forall_intro (parse_raw_eq k);
  Classical.forall_intro_2 (fun x1 x2 -> Classical.move_requires (forget_inj k x1) x2)

ghost
fn elem_fwd (#s: _) (k: asn1_k s) (b: bool) (sq: squash (b == true)) (c: conv_t b (asn1_rel k) (asn1_raw_rel k) (forget k))
  (x: asn1_impl_t k) (pm0: perm) (y1: asn1_t k) (y2: asn1_raw_t k { fwd_r k y1 y2 })
requires asn1_rel k pm0 x y1
ensures asn1_raw_rel k pm0 x y2
{
  rewrite (asn1_rel k pm0 x y1) as (cv b (asn1_rel k pm0 x y1) (asn1_raw_rel k pm0 x (forget k y1)));
  c pm0 x y1;
  rewrite (cv b (asn1_raw_rel k pm0 x (forget k y1)) (asn1_rel k pm0 x y1)) as (asn1_raw_rel k pm0 x y2)
}

ghost
fn elem_bwd (#s: _) (k: asn1_k s) (b: bool) (sq: squash (b == false)) (c: conv_t b (asn1_rel k) (asn1_raw_rel k) (forget k))
  (x: asn1_impl_t k) (pm0: perm) (y1: asn1_raw_t k) (y2: asn1_t k { bwd_r k y1 y2 })
requires asn1_raw_rel k pm0 x y1
ensures asn1_rel k pm0 x y2
{
  rewrite (asn1_raw_rel k pm0 x y1) as (cv b (asn1_rel k pm0 x y2) (asn1_raw_rel k pm0 x (forget k y2)));
  c pm0 x y2;
  rewrite (cv b (asn1_raw_rel k pm0 x (forget k y2)) (asn1_rel k pm0 x y2)) as (asn1_rel k pm0 x y2)
}

ghost
fn conv_list (b: bool) (#s: _) (k: asn1_k s) (c: conv_t b (asn1_rel k) (asn1_raw_rel k) (forget k))
: conv_t b #(ml (asn1_impl_t k)) #(list (asn1_t k)) #(list (asn1_raw_t k))
    (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k))
    (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k))
    (forget_list k)
= (pm: perm) (x: ml (asn1_impl_t k)) (y: list (asn1_t k))
{
  if b {
    rewrite (cv b (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y) (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k y)))
      as (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y);
    list_rel_fwd k y;
    parsers_fwd k;
    ItR.mixed_list_match_rel (asn1_rel k) (asn1_raw_rel k) ml_ops (asn1_as_parser k) (parse_raw k) (fwd_r k) () pm x y (forget_list k y) (elem_fwd k b () c);
    rewrite (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k y))
      as (cv b (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k y)) (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y))
  } else {
    rewrite (cv b (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y) (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k y)))
      as (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k y));
    list_rel_bwd k y;
    parsers_bwd k;
    ItR.mixed_list_match_rel (asn1_raw_rel k) (asn1_rel k) ml_ops (parse_raw k) (asn1_as_parser k) (bwd_r k) () pm x (forget_list k y) y (elem_bwd k b () c);
    rewrite (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y)
      as (cv b (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k y)) (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y))
  }
}

let raw_seq_of_eq (ne: bool) (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) (y: asn1_raw_content_t (ASN1_SEQUENCE_OF ne k))
: Lemma (asn1_raw_content_rel (ASN1_SEQUENCE_OF ne k) pm x y == It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x y)
= assert (asn1_raw_content_rel (ASN1_SEQUENCE_OF ne k) pm x y == It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x y)
    by (T.norm [delta_only [`%asn1_raw_content_rel]; iota; zeta]; T.trefl ())

let raw_set_of_eq (ne: bool) (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_content_impl_t (ASN1_SET_OF ne k)) (y: asn1_raw_content_t (ASN1_SET_OF ne k))
: Lemma (asn1_raw_content_rel (ASN1_SET_OF ne k) pm x y == It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x y)
= assert (asn1_raw_content_rel (ASN1_SET_OF ne k) pm x y == It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x y)
    by (T.norm [delta_only [`%asn1_raw_content_rel]; iota; zeta]; T.trefl ())

#push-options "--fuel 2 --ifuel 1"
let forget_seq_of (ne: bool) (#s: _) (k: asn1_k s) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k))
: Lemma (forget_content (ASN1_SEQUENCE_OF ne k) y == forget_list k (RS.seq_of_up ne k y))
= ()

let forget_set_of (ne: bool) (#s: _) (k: asn1_k s) (y: asn1_content_t (ASN1_SET_OF ne k))
: Lemma (forget_content (ASN1_SET_OF ne k) y == forget_list k (RS.set_of_up ne k y))
= ()
#pop-options

ghost
fn conv_seq_of (b: bool) (ne: bool) (#s: _) (k: asn1_k s) (c: conv_t b (asn1_rel k) (asn1_raw_rel k) (forget k))
: conv_t b (asn1_content_rel (ASN1_SEQUENCE_OF ne k)) (asn1_raw_content_rel (ASN1_SEQUENCE_OF ne k)) (forget_content (ASN1_SEQUENCE_OF ne k))
= (pm: perm) (x: asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k))
{
  RS.seq_of_eq ne k pm x y;
  raw_seq_of_eq ne k pm x (forget_content (ASN1_SEQUENCE_OF ne k) y);
  forget_seq_of ne k y;
  rewrite (cv b (asn1_content_rel (ASN1_SEQUENCE_OF ne k) pm x y) (asn1_raw_content_rel (ASN1_SEQUENCE_OF ne k) pm x (forget_content (ASN1_SEQUENCE_OF ne k) y)))
    as (cv b (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x (RS.seq_of_up ne k y)) (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k (RS.seq_of_up ne k y))));
  conv_list b k c pm x (RS.seq_of_up ne k y);
  rewrite (cv b (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k (RS.seq_of_up ne k y))) (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x (RS.seq_of_up ne k y)))
    as (cv b (asn1_raw_content_rel (ASN1_SEQUENCE_OF ne k) pm x (forget_content (ASN1_SEQUENCE_OF ne k) y)) (asn1_content_rel (ASN1_SEQUENCE_OF ne k) pm x y))
}

ghost
fn conv_set_of (b: bool) (ne: bool) (#s: _) (k: asn1_k s) (c: conv_t b (asn1_rel k) (asn1_raw_rel k) (forget k))
: conv_t b (asn1_content_rel (ASN1_SET_OF ne k)) (asn1_raw_content_rel (ASN1_SET_OF ne k)) (forget_content (ASN1_SET_OF ne k))
= (pm: perm) (x: asn1_content_impl_t (ASN1_SET_OF ne k)) (y: asn1_content_t (ASN1_SET_OF ne k))
{
  RS.set_of_eq ne k pm x y;
  raw_set_of_eq ne k pm x (forget_content (ASN1_SET_OF ne k) y);
  forget_set_of ne k y;
  rewrite (cv b (asn1_content_rel (ASN1_SET_OF ne k) pm x y) (asn1_raw_content_rel (ASN1_SET_OF ne k) pm x (forget_content (ASN1_SET_OF ne k) y)))
    as (cv b (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x (RS.set_of_up ne k y)) (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k (RS.set_of_up ne k y))));
  conv_list b k c pm x (RS.set_of_up ne k y);
  rewrite (cv b (It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k (RS.set_of_up ne k y))) (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x (RS.set_of_up ne k y)))
    as (cv b (asn1_raw_content_rel (ASN1_SET_OF ne k) pm x (forget_content (ASN1_SET_OF ne k) y)) (asn1_content_rel (ASN1_SET_OF ne k) pm x y))
}

(* CHOICE alternatives *)

let raw_lc_head_val (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (raw_lc_t ((id', c) :: tl))) (sq: squash (dfst v == id'))
: Tot (asn1_raw_content_t c)
= dsnd v

let raw_lc_tail_val (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (raw_lc_t (hd :: tl))) (sq: squash (dfst v <> fst hd))
: Tot (make_gen_choice_type (raw_lc_t tl))
= (| dfst v, dsnd v |)

let raw_lc_single_eq (id': asn1_id_t) (c: asn1_content_k) (pm: perm) (x: asn1_lc_impl_t [(id', c)])
  (v: make_gen_choice_type (raw_lc_t [(id', c)]))
: Lemma (asn1_raw_lc_rel [(id', c)] pm x v == (if dfst v = id' then asn1_raw_content_rel c pm x (raw_lc_head_val id' c [] v ()) else pure False))
= assert_norm (asn1_raw_lc_rel [(id', c)] pm x v == (let (| id, v |) = v in if id = id' then asn1_raw_content_rel c pm x v else pure False))

let raw_lc_cons_inl_eq (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (a: asn1_content_impl_t c) (v: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm (RS.lc_inl id' c hd2 tl2 a) v ==
    (if dfst v = id' then asn1_raw_content_rel c pm a (raw_lc_head_val id' c (hd2 :: tl2) v ()) else pure False))
= let (| id, w |) = v in
  assert_norm (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm (RS.lc_inl id' c hd2 tl2 a) (| id, w |) ==
    (if id = id' then asn1_raw_content_rel c pm a w else pure False))

let raw_lc_cons_inr_eq (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (b: asn1_lc_impl_t (hd2 :: tl2)) (v: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm (RS.lc_inr id' c hd2 tl2 b) v ==
    (if dfst v = id' then pure False else asn1_raw_lc_rel (hd2 :: tl2) pm b (raw_lc_tail_val (id', c) (hd2 :: tl2) v ())))
= let (| id, w |) = v in
  assert_norm (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm (RS.lc_inr id' c hd2 tl2 b) (| id, w |) ==
    (if id = id' then pure False else asn1_raw_lc_rel (hd2 :: tl2) pm b (| id, w |)));
  if id = id' then () else begin
    assert_norm (raw_lc_tail_val (id', c) (hd2 :: tl2) v () == (| dfst v, dsnd v |))
  end

#push-options "--fuel 2 --ifuel 1"
let lc_forget_dfst (lc: list (asn1_id_t & asn1_content_k)) (v: make_gen_choice_type (asn1_lc_t lc))
: Lemma (dfst (lc_forget lc v) == dfst v)
= ()

let lc_forget_head (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (asn1_lc_t ((id', c) :: tl)))
: Lemma (requires (dfst v == id'))
  (ensures (raw_lc_head_val id' c tl (lc_forget ((id', c) :: tl) v) () == forget_content c (RS.lc_head_val id' c tl v ())))
= ()

let lc_forget_tail (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (asn1_lc_t (hd :: tl)))
: Lemma (requires (dfst v <> fst hd))
  (ensures (raw_lc_tail_val hd tl (lc_forget (hd :: tl) v) () == lc_forget tl (RS.lc_tail_val hd tl v ())))
= ()
#pop-options

ghost
fn conv_lc_nil (b: bool)
: conv_t b (asn1_lc_rel []) (asn1_raw_lc_rel []) (lc_forget [])
= (pm: perm) (x: asn1_lc_impl_t []) (y: make_gen_choice_type (asn1_lc_t []))
{
  rewrite (cv b (asn1_lc_rel [] pm x y) (asn1_raw_lc_rel [] pm x (lc_forget [] y))) as (pure False);
  unreachable ()
}

ghost
fn conv_lc_single (b: bool) (id': asn1_id_t) (c: asn1_content_k) (cc: conv_t b (asn1_content_rel c) (asn1_raw_content_rel c) (forget_content c))
: conv_t b (asn1_lc_rel [(id', c)]) (asn1_raw_lc_rel [(id', c)]) (lc_forget [(id', c)])
= (pm: perm) (x: asn1_lc_impl_t [(id', c)]) (y: make_gen_choice_type (asn1_lc_t [(id', c)]))
{
  RS.lc_single_eq id' c pm x y;
  raw_lc_single_eq id' c pm x (lc_forget [(id', c)] y);
  lc_forget_dfst [(id', c)] y;
  if (dfst y = id') {
    lc_forget_head id' c [] y;
    rewrite (cv b (asn1_lc_rel [(id', c)] pm x y) (asn1_raw_lc_rel [(id', c)] pm x (lc_forget [(id', c)] y)))
      as (cv b (asn1_content_rel c pm x (RS.lc_head_val id' c [] y ())) (asn1_raw_content_rel c pm x (forget_content c (RS.lc_head_val id' c [] y ()))));
    cc pm x (RS.lc_head_val id' c [] y ());
    rewrite (cv b (asn1_raw_content_rel c pm x (forget_content c (RS.lc_head_val id' c [] y ()))) (asn1_content_rel c pm x (RS.lc_head_val id' c [] y ())))
      as (cv b (asn1_raw_lc_rel [(id', c)] pm x (lc_forget [(id', c)] y)) (asn1_lc_rel [(id', c)] pm x y))
  } else {
    rewrite (cv b (asn1_lc_rel [(id', c)] pm x y) (asn1_raw_lc_rel [(id', c)] pm x (lc_forget [(id', c)] y))) as (pure False);
    unreachable ()
  }
}

ghost
fn conv_lc_cons (b: bool) (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (cc: conv_t b (asn1_content_rel c) (asn1_raw_content_rel c) (forget_content c))
  (ct: conv_t b (asn1_lc_rel (hd2 :: tl2)) (asn1_raw_lc_rel (hd2 :: tl2)) (lc_forget (hd2 :: tl2)))
: conv_t b (asn1_lc_rel ((id', c) :: hd2 :: tl2)) (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2)) (lc_forget ((id', c) :: hd2 :: tl2))
= (pm: perm) (x: asn1_lc_impl_t ((id', c) :: hd2 :: tl2)) (y: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
{
  lc_forget_dfst ((id', c) :: hd2 :: tl2) y;
  let x' : either (asn1_content_impl_t c) (asn1_lc_impl_t (hd2 :: tl2)) = x;
  match x' {
    Inl a -> {
      RS.lc_cons_inl_eq id' c hd2 tl2 pm a y;
      raw_lc_cons_inl_eq id' c hd2 tl2 pm a (lc_forget ((id', c) :: hd2 :: tl2) y);
      assert (pure (x == RS.lc_inl id' c hd2 tl2 a));
      if (dfst y = id') {
        lc_forget_head id' c (hd2 :: tl2) y;
        rewrite (cv b (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x y) (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm x (lc_forget ((id', c) :: hd2 :: tl2) y)))
          as (cv b (asn1_content_rel c pm a (RS.lc_head_val id' c (hd2 :: tl2) y ())) (asn1_raw_content_rel c pm a (forget_content c (RS.lc_head_val id' c (hd2 :: tl2) y ()))));
        cc pm a (RS.lc_head_val id' c (hd2 :: tl2) y ());
        rewrite (cv b (asn1_raw_content_rel c pm a (forget_content c (RS.lc_head_val id' c (hd2 :: tl2) y ()))) (asn1_content_rel c pm a (RS.lc_head_val id' c (hd2 :: tl2) y ())))
          as (cv b (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm x (lc_forget ((id', c) :: hd2 :: tl2) y)) (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x y))
      } else {
        rewrite (cv b (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x y) (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm x (lc_forget ((id', c) :: hd2 :: tl2) y))) as (pure False);
        unreachable ()
      }
    }
    Inr bb -> {
      RS.lc_cons_inr_eq id' c hd2 tl2 pm bb y;
      raw_lc_cons_inr_eq id' c hd2 tl2 pm bb (lc_forget ((id', c) :: hd2 :: tl2) y);
      assert (pure (x == RS.lc_inr id' c hd2 tl2 bb));
      if (dfst y = id') {
        rewrite (cv b (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x y) (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm x (lc_forget ((id', c) :: hd2 :: tl2) y))) as (pure False);
        unreachable ()
      } else {
        lc_forget_tail (id', c) (hd2 :: tl2) y;
        rewrite (cv b (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x y) (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm x (lc_forget ((id', c) :: hd2 :: tl2) y)))
          as (cv b (asn1_lc_rel (hd2 :: tl2) pm bb (RS.lc_tail_val (id', c) (hd2 :: tl2) y ())) (asn1_raw_lc_rel (hd2 :: tl2) pm bb (lc_forget (hd2 :: tl2) (RS.lc_tail_val (id', c) (hd2 :: tl2) y ()))));
        ct pm bb (RS.lc_tail_val (id', c) (hd2 :: tl2) y ());
        rewrite (cv b (asn1_raw_lc_rel (hd2 :: tl2) pm bb (lc_forget (hd2 :: tl2) (RS.lc_tail_val (id', c) (hd2 :: tl2) y ()))) (asn1_lc_rel (hd2 :: tl2) pm bb (RS.lc_tail_val (id', c) (hd2 :: tl2) y ())))
          as (cv b (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm x (lc_forget ((id', c) :: hd2 :: tl2) y)) (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x y))
      }
    }
  }
}

(* Restricted terminals *)

let restricted_rel_forget (k: asn1_terminal_k) (r: asn1_restriction k) (pm: perm) (x: asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) (y: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r))
: Lemma (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm x y == asn1_raw_terminal_rel k pm x (restricted_forget k r y))
= RS.content_restricted_eq k r pm x y;
  terminal_rel_forget k pm x (RS.restricted_up k r y)

let conv_restricted (b: bool) (k: asn1_terminal_k) (r: asn1_restriction k)
: conv_t b (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (asn1_raw_terminal_rel k) (restricted_forget k r)
= conv_eq b (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (asn1_raw_terminal_rel k) (restricted_forget k r) (restricted_rel_forget k r)

(* ANY DEFINED BY, without a fallback *)

let rady (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Type0 =
  make_gen_choice_type (raw_any_t_core key_k ls)

let rady_head_val (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (v: rady key_k ((kx, y) :: tl)) (sq: squash (dfst v == raw_key_of_lit key_k kx))
: Tot (raw_items_t (dsnd y))
= dsnd v

let rady_tail_val (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (v: rady key_k ((kx, y) :: tl)) (sq: squash (dfst v <> raw_key_of_lit key_k kx))
: Tot (rady key_k tl)
= (| dfst v, dsnd v |)

let raw_adb_single_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (pm: perm)
  (r: asn1_items_impl_t (Mkdtuple2?._2 y)) (key: asn1_raw_terminal_t key_k) (w: idlookup_t key (raw_any_t_core key_k [(kx, y)]))
: Lemma (asn1_raw_adb_rel key_k [(kx, y)] pm r ((| key, w |) <: rady key_k [(kx, y)]) ==
    (if key = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm r (rady_head_val kx y [] ((| key, w |) <: rady key_k [(kx, y)]) ()) else pure False))
= assert (asn1_raw_adb_rel key_k [(kx, y)] pm r ((| key, w |) <: rady key_k [(kx, y)]) ==
    (if key = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm r (rady_head_val kx y [] ((| key, w |) <: rady key_k [(kx, y)]) ()) else pure False))
  by (T.norm [delta_only [`%asn1_raw_adb_rel; `%rady_head_val; `%rady]; zeta; iota]; T.trefl ())

let raw_adb_single_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (pm: perm)
  (r: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: rady key_k [(kx, y)])
: Lemma (asn1_raw_adb_rel key_k [(kx, y)] pm r v ==
    (if dfst v = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm r (rady_head_val kx y [] v ()) else pure False))
= let (| key, w |) = v in
  raw_adb_single_aux kx y pm r key w

let raw_adb_cons_inl_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (key: asn1_raw_terminal_t key_k) (w: idlookup_t key (raw_any_t_core key_k ((kx, y) :: hd2 :: tl2)))
: Lemma (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) a) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm a (rady_head_val kx y (hd2 :: tl2) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ()) else pure False))
= assert (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) a) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm a (rady_head_val kx y (hd2 :: tl2) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ()) else pure False))
  by (T.norm [delta_only [`%asn1_raw_adb_rel; `%rady_head_val; `%rady]; zeta; iota]; T.trefl ())

let raw_adb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: rady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) a) v ==
    (if dfst v = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm a (rady_head_val kx y (hd2 :: tl2) v ()) else pure False))
= let (| key, w |) = v in
  raw_adb_cons_inl_aux kx y hd2 tl2 pm a key w

let raw_adb_cons_inr_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) (key: asn1_raw_terminal_t key_k) (w: idlookup_t key (raw_any_t_core key_k ((kx, y) :: hd2 :: tl2)))
: Lemma (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = raw_key_of_lit key_k kx then pure False else asn1_raw_adb_rel key_k (hd2 :: tl2) pm b (rady_tail_val kx y (hd2 :: tl2) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ())))
= assert (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = raw_key_of_lit key_k kx then pure False else asn1_raw_adb_rel key_k (hd2 :: tl2) pm b (rady_tail_val kx y (hd2 :: tl2) ((| key, w |) <: rady key_k ((kx, y) :: hd2 :: tl2)) ())))
  by (T.norm [delta_only [`%asn1_raw_adb_rel; `%rady_tail_val; `%rady]; zeta; iota]; T.trefl ())

let raw_adb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) (v: rady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b) v ==
    (if dfst v = raw_key_of_lit key_k kx then pure False else asn1_raw_adb_rel key_k (hd2 :: tl2) pm b (rady_tail_val kx y (hd2 :: tl2) v ())))
= let (| key, w |) = v in
  raw_adb_cons_inr_aux kx y hd2 tl2 pm b key w

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let adb_forget_dfst (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (v: AL.ady key_k ls)
: Lemma (dfst (forget_adb_sfx key_k ls v) == forget_terminal key_k (dfst v))
= ()

let adb_forget_head (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (v: AL.ady key_k ((kx, y) :: tl))
: Lemma (requires (dfst v == key_of_lit key_k kx /\ dfst (forget_adb_sfx key_k ((kx, y) :: tl) v) == raw_key_of_lit key_k kx))
  (ensures (rady_head_val kx y tl (forget_adb_sfx key_k ((kx, y) :: tl) v) () == forget_items (dsnd y) (AL.ady_head_val kx y tl v ())))
= ()

let adb_forget_tail (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (v: AL.ady key_k ((kx, y) :: tl))
: Lemma (requires (dfst v <> key_of_lit key_k kx /\ dfst (forget_adb_sfx key_k ((kx, y) :: tl) v) <> raw_key_of_lit key_k kx))
  (ensures (rady_tail_val kx y tl (forget_adb_sfx key_k ((kx, y) :: tl) v) () == forget_adb_sfx key_k tl (AL.ady_tail_val kx y tl v ())))
= ()
#pop-options

let conv_adb_t (b: bool) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Type =
  conv_t b #(asn1_adb_suffix_impl_t key_k ls None) #(AL.ady key_k ls) #(rady key_k ls) (asn1_adb_rel key_k ls) (asn1_raw_adb_rel key_k ls) (forget_adb_sfx key_k ls)

let conv_items_t (b: bool) (#ids: _) (items: asn1_gen_items_l ids) : Type =
  conv_t b (asn1_items_rel items) (asn1_raw_items_rel items) (forget_items items)

ghost
fn conv_adb_nil (b: bool) (key_k: asn1_terminal_k)
: conv_adb_t b key_k []
= (pm: perm) (x: asn1_adb_suffix_impl_t key_k [] None) (y: AL.ady key_k [])
{
  rewrite (cv b (asn1_adb_rel key_k [] pm x y) (asn1_raw_adb_rel key_k [] pm x (forget_adb_sfx key_k [] y))) as (pure False);
  unreachable ()
}

ghost
fn conv_adb_single (b: bool) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (ci: conv_items_t b (dsnd y))
: conv_adb_t b key_k [(kx, y)]
= (pm: perm) (x: asn1_adb_suffix_impl_t key_k [(kx, y)] None) (v: AL.ady key_k [(kx, y)])
{
  RS.adb_single_eq kx y pm x v;
  raw_adb_single_eq kx y pm x (forget_adb_sfx key_k [(kx, y)] v);
  adb_forget_dfst key_k [(kx, y)] v;
  if (dfst v = key_of_lit key_k kx) {
    adb_forget_head kx y [] v;
    rewrite (cv b (asn1_adb_rel key_k [(kx, y)] pm x v) (asn1_raw_adb_rel key_k [(kx, y)] pm x (forget_adb_sfx key_k [(kx, y)] v)))
      as (cv b (asn1_items_rel (dsnd y) pm x (AL.ady_head_val kx y [] v ())) (asn1_raw_items_rel (dsnd y) pm x (forget_items (dsnd y) (AL.ady_head_val kx y [] v ()))));
    ci pm x (AL.ady_head_val kx y [] v ());
    rewrite (cv b (asn1_raw_items_rel (dsnd y) pm x (forget_items (dsnd y) (AL.ady_head_val kx y [] v ()))) (asn1_items_rel (dsnd y) pm x (AL.ady_head_val kx y [] v ())))
      as (cv b (asn1_raw_adb_rel key_k [(kx, y)] pm x (forget_adb_sfx key_k [(kx, y)] v)) (asn1_adb_rel key_k [(kx, y)] pm x v))
  } else {
    forget_key_ne key_k (dfst v) kx;
    rewrite (cv b (asn1_adb_rel key_k [(kx, y)] pm x v) (asn1_raw_adb_rel key_k [(kx, y)] pm x (forget_adb_sfx key_k [(kx, y)] v))) as (pure False);
    unreachable ()
  }
}

ghost
fn conv_adb_cons (b: bool) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (ci: conv_items_t b (dsnd y)) (ct: conv_adb_t b key_k (hd2 :: tl2))
: conv_adb_t b key_k ((kx, y) :: hd2 :: tl2)
= (pm: perm) (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None) (v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
{
  adb_forget_dfst key_k ((kx, y) :: hd2 :: tl2) v;
  let x' : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) = x;
  match x' {
    Inl a -> {
      RS.adb_cons_inl_eq kx y hd2 tl2 pm a v;
      raw_adb_cons_inl_eq kx y hd2 tl2 pm a (forget_adb_sfx key_k ((kx, y) :: hd2 :: tl2) v);
      if (dfst v = key_of_lit key_k kx) {
        adb_forget_head kx y (hd2 :: tl2) v;
        rewrite (cv b (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x (forget_adb_sfx key_k ((kx, y) :: hd2 :: tl2) v)))
          as (cv b (asn1_items_rel (dsnd y) pm a (AL.ady_head_val kx y (hd2 :: tl2) v ())) (asn1_raw_items_rel (dsnd y) pm a (forget_items (dsnd y) (AL.ady_head_val kx y (hd2 :: tl2) v ()))));
        ci pm a (AL.ady_head_val kx y (hd2 :: tl2) v ());
        rewrite (cv b (asn1_raw_items_rel (dsnd y) pm a (forget_items (dsnd y) (AL.ady_head_val kx y (hd2 :: tl2) v ()))) (asn1_items_rel (dsnd y) pm a (AL.ady_head_val kx y (hd2 :: tl2) v ())))
          as (cv b (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x (forget_adb_sfx key_k ((kx, y) :: hd2 :: tl2) v)) (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v))
      } else {
        forget_key_ne key_k (dfst v) kx;
        rewrite (cv b (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x (forget_adb_sfx key_k ((kx, y) :: hd2 :: tl2) v))) as (pure False);
        unreachable ()
      }
    }
    Inr bb -> {
      RS.adb_cons_inr_eq kx y hd2 tl2 pm bb v;
      raw_adb_cons_inr_eq kx y hd2 tl2 pm bb (forget_adb_sfx key_k ((kx, y) :: hd2 :: tl2) v);
      if (dfst v = key_of_lit key_k kx) {
        rewrite (cv b (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x (forget_adb_sfx key_k ((kx, y) :: hd2 :: tl2) v))) as (pure False);
        unreachable ()
      } else {
        forget_key_ne key_k (dfst v) kx;
        adb_forget_tail kx y (hd2 :: tl2) v;
        rewrite (cv b (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x (forget_adb_sfx key_k ((kx, y) :: hd2 :: tl2) v)))
          as (cv b (asn1_adb_rel key_k (hd2 :: tl2) pm bb (AL.ady_tail_val kx y (hd2 :: tl2) v ())) (asn1_raw_adb_rel key_k (hd2 :: tl2) pm bb (forget_adb_sfx key_k (hd2 :: tl2) (AL.ady_tail_val kx y (hd2 :: tl2) v ()))));
        ct pm bb (AL.ady_tail_val kx y (hd2 :: tl2) v ());
        rewrite (cv b (asn1_raw_adb_rel key_k (hd2 :: tl2) pm bb (forget_adb_sfx key_k (hd2 :: tl2) (AL.ady_tail_val kx y (hd2 :: tl2) v ()))) (asn1_adb_rel key_k (hd2 :: tl2) pm bb (AL.ady_tail_val kx y (hd2 :: tl2) v ())))
          as (cv b (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x (forget_adb_sfx key_k ((kx, y) :: hd2 :: tl2) v)) (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v))
      }
    }
  }
}

(* ANY DEFINED BY, with a fallback *)

let raw_fbr (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) : perm -> PA.fbt key_k fb -> asn1_raw_terminal_t key_k -> raw_items_t (dsnd fb) -> slprop =
  fun pm (z: asn1_terminal_impl_t key_k & asn1_items_impl_t (Mkdtuple2?._2 fb)) key (v: raw_items_t (dsnd fb)) ->
    asn1_raw_terminal_rel key_k pm (fst z) key ** asn1_raw_items_rel (dsnd fb) pm (snd z) v

let raw_afb_rel (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) =
  asn1_raw_adb_fb_rel key_k ls (PA.fbt key_k fb) (raw_items_t (dsnd fb)) (raw_fbr key_k fb)

let rady_fb (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) : Type0 =
  make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t (dsnd fb))

let rady_fb_nil_val (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (v: rady_fb key_k [] fb)
: Tot (raw_items_t (dsnd fb))
= dsnd v

let rady_fb_head_val (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (v: rady_fb key_k ((kx, y) :: tl) fb) (sq: squash (dfst v == raw_key_of_lit key_k kx))
: Tot (raw_items_t (dsnd y))
= dsnd v

let rady_fb_tail_val (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (v: rady_fb key_k ((kx, y) :: tl) fb) (sq: squash (dfst v <> raw_key_of_lit key_k kx))
: Tot (rady_fb key_k tl fb)
= (| dfst v, dsnd v |)

let raw_afb_nil_aux (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (pm: perm) (z: PA.fbt key_k fb)
  (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k []) (raw_items_t (dsnd fb)))
: Lemma (raw_afb_rel key_k [] fb pm z ((| key, w |) <: rady_fb key_k [] fb) ==
    (asn1_raw_terminal_rel key_k pm (fst z) key ** asn1_raw_items_rel (dsnd fb) pm (snd z) (rady_fb_nil_val fb ((| key, w |) <: rady_fb key_k [] fb))))
= assert (raw_afb_rel key_k [] fb pm z ((| key, w |) <: rady_fb key_k [] fb) ==
    (asn1_raw_terminal_rel key_k pm (fst z) key ** asn1_raw_items_rel (dsnd fb) pm (snd z) (rady_fb_nil_val fb ((| key, w |) <: rady_fb key_k [] fb))))
  by (T.norm [delta_only [`%raw_afb_rel; `%asn1_raw_adb_fb_rel; `%raw_fbr; `%rady_fb_nil_val; `%rady_fb; `%dsnd]; zeta; iota]; T.trefl ())

let raw_afb_nil_eq (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (pm: perm) (z: PA.fbt key_k fb) (v: rady_fb key_k [] fb)
: Lemma (raw_afb_rel key_k [] fb pm z v ==
    (asn1_raw_terminal_rel key_k pm (fst z) (dfst v) ** asn1_raw_items_rel (dsnd fb) pm (snd z) (rady_fb_nil_val fb v)))
= let (| key, w |) = v in
  raw_afb_nil_aux fb pm z key w

let raw_afb_single_inl_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k [(kx, y)]) (raw_items_t (dsnd fb)))
: Lemma (raw_afb_rel key_k [(kx, y)] fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) a) ((| key, w |) <: rady_fb key_k [(kx, y)] fb) ==
    (if key = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm a (rady_fb_head_val kx y [] fb ((| key, w |) <: rady_fb key_k [(kx, y)] fb) ()) else pure False))
= assert (raw_afb_rel key_k [(kx, y)] fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) a) ((| key, w |) <: rady_fb key_k [(kx, y)] fb) ==
    (if key = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm a (rady_fb_head_val kx y [] fb ((| key, w |) <: rady_fb key_k [(kx, y)] fb) ()) else pure False))
  by (T.norm [delta_only [`%raw_afb_rel; `%asn1_raw_adb_fb_rel; `%rady_fb_head_val; `%rady_fb]; zeta; iota]; T.trefl ())

let raw_afb_single_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: rady_fb key_k [(kx, y)] fb)
: Lemma (raw_afb_rel key_k [(kx, y)] fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) a) v ==
    (if dfst v = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm a (rady_fb_head_val kx y [] fb v ()) else pure False))
= let (| key, w |) = v in
  raw_afb_single_inl_aux kx y fb pm a key w

let raw_fbr_eq (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (pm: perm) (z: PA.fbt key_k fb) (key: asn1_raw_terminal_t key_k) (v: raw_items_t (dsnd fb))
: Lemma (raw_fbr key_k fb pm z key v == (asn1_raw_terminal_rel key_k pm (fst z) key ** asn1_raw_items_rel (dsnd fb) pm (snd z) v))
= ()

let raw_afb_single_inr_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (bb: PA.fbt key_k fb) (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k [(kx, y)]) (raw_items_t (dsnd fb)))
: Lemma (raw_afb_rel key_k [(kx, y)] fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) bb) ((| key, w |) <: rady_fb key_k [(kx, y)] fb) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_fbr key_k fb pm bb key (rady_fb_nil_val fb (rady_fb_tail_val kx y [] fb ((| key, w |) <: rady_fb key_k [(kx, y)] fb) ()))))
= assert (raw_afb_rel key_k [(kx, y)] fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) bb) ((| key, w |) <: rady_fb key_k [(kx, y)] fb) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_fbr key_k fb pm bb key (rady_fb_nil_val fb (rady_fb_tail_val kx y [] fb ((| key, w |) <: rady_fb key_k [(kx, y)] fb) ()))))
  by (T.norm [delta_only [`%raw_afb_rel; `%asn1_raw_adb_fb_rel; `%rady_fb_tail_val; `%rady_fb_nil_val; `%rady_fb]; zeta; iota]; T.trefl ())

let raw_afb_single_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (bb: PA.fbt key_k fb) (v: rady_fb key_k [(kx, y)] fb)
: Lemma (raw_afb_rel key_k [(kx, y)] fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) bb) v ==
    (if dfst v = raw_key_of_lit key_k kx then pure False else raw_afb_rel key_k [] fb pm bb (rady_fb_tail_val kx y [] fb v ())))
= let (| key, w |) = v in
  raw_afb_single_inr_aux kx y fb pm bb key w;
  if key = raw_key_of_lit key_k kx then ()
  else begin
    let tv = rady_fb_tail_val kx y [] fb v () in
    raw_afb_nil_eq fb pm bb tv;
    raw_fbr_eq key_k fb pm bb key (rady_fb_nil_val fb tv)
  end

let raw_afb_cons_inl_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k ((kx, y) :: hd2 :: tl2)) (raw_items_t (dsnd fb)))
: Lemma (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) a) ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb) ==
    (if key = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm a (rady_fb_head_val kx y (hd2 :: tl2) fb ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb) ()) else pure False))
= assert (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) a) ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb) ==
    (if key = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm a (rady_fb_head_val kx y (hd2 :: tl2) fb ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb) ()) else pure False))
  by (T.norm [delta_only [`%raw_afb_rel; `%asn1_raw_adb_fb_rel; `%rady_fb_head_val; `%rady_fb]; zeta; iota]; T.trefl ())

let raw_afb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
: Lemma (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) a) v ==
    (if dfst v = raw_key_of_lit key_k kx then asn1_raw_items_rel (dsnd y) pm a (rady_fb_head_val kx y (hd2 :: tl2) fb v ()) else pure False))
= let (| key, w |) = v in
  raw_afb_cons_inl_aux kx y hd2 tl2 fb pm a key w

let raw_afb_cons_inr_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (bb: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) (key: asn1_raw_terminal_t key_k) (w: idlookup_with_fallback_t key (raw_any_t_core key_k ((kx, y) :: hd2 :: tl2)) (raw_items_t (dsnd fb)))
: Lemma (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) bb) ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_afb_rel key_k (hd2 :: tl2) fb pm bb (rady_fb_tail_val kx y (hd2 :: tl2) fb ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb) ())))
= assert (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) bb) ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb) ==
    (if key = raw_key_of_lit key_k kx then pure False else raw_afb_rel key_k (hd2 :: tl2) fb pm bb (rady_fb_tail_val kx y (hd2 :: tl2) fb ((| key, w |) <: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb) ())))
  by (T.norm [delta_only [`%raw_afb_rel; `%asn1_raw_adb_fb_rel; `%rady_fb_tail_val; `%rady_fb]; zeta; iota]; T.trefl ())

let raw_afb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (bb: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) (v: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
: Lemma (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) bb) v ==
    (if dfst v = raw_key_of_lit key_k kx then pure False else raw_afb_rel key_k (hd2 :: tl2) fb pm bb (rady_fb_tail_val kx y (hd2 :: tl2) fb v ())))
= let (| key, w |) = v in
  raw_afb_cons_inr_aux kx y hd2 tl2 fb pm bb key w

(* The typed side, with `[]` for the single-alternative fallback case *)

let afb_single_inr_eq' (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (bb: PA.fbt key_k fb) (v: AL.ady_fb key_k [(kx, y)] fb)
: Lemma (PA.afb_rel key_k [(kx, y)] fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) bb) v ==
    (if dfst v = key_of_lit key_k kx then pure False else PA.afb_rel key_k [] fb pm bb (AL.ady_fb_tail_val kx y [] fb v ())))
= RS.afb_single_inr_eq kx y fb pm bb v;
  if dfst v = key_of_lit key_k kx then ()
  else RS.afb_nil_eq fb pm bb (AL.ady_fb_tail_val kx y [] fb v ())

let afb_forget (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (sq: squash (ls << k0 /\ dsnd fb << k0)) (v: AL.ady_fb key_k ls fb)
: Tot (rady_fb key_k ls fb)
= forget_adb_fb_sfx k0 key_k ls (dsnd fb) v

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let afb_forget_dfst (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (sq: squash (ls << k0 /\ dsnd fb << k0)) (v: AL.ady_fb key_k ls fb)
: Lemma (dfst (afb_forget k0 key_k ls fb sq v) == forget_terminal key_k (dfst v))
= ()

let afb_forget_nil (k0: asn1_content_k) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk)
  (sq: squash ([] << k0 /\ dsnd fb << k0)) (v: AL.ady_fb key_k [] fb)
: Lemma (rady_fb_nil_val fb (afb_forget k0 key_k [] fb sq v) == forget_items (dsnd fb) (AL.ady_fb_nil_val fb v))
= ()

let afb_forget_head (k0: asn1_content_k) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (sq: squash (((kx, y) :: tl) << k0 /\ dsnd fb << k0)) (v: AL.ady_fb key_k ((kx, y) :: tl) fb)
: Lemma (requires (dfst v == key_of_lit key_k kx /\ dfst (afb_forget k0 key_k ((kx, y) :: tl) fb sq v) == raw_key_of_lit key_k kx))
  (ensures (rady_fb_head_val kx y tl fb (afb_forget k0 key_k ((kx, y) :: tl) fb sq v) () == forget_items (dsnd y) (AL.ady_fb_head_val kx y tl fb v ())))
= ()

let afb_forget_tail (k0: asn1_content_k) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (sq: squash (((kx, y) :: tl) << k0 /\ dsnd fb << k0)) (v: AL.ady_fb key_k ((kx, y) :: tl) fb)
: Lemma (requires (dfst v <> key_of_lit key_k kx /\ dfst (afb_forget k0 key_k ((kx, y) :: tl) fb sq v) <> raw_key_of_lit key_k kx))
  (ensures (rady_fb_tail_val kx y tl fb (afb_forget k0 key_k ((kx, y) :: tl) fb sq v) () == afb_forget k0 key_k tl fb () (AL.ady_fb_tail_val kx y tl fb v ())))
= ()
#pop-options

let conv_afb_t (b: bool) (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (sq: squash (ls << k0 /\ dsnd fb << k0))
: Type
= conv_t b #(asn1_adb_suffix_impl_t key_k ls (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k ls fb) #(rady_fb key_k ls fb) (PA.afb_rel key_k ls fb) (raw_afb_rel key_k ls fb) (afb_forget k0 key_k ls fb sq)

ghost
fn conv_afb_nil (b: bool) (k0: asn1_content_k) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (sq: squash ([] << k0 /\ dsnd fb << k0))
  (ci: conv_items_t b (dsnd fb))
: conv_afb_t b k0 key_k [] fb sq
= (pm: perm) (z: asn1_adb_suffix_impl_t key_k [] (Some (PA.fbt key_k fb))) (v: AL.ady_fb key_k [] fb)
{
  let z' : PA.fbt key_k fb = z;
  RS.afb_nil_eq fb pm z' v;
  RS.fbr_eq key_k fb pm z' (dfst v) (AL.ady_fb_nil_val fb v);
  raw_afb_nil_eq fb pm z' (afb_forget k0 key_k [] fb sq v);
  afb_forget_dfst k0 key_k [] fb sq v;
  afb_forget_nil k0 key_k fb sq v;
  cv_star b (asn1_terminal_rel key_k pm (fst z') (dfst v)) (asn1_items_rel (dsnd fb) pm (snd z') (AL.ady_fb_nil_val fb v))
    (asn1_raw_terminal_rel key_k pm (fst z') (forget_terminal key_k (dfst v))) (asn1_raw_items_rel (dsnd fb) pm (snd z') (forget_items (dsnd fb) (AL.ady_fb_nil_val fb v)));
  rewrite (cv b (PA.afb_rel key_k [] fb pm z v) (raw_afb_rel key_k [] fb pm z (afb_forget k0 key_k [] fb sq v)))
    as (cv b (asn1_terminal_rel key_k pm (fst z') (dfst v)) (asn1_raw_terminal_rel key_k pm (fst z') (forget_terminal key_k (dfst v))) **
        cv b (asn1_items_rel (dsnd fb) pm (snd z') (AL.ady_fb_nil_val fb v)) (asn1_raw_items_rel (dsnd fb) pm (snd z') (forget_items (dsnd fb) (AL.ady_fb_nil_val fb v))));
  conv_terminal b key_k pm (fst z') (dfst v);
  ci pm (snd z') (AL.ady_fb_nil_val fb v);
  cv_star b (asn1_raw_terminal_rel key_k pm (fst z') (forget_terminal key_k (dfst v))) (asn1_raw_items_rel (dsnd fb) pm (snd z') (forget_items (dsnd fb) (AL.ady_fb_nil_val fb v)))
    (asn1_terminal_rel key_k pm (fst z') (dfst v)) (asn1_items_rel (dsnd fb) pm (snd z') (AL.ady_fb_nil_val fb v));
  rewrite (cv b (asn1_raw_terminal_rel key_k pm (fst z') (forget_terminal key_k (dfst v))) (asn1_terminal_rel key_k pm (fst z') (dfst v)) **
        cv b (asn1_raw_items_rel (dsnd fb) pm (snd z') (forget_items (dsnd fb) (AL.ady_fb_nil_val fb v))) (asn1_items_rel (dsnd fb) pm (snd z') (AL.ady_fb_nil_val fb v)))
    as (cv b (raw_afb_rel key_k [] fb pm z (afb_forget k0 key_k [] fb sq v)) (PA.afb_rel key_k [] fb pm z v))
}

ghost
fn conv_afb_single (b: bool) (k0: asn1_content_k) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk)
  (sq: squash ([(kx, y)] << k0 /\ dsnd fb << k0))
  (ci: conv_items_t b (dsnd y)) (cn: conv_afb_t b k0 key_k [] fb ())
: conv_afb_t b k0 key_k [(kx, y)] fb sq
= (pm: perm) (x: asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb))) (v: AL.ady_fb key_k [(kx, y)] fb)
{
  afb_forget_dfst k0 key_k [(kx, y)] fb sq v;
  let x' : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (PA.fbt key_k fb) = x;
  match x' {
    Inl a -> {
      RS.afb_single_inl_eq kx y fb pm a v;
      raw_afb_single_inl_eq kx y fb pm a (afb_forget k0 key_k [(kx, y)] fb sq v);
      if (dfst v = key_of_lit key_k kx) {
        afb_forget_head k0 kx y [] fb sq v;
        rewrite (cv b (PA.afb_rel key_k [(kx, y)] fb pm x v) (raw_afb_rel key_k [(kx, y)] fb pm x (afb_forget k0 key_k [(kx, y)] fb sq v)))
          as (cv b (asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val kx y [] fb v ())) (asn1_raw_items_rel (dsnd y) pm a (forget_items (dsnd y) (AL.ady_fb_head_val kx y [] fb v ()))));
        ci pm a (AL.ady_fb_head_val kx y [] fb v ());
        rewrite (cv b (asn1_raw_items_rel (dsnd y) pm a (forget_items (dsnd y) (AL.ady_fb_head_val kx y [] fb v ()))) (asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val kx y [] fb v ())))
          as (cv b (raw_afb_rel key_k [(kx, y)] fb pm x (afb_forget k0 key_k [(kx, y)] fb sq v)) (PA.afb_rel key_k [(kx, y)] fb pm x v))
      } else {
        forget_key_ne key_k (dfst v) kx;
        rewrite (cv b (PA.afb_rel key_k [(kx, y)] fb pm x v) (raw_afb_rel key_k [(kx, y)] fb pm x (afb_forget k0 key_k [(kx, y)] fb sq v))) as (pure False);
        unreachable ()
      }
    }
    Inr bb -> {
      afb_single_inr_eq' kx y fb pm bb v;
      raw_afb_single_inr_eq kx y fb pm bb (afb_forget k0 key_k [(kx, y)] fb sq v);
      if (dfst v = key_of_lit key_k kx) {
        rewrite (cv b (PA.afb_rel key_k [(kx, y)] fb pm x v) (raw_afb_rel key_k [(kx, y)] fb pm x (afb_forget k0 key_k [(kx, y)] fb sq v))) as (pure False);
        unreachable ()
      } else {
        forget_key_ne key_k (dfst v) kx;
        afb_forget_tail k0 kx y [] fb sq v;
        rewrite (cv b (PA.afb_rel key_k [(kx, y)] fb pm x v) (raw_afb_rel key_k [(kx, y)] fb pm x (afb_forget k0 key_k [(kx, y)] fb sq v)))
          as (cv b (PA.afb_rel key_k [] fb pm bb (AL.ady_fb_tail_val kx y [] fb v ())) (raw_afb_rel key_k [] fb pm bb (afb_forget k0 key_k [] fb () (AL.ady_fb_tail_val kx y [] fb v ()))));
        cn pm bb (AL.ady_fb_tail_val kx y [] fb v ());
        rewrite (cv b (raw_afb_rel key_k [] fb pm bb (afb_forget k0 key_k [] fb () (AL.ady_fb_tail_val kx y [] fb v ()))) (PA.afb_rel key_k [] fb pm bb (AL.ady_fb_tail_val kx y [] fb v ())))
          as (cv b (raw_afb_rel key_k [(kx, y)] fb pm x (afb_forget k0 key_k [(kx, y)] fb sq v)) (PA.afb_rel key_k [(kx, y)] fb pm x v))
      }
    }
  }
}

ghost
fn conv_afb_cons (b: bool) (k0: asn1_content_k) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (sq: squash (((kx, y) :: hd2 :: tl2) << k0 /\ dsnd fb << k0))
  (ci: conv_items_t b (dsnd y)) (ct: conv_afb_t b k0 key_k (hd2 :: tl2) fb ())
: conv_afb_t b k0 key_k ((kx, y) :: hd2 :: tl2) fb sq
= (pm: perm) (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb))) (v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
{
  afb_forget_dfst k0 key_k ((kx, y) :: hd2 :: tl2) fb sq v;
  let x' : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) = x;
  match x' {
    Inl a -> {
      RS.afb_cons_inl_eq kx y hd2 tl2 fb pm a v;
      raw_afb_cons_inl_eq kx y hd2 tl2 fb pm a (afb_forget k0 key_k ((kx, y) :: hd2 :: tl2) fb sq v);
      if (dfst v = key_of_lit key_k kx) {
        afb_forget_head k0 kx y (hd2 :: tl2) fb sq v;
        rewrite (cv b (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x (afb_forget k0 key_k ((kx, y) :: hd2 :: tl2) fb sq v)))
          as (cv b (asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ())) (asn1_raw_items_rel (dsnd y) pm a (forget_items (dsnd y) (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ()))));
        ci pm a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ());
        rewrite (cv b (asn1_raw_items_rel (dsnd y) pm a (forget_items (dsnd y) (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ()))) (asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ())))
          as (cv b (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x (afb_forget k0 key_k ((kx, y) :: hd2 :: tl2) fb sq v)) (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v))
      } else {
        forget_key_ne key_k (dfst v) kx;
        rewrite (cv b (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x (afb_forget k0 key_k ((kx, y) :: hd2 :: tl2) fb sq v))) as (pure False);
        unreachable ()
      }
    }
    Inr bb -> {
      RS.afb_cons_inr_eq kx y hd2 tl2 fb pm bb v;
      raw_afb_cons_inr_eq kx y hd2 tl2 fb pm bb (afb_forget k0 key_k ((kx, y) :: hd2 :: tl2) fb sq v);
      if (dfst v = key_of_lit key_k kx) {
        rewrite (cv b (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x (afb_forget k0 key_k ((kx, y) :: hd2 :: tl2) fb sq v))) as (pure False);
        unreachable ()
      } else {
        forget_key_ne key_k (dfst v) kx;
        afb_forget_tail k0 kx y (hd2 :: tl2) fb sq v;
        rewrite (cv b (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x (afb_forget k0 key_k ((kx, y) :: hd2 :: tl2) fb sq v)))
          as (cv b (PA.afb_rel key_k (hd2 :: tl2) fb pm bb (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ())) (raw_afb_rel key_k (hd2 :: tl2) fb pm bb (afb_forget k0 key_k (hd2 :: tl2) fb () (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ()))));
        ct pm bb (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ());
        rewrite (cv b (raw_afb_rel key_k (hd2 :: tl2) fb pm bb (afb_forget k0 key_k (hd2 :: tl2) fb () (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ()))) (PA.afb_rel key_k (hd2 :: tl2) fb pm bb (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ())))
          as (cv b (raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x (afb_forget k0 key_k ((kx, y) :: hd2 :: tl2) fb sq v)) (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v))
      }
    }
  }
}

(* ANY DEFINED BY, at the content level *)

let raw_adb_rel_none_eq (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (pm: perm) (x: asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls None)) (y: raw_items_any_t prefix (rady key_k ls))
: Lemma (asn1_raw_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf') pm x y == asn1_raw_items_any_rel prefix (asn1_raw_adb_rel key_k ls) pm x y)
= assert (asn1_raw_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf') pm x y == asn1_raw_items_any_rel prefix (asn1_raw_adb_rel key_k ls) pm x y)
    by (T.norm [delta_only [`%PA.adb_k_none; `%asn1_raw_content_rel]; zeta; iota]; T.trefl ())

let raw_adb_rel_some_eq (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (pm: perm) (x: asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls (Some (PA.fbt key_k fb)))) (y: raw_items_any_t prefix (rady_fb key_k ls fb))
: Lemma (asn1_raw_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf') pm x y == asn1_raw_items_any_rel prefix (raw_afb_rel key_k ls fb) pm x y)
= assert (asn1_raw_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf') pm x y == asn1_raw_items_any_rel prefix (raw_afb_rel key_k ls fb) pm x y)
    by (T.norm [delta_only [`%PA.adb_k_some; `%asn1_raw_content_rel; `%raw_afb_rel; `%PA.fbt; `%raw_fbr; `%rady_fb]; zeta; iota]; T.trefl ())

let raw_adb_none_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma (pequiv
    #(asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls None))
    #(raw_items_any_t prefix (rady key_k ls))
    (asn1_raw_items_any_rel prefix (asn1_raw_adb_rel key_k ls))
    (asn1_raw_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf')))
= Classical.forall_intro_3 (raw_adb_rel_none_eq ipd prefix kid key_k ls pf pf')

let raw_adb_some_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma (pequiv
    #(asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls (Some (PA.fbt key_k fb))))
    #(raw_items_any_t prefix (rady_fb key_k ls fb))
    (asn1_raw_items_any_rel prefix (raw_afb_rel key_k ls fb))
    (asn1_raw_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf')))
= Classical.forall_intro_3 (raw_adb_rel_some_eq ipd prefix kid key_k ls fb pf pf')

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let forget_content_adb_none (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma (forall (y: asn1_sequence_any_t_core prefix (AL.ady key_k ls)) .
    forget_content (PA.adb_k_none ipd prefix kid key_k ls pf pf') y ==
    items_any_forget prefix #(AL.ady key_k ls) #(rady key_k ls) (forget_adb_sfx key_k ls) y)
= ()

let forget_content_adb_some (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (sq: squash (ls << PA.adb_k_some ipd prefix kid key_k ls fb pf pf' /\ dsnd fb << PA.adb_k_some ipd prefix kid key_k ls fb pf pf'))
: Lemma (forall (y: asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb)) .
    forget_content (PA.adb_k_some ipd prefix kid key_k ls fb pf pf') y ==
    items_any_forget prefix #(AL.ady_fb key_k ls fb) #(rady_fb key_k ls fb) (afb_forget (PA.adb_k_some ipd prefix kid key_k ls fb pf pf') key_k ls fb sq) y)
= ()
#pop-options

let conv_items_any_t (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (#sfxi: Type0) (#sfxs #rsfx: Type0)
  (sfxr: prel sfxi sfxs) (rsfxr: prel sfxi rsfx) (fs: sfxs -> rsfx)
: Type
= conv_t b #(asn1_items_any_impl_t items sfxi) #(asn1_sequence_any_t_core items sfxs) #(raw_items_any_t items rsfx)
    (asn1_items_any_rel items sfxr) (asn1_raw_items_any_rel items rsfxr) (items_any_forget items fs)

(* The conversions of a whole schema *)

let rec conv_content (b: bool) (k: asn1_content_k)
: Tot (conv_t b (asn1_content_rel k) (asn1_raw_content_rel k) (forget_content k)) (decreases k)
= match k with
  | ASN1_TERMINAL k' ->
    RS.content_terminal_equiv k';
    raw_content_terminal_equiv k';
    forget_content_terminal k';
    conv_ext b (asn1_terminal_rel k') (asn1_content_rel (ASN1_TERMINAL k')) (asn1_raw_terminal_rel k') (asn1_raw_content_rel (ASN1_TERMINAL k'))
      (forget_terminal k') (forget_content (ASN1_TERMINAL k')) () (conv_terminal b k')
  | ASN1_RESTRICTED_TERMINAL k' r ->
    raw_content_restricted_equiv k' r;
    forget_content_restricted k' r;
    conv_ext b (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (asn1_raw_terminal_rel k') (asn1_raw_content_rel (ASN1_RESTRICTED_TERMINAL k' r))
      (restricted_forget k' r) (forget_content (ASN1_RESTRICTED_TERMINAL k' r)) () (conv_restricted b k' r)
  | ASN1_PREFIXED k' ->
    RS.content_prefixed_equiv k';
    raw_content_prefixed_equiv k';
    forget_content_prefixed k';
    conv_ext b (asn1_rel k') (asn1_content_rel (ASN1_PREFIXED k')) (asn1_raw_rel k') (asn1_raw_content_rel (ASN1_PREFIXED k'))
      (forget k') (forget_content (ASN1_PREFIXED k')) () (conv_k b k')
  | ASN1_SEQUENCE gitems ->
    RS.content_sequence_equiv gitems;
    raw_content_sequence_equiv gitems;
    forget_content_sequence gitems;
    conv_ext b (asn1_items_rel (dsnd gitems)) (asn1_content_rel (ASN1_SEQUENCE gitems)) (asn1_raw_items_rel (dsnd gitems)) (asn1_raw_content_rel (ASN1_SEQUENCE gitems))
      (forget_items (dsnd gitems)) (forget_content (ASN1_SEQUENCE gitems)) () (conv_items b (dsnd gitems))
  | ASN1_SET ids items pf ->
    RS.content_set_equiv ids items pf;
    raw_content_set_equiv ids items pf;
    forget_content_set ids items pf;
    conv_ext b (asn1_items_rel items) (asn1_content_rel (ASN1_SET ids items pf)) (asn1_raw_items_rel items) (asn1_raw_content_rel (ASN1_SET ids items pf))
      (forget_items items) (forget_content (ASN1_SET ids items pf)) () (conv_items b items)
  | ASN1_SEQUENCE_OF ne k' -> conv_seq_of b ne k' (conv_k b k')
  | ASN1_SET_OF ne k' -> conv_set_of b ne k' (conv_k b k')
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None ->
      RS.adb_none_equiv ipd prefix kid key_k ls pf pf';
      raw_adb_none_equiv ipd prefix kid key_k ls pf pf';
      forget_content_adb_none ipd prefix kid key_k ls pf pf';
      conv_ext b
        (asn1_items_any_rel prefix (asn1_adb_rel key_k ls)) (asn1_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf'))
        (asn1_raw_items_any_rel prefix (asn1_raw_adb_rel key_k ls)) (asn1_raw_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf'))
        (items_any_forget prefix #(AL.ady key_k ls) #(rady key_k ls) (forget_adb_sfx key_k ls)) (forget_content (PA.adb_k_none ipd prefix kid key_k ls pf pf')) ()
        (conv_items_any b prefix (asn1_adb_rel key_k ls) (asn1_raw_adb_rel key_k ls) (forget_adb_sfx key_k ls) (conv_adb b key_k ls))
    | Some fb ->
      fb_precedes k;
      let sq : squash (ls << PA.adb_k_some ipd prefix kid key_k ls fb pf pf' /\ dsnd fb << PA.adb_k_some ipd prefix kid key_k ls fb pf pf') = () in
      RS.adb_some_equiv ipd prefix kid key_k ls fb pf pf';
      raw_adb_some_equiv ipd prefix kid key_k ls fb pf pf';
      forget_content_adb_some ipd prefix kid key_k ls fb pf pf' sq;
      conv_ext b
        (asn1_items_any_rel prefix (PA.afb_rel key_k ls fb)) (asn1_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf'))
        (asn1_raw_items_any_rel prefix (raw_afb_rel key_k ls fb)) (asn1_raw_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf'))
        (items_any_forget prefix #(AL.ady_fb key_k ls fb) #(rady_fb key_k ls fb) (afb_forget (PA.adb_k_some ipd prefix kid key_k ls fb pf pf') key_k ls fb sq))
        (forget_content (PA.adb_k_some ipd prefix kid key_k ls fb pf pf')) ()
        (conv_items_any b prefix (PA.afb_rel key_k ls fb) (raw_afb_rel key_k ls fb) (afb_forget (PA.adb_k_some ipd prefix kid key_k ls fb pf pf') key_k ls fb sq)
          (conv_afb b (PA.adb_k_some ipd prefix kid key_k ls fb pf pf') key_k ls fb sq (conv_items b (dsnd fb))))
    end

and conv_adb (b: bool) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Tot (conv_adb_t b key_k ls) (decreases ls)
= match ls with
  | [] -> conv_adb_nil b key_k
  | [(kx, y)] -> conv_adb_single b kx y (conv_items b (dsnd y))
  | (kx, y) :: hd2 :: tl2 -> conv_adb_cons b kx y hd2 tl2 (conv_items b (dsnd y)) (conv_adb b key_k (hd2 :: tl2))

and conv_afb (b: bool) (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (sq: squash (ls << k0 /\ dsnd fb << k0)) (ci: conv_items_t b (dsnd fb))
: Tot (conv_afb_t b k0 key_k ls fb sq) (decreases ls)
= match ls with
  | [] -> conv_afb_nil b k0 key_k fb sq ci
  | [(kx, y)] -> conv_afb_single b k0 kx y fb sq (conv_items b (dsnd y)) (conv_afb b k0 key_k [] fb () ci)
  | (kx, y) :: hd2 :: tl2 -> conv_afb_cons b k0 kx y hd2 tl2 fb sq (conv_items b (dsnd y)) (conv_afb b k0 key_k (hd2 :: tl2) fb () ci)

and conv_items_any (b: bool) (#i: _) (ls: asn1_gen_items_l i) (#sfxi: Type0) (#sfxs #rsfx: Type0)
  (sfxr: prel sfxi sfxs) (rsfxr: prel sfxi rsfx) (fs: sfxs -> rsfx) (cs: conv_t b sfxr rsfxr fs)
: Tot (conv_items_any_t b ls sfxr rsfxr fs) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    RS.items_any_nil_equiv sfxr;
    raw_items_any_nil_equiv rsfxr;
    forget_items_any_nil #sfxs #rsfx fs;
    conv_ext b sfxr (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr) rsfxr (asn1_raw_items_any_rel ASN1_GEN_ITEMS_NIL rsfxr)
      fs (items_any_forget ASN1_GEN_ITEMS_NIL fs) () cs
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    RS.items_any_single_equiv dk sfxr;
    raw_items_any_single_equiv dk rsfxr;
    forget_items_any_single dk #sfxs #rsfx fs;
    conv_ext b (prel_pair (asn1_decorated_rel dk) sfxr) (asn1_items_any_rel (PS.single dk) sfxr)
      (prel_pair (asn1_raw_decorated_rel dk) rsfxr) (asn1_raw_items_any_rel (PS.single dk) rsfxr)
      (pair_map (forget_dec dk) fs) (items_any_forget (PS.single dk) fs) ()
      (conv_pair b (asn1_decorated_rel dk) (asn1_raw_decorated_rel dk) (forget_dec dk) sfxr rsfxr fs (conv_dec b dk) cs)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    RS.items_any_cons_equiv dk dk2 tl2 sfxr;
    raw_items_any_cons_equiv dk dk2 tl2 rsfxr;
    forget_items_any_cons dk dk2 tl2 #sfxs #rsfx fs;
    conv_ext b
      (prel_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr)) (asn1_items_any_rel (PS.cons2 dk dk2 tl2) sfxr)
      (prel_pair (asn1_raw_decorated_rel dk) (asn1_raw_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) rsfxr)) (asn1_raw_items_any_rel (PS.cons2 dk dk2 tl2) rsfxr)
      (pair_map (forget_dec dk) (items_any_forget (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) fs)) (items_any_forget (PS.cons2 dk dk2 tl2) fs) ()
      (conv_pair b (asn1_decorated_rel dk) (asn1_raw_decorated_rel dk) (forget_dec dk)
        (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr) (asn1_raw_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) rsfxr) (items_any_forget (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) fs)
        (conv_dec b dk) (conv_items_any b (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr rsfxr fs cs))

and conv_lc (b: bool) (lc: list (asn1_id_t & asn1_content_k))
: Tot (conv_t b (asn1_lc_rel lc) (asn1_raw_lc_rel lc) (lc_forget lc)) (decreases lc)
= match lc with
  | [] -> conv_lc_nil b
  | [(id', c)] -> conv_lc_single b id' c (conv_content b c)
  | (id', c) :: hd2 :: tl2 -> conv_lc_cons b id' c hd2 tl2 (conv_content b c) (conv_lc b (hd2 :: tl2))

and conv_k (b: bool) (#s: _) (k: asn1_k s)
: Tot (conv_t b (asn1_rel k) (asn1_raw_rel k) (forget k)) (decreases k)
= match k with
  | ASN1_ILC id k' ->
    RS.rel_ilc_equiv id k';
    raw_rel_ilc_equiv id k';
    forget_ilc id k';
    conv_ext b (asn1_content_rel k') (asn1_rel (ASN1_ILC id k')) (asn1_raw_content_rel k') (asn1_raw_rel (ASN1_ILC id k'))
      (forget_content k') (forget (ASN1_ILC id k')) () (conv_content b k')
  | ASN1_CHOICE_ILC lc pf ->
    RS.rel_choice_equiv lc pf;
    raw_rel_choice_equiv lc pf;
    forget_choice_ilc lc pf;
    conv_ext b (asn1_lc_rel lc) (asn1_rel (ASN1_CHOICE_ILC lc pf)) (asn1_raw_lc_rel lc) (asn1_raw_rel (ASN1_CHOICE_ILC lc pf))
      (lc_forget lc) (forget (ASN1_CHOICE_ILC lc pf)) () (conv_lc b lc)
  | ASN1_ANY_ILC ->
    RS.rel_any_equiv ();
    raw_rel_any_equiv ();
    forget_any ();
    conv_ext b (prel_slice_ser asn1_value_enc) (asn1_rel ASN1_ANY_ILC) (prel_slice_ser asn1_value_enc) (asn1_raw_rel ASN1_ANY_ILC)
      (fun y -> y) (forget ASN1_ANY_ILC) () (conv_eq b (prel_slice_ser asn1_value_enc) (prel_slice_ser asn1_value_enc) (fun y -> y) (fun _ _ _ -> ()))

and conv_dec (b: bool) (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Tot (conv_t b (asn1_decorated_rel dk) (asn1_raw_decorated_rel dk) (forget_dec dk)) (decreases dk)
= match dk with
  | ASN1_PLAIN_ILC k ->
    RS.dec_plain_equiv k;
    raw_dec_plain_equiv k;
    forget_dec_plain k;
    conv_ext b (asn1_rel k) (asn1_decorated_rel (ASN1_PLAIN_ILC k)) (asn1_raw_rel k) (asn1_raw_decorated_rel (ASN1_PLAIN_ILC k))
      (forget k) (forget_dec (ASN1_PLAIN_ILC k)) () (conv_k b k)
  | ASN1_OPTION_ILC k ->
    RS.dec_option_equiv k;
    raw_dec_option_equiv k;
    forget_dec_option k;
    conv_ext b (prel_option (asn1_rel k)) (asn1_decorated_rel (ASN1_OPTION_ILC k)) (prel_option (asn1_raw_rel k)) (asn1_raw_decorated_rel (ASN1_OPTION_ILC k))
      (omap (forget k)) (forget_dec (ASN1_OPTION_ILC k)) () (conv_option b (asn1_rel k) (asn1_raw_rel k) (forget k) (conv_k b k))
  | ASN1_DEFAULT_TERMINAL id0 #k defv ->
    RS.dec_default_equiv id0 defv;
    raw_dec_default_equiv id0 defv;
    forget_dec_default id0 defv;
    conv_ext b (RS.prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv))
      (prel_option (asn1_raw_terminal_rel k)) (asn1_raw_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv))
      (dmap #(asn1_terminal_t k) #(key_of_lit k defv) (forget_terminal k)) (forget_dec (ASN1_DEFAULT_TERMINAL id0 #k defv)) ()
      (conv_default b (asn1_terminal_rel k) (key_of_lit k defv) (asn1_raw_terminal_rel k) (forget_terminal k) (conv_terminal b k))
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv ->
    RS.dec_default_restricted_equiv id0 r defv;
    raw_dec_default_restricted_equiv id0 r defv;
    forget_dec_default_restricted id0 r defv;
    conv_ext b (RS.prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv))
      (prel_option (asn1_raw_terminal_rel k)) (asn1_raw_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv))
      (dmap #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) #(key_of_lit k defv) (restricted_forget k r)) (forget_dec (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)) ()
      (conv_default b (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv) (asn1_raw_terminal_rel k) (restricted_forget k r) (conv_restricted b k r))

and conv_items (b: bool) (#i: _) (ls: asn1_gen_items_l i)
: Tot (conv_items_t b ls) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    RS.items_nil_equiv ();
    raw_items_nil_equiv ();
    forget_items_nil ();
    conv_ext b (prel_emp unit unit) (asn1_items_rel ASN1_GEN_ITEMS_NIL) (prel_emp unit unit) (asn1_raw_items_rel ASN1_GEN_ITEMS_NIL)
      (fun y -> y) (forget_items ASN1_GEN_ITEMS_NIL) () (conv_eq b (prel_emp unit unit) (prel_emp unit unit) (fun y -> y) (fun _ _ _ -> ()))
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    RS.items_single_equiv dk;
    raw_items_single_equiv dk;
    forget_items_single dk;
    conv_ext b (asn1_decorated_rel dk) (asn1_items_rel (PS.single dk)) (asn1_raw_decorated_rel dk) (asn1_raw_items_rel (PS.single dk))
      (forget_dec dk) (forget_items (PS.single dk)) () (conv_dec b dk)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    RS.items_cons_equiv dk dk2 tl2;
    raw_items_cons_equiv dk dk2 tl2;
    forget_items_cons dk dk2 tl2;
    conv_ext b
      (prel_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (asn1_items_rel (PS.cons2 dk dk2 tl2))
      (prel_pair (asn1_raw_decorated_rel dk) (asn1_raw_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (asn1_raw_items_rel (PS.cons2 dk dk2 tl2))
      (pair_map (forget_dec dk) (forget_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (forget_items (PS.cons2 dk dk2 tl2)) ()
      (conv_pair b (asn1_decorated_rel dk) (asn1_raw_decorated_rel dk) (forget_dec dk)
        (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (asn1_raw_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (forget_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
        (conv_dec b dk) (conv_items b (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))

(* The main result: from the typed relation to the raw relation, with a trade back *)

ghost
fn asn1_rel_to_raw (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_impl_t k) (y: asn1_t k)
requires asn1_rel k pm x y
ensures asn1_raw_rel k pm x (forget k y) ** Trade.trade (asn1_raw_rel k pm x (forget k y)) (asn1_rel k pm x y)
{
  rewrite (asn1_rel k pm x y) as (cv true (asn1_rel k pm x y) (asn1_raw_rel k pm x (forget k y)));
  conv_k true k pm x y;
  rewrite (cv true (asn1_raw_rel k pm x (forget k y)) (asn1_rel k pm x y)) as (asn1_raw_rel k pm x (forget k y));
  Trade.intro_trade (asn1_raw_rel k pm x (forget k y)) (asn1_rel k pm x y) emp fn _ {
    rewrite (asn1_raw_rel k pm x (forget k y)) as (cv false (asn1_rel k pm x y) (asn1_raw_rel k pm x (forget k y)));
    conv_k false k pm x y;
    rewrite (cv false (asn1_raw_rel k pm x (forget k y)) (asn1_rel k pm x y)) as (asn1_rel k pm x y)
  }
}

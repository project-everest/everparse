module LowParse.Spec.BitSum
include LowParse.Spec.Sum
include LowParse.Spec.BitFields

module L = FStar.List.Tot

let rec valid_bitfield_widths_inj
  (lo: nat)
  (hi1: nat { lo <= hi1 })
  (hi2: nat { lo <= hi2 })
  (l: list nat)
: Lemma
  (requires (valid_bitfield_widths lo hi1 l /\ valid_bitfield_widths lo hi2 l))
  (ensures (hi1 == hi2))
  (decreases l)
= match l with
  | [] -> ()
  | sz :: q -> valid_bitfield_widths_inj (lo + sz) hi1 hi2 q

let rec valid_bitfield_widths_prefix
  (lo: nat)
  (hi: nat { lo <= hi })
  (prefix: list nat)
  (suffix: list nat { valid_bitfield_widths lo hi (prefix `L.append` suffix) })
: Tot (mi: nat { lo <= mi /\ mi <= hi /\ valid_bitfield_widths lo mi prefix })
  (decreases prefix)
= match prefix with
  | [] -> lo
  | sz :: q -> valid_bitfield_widths_prefix (lo + sz) hi q suffix

let rec valid_bitfield_widths_append
  (lo: nat)
  (mi: nat { lo <= mi })
  (hi: nat { mi <= hi })
  (prefix: list nat { valid_bitfield_widths lo mi prefix })
  (suffix: list nat { valid_bitfield_widths mi hi suffix })
: Lemma
  (ensures (valid_bitfield_widths lo hi (prefix `L.append` suffix)))
  (decreases prefix)
= match prefix with
  | [] -> ()
  | sz :: q -> valid_bitfield_widths_append (lo + sz) mi hi q suffix

noeq
type bitsum' =
| BitSum' :
    (tot: pos) ->
    (t: eqtype) ->
    (cl: uint_t tot t) ->
    (key: eqtype) ->
    (header: list nat) ->
    (header_size: nat { valid_bitfield_widths 0 header_size header }) ->
    (key_size: nat { header_size + key_size <= tot }) ->
    (e: enum key (bitfield cl key_size)) ->
    (payload: (enum_key e -> Tot (l: list nat { valid_bitfield_widths (header_size + key_size) tot l }))) ->
    bitsum'

noextract
let bitsum'_type
  (b: bitsum')
: Tot Type0
= (bitfields b.cl 0 b.header_size b.header & (key: enum_key b.e & bitfields b.cl (b.header_size + b.key_size) b.tot (b.payload key)))

inline_for_extraction
let filter_bitsum'
  (b: bitsum')
  (x: b.t)
: Tot bool
= let f : bitfield b.cl b.key_size = b.cl.get_bitfield x b.header_size (b.header_size + b.key_size) in
  list_mem f (list_map snd b.e)

inline_for_extraction
let synth_bitsum'
  (b: bitsum')
  (x: parse_filter_refine (filter_bitsum' b))
: Tot (bitsum'_type b)
= let f : bitfield b.cl b.key_size = b.cl.get_bitfield x b.header_size (b.header_size + b.key_size) in
  let k = enum_key_of_repr b.e f in
  (synth_bitfield b.cl 0 b.header_size b.header x, (| k, synth_bitfield b.cl (b.header_size + b.key_size) b.tot (b.payload k) x |))
  
module BF = LowParse.BitFields

let synth_bitsum'_injective'
  (b: bitsum')
  (x y: parse_filter_refine (filter_bitsum' b))
: Lemma
  (requires (synth_bitsum' b x == synth_bitsum' b y))
  (ensures (x == y))
= let f : bitfield b.cl b.key_size = b.cl.get_bitfield x b.header_size (b.header_size + b.key_size) in
  let g : bitfield b.cl b.key_size = b.cl.get_bitfield x b.header_size (b.header_size + b.key_size) in
  let k = enum_key_of_repr b.e f in
  assert (f == g);
  synth_bitfield_injective' b.cl 0 b.header_size b.header x y;
  synth_bitfield_injective' b.cl (b.header_size + b.key_size) b.tot (b.payload k) x y;
  BF.get_bitfield_partition (b.cl.v x) (b.cl.v y) 0 b.tot [b.header_size; b.header_size + b.key_size];
  BF.get_bitfield_full (b.cl.v x);
  BF.get_bitfield_full (b.cl.v y);
  assert (b.cl.uint_to_t (b.cl.v x) == b.cl.uint_to_t (b.cl.v y))

let synth_bitsum'_injective
  (b: bitsum')
: Lemma
  (synth_injective (synth_bitsum' b))
  [SMTPat (synth_injective (synth_bitsum' b))]
= synth_injective_intro' (synth_bitsum' b) (fun x y ->
    synth_bitsum'_injective' b x y
  )

let parse_bitsum'
  (b: bitsum')
  (#k: parser_kind)
  (p: parser k b.t)
: Tot (parser (parse_filter_kind k) (bitsum'_type b))
= (p `parse_filter` filter_bitsum' b) `parse_synth` synth_bitsum' b

inline_for_extraction
let synth_bitsum'_recip'
  (b: bitsum')
  (x: bitsum'_type b)
: Tot b.t
= let (hd, (| k, tl |)) = x in
  let y1 = synth_bitfield_recip b.cl (b.header_size + b.key_size) b.tot (b.payload k) tl in
  let y2 = b.cl.set_bitfield y1 b.header_size (b.header_size + b.key_size) (enum_repr_of_key b.e k) in
  let y3 = y2 `b.cl.logor` synth_bitfield_recip b.cl 0 b.header_size b.header hd in
  y3

(*
let rec get_bitfield_synth_bitfield_recip_other
  (#tot: pos) (#t: Type0) (cl: uint_t tot t)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
  (l: list nat { valid_bitfield_widths lo hi l })
  (x: bitfields cl lo hi l)
  (lo' : nat) (hi' : nat { lo' <= hi' /\ hi' <= tot /\ (hi' <= lo \/ hi <= lo') })
: Lemma
  (ensures (cl.v (cl.get_bitfield (synth_bitfield_recip cl lo hi l x) lo' hi') == 0))
  (decreases l)
= match l with
  | [] ->
    BF.get_bitfield_zero tot lo' hi'
  | [_] ->
    BF.get_bitfield_set_bitfield_other #tot 0 lo hi (cl.v x) lo' hi';
    BF.get_bitfield_zero tot lo' hi'
  | sz :: q ->

    assume (cl.get_bitfield (synth_bitfield_recip cl lo hi l x) lo' hi' == cl.uint_to_t 0)

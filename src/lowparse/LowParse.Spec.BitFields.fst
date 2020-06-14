module LowParse.Spec.BitFields
include LowParse.Spec.Combinators
include LowParse.Spec.Int
include LowParse.BitFields

module BF = LowParse.BitFields

let rec valid_bitfield_bounds (lo: nat) (hi: nat { lo <= hi }) (l: list nat) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | mi :: q -> lo <= mi && mi <= hi && valid_bitfield_bounds mi hi q

let rec valid_bitfield_widths (lo: nat) (hi: nat { lo <= hi }) (l: list nat) : Tot bool (decreases l) =
  match l with
  | [] -> lo = hi
  | sz :: q -> lo + sz <= hi && valid_bitfield_widths (lo + sz) hi q

let rec bounds_of_widths (lo: nat) (hi: nat { lo <= hi }) (l: list nat) : Pure (list nat)
  (requires (valid_bitfield_widths lo hi l))
  (ensures (fun res -> valid_bitfield_bounds lo hi res))
  (decreases l)
= match l with
  | [] -> []
  | [_] -> []
  | sz :: q -> (lo + sz) :: bounds_of_widths (lo + sz) hi q

module U = FStar.UInt

noextract
let rec bitfields (#tot: pos) (#t: Type) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) : Tot Type (decreases l) =
  match l with
  | [] -> unit
  | [sz] -> bitfield cl sz
  | sz :: q -> bitfield cl sz & bitfields cl (lo + sz) hi q

let rec synth_bitfield' (#tot: pos) (#t: Type) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: t) : Tot (bitfields cl lo hi l) (decreases l) =
  match l with
  | [] -> ()
  | [_] -> cl.get_bitfield x lo hi
  | sz :: q -> (((cl.get_bitfield x lo (lo + sz) <: t) <: bitfield cl sz), synth_bitfield' cl (lo + sz) hi q x)

let synth_bitfield (#tot: pos) (#t: Type) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: t) : Tot (bitfields cl lo hi l) = synth_bitfield' cl lo hi l x

let rec synth_bitfield_injective' (#tot: pos) (#t: Type) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x y: t) : Lemma
  (requires (synth_bitfield cl lo hi l x == synth_bitfield cl lo hi l y))
  (ensures (BF.get_bitfield (cl.v x) lo hi == BF.get_bitfield (cl.v y) lo hi))
  (decreases l)
= match l with
  | [] ->
    BF.get_bitfield_empty (cl.v x) lo;
    BF.get_bitfield_empty (cl.v y) lo
  | [_] -> ()
  | sz :: q ->
    synth_bitfield_injective' cl (lo + sz) hi q x y;
    BF.get_bitfield_partition_2_gen lo (lo + sz) hi (cl.v x) (cl.v y)

let synth_bitfield_injective (#tot: pos) (#t: Type) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths 0 tot l })
  : Lemma ((lo == 0 /\ hi == tot) ==> synth_injective (synth_bitfield cl lo hi l))
    [SMTPat (synth_injective (synth_bitfield #tot #t cl lo hi l))]
=
  synth_injective_intro' (synth_bitfield cl 0 tot l) (fun x y ->
    synth_bitfield_injective' cl 0 tot l x y;
    BF.get_bitfield_full (cl.v x);
    BF.get_bitfield_full (cl.v y);
    assert (cl.uint_to_t (cl.v x) == cl.uint_to_t (cl.v y)))

#push-options "--z3rlimit 128"

let rec synth_bitfield_ext (#tot: pos) (#t: Type) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x y: t) : Lemma
  (requires (BF.get_bitfield (cl.v x) lo hi == BF.get_bitfield (cl.v y) lo hi))
  (ensures (synth_bitfield cl lo hi l x == synth_bitfield cl lo hi l y))
  (decreases l)
= match l with
  | [] -> assert (synth_bitfield cl lo hi l x == synth_bitfield cl lo hi l y)
  | [_] ->
    assert (cl.uint_to_t (cl.v (cl.get_bitfield x lo hi)) == cl.uint_to_t (cl.v (cl.get_bitfield y lo hi)));
    assert (synth_bitfield cl lo hi l x == synth_bitfield cl lo hi l y)
  | sz :: q ->
    BF.get_bitfield_get_bitfield (cl.v x) lo hi 0 sz;
    BF.get_bitfield_get_bitfield (cl.v x) lo hi sz (hi - lo);
    BF.get_bitfield_get_bitfield (cl.v y) lo hi 0 sz;
    BF.get_bitfield_get_bitfield (cl.v y) lo hi sz (hi - lo);
    assert (cl.uint_to_t (cl.v (cl.get_bitfield x lo (lo + sz))) == cl.uint_to_t (cl.v (cl.get_bitfield y lo (lo + sz))));
    synth_bitfield_ext cl (lo + sz) hi q x y;
    assert (synth_bitfield cl lo hi l x == synth_bitfield cl lo hi l y)

#pop-options

let parse_bitfield (#t: Type) (#k: parser_kind) (p: parser k t) (#tot: pos) (cl: uint_t tot t) (l: list nat { valid_bitfield_widths 0 tot l }) : Tot (parser k (bitfields cl 0 tot l)) =
  p `parse_synth` synth_bitfield cl 0 tot l

let rec synth_bitfield_recip' (#tot: pos) (#t: Type) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: bitfields cl lo hi l) : Tot t (decreases l) =
  match l with
  | [] -> cl.uint_to_t 0
  | [_] -> cl.set_bitfield (cl.uint_to_t 0) lo hi x
  | sz :: q ->
    let (hd, tl) = x <: (bitfield cl sz & bitfields cl (lo + sz) hi q) in
    cl.set_bitfield (synth_bitfield_recip' cl (lo + sz) hi q tl) lo (lo + sz) hd

let synth_bitfield_recip (#tot: pos) (#t: Type) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: bitfields cl lo hi l) : Tot t = synth_bitfield_recip' cl lo hi l x

#push-options "--z3rlimit 64"

let rec synth_bitfield_recip_inverse'
  (#tot: pos) (#t: Type) (cl: uint_t tot t)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: bitfields cl lo hi l)
: Lemma
  (ensures (synth_bitfield cl lo hi l (synth_bitfield_recip cl lo hi l x) == x))
  (decreases l)
= match l with
  | [] ->
    assert (synth_bitfield cl lo hi l (synth_bitfield_recip cl lo hi l x) == x)
  | [sz] ->
    let x = x <: bitfield cl sz in
    BF.get_bitfield_set_bitfield_same 0 lo hi (cl.v x);
    assert (synth_bitfield cl lo hi l (synth_bitfield_recip cl lo hi l x) ==
      cl.get_bitfield (cl.set_bitfield (cl.uint_to_t 0) lo hi x) lo hi);
    assert (cl.uint_to_t (cl.v (cl.get_bitfield (cl.set_bitfield (cl.uint_to_t 0) lo hi x) lo hi)) == cl.uint_to_t (cl.v x));
    assert (synth_bitfield cl lo hi l (synth_bitfield_recip cl lo hi l x) == x)
  | sz :: q ->
    let (hd, tl) = x <: (bitfield cl sz & bitfields cl (lo + sz) hi q) in
    let y = synth_bitfield_recip cl (lo + sz) hi q tl in
    BF.get_bitfield_set_bitfield_same (cl.v y) lo (lo + sz) (cl.v hd);
    BF.get_bitfield_set_bitfield_other (cl.v y) lo (lo + sz) (cl.v hd) (lo + sz) hi;
    synth_bitfield_ext cl (lo + sz) hi q y (cl.set_bitfield y lo (lo + sz) hd);
    synth_bitfield_recip_inverse' cl (lo + sz) hi q tl;
    assert (cl.uint_to_t (cl.v (fst (synth_bitfield cl lo hi l (synth_bitfield_recip cl lo hi l x) <: (bitfield cl sz & bitfields cl (lo + sz) hi q)))) == cl.uint_to_t (cl.v (cl.get_bitfield (cl.set_bitfield (synth_bitfield_recip cl (lo + sz) hi q tl) lo (lo + sz) hd) lo (lo + sz))));
    assert (synth_bitfield cl lo hi l (synth_bitfield_recip cl lo hi l x) == x)

#pop-options

let synth_bitfield_recip_inverse (#tot: pos) (#t: Type) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths 0 tot l })
  : Lemma ((lo == 0 /\ hi == tot) ==> synth_inverse (synth_bitfield cl lo hi l) (synth_bitfield_recip cl lo hi l))
    [SMTPat (synth_inverse (synth_bitfield #tot #t cl lo hi l) (synth_bitfield_recip #tot #t cl lo hi l))]
=
  synth_inverse_intro' (synth_bitfield cl 0 tot l) (synth_bitfield_recip cl 0 tot l) (fun x ->
    synth_bitfield_recip_inverse' cl 0 tot l x
  )

let serialize_bitfield
  (#t: Type) (#k: parser_kind) (#p: parser k t) (s: serializer p)
  (#tot: pos) (cl: uint_t tot t) (l: list nat { valid_bitfield_widths 0 tot l })
: Tot (serializer (parse_bitfield p cl l))
= serialize_synth
    p
    (synth_bitfield cl 0 tot l)
    s
    (synth_bitfield_recip cl 0 tot l)
    ()

let parse_bitfield64 (l: list nat { valid_bitfield_widths 0 64 l }) : Tot (parser parse_u64_kind (bitfields uint64 0 64 l)) =
  parse_bitfield parse_u64 uint64 l

let serialize_bitfield64 (l: list nat { valid_bitfield_widths 0 64 l }) : Tot (serializer (parse_bitfield64 l)) =
  serialize_bitfield serialize_u64 uint64 l

let parse_bitfield32 (l: list nat { valid_bitfield_widths 0 32 l }) : Tot (parser parse_u32_kind (bitfields uint32 0 32 l)) =
  parse_bitfield parse_u32 uint32 l

let serialize_bitfield32 (l: list nat { valid_bitfield_widths 0 32 l }) : Tot (serializer (parse_bitfield32 l)) =
  serialize_bitfield serialize_u32 uint32 l

let parse_bitfield16 (l: list nat { valid_bitfield_widths 0 16 l }) : Tot (parser parse_u16_kind (bitfields uint16 0 16 l)) =
  parse_bitfield parse_u16 uint16 l

let serialize_bitfield16 (l: list nat { valid_bitfield_widths 0 16 l }) : Tot (serializer (parse_bitfield16 l)) =
  serialize_bitfield serialize_u16 uint16 l

let parse_bitfield8 (l: list nat { valid_bitfield_widths 0 8 l }) : Tot (parser parse_u8_kind (bitfields uint8 0 8 l)) =
  parse_bitfield parse_u8 uint8 l

let serialize_bitfield8 (l: list nat { valid_bitfield_widths 0 8 l }) : Tot (serializer (parse_bitfield8 l)) =
  serialize_bitfield serialize_u8 uint8 l

(* Universal destructor *)

inline_for_extraction
noextract
let bitfields_destr_t
  (#tot: pos)
  (#t: Type)
  (cl: uint_t tot t)
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot })
  (l: list nat { valid_bitfield_widths lo hi l })
: Tot Type
=
  (f_t: (bitfields cl lo hi l -> Tot Type)) ->
  (f: ((x: bitfields cl lo hi l) -> Tot (f_t x))) ->
  (x: t) ->
  Tot (f_t (synth_bitfield cl lo hi l x))

inline_for_extraction
noextract
let bitfields_destr_cons
  (#tot: pos)
  (#t: Type)
  (cl: uint_t tot t)
  (lo: nat)
  (sz: nat)
  (hi: nat { lo + sz <= hi /\ hi <= tot })
  (l: list nat { valid_bitfield_widths (lo + sz) hi l /\ Cons? l })
  (phi: bitfields_destr_t cl (lo + sz) hi l)
: Tot (bitfields_destr_t cl lo hi (sz :: l))
= fun f_t f x ->
    phi
      (fun x' -> f_t (((cl.get_bitfield x lo (lo + sz) <: t) <: bitfield cl sz), x'))
      (fun x' -> f (((cl.get_bitfield x lo (lo + sz) <: t) <: bitfield cl sz), x'))
      x

inline_for_extraction
noextract
let bitfields_destr_cons_nil
  (#tot: pos)
  (#t: Type)
  (cl: uint_t tot t)
  (lo: nat)
  (sz: nat { lo + sz <= tot })
: Tot (bitfields_destr_t cl lo (lo + sz) [sz])
= fun f_t f x ->
    f (cl.get_bitfield x lo (lo + sz))

inline_for_extraction
noextract
let bitfields_destr_nil
  (#tot: pos)
  (#t: Type)
  (cl: uint_t tot t)
  (lo: nat { lo <= tot } )
: Tot (bitfields_destr_t cl lo lo [])
= fun f_t f x ->
    f ()

noextract
let rec mk_bitfields_destr'
  (#tot: pos)
  (#t: Type)
  (cl: uint_t tot t)
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot })
  (l: list nat { valid_bitfield_widths lo hi l })
: Tot (bitfields_destr_t cl lo hi l)
  (decreases l)
= match l with
  | [] -> bitfields_destr_nil cl lo
  | [sz] -> bitfields_destr_cons_nil cl lo sz
  | sz :: q -> bitfields_destr_cons cl lo sz hi q (mk_bitfields_destr' cl (lo + sz) hi q)

inline_for_extraction
noextract
let mk_bitfields_destr
  (#tot: pos)
  (#t: Type)
  (cl: uint_t tot t)
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot })
  (l: list nat { valid_bitfield_widths lo hi l })
: Tot (bitfields_destr_t cl lo hi l)
= norm [delta_only [`%mk_bitfields_destr'; `%bitfields_destr_nil; `%bitfields_destr_cons_nil; `%bitfields_destr_cons]; iota; zeta; primops] (mk_bitfields_destr' cl lo hi l)

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

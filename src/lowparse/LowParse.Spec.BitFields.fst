module LowParse.Spec.BitFields
include LowParse.Spec.Combinators
include LowParse.Spec.Int

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

inline_for_extraction
noextract
noeq
type uint_t (tot: pos) (t: Type0) = {
  v: (t -> Tot (U.uint_t tot));
  uint_to_t: (U.uint_t tot -> Tot t);
  v_uint_to_t: ((x: U.uint_t tot) -> Lemma (v (uint_to_t x) == x));
  uint_to_t_v: ((x: t) -> Lemma (uint_to_t (v x) == x));
  get_bitfield: ((x: t) -> (lo: nat) -> (hi: nat { lo <= hi /\ hi <= tot }) -> Tot (y: t { v y == BF.get_bitfield (v x) lo hi }));
  set_bitfield: ((x: t) -> (lo: nat) -> (hi: nat { lo <= hi /\ hi <= tot }) -> (z: t { v z < pow2 (hi - lo) }) -> Tot (y : t { v y == BF.set_bitfield (v x) lo hi (v z)}));
  logor: ((x: t) -> (y: t) -> Tot (z: t { v z == v x `U.logor` v y }));
}

let uint_t_v_uint_to_t #tot #t (cl: uint_t tot t) (x: U.uint_t tot) : Lemma
  (cl.v (cl.uint_to_t x) == x)
  [SMTPat (cl.v (cl.uint_to_t x))]
= cl.v_uint_to_t x

let uint_t_uint_to_t_v #tot #t (cl: uint_t tot t) (x: t) : Lemma
  (cl.uint_to_t (cl.v x) == x)
  [SMTPat (cl.uint_to_t (cl.v x))]
= cl.uint_to_t_v x

inline_for_extraction
let bitfield (#tot: pos) (#t: Type0) (cl: uint_t tot t) (sz: nat { sz <= tot }) : Tot Type0 =
  (x: t { cl.v x < pow2 sz })

noextract
let rec bitfields (#tot: pos) (#t: Type0) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) : Tot Type0 (decreases l) =
  match l with
  | [] -> unit
  | [sz] -> bitfield cl sz
  | sz :: q -> bitfield cl sz & bitfields cl (lo + sz) hi q

let rec synth_bitfield' (#tot: pos) (#t: Type0) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: t) : Tot (bitfields cl lo hi l) (decreases l) =
  match l with
  | [] -> ()
  | [_] -> cl.get_bitfield x lo hi
  | sz :: q -> (((cl.get_bitfield x lo (lo + sz) <: t) <: bitfield cl sz), synth_bitfield' cl (lo + sz) hi q x)

let synth_bitfield (#tot: pos) (#t: Type0) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: t) : Tot (bitfields cl lo hi l) = synth_bitfield' cl lo hi l x

let rec synth_bitfield_injective' (#tot: pos) (#t: Type0) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x y: t) : Lemma
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

let synth_bitfield_injective (#tot: pos) (#t: Type0) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths 0 tot l })
  : Lemma ((lo == 0 /\ hi == tot) ==> synth_injective (synth_bitfield cl lo hi l))
    [SMTPat (synth_injective (synth_bitfield #tot #t cl lo hi l))]
=
  synth_injective_intro' (synth_bitfield cl 0 tot l) (fun x y ->
    synth_bitfield_injective' cl 0 tot l x y;
    BF.get_bitfield_full (cl.v x);
    BF.get_bitfield_full (cl.v y);
    assert (cl.uint_to_t (cl.v x) == cl.uint_to_t (cl.v y)))

#push-options "--z3rlimit 64"

let rec synth_bitfield_ext (#tot: pos) (#t: Type0) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x y: t) : Lemma
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

let parse_bitfield (#t: Type0) (#k: parser_kind) (p: parser k t) (#tot: pos) (cl: uint_t tot t) (l: list nat { valid_bitfield_widths 0 tot l }) : Tot (parser k (bitfields cl 0 tot l)) =
  p `parse_synth` synth_bitfield cl 0 tot l

let rec synth_bitfield_recip' (#tot: pos) (#t: Type0) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: bitfields cl lo hi l) : Tot t (decreases l) =
  match l with
  | [] -> cl.uint_to_t 0
  | [_] -> cl.set_bitfield (cl.uint_to_t 0) lo hi x
  | sz :: q ->
    let (hd, tl) = x <: (bitfield cl sz & bitfields cl (lo + sz) hi q) in
    cl.set_bitfield (synth_bitfield_recip' cl (lo + sz) hi q tl) lo (lo + sz) hd

let synth_bitfield_recip (#tot: pos) (#t: Type0) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: bitfields cl lo hi l) : Tot t = synth_bitfield_recip' cl lo hi l x

#push-options "--z3rlimit 64"

let rec synth_bitfield_recip_inverse'
  (#tot: pos) (#t: Type0) (cl: uint_t tot t)
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

let synth_bitfield_recip_inverse (#tot: pos) (#t: Type0) (cl: uint_t tot t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths 0 tot l })
  : Lemma ((lo == 0 /\ hi == tot) ==> synth_inverse (synth_bitfield cl lo hi l) (synth_bitfield_recip cl lo hi l))
    [SMTPat (synth_inverse (synth_bitfield #tot #t cl lo hi l) (synth_bitfield_recip #tot #t cl lo hi l))]
=
  synth_inverse_intro' (synth_bitfield cl 0 tot l) (synth_bitfield_recip cl 0 tot l) (fun x ->
    synth_bitfield_recip_inverse' cl 0 tot l x
  )

let serialize_bitfield
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (s: serializer p)
  (#tot: pos) (cl: uint_t tot t) (l: list nat { valid_bitfield_widths 0 tot l })
: Tot (serializer (parse_bitfield p cl l))
= serialize_synth
    p
    (synth_bitfield cl 0 tot l)
    s
    (synth_bitfield_recip cl 0 tot l)
    ()

module U32 = FStar.UInt32
module U64 = FStar.UInt64

inline_for_extraction
noextract
let uint64 : uint_t 64 U64.t = {
  v = U64.v;
  uint_to_t = U64.uint_to_t;
  v_uint_to_t = (fun _ -> ());
  uint_to_t_v = (fun _ -> ());
  get_bitfield = (fun x lo hi -> BF.get_bitfield64 x lo hi);
  set_bitfield = (fun x lo hi z -> BF.set_bitfield64 x lo hi z);
  logor = (fun x y -> U64.logor x y);
}

inline_for_extraction
noextract
let uint32 : uint_t 32 U32.t = {
  v = U32.v;
  uint_to_t = U32.uint_to_t;
  v_uint_to_t = (fun _ -> ());
  uint_to_t_v = (fun _ -> ());
  get_bitfield = (fun x lo hi -> BF.get_bitfield32 x lo hi);
  set_bitfield = (fun x lo hi z -> BF.set_bitfield32 x lo hi z);
  logor = (fun x y -> U32.logor x y);
}

module U16 = FStar.UInt16
module U8 = FStar.UInt8

inline_for_extraction
noextract
let uint16 : uint_t 16 U16.t = {
  v = U16.v;
  uint_to_t = U16.uint_to_t;
  v_uint_to_t = (fun _ -> ());
  uint_to_t_v = (fun _ -> ());
  get_bitfield = (fun x lo hi -> BF.get_bitfield16 x lo hi);
  set_bitfield = (fun x lo hi z -> BF.set_bitfield16 x lo hi z);
  logor = (fun x y -> U16.logor x y);
}

inline_for_extraction
noextract
let uint8 : uint_t 8 U8.t = {
  v = U8.v;
  uint_to_t = U8.uint_to_t;
  v_uint_to_t = (fun _ -> ());
  uint_to_t_v = (fun _ -> ());
  get_bitfield = (fun x lo hi -> BF.get_bitfield8 x lo hi);
  set_bitfield = (fun x lo hi z -> BF.set_bitfield8 x lo hi z);
  logor = (fun x y -> U8.logor x y);
}

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
  (#t: Type0)
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
  (#t: Type0)
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
  (#t: Type0)
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
  (#t: Type0)
  (cl: uint_t tot t)
  (lo: nat { lo <= tot } )
: Tot (bitfields_destr_t cl lo lo [])
= fun f_t f x ->
    f ()

noextract
let rec mk_bitfields_destr'
  (#tot: pos)
  (#t: Type0)
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
  (#t: Type0)
  (cl: uint_t tot t)
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot })
  (l: list nat { valid_bitfield_widths lo hi l })
: Tot (bitfields_destr_t cl lo hi l)
= norm [delta_only [`%mk_bitfields_destr'; `%bitfields_destr_nil; `%bitfields_destr_cons_nil; `%bitfields_destr_cons]; iota; zeta; primops] (mk_bitfields_destr' cl lo hi l)

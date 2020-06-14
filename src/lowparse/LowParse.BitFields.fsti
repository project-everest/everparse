module LowParse.BitFields
module U = FStar.UInt

type ubitfield (tot: nat) (sz: nat) = (x: U.uint_t tot { x < pow2 sz })

val get_bitfield 
  (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot})
: Tot (ubitfield tot (hi - lo))

val get_bitfield_logor
  (#tot: pos) (x y: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot})
: Lemma
  (get_bitfield (x `U.logor` y) lo hi == get_bitfield x lo hi `U.logor` get_bitfield y lo hi)

val get_bitfield_logxor
  (#tot: pos) (x y: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot})
: Lemma
  (get_bitfield (x `U.logxor` y) lo hi == get_bitfield x lo hi `U.logxor` get_bitfield y lo hi)

val set_bitfield
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
: Tot (U.uint_t tot)

val get_bitfield_set_bitfield_same
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
: Lemma
  (get_bitfield (set_bitfield x lo hi v) lo hi == v)

val get_bitfield_set_bitfield_other
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
  (lo' : nat) (hi' : nat { lo' <= hi' /\ hi' <= tot })
: Lemma
  (requires (hi' <= lo \/ hi <= lo'))
  (ensures (get_bitfield (set_bitfield x lo hi v) lo' hi' == get_bitfield x lo' hi'))

val set_bitfield_set_bitfield_same_gen
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
  (lo' : nat) (hi' : nat { lo' <= lo /\ hi <= hi' /\ hi' <= tot })
  (v' : ubitfield tot (hi' - lo'))
: Lemma
  (ensures (set_bitfield (set_bitfield x lo hi v) lo' hi' v' == set_bitfield x lo' hi' v'))

let set_bitfield_set_bitfield_same
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
  (v' : ubitfield tot (hi - lo))
: Lemma
  (ensures (set_bitfield (set_bitfield x lo hi v) lo hi v' == set_bitfield x lo hi v'))
= set_bitfield_set_bitfield_same_gen x lo hi v lo hi v'

val set_bitfield_set_bitfield_other
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
  (lo' : nat) (hi' : nat { lo' <= hi' /\ hi' <= tot }) (v' : ubitfield tot (hi' - lo'))
: Lemma
  (requires (hi' <= lo \/ hi <= lo'))
  (ensures (set_bitfield (set_bitfield x lo hi v) lo' hi' v' == set_bitfield (set_bitfield x lo' hi' v') lo hi v))

val set_bitfield_full
  (#tot: pos) (x: U.uint_t tot) (y: ubitfield tot tot)
: Lemma
  (set_bitfield x 0 tot y == y)

val set_bitfield_empty
  (#tot: pos) (x: U.uint_t tot) (i: nat { i <= tot }) (y: ubitfield tot 0)
: Lemma
  (set_bitfield x i i y == x)

val get_bitfield_zero
  (tot: pos)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
: Lemma
  (get_bitfield #tot 0 lo hi == 0)

val get_bitfield_full
  (#tot: pos)
  (x: U.uint_t tot)
: Lemma
  (get_bitfield x 0 tot == x)

val get_bitfield_empty
  (#tot: pos)
  (x: U.uint_t tot)
  (i: nat { i <= tot })
: Lemma
  (get_bitfield x i i == 0)

val lt_pow2_get_bitfield_hi
  (#tot: pos)
  (x: U.uint_t tot)
  (mi: nat {mi <= tot})
: Lemma
  (requires (x < pow2 mi))
  (ensures (get_bitfield x mi tot == 0))

val get_bitfield_hi_lt_pow2
  (#tot: pos)
  (x: U.uint_t tot)
  (mi: nat {mi <= tot})
: Lemma
  (requires (get_bitfield x mi tot == 0))
  (ensures (x < pow2 mi))

val get_bitfield_get_bitfield
  (#tot: pos)
  (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
  (lo': nat) (hi': nat { lo' <= hi' /\ hi' <= hi - lo })
: Lemma
  (get_bitfield (get_bitfield x lo hi) lo' hi' == get_bitfield x (lo + lo') (lo + hi'))

val get_bitfield_zero_inner
  (#tot: pos)
  (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
  (lo': nat { lo <= lo' }) (hi': nat { lo' <= hi' /\ hi' <= hi })
: Lemma
  (ensures (get_bitfield x lo hi == 0 ==> get_bitfield x lo' hi' == 0))

val set_bitfield_get_bitfield
  (#tot: pos)
  (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
: Lemma
  (set_bitfield x lo hi (get_bitfield x lo hi) == x)

val get_bitfield_partition_2_gen
  (#tot: pos)
  (lo: nat)
  (mi: nat)
  (hi: nat { lo <= mi /\ mi <= hi /\ hi <= tot })
  (x y: U.uint_t tot)
: Lemma
  (requires (
    get_bitfield x lo mi == get_bitfield y lo mi /\
    get_bitfield x mi hi == get_bitfield y mi hi
  ))
  (ensures (
    get_bitfield x lo hi == get_bitfield y lo hi
  ))

val get_bitfield_partition_2
  (#tot: pos)
  (mid: nat { mid <= tot })
  (x y: U.uint_t tot)  
: Lemma
  (requires (
    get_bitfield x 0 mid == get_bitfield y 0 mid /\
    get_bitfield x mid tot == get_bitfield y mid tot
  ))
  (ensures (
    x == y
  ))

let rec get_bitfield_partition_prop
  (#tot: pos)
  (x y: U.uint_t tot)
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot })
  (l: list nat)
: Tot bool
  (decreases l)
= match l with
  | [] ->
    get_bitfield x lo hi = get_bitfield y lo hi
  | mi :: q ->
    lo <= mi && mi <= hi &&
    get_bitfield_partition_prop x y mi hi q &&
    get_bitfield x lo mi = get_bitfield y lo mi

val get_bitfield_partition
  (#tot: pos)
  (x y: U.uint_t tot)
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot })
  (l: list nat)
: Lemma
  (requires (get_bitfield_partition_prop x y lo hi l))
  (ensures (get_bitfield x lo hi == get_bitfield y lo hi))

let get_bitfield_partition_3
  (#tot: pos)
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot })
  (x y: U.uint_t tot)  
: Lemma
  (requires (
    get_bitfield x 0 lo == get_bitfield y 0 lo /\
    get_bitfield x lo hi == get_bitfield y lo hi /\
    get_bitfield x hi tot == get_bitfield y hi tot
  ))
  (ensures (x == y))
= assert_norm (get_bitfield_partition_prop x y 0 tot [lo; hi]); // does not need fuel, thanks to normalization
  get_bitfield_partition x y 0 tot [lo; hi];
  get_bitfield_full x;
  get_bitfield_full y

val get_bitfield_size
  (tot1 tot2: pos)
  (x: nat { x < pow2 tot1 /\ tot1 <= tot2 })
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot1 })
: Lemma
  (x < pow2 tot2 /\ (get_bitfield #tot1 x lo hi <: nat) == (get_bitfield #tot2 x lo hi <: nat))

val set_bitfield_size
  (tot1 tot2: pos)
  (x: nat { x < pow2 tot1 /\ tot1 <= tot2 })
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot1 })
  (v: ubitfield tot1 (hi - lo))
: Lemma
  (x < pow2 tot2 /\  v < pow2 tot2 /\ (set_bitfield #tot1 x lo hi v <: nat) == (set_bitfield #tot2 x lo hi v <: nat))

val set_bitfield_bound
  (#tot: pos)
  (x: U.uint_t tot)
  (bound: nat { bound <= tot /\ x < pow2 bound })
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= bound })
  (v: ubitfield tot (hi - lo))
: Lemma
  (set_bitfield x lo hi v < pow2 bound)

val set_bitfield_set_bitfield_get_bitfield
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
  (lo' : nat) (hi' : nat { lo' <= hi' /\ hi' <= hi - lo }) (v' : ubitfield tot (hi' - lo'))
: Lemma
  ( let v = set_bitfield (get_bitfield x lo hi) lo' hi' v' in
    v < pow2 (hi - lo) /\
    set_bitfield x lo hi v == set_bitfield x (lo + lo') (lo + hi') v' )

val get_bitfield_eq
  (#tot: pos)
  (x: U.uint_t tot)
  (lo: nat) (hi: nat {lo <= hi /\ hi <= tot})
: Lemma
  (get_bitfield x lo hi == (x / pow2 lo) % pow2 (hi - lo))

val get_bitfield_eq_2
  (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
: Lemma
  (get_bitfield x lo hi == (x `U.shift_left` (tot - hi)) `U.shift_right` (tot - hi + lo))

val set_bitfield_eq
  (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
: Lemma
  (set_bitfield x lo hi v == (x `U.logand` U.lognot ((U.lognot 0 `U.shift_right` (tot - (hi - lo))) `U.shift_left` lo)) `U.logor` (v `U.shift_left` lo))

module U32 = FStar.UInt32

inline_for_extraction
noextract
noeq
type uint_t (tot: pos) (t: Type) = {
  v: (t -> Tot (U.uint_t tot));
  uint_to_t: (U.uint_t tot -> Tot t);
  v_uint_to_t: ((x: U.uint_t tot) -> Lemma (v (uint_to_t x) == x));
  uint_to_t_v: ((x: t) -> Lemma (uint_to_t (v x) == x));
  get_bitfield_gen: ((x: t) -> (lo: U32.t) -> (hi: U32.t { U32.v lo < U32.v hi /\ U32.v hi <= tot }) -> Tot (y: t { v y == get_bitfield (v x) (U32.v lo) (U32.v hi) }));
  set_bitfield_gen: ((x: t) -> (lo: U32.t) -> (hi: U32.t { U32.v lo < U32.v hi /\ U32.v hi <= tot }) -> (z: t { v z < pow2 (U32.v hi - U32.v lo) }) -> Tot (y : t { v y == set_bitfield (v x) (U32.v lo) (U32.v hi) (v z)}));
  get_bitfield: ((x: t) -> (lo: nat) -> (hi: nat { lo <= hi /\ hi <= tot }) -> Tot (y: t { v y == get_bitfield (v x) lo hi }));
  set_bitfield: ((x: t) -> (lo: nat) -> (hi: nat { lo <= hi /\ hi <= tot }) -> (z: t { v z < pow2 (hi - lo) }) -> Tot (y : t { v y == set_bitfield (v x) lo hi (v z)}));
  logor: ((x: t) -> (y: t) -> Tot (z: t { v z == v x `U.logor` v y }));
  bitfield_eq_lhs: ((x: t) -> (lo: nat) -> (hi: nat { lo <= hi /\ hi <= tot }) -> Tot t);
  bitfield_eq_rhs: ((x: t) -> (lo: nat) -> (hi: nat { lo <= hi /\ hi <= tot }) -> (z: t { v z < pow2 (hi - lo) }) -> Tot (y: t { bitfield_eq_lhs x lo hi == y <==> (get_bitfield x lo hi <: t) == z }));
}

inline_for_extraction
let bitfield (#tot: pos) (#t: Type) (cl: uint_t tot t) (sz: nat { sz <= tot }) : Tot Type =
  (x: t { cl.v x < pow2 sz })

let uint_t_v_uint_to_t #tot #t (cl: uint_t tot t) (x: U.uint_t tot) : Lemma
  (cl.v (cl.uint_to_t x) == x)
  [SMTPat (cl.v (cl.uint_to_t x))]
= cl.v_uint_to_t x

let uint_t_uint_to_t_v #tot #t (cl: uint_t tot t) (x: t) : Lemma
  (cl.uint_to_t (cl.v x) == x)
  [SMTPat (cl.uint_to_t (cl.v x))]
= cl.uint_to_t_v x

let uint_get_bitfield_set_bitfield_same
  #tot #t (cl: uint_t tot t)
  (x: t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (z: bitfield cl (hi - lo))
: Lemma
  (cl.get_bitfield (cl.set_bitfield x lo hi z) lo hi == z)
  [SMTPat (cl.get_bitfield (cl.set_bitfield x lo hi z) lo hi)]
= get_bitfield_set_bitfield_same (cl.v x) lo hi (cl.v z);
  assert (cl.uint_to_t (cl.v (cl.get_bitfield (cl.set_bitfield x lo hi z) lo hi)) == cl.uint_to_t (cl.v z))

let uint_get_bitfield_set_bitfield_other
  #tot #t (cl: uint_t tot t)
  (x: t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (z: bitfield cl (hi - lo))
  (lo' : nat) (hi' : nat { lo' <= hi' /\ hi' <= tot /\ (hi' <= lo \/ hi <= lo') })
: Lemma
  (cl.get_bitfield (cl.set_bitfield x lo hi z) lo' hi' == cl.get_bitfield x lo' hi')
  [SMTPat (cl.get_bitfield (cl.set_bitfield x lo hi z) lo' hi')]
= get_bitfield_set_bitfield_other (cl.v x) lo hi (cl.v z) lo' hi';
  assert (cl.uint_to_t (cl.v (cl.get_bitfield (cl.set_bitfield x lo hi z) lo' hi')) == cl.uint_to_t (cl.v (cl.get_bitfield x lo' hi')))

let uint_set_bitfield_set_bitfield_same_gen
  #tot #t (cl: uint_t tot t)
  (x: t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (z: bitfield cl (hi - lo))
  (lo': nat) (hi': nat { lo' <= lo /\ hi <= hi' /\ hi' <= tot }) (z' : bitfield cl (hi' - lo'))
: Lemma
  (cl.set_bitfield (cl.set_bitfield x lo hi z) lo' hi' z' == cl.set_bitfield x lo' hi' z')
= set_bitfield_set_bitfield_same_gen (cl.v x) lo hi (cl.v z) lo' hi' (cl.v z');
  assert (cl.uint_to_t (cl.v (cl.set_bitfield (cl.set_bitfield x lo hi z) lo' hi' z')) == cl.uint_to_t (cl.v (cl.set_bitfield x lo' hi' z')))

let uint_set_bitfield_set_bitfield_same
  #tot #t (cl: uint_t tot t)
  (x: t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (z: bitfield cl (hi - lo))
  (z' : bitfield cl (hi - lo))
: Lemma
  (cl.set_bitfield (cl.set_bitfield x lo hi z) lo hi z' == cl.set_bitfield x lo hi z')
= set_bitfield_set_bitfield_same (cl.v x) lo hi (cl.v z) (cl.v z');
  assert (cl.uint_to_t (cl.v (cl.set_bitfield (cl.set_bitfield x lo hi z) lo hi z')) == cl.uint_to_t (cl.v (cl.set_bitfield x lo hi z')))

let uint_set_bitfield_set_bitfield_other
  #tot #t (cl: uint_t tot t)
  (x: t) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (z: bitfield cl (hi - lo))
  (lo' : nat) (hi' : nat { lo' <= hi' /\ hi' <= tot /\ (hi' <= lo \/ hi <= lo') })
  (z' : bitfield cl (hi' - lo'))
: Lemma
  (cl.set_bitfield (cl.set_bitfield x lo hi z) lo' hi' z' == cl.set_bitfield (cl.set_bitfield x lo' hi' z') lo hi z)
= set_bitfield_set_bitfield_other (cl.v x) lo hi (cl.v z) lo' hi' (cl.v z');
  assert (cl.uint_to_t (cl.v (cl.set_bitfield (cl.set_bitfield x lo hi z) lo' hi' z')) == cl.uint_to_t (cl.v (cl.set_bitfield (cl.set_bitfield x lo' hi' z') lo hi z)))


module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U16 = FStar.UInt16
module U8 = FStar.UInt8

inline_for_extraction
noextract
val uint64 : uint_t 64 U64.t

val uint64_v_eq
  (x: U64.t)
: Lemma
  (uint64.v x == U64.v x)
  [SMTPat (uint64.v x)]

val uint64_uint_to_t_eq
  (x: U.uint_t 64)
: Lemma
  (uint64.uint_to_t x == U64.uint_to_t x)
  [SMTPat (uint64.uint_to_t x)]

inline_for_extraction
noextract
val uint32 : uint_t 32 U32.t

val uint32_v_eq
  (x: U32.t)
: Lemma
  (uint32.v x == U32.v x)
  [SMTPat (uint32.v x)]

val uint32_uint_to_t_eq
  (x: U.uint_t 32)
: Lemma
  (uint32.uint_to_t x == U32.uint_to_t x)
  [SMTPat (uint32.uint_to_t x)]

inline_for_extraction
noextract
val uint16 : uint_t 16 U16.t

val uint16_v_eq
  (x: U16.t)
: Lemma
  (uint16.v x == U16.v x)
  [SMTPat (uint16.v x)]

val uint16_uint_to_t_eq
  (x: U.uint_t 16)
: Lemma
  (uint16.uint_to_t x == U16.uint_to_t x)
  [SMTPat (uint16.uint_to_t x)]

inline_for_extraction
noextract
val uint8 : uint_t 8 U8.t

val uint8_v_eq
  (x: U8.t)
: Lemma
  (uint8.v x == U8.v x)
  [SMTPat (uint8.v x)]

val uint8_uint_to_t_eq
  (x: U.uint_t 8)
: Lemma
  (uint8.uint_to_t x == U8.uint_to_t x)
  [SMTPat (uint8.uint_to_t x)]

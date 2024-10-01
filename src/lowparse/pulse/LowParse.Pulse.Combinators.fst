module LowParse.Pulse.Combinators
include LowParse.Spec.Combinators
include LowParse.Pulse.Base
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
```pulse
fn validate_ret
  (#t: Type0)
  (x: t)
: validator #t #parse_ret_kind (parse_ret x)
= (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  true
}
```

inline_for_extraction
```pulse
fn leaf_read_ret
  (#t: Type0)
  (x: t)
  (v_unique: (v' : t) -> Lemma (x == v'))
: leaf_reader #t #parse_ret_kind #(parse_ret x) (serialize_ret x v_unique)
= (input: slice byte)
  (#pm: _)
  (#v: _)
{
  v_unique v;
  x
}
```

inline_for_extraction
let read_ret
  (#t: Type0)
  (x: t)
  (v_unique: (v' : t) -> Lemma (x == v'))
: Tot (reader (serialize_ret x v_unique))
= reader_of_leaf_reader (leaf_read_ret x v_unique)

inline_for_extraction
let jump_ret (#t: Type) (x: t) : jumper (parse_ret x) = jump_constant_size (parse_ret x) 0sz 

inline_for_extraction
let validate_empty : validator parse_empty = validate_ret ()

inline_for_extraction
let leaf_read_empty : leaf_reader serialize_empty = leaf_read_ret () (fun _ -> ())

inline_for_extraction
let read_empty : reader serialize_empty = reader_of_leaf_reader leaf_read_empty

inline_for_extraction
let jump_empty : jumper parse_empty = jump_ret ()

let parse_serialize_strong_prefix
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (v: t)
  (suff: bytes)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    let sv = bare_serialize s v in
    parse p (sv `Seq.append` suff) == Some (v, Seq.length sv)
  ))
= let sv = bare_serialize s v in
  parse_strong_prefix #k p sv (sv `Seq.append` suff)

inline_for_extraction
```pulse
fn validate_synth
  (#t #t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: validator p)
  (f: (t -> GTot t') { synth_injective f })
: validator #t' #k (parse_synth p f)
= (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  parse_synth_eq p f (Seq.slice v (SZ.v offset) (Seq.length v));
  w input poffset #offset #pm #v
}
```

inline_for_extraction
```pulse
fn jump_synth
  (#t #t': Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: jumper p)
  (f: (t -> GTot t') { synth_injective f })
: jumper #t' #k (parse_synth #k #t p f)
=
  (input: _)
  (offset: _)
  (#pm: _)
  (#v: _)
{    
  parse_synth_eq p f (Seq.slice v (SZ.v offset) (Seq.length v));
  w input offset #pm #v
}
```

```pulse
ghost
fn pts_to_serialized_synth_intro
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_serialized s input #pm v
  ensures pts_to_serialized (serialize_synth p f s f' ()) input #pm (f v)
{
  parse_synth_eq p f (bare_serialize s v);
  parse_serialize #k #t' #(parse_synth p f) (serialize_synth p f s f' ()) (f v);
  parse_injective #k #t' (parse_synth p f) (bare_serialize s v) (bare_serialize (serialize_synth p f s f' ()) (f v));
  unfold (pts_to_serialized s input #pm v);
  rewrite (pts_to input #pm (bare_serialize s v))
    as (pts_to input #pm (bare_serialize (serialize_synth p f s f' ()) (f v)));
  fold (pts_to_serialized (serialize_synth p f s f' ()) input #pm (f v))
}
```

```pulse
ghost
fn pts_to_serialized_synth_elim
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (v: t)
  requires pts_to_serialized (serialize_synth p f s f' ()) input #pm (f v)
  ensures pts_to_serialized s input #pm v
{
  parse_synth_eq p f (bare_serialize s v);
  parse_serialize #k #t' #(parse_synth p f) (serialize_synth p f s f' ()) (f v);
  parse_injective #k #t' (parse_synth p f) (bare_serialize s v) (bare_serialize (serialize_synth p f s f' ()) (f v));
  unfold (pts_to_serialized (serialize_synth p f s f' ()) input #pm (f v));
  rewrite (pts_to input #pm (bare_serialize (serialize_synth p f s f' ()) (f v)))
    as (pts_to input #pm (bare_serialize s v));
  fold (pts_to_serialized s input #pm v)
}
```

```pulse
ghost
fn pts_to_serialized_synth_trade
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_serialized s input #pm v
  ensures pts_to_serialized (serialize_synth p f s f' ()) input #pm (f v) ** trade (pts_to_serialized (serialize_synth p f s f' ()) input #pm (f v)) (pts_to_serialized s input #pm v)
{
  pts_to_serialized_synth_intro s f f' input;
  ghost
  fn aux
    (_: unit)
    requires emp ** pts_to_serialized (serialize_synth p f s f' ()) input #pm (f v)
    ensures pts_to_serialized s input #pm v
  {
    pts_to_serialized_synth_elim s f f' input v 
  };
  intro_trade _ _ _ aux
}
```

```pulse
ghost
fn pts_to_serialized_synth_l2r
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t')
  requires pts_to_serialized (serialize_synth p f s f' ()) input #pm v
  ensures pts_to_serialized s input #pm (f' v)
{
  serialize_synth_eq p f s f' () v;
  unfold (pts_to_serialized (serialize_synth p f s f' ()) input #pm v);
  fold (pts_to_serialized s input #pm (f' v))
}
```

```pulse
ghost
fn pts_to_serialized_synth_r2l
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (v: t')
  requires pts_to_serialized s input #pm (f' v)
  ensures pts_to_serialized (serialize_synth p f s f' ()) input #pm v
{
  serialize_synth_eq p f s f' () v;
  unfold (pts_to_serialized s input #pm (f' v));
  fold (pts_to_serialized (serialize_synth p f s f' ()) input #pm v)
}
```

```pulse
ghost
fn pts_to_serialized_synth_l2r_trade
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t')
  requires pts_to_serialized (serialize_synth p f s f' ()) input #pm v
  ensures pts_to_serialized s input #pm (f' v) ** trade (pts_to_serialized s input #pm (f' v)) (pts_to_serialized (serialize_synth p f s f' ()) input #pm v)
{
  pts_to_serialized_synth_l2r s f f' input;
  ghost
  fn aux
    (_: unit)
    requires emp ** pts_to_serialized s input #pm (f' v)
    ensures pts_to_serialized (serialize_synth p f s f' ()) input #pm v
  {
    pts_to_serialized_synth_r2l s f f' input v
  };
  intro_trade _ _ _ aux
}
```

```pulse
ghost
fn pts_to_serialized_synth_l2r_trade'
  (#t #t': Type0)
  (#k_: parser_kind)
  (#p_: parser k_ t')
  (#s_: serializer p_)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t')
  requires pts_to_serialized s_ input #pm v ** pure (forall x . parse p_ x == parse (parse_synth p f) x)
  ensures pts_to_serialized s input #pm (f' v) ** trade (pts_to_serialized s input #pm (f' v)) (pts_to_serialized s_ input #pm v)
{
  pts_to_serialized_ext_trade
    s_
    (serialize_synth p f s f' ())
    input;
  pts_to_serialized_synth_l2r_trade
    s f f' input;
  Trade.trans _ _ (pts_to_serialized s_ input #pm v)
}
```

inline_for_extraction
let read_synth_cont_t
  (#t: Type0)
  (x: t)
= (t': Type0) -> (g': ((y: t { y == x }) -> t')) -> (y': t' { y' == g' x })

inline_for_extraction
let read_synth_cont
  (#t1 #t2: Type0)
  (f2: (t1 -> GTot t2))
  (f2': ((x: t1) -> read_synth_cont_t (f2 x)))
  (x1: Ghost.erased t1)
  (t': Type0)
  (g: ((x2: t2 { x2 == f2 x1 }) -> Tot t'))
  (x1': t1 { x1' == Ghost.reveal x1 })
: Tot t'
= f2' x1' t' g

inline_for_extraction
```pulse
fn read_synth
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (r: reader s1)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
  (f2': ((x: t1) -> read_synth_cont_t (f2 x)))
: reader #t2 #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= (input: slice byte)
  (#pm: _)
  (#v: _)
  (t': Type0)
  (g: _)
{
  pts_to_serialized_synth_l2r_trade s1 f2 f1 input;
  let res = r input #pm #(f1 v) t' (read_synth_cont f2 f2' (f1 v) t' g);
  elim_trade _ _;
  res
}
```

inline_for_extraction
let read_synth_cont_init
  (#t: Type0)
  (x: t)
: Tot (read_synth_cont_t #t x)
= fun t' g' -> g' x

inline_for_extraction
let read_synth'
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (r: reader s1)
  (#t2: Type0) (f2: (t1 -> Tot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
: reader #t2 #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= read_synth r f2 f1 (fun x -> read_synth_cont_init (f2 x))

inline_for_extraction
```pulse
fn validate_filter
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: validator p)
  (#s: serializer p)
  (r: leaf_reader s)
  (f: (t -> GTot bool))
  (f': (x: t) -> (y: bool { y == f x }))
: validator #_ #(parse_filter_kind k) (parse_filter p f)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parse_filter_eq p f (Seq.slice v (SZ.v offset) (Seq.length v));
  let offset = !poffset;
  let is_valid = w input poffset;
  if is_valid {
    let off = !poffset;
    let x = read_from_validator_success r input offset off;
    f' x
  } else {
    false
  }
}
```

inline_for_extraction
let validate_filter'_test
  (#t: Type0)
  (f: (t -> bool))
  (x: t)
: Tot (y: bool { y == f x })
= f x

inline_for_extraction
let validate_filter'
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: validator p)
  (#s: serializer p)
  (r: leaf_reader s)
  (f: (t -> bool))
: validator #_ #(parse_filter_kind k) (parse_filter p f)
= validate_filter w r f (validate_filter'_test f)

inline_for_extraction
```pulse
fn jump_filter
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: jumper p)
  (f: (t -> GTot bool))
: jumper #_ #(parse_filter_kind k) (parse_filter p f)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  Classical.forall_intro (parse_filter_eq p f);
  w input offset #pm #v
}
```

inline_for_extraction
let parse_filter_refine_intro
  (#t: Type)
  (f: (t -> GTot bool))
  (v: t)
  (sq: squash (f v == true))
: Tot (parse_filter_refine f)
= v

```pulse
ghost
fn pts_to_serialized_filter_intro
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires (pts_to_serialized s input #pm v ** pure (f v == true))
  ensures exists* (v': parse_filter_refine f) . pts_to_serialized (serialize_filter s f) input #pm v' ** pure ((v' <: t) == v)
{
  unfold (pts_to_serialized s input #pm v);
  fold (pts_to_serialized (serialize_filter s f) input #pm v);
}
```

```pulse
ghost
fn pts_to_serialized_filter_elim
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
  (input: slice byte)
  (#pm: perm)
  (#v: parse_filter_refine f)
  requires (pts_to_serialized (serialize_filter s f) input #pm v)
  ensures pts_to_serialized s input #pm v
{
  unfold (pts_to_serialized (serialize_filter s f) input #pm v);
  fold (pts_to_serialized s input #pm v);
}
```

inline_for_extraction
let read_filter_cont
  (#t: Type0)
  (f: t -> GTot bool)
  (v: Ghost.erased (parse_filter_refine f))
  (t': Type0)
  (g: (x: parse_filter_refine f { x == Ghost.reveal v }) -> t')
  (x: t { x == Ghost.reveal #t (Ghost.hide #t (Ghost.reveal v)) })
: Tot t'
= g x

inline_for_extraction
```pulse
fn read_filter
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (r: reader s1) (f: (t1 -> GTot bool))
: reader #(parse_filter_refine f) #(parse_filter_kind k1) #(parse_filter p1 f) (serialize_filter s1 f)
= (input: slice byte)
  (#pm: _)
  (#v: _)
  (t': Type0)
  (g: _)
{
  pts_to_serialized_filter_elim s1 f input;
  let res = r input #pm #(Ghost.hide (Ghost.reveal v)) t' (read_filter_cont f v t' g);
  pts_to_serialized_filter_intro s1 f input;
  res
}
```

let pair_of_dtuple2
  (#t1 #t2: Type)
  (x: dtuple2 t1 (fun _ -> t2))
: Tot (t1 & t2)
= match x with
  | (| x1, x2 |) -> (x1, x2)

let dtuple2_of_pair
  (#t1 #t2: Type)
  (x: (t1 & t2))
: Tot (dtuple2 t1 (fun _ -> t2))
= match x with
  | (x1, x2) -> (| x1, x2 |)

let const_fun (#t1: Type) (#t2: Type) (x2: t2) (x1: t1) : Tot t2 = x2

let nondep_then_eq_dtuple2
  (#t1 #t2: Type)
  (#k1 #k2: parser_kind)
  (p1: parser k1 t1)
  (p2: parser k2 t2)
  (input: bytes)
: Lemma
  (parse (nondep_then p1 p2) input == parse (parse_synth (parse_dtuple2 p1 #k2 #(const_fun t2) (const_fun p2)) pair_of_dtuple2) input)
= parse_synth_eq (parse_dtuple2 p1 #k2 #(const_fun t2) (const_fun p2)) pair_of_dtuple2 input;
  parse_dtuple2_eq p1 #k2 #(const_fun t2) (const_fun p2) input;
  nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 input

inline_for_extraction
```pulse
fn validate_nondep_then
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (v2: validator p2)
: validator #(t1 & t2) #(and_then_kind k1 k2) (nondep_then #k1 #t1 p1 #k2 #t2 p2)
= 
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  let is_valid1 = v1 input poffset;
  if is_valid1 {
    v2 input poffset
  } else {
    false
  }
}
```

inline_for_extraction
```pulse
fn validate_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (#s1: serializer p1)
  (r1: leaf_reader s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (v2: ((x: t1) -> validator (p2 x)))
: validator #(dtuple2 t1 t2) #(and_then_kind k1 k2) (parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parse_dtuple2_eq p1 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  let offset = !poffset;
  let is_valid1 = v1 input poffset;
  if is_valid1 {
    let off = !poffset;
    let x = read_from_validator_success r1 input offset off;
    v2 x input poffset
  } else {
    false
  }
}
```

inline_for_extraction
```pulse
fn jump_nondep_then
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (v1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (v2: jumper p2)
: jumper #(t1 & t2) #(and_then_kind k1 k2) (nondep_then #k1 #t1 p1 #k2 #t2 p2)
= 
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  nondep_then_eq #k1 p1 #k2 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  pts_to_len input;
  let off1 = v1 input offset;
  v2 input off1
}
```

inline_for_extraction
```pulse
fn jump_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (v1: jumper p1)
  (#s1: serializer p1)
  (r1: leaf_reader s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (v2: (x: t1) -> jumper (p2 x))
: jumper #(dtuple2 t1 t2) #(and_then_kind k1 k2) (parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2)
= 
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parse_dtuple2_eq p1 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  pts_to_len input;
  let off1 = v1 input offset;
  let x = read_from_validator_success r1 input offset off1;
  v2 x input off1
}
```

let split_dtuple2_post'
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased (dtuple2 t1 t2))
  (left right: slice byte)
: Tot slprop
= pts_to_serialized s1 left #pm (dfst v) **
  pts_to_serialized (s2 (dfst v)) right #pm (dsnd v) **
  trade (pts_to_serialized s1 left #pm (dfst v) **
  pts_to_serialized (s2 (dfst v)) right #pm (dsnd v))
    (pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v)

let split_dtuple2_post
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased (dtuple2 t1 t2))
  (res: slice_pair byte)
: Tot slprop
= let (SlicePair left right) = res in
  split_dtuple2_post' s1 s2 input pm v left right

inline_for_extraction
```pulse
fn split_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1 t2))
  requires pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v
  returns res: slice_pair byte
  ensures split_dtuple2_post s1 s2 input pm v res
{
  serialize_dtuple2_eq s1 s2 v;
  Trade.rewrite_with_trade
    (pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v)
    (pts_to input #pm (bare_serialize s1 (dfst v) `Seq.append` bare_serialize (s2 (dfst v)) (dsnd v)));
  parse_serialize_strong_prefix s1 (dfst v) (bare_serialize (s2 (dfst v)) (dsnd v));
  let i = j1 input 0sz;
  let res = append_split_trade false input i;
  match res {
    SlicePair input1 input2 -> {
      unfold (append_split_trade_post input pm (bare_serialize s1 (dfst v)) (bare_serialize (s2 (dfst v)) (dsnd v)) i res);
      unfold (append_split_trade_post' input pm (bare_serialize s1 (dfst v)) (bare_serialize (s2 (dfst v)) (dsnd v)) i input1 input2);
      Trade.trans (_ ** _) _ _;
      pts_to_serialized_intro_trade s1 input1 (dfst v);
      pts_to_serialized_intro_trade (s2 (dfst v)) input2 (dsnd v);
      Trade.prod (pts_to_serialized s1 input1 #pm _) (pts_to input1 #pm _) (pts_to_serialized (s2 (dfst v)) input2 #pm _) (pts_to input2 #pm _);
      Trade.trans (pts_to_serialized s1 input1 #pm _ ** pts_to_serialized (s2 (dfst v)) input2 #pm _) (pts_to input1 #pm _ ** pts_to input2 #pm _) _;
      fold (split_dtuple2_post' s1 s2 input pm v input1 input2);
      fold (split_dtuple2_post s1 s2 input pm v (input1 `SlicePair` input2));
      (input1 `SlicePair` input2)
    }
  }
}
```

inline_for_extraction
```pulse
fn dtuple2_dfst
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1 t2))
  requires pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v
  returns res: slice byte
  ensures pts_to_serialized s1 res #pm (dfst v) **
    trade (pts_to_serialized s1 res #pm (dfst v)) (pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v)
{
  let spl = split_dtuple2 s1 j1 s2 input;
  match spl { SlicePair input1 input2 -> {
    unfold (split_dtuple2_post s1 s2 input pm v spl);
    unfold (split_dtuple2_post' s1 s2 input pm v input1 input2);
    Trade.elim_hyp_r _ _ _;
    input1
  }}
}
```

inline_for_extraction
```pulse
fn dtuple2_dsnd
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1 t2))
  requires pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v
  returns res: slice byte
  ensures pts_to_serialized (s2 (dfst v)) res #pm (dsnd v) **
    trade (pts_to_serialized (s2 (dfst v)) res #pm (dsnd v)) (pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v)
{
  let spl = split_dtuple2 s1 j1 s2 input;
  match spl { SlicePair input1 input2 -> {
    unfold (split_dtuple2_post s1 s2 input pm v spl);
    unfold (split_dtuple2_post' s1 s2 input pm v input1 input2);
    Trade.elim_hyp_l _ _ _;
    input2
  }}
}
```

let split_nondep_then_post'
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased (t1 & t2))
  (left right: slice byte)
: Tot slprop
= pts_to_serialized s1 left #pm (fst v) **
  pts_to_serialized s2 right #pm (snd v) **
  trade (pts_to_serialized s1 left #pm (fst v) **
  pts_to_serialized s2 right #pm (snd v))
    (pts_to_serialized (serialize_nondep_then s1 s2) input #pm v)

let split_nondep_then_post
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased (t1 & t2))
  (res: slice_pair byte)
: Tot slprop
= let (SlicePair left right) = res in
  split_nondep_then_post' s1 s2 input pm v left right

#set-options "--print_implicits"

```pulse
ghost
fn pts_to_serialized_ext_trade'
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2)
  (input: slice byte)
  (prf: (x: bytes) -> Lemma
    (parse p1 x == parse p2 x)
  )
  (#pm: perm)
  (#v: t)
  requires pts_to_serialized s1 input #pm v
  ensures pts_to_serialized s2 input #pm v ** trade (pts_to_serialized s2 input #pm v) (pts_to_serialized s1 input #pm v)
{
  Classical.forall_intro prf;
  pts_to_serialized_ext_trade s1 s2 input
}
```

inline_for_extraction
```pulse
fn split_nondep_then
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  requires pts_to_serialized (serialize_nondep_then s1 s2) input #pm v
  returns res: slice_pair byte
  ensures split_nondep_then_post s1 s2 input pm v res
{
  pts_to_serialized_ext_trade'
    (serialize_nondep_then s1 s2)
    (serialize_synth #(and_then_kind k1 k2) #(_: t1 & t2) #(t1 & t2)
      (parse_dtuple2 #k1 #t1 p1 #k2 #(const_fun t2) (const_fun p2))
      (pair_of_dtuple2 #t1 #t2)
      (serialize_dtuple2 s1 #k2 #(const_fun t2) #(const_fun p2) (const_fun s2))
      dtuple2_of_pair
      ()
    )
    input
    (nondep_then_eq_dtuple2 #t1 #t2 #k1 #k2 p1 p2);
  pts_to_serialized_synth_l2r_trade
    (serialize_dtuple2 s1 #k2 #(const_fun t2) #(const_fun p2) (const_fun s2))
    pair_of_dtuple2
    dtuple2_of_pair
    input;
  Trade.trans (pts_to_serialized (serialize_dtuple2 s1 #k2 #(const_fun t2) #(const_fun p2) (const_fun s2)) _ #pm _) _ _;
  let res = split_dtuple2 #t1 #(const_fun t2) s1 j1 #_ #(const_fun p2) (const_fun s2) input;
  match res { SlicePair input1 input2 -> {
    unfold (split_dtuple2_post #t1 #(const_fun t2) s1 #k2 #(const_fun p2) (const_fun s2) input pm (dtuple2_of_pair v) res);
    unfold (split_dtuple2_post' #t1 #(const_fun t2) s1 #_ #(const_fun p2) (const_fun s2) input pm (dtuple2_of_pair v) input1 input2);
    Trade.trans (_ ** _) _ _;
    fold (split_nondep_then_post' s1 s2 input pm v input1 input2);
    fold (split_nondep_then_post s1 s2 input pm v (input1 `SlicePair` input2));
    (input1 `SlicePair` input2)
  }}
}
```

inline_for_extraction
```pulse
fn nondep_then_fst
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  requires pts_to_serialized (serialize_nondep_then s1 s2) input #pm v
  returns res: slice byte
  ensures pts_to_serialized s1 res #pm (fst v) **
    trade (pts_to_serialized s1 res #pm (fst v)) (pts_to_serialized (serialize_nondep_then s1 s2) input #pm v)
{
  let spl = split_nondep_then s1 j1 s2 input;
  match spl { SlicePair input1 input2 -> {
    unfold (split_nondep_then_post s1 s2 input pm v spl);
    unfold (split_nondep_then_post' s1 s2 input pm v input1 input2);
    Trade.elim_hyp_r _ _ _;
    input1
  }}
}
```

inline_for_extraction
```pulse
fn nondep_then_snd
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  requires pts_to_serialized (serialize_nondep_then s1 s2) input #pm v
  returns res: slice byte
  ensures pts_to_serialized s2 res #pm (snd v) **
    trade (pts_to_serialized s2 res #pm (snd v)) (pts_to_serialized (serialize_nondep_then s1 s2) input #pm v)
{
  let spl = split_nondep_then s1 j1 s2 input;
  match spl { SlicePair input1 input2 -> {
    unfold (split_nondep_then_post s1 s2 input pm v spl);
    unfold (split_nondep_then_post' s1 s2 input pm v input1 input2);
    Trade.elim_hyp_l _ _ _;
    input2
  }}
}
```

inline_for_extraction
```pulse
fn read_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (j1: jumper p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#s1: serializer p1)
  (r1: reader s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (#s2: (x: t1) -> serializer (p2 x))
  (r2: (x: t1) -> reader (s2 x))
: reader #(dtuple2 t1 t2) #(and_then_kind k1 k2) #(parse_dtuple2 p1 p2) (serialize_dtuple2 s1 s2)
=   
  (input: slice byte)
  (#pm: perm)
  (#v: _)
  (t': Type0)
  (f: _)
{
  let split12 = split_dtuple2 s1 j1 s2 input;
  match split12 { SlicePair input1 input2 -> {
    unfold (split_dtuple2_post s1 s2 input pm v split12);
    unfold (split_dtuple2_post' s1 s2 input pm v input1 input2);
    let x1 = leaf_reader_of_reader r1 input1;
    let x2 = leaf_reader_of_reader (r2 x1) input2;
    elim_trade _ _;
    f (Mkdtuple2 x1 x2)
  }}
}
```

inline_for_extraction // because Karamel does not like tuple2
let cpair (t1 t2: Type) = dtuple2 t1 (fun _ -> t2)

let vmatch_dep_prod
  (#tl1 #tl2 #th1: Type)
  (#th2: th1 -> Type)
  (vmatch1: tl1 -> th1 -> slprop)
  (vmatch2: (x: th1) -> tl2 -> th2 x -> slprop)
  (xl: (tl1 `cpair` tl2))
  (xh: dtuple2 th1 th2)
: Tot slprop
= vmatch1 (dfst xl) (dfst xh) ** vmatch2 (dfst xh) (dsnd xl) (dsnd xh)

inline_for_extraction
```pulse
fn size_dtuple2
  (#tl1 #tl2 #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: compute_remaining_size vmatch1 s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#vmatch2: (x: th1) -> tl2 -> th2 x -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xl: tl1) -> (xh: Ghost.erased th1) -> compute_remaining_size (vmatch_and_const (vmatch1 xl xh) (vmatch2 xh)) (s2 xh))
: compute_remaining_size #(tl1 `cpair` tl2) #(dtuple2 th1 th2) (vmatch_dep_prod vmatch1 vmatch2) #(and_then_kind k1 k2) #(parse_dtuple2 p1 p2) (serialize_dtuple2 s1 s2)
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  serialize_dtuple2_eq s1 s2 x;
  unfold (vmatch_dep_prod vmatch1 vmatch2);
  let res1 = w1 (dfst x') #(dfst x) out;
  if res1 {
    fold (vmatch_and_const (vmatch1 (dfst x') (dfst x)) (vmatch2 (dfst x)) (dsnd x') (dsnd x));
    let res2 = w2 (dfst x') (dfst x) (dsnd x') #(dsnd x) out;
    unfold (vmatch_and_const (vmatch1 (dfst x') (dfst x)) (vmatch2 (dfst x)) (dsnd x') (dsnd x));
    fold (vmatch_dep_prod vmatch1 vmatch2);
    res2
  } else {
    fold (vmatch_dep_prod vmatch1 vmatch2);
    false
  }
}
```

module S = Pulse.Lib.Slice

inline_for_extraction
```pulse
fn l2r_write_dtuple2
  (#tl1 #tl2 #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: l2r_writer vmatch1 s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#vmatch2: (x: th1) -> tl2 -> th2 x -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xl: tl1) -> (xh: Ghost.erased th1) -> l2r_writer (vmatch_and_const (vmatch1 xl xh) (vmatch2 xh)) (s2 xh))
: l2r_writer #(tl1 `cpair` tl2) #(dtuple2 th1 th2) (vmatch_dep_prod vmatch1 vmatch2) #(and_then_kind k1 k2) #(parse_dtuple2 p1 p2) (serialize_dtuple2 s1 s2)
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  serialize_dtuple2_eq s1 s2 x;
  unfold (vmatch_dep_prod vmatch1 vmatch2);
  let res1 = w1 (dfst x') #(dfst x) out offset;
  with v1 . assert (S.pts_to out v1);
  fold (vmatch_and_const (vmatch1 (dfst x') (dfst x)) (vmatch2 (dfst x)) (dsnd x') (dsnd x));
  let res2 = w2 (dfst x') (dfst x) (dsnd x') #(dsnd x) out res1;
  with v2 . assert (S.pts_to out v2);
  Seq.slice_slice v1 0 (SZ.v res1) (SZ.v offset) (SZ.v res1);
  Seq.slice_slice v1 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 0 (SZ.v res1) 0 (SZ.v offset);
  unfold (vmatch_and_const (vmatch1 (dfst x') (dfst x)) (vmatch2 (dfst x)) (dsnd x') (dsnd x));
  fold (vmatch_dep_prod vmatch1 vmatch2);
  res2
}
```

let vmatch_dep_proj2
  (#tl #th1: Type)
  (#th2: th1 -> Type)
  (vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (xh1: th1)
  (xl: tl)
  (xh2: th2 xh1)
: Tot slprop
= vmatch xl (| xh1, xh2 |)

inline_for_extraction
```pulse
fn l2r_write_dtuple2_recip
  (#tl #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (#vmatch1: tl -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: l2r_writer vmatch1 s1)
  (phi: (xl: tl) -> (xh: Ghost.erased (dtuple2 th1 th2)) -> stt_ghost unit emp_inames
    (vmatch xl xh)
    (fun _ -> vmatch1 xl (dfst xh) ** trade (vmatch1 xl (dfst xh)) (vmatch xl xh))
  )
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh1: Ghost.erased th1) -> l2r_writer (vmatch_dep_proj2 vmatch xh1) (s2 xh1))
: l2r_writer #tl #(dtuple2 th1 th2) vmatch #(and_then_kind k1 k2) #(parse_dtuple2 p1 p2) (serialize_dtuple2 s1 s2)
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  serialize_dtuple2_eq s1 s2 x;
  phi x' x;
  let res1 = w1 x' out offset;
  Trade.elim _ _;
  with v1 . assert (S.pts_to out v1);
  Trade.rewrite_with_trade 
    (vmatch x' x)
    (vmatch x' (| dfst x, dsnd x |));
  fold (vmatch_dep_proj2 vmatch (dfst x) x' (dsnd x));
  let res2 = w2 (dfst x) x' out res1;
  unfold (vmatch_dep_proj2 vmatch (dfst x) x' (dsnd x));
  Trade.elim _ _;
  with v2 . assert (S.pts_to out v2);
  Seq.slice_slice v1 0 (SZ.v res1) (SZ.v offset) (SZ.v res1);
  Seq.slice_slice v1 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 0 (SZ.v res1) 0 (SZ.v offset);
  res2
}
```

inline_for_extraction
```pulse
fn l2r_write_dtuple2_recip_explicit_header
  (#tl #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: l2r_leaf_writer s1)
  (phi: (xl: tl) -> (xh: Ghost.erased (dtuple2 th1 th2)) -> stt th1
    (vmatch xl xh)
    (fun res -> vmatch xl xh ** pure (res == dfst xh))
  )
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh1: th1) -> l2r_writer (vmatch_dep_proj2 vmatch xh1) (s2 xh1))
: l2r_writer #tl #(dtuple2 th1 th2) vmatch #(and_then_kind k1 k2) #(parse_dtuple2 p1 p2) (serialize_dtuple2 s1 s2)
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  serialize_dtuple2_eq s1 s2 x;
  let xh1 = phi x' x;
  let res1 = w1 xh1 out offset;
  with v1 . assert (S.pts_to out v1);
  Trade.rewrite_with_trade 
    (vmatch x' x)
    (vmatch x' (| xh1, dsnd x |));
  fold (vmatch_dep_proj2 vmatch xh1 x' (dsnd x));
  let res2 = w2 xh1 x' out res1;
  unfold (vmatch_dep_proj2 vmatch xh1 x' (dsnd x));
  Trade.elim _ _;
  with v2 . assert (S.pts_to out v2);
  Seq.slice_slice v1 0 (SZ.v res1) (SZ.v offset) (SZ.v res1);
  Seq.slice_slice v1 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 0 (SZ.v res1) 0 (SZ.v offset);
  res2
}
```

inline_for_extraction
```pulse
fn size_nondep_then
  (#tl1 #tl2 #th1 #th2: Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: compute_remaining_size vmatch1 s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#vmatch2: tl2 -> th2 -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 th2)
  (#s2: serializer p2)
  (w2: compute_remaining_size vmatch2 s2)
  (#tl: Type0)
  (vmatch: tl -> (th1 & th2) -> slprop)
  (f1: (xl: tl) -> (xh: Ghost.erased (th1 & th2)) -> stt tl1
    (vmatch xl xh)
    (fun xl1 -> vmatch1 xl1 (fst xh) ** trade (vmatch1 xl1 (fst xh)) (vmatch xl xh))
  )
  (f2: (xl: tl) -> (xh: Ghost.erased (th1 & th2)) -> stt tl2
    (vmatch xl xh)
    (fun xl2 -> vmatch2 xl2 (snd xh) ** trade (vmatch2 xl2 (snd xh)) (vmatch xl xh))
  )
: compute_remaining_size #tl #(th1 & th2) vmatch #(and_then_kind k1 k2) #(nondep_then p1 p2) (serialize_nondep_then s1 s2)
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
 serialize_nondep_then_eq s1 s2 x;
 let x1 = f1 x' x;
 let res1 = w1 x1 #(Ghost.hide (fst x)) out #v;
 Trade.elim _ _;
 if res1 {
   let x2 = f2 x' x;
   let res2 = w2 x2 #(Ghost.hide (snd x)) out;
   Trade.elim _ _;
   res2
 } else {
   false
 }
}
```

inline_for_extraction
```pulse
fn l2r_write_nondep_then
  (#tl1 #tl2 #th1 #th2: Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: l2r_writer vmatch1 s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#vmatch2: tl2 -> th2 -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 th2)
  (#s2: serializer p2)
  (w2: l2r_writer vmatch2 s2)
  (#tl: Type0)
  (vmatch: tl -> (th1 & th2) -> slprop)
  (f1: (xl: tl) -> (xh: Ghost.erased (th1 & th2)) -> stt tl1
    (vmatch xl xh)
    (fun xl1 -> vmatch1 xl1 (fst xh) ** trade (vmatch1 xl1 (fst xh)) (vmatch xl xh))
  )
  (f2: (xl: tl) -> (xh: Ghost.erased (th1 & th2)) -> stt tl2
    (vmatch xl xh)
    (fun xl2 -> vmatch2 xl2 (snd xh) ** trade (vmatch2 xl2 (snd xh)) (vmatch xl xh))
  )
: l2r_writer #tl #(th1 & th2) vmatch #(and_then_kind k1 k2) #(nondep_then p1 p2) (serialize_nondep_then s1 s2)
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  serialize_nondep_then_eq s1 s2 x;
  let x1 = f1 x' x;
  let res1 = w1 x1 #(Ghost.hide (fst x)) out offset;
  with v1 . assert (S.pts_to out v1);
  Trade.elim _ _;
  let x2 = f2 x' x;
  let res2 = w2 x2 #(Ghost.hide (snd x)) out res1;
  with v2 . assert (S.pts_to out v2);
  Seq.slice_slice v1 0 (SZ.v res1) (SZ.v offset) (SZ.v res1);
  Seq.slice_slice v1 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 0 (SZ.v res1) 0 (SZ.v offset);
  Trade.elim _ _;
  res2
}
```

inline_for_extraction
```pulse
fn l2r_leaf_write_synth
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (w: l2r_leaf_writer u#0 s1)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
  (f1': ((x2: t2) -> (x1: t1 { x1 == f1 x2 })))
: l2r_leaf_writer u#0 #t2 #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
=
  (x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  serialize_synth_eq p1 f2 s1 f1 () x;
  w (f1' x) out offset
}
```

inline_for_extraction
let mk_synth
  (#t1 #t2: Type)
  (f: (t1 -> Tot t2))
  (x: t1)
: Tot (y: t2 { y == f x })
= f x

inline_for_extraction
let l2r_leaf_write_synth'
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (w: l2r_leaf_writer u#0 s1)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> Tot t1) { synth_inverse f2 f1 })
: l2r_leaf_writer u#0 #t2 #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= l2r_leaf_write_synth w f2 f1 (mk_synth f1)

let vmatch_synth
  (#tl: Type)
  (#th1 #th2: Type)
  (vmatch: tl -> th1 -> slprop)
  (f21: th2 -> GTot th1)
  (xh: tl)
  (xl2: th2)
: slprop
= vmatch xh (f21 xl2)

inline_for_extraction
```pulse
fn size_synth
  (#t: Type0) (#t1: Type0) (#t2: Type0)
  (vmatch: t -> t1 -> slprop)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: compute_remaining_size vmatch s1)
  (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
: compute_remaining_size #t #t2 (vmatch_synth vmatch f1) #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  serialize_synth_eq p1 f2 s1 f1 () x;
  unfold (vmatch_synth vmatch f1 x' x);
  let res = w x' out;
  fold (vmatch_synth vmatch f1 x' x);
  res
}
```

inline_for_extraction
```pulse
fn l2r_write_synth
  (#t: Type0) (#t1: Type0) (#t2: Type0)
  (vmatch: t -> t1 -> slprop)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: l2r_writer vmatch s1)
  (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
: l2r_writer #t #t2 (vmatch_synth vmatch f1) #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  serialize_synth_eq p1 f2 s1 f1 () x;
  unfold (vmatch_synth vmatch f1 x' x);
  let res = w x' out offset;
  fold (vmatch_synth vmatch f1 x' x);
  res
}
```

inline_for_extraction
```pulse
fn l2r_write_synth_recip
  (#t: Type0) (#t1: Type0) (#t2: Type0)
  (vmatch: t -> t2 -> slprop)
  (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: l2r_writer (vmatch_synth vmatch f2) s1)
: l2r_writer #t #t2 vmatch #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  serialize_synth_eq p1 f2 s1 f1 () x;
  Trade.rewrite_with_trade
    (vmatch x' x)
    (vmatch x' (f2 (f1 x)));
  fold (vmatch_synth vmatch f2 x' (f1 x));
  let res = w x' out offset;
  unfold (vmatch_synth vmatch f2 x' (f1 x));
  Trade.elim _ _;
  res
}
```

let vmatch_filter
  (#tl: Type0)
  (#th: Type0)
  (vmatch: tl -> th -> slprop)
  (f: th -> GTot bool)
: Tot (tl -> parse_filter_refine f -> slprop)
= vmatch


#set-options "--print_universes --print_implicits"

inline_for_extraction
```pulse
fn l2r_leaf_write_filter
  (#t1: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: l2r_leaf_writer #t1 s1)
  (f: (t1 -> GTot bool))
: l2r_leaf_writer u#0 #(parse_filter_refine u#0 f) #(parse_filter_kind k1) #(parse_filter p1 f) (serialize_filter s1 f)
= (x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  w x out offset
}
```

inline_for_extraction
```pulse
fn l2r_write_filter
  (#t: Type0) (#t1: Type0)
  (vmatch: t -> t1 -> slprop)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: l2r_writer #t #t1 vmatch s1)
  (f: (t1 -> GTot bool))
: l2r_writer #t #(parse_filter_refine u#0 f) (vmatch_filter vmatch f) #(parse_filter_kind k1) #(parse_filter p1 f) (serialize_filter s1 f)
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  unfold (vmatch_filter vmatch f x' x);
  let res = w x' #(Ghost.hide #t1 (Ghost.reveal x)) out offset;
  fold (vmatch_filter vmatch f x' x);
  res
}
```

let vmatch_filter_recip
  (#tl: Type0)
  (#th: Type0)
  (f: th -> GTot bool)
  (vmatch: tl -> parse_filter_refine f -> slprop)
  (xl: tl)
  (xh: th)
: Tot slprop
= exists* (xh' : parse_filter_refine f) . vmatch xl xh' ** pure (xh == xh')

inline_for_extraction
```pulse
fn l2r_write_filter_recip
  (#t: Type0) (#t1: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1)
  (f: (t1 -> GTot bool))
  (vmatch: t -> parse_filter_refine f -> slprop)
  (w: l2r_writer (vmatch_filter_recip f vmatch) s1)
: l2r_writer #t #(parse_filter_refine u#0 f) vmatch #(parse_filter_kind k1) #(parse_filter p1 f) (serialize_filter s1 f)
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  fold (vmatch_filter_recip f vmatch x' x);
  let res = w x' #(Ghost.hide (Ghost.reveal x)) out offset;
  unfold (vmatch_filter_recip f vmatch x' x);
  with xh . assert (vmatch x' xh);
  rewrite (vmatch x' xh) as (vmatch x' x);
  res
}
```

inline_for_extraction
```pulse
fn size_filter
  (#t: Type0) (#t1: Type0)
  (vmatch: t -> t1 -> slprop)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: compute_remaining_size #t #t1 vmatch s1)
  (f: (t1 -> GTot bool))
: compute_remaining_size #t #(parse_filter_refine u#0 f) (vmatch_filter vmatch f) #(parse_filter_kind k1) #(parse_filter p1 f) (serialize_filter s1 f)
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  unfold (vmatch_filter vmatch f x' x);
  let res = w x' #(Ghost.hide #t1 (Ghost.reveal x)) out;
  fold (vmatch_filter vmatch f x' x);
  res
}
```

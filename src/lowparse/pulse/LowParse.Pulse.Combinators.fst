module LowParse.Pulse.Combinators
include LowParse.Spec.Combinators
include LowParse.Pulse.Base
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
```pulse
fn validate_ret
  (#t: Type0)
  (x: t)
: validator #t #parse_ret_kind (tot_parse_ret x)
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
: leaf_reader #t #parse_ret_kind #(tot_parse_ret x) (tot_serialize_ret x v_unique)
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
: Tot (reader (tot_serialize_ret x v_unique))
= reader_of_leaf_reader (leaf_read_ret x v_unique)

inline_for_extraction
let jump_ret (#t: Type) (x: t) : jumper (tot_parse_ret x) = jump_constant_size (tot_parse_ret x) 0sz 

inline_for_extraction
let validate_empty : validator tot_parse_empty = validate_ret ()

inline_for_extraction
let leaf_read_empty : leaf_reader tot_serialize_empty = leaf_read_ret () (fun _ -> ())

inline_for_extraction
let read_empty : reader tot_serialize_empty = reader_of_leaf_reader leaf_read_empty

inline_for_extraction
let jump_empty : jumper tot_parse_empty = jump_ret ()

let parse_serialize_strong_prefix
  (#t: Type)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: tot_serializer p)
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

let tot_parse_synth_eq'
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: tot_parser k t1)
  (f2: (t1 -> Tot t2) {synth_injective f2})
  (b: bytes)
: Lemma
  (ensures (parse (tot_parse_synth p1 f2) b == parse_synth' #k p1 f2 b))
= parse_synth_eq #k p1 f2 b

inline_for_extraction
```pulse
fn validate_synth
  (#t #t': Type)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (w: validator p)
  (f: (t -> t') { synth_injective f })
: validator #t' #k (tot_parse_synth p f)
= (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  tot_parse_synth_eq' p f (Seq.slice v (SZ.v offset) (Seq.length v));
  w input poffset #offset #pm #v
}
```

inline_for_extraction
```pulse
fn jump_synth
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (w: jumper p)
  (f: (t -> t') { synth_injective f })
: jumper #t' #k (tot_parse_synth #k #t p f)
=
  (input: _)
  (offset: _)
  (#pm: _)
  (#v: _)
{    
  tot_parse_synth_eq' p f (Seq.slice v (SZ.v offset) (Seq.length v));
  w input offset #pm #v
}
```

```pulse
ghost
fn pts_to_serialized_synth_intro
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (f: (t -> t') { synth_injective f })
  (f': (t' -> t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_serialized s input #pm v
  ensures pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm (f v)
{
  tot_parse_synth_eq p f (bare_serialize s v);
  parse_serialize #k #t' #(tot_parse_synth p f) (tot_serialize_synth p f s f' ()) (f v);
  parse_injective #k #t' (tot_parse_synth p f) (bare_serialize s v) (bare_serialize (tot_serialize_synth p f s f' ()) (f v));
  unfold (pts_to_serialized s input #pm v);
  rewrite (pts_to input #pm (bare_serialize s v))
    as (pts_to input #pm (bare_serialize (tot_serialize_synth p f s f' ()) (f v)));
  fold (pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm (f v))
}
```

```pulse
ghost
fn pts_to_serialized_synth_elim
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (f: (t -> t') { synth_injective f })
  (f': (t' -> t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (v: t)
  requires pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm (f v)
  ensures pts_to_serialized s input #pm v
{
  tot_parse_synth_eq p f (bare_serialize s v);
  parse_serialize #k #t' #(tot_parse_synth p f) (tot_serialize_synth p f s f' ()) (f v);
  parse_injective #k #t' (tot_parse_synth p f) (bare_serialize s v) (bare_serialize (tot_serialize_synth p f s f' ()) (f v));
  unfold (pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm (f v));
  rewrite (pts_to input #pm (bare_serialize (tot_serialize_synth p f s f' ()) (f v)))
    as (pts_to input #pm (bare_serialize s v));
  fold (pts_to_serialized s input #pm v)
}
```

```pulse
ghost
fn pts_to_serialized_synth_trade
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (f: (t -> t') { synth_injective f })
  (f': (t' -> t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_serialized s input #pm v
  ensures pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm (f v) ** trade (pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm (f v)) (pts_to_serialized s input #pm v)
{
  pts_to_serialized_synth_intro s f f' input;
  ghost
  fn aux
    (_: unit)
    requires emp ** pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm (f v)
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
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (f: (t -> t') { synth_injective f })
  (f': (t' -> t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t')
  requires pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm v
  ensures pts_to_serialized s input #pm (f' v)
{
  tot_serialize_synth_eq p f s f' () v;
  unfold (pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm v);
  fold (pts_to_serialized s input #pm (f' v))
}
```

```pulse
ghost
fn pts_to_serialized_synth_r2l
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (f: (t -> t') { synth_injective f })
  (f': (t' -> t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (v: t')
  requires pts_to_serialized s input #pm (f' v)
  ensures pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm v
{
  tot_serialize_synth_eq p f s f' () v;
  unfold (pts_to_serialized s input #pm (f' v));
  fold (pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm v)
}
```

```pulse
ghost
fn pts_to_serialized_synth_l2r_trade
  (#t #t': Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (f: (t -> t') { synth_injective f })
  (f': (t' -> t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t')
  requires pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm v
  ensures pts_to_serialized s input #pm (f' v) ** trade (pts_to_serialized s input #pm (f' v)) (pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm v)
{
  pts_to_serialized_synth_l2r s f f' input;
  ghost
  fn aux
    (_: unit)
    requires emp ** pts_to_serialized s input #pm (f' v)
    ensures pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm v
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
  (#p_: tot_parser k_ t')
  (#s_: tot_serializer p_)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (f: (t -> t') { synth_injective f })
  (f': (t' -> t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t')
  requires pts_to_serialized s_ input #pm v ** pure (forall x . parse p_ x == parse (tot_parse_synth p f) x)
  ensures pts_to_serialized s input #pm (f' v) ** trade (pts_to_serialized s input #pm (f' v)) (pts_to_serialized s_ input #pm v)
{
  pts_to_serialized_ext_trade
    s_
    (tot_serialize_synth p f s f' ())
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
  (f2: (t1 -> Tot t2))
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
  (#k1: parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (r: reader s1)
  (#t2: Type0) (f2: (t1 -> Tot t2) { synth_injective f2 }) (f1: (t2 -> Tot t1) { synth_inverse f2 f1 })
  (f2': ((x: t1) -> read_synth_cont_t (f2 x)))
: reader #t2 #k1 #(tot_parse_synth p1 f2) (tot_serialize_synth p1 f2 s1 f1 ())
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
  (#k1: parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (r: reader s1)
  (#t2: Type0) (f2: (t1 -> Tot t2) { synth_injective f2 }) (f1: (t2 -> Tot t1) { synth_inverse f2 f1 })
: reader #t2 #k1 #(tot_parse_synth p1 f2) (tot_serialize_synth p1 f2 s1 f1 ())
= read_synth r f2 f1 (fun x -> read_synth_cont_init (f2 x))

inline_for_extraction
```pulse
fn validate_filter
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (w: validator p)
  (#s: serializer p)
  (r: leaf_reader s)
  (f: (t -> bool))
  (f': (x: t) -> (y: bool { y == f x }))
: validator #_ #(parse_filter_kind k) (tot_parse_filter p f)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  tot_parse_filter_eq p f (Seq.slice v (SZ.v offset) (Seq.length v));
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
  (#k: parser_kind)
  (#p: tot_parser k t)
  (w: validator p)
  (#s: serializer p)
  (r: leaf_reader s)
  (f: (t -> bool))
: validator #_ #(parse_filter_kind k) (tot_parse_filter p f)
= validate_filter w r f (validate_filter'_test f)

inline_for_extraction
```pulse
fn jump_filter
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (w: jumper p)
  (f: (t -> bool))
: jumper #_ #(parse_filter_kind k) (tot_parse_filter p f)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  Classical.forall_intro (tot_parse_filter_eq p f);
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
  (#p: tot_parser k t)
  (s: serializer p)
  (f: (t -> bool))
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires (pts_to_serialized s input #pm v ** pure (f v == true))
  ensures exists* (v': parse_filter_refine f) . pts_to_serialized (tot_serialize_filter s f) input #pm v' ** pure ((v' <: t) == v)
{
  unfold (pts_to_serialized s input #pm v);
  fold (pts_to_serialized (tot_serialize_filter s f) input #pm v);
}
```

```pulse
ghost
fn pts_to_serialized_filter_elim
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: serializer p)
  (f: (t -> bool))
  (input: slice byte)
  (#pm: perm)
  (#v: parse_filter_refine f)
  requires (pts_to_serialized (tot_serialize_filter s f) input #pm v)
  ensures pts_to_serialized s input #pm v
{
  unfold (pts_to_serialized (tot_serialize_filter s f) input #pm v);
  fold (pts_to_serialized s input #pm v);
}
```

inline_for_extraction
let read_filter_cont
  (#t: Type0)
  (f: t -> bool)
  (v: Ghost.erased (parse_filter_refine f))
  (t': Type0)
  (g: (x: parse_filter_refine f { x == Ghost.reveal v }) -> t')
  (x: t { x == Ghost.reveal #t (Ghost.hide #t (Ghost.reveal v)) })
: Tot t'
= g x

inline_for_extraction
```pulse
fn read_filter
  (#k1: parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (r: reader s1) (f: (t1 -> bool))
: reader #(parse_filter_refine f) #(parse_filter_kind k1) #(tot_parse_filter p1 f) (tot_serialize_filter s1 f)
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

let nondep_then_eq_dtuple2
  (#t1 #t2: Type)
  (#k1 #k2: parser_kind)
  (p1: tot_parser k1 t1)
  (p2: tot_parser k2 t2)
  (input: bytes)
: Lemma
  (parse (tot_nondep_then p1 p2) input == parse (tot_parse_synth (tot_parse_dtuple2 p1 (fun _ -> p2)) pair_of_dtuple2) input)
= tot_parse_synth_eq (tot_parse_dtuple2 p1 (fun _ -> p2)) pair_of_dtuple2 input;
  nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 input

inline_for_extraction
```pulse
fn validate_nondep_then
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (v2: validator p2)
: validator #(t1 & t2) #(and_then_kind k1 k2) (tot_nondep_then #k1 #t1 p1 #k2 #t2 p2)
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
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (#s1: serializer p1)
  (r1: leaf_reader s1)
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (v2: ((x: t1) -> validator (p2 x)))
: validator #(dtuple2 t1 t2) #(and_then_kind k1 k2) (tot_parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
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
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (v1: jumper p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (v2: jumper p2)
: jumper #(t1 & t2) #(and_then_kind k1 k2) (tot_nondep_then #k1 #t1 p1 #k2 #t2 p2)
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
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (v1: jumper p1)
  (#s1: serializer p1)
  (r1: leaf_reader s1)
  (#k2: parser_kind)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (v2: (x: t1) -> jumper (p2 x))
: jumper #(dtuple2 t1 t2) #(and_then_kind k1 k2) (tot_parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2)
= 
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
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
: Tot vprop
= pts_to_serialized s1 left #pm (dfst v) **
  pts_to_serialized (s2 (dfst v)) right #pm (dsnd v) **
  trade (pts_to_serialized s1 left #pm (dfst v) **
  pts_to_serialized (s2 (dfst v)) right #pm (dsnd v))
    (pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v)

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
: Tot vprop
= let (SlicePair left right) = res in
  split_dtuple2_post' s1 s2 input pm v left right

inline_for_extraction
```pulse
fn split_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1 t2))
  requires pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v
  returns res: slice_pair byte
  ensures split_dtuple2_post s1 s2 input pm v res
{
  Trade.rewrite_with_trade
    (pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v)
    (pts_to input #pm (bare_serialize s1 (dfst v) `Seq.append` bare_serialize (s2 (dfst v)) (dsnd v)));
  parse_serialize_strong_prefix s1 (dfst v) (bare_serialize (s2 (dfst v)) (dsnd v));
  let i = j1 input 0sz;
  let res = slice_append_split_trade false input i;
  match res {
    SlicePair input1 input2 -> {
      unfold (slice_append_split_trade_post input pm (bare_serialize s1 (dfst v)) (bare_serialize (s2 (dfst v)) (dsnd v)) i res);
      unfold (slice_append_split_trade_post' input pm (bare_serialize s1 (dfst v)) (bare_serialize (s2 (dfst v)) (dsnd v)) i input1 input2);
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
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1 t2))
  requires pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v
  returns res: slice byte
  ensures pts_to_serialized s1 res #pm (dfst v) **
    trade (pts_to_serialized s1 res #pm (dfst v)) (pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v)
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
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1 t2))
  requires pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v
  returns res: slice byte
  ensures pts_to_serialized (s2 (dfst v)) res #pm (dsnd v) **
    trade (pts_to_serialized (s2 (dfst v)) res #pm (dsnd v)) (pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v)
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
: Tot vprop
= pts_to_serialized s1 left #pm (fst v) **
  pts_to_serialized s2 right #pm (snd v) **
  trade (pts_to_serialized s1 left #pm (fst v) **
  pts_to_serialized s2 right #pm (snd v))
    (pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v)

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
: Tot vprop
= let (SlicePair left right) = res in
  split_nondep_then_post' s1 s2 input pm v left right

inline_for_extraction
```pulse
fn split_nondep_then
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  requires pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v
  returns res: slice_pair byte
  ensures split_nondep_then_post s1 s2 input pm v res
{
  Classical.forall_intro (nondep_then_eq_dtuple2 p1 p2);
  pts_to_serialized_ext_trade
    (tot_serialize_nondep_then s1 s2)
    (tot_serialize_synth
      (tot_parse_dtuple2 p1 (fun _ -> p2))
      pair_of_dtuple2
      (tot_serialize_dtuple2 s1 (fun _ -> s2))
      dtuple2_of_pair
      ()
    )
    input;
  pts_to_serialized_synth_l2r_trade
    (tot_serialize_dtuple2 s1 (fun _ -> s2))
    pair_of_dtuple2
    dtuple2_of_pair
    input;
  Trade.trans (pts_to_serialized (tot_serialize_dtuple2 s1 (fun _ -> s2)) _ #pm _) _ _;
  let res = split_dtuple2 s1 j1 (fun _ -> s2) input;
  match res { SlicePair input1 input2 -> {
    unfold (split_dtuple2_post s1 (fun _ -> s2) input pm (dtuple2_of_pair v) res);
    unfold (split_dtuple2_post' s1 (fun _ -> s2) input pm (dtuple2_of_pair v) input1 input2);
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
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  requires pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v
  returns res: slice byte
  ensures pts_to_serialized s1 res #pm (fst v) **
    trade (pts_to_serialized s1 res #pm (fst v)) (pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v)
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
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  requires pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v
  returns res: slice byte
  ensures pts_to_serialized s2 res #pm (snd v) **
    trade (pts_to_serialized s2 res #pm (snd v)) (pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v)
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
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (j1: jumper p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#s1: serializer p1)
  (r1: reader s1)
  (#k2: parser_kind)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (#s2: (x: t1) -> serializer (p2 x))
  (r2: (x: t1) -> reader (s2 x))
: reader #(dtuple2 t1 t2) #(and_then_kind k1 k2) #(tot_parse_dtuple2 p1 p2) (tot_serialize_dtuple2 s1 s2)
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

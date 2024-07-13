module LowParse.Pulse.Combinators
include LowParse.Spec.Combinators
include LowParse.Pulse.Base
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Stick
open Pulse.Lib.Slice

module SZ = FStar.SizeT

inline_for_extraction
```pulse
fn validate_ret
  (#t: Type0)
  (x: t)
: validator #t #parse_ret_kind (tot_parse_ret x)
= (input: slice byte)
  (offset: _)
  (#pm: _)
  (#v: _)
  (pre: _)
  (t': Type0)
  (post: _)
  (ksucc: _)
  (kfail: _)
{
  ksucc 0sz
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
let validate_and_read_ret
  (#t: Type0)
  (x: t)
  (v_unique: (v' : t) -> Lemma (x == v'))
: Tot (validate_and_read (tot_parse_ret x))
= validate_and_read_intro (validate_ret x) (leaf_read_ret x v_unique)

inline_for_extraction
let jump_ret (#t: Type) (x: t) : jumper (tot_parse_ret x) = jump_constant_size (tot_parse_ret x) 0sz 

inline_for_extraction
let validate_empty : validator tot_parse_empty = validate_ret ()

inline_for_extraction
let leaf_read_empty : leaf_reader tot_serialize_empty = leaf_read_ret () (fun _ -> ())

inline_for_extraction
let read_empty : reader tot_serialize_empty = reader_of_leaf_reader leaf_read_empty

inline_for_extraction
let validate_and_read_empty : validate_and_read tot_parse_empty =
  validate_and_read_intro validate_empty leaf_read_empty

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
let validate_synth
  (#t #t': Type)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (w: validator p)
  (f: (t -> t') { synth_injective f })
: Tot (validator (tot_parse_synth p f))
= Classical.forall_intro (tot_parse_synth_eq' p f);
  w

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
fn pts_to_serialized_synth_stick
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
  ensures pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm (f v) ** (pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm (f v) @==> pts_to_serialized s input #pm v)
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
  intro_stick _ _ _ aux
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
fn pts_to_serialized_synth_l2r_stick
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
  ensures pts_to_serialized s input #pm (f' v) ** (pts_to_serialized s input #pm (f' v) @==> pts_to_serialized (tot_serialize_synth p f s f' ()) input #pm v)
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
  intro_stick _ _ _ aux
}
```

inline_for_extraction
let stt_cps
  (#t: Type)
  (y: t)
: Tot Type
= (pre: vprop) -> (t': Type0) -> (post: (t' -> vprop)) -> (phi: ((y': t { y' == y }) -> stt t' pre (fun x -> post x))) -> stt t' pre (fun x -> post x)

inline_for_extraction
let intro_stt_cps
  (#t: Type)
  (y: t)
: Tot (stt_cps y)
= fun pre t' post phi -> phi y

inline_for_extraction
let elim_stt_cps
  (#t: Type)
  (y: Ghost.erased t)
  (cps: stt_cps (Ghost.reveal y))
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (phi: ((y': t { y' == Ghost.reveal y }) -> stt t' pre (fun x -> post x)))
: stt t' pre (fun x -> post x)
= cps pre t' post phi

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
  pts_to_serialized_synth_l2r_stick s1 f2 f1 input;
  let res = r input #pm #(f1 v) t' (read_synth_cont f2 f2' (f1 v) t' g);
  elim_stick _ _;
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
fn validate_and_read_synth_cont_cont
  (#k1: parser_kind) (#t1: Type0) (p1: parser k1 t1)
  (#t2: Type0) (f2: (t1 -> Tot t2) { synth_injective f2 })
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased bytes)
  (offset: SZ.t)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (cont: (off: SZ.t) -> (x: t2) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_synth p1 f2) offset v off /\ parse (tot_parse_synth p1 f2) (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))) (fun x -> post x))
  (off: SZ.t)
  (x: t1 { validator_success p1 offset v off /\ parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off) })
  (x2: t2 { x2 == f2 x })
  requires pts_to input #pm v ** pre
  returns x': t'
  ensures post x'
{
  tot_parse_synth_eq p1 f2 (Seq.slice v (SZ.v offset) (Seq.length v));
  cont off x2
}
```

inline_for_extraction
```pulse
fn validate_and_read_synth_cont
  (#k1: parser_kind) (#t1: Type0) (p1: parser k1 t1)
  (#t2: Type0) (f2: (t1 -> Tot t2) { synth_injective f2 })
  (f2': (x: t1) -> stt_cps (f2 x))
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased bytes)
  (offset: SZ.t)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (cont: (off: SZ.t) -> (x: t2) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_synth p1 f2) offset v off /\ parse (tot_parse_synth p1 f2) (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))) (fun x -> post x))
  (off: SZ.t)
  (x: t1)
  requires pts_to input #pm v ** pre ** pure (validator_success p1 offset v off /\ parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))
  returns x': t'
  ensures post x'
{
  f2' x (pts_to input #pm v ** pre) t' post (validate_and_read_synth_cont_cont p1 f2 input pm v offset pre t' post cont off x)
}
```

inline_for_extraction
```pulse
fn validate_and_read_synth
  (#k1: parser_kind) (#t1: Type0) (#p1: parser k1 t1) (w: validate_and_read p1)
  (#t2: Type0) (f2: (t1 -> Tot t2) { synth_injective f2 })
  (f2': (x: t1) -> stt_cps (f2 x))
: validate_and_read #t2 #k1 (tot_parse_synth p1 f2)
= (input: slice byte)
  (offset: _)
  (#pm: _)
  (#v: _)
  (pre: _)
  (t': Type0)
  (post: _)
  (ksucc: _)
  (kfail: _)
{
  tot_parse_synth_eq p1 f2 (Seq.slice v (SZ.v offset) (Seq.length v));
  w input offset #pm #v pre t' post (validate_and_read_synth_cont p1 f2 f2' input pm v offset pre t' post ksucc) kfail
}
```

inline_for_extraction
let validate_and_read_synth'
  (#k1: parser_kind) (#t1: Type0) (#p1: parser k1 t1) (w: validate_and_read p1)
  (#t2: Type0) (f2: (t1 -> Tot t2) { synth_injective f2 })
: Tot (validate_and_read (tot_parse_synth p1 f2))
= validate_and_read_synth w f2 (fun x -> intro_stt_cps (f2 x))

inline_for_extraction
```pulse
fn validate_and_read_filter_cont_failure
  (#t: Type0)
  (#k: parser_kind)
  (p: tot_parser k t)
  (f: (t -> bool))
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_filter p f) offset v)) (fun x -> post x)))
  (_: unit)
  requires (pts_to input #pm v ** pre ** pure (validator_failure (p) offset v))
  returns res: t'
  ensures post res
{
  tot_parse_filter_eq p f (Seq.slice v (SZ.v offset) (Seq.length v));
  kfail ()
}
```

inline_for_extraction
```pulse
fn validate_and_read_filter_cont_success
  (#t: Type0)
  (#k: parser_kind)
  (p: tot_parser k t)
  (f: (t -> bool))
  (f': (x: t) -> (y: bool { y == f x }))
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> (x: parse_filter_refine f) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_filter p f) offset v off /\ parse (tot_parse_filter p f) (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_filter p f) offset v)) (fun x -> post x)))
  (off: SZ.t)
  (x: t)
  requires pts_to input #pm v ** pre ** pure (validator_success p offset v off /\ parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))
  returns res: t'
  ensures post res
{
  tot_parse_filter_eq p f (Seq.slice v (SZ.v offset) (Seq.length v));
  if f' x {
    ksucc off x
  } else {
    kfail ()
  }
}
```

inline_for_extraction
```pulse
fn validate_and_read_filter
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (w: validate_and_read p)
  (f: (t -> bool))
  (f': (x: t) -> (y: bool { y == f x }))
: validate_and_read #_ #(parse_filter_kind k) (tot_parse_filter p f)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> (x: parse_filter_refine f) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_filter p f) offset v off /\ parse (tot_parse_filter p f) (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_filter p f) offset v)) (fun x -> post x)))
{
  w input offset #pm #v pre t' post
    (validate_and_read_filter_cont_success p f f' input offset #pm #v pre t' post ksucc kfail)
    (validate_and_read_filter_cont_failure p f input offset #pm #v pre t' post kfail)
}
```

inline_for_extraction
let validate_and_read_filter'
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (w: validate_and_read p)
  (f: (t -> bool))
: validate_and_read #_ #(parse_filter_kind k) (tot_parse_filter p f)
= validate_and_read_filter w f (fun x -> f x)

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
fn validate_nondep_then_cont_success2
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: parser k2 t2)
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (off: SZ.t {validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) })
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_nondep_then p1 p2) offset v off)) (fun x -> post x)))
  (off': SZ.t)
  requires pts_to input #pm v ** pre ** pure (validator_success p2 (offset `SZ.add` off) v off')
  returns x: t'
  ensures post x
{
  pts_to_len input; // for SZ.fits (off + off')
  nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  ksucc (off `SZ.add` off')
}
```

inline_for_extraction
```pulse
fn validate_nondep_then_cont_failure2
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: parser k2 t2)
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (off: SZ.t {validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) })
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_nondep_then p1 p2) offset v)) (fun x -> post x)))
  (_: unit)
  requires pts_to input #pm v ** pre ** pure (validator_failure p2 (offset `SZ.add` off) v)
  returns x: t'
  ensures post x
{
  nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  kfail ()
}
```

inline_for_extraction
```pulse
fn validate_nondep_then_cont_success1
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (v2: validator p2)
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_nondep_then p1 p2) offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_nondep_then p1 p2) offset v)) (fun x -> post x)))
  (off: SZ.t)
  requires pts_to input #pm v ** pre ** pure (validator_success p1 offset v off)
  returns x: t'
  ensures post x
{
  pts_to_len input; // for SZ.fits (offset + off)  
  v2 input (offset `SZ.add` off) #pm #v pre t' post
    (validate_nondep_then_cont_success2 p1 p2 input offset #pm #v pre t' post off ksucc)
    (validate_nondep_then_cont_failure2 p1 p2 input offset #pm #v pre t' post off kfail)
}
```

inline_for_extraction
```pulse
fn validate_nondep_then_cont_failure1
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: parser k2 t2)
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_nondep_then p1 p2) offset v)) (fun x -> post x)))
  (_: unit)
  requires pts_to input #pm v ** pre ** pure (validator_failure p1 offset v)
  returns x: t'
  ensures post x
{
  nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  kfail ()
}
```

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
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_nondep_then p1 p2) offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_nondep_then p1 p2) offset v)) (fun x -> post x)))
{
  v1 input offset #pm #v pre t' post
    (validate_nondep_then_cont_success1 p1 v2 input offset #pm #v pre t' post ksucc kfail)
    (validate_nondep_then_cont_failure1 p1 p2 input offset #pm #v pre t' post kfail)
}
```

inline_for_extraction
```pulse
fn validate_dtuple2_cont_success2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (key: Ghost.erased t1)
  (off: SZ.t { validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) /\ fst (Some?.v (parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)))) == Ghost.reveal key })
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_dtuple2 p1 p2) offset v off)) (fun x -> post x)))
  (off': SZ.t)
  requires pts_to input #pm v ** pre ** pure (validator_success (p2 key) (offset `SZ.add` off) v off')
  returns x: t'
  ensures post x
{
  pts_to_len input; // for SZ.fits (off + off')
  ksucc (off `SZ.add` off')
}
```

inline_for_extraction
```pulse
fn validate_dtuple2_cont_failure2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (key: Ghost.erased t1)
  (off: SZ.t { validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) /\ fst (Some?.v (parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)))) == Ghost.reveal key })
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_dtuple2 p1 p2) offset v)) (fun x -> post x)))
  (_: unit)
  requires pts_to input #pm v ** pre ** pure (validator_failure (p2 key) (offset `SZ.add` off) v)
  returns x: t'
  ensures post x
{
  kfail ()
}
```

inline_for_extraction
```pulse
fn validate_dtuple2_cont_success1
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (v2: (x: t1) -> validator (p2 x))
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_dtuple2 p1 p2) offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_dtuple2 p1 p2) offset v)) (fun x -> post x)))
  (off: SZ.t)
  (x: t1)
  requires pts_to input #pm v ** pre ** pure (validator_success p1 offset v off /\ parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))
  returns x: t'
  ensures post x
{
  pts_to_len input; // for SZ.fits (offset + off)
  v2 x input (offset `SZ.add` off) #pm #v pre t' post
    (validate_dtuple2_cont_success2 p1 p2 input offset #pm #v pre t' post x off ksucc)
    (validate_dtuple2_cont_failure2 p1 p2 input offset #pm #v pre t' post x off kfail)
}
```

inline_for_extraction
```pulse
fn validate_dtuple2_cont_failure1
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_dtuple2 p1 p2) offset v)) (fun x -> post x)))
  (_: unit)
  requires pts_to input #pm v ** pre ** pure (validator_failure p1 offset v)
  returns x: t'
  ensures post x
{
  kfail ()
}
```

inline_for_extraction
```pulse
fn validate_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (v1: validate_and_read p1)
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (v2: ((x: t1) -> validator (p2 x)))
: validator #(dtuple2 t1 t2) #(and_then_kind k1 k2) (tot_parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_dtuple2 p1 p2) offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_nondep_then p1 p2) offset v)) (fun x -> post x)))
{
  v1 input offset #pm #v pre t' post
    (validate_dtuple2_cont_success1 p1 p2 input offset #pm #v v2 pre t' post ksucc kfail)
    (validate_dtuple2_cont_failure1 p1 p2 input offset #pm #v pre t' post kfail)
}
```

inline_for_extraction
```pulse
fn validate_and_read_dtuple2_cont_success2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (key: t1)
  (off: SZ.t { validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) /\ fst (Some?.v (parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)))) == key })
  (ksucc: ((off: SZ.t) -> (x: dtuple2 t1 t2) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_dtuple2 p1 p2) offset v off /\ parse (tot_parse_dtuple2 p1 p2) (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))) (fun x -> post x)))
  (off': SZ.t)
  (x: t2 key)
  requires pts_to input #pm v ** pre ** pure (validator_success (p2 key) (offset `SZ.add` off) v off' /\ parse (p2 key) (Seq.slice v (SZ.v (offset `SZ.add` off)) (Seq.length v)) == Some (x, SZ.v off'))
  returns x: t'
  ensures post x
{
  pts_to_len input; // for SZ.fits (off + off')
  ksucc (off `SZ.add` off') (| key, x |)
}
```

inline_for_extraction
```pulse
fn validate_and_read_dtuple2_cont_success1
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (v2: (x: t1) -> validate_and_read (p2 x))
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> (x: dtuple2 t1 t2) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_dtuple2 p1 p2) offset v off /\ parse (tot_parse_dtuple2 p1 p2) (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_dtuple2 p1 p2) offset v)) (fun x -> post x)))
  (off: SZ.t)
  (x: t1)
  requires pts_to input #pm v ** pre ** pure (validator_success p1 offset v off /\ parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))
  returns x: t'
  ensures post x
{
  pts_to_len input; // for SZ.fits (offset + off)
  v2 x input (offset `SZ.add` off) #pm #v pre t' post
    (validate_and_read_dtuple2_cont_success2 p1 p2 input offset #pm #v pre t' post x off ksucc)
    (validate_dtuple2_cont_failure2 p1 p2 input offset #pm #v pre t' post x off kfail)
}
```

inline_for_extraction
```pulse
fn validate_and_read_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (v1: validate_and_read p1)
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (v2: ((x: t1) -> validate_and_read (p2 x)))
: validate_and_read #(dtuple2 t1 t2) #(and_then_kind k1 k2) (tot_parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> (x: dtuple2 t1 t2) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_dtuple2 p1 p2) offset v off /\ parse (tot_parse_dtuple2 p1 p2) (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off))) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_nondep_then p1 p2) offset v)) (fun x -> post x)))
{
  v1 input offset #pm #v pre t' post
    (validate_and_read_dtuple2_cont_success1 p1 p2 input offset #pm #v v2 pre t' post ksucc kfail)
    (validate_dtuple2_cont_failure1 p1 p2 input offset #pm #v pre t' post kfail)
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
  let consumed1 = v1 input offset;
  let consumed2 = v2 input (offset `SZ.add` consumed1);
  SZ.add consumed1 consumed2
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
  let off2 = v2 x input (SZ.add offset off1);
  SZ.add off1 off2
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
  ((pts_to_serialized s1 left #pm (dfst v) **
  pts_to_serialized (s2 (dfst v)) right #pm (dsnd v)) @==>
    pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v)

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
  rewrite_with_stick
    (pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v)
    (pts_to input #pm (bare_serialize s1 (dfst v) `Seq.append` bare_serialize (s2 (dfst v)) (dsnd v)));
  parse_serialize_strong_prefix s1 (dfst v) (bare_serialize (s2 (dfst v)) (dsnd v));
  let i = j1 input 0sz;
  let res = slice_append_split_stick false input i;
  match res {
    SlicePair input1 input2 -> {
      unfold (slice_append_split_stick_post input pm (bare_serialize s1 (dfst v)) (bare_serialize (s2 (dfst v)) (dsnd v)) i res);
      unfold (slice_append_split_stick_post' input pm (bare_serialize s1 (dfst v)) (bare_serialize (s2 (dfst v)) (dsnd v)) i input1 input2);
      stick_trans (_ ** _) _ _;
      pts_to_serialized_intro_stick s1 input1 (dfst v);
      pts_to_serialized_intro_stick (s2 (dfst v)) input2 (dsnd v);
      stick_prod (pts_to_serialized s1 input1 #pm _) (pts_to input1 #pm _) (pts_to_serialized (s2 (dfst v)) input2 #pm _) (pts_to input2 #pm _);
      stick_trans (pts_to_serialized s1 input1 #pm _ ** pts_to_serialized (s2 (dfst v)) input2 #pm _) (pts_to input1 #pm _ ** pts_to input2 #pm _) _;
      fold (split_dtuple2_post' s1 s2 input pm v input1 input2);
      fold (split_dtuple2_post s1 s2 input pm v (input1 `SlicePair` input2));
      (input1 `SlicePair` input2)
    }
  }
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
  ((pts_to_serialized s1 left #pm (fst v) **
  pts_to_serialized s2 right #pm (snd v)) @==>
    pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v)

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
  pts_to_serialized_ext_stick
    (tot_serialize_nondep_then s1 s2)
    (tot_serialize_synth
      (tot_parse_dtuple2 p1 (fun _ -> p2))
      pair_of_dtuple2
      (tot_serialize_dtuple2 s1 (fun _ -> s2))
      dtuple2_of_pair
      ()
    )
    input;
  pts_to_serialized_synth_l2r_stick
    (tot_serialize_dtuple2 s1 (fun _ -> s2))
    pair_of_dtuple2
    dtuple2_of_pair
    input;
  stick_trans (pts_to_serialized (tot_serialize_dtuple2 s1 (fun _ -> s2)) _ #pm _) _ _;
  let res = split_dtuple2 s1 j1 (fun _ -> s2) input;
  match res { SlicePair input1 input2 -> {
    unfold (split_dtuple2_post s1 (fun _ -> s2) input pm (dtuple2_of_pair v) res);
    unfold (split_dtuple2_post' s1 (fun _ -> s2) input pm (dtuple2_of_pair v) input1 input2);
    stick_trans (_ ** _) _ _;
    fold (split_nondep_then_post' s1 s2 input pm v input1 input2);
    fold (split_nondep_then_post s1 s2 input pm v (input1 `SlicePair` input2));
    (input1 `SlicePair` input2)
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
    elim_stick _ _;
    f (Mkdtuple2 x1 x2)
  }}
}
```

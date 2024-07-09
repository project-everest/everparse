module LowParse.Pulse.Combinators
include LowParse.Spec.Combinators
include LowParse.Pulse.Base
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Stick
open Pulse.Lib.Slice

module SZ = FStar.SizeT

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
let jump_synth
  (#t #t': Type)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (w: jumper p)
  (f: (t -> t') { synth_injective f })
: Tot (jumper (tot_parse_synth p f))
= Classical.forall_intro (tot_parse_synth_eq' p f);
  w

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
```pulse
fn validate_filter_gen_cont_success
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: serializer p)
  (f: (t -> bool))
  (f': (input: slice byte) -> (pm: perm) -> (v: Ghost.erased t) -> stt bool (pts_to_serialized s input #pm v) (fun res -> pts_to_serialized s input #pm v ** pure (res == f v)))
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_filter p f) offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_filter p f) offset v)) (fun x -> post x)))
  (off: SZ.t)
  requires (pts_to input #pm v ** pre ** pure (validator_success (p) offset v off))
  returns res: t'
  ensures post res
{
  Seq.lemma_split v (SZ.v offset);
  let split123 = split false input offset;
  match split123 { Mktuple2 input1 input23 -> {
    unfold (split_post input pm v offset split123);
    unfold (split_post' input pm v offset input1 input23);
    with v1 v23 . assert (pts_to input1 #pm v1 ** pts_to input23 #pm v23);
    tot_parse_filter_eq p f v23;
    let split23 = peek_stick s input23 off;
    match split23 { Mktuple2 input2 input3 -> {
      unfold (peek_stick_post s input23 pm v23 off split23);
      unfold (peek_stick_post' s input23 pm v23 off input2 input3);
      let cond = f' input2 pm _;
      elim_stick (pts_to_serialized s input2 #pm _ ** _) _;
      join input1 input23 input;
      rewrite (pts_to input #pm (Seq.append v1 v23)) as (pts_to input #pm v);
      if cond {
        ksucc off
      } else {
        kfail ()
      }
    }}
  }}
}
```

inline_for_extraction
```pulse
fn validate_filter_gen_cont_failure
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
fn validate_filter_gen
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: serializer p)
  (w: validator p)
  (f: (t -> bool))
  (f': (input: slice byte) -> (pm: perm) -> (v: Ghost.erased t) -> stt bool (pts_to_serialized s input #pm v) (fun res -> pts_to_serialized s input #pm v ** pure (res == f v)))
: validator #_ #(parse_filter_kind k) (tot_parse_filter p f)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_filter p f) offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_filter p f) offset v)) (fun x -> post x)))
{
  w input offset pre t' post
    (validate_filter_gen_cont_success s f f' input offset #pm #v pre t' post ksucc kfail)
    (validate_filter_gen_cont_failure p f input offset #pm #v pre t' post kfail)
}
```

inline_for_extraction
```pulse
fn validate_filter_read_cond_cont
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: serializer p)
  (f: (t -> bool))
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased t)
  (x: t { x == Ghost.reveal v })
  requires (pts_to_serialized s input #pm v ** emp)
  returns res: bool
  ensures pts_to_serialized s input #pm v ** pure (res == f v)
{
  f x
}
```

inline_for_extraction
```pulse
fn validate_filter_read_cond
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (#s: serializer p)
  (r: reader s)
  (f: (t -> bool))
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased t)
  requires (pts_to_serialized s input #pm v)
  returns res: bool
  ensures pts_to_serialized s input #pm v ** pure (res == f v)
{
  r input #pm #v emp bool (fun res -> pts_to_serialized s input #pm v ** pure (res == f v)) (validate_filter_read_cond_cont s f input pm v)
}
```

inline_for_extraction
let validate_filter
  (#t: Type0)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (#s: serializer p)
  (r: reader s)
  (w: validator p)
  (f: (t -> bool))
: validator #_ #(parse_filter_kind k) (tot_parse_filter p f)
= validate_filter_gen s w f (validate_filter_read_cond r f)

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
  (#v: Ghost.erased t)
  requires (pts_to_serialized s input #pm v ** pure (f v == true))
  ensures exists* (v': parse_filter_refine f) . pts_to_serialized (tot_serialize_filter s f) input #pm v' ** pure ((v' <: t) == Ghost.reveal v)
{
  unfold (pts_to_serialized s input #pm v);
  let sq: squash (f v == true) = ();
  let v' : Ghost.erased (parse_filter_refine f) = Ghost.hide (parse_filter_refine_intro #t f (Ghost.reveal v) sq);
  fold (pts_to_serialized (tot_serialize_filter s f) input #pm v');
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
  (#v: Ghost.erased (parse_filter_refine f))
  requires (pts_to_serialized (tot_serialize_filter s f) input #pm v)
  ensures pts_to_serialized s input #pm v
{
  unfold (pts_to_serialized (tot_serialize_filter s f) input #pm v);
  fold (pts_to_serialized s input #pm v);
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
  (v2: (off: SZ.t { validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) }) -> (key: Ghost.erased t1 { fst (Some?.v (parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)))) == Ghost.reveal key }) ->
  validator_for (p2 key) input (SZ.add offset off) pm v)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (tot_parse_dtuple2 p1 p2) offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (tot_parse_dtuple2 p1 p2) offset v)) (fun x -> post x)))
  (off: SZ.t)
  requires pts_to input #pm v ** pre ** pure (validator_success p1 offset v off)
  returns x: t'
  ensures post x
{
  pts_to_len input; // for SZ.fits (offset + off)
  let key : Ghost.erased t1 = Ghost.hide (fst (Some?.v (parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)))));
  v2 off key pre t' post
    (validate_dtuple2_cont_success2 p1 p2 input offset #pm #v pre t' post key off ksucc)
    (validate_dtuple2_cont_failure2 p1 p2 input offset #pm #v pre t' post key off kfail)
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
fn validate_dtuple2_gen
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (pm: perm)
  (v: Ghost.erased bytes)
  (v2: (off: SZ.t { validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) }) -> (key: Ghost.erased t1 { fst (Some?.v (parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)))) == Ghost.reveal key }) ->
  validator_for (p2 key) input (SZ.add offset off) pm v)
: validator_for #(dtuple2 t1 t2) #(and_then_kind k1 k2) (tot_parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2) input offset pm v
= 
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
let validate_nondep_then
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (v2: validator p2)
: validator #(t1 & t2) #(and_then_kind k1 k2) (tot_nondep_then #k1 #t1 p1 #k2 #t2 p2)
= Classical.forall_intro (nondep_then_eq_dtuple2 p1 p2);
  validate_ext
    (validate_synth
      (fun input offset #pm #v ->
        validate_dtuple2_gen
          v1
          (fun _ -> p2)
          input
          offset
          pm
          v
          (fun off _ -> v2 input (SZ.add offset off) #pm #v)
      )
      pair_of_dtuple2
    )
    (tot_nondep_then #k1 #t1 p1 #k2 #t2 p2)    

inline_for_extraction
```pulse
fn validate_dtuple2_payload_cont
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (v2: ((x: t1) -> validator (p2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (pm: perm)
  (v: Ghost.erased bytes)
  (off: SZ.t { validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) })
  (key: Ghost.erased t1 { fst (Some?.v (parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)))) == Ghost.reveal key })
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off': SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (p2 key) (SZ.add offset off) v off')) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (p2 key) (SZ.add offset off) v)) (fun x -> post x)))
  (input_key: slice byte)
  (x: t1 { x == Ghost.reveal key })
  requires (pts_to_serialized s1 input_key #pm key ** (pre ** (pts_to_serialized s1 input_key #pm key @==> pts_to input #pm v)))
  returns res: t'
  ensures post res
{
  elim_stick (pts_to_serialized s1 input_key #pm key) _;
  v2 x input (SZ.add offset off) pre t' post ksucc kfail
}
```

inline_for_extraction
```pulse
fn validate_dtuple2_payload
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (r1: reader s1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (v2: ((x: t1) -> validator (p2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (pm: perm)
  (v: Ghost.erased bytes)
  (off: SZ.t { validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) })
  (key: Ghost.erased t1 { fst (Some?.v (parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)))) == Ghost.reveal key })
: validator_for #(t2 key) #k2 (p2 key) input (SZ.add offset off) pm v
=
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off': SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success (p2 key) (SZ.add offset off) v off')) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure (p2 key) (SZ.add offset off) v)) (fun x -> post x)))
{
  let input' = peek_stick_gen s1 input offset off;
  assert (pts_to_serialized s1 input' #pm key);
  r1 input' _ t' post (validate_dtuple2_payload_cont s1 p2 v2 input offset pm v off key pre t' post ksucc kfail input')
}
```

inline_for_extraction
let validate_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (#s1: serializer p1)
  (r1: reader s1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (v2: ((x: t1) -> validator (p2 x)))
: Tot (validator (tot_parse_dtuple2 p1 p2))
= fun input offset #pm #v ->
    validate_dtuple2_gen
      v1
      p2
      input
      offset
      pm
      v
      (validate_dtuple2_payload r1 p2 v2 input offset pm v)

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
fn jump_dtuple2_payload_cont
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (p2: ((x: t1) -> parser k2 (t2 x)))
  (v2: ((x: t1) -> jumper (p2 x)))
  (input: slice byte)
  (offset: SZ.t)
  (pm: perm)
  (v: Ghost.erased bytes)
  (off: SZ.t { jumper_pre (tot_parse_dtuple2 p1 p2) offset v /\ validator_success p1 offset v off /\ SZ.fits (SZ.v offset + SZ.v off) })
  (key: Ghost.erased t1 { fst (Some?.v (parse p1 (Seq.slice v (SZ.v offset) (Seq.length v)))) == Ghost.reveal key })
  (input_key: slice byte)
  (x: t1 { x == Ghost.reveal key })
  requires (pts_to_serialized s1 input_key #pm key ** (pts_to_serialized s1 input_key #pm key @==> pts_to input #pm v))
  returns res: SZ.t
  ensures (pts_to input #pm v ** pure (validator_success (tot_parse_dtuple2 p1 p2) offset v res))
{
  elim_stick (pts_to_serialized s1 input_key #pm key) _;
  pts_to_len input;
  let off2 = v2 x input (SZ.add offset off);
  SZ.add off off2
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
  (r1: reader s1)
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
  let input1 = peek_stick_gen s1 input offset off1;
  with key . assert (pts_to_serialized s1 input1 #pm key);
  r1
    input1
    (pts_to_serialized s1 input1 #pm key @==> pts_to input #pm v) 
    SZ.t
    (fun res -> pts_to input #pm v ** pure (validator_success (tot_parse_dtuple2 p1 p2) offset v res))
    (jump_dtuple2_payload_cont s1 p2 v2 input offset pm v off1 key input1)
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
  (res: (slice byte & slice byte))
: Tot vprop
= let (left, right) = res in
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
  returns res: (slice byte & slice byte)
  ensures split_dtuple2_post s1 s2 input pm v res
{
  rewrite_with_stick
    (pts_to_serialized (tot_serialize_dtuple2 s1 s2) input #pm v)
    (pts_to input #pm (bare_serialize s1 (dfst v) `Seq.append` bare_serialize (s2 (dfst v)) (dsnd v)));
  parse_serialize_strong_prefix s1 (dfst v) (bare_serialize (s2 (dfst v)) (dsnd v));
  let i = j1 input 0sz;
  let res = slice_append_split_stick false input i;
  match res {
    Mktuple2 input1 input2 -> {
      unfold (slice_append_split_stick_post input pm (bare_serialize s1 (dfst v)) (bare_serialize (s2 (dfst v)) (dsnd v)) i res);
      unfold (slice_append_split_stick_post' input pm (bare_serialize s1 (dfst v)) (bare_serialize (s2 (dfst v)) (dsnd v)) i input1 input2);
      stick_trans (_ ** _) _ _;
      pts_to_serialized_intro_stick s1 input1 (dfst v);
      pts_to_serialized_intro_stick (s2 (dfst v)) input2 (dsnd v);
      stick_prod (pts_to_serialized s1 input1 #pm _) (pts_to input1 #pm _) (pts_to_serialized (s2 (dfst v)) input2 #pm _) (pts_to input2 #pm _);
      stick_trans (pts_to_serialized s1 input1 #pm _ ** pts_to_serialized (s2 (dfst v)) input2 #pm _) (pts_to input1 #pm _ ** pts_to input2 #pm _) _;
      fold (split_dtuple2_post' s1 s2 input pm v input1 input2);
      fold (split_dtuple2_post s1 s2 input pm v (input1, input2));
      (input1, input2)
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
  (res: (slice byte & slice byte))
: Tot vprop
= let (left, right) = res in
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
  returns res: (slice byte & slice byte)
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
  match res { Mktuple2 input1 input2 -> {
    unfold (split_dtuple2_post s1 (fun _ -> s2) input pm (dtuple2_of_pair v) res);
    unfold (split_dtuple2_post' s1 (fun _ -> s2) input pm (dtuple2_of_pair v) input1 input2);
    stick_trans (_ ** _) _ _;
    fold (split_nondep_then_post' s1 s2 input pm v input1 input2);
    fold (split_nondep_then_post s1 s2 input pm v (input1, input2));
    (input1, input2)
  }}
}
```

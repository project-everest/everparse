module LowParse.Pulse.Base
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

let parser = tot_parser
let serializer #k = tot_serializer #k

let pts_to_serialized (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (input: slice byte) (#[exact (`1.0R)] pm: perm) (v: t) : vprop =
  pts_to input #pm (bare_serialize s v)

```pulse
ghost
fn pts_to_serialized_intro_stick
  (#k: parser_kind) (#t: Type0) (#p: parser k t) (s: serializer p) (input: slice byte) (#pm: perm) (#v0: bytes) (v: t)
  requires (pts_to input #pm v0 ** pure (v0 == bare_serialize s v))
  ensures (pts_to_serialized s input #pm v ** (trade (pts_to_serialized s input #pm v) (pts_to input #pm v0)))
{
  Trade.rewrite_with_trade (pts_to input #pm v0) (pts_to_serialized s input #pm v)
}
```

```pulse
ghost
fn pts_to_serialized_elim_stick
  (#k: parser_kind) (#t: Type0) (#p: parser k t) (s: serializer p) (input: slice byte) (#pm: perm) (#v: t)
  requires (pts_to_serialized s input #pm v)
  ensures (pts_to input #pm (bare_serialize s v) ** (trade (pts_to input #pm (bare_serialize s v)) (pts_to_serialized s input #pm v)))
{
  Trade.rewrite_with_trade (pts_to_serialized s input #pm v) (pts_to input #pm (bare_serialize s v))
}
```

```pulse
ghost
fn pts_to_serialized_length
  (#k: parser_kind) (#t: Type0) (#p: parser k t) (s: serializer p) (input: slice byte) (#pm: perm) (#v: t)
  requires (pts_to_serialized s input #pm v)
  ensures (pts_to_serialized s input #pm v ** pure (Seq.length (bare_serialize s v) == SZ.v (len input)))
{
  unfold (pts_to_serialized s input #pm v);
  pts_to_len input;
  fold (pts_to_serialized s input #pm v)
}
```

let serializer_ext_eq
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2)
  (v: t)
: Lemma
  (requires forall x . parse p1 x == parse p2 x)
  (ensures (bare_serialize s1 v == bare_serialize s2 v))
= let s2' = serialize_ext #k1 p1 s1 #k2 p2 in
  serializer_unique p2 s2 s2' v

```pulse
ghost
fn pts_to_serialized_ext
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_serialized s1 input #pm v ** pure (
    forall x . parse p1 x == parse p2 x
  )
  ensures pts_to_serialized s2 input #pm v
{
  serializer_ext_eq s1 s2 v;
  unfold (pts_to_serialized s1 input #pm v);
  fold (pts_to_serialized s2 input #pm v)
}
```

```pulse
ghost
fn pts_to_serialized_ext_stick
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_serialized s1 input #pm v ** pure (
    forall x . parse p1 x == parse p2 x
  )
  ensures pts_to_serialized s2 input #pm v ** trade (pts_to_serialized s2 input #pm v) (pts_to_serialized s1 input #pm v)
{
  pts_to_serialized_ext s1 s2 input;
  ghost
  fn aux
    (_: unit)
    requires emp ** pts_to_serialized s2 input #pm v
    ensures pts_to_serialized s1 input #pm v
  {
    pts_to_serialized_ext s2 s1 input
  };
  intro_trade _ _ _ aux
}
```

let validator_success (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t) : GTot bool =
    SZ.v offset <= Seq.length v && (
    let pv = parse p (Seq.slice v (SZ.v offset) (Seq.length v)) in
    Some? pv &&
    SZ.v offset + snd (Some?.v pv) = SZ.v off
  )

let validator_failure (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) : GTot bool =
    SZ.v offset <= Seq.length v &&
    None? (parse p (Seq.slice v (SZ.v offset) (Seq.length v)))

let validator_postcond (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t) (res: bool) : GTot bool =
  SZ.v off <= Seq.length v && (
  if res
  then validator_success p offset v off
  else validator_failure p offset v
)

module R = Pulse.Lib.Reference

inline_for_extraction
let validator (#t: Type0) (#k: parser_kind) (p: parser k t) : Tot Type =
  (input: slice byte) ->
  (poffset: R.ref SZ.t) ->
  (#offset: Ghost.erased SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt bool
    (pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v))
    (fun res -> pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (validator_postcond p offset v off res)))

inline_for_extraction
```pulse
fn validate
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (w: validator p)
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: bool
  ensures pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (validator_postcond p offset v off res))
{
  w input poffset #offset #pm #v
}
```

inline_for_extraction
```pulse
fn ifthenelse_validator
  (#t: Type0) (#k: parser_kind) (p: parser k t)
  (cond: bool)
  (wtrue: squash (cond == true) -> validator p)
  (wfalse: squash (cond == false) -> validator p)
: validator #t #k p
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  if cond {
    wtrue () input poffset
  } else {
    wfalse () input poffset
  }
}
```

let validate_nonempty_post
  (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t)
: Tot prop
= SZ.v offset <= Seq.length v /\
  (off == 0sz <==> None? (parse p (Seq.slice v (SZ.v offset) (Seq.length v)))) /\
  (if off = 0sz then validator_failure p offset v else validator_success p offset v off)

inline_for_extraction
```pulse
fn validate_nonempty (#t: Type0) (#k: parser_kind) (#p: parser k t) (w: validator p { k.parser_kind_low > 0 })
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** pure (SZ.v offset <= Seq.length v)
  returns off: SZ.t
  ensures pts_to input #pm v ** pure (validate_nonempty_post p offset v off)
{
  parser_kind_prop_equiv k p;
  let mut poffset = offset;
  let is_valid = validate w input poffset;
  if is_valid {
    !poffset;
  } else {
    0sz
  }
}
```

inline_for_extraction
let validate_ext (#t: Type0) (#k1: parser_kind) (#p1: parser k1 t) (v1: validator p1) (#k2: parser_kind) (p2: parser k2 t { forall x . parse p1 x == parse p2 x }) : validator #_ #k2 p2 =
  v1

inline_for_extraction
let validate_weaken (#t: Type0) (#k1: parser_kind) (k2: parser_kind) (#p1: parser k1 t) (v1: validator p1 { k2 `is_weaker_than` k1 }) : validator (tot_weaken k2 p1) =
  validate_ext v1 (tot_weaken k2 p1)

inline_for_extraction
```pulse
fn validate_total_constant_size (#t: Type0) (#k: parser_kind) (p: parser k t) (sz: SZ.t {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == SZ.v sz /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
})
: validator #_ #k p =
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parser_kind_prop_equiv k p;
  pts_to_len input;
  let offset = !poffset;
  if SZ.lt (SZ.sub (len input) offset) sz
  {
    false
  } else {
    poffset := SZ.add offset sz;
    true
  }
}
```

let jumper_pre
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (offset: SZ.t)
  (v: Ghost.erased bytes)
: GTot bool
= 
  SZ.v offset <= Seq.length v && Some? (parse p (Seq.slice v (SZ.v offset) (Seq.length v)))  

let jumper_pre'
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (offset: SZ.t)
  (v: Ghost.erased bytes)
: Tot prop
= 
  jumper_pre p offset v

inline_for_extraction
let jumper (#t: Type0) (#k: parser_kind) (p: parser k t) : Tot Type =
  (input: slice byte) ->
  (offset: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt SZ.t
    (pts_to input #pm v ** pure (jumper_pre' p offset v))
    (fun res -> pts_to input #pm v ** pure (validator_success p offset v res))

inline_for_extraction
```pulse
fn ifthenelse_jumper (#t: Type0) (#k: parser_kind) (p: parser k t) (cond: bool) (jtrue: squash (cond == true) -> jumper p) (jfalse: squash (cond == false) -> jumper p)
: jumper #t #k p
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  if cond {
    jtrue () input offset
  } else {
    jfalse () input offset
  }
}
```

inline_for_extraction
```pulse
fn jump_ext (#t: Type0) (#k1: parser_kind) (#p1: parser k1 t) (v1: jumper p1) (#k2: parser_kind) (p2: parser k2 t { forall x . parse p1 x == parse p2 x }) : jumper #_ #k2 p2 =
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  v1 input offset #pm #v
}
```

inline_for_extraction
```pulse
fn jump_constant_size (#t: Type0) (#k: parser_kind) (p: parser k t) (sz: SZ.t {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == SZ.v sz
})
: jumper #_ #k p =
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parser_kind_prop_equiv k p;
  pts_to_len input;
  SZ.add offset sz
}
```

let peek_post'
  (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (pm: perm)
  (v: bytes)
  (consumed: SZ.t)
  (left right: slice byte)
: Tot vprop
= exists* v1 v2 . pts_to_serialized s left #pm v1 ** pts_to right #pm v2 ** is_split input pm consumed left right ** pure (
    bare_serialize s v1 `Seq.append` v2 == v /\
    Seq.length (bare_serialize s v1) == SZ.v consumed /\
    parse p v == Some (v1, SZ.v consumed)
  )

let peek_post
  (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (pm: perm)
  (v: bytes)
  (consumed: SZ.t)
  (res: slice_pair byte)
: Tot vprop
= let SlicePair left right = res in
  peek_post' s input pm v consumed left right

inline_for_extraction
```pulse
fn peek
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (consumed: SZ.t)
  requires (pts_to input #pm v ** pure (validator_success #k #t p 0sz v (consumed)))
  returns res: slice_pair byte
  ensures peek_post s input pm v consumed res
{
  let s1s2 = split false input #pm #v consumed;
  match s1s2 {
    SlicePair s1 s2 -> {
      Seq.lemma_split v (SZ.v consumed);
      let v1 = Ghost.hide (fst (Some?.v (parse p v)));
      parse_injective #k p (bare_serialize s v1) v;
      unfold (split_post input pm v consumed (SlicePair s1 s2));
      unfold (split_post' input pm v consumed s1 s2);
      with v1' . assert (pts_to s1 #pm v1');
      rewrite (pts_to s1 #pm v1') as (pts_to_serialized s s1 #pm v1);
      fold (peek_post' s input pm v consumed s1 s2);
      fold (peek_post s input pm v consumed (SlicePair s1 s2));
      (SlicePair s1 s2)
    }
  }
}
```

let peek_stick_post'
  (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (pm: perm)
  (v: bytes)
  (consumed: SZ.t)
  (left right: slice byte)
: Tot vprop
= exists* v1 v2 . pts_to_serialized s left #pm v1 ** pts_to right #pm v2 ** trade (pts_to_serialized s left #pm v1 ** pts_to right #pm v2) (pts_to input #pm v) ** pure (
    bare_serialize s v1 `Seq.append` v2 == v /\
    Seq.length (bare_serialize s v1) == SZ.v consumed /\
    parse p v == Some (v1, SZ.v consumed)
  )

let peek_stick_post
  (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (pm: perm)
  (v: bytes)
  (consumed: SZ.t)
  (res: slice_pair byte)
: Tot vprop
= let (SlicePair left right) = res in
  peek_stick_post' s input pm v consumed left right

```pulse
ghost
fn peek_stick_aux
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (pm: perm)
  (consumed: SZ.t)
  (v: bytes)
  (left right: slice byte)
  (v1: t)
  (v2: bytes)
  (hyp: squash (
    bare_serialize s v1 `Seq.append` v2 == v
  ))
  (_: unit)
  requires (is_split input pm consumed left right ** (pts_to_serialized s left #pm v1 ** pts_to right #pm v2))
  ensures pts_to input #pm v
{
  unfold (pts_to_serialized s left #pm v1);
  join left right input
}
```

inline_for_extraction
```pulse
fn peek_stick
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (consumed: SZ.t)
  requires (pts_to input #pm v ** pure (validator_success #k #t p 0sz v (consumed)))
  returns res: (slice_pair byte)
  ensures peek_stick_post s input pm v consumed res
{
  let res = peek s input consumed;
  match res { SlicePair left right -> {
    unfold (peek_post s input pm v consumed res);
    unfold (peek_post' s input pm v consumed left right);
    with v1 v2 . assert (pts_to_serialized s left #pm v1 ** pts_to right #pm v2);
    intro_trade (pts_to_serialized s left #pm v1 ** pts_to right #pm v2) (pts_to input #pm v) (is_split input pm consumed left right) (peek_stick_aux s input pm consumed v left right v1 v2 ());
    fold (peek_stick_post' s input pm v consumed left right);
    fold (peek_stick_post s input pm v consumed (left `SlicePair` right));
    (left `SlicePair` right)
  }}
}
```

inline_for_extraction
```pulse
fn peek_stick_gen
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (offset: SZ.t)
  (off: SZ.t)
  requires (pts_to input #pm v ** pure (validator_success #k #t p offset v (off)))
  returns input': slice byte
  ensures exists* v' . pts_to_serialized s input' #pm v' ** trade (pts_to_serialized s input' #pm v') (pts_to input #pm v) ** pure (
    validator_success #k #t p offset v off /\
    parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (v', SZ.v off - SZ.v offset)
  )
{
  let split123 = slice_split_stick false input offset;
  match split123 { SlicePair input1 input23 -> {
    unfold (slice_split_stick_post input pm v offset split123);
    unfold (slice_split_stick_post' input pm v offset input1 input23);
    with v23 . assert (pts_to input23 #pm v23);
    Trade.elim_hyp_l (pts_to input1 #pm _) (pts_to input23 #pm v23) (pts_to input #pm v);
    let consumed = SZ.sub off offset;
    let split23 = peek_stick s input23 consumed;
    match split23 { SlicePair input2 input3 -> {
      unfold (peek_stick_post s input23 pm v23 consumed split23);
      unfold (peek_stick_post' s input23 pm v23 consumed input2 input3);
      with v' . assert (pts_to_serialized s input2 #pm v');
      Trade.elim_hyp_r (pts_to_serialized s input2 #pm _) (pts_to input3 #pm _) (pts_to input23 #pm v23);
      Trade.trans (pts_to_serialized s input2 #pm _) (pts_to input23 #pm _) (pts_to input #pm _);
      input2
    }}
  }}
}
```

inline_for_extraction
let leaf_reader
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  stt t (pts_to_serialized s input #pm v) (fun res ->
    pts_to_serialized s input #pm v **
    pure (res == Ghost.reveal v)
  )

inline_for_extraction
let leaf_read
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: leaf_reader s)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
: stt t (pts_to_serialized s input #pm v) (fun res ->
    pts_to_serialized s input #pm v **
    pure (res == Ghost.reveal v)
  )
= r input #pm #v

inline_for_extraction
```pulse
fn read_from_validator_success
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: leaf_reader s)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (offset: SZ.t)
  (off: SZ.t)
  requires (pts_to input #pm v ** pure (validator_success #k #t p offset v (off)))
  returns v' : t
  ensures pts_to input #pm v ** pure (
    validator_success #k #t p offset v off /\
    parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (v', SZ.v off - SZ.v offset)
  )
{
  let input' = peek_stick_gen s input offset off;
  let res = r input';
  Trade.elim _ _;
  res
}
```

inline_for_extraction
let reader
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  (t': Type0) ->
  (f: ((x: t { x == Ghost.reveal v }) -> Tot t')) ->
  stt t' (pts_to_serialized s input #pm v) (fun x' -> pts_to_serialized s input #pm v ** pure (x' == f v))

inline_for_extraction
```pulse
fn leaf_reader_of_reader
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: reader s)
: leaf_reader #t #k #p s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  r input #pm #v t id
}
```

inline_for_extraction
```pulse
fn ifthenelse_reader
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (cond: bool)
  (iftrue: squash (cond == true) -> reader s)
  (iffalse: squash (cond == false) -> reader s)
:reader #t #k #p s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  if cond {
    iftrue () input #pm #v t' f
  } else {
    iffalse () input #pm #v t' f
  }
}
```

inline_for_extraction
```pulse
fn reader_ext
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (r1: reader s1)
  (#k2: parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2 { forall x . parse p1 x == parse p2 x })
:reader #t #k2 #p2 s2
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  pts_to_serialized_ext_stick s2 s1 input;
  let res = r1 input #pm #v t' f;
  elim_trade _ _;
  res
}
```

inline_for_extraction
```pulse
fn reader_of_leaf_reader
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: leaf_reader s)
: reader #t #k #p s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  let x = r input #pm #v;
  f x
}
```

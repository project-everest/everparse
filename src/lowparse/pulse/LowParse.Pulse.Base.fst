module LowParse.Pulse.Base
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT

let parser = tot_parser
let serializer #k = tot_serializer #k

let pts_to_serialized (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (input: slice byte) (#[exact (`1.0R)] pm: perm) (v: t) : vprop =
  pts_to input #pm (bare_serialize s v)

let validator_success (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t) : GTot bool =
    SZ.v offset <= Seq.length v && (
    let pv = parse p (Seq.slice v (SZ.v offset) (Seq.length v)) in
    Some? pv &&
    snd (Some?.v pv) = SZ.v off
  )

let validator_failure (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) : GTot bool =
    SZ.v offset <= Seq.length v &&
    None? (parse p (Seq.slice v (SZ.v offset) (Seq.length v)))

inline_for_extraction
let validator_for (#t: Type0) (#k: parser_kind) (p: parser k t)
  (input: slice byte)
  (offset: SZ.t)
  (pm: perm)
  (v: Ghost.erased bytes)
: Tot Type
=
  (pre: vprop) ->
  (t': Type0) ->
  (post: (t' -> vprop)) ->
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success p offset v off)) (fun x -> post x))) ->
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure p offset v)) (fun x -> post x))) ->
  stt t'
    (pts_to input #pm v ** pre ** pure (SZ.v offset <= Seq.length v))
    (fun x -> post x)

inline_for_extraction
let validator (#t: Type0) (#k: parser_kind) (p: parser k t) : Tot Type =
  (input: slice byte) ->
  (offset: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  validator_for p input offset pm v

inline_for_extraction
let validate
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (w: validator p)
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success p offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure p offset v)) (fun x -> post x)))
: stt t'
    (pts_to input #pm v ** pre ** pure (SZ.v offset <= Seq.length v))
    (fun x -> post x)
= w input offset #pm #v pre t' post ksucc kfail

let validate_nonempty_post
  (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t)
: Tot prop
= SZ.v offset <= Seq.length v /\
  (off == 0sz <==> None? (parse p (Seq.slice v (SZ.v offset) (Seq.length v)))) /\
  (if off = 0sz then validator_failure p offset v else validator_success p offset v off)

inline_for_extraction
```pulse
fn validate_nonempty_success (#t: Type0) (#k: parser_kind) (p: parser k t { k.parser_kind_low > 0 })
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (sq: squash (SZ.v offset <= Seq.length v))
  (off: SZ.t)
  requires pts_to input #pm v ** emp ** pure (validator_success p offset v off)
  returns off: SZ.t
  ensures pts_to input #pm v ** pure (validate_nonempty_post p offset v off)
{
  parser_kind_prop_equiv k p;
  off
}
```

inline_for_extraction
```pulse
fn validate_nonempty_failure (#t: Type0) (#k: parser_kind) (p: parser k t { k.parser_kind_low > 0 })
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (sq: squash (SZ.v offset <= Seq.length v))
  (_: unit)
  requires pts_to input #pm v ** emp ** pure (validator_failure p offset v)
  returns off: SZ.t
  ensures pts_to input #pm v ** pure (validate_nonempty_post p offset v off)
{
  parser_kind_prop_equiv k p;
  0sz
}
```

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
  validate w input offset #pm #v emp SZ.t (fun off -> pts_to input #pm v ** pure (validate_nonempty_post p offset v off))
    (validate_nonempty_success p input offset #pm #v ())
    (validate_nonempty_failure p input offset #pm #v ())
}
```

inline_for_extraction
let validate_ext (#t: Type0) (#k1: parser_kind) (#p1: parser k1 t) (v1: validator p1) (#k2: parser_kind) (p2: parser k2 t { forall x . parse p1 x == parse p2 x }) : validator #_ #k2 p2 =
  v1

inline_for_extraction
```pulse
fn validate_total_constant_size (#t: Type0) (#k: parser_kind) (p: parser k t) (sz: SZ.t {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == SZ.v sz /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
})
: validator #_ #k p =
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success p offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure p offset v)) (fun x -> post x)))
{
  parser_kind_prop_equiv k p;
  pts_to_len input;
  if SZ.lt (SZ.sub (len input) offset) sz
  {
    kfail ()
  } else {
    ksucc (sz <: SZ.t)
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
let jump_ext (#t: Type0) (#k1: parser_kind) (#p1: parser k1 t) (v1: jumper p1) (#k2: parser_kind) (p2: parser k2 t { forall x . parse p1 x == parse p2 x }) : jumper #_ #k2 p2 =
  v1

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
  (sz <: SZ.t)
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
  (res: (slice byte & slice byte))
: Tot vprop
= let (left, right) = res in
  peek_post' s input pm v consumed left right

```pulse
fn peek
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (consumed: SZ.t)
  requires (pts_to input #pm v ** pure (validator_success #k #t p 0sz v (consumed)))
  returns res: (slice byte & slice byte)
  ensures peek_post s input pm v consumed res
{
  let s1s2 = split false input #pm #v consumed;
  match s1s2 {
    Mktuple2 s1 s2 -> {
      Seq.lemma_split v (SZ.v consumed);
      let v1 = Ghost.hide (fst (Some?.v (parse p v)));
      parse_injective #k p (bare_serialize s v1) v;
      unfold (split_post input pm v consumed (s1, s2));
      unfold (split_post' input pm v consumed s1 s2);
      with v1' . assert (pts_to s1 #pm v1');
      rewrite (pts_to s1 #pm v1') as (pts_to_serialized s s1 #pm v1);
      fold (peek_post' s input pm v consumed s1 s2);
      fold (peek_post s input pm v consumed (s1, s2));
      (s1, s2)
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
= exists* v1 v2 . pts_to_serialized s left #pm v1 ** pts_to right #pm v2 ** ((pts_to_serialized s left #pm v1 ** pts_to right #pm v2) @==> pts_to input #pm v) ** pure (
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
  (res: (slice byte & slice byte))
: Tot vprop
= let (left, right) = res in
  peek_stick_post' s input pm v consumed left right

```pulse
fn peek_stick
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (consumed: SZ.t)
  requires (pts_to input #pm v ** pure (validator_success #k #t p 0sz v (consumed)))
  returns res: (slice byte & slice byte)
  ensures peek_stick_post s input pm v consumed res
{
  let res = peek s input consumed;
  match res { Mktuple2 left right -> {
    unfold (peek_post s input pm v consumed res);
    unfold (peek_post' s input pm v consumed left right);
    with v1 v2 . assert (pts_to_serialized s left #pm v1 ** pts_to right #pm v2);
    ghost
    fn aux
      (_foo: unit)
      requires (is_split input pm consumed left right ** (pts_to_serialized s left #pm v1 ** pts_to right #pm v2))
      ensures pts_to input #pm v
      {
        unfold (pts_to_serialized s left #pm v1);
        join left right input
      };
    intro_stick (pts_to_serialized s left #pm v1 ** pts_to right #pm v2) (pts_to input #pm v) (is_split input pm consumed left right) aux;
    fold (peek_stick_post' s input pm v consumed left right);
    fold (peek_stick_post s input pm v consumed (left, right));
    (left, right)
  }}
}
```

```pulse
fn peek_stick_gen
  (#t: Type0) (#k: parser_kind) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (offset: SZ.t)
  (consumed: SZ.t)
  requires (pts_to input #pm v ** pure (validator_success #k #t p offset v (consumed)))
  returns input': slice byte
  ensures exists* v' . pts_to_serialized s input' #pm v' ** (pts_to_serialized s input' #pm v' @==> pts_to input #pm v) ** pure (
    validator_success #k #t p offset v consumed /\
    parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (v', SZ.v consumed)
  )
{
  let split123 = slice_split_stick false input offset;
  match split123 { Mktuple2 input1 input23 -> {
    unfold (slice_split_stick_post input pm v offset split123);
    unfold (slice_split_stick_post' input pm v offset input1 input23);
    with v23 . assert (pts_to input23 #pm v23);
    stick_elim_partial_l (pts_to input1 #pm _) (pts_to input23 #pm v23) (pts_to input #pm v);
    let split23 = peek_stick s input23 consumed;
    match split23 { Mktuple2 input2 input3 -> {
      unfold (peek_stick_post s input23 pm v23 consumed split23);
      unfold (peek_stick_post' s input23 pm v23 consumed input2 input3);
      with v' . assert (pts_to_serialized s input2 #pm v');
      stick_elim_partial_r (pts_to_serialized s input2 #pm _) (pts_to input3 #pm _) (pts_to input23 #pm v23);
      stick_trans (pts_to_serialized s input2 #pm _) (pts_to input23 #pm _) (pts_to input #pm _);
      input2
    }}
  }}
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
  (pre: vprop) ->
  (t': Type0) ->
  (post: (t' -> vprop)) ->
  (cont: (x: t { x == Ghost.reveal v }) -> stt t' (pts_to_serialized s input #pm v ** pre) (fun x -> post x)) ->
  stt t' (pts_to_serialized s input #pm v ** pre) (fun x -> post x)

inline_for_extraction
let call_reader
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: reader s)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (cont: (x: t { x == Ghost.reveal v }) -> stt t' (pts_to_serialized s input #pm v ** pre) (fun t' -> post t'))
: stt t' (pts_to_serialized s input #pm v ** pre) (fun t' -> post t')
= r input pre t' (fun x -> post x) (fun x -> cont x)

#push-options "--print_implicits --query_stats"

inline_for_extraction
```pulse
fn read_cont
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: reader s)
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased t)
  (v': t { Ghost.reveal v == v' })
  requires (pts_to_serialized s input #pm v ** emp)
  returns v' : t
  ensures (pts_to_serialized s input #pm v' ** pure (Ghost.reveal v == v'))
{
  v'
}
```

inline_for_extraction
```pulse
fn read
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: reader s)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  requires (pts_to_serialized s input #pm v)
  returns v' : t
  ensures (pts_to_serialized s input #pm v' ** pure (Ghost.reveal v == v'))
{
  call_reader r input #pm #v emp t (fun v' -> pts_to_serialized s input #pm v' ** pure (Ghost.reveal v == v')) (read_cont r input pm v)
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
fn reader_of_leaf_reader'
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: leaf_reader s)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (cont: (x: t { x == Ghost.reveal v }) -> stt t' (pts_to_serialized s input #pm v ** pre) (fun x -> post x))
  requires (pts_to_serialized s input #pm v ** pre)
  returns res: t'
  ensures post res
{
  let res = leaf_read r input #pm #v;
  cont res
}
```

inline_for_extraction
let reader_of_leaf_reader
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: leaf_reader s)
: reader s
= reader_of_leaf_reader' r

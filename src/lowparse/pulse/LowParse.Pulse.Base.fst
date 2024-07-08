module LowParse.Pulse.Base
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT

let parser = tot_parser
let serializer #k = tot_serializer #k

let pts_to_serialized (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (input: slice byte) (#[exact (`1.0R)] pm: perm) (v: t) : vprop =
  pts_to input #pm (bare_serialize s v)

let validator_success (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t) : Tot prop =
    SZ.v offset <= Seq.length v /\ (
    let pv = parse p (Seq.slice v (SZ.v offset) (Seq.length v)) in
    Some? pv /\
    snd (Some?.v pv) == SZ.v off
  )

let validator_failure (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) : Tot prop =
    SZ.v offset <= Seq.length v /\
    parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == None

inline_for_extraction
let validator (#t: Type0) (#k: parser_kind) (p: parser k t) : Tot Type =
  (input: slice byte) ->
  (offset: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  (pre: vprop) ->
  (t': Type0) ->
  (post: (t' -> vprop)) ->
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success p offset v off)) (fun x -> post x))) ->
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure p offset v)) (fun x -> post x))) ->
  stt t'
    (pts_to input #pm v ** pre ** pure (SZ.v offset <= Seq.length v))
    (fun x -> post x)

inline_for_extraction
```pulse
fn validate_ext (#t: Type0) (#k1: parser_kind) (#p1: parser k1 t) (v1: validator p1) (#k2: parser_kind) (p2: parser k2 t { forall x . parse p1 x == parse p2 x }) : validator #_ #k2 p2 =
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (ksucc: ((off: SZ.t) -> stt t' (pts_to input #pm v ** pre ** pure (validator_success p2 offset v off)) (fun x -> post x)))
  (kfail: (unit -> stt t' (pts_to input #pm v ** pre ** pure (validator_failure p2 offset v)) (fun x -> post x)))
{
  v1 input offset pre t' post ksucc kfail;
}
```

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

inline_for_extraction
let jumper (#t: Type0) (#k: parser_kind) (p: parser k t) : Tot Type =
  (input: slice byte) ->
  (offset: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt SZ.t
    (pts_to input #pm v ** pure (SZ.v offset <= Seq.length v /\ Some? (parse p (Seq.slice v (SZ.v offset) (Seq.length v)))))
    (fun res -> pts_to input #pm v ** pure (validator_success p offset v res))

inline_for_extraction
```pulse
fn jump_ext (#t: Type0) (#k1: parser_kind) (#p1: parser k1 t) (v1: jumper p1) (#k2: parser_kind) (p2: parser k2 t { forall x . parse p1 x == parse p2 x }) : jumper #_ #k2 p2 =
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  v1 input offset;
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
    Seq.length (bare_serialize s v1) == SZ.v consumed
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

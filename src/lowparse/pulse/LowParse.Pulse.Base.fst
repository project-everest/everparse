module LowParse.Pulse.Base
#lang-pulse
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice

let pts_to_serialized
  (#k: parser_kind) (#t: Type) (#p: parser k t)
  (s: serializer p)
  ([@@@mkey]input: slice byte)
  (#[exact (`1.0R)] pm: perm)
  (v: t)
: slprop =
  S.pts_to input #pm (bare_serialize s v)

ghost
fn pts_to_serialized_intro_trade
  (#k: parser_kind) (#t: Type0) (#p: parser k t) (s: serializer p) (input: slice byte) (#pm: perm) (#v0: bytes) (v: t)
  requires (pts_to input #pm v0 ** pure (v0 == bare_serialize s v))
  ensures (pts_to_serialized s input #pm v ** (trade (pts_to_serialized s input #pm v) (pts_to input #pm v0)))
{
  Trade.rewrite_with_trade (pts_to input #pm v0) (pts_to_serialized s input #pm v)
}

ghost
fn pts_to_serialized_elim_trade
  (#k: parser_kind) (#t: Type0) (#p: parser k t) (s: serializer p) (input: slice byte) (#pm: perm) (#v: t)
  requires (pts_to_serialized s input #pm v)
  ensures (pts_to input #pm (bare_serialize s v) ** (trade (pts_to input #pm (bare_serialize s v)) (pts_to_serialized s input #pm v)))
{
  Trade.rewrite_with_trade (pts_to_serialized s input #pm v) (pts_to input #pm (bare_serialize s v))
}

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

let pts_to_serialized_ext_trade_gen_precond
  (#t1 #t2: Type)
  (#k1 #k2: parser_kind)
  (p1: parser k1 t1)
  (p2: parser k2 t2)
: Tot prop
=
  t1 == t2 /\
  (forall x . parse p1 x == parse p2 x)

ghost
fn pts_to_serialized_ext_trade_gen
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: t1)
  requires pts_to_serialized s1 input #pm v ** pure (
    pts_to_serialized_ext_trade_gen_precond p1 p2
  )
  ensures exists* v2 .
    pts_to_serialized s2 input #pm v2 ** trade (pts_to_serialized s2 input #pm v2) (pts_to_serialized s1 input #pm v) **
    pure (t1 == t2 /\
      v == v2
    )
{
  pts_to_serialized_ext s1 s2 input;
  intro
    (Trade.trade (pts_to_serialized s2 input #pm v) (pts_to_serialized s1 input #pm v))
    #emp
    fn _{
      pts_to_serialized_ext s2 s1 input
    };
}

ghost
fn pts_to_serialized_ext_trade
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
  intro
    (Trade.trade (pts_to_serialized s2 input #pm v) (pts_to_serialized s1 input #pm v))
    #emp
    fn _{
    pts_to_serialized_ext s2 s1 input
  };
}

ghost
fn pts_to_serialized_share
  (#k: parser_kind) (#t: Type0) (#p: parser k t) (s: serializer p) (input: slice byte) (#pm: perm) (#v: t)
  requires (pts_to_serialized s input #pm v)
  ensures (pts_to_serialized s input #(pm /. 2.0R) v ** pts_to_serialized s input #(pm /. 2.0R) v)
{
  unfold (pts_to_serialized s input #pm v);
  S.share input;
  fold (pts_to_serialized s input #(pm /. 2.0R) v);
  fold (pts_to_serialized s input #(pm /. 2.0R) v)
}

[@@allow_ambiguous]
ghost
fn pts_to_serialized_gather
  (#k: parser_kind) (#t: Type0) (#p: parser k t) (s: serializer p) (input: slice byte) (#pm0 #pm1: perm) (#v0 #v1: t)
  requires (pts_to_serialized s input #pm0 v0 ** pts_to_serialized s input #pm1 v1)
  ensures (pts_to_serialized s input #(pm0 +. pm1) v0 ** pure (v0 == v1))
{
  unfold (pts_to_serialized s input #pm0 v0);
  unfold (pts_to_serialized s input #pm1 v1);
  S.gather input;
  serializer_injective _ s v0 v1;
  fold (pts_to_serialized s input #(pm0 +. pm1) v0)
}

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
fn validate
  (#t: Type0) (#k: Ghost.erased parser_kind) (#p: parser k t) (w: validator p)
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

inline_for_extraction
fn ifthenelse_validator
  (#t: Type0) (#k: Ghost.erased parser_kind) (p: parser k t)
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

let validate_nonempty_post
  (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t)
: Tot prop
= SZ.v offset <= Seq.length v /\
  (off == 0sz <==> None? (parse p (Seq.slice v (SZ.v offset) (Seq.length v)))) /\
  (if off = 0sz then validator_failure p offset v else validator_success p offset v off)

inline_for_extraction
fn validate_nonempty (#t: Type0) (#k: Ghost.erased parser_kind) (#p: parser k t) (w: validator p { k.parser_kind_low > 0 })
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

inline_for_extraction
let validate_ext (#t: Type0) (#k1: Ghost.erased parser_kind) (#p1: parser k1 t) (v1: validator p1) (#k2: Ghost.erased parser_kind) (p2: parser k2 t { forall x . parse p1 x == parse p2 x }) : validator #_ #k2 p2 =
  v1

inline_for_extraction
let validate_weaken (#t: Type0) (#k1: Ghost.erased parser_kind) (k2: Ghost.erased parser_kind) (#p1: parser k1 t) (v1: validator p1 { k2 `is_weaker_than` k1 }) : validator (weaken k2 p1) =
  validate_ext v1 (weaken k2 p1)

inline_for_extraction
fn validate_total_constant_size (#t: Type0) (#k: Ghost.erased parser_kind) (p: parser k t) (sz: SZ.t {
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
fn ifthenelse_jumper (#t: Type0) (#k: Ghost.erased parser_kind) (p: parser k t) (cond: bool) (jtrue: squash (cond == true) -> jumper p) (jfalse: squash (cond == false) -> jumper p)
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

inline_for_extraction
fn jump_ext (#t: Type0) (#k1: Ghost.erased parser_kind) (#p1: parser k1 t) (v1: jumper p1) (#k2: Ghost.erased parser_kind) (p2: parser k2 t { forall x . parse p1 x == parse p2 x }) : jumper #_ #k2 p2 =
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  v1 input offset #pm #v
}

inline_for_extraction
fn jump_constant_size (#t: Type0) (#k: Ghost.erased parser_kind) (p: parser k t) (sz: SZ.t {
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

let peek_post'
  (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (pm: perm)
  (v: bytes)
  (consumed: SZ.t)
  (left right: slice byte)
: Tot slprop
= exists* v1 v2 . pts_to_serialized s left #pm v1 ** pts_to right #pm v2 ** is_split input left right ** pure (
    bare_serialize s v1 `Seq.append` v2 == v /\
    Seq.length (bare_serialize s v1) == SZ.v consumed /\
    begin match parse p v with
    | Some (v2, consumed2) -> v1 == v2 /\ SZ.v consumed == consumed2
    | _ -> False
    end
  )

let peek_post
  (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (pm: perm)
  (v: bytes)
  (consumed: SZ.t)
  (res: (slice byte & slice byte))
: Tot slprop
= let (left, right) = res in
  peek_post' s input pm v consumed left right

inline_for_extraction
fn peek
  (#t: Type0) (#k: Ghost.erased parser_kind) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (consumed: SZ.t)
  requires (pts_to input #pm v ** pure (validator_success #k #t p 0sz v (consumed)))
  returns res: (slice byte & slice byte)
  ensures peek_post s input pm v consumed res
{
  let s1, s2 = split input consumed;
  Seq.lemma_split v (SZ.v consumed);
  let v1 = Ghost.hide (fst (Some?.v (parse p v)));
  parse_injective #k p (bare_serialize s v1) v;
  with v1' . assert (pts_to s1 #pm v1');
  rewrite (pts_to s1 #pm v1') as (pts_to_serialized s s1 #pm v1);
  fold (peek_post' s input pm v consumed s1 s2);
  fold (peek_post s input pm v consumed (s1, s2));
  (s1, s2)
}

let peek_trade_post'
  (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (pm: perm)
  (v: bytes)
  (consumed: SZ.t)
  (left right: slice byte)
: Tot slprop
= exists* v1 v2 . pts_to_serialized s left #pm v1 ** pts_to right #pm v2 ** trade (pts_to_serialized s left #pm v1 ** pts_to right #pm v2) (pts_to input #pm v) ** pure (
    bare_serialize s v1 `Seq.append` v2 == v /\
    Seq.length (bare_serialize s v1) == SZ.v consumed /\
    begin match parse p v with
    | Some (v2, consumed2) -> v1 == v2 /\ SZ.v consumed == consumed2
    | _ -> False
    end
  )

let peek_trade_post
  (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (pm: perm)
  (v: bytes)
  (consumed: SZ.t)
  (res: (slice byte & slice byte))
: Tot slprop
= let (left, right) = res in
  peek_trade_post' s input pm v consumed left right

ghost
fn peek_trade_aux
  (#t: Type0) (#k: Ghost.erased parser_kind) (#p: parser k t) (s: serializer p)
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
  requires (is_split input left right ** (pts_to_serialized s left #pm v1 ** pts_to right #pm v2))
  ensures pts_to input #pm v
{
  unfold (pts_to_serialized s left #pm v1);
  join left right input
}

inline_for_extraction
fn peek_trade
  (#t: Type0) (#k: Ghost.erased parser_kind) (#p: parser k t) (s: serializer p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (consumed: SZ.t)
  requires (pts_to input #pm v ** pure (validator_success #k #t p 0sz v (consumed)))
  returns res: (slice byte & slice byte)
  ensures peek_trade_post s input pm v consumed res
{
  let left, right = peek s input consumed;
  unfold (peek_post s input pm v consumed (left, right));
  unfold (peek_post' s input pm v consumed left right);
  with v1 v2 . assert (pts_to_serialized s left #pm v1 ** pts_to right #pm v2);
  intro_trade (pts_to_serialized s left #pm v1 ** pts_to right #pm v2) (pts_to input #pm v) (is_split input left right) (peek_trade_aux s input pm consumed v left right v1 v2 ());
  fold (peek_trade_post' s input pm v consumed left right);
  fold (peek_trade_post s input pm v consumed (left, right));
  (left, right)
}

inline_for_extraction
fn peek_trade_gen
  (#t: Type0) (#k: Ghost.erased parser_kind) (#p: parser k t) (s: serializer p)
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
  let input1, input23 = split_trade input offset;
  with v23 . assert (pts_to input23 #pm v23);
  Trade.elim_hyp_l (pts_to input1 #pm _) (pts_to input23 #pm v23) _;
  let consumed = SZ.sub off offset;
  let input2, input3 = peek_trade s input23 consumed;
  unfold (peek_trade_post s input23 pm v23 consumed (input2, input3));
  unfold (peek_trade_post' s input23 pm v23 consumed input2 input3);
  with v' . assert (pts_to_serialized s input2 #pm v');
  Trade.elim_hyp_r (pts_to_serialized s input2 #pm _) (pts_to input3 #pm _) (pts_to input23 #pm v23);
  Trade.trans (pts_to_serialized s input2 #pm _) (pts_to input23 #pm _) (pts_to input #pm _);
  input2
}

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
  (#k: Ghost.erased parser_kind)
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
fn read_from_validator_success
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
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
  let input' = peek_trade_gen s input offset off;
  let res = r input';
  Trade.elim _ _;
  res
}

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
fn leaf_reader_of_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
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

inline_for_extraction
fn ifthenelse_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
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

inline_for_extraction
fn reader_ext
  (#t: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (r1: reader s1)
  (#k2: Ghost.erased parser_kind)
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
  pts_to_serialized_ext_trade s2 s1 input;
  let res = r1 input #pm #v t' f;
  elim_trade _ _;
  res
}

inline_for_extraction
fn reader_of_leaf_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
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

let l2r_writer_for_pre
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (x: Ghost.erased t)
  (offset: SZ.t)
  (v: Ghost.erased bytes)
: Tot prop
= SZ.v offset + Seq.length (bare_serialize s x) <= Seq.length v

let l2r_writer_for_post
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (x: Ghost.erased t)
  (offset: SZ.t)
  (v: Ghost.erased bytes)
  (res: SZ.t)
  (v' : Seq.seq byte)
: Tot prop
=
      let bs = bare_serialize s x in
      SZ.v res == SZ.v offset + Seq.length bs /\
      SZ.v res <= Seq.length v /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
      Seq.slice v' (SZ.v offset) (SZ.v res) `Seq.equal` bs

inline_for_extraction
let l2r_writer_for
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (x': t')
  (x: Ghost.erased t)
=
  (out: slice byte) ->
  (offset: SZ.t) ->
  (#v: Ghost.erased bytes) ->
  stt SZ.t
    (pts_to out v ** vmatch x' x ** pure (
      l2r_writer_for_pre s x offset v
    ))
    (fun res -> exists* v' .
      pts_to out v' ** vmatch x' x ** pure (
      l2r_writer_for_post s x offset v res v'
    ))

inline_for_extraction
let l2r_writer
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
= (x': t') ->
  (#x: Ghost.erased t) ->
  l2r_writer_for vmatch s x' x

inline_for_extraction
fn l2r_writer_ext
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (w: l2r_writer vmatch s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2 { forall b . parse p1 b == parse p2 b })
: l2r_writer #t' #t vmatch #k2 #p2 s2
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  serializer_unique_strong s1 s2 x;
  w x' out offset
}

let vmatch_ext
  (#t' #t1 t2: Type)
  (vmatch: t' -> t1 -> slprop)
  (x': t')
  (x2: t2)
: Tot slprop
= exists* (x1: t1) . vmatch x' x1 ** pure (t1 == t2 /\ x1 == x2)

ghost
fn vmatch_ext_elim_trade
  (#t' #t1 t2: Type0)
  (vmatch: t' -> t1 -> slprop)
  (x': t')
  (x2: t2)
requires
  vmatch_ext t2 vmatch x' x2
returns x1: Ghost.erased t1
ensures
  vmatch x' x1 **
  Trade.trade (vmatch x' x1) (vmatch_ext t2 vmatch x' x2) **
  pure (t1 == t2 /\ x1 == x2)
{
  unfold (vmatch_ext t2 vmatch x' x2);
  with x1 . assert (vmatch x' x1);
  intro (Trade.trade (vmatch x' x1) (vmatch_ext t2 vmatch x' x2)) #emp fn _{
    fold (vmatch_ext t2 vmatch x' x2);
  };
  x1
}

inline_for_extraction
fn l2r_writer_ext_gen
  (#t' #t1 #t2: Type0)
  (#vmatch: t' -> t2 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (w: l2r_writer (vmatch_ext t1 vmatch) s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2 { t1 == t2 /\ (forall b . parse p1 b == parse p2 b) })
: l2r_writer #t' #t2 vmatch #k2 #p2 s2
= (x': t')
  (#x: Ghost.erased t2)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  let x1 : Ghost.erased t1 = Ghost.hide #t1 (Ghost.reveal #t2 x);
  serializer_unique_strong s1 s2 x1;
  fold (vmatch_ext t1 vmatch x' x1);
  let res = w x' out offset;
  unfold (vmatch_ext t1 vmatch x' x1);
  with x2 . assert (vmatch x' x2);
  rewrite (vmatch x' x2) as (vmatch x' x);
  res
}

inline_for_extraction
fn l2r_writer_ifthenelse
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (cond: bool)
  (iftrue: (squash (cond == true) -> l2r_writer vmatch s))
  (iffalse: (squash (cond == false) -> l2r_writer vmatch s))
: l2r_writer #t' #t vmatch #k #p s
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  if (cond) {
    iftrue () x' out offset
  } else {
    iffalse () x' out offset
  }
}

inline_for_extraction
fn l2r_writer_zero_size
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_high == Some 0))
: l2r_writer #t' #t vmatch #k #p s
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  serialize_length s x;
  offset
}

let vmatch_with_cond
  (#tl #th: Type)
  (vmatch: tl -> th -> slprop)
  (cond: tl -> GTot bool)
  (xl: tl)
  (xh: th)
: Tot slprop
= vmatch xl xh ** pure (cond xl)

ghost
fn vmatch_with_cond_elim_trade
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (cond: tl -> GTot bool)
  (xl: tl)
  (xh: th)
requires
  vmatch_with_cond vmatch cond xl xh
ensures
  vmatch xl xh **
  Trade.trade (vmatch xl xh) (vmatch_with_cond vmatch cond xl xh) **
  pure (cond xl)
{
  unfold (vmatch_with_cond vmatch cond xl xh);
  intro (Trade.trade (vmatch xl xh) (vmatch_with_cond vmatch cond xl xh)) #emp fn _{
    fold (vmatch_with_cond vmatch cond xl xh)
  };
}

let pnot (#t: Type) (cond: t -> GTot bool) (x: t) : GTot bool = not (cond x)

inline_for_extraction
fn l2r_writer_ifthenelse_low
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (cond: (t' -> bool))
  (iftrue: l2r_writer (vmatch_with_cond vmatch cond) s)
  (iffalse: l2r_writer (vmatch_with_cond vmatch (pnot cond)) s)
: l2r_writer #t' #t vmatch #k #p s
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  if (cond x') {
    fold (vmatch_with_cond vmatch cond x' x);
    let res = iftrue x' out offset;
    unfold (vmatch_with_cond vmatch cond x' x);
    res
  } else {
    fold (vmatch_with_cond vmatch (pnot cond) x' x);
    let res = iffalse x' out offset;
    unfold (vmatch_with_cond vmatch (pnot cond) x' x);
    res
  }
}

let vmatch_and_const
  (#tl #th: Type)
  (const: slprop)
  (vmatch: tl -> th -> slprop)
  (xl: tl)
  (xh: th)
: Tot slprop
= const ** vmatch xl xh

inline_for_extraction
fn l2r_writer_frame
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (const: slprop)
  (w: l2r_writer vmatch s1)
: l2r_writer #t' #t (vmatch_and_const const vmatch) #k1 #p1 s1
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  unfold (vmatch_and_const const vmatch);
  let res = w x' out offset;
  fold (vmatch_and_const const vmatch);
  res
}

inline_for_extraction
let vmatch_lens
  (#t1' #t2'  #t: Type0)
  (vmatch1: t1' -> t -> slprop)
  (vmatch2: t2' -> t -> slprop)
: Type
= (x1': t1') -> (x: Ghost.erased t) -> stt t2'
    (vmatch1 x1' x)
    (fun x2' -> vmatch2 x2' x ** trade (vmatch2 x2' x) (vmatch1 x1' x))

inline_for_extraction
fn vmatch_lens_compose
  (#t1' #t2' #t3' #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#vmatch2: t2' -> t -> slprop)
  (#vmatch3: t3' -> t -> slprop)
  (l12: vmatch_lens vmatch1 vmatch2)
  (l23: vmatch_lens vmatch2 vmatch3)
: vmatch_lens #t1' #t3' #t vmatch1 vmatch3
= (x1': t1')
  (x: Ghost.erased t)
{
  let x2' = l12 x1' x;
  let x3' = l23 x2' x;
  Trade.trans _ _ (vmatch1 x1' x);
  x3'
}

inline_for_extraction
fn l2r_writer_lens
  (#t1' #t2' #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#vmatch2: t2' -> t -> slprop)
  (lens: vmatch_lens vmatch1 vmatch2)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: l2r_writer vmatch2 s)
: l2r_writer #t1' #t vmatch1 #k #p s
= (x1': t1')
  (#x: Ghost.erased t)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  let x2' = lens x1' _;
  let res = w x2' out offset;
  elim_trade _ _;
  res
}

let eq_as_slprop (t: Type) (x x': t) : slprop = pure (x == x')

let ref_pts_to (t: Type0) (p: perm) (r: ref t) (v: t) : slprop =
  R.pts_to r #p v

inline_for_extraction
fn ref_pts_to_lens
  (t: Type0)
  (p: perm)
: vmatch_lens #(ref t) #t #t (ref_pts_to t p) (eq_as_slprop t)
=
  (r: ref t)
  (v: Ghost.erased t)
{
  unfold (ref_pts_to t p r (Ghost.reveal v));
  let x = !r;
  fold (ref_pts_to t p r v);
  fold (eq_as_slprop t x v);
  intro (Trade.trade (eq_as_slprop t x v) (ref_pts_to t p r v)) #(ref_pts_to t p r v) fn _{
    unfold (eq_as_slprop t x v)
  };
  x
}

inline_for_extraction
let l2r_leaf_writer
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
= (x: t) ->
  (out: slice byte) ->
  (offset: SZ.t) ->
  (#v: Ghost.erased bytes) ->
  stt SZ.t
    (pts_to out v ** pure (
      SZ.v offset + Seq.length (bare_serialize s x) <= Seq.length v
    ))
    (fun res -> exists* v' .
      pts_to out v' ** pure (
      let bs = bare_serialize s x in
      SZ.v res == SZ.v offset + Seq.length bs /\
      SZ.v res <= Seq.length v /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v offset) == Seq.slice v 0 (SZ.v offset) /\
      Seq.slice v' (SZ.v offset) (SZ.v res) == bs
    ))

inline_for_extraction
fn l2r_leaf_writer_ext
  (#t: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (w1: l2r_leaf_writer s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2 { forall x . parse p1 x == parse p2 x })
: l2r_leaf_writer u#0 #t #k2 #p2 s2
= (x: t)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  serializer_unique_strong s1 s2 x;
  w1 x out offset
}

inline_for_extraction
fn l2r_leaf_writer_ifthenelse
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (cond: bool)
  (iftrue: (squash (cond == true) -> l2r_leaf_writer s))
  (iffalse: (squash (cond == false) -> l2r_leaf_writer s))
: l2r_leaf_writer u#0 #t #k #p s
= (x: t)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  if (cond) {
    iftrue () x out offset;
  } else {
    iffalse () x out offset;
  }
}

inline_for_extraction
fn l2r_writer_of_leaf_writer
  (#t: Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: l2r_leaf_writer s)
: l2r_writer #t #t (eq_as_slprop t) #k #p s
= (x': t)
  (#x: Ghost.erased t)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  unfold (eq_as_slprop t x' x);
  fold (eq_as_slprop t x' x);
  w x' out offset
}

inline_for_extraction
fn l2r_leaf_writer_of_writer
  (#t: Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: l2r_writer #t #t (eq_as_slprop t) #k #p s)
: l2r_leaf_writer u#0 #t #k #p s
= (x: t)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  fold (eq_as_slprop t x x);
  let res = w x out offset;
  unfold (eq_as_slprop t x x);
  res
}

inline_for_extraction
let l2r_leaf_writer_zero_size
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_high == Some 0))
: l2r_leaf_writer u#0 #t #k #p s
= l2r_leaf_writer_of_writer
    (l2r_writer_zero_size _ s ())

inline_for_extraction
let compute_remaining_size
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
= (x': t') ->
  (#x: Ghost.erased t) ->
  (out: R.ref SZ.t) ->
  (#v: Ghost.erased SZ.t) ->
  stt bool
    (R.pts_to out v ** vmatch x' x)
    (fun res -> exists* v' .
      R.pts_to out v' ** vmatch x' x ** pure (
      let bs = Seq.length (bare_serialize s x) in
      (res == true <==> bs <= SZ.v v) /\
      (res == true ==> bs + SZ.v v' == SZ.v v)
    ))

inline_for_extraction
fn compute_size
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (cr: compute_remaining_size vmatch s)
  (x': t')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
  requires
    (R.pts_to out v ** vmatch x' x)
  returns res: bool
  ensures exists* v' .
      R.pts_to out v' ** vmatch x' x ** pure (
      let bs = Seq.length (bare_serialize s x) in
      (res == true <==> bs <= SZ.v v) /\
      (res == true ==> bs == SZ.v v')
    )
{
  let capacity = !out;
  let res = cr x' out;
  if res {
    let remaining = !out;
    out := SZ.sub capacity remaining;
    true
  } else {
    false
  }
}

inline_for_extraction
fn compute_remaining_size_ext
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (cr1: compute_remaining_size vmatch s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2 {
    forall b . parse p1 b == parse p2 b
  })
: compute_remaining_size #t' #t vmatch #k2 #p2 s2
=
  (x': t')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
{
  serializer_unique_strong s1 s2 x;
  cr1 x' out
}

inline_for_extraction
fn compute_remaining_size_ext_gen
  (#t' #t1 #t2: Type0)
  (#vmatch: t' -> t2 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (w: compute_remaining_size (vmatch_ext t1 vmatch) s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2 { t1 == t2 /\ (forall b . parse p1 b == parse p2 b) })
: compute_remaining_size #t' #t2 vmatch #k2 #p2 s2
= (x': t')
  (#x: Ghost.erased t2)
  (out: _)
  (#v: _)
{
  let x1 : Ghost.erased t1 = Ghost.hide #t1 (Ghost.reveal #t2 x);
  serializer_unique_strong s1 s2 x1;
  fold (vmatch_ext t1 vmatch x' x1);
  let res = w x' out;
  unfold (vmatch_ext t1 vmatch x' x1);
  with x2 . assert (vmatch x' x2);
  rewrite (vmatch x' x2) as (vmatch x' x);
  res
}

inline_for_extraction
fn compute_remaining_size_frame
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (const: slprop)
  (cr1: compute_remaining_size vmatch s1)
: compute_remaining_size #t' #t (vmatch_and_const const vmatch) #k1 #p1 s1
=
  (x': t')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
{
  unfold (vmatch_and_const const vmatch);
  let res = cr1 x' out;
  fold (vmatch_and_const const vmatch);
  res
}

inline_for_extraction
fn compute_remaining_size_lens
  (#t1' #t2' #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#vmatch2: t2' -> t -> slprop)
  (lens: vmatch_lens vmatch1 vmatch2)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: compute_remaining_size vmatch2 s)
: compute_remaining_size #t1' #t vmatch1 #k #p s
=
  (x1': t1')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
{
  let x2' = lens x1' _;
  let res = w x2' out;
  elim_trade _ _;
  res
}

inline_for_extraction
fn compute_remaining_size_constant_size
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sz: SZ.t {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == SZ.v sz
  })
: compute_remaining_size #t' #t vmatch #k #p s
=
  (x': t')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
{
  serialize_length s x;
  let capacity = !out;
  if (SZ.lt capacity sz) {
    false
  } else {
    out := SZ.sub capacity sz;
    true
  }
}

inline_for_extraction
fn compute_remaining_size_zero_size
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (
    k.parser_kind_high == Some 0
  ))
: compute_remaining_size #t' #t vmatch #k #p s
=
  (x': t')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
{
  serialize_length s x;
  true
}

inline_for_extraction
fn compute_remaining_size_ifthenelse
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (cond: bool)
  (iftrue: (squash (cond == true) -> compute_remaining_size vmatch s))
  (iffalse: (squash (cond == false) -> compute_remaining_size vmatch s))
: compute_remaining_size #t' #t vmatch #k #p s
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  if (cond) {
    iftrue () x' out
  } else {
    iffalse () x' out
  }
}

inline_for_extraction
fn compute_remaining_size_ifthenelse_low
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (cond: (t' -> bool))
  (iftrue: compute_remaining_size (vmatch_with_cond vmatch cond) s)
  (iffalse: compute_remaining_size (vmatch_with_cond vmatch (pnot cond)) s)
: compute_remaining_size #t' #t vmatch #k #p s
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  if (cond x') {
    fold (vmatch_with_cond vmatch cond x' x);
    let res = iftrue x' out;
    unfold (vmatch_with_cond vmatch cond x' x);
    res
  } else {
    fold (vmatch_with_cond vmatch (pnot cond) x' x);
    let res = iffalse x' out;
    unfold (vmatch_with_cond vmatch (pnot cond) x' x);
    res
  }
}

inline_for_extraction
let leaf_compute_remaining_size
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
= (x: t) ->
  (out: R.ref SZ.t) ->
  (#v: Ghost.erased SZ.t) ->
  stt bool
    (R.pts_to out v)
    (fun res -> exists* v' .
      R.pts_to out v' ** pure (
      let bs = Seq.length (bare_serialize s x) in
      (res == true <==> bs <= SZ.v v) /\
      (res == true ==> bs + SZ.v v' == SZ.v v)
    ))

inline_for_extraction
fn compute_remaining_size_of_leaf_compute_remaining_size
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: leaf_compute_remaining_size s)
: compute_remaining_size #_ #_ (eq_as_slprop _) #_ #_ s
= (x: _)
  (#v: _)
  (out: _)
  (#outv: _)
{
  unfold (eq_as_slprop t x v);
  fold (eq_as_slprop t x v);
  w x out;
}

inline_for_extraction
fn leaf_compute_remaining_size_of_compute_remaining_size
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: compute_remaining_size (eq_as_slprop _) s)
: leaf_compute_remaining_size #_ #_ #_ s
= (x: _)
  (out: _)
  (#outv: _)
{
  fold (eq_as_slprop t x x);
  let res = w x out;
  unfold (eq_as_slprop t x x);
  res
}

inline_for_extraction
fn leaf_compute_remaining_size_ext
  (#t: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (w1: leaf_compute_remaining_size s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2 { forall x . parse p1 x == parse p2 x })
: leaf_compute_remaining_size #t #k2 #p2 s2
= (x: t)
  (out: _)
  (#v: _)
{
  serializer_unique_strong s1 s2 x;
  w1 x out
}

inline_for_extraction
fn leaf_compute_remaining_size_ifthenelse
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (cond: bool)
  (iftrue: (squash (cond == true) -> leaf_compute_remaining_size s))
  (iffalse: (squash (cond == false) -> leaf_compute_remaining_size s))
: leaf_compute_remaining_size #t #k #p s
= (x: t)
  (out: _)
  (#v: _)
{
  if (cond) {
    iftrue () x out;
  } else {
    iffalse () x out;
  }
}

inline_for_extraction
let leaf_compute_remaining_size_constant_size
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sz: SZ.t {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == SZ.v sz
  })
: leaf_compute_remaining_size s
= leaf_compute_remaining_size_of_compute_remaining_size
    (compute_remaining_size_constant_size _ s sz)

inline_for_extraction
let leaf_compute_remaining_size_zero_size
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (
    k.parser_kind_high == Some 0
  ))
: leaf_compute_remaining_size s
= leaf_compute_remaining_size_of_compute_remaining_size
    (compute_remaining_size_zero_size _ s sq)

inline_for_extraction
noeq
type with_perm (t: Type) = {
  v: t;
  p: perm
}

let vmatch_ref
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
: Tot slprop
= exists* vl . R.pts_to r.v #r.p vl ** vmatch vl vh

let vmatch_ref_wf0
  (#tbound: Type)
  (#tl #th: Type0)
  (bound: tbound)
  (vmatch: tl -> (vh: th { vh << bound }) -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
  (sq: option (squash (vh << bound)))
: Tot slprop
= match sq with
  | Some _ -> exists* vl . R.pts_to r.v #r.p vl ** vmatch vl vh
  | None -> pure False

let vmatch_ref_wf
  (#tbound: Type)
  (#tl #th: Type0)
  (bound: tbound)
  (vmatch: tl -> (vh: th { vh << bound }) -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
: Tot slprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (vh << bound)
  then vmatch_ref_wf0 bound vmatch r vh (Some ())
  else pure False

let vmatch_ref_wf_eq
  (#tbound: Type)
  (#tl #th: Type0)
  (bound: tbound)
  (vmatch: tl -> th -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
: Lemma
  (requires (vh << bound))
  (ensures (vmatch_ref_wf bound vmatch r vh == vmatch_ref vmatch r vh))
= let b = (FStar.StrongExcludedMiddle.strong_excluded_middle (vh << bound)) in // FIXME: WHY WHY WHY the let binding?
  assert (vmatch_ref_wf bound vmatch r vh == vmatch_ref_wf0 bound vmatch r vh (Some ()));
  assert_norm (vmatch_ref_wf0 bound vmatch r vh (Some ()) == vmatch_ref vmatch r vh)

ghost fn vmatch_ref_elim_trade
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
requires vmatch_ref vmatch r vh
ensures exists* vl .
  R.pts_to r.v #r.p vl ** vmatch vl vh **
  Trade.trade
    (R.pts_to r.v #r.p vl ** vmatch vl vh)
    (vmatch_ref vmatch r vh)
{
  unfold (vmatch_ref vmatch r vh);
  with vl . assert (R.pts_to r.v #r.p vl ** vmatch vl vh);
  intro (Trade.trade (R.pts_to r.v #r.p vl ** vmatch vl vh) (vmatch_ref vmatch r vh)) #emp fn _{
    fold (vmatch_ref vmatch r vh)
  };
}

inline_for_extraction
fn l2r_write_ref
  (#th: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k th)
  (#s: serializer p)
  (#tl: Type0)
  (#vmatch: tl -> th -> slprop)
  (w: l2r_writer vmatch s)
: l2r_writer #_ #_ (vmatch_ref vmatch) #_ #_ s
=
  (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  vmatch_ref_elim_trade vmatch x' x;
  with gz . assert (vmatch gz x);
  let z = !(x'.v);
  Trade.elim_hyp_l _ _ _;
  Trade.rewrite_with_trade (vmatch gz x) (vmatch z x);
  Trade.trans _ _ (vmatch_ref vmatch x' x);
  let res = w z out offset;
  Trade.elim _ _;
  res
}

let pts_to_serialized_with_perm
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (input: with_perm (S.slice byte))
  (v: t)
: Tot slprop
= pts_to_serialized s input.v #input.p v

inline_for_extraction
fn l2r_write_copy
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
: l2r_writer #_ #_ (pts_to_serialized_with_perm s) #_ #_ s
= (x: _)
  (#v: _)
  (out: _)
  (offset: SZ.t)
  (#w: _)
{
  Trade.rewrite_with_trade
    (pts_to_serialized_with_perm s x v)
    (pts_to_serialized s x.v #x.p v);
  pts_to_serialized_elim_trade s x.v;
  Trade.trans _ _ (pts_to_serialized_with_perm s x v);
  S.pts_to_len out;
  S.pts_to_len x.v;
  let length = S.len x.v;
  let sp11, sp12 = S.split out offset;
  with v12 . assert (pts_to sp12 v12);
  let sp21, sp22 = S.split sp12 length;
  S.pts_to_len sp21;
  S.copy sp21 x.v;
  S.join sp21 sp22 sp12;
  S.join sp11 sp12 out;
  Trade.elim _ _;
  SZ.add offset length;
}

inline_for_extraction
fn compute_remaining_size_copy
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
: compute_remaining_size #_ #_ (pts_to_serialized_with_perm s) #_ #_ s
= (x: _)
  (#v: _)
  (out: _)
  (#w: _)
{
  Trade.rewrite_with_trade
    (pts_to_serialized_with_perm s x v)
    (pts_to_serialized s x.v #x.p v);
  pts_to_serialized_elim_trade s x.v;
  Trade.trans _ _ (pts_to_serialized_with_perm s x v);
  S.pts_to_len x.v;
  Trade.elim _ _;
  let length = S.len x.v;
  let cur = !out;
  if (SZ.lt cur length) {
    false
  } else {
    out := SZ.sub cur length;
    true
  }
}

inline_for_extraction
fn pts_to_serialized_copy
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (src: S.slice byte)
  (#psrc: perm)
  (#vsrc: Ghost.erased t)
  (dst: S.slice byte)
requires
  exists* vdst . pts_to dst vdst ** pts_to_serialized s src #psrc vsrc **
    pure (S.len src == S.len dst)
ensures
  pts_to_serialized s src #psrc vsrc **
  pts_to_serialized s dst vsrc
{
  unfold (pts_to_serialized s src #psrc vsrc);
  S.copy dst src;
  fold (pts_to_serialized s src #psrc vsrc);
  fold (pts_to_serialized s dst vsrc);
}

inline_for_extraction
let zero_copy_parse
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
=
  (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  stt t'
    (pts_to_serialized s input #pm v)
    (fun res ->
      vmatch res v **
      Trade.trade
        (vmatch res v)
        (pts_to_serialized s input #pm v)
    )

inline_for_extraction
fn zero_copy_parse_id
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
: zero_copy_parse #_ #_ (pts_to_serialized_with_perm s) #_ #_ s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let res = { v = input; p = pm };
  Trade.rewrite_with_trade
    (pts_to_serialized s input #pm v)
    (pts_to_serialized_with_perm s res v);
  res
}

inline_for_extraction
fn zero_copy_parse_lens
  (#t1'  #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: zero_copy_parse vmatch1 s)
  (#t2': Type0)
  (#vmatch2: t2' -> t -> slprop)
  (lens: vmatch_lens vmatch1 vmatch2)
: zero_copy_parse #_ #_ vmatch2 #_ #_ s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let tmp = r input;
  let res = lens tmp _;
  Trade.trans (vmatch2 res _) _ _;
  res
}

inline_for_extraction
fn zero_copy_parse_read
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: leaf_reader s)
: zero_copy_parse #_ #_ (eq_as_slprop t) #_ #_ s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let res = r input;
  fold (eq_as_slprop t res v);
  intro (Trade.trade (eq_as_slprop t res v) (pts_to_serialized s input #pm v)) #(pts_to_serialized s input #pm v) fn _{
    unfold (eq_as_slprop t res v)
  };
  res
}

let vmatch_ignore (#t2: Type0) (x1: unit) (x2: t2) : Tot slprop = emp

inline_for_extraction
fn zero_copy_parse_ignore
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
: zero_copy_parse #_ #_ (vmatch_ignore #t) #_ #_ s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  fold (vmatch_ignore () (Ghost.reveal v));
  intro (Trade.trade (vmatch_ignore () (Ghost.reveal v)) (pts_to_serialized s input #pm v)) #(pts_to_serialized s input #pm v) fn _{
    unfold (vmatch_ignore () (Ghost.reveal v))
  };
  ()
}

inline_for_extraction
fn zero_copy_parse_ext
  (#t1'  #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: zero_copy_parse vmatch1 s)
  (#k': Ghost.erased parser_kind)
  (#p': parser k' t)
  (s': serializer p' {
    forall b . parse p b == parse p' b
  })
: zero_copy_parse #_ #_ vmatch1 #_ #_ s'
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  pts_to_serialized_ext_trade s' s input;
  let res = r input;
  Trade.trans (vmatch1 res v) _ _;
  res
}

inline_for_extraction
fn zero_copy_parse_ifthenelse
  (#t1'  #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (cond: bool)
  (rtrue: squash (cond == true) -> zero_copy_parse vmatch1 s)
  (rfalse: squash (cond == false) -> zero_copy_parse vmatch1 s)
: zero_copy_parse #_ #_ vmatch1 #_ #_ s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  if (cond) {
    rtrue () input
  } else {
    rfalse () input
  }
}

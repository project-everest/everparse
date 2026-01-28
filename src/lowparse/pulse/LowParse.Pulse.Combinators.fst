module LowParse.Pulse.Combinators
#lang-pulse
include LowParse.Spec.Combinators
include LowParse.Pulse.Base
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
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

inline_for_extraction
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

inline_for_extraction
fn l2r_leaf_write_ret
  (#t: Type0)
  (x: t)
  (v_unique: (v' : t) -> Lemma (x == v'))
: l2r_leaf_writer u#0 #t #_ #_ (serialize_ret x v_unique)
= (x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  offset
}

inline_for_extraction
fn compute_remaining_size_ret
  (#t: Type0)
  (x: t)
  (v_unique: (v' : t) -> Lemma (x == v'))
: leaf_compute_remaining_size #t #_ #_ (serialize_ret x v_unique)
= (x: _)
  (out: _)
  (#v: _)
{
  true
}

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

inline_for_extraction
let l2r_leaf_write_empty : l2r_leaf_writer serialize_empty = l2r_leaf_write_ret () (fun _ -> ())

inline_for_extraction
let leaf_compute_remaining_size_empty : leaf_compute_remaining_size serialize_empty = compute_remaining_size_ret () (fun _ -> ())

ghost
fn l2r_write_empty_lens_aux
  (#tl: Type0)
  (vmatch: tl -> unit -> slprop)
  (xl: tl)
  (v: unit)
requires
  vmatch xl v
ensures
  eq_as_slprop unit () v **
  Trade.trade
    (eq_as_slprop unit () v)
    (vmatch xl v)
{
  fold (eq_as_slprop unit () v);
  intro
    (Trade.trade
      (eq_as_slprop unit () v)
      (vmatch xl v)
    )
    #(vmatch xl v)
    fn _
  {
    unfold (eq_as_slprop unit () v)
  };
}

inline_for_extraction
fn l2r_write_empty_lens
  (#tl: Type0)
  (vmatch: tl -> unit -> slprop)
: vmatch_lens #_ #_ #_ vmatch (eq_as_slprop unit)
= (xl: _)
  (v: _)
{
  l2r_write_empty_lens_aux vmatch xl v;
  ()
}

inline_for_extraction
let l2r_write_empty
  (#tl: Type0)
  (vmatch: tl -> unit -> slprop)
: l2r_writer vmatch serialize_empty
= l2r_writer_lens (l2r_write_empty_lens vmatch) (l2r_writer_of_leaf_writer l2r_leaf_write_empty)

inline_for_extraction
let compute_remaining_size_empty
  (#tl: Type0)
  (vmatch: tl -> unit -> slprop)
: compute_remaining_size vmatch serialize_empty
= compute_remaining_size_lens (l2r_write_empty_lens vmatch) (compute_remaining_size_of_leaf_compute_remaining_size leaf_compute_remaining_size_empty)

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

inline_for_extraction
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
  intro
    (Trade.trade
      (pts_to_serialized (serialize_synth p f s f' ()) input #pm (f v))
      (pts_to_serialized s input #pm v)
    )
    #emp
    fn _
  {
    pts_to_serialized_synth_elim s f f' input v 
  };
}

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
  intro
    (Trade.trade
      (pts_to_serialized s input #pm (f' v))
      (pts_to_serialized (serialize_synth p f s f' ()) input #pm v)
    )
    #emp
    fn _
  {
    pts_to_serialized_synth_r2l s f f' input v
  };
}

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
let validate_filter_test_t
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
: Tot Type
= 
  (x: slice byte) -> (#pm: perm) -> (#v: Ghost.erased t) -> stt bool
    (requires pts_to_serialized s x #pm v)
    (ensures fun res -> pts_to_serialized s x #pm v ** pure (res == f v))

inline_for_extraction
fn validate_filter_gen
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: validator p)
  (s: serializer p)
  (f: (t -> GTot bool))
  (f': validate_filter_test_t s f)
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
    let x = peek_trade_gen s input offset off;
    let res = f' x;
    Trade.elim _ _;
    res
  } else {
    false
  }
}

inline_for_extraction
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

inline_for_extraction
let parse_filter_refine_intro
  (#t: Type)
  (f: (t -> GTot bool))
  (v: t)
  (sq: squash (f v == true))
: Tot (parse_filter_refine f)
= v

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

ghost
fn pts_to_serialized_filter_elim_trade
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
  (input: slice byte)
  (#pm: perm)
  (#v: parse_filter_refine f)
  requires (pts_to_serialized (serialize_filter s f) input #pm v)
  ensures exists* (v': t) . pts_to_serialized s input #pm v' ** Trade.trade (pts_to_serialized s input #pm v') (pts_to_serialized (serialize_filter s f) input #pm v) ** pure (v' == v)
{
  pts_to_serialized_filter_elim s f input;
  intro
    (Trade.trade
      (pts_to_serialized s input #pm v)
      (pts_to_serialized (serialize_filter s f) input #pm v)
    )
    #emp
    fn _
  {
    pts_to_serialized_filter_intro s f input
  };
}

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

inline_for_extraction
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

inline_for_extraction
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

inline_for_extraction
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
  (res: (slice byte & slice byte))
: Tot slprop
= let (left, right) = res in
  split_dtuple2_post' s1 s2 input pm v left right

inline_for_extraction
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
  returns res: (slice byte & slice byte)
  ensures split_dtuple2_post s1 s2 input pm v res
{
  serialize_dtuple2_eq s1 s2 v;
  Trade.rewrite_with_trade
    (pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v)
    (pts_to input #pm (bare_serialize s1 (dfst v) `Seq.append` bare_serialize (s2 (dfst v)) (dsnd v)));
  parse_serialize_strong_prefix s1 (dfst v) (bare_serialize (s2 (dfst v)) (dsnd v));
  let i = j1 input 0sz;
  let input1, input2 = append_split_trade input i;
  Trade.trans (_ ** _) _ _;
  pts_to_serialized_intro_trade s1 input1 (dfst v);
  pts_to_serialized_intro_trade (s2 (dfst v)) input2 (dsnd v);
  Trade.prod (pts_to_serialized s1 input1 #pm _) (pts_to input1 #pm _) (pts_to_serialized (s2 (dfst v)) input2 #pm _) (pts_to input2 #pm _);
  Trade.trans (pts_to_serialized s1 input1 #pm _ ** pts_to_serialized (s2 (dfst v)) input2 #pm _) (pts_to input1 #pm _ ** pts_to input2 #pm _) _;
  fold (split_dtuple2_post' s1 s2 input pm v input1 input2);
  fold (split_dtuple2_post s1 s2 input pm v (input1, input2));
  (input1, input2)
}

ghost fn ghost_split_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (#pm: perm)
  (#v: (dtuple2 t1 t2))
  requires pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v
  returns res: Ghost.erased (slice byte & slice byte)
  ensures
    pts_to_serialized s1 (fst res) #pm (dfst v) **
    pts_to_serialized (s2 (dfst v)) (snd res) #pm (dsnd v) **
    is_split input (fst res) (snd res)
{
  serialize_dtuple2_eq s1 s2 v;
  rewrite
    (pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v)
    as
    (pts_to input #pm (bare_serialize s1 (dfst v) `Seq.append` bare_serialize (s2 (dfst v)) (dsnd v)));
  parse_serialize_strong_prefix s1 (dfst v) (bare_serialize (s2 (dfst v)) (dsnd v));
  pts_to_len input;
  let i = SZ.uint_to_t (Seq.length (bare_serialize s1 (dfst v)));
  let res = ghost_append_split input i;
  fold pts_to_serialized s1 (fst res) #pm (dfst v);
  fold pts_to_serialized (s2 (dfst v)) (snd res) #pm (dsnd v);
  res
}

ghost fn join_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (x1: slice byte)
  (#pm: perm)
  (#v1: t1)
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: (x: t1) -> serializer (p2 x))
  (x2: slice byte)
  (x: slice byte)
  (#v2: t2 v1)
requires
  pts_to_serialized s1 x1 #pm v1 **
  pts_to_serialized (s2 v1) x2 #pm v2 **
  is_split x x1 x2
ensures exists* (v: dtuple2 t1 t2) .
  pts_to_serialized (serialize_dtuple2 s1 s2) x #pm v **
  pure (dfst v == v1 /\ dsnd v == v2)
{
  unfold (pts_to_serialized s1 x1 #pm v1);
  unfold (pts_to_serialized (s2 v1) x2 #pm v2);
  join x1 x2 x;
  let v : dtuple2 t1 t2 = (| v1, v2 |);
  serialize_dtuple2_eq s1 s2 v;
  fold (pts_to_serialized (serialize_dtuple2 s1 s2) x #pm v)
}

inline_for_extraction
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
  let input1, input2 = split_dtuple2 s1 j1 s2 input;
  unfold (split_dtuple2_post s1 s2 input pm v (input1, input2));
  unfold (split_dtuple2_post' s1 s2 input pm v input1 input2);
  Trade.elim_hyp_r _ _ _;
  input1
}

inline_for_extraction
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
  let input1, input2 = split_dtuple2 s1 j1 s2 input;
  unfold (split_dtuple2_post s1 s2 input pm v (input1, input2));
  unfold (split_dtuple2_post' s1 s2 input pm v input1 input2);
  Trade.elim_hyp_l _ _ _;
  input2
}

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
  (v: (t1 & t2))
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
  (v: (t1 & t2))
  (res: (slice byte & slice byte))
: Tot slprop
= let (left, right) = res in
  split_nondep_then_post' s1 s2 input pm v left right

ghost
fn pts_to_serialized_ext'
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
  ensures pts_to_serialized s2 input #pm v
{
  Classical.forall_intro prf;
  pts_to_serialized_ext s1 s2 input
}

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

inline_for_extraction
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
  returns res: (slice byte & slice byte)
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
  let input1, input2 = split_dtuple2 #t1 #(const_fun t2) s1 j1 #_ #(const_fun p2) (const_fun s2) input;
  unfold (split_dtuple2_post #t1 #(const_fun t2) s1 #k2 #(const_fun p2) (const_fun s2) input pm (dtuple2_of_pair v) (input1, input2));
  unfold (split_dtuple2_post' #t1 #(const_fun t2) s1 #_ #(const_fun p2) (const_fun s2) input pm (dtuple2_of_pair v) input1 input2);
  Trade.trans (_ ** _) _ _;
  rewrite
    (trade (pts_to_serialized s1 input1 #pm (dfst (dtuple2_of_pair v)) **
        pts_to_serialized (const_fun s2 (dfst (dtuple2_of_pair v)))
          input2 #pm
          (dsnd (dtuple2_of_pair v)))
      (pts_to_serialized (serialize_nondep_then s1 s2) input #pm v))
    as
    (trade (pts_to_serialized s1 input1 #pm (fst v) **
        pts_to_serialized (const_fun s2 (fst v))
          input2 #pm
          (snd v))
      (pts_to_serialized (serialize_nondep_then s1 s2) input #pm v));
  fold (split_nondep_then_post' s1 s2 input pm v input1 input2);
  fold (split_nondep_then_post s1 s2 input pm v (input1, input2));
  (input1, input2)
}

inline_for_extraction
fn split_nondep_then'
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
  returns res: (slice byte & slice byte)
  ensures (
  let (left, right) = res in
  pts_to_serialized s1 left #pm (fst v) **
  pts_to_serialized s2 right #pm (snd v) **
  trade (pts_to_serialized s1 left #pm (fst v) **
  pts_to_serialized s2 right #pm (snd v))
    (pts_to_serialized (serialize_nondep_then s1 s2) input #pm v)
  )
{
  let (left, right) = split_nondep_then s1 j1 s2 input;
  unfold (split_nondep_then_post s1 s2 input pm v (left, right));
  unfold (split_nondep_then_post' s1 s2 input pm v left right);
  (left, right)
}

let split_nondep_then''_precond
  (#t0 #t1 #t2: Type0)
  (#k0: Ghost.erased parser_kind)
  (p0: parser k0 t0)
  (#k1: Ghost.erased parser_kind)
  (p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (p2: parser k2 t2)
: Tot prop
= t0 == (t1 & t2) /\
  k1.parser_kind_subkind == Some ParserStrong /\
  (forall b . parse p0 b == parse (nondep_then p1 p2) b)

let split_nondep_then''_postcond
  (#t0 #t1 #t2: Type)
  (v: t0)
  (v1: t1)
  (v2: t2)
: Tot prop
= t0 == (t1 & t2) /\
  v == coerce_eq () (v1, v2)

#push-options "--print_implicits"

inline_for_extraction
fn split_nondep_then''
  (#t0 #t1 #t2: Type0)
  (#k0: Ghost.erased parser_kind)
  (#p0: parser k0 t0)
  (#s0: serializer p0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1)
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t0)
  (sq: squash (
    split_nondep_then''_precond p0 p1 p2
  ))
  requires pts_to_serialized s0 input #pm v
  returns res: (slice byte & slice byte)
  ensures (
  let (left, right) = res in
  exists* v1 v2 .
  pts_to_serialized s1 left #pm v1 **
  pts_to_serialized s2 right #pm v2 **
  trade (pts_to_serialized s1 left #pm v1 **
  pts_to_serialized s2 right #pm v2)
    (pts_to_serialized s0 input #pm v) **
  pure (split_nondep_then''_postcond (Ghost.reveal v) v1 v2)
  )
{
  pts_to_serialized_ext_trade
    s0
    (serialize_nondep_then s1 s2)
    input;
  let (left, right) = split_nondep_then s1 j1 s2 input;
  unfold (split_nondep_then_post s1 s2 input pm v (left, right));
  unfold (split_nondep_then_post' s1 s2 input pm v left right);
  rewrite each (t1 & t2) as t0;
  Trade.trans (_ ** _) _ (pts_to_serialized s0 input #pm v);
  (left, right)
}

ghost fn ghost_split_nondep_then
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: (t1 & t2))
  requires pts_to_serialized (serialize_nondep_then s1 s2) input #pm v
  returns res: Ghost.erased (slice byte & slice byte)
  ensures
    pts_to_serialized s1 (fst res) #pm (fst v) **
    pts_to_serialized s2 (snd res) #pm (snd v) **
    is_split input (fst res) (snd res)
{
  pts_to_serialized_ext'
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
  pts_to_serialized_synth_l2r
    (serialize_dtuple2 s1 #k2 #(const_fun t2) #(const_fun p2) (const_fun s2))
    pair_of_dtuple2
    dtuple2_of_pair
    input;
  ghost_split_dtuple2 #t1 #(const_fun t2) s1 #_ #(const_fun p2) (const_fun s2) input;
}

ghost fn join_nondep_then
  (#t1: Type0)
  (#t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (x1: slice byte)
  (#pm: perm)
  (#v1: t1)
  (#k2: parser_kind)
  (#p2: (parser k2 (t2)))
  (s2: serializer (p2))
  (x2: slice byte)
  (x: slice byte)
  (#v2: t2)
requires
  pts_to_serialized s1 x1 #pm v1 **
  pts_to_serialized (s2) x2 #pm v2 **
  is_split x x1 x2
ensures exists* v .
  pts_to_serialized (serialize_nondep_then s1 s2) x #pm v **
  pure (fst v == v1 /\ snd v == v2)
{
  unfold (pts_to_serialized s1 x1 #pm v1);
  unfold (pts_to_serialized (s2) x2 #pm v2);
  join x1 x2 x;
  let v : (t1 & t2) = (v1, v2);
  serialize_nondep_then_eq s1 s2 v;
  fold (pts_to_serialized (serialize_nondep_then s1 s2) x #pm v)
}

ghost fn pts_to_serialized_nondep_then_assoc_l2r
  (#t1: Type0)
  (#t2: Type0)
  (#t3: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: (parser k2 (t2)))
  (s2: serializer (p2) { k2.parser_kind_subkind == Some ParserStrong })
  (#k3: parser_kind)
  (#p3: (parser k3 (t3)))
  (s3: serializer (p3))
  (x: slice byte)
  (#pm: perm)
  (#v: ((t1 & t2) & t3))
requires
  pts_to_serialized (serialize_nondep_then (serialize_nondep_then s1 s2) s3) x #pm v
ensures exists* v' .
  pts_to_serialized (serialize_nondep_then s1 (serialize_nondep_then s2 s3)) x #pm v' **
  Trade.trade
    (pts_to_serialized (serialize_nondep_then s1 (serialize_nondep_then s2 s3)) x #pm v')
    (pts_to_serialized (serialize_nondep_then (serialize_nondep_then s1 s2) s3) x #pm v) **
  pure (v' == (fst (fst v), (snd (fst v), snd v)))
{
  let v1 = fst (fst v);
  let v2 = snd (fst v);
  let v3 = snd v;
  serialize_nondep_then_eq (serialize_nondep_then s1 s2) s3 v;
  serialize_nondep_then_eq s1 s2 (fst v);
  let v23 = (v2, v3);
  serialize_nondep_then_eq s2 s3 v23;
  let v' = (v1, v23);
  serialize_nondep_then_eq s1 (serialize_nondep_then s2 s3) v';
  Seq.append_assoc (serialize s1 v1) (serialize s2 v2) (serialize s3 v3);
  Trade.rewrite_with_trade
    (pts_to_serialized (serialize_nondep_then (serialize_nondep_then s1 s2) s3) x #pm v)
    (pts_to_serialized (serialize_nondep_then s1 (serialize_nondep_then s2 s3)) x #pm v')
}

ghost fn pts_to_serialized_nondep_then_assoc_r2l
  (#t1: Type0)
  (#t2: Type0)
  (#t3: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: (parser k2 (t2)))
  (s2: serializer (p2) { k2.parser_kind_subkind == Some ParserStrong })
  (#k3: parser_kind)
  (#p3: (parser k3 (t3)))
  (s3: serializer (p3))
  (x: slice byte)
  (#pm: perm)
  (#v: (t1 & (t2 & t3)))
requires
  pts_to_serialized (serialize_nondep_then s1 (serialize_nondep_then s2 s3)) x #pm v
ensures exists* v' .
  pts_to_serialized (serialize_nondep_then (serialize_nondep_then s1 s2) s3) x #pm v' **
  Trade.trade
    (pts_to_serialized (serialize_nondep_then (serialize_nondep_then s1 s2) s3) x #pm v')
    (pts_to_serialized (serialize_nondep_then s1 (serialize_nondep_then s2 s3)) x #pm v) **
  pure (v' == ((fst v, fst (snd v)), snd (snd v)))
{
  let v1 = fst v;
  let v2 = fst (snd v);
  let v3 = snd (snd v);
  serialize_nondep_then_eq s1 (serialize_nondep_then s2 s3) v;
  serialize_nondep_then_eq s2 s3 (snd v);
  let v12 = (v1, v2);
  serialize_nondep_then_eq s1 s2 v12;
  let v' = (v12, v3);
  serialize_nondep_then_eq (serialize_nondep_then s1 s2) s3 v';
  Seq.append_assoc (serialize s1 v1) (serialize s2 v2) (serialize s3 v3);
  Trade.rewrite_with_trade
    (pts_to_serialized (serialize_nondep_then s1 (serialize_nondep_then s2 s3)) x #pm v)
    (pts_to_serialized (serialize_nondep_then (serialize_nondep_then s1 s2) s3) x #pm v')
}

ghost fn pts_to_serialized_dtuple2_as_nondep_then
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: (x: t1) -> serializer (p2 x))
  (input: slice byte)
  (#pm: perm)
  (#v: (dtuple2 t1 t2))
  requires pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v
  ensures exists* v' .
    pts_to_serialized (serialize_nondep_then s1 (s2 (dfst v))) input #pm v' **
    Trade.trade
      (pts_to_serialized (serialize_nondep_then s1 (s2 (dfst v))) input #pm v')
      (pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v) **
    pure (fst v' == dfst v /\ snd v' == dsnd v)
{
  let v' : (t1 & t2 (dfst v)) = (dfst v, dsnd v);
  serialize_dtuple2_eq s1 s2 v;
  serialize_nondep_then_eq s1 (s2 (dfst v)) v';
  Trade.rewrite_with_trade
    (pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v)
    ((pts_to_serialized (serialize_nondep_then s1 (s2 (dfst v))) input #pm v'))
}

ghost fn pts_to_serialized_dtuple2_nondep_then_assoc_l2r
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#t3: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (s2: ((x: t1) -> serializer (p2 x)) { k2.parser_kind_subkind == Some ParserStrong } ) 
  (#k3: parser_kind)
  (#p3: parser k3 t3)
  (s3: serializer p3)
  (input: slice byte)
  (#pm: perm)
  (#v: (dtuple2 t1 t2 & t3))
  requires pts_to_serialized (serialize_nondep_then (serialize_dtuple2 s1 s2) s3) input #pm v
  ensures exists* v' .
    pts_to_serialized (serialize_nondep_then s1 (serialize_nondep_then (s2 (dfst (fst v))) s3)) input #pm v' **
    Trade.trade
      (pts_to_serialized (serialize_nondep_then s1 (serialize_nondep_then (s2 (dfst (fst v))) s3)) input #pm v')
      (pts_to_serialized (serialize_nondep_then (serialize_dtuple2 s1 s2) s3) input #pm v) **
    pure (fst v' == dfst (fst v) /\ fst (snd v') == dsnd (fst v) /\ snd (snd v') == snd v)
{
  let res = ghost_split_nondep_then (serialize_dtuple2 s1 s2) s3 input;
  with v12 . assert (pts_to_serialized (serialize_dtuple2 s1 s2) (fst res) #pm v12);
  let res12 = ghost_split_dtuple2 s1 s2 (fst res);
  join_nondep_then s1 (fst res12) (s2 (dfst v12)) (snd res12) (fst res);
  join_nondep_then (serialize_nondep_then s1 (s2 (dfst v12))) (fst res) s3 (snd res) input;
  with v_ . assert (pts_to_serialized (serialize_nondep_then (serialize_nondep_then s1 (s2 (dfst v12))) s3) input #pm v_);
  intro
    (Trade.trade
      (pts_to_serialized (serialize_nondep_then (serialize_nondep_then s1 (s2 (dfst v12))) s3) input #pm v_)
      (pts_to_serialized (serialize_nondep_then (serialize_dtuple2 s1 s2) s3) input #pm v)
    )
    #emp
    fn _
  {
    let res = ghost_split_nondep_then (serialize_nondep_then s1 (s2 (dfst v12))) s3 input;
    let res12 = ghost_split_nondep_then s1 (s2 (dfst v12)) (fst res);
    join_dtuple2 s1 (fst res12) s2 (snd res12) (fst res);
    join_nondep_then (serialize_dtuple2 s1 s2) (fst res) s3 (snd res) input
  };
  pts_to_serialized_nondep_then_assoc_l2r s1 (s2 (dfst v12)) s3 input;
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then (serialize_dtuple2 s1 s2) s3) input #pm v)
}

ghost
fn pts_to_serialized_synth_l2r_nondep_then_left
  (#t: Type0)
  (#t': Type0)
  (#t2: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: (t' & t2))
  requires pts_to_serialized (serialize_nondep_then (serialize_synth p f s f' ()) s2) input #pm v
  ensures exists* v' .
    pts_to_serialized (serialize_nondep_then s s2) input #pm v' **
    Trade.trade
      (pts_to_serialized (serialize_nondep_then s s2) input #pm v')
      (pts_to_serialized (serialize_nondep_then (serialize_synth p f s f' ()) s2) input #pm v) **
    pure (fst v' == f' (fst v) /\ snd v' == snd v)
{
  let res = ghost_split_nondep_then (serialize_synth p f s f' ()) s2 input;
  pts_to_serialized_synth_l2r s f f' (fst res);
  join_nondep_then s (fst res) s2 (snd res) input;
  with v' . assert (pts_to_serialized (serialize_nondep_then s s2) input #pm v');
  intro
    (Trade.trade
      (pts_to_serialized (serialize_nondep_then s s2) input #pm v')
      (pts_to_serialized (serialize_nondep_then (serialize_synth p f s f' ()) s2) input #pm v)
    )
    #emp
    fn _
  {
    let res = ghost_split_nondep_then s s2 input;
    pts_to_serialized_synth_intro s f f' (fst res);
    join_nondep_then (serialize_synth p f s f' ()) (fst res) s2 (snd res) input;
  };
}

ghost
fn pts_to_serialized_filter_elim_nondep_then_left
  (#t: Type0)
  (#t2: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (f: (t -> GTot bool))
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: (parse_filter_refine f & t2))
  requires (pts_to_serialized (serialize_filter s f `serialize_nondep_then` s2) input #pm v)
  ensures exists* (v': (t & t2)) . pts_to_serialized (s `serialize_nondep_then` s2) input #pm v' **
    Trade.trade
      (pts_to_serialized (s `serialize_nondep_then` s2) input #pm v')
      (pts_to_serialized (serialize_filter s f `serialize_nondep_then` s2) input #pm v) **
    pure (fst v' == fst v /\ snd v' == snd v)
{
  let res = ghost_split_nondep_then (serialize_filter s f) s2 input;
  pts_to_serialized_filter_elim s f (fst res);
  join_nondep_then s (fst res) s2 (snd res) input;
  with v' . assert (pts_to_serialized (s `serialize_nondep_then` s2) input #pm v');
  intro
    (Trade.trade
      (pts_to_serialized (s `serialize_nondep_then` s2) input #pm v')
      (pts_to_serialized (serialize_filter s f `serialize_nondep_then` s2) input #pm v)
    )
    #emp
    fn _
  {
    let res = ghost_split_nondep_then s s2 input;
    pts_to_serialized_filter_intro s f (fst res);
    join_nondep_then (serialize_filter s f) (fst res) s2 (snd res) input;
  };
}

ghost
fn pts_to_serialized_ext_nondep_then_left'
  (#t1 #t2 #t3: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2 { k2.parser_kind_subkind == Some ParserStrong })
  (#k3: parser_kind)
  (#p3: parser k3 t3)
  (s3: serializer p3)
  (input: slice byte)
  (#pm: perm)
  (#v: (t1 & t3))
  requires pts_to_serialized (serialize_nondep_then s1 s3) input #pm v ** pure (
    pts_to_serialized_ext_trade_gen_precond p1 p2
  )
  ensures exists* v23 .
    pts_to_serialized (serialize_nondep_then s2 s3) input #pm v23 **
    pure (t1 == t2 /\
      v == v23
    )
{
  let res = ghost_split_nondep_then s1 s3 input;
  pts_to_serialized_ext s1 s2 (fst res);
  join_nondep_then s2 (fst res) s3 (snd res) input;
}

ghost
fn pts_to_serialized_ext_nondep_then_left
  (#t1 #t2 #t3: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2 { k2.parser_kind_subkind == Some ParserStrong })
  (#k3: parser_kind)
  (#p3: parser k3 t3)
  (s3: serializer p3)
  (input: slice byte)
  (#pm: perm)
  (#v: (t1 & t3))
  requires pts_to_serialized (serialize_nondep_then s1 s3) input #pm v ** pure (
    pts_to_serialized_ext_trade_gen_precond p1 p2
  )
  ensures exists* v23 .
    pts_to_serialized (serialize_nondep_then s2 s3) input #pm v23 ** trade (pts_to_serialized (serialize_nondep_then s2 s3) input #pm v23) (pts_to_serialized (serialize_nondep_then s1 s3) input #pm v) **
    pure (t1 == t2 /\
      v == v23
    )
{
  pts_to_serialized_ext_nondep_then_left' s1 s2 s3 input;
  with v23 . assert (pts_to_serialized (serialize_nondep_then s2 s3) input #pm v23);
  intro
    (Trade.trade
      (pts_to_serialized (serialize_nondep_then s2 s3) input #pm v23)
      (pts_to_serialized (serialize_nondep_then s1 s3) input #pm v)
    )
    #emp
    fn _
  {
    pts_to_serialized_ext_nondep_then_left' s2 s1 s3 input;
  };
}

ghost
fn pts_to_serialized_ext_nondep_then_right'
  (#t1 #t2 #t3: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (#k3: parser_kind)
  (#p3: parser k3 t3)
  (s3: serializer p3)
  (input: slice byte)
  (#pm: perm)
  (#v: (t1 & t2))
  requires pts_to_serialized (serialize_nondep_then s1 s2) input #pm v ** pure (
    pts_to_serialized_ext_trade_gen_precond p2 p3
  )
  ensures exists* v13 .
    pts_to_serialized (serialize_nondep_then s1 s3) input #pm v13 **
    pure (t2 == t3 /\
      v == v13
    )
{
  let res = ghost_split_nondep_then s1 s2 input;
  pts_to_serialized_ext s2 s3 (snd res);
  join_nondep_then s1 (fst res) s3 (snd res) input;
}

let pts_to_serialized_ext_nondep_then_right_post
  (#t1 #t2 #t3: Type)
  (v: (t1 & t2))
  (v13: (t1 & t3))
: Tot prop
= t2 == t3 /\
  v == v13

ghost
fn pts_to_serialized_ext_nondep_then_right
  (#t1 #t2 #t3: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (#k3: parser_kind)
  (#p3: parser k3 t3)
  (s3: serializer p3)
  (input: slice byte)
  (#pm: perm)
  (#v: (t1 & t2))
  requires pts_to_serialized (serialize_nondep_then s1 s2) input #pm v ** pure (
    pts_to_serialized_ext_trade_gen_precond p2 p3
  )
  ensures exists* v13 .
    pts_to_serialized (serialize_nondep_then s1 s3) input #pm v13 ** trade (pts_to_serialized (serialize_nondep_then s1 s3) input #pm v13) (pts_to_serialized (serialize_nondep_then s1 s2) input #pm v) **
    pure (
      pts_to_serialized_ext_nondep_then_right_post v v13
    )
{
  pts_to_serialized_ext_nondep_then_right' s1 s2 s3 input;
  with v13 . assert (pts_to_serialized (serialize_nondep_then s1 s3) input #pm v13);
  intro
    (Trade.trade
      (pts_to_serialized (serialize_nondep_then s1 s3) input #pm v13)
      (pts_to_serialized (serialize_nondep_then s1 s2) input #pm v)
    )
    #emp
    fn _
  {
    pts_to_serialized_ext_nondep_then_right' s1 s3 s2 input;
  };
}


inline_for_extraction
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
  let input1, input2 = split_nondep_then s1 j1 s2 input;
  unfold (split_nondep_then_post s1 s2 input pm v (input1, input2));
  unfold (split_nondep_then_post' s1 s2 input pm v input1 input2);
  Trade.elim_hyp_r _ _ _;
  input1
}

let nondep_then_fst'_precond
  (#t0 #t1 #t2: Type0)
  (#k0: Ghost.erased parser_kind)
  (p0: parser k0 t0)
  (#k1: Ghost.erased parser_kind)
  (p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (p2: parser k2 t2)
: Tot prop
= t0 == (t1 & t2) /\
  k1.parser_kind_subkind == Some ParserStrong /\
  (forall b . parse p0 b == parse (nondep_then p1 p2) b)

let nondep_then_fst'_postcond
  (#t0 #t1 t2: Type)
  (v: t0)
  (v': t1)
: Tot prop
= t0 == (t1 & t2) /\
  v' == fst #t1 #t2 (coerce_eq () v)

inline_for_extraction
fn nondep_then_fst'
  (#t0 #t1 #t2: Type0)
  (#k0: Ghost.erased parser_kind)
  (#p0: parser k0 t0)
  (#s0: serializer p0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1)
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t0)
  (sq: squash (
    nondep_then_fst'_precond p0 p1 p2
  ))
  requires pts_to_serialized s0 input #pm v
  returns res: slice byte
  ensures exists* v' . pts_to_serialized s1 res #pm v' **
    trade (pts_to_serialized s1 res #pm v') (pts_to_serialized s0 input #pm v) **
    pure (nondep_then_fst'_postcond #t0 #t1 t2 v v')
{
  pts_to_serialized_ext_trade
    s0
    (serialize_nondep_then s1 s2)
    input;
  let v0 : Ghost.erased (t1 & t2) = Ghost.hide (coerce_eq () (Ghost.reveal v));
  let input1, input2 = split_nondep_then s1 j1 s2 input;
  unfold (split_nondep_then_post s1 s2 input pm v (input1, input2));
  unfold (split_nondep_then_post' s1 s2 input pm v input1 input2);
  Trade.elim_hyp_r _ _ _;
  rewrite each (t1 & t2) as t0;
  Trade.trans _ _ (pts_to_serialized s0 input #pm v);
  input1
}

inline_for_extraction
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
  let input1, input2 = split_nondep_then s1 j1 s2 input;
  unfold (split_nondep_then_post s1 s2 input pm v (input1, input2));
  unfold (split_nondep_then_post' s1 s2 input pm v input1 input2);
  Trade.elim_hyp_l _ _ _;
  input2
}

inline_for_extraction
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
  let input1, input2 = split_dtuple2 s1 j1 s2 input;
  unfold (split_dtuple2_post s1 s2 input pm v (input1, input2));
  unfold (split_dtuple2_post' s1 s2 input pm v input1 input2);
  let x1 = leaf_reader_of_reader r1 input1;
  let x2 = leaf_reader_of_reader (r2 x1) input2;
  elim_trade _ _;
  f (|x1, x2|)
}

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
fn compute_remaining_size_dtuple2
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

module S = Pulse.Lib.Slice

inline_for_extraction
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
  with v1 . assert (pts_to out v1);
  fold (vmatch_and_const (vmatch1 (dfst x') (dfst x)) (vmatch2 (dfst x)) (dsnd x') (dsnd x));
  let res2 = w2 (dfst x') (dfst x) (dsnd x') #(dsnd x) out res1;
  with v2 . assert (pts_to out v2);
  Seq.slice_slice v1 0 (SZ.v res1) (SZ.v offset) (SZ.v res1);
  Seq.slice_slice v1 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 0 (SZ.v res1) 0 (SZ.v offset);
  unfold (vmatch_and_const (vmatch1 (dfst x') (dfst x)) (vmatch2 (dfst x)) (dsnd x') (dsnd x));
  fold (vmatch_dep_prod vmatch1 vmatch2);
  res2
}

let vmatch_dep_proj2
  (#tl #th1: Type)
  (#th2: th1 -> Type)
  (vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (xh1: th1)
  (xl: tl)
  (xh2: th2 xh1)
: Tot slprop
= vmatch xl (| xh1, xh2 |)

ghost fn vmatch_dep_proj2_elim_trade
  (#tl #th1: Type0)
  (#th2: th1 -> Type0)
  (vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (xh1: th1)
  (xl: tl)
  (xh2: th2 xh1)
requires vmatch_dep_proj2 vmatch xh1 xl xh2
ensures vmatch xl (| xh1, xh2 |) **
  Trade.trade
    (vmatch xl (| xh1, xh2 |))
    (vmatch_dep_proj2 vmatch xh1 xl xh2)
{
  Trade.rewrite_with_trade
    (vmatch_dep_proj2 vmatch xh1 xl xh2)
    (vmatch xl (| xh1, xh2 |))
}

inline_for_extraction
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
  with v1 . assert (pts_to out v1);
  Trade.rewrite_with_trade 
    (vmatch x' x)
    (vmatch x' (| dfst x, dsnd x |));
  fold (vmatch_dep_proj2 vmatch (dfst x) x' (dsnd x));
  let res2 = w2 (dfst x) x' out res1;
  unfold (vmatch_dep_proj2 vmatch (dfst x) x' (dsnd x));
  Trade.elim _ _;
  with v2 . assert (pts_to out v2);
  Seq.slice_slice v1 0 (SZ.v res1) (SZ.v offset) (SZ.v res1);
  Seq.slice_slice v1 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 0 (SZ.v res1) 0 (SZ.v offset);
  res2
}

inline_for_extraction
fn compute_remaining_size_dtuple2_recip
  (#tl #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (#vmatch1: tl -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: compute_remaining_size vmatch1 s1)
  (phi: (xl: tl) -> (xh: Ghost.erased (dtuple2 th1 th2)) -> stt_ghost unit emp_inames
    (vmatch xl xh)
    (fun _ -> vmatch1 xl (dfst xh) ** trade (vmatch1 xl (dfst xh)) (vmatch xl xh))
  )
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh1: Ghost.erased th1) -> compute_remaining_size (vmatch_dep_proj2 vmatch xh1) (s2 xh1))
: compute_remaining_size #tl #(dtuple2 th1 th2) vmatch #(and_then_kind k1 k2) #(parse_dtuple2 p1 p2) (serialize_dtuple2 s1 s2)
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  serialize_dtuple2_eq s1 s2 x;
  phi x' x;
  let res1 = w1 x' out;
  Trade.elim _ _;
  if (res1) {
    Trade.rewrite_with_trade 
      (vmatch x' x)
      (vmatch x' (| dfst x, dsnd x |));
    fold (vmatch_dep_proj2 vmatch (dfst x) x' (dsnd x));
    let res2 = w2 (dfst x) x' out;
    unfold (vmatch_dep_proj2 vmatch (dfst x) x' (dsnd x));
    Trade.elim _ _;
    res2
  } else {
    false
  }
}

let lemma_seq_append_ijk
  (#t: Type)
  (s: Seq.seq t)
  (i j k: nat)
: Lemma
  (requires (i <= j /\ j <= k /\ k <= Seq.length s))
  (ensures (
    Seq.slice s i k == Seq.append (Seq.slice s i j) (Seq.slice s j k)
  ))
= assert (Seq.equal (Seq.slice s i k) (Seq.append (Seq.slice s i j) (Seq.slice s j k)))

inline_for_extraction
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
  with v1 . assert (pts_to out v1);
  Trade.rewrite_with_trade 
    (vmatch x' x)
    (vmatch x' (| xh1, dsnd x |));
  fold (vmatch_dep_proj2 vmatch xh1 x' (dsnd x));
  let res2 = w2 xh1 x' out res1;
  unfold (vmatch_dep_proj2 vmatch xh1 x' (dsnd x));
  Trade.elim _ _;
  with v2 . assert (pts_to out v2);
  Seq.slice_slice v1 0 (SZ.v res1) (SZ.v offset) (SZ.v res1);
  Seq.slice_slice v1 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 0 (SZ.v res1) 0 (SZ.v offset);
  lemma_seq_append_ijk v2 (SZ.v offset) (SZ.v res1) (SZ.v res2);
  res2
}

inline_for_extraction
fn compute_remaining_size_dtuple2_recip_explicit_header
  (#tl #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: leaf_compute_remaining_size s1)
  (phi: (xl: tl) -> (xh: Ghost.erased (dtuple2 th1 th2)) -> stt th1
    (vmatch xl xh)
    (fun res -> vmatch xl xh ** pure (res == dfst xh))
  )
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh1: th1) -> compute_remaining_size (vmatch_dep_proj2 vmatch xh1) (s2 xh1))
: compute_remaining_size #tl #(dtuple2 th1 th2) vmatch #(and_then_kind k1 k2) #(parse_dtuple2 p1 p2) (serialize_dtuple2 s1 s2)
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  serialize_dtuple2_eq s1 s2 x;
  let xh1 = phi x' x;
  let res1 = w1 xh1 out;
  if (res1) {
    Trade.rewrite_with_trade 
      (vmatch x' x)
      (vmatch x' (| xh1, dsnd x |));
    fold (vmatch_dep_proj2 vmatch xh1 x' (dsnd x));
    let res2 = w2 xh1 x' out;
    unfold (vmatch_dep_proj2 vmatch xh1 x' (dsnd x));
    Trade.elim _ _;
    res2
  } else {
    false
  }
}

inline_for_extraction
fn l2r_leaf_write_dtuple2_phi
  (th1: Type0)
  (th2: (th1 -> Type0))
  (xl: dtuple2 th1 th2)
  (xh: Ghost.erased (dtuple2 th1 th2))
requires
  eq_as_slprop (dtuple2 th1 th2) xl xh
returns res: th1
ensures
  eq_as_slprop (dtuple2 th1 th2) xl xh ** pure (res == dfst xh)
{
  unfold (eq_as_slprop (dtuple2 th1 th2) xl xh);
  fold (eq_as_slprop (dtuple2 th1 th2) xl xh);
  dfst xl
}

ghost
fn l2r_leaf_write_dtuple2_body_lens_aux
  (#th1: Type0)
  (#th2: (th1 -> Tot Type0))
  (xh1: th1)
  (x': dtuple2 th1 th2)
  (x: th2 xh1)
requires
  vmatch_dep_proj2 (eq_as_slprop (dtuple2 th1 th2)) xh1 x' x
returns res: Ghost.erased (th2 xh1)
ensures
  eq_as_slprop (th2 xh1) res x **
  Trade.trade
    (eq_as_slprop (th2 xh1) res x)
    (vmatch_dep_proj2 (eq_as_slprop (dtuple2 th1 th2)) xh1 x' x) **
    pure (
      dfst x' == xh1 /\
      Ghost.reveal res == dsnd x'
    )
{
  unfold (vmatch_dep_proj2 (eq_as_slprop (dtuple2 th1 th2)) xh1 x' x);
  unfold (eq_as_slprop (dtuple2 th1 th2) x' (| xh1, x |));
  let res : Ghost.erased (th2 xh1) = dsnd x';
  fold (eq_as_slprop (th2 xh1) res x);
  intro
    (Trade.trade
      (eq_as_slprop (th2 xh1) res x)
      (vmatch_dep_proj2 (eq_as_slprop (dtuple2 th1 th2)) xh1 x' x)
    )
    #emp
    fn _
  {
    unfold (eq_as_slprop (th2 xh1) res x);
    fold (eq_as_slprop (dtuple2 th1 th2) x' (| xh1, x |));
    fold (vmatch_dep_proj2 (eq_as_slprop (dtuple2 th1 th2)) xh1 x' x);
  };
  res
}

inline_for_extraction
fn l2r_leaf_write_dtuple2_body_lens
  (#th1: Type0)
  (#th2: (th1 -> Tot Type0))
  (xh1: th1)
: vmatch_lens #(dtuple2 th1 th2)
  #(th2 xh1)
  #(th2 xh1)
  (vmatch_dep_proj2 #(dtuple2 th1 th2) #th1 #th2 (eq_as_slprop (dtuple2 th1 th2)) xh1)
  (eq_as_slprop (th2 xh1))
= (x': dtuple2 th1 th2)
  (x: Ghost.erased (th2 xh1))
{
  let _ = l2r_leaf_write_dtuple2_body_lens_aux xh1 x' x;
  with y . rewrite (trade (eq_as_slprop (th2 xh1) y x)
      (vmatch_dep_proj2 (eq_as_slprop (dtuple2 th1 th2)) xh1 x' x) ** eq_as_slprop (th2 xh1) y x)
    as (trade (eq_as_slprop (th2 xh1) (dsnd x') x)
      (vmatch_dep_proj2 (eq_as_slprop (dtuple2 th1 th2)) xh1 x' x) ** eq_as_slprop (th2 xh1) (dsnd x') x);
  dsnd x'
}

inline_for_extraction
let l2r_leaf_write_dtuple2_body
  (#th1: Type0)
  (#th2: (th1 -> Type0))
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh1: th1) -> l2r_leaf_writer (s2 xh1))
  (xh1: th1)
: l2r_writer (vmatch_dep_proj2 (eq_as_slprop (dtuple2 th1 th2)) xh1) (s2 xh1)
= l2r_writer_lens
    (l2r_leaf_write_dtuple2_body_lens #th1 #th2 xh1)
    (l2r_writer_of_leaf_writer (w2 xh1))

inline_for_extraction
let leaf_compute_remaining_size_dtuple2_body
  (#th1: Type0)
  (#th2: (th1 -> Type0))
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh1: th1) -> leaf_compute_remaining_size (s2 xh1))
  (xh1: th1)
: compute_remaining_size (vmatch_dep_proj2 (eq_as_slprop (dtuple2 th1 th2)) xh1) (s2 xh1)
= compute_remaining_size_lens
    (l2r_leaf_write_dtuple2_body_lens #th1 #th2 xh1)
    (compute_remaining_size_of_leaf_compute_remaining_size (w2 xh1))

inline_for_extraction
let l2r_leaf_write_dtuple2
  (#th1: Type0)
  (#th2: (th1 -> Type0))
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: l2r_leaf_writer s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh1: th1) -> l2r_leaf_writer (s2 xh1))
: l2r_leaf_writer (serialize_dtuple2 s1 s2)
= l2r_leaf_writer_of_writer
    (l2r_write_dtuple2_recip_explicit_header
      w1
      (l2r_leaf_write_dtuple2_phi th1 th2)
      sq
      (l2r_leaf_write_dtuple2_body w2)
    )

inline_for_extraction
let leaf_compute_remaining_size_dtuple2
  (#th1: Type0)
  (#th2: (th1 -> Type0))
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (w1: leaf_compute_remaining_size s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh1: th1) -> leaf_compute_remaining_size (s2 xh1))
: leaf_compute_remaining_size (serialize_dtuple2 s1 s2)
= leaf_compute_remaining_size_of_compute_remaining_size
    (compute_remaining_size_dtuple2_recip_explicit_header
      w1
      (l2r_leaf_write_dtuple2_phi th1 th2)
      sq
      (leaf_compute_remaining_size_dtuple2_body w2)
    )

// FIXME: WHY WHY WHY do my Pulse functions with functional types no longer typecheck? WHY WHY WHY do I need to expand the definition of the functional type in Pulse as below? In most cases this will be awfully painful!
inline_for_extraction
fn zero_copy_parse_dtuple2'
  (#tl1 #tl2 #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (j1: jumper p1)
  (w1: zero_copy_parse vmatch1 s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#vmatch2: (x: th1) -> tl2 -> th2 x -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh: Ghost.erased th1) -> zero_copy_parse (vmatch2 xh) (s2 xh))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 th1 th2))
requires
  pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v
returns res: (tl1 `cpair` tl2)
ensures
  vmatch_dep_prod vmatch1 vmatch2 res v **
  Trade.trade
    (vmatch_dep_prod vmatch1 vmatch2 res v)
    (pts_to_serialized (serialize_dtuple2 s1 s2) input #pm v)
{
  let (input1, input2) = split_dtuple2 s1 j1 s2 input;
  unfold (split_dtuple2_post s1 s2 input pm v (input1, input2));
  unfold (split_dtuple2_post' s1 s2 input pm v input1 input2);
  let res1 = w1 input1;
  with v1 . assert (vmatch1 res1 v1);
  Trade.trans_hyp_l (vmatch1 res1 _) _ _ _;
  let res2 = w2 v1 input2;
  Trade.trans_hyp_r _ (vmatch2 v1 res2 _) _ _;
  let res : cpair tl1 tl2 = (| res1, res2 |);
  Trade.rewrite_with_trade
    (vmatch1 res1 v1 ** vmatch2 v1 res2 _)
    (vmatch_dep_prod vmatch1 vmatch2 res v);
  Trade.trans (vmatch_dep_prod vmatch1 vmatch2 res v) _ _;
  res
}

inline_for_extraction
let zero_copy_parse_dtuple2
  (#tl1 #tl2 #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (j1: jumper p1)
  (w1: zero_copy_parse vmatch1 s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#vmatch2: (x: th1) -> tl2 -> th2 x -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh: Ghost.erased th1) -> zero_copy_parse (vmatch2 xh) (s2 xh))
: zero_copy_parse #(tl1 `cpair` tl2) #(dtuple2 th1 th2) (vmatch_dep_prod vmatch1 vmatch2) #(and_then_kind k1 k2) #(parse_dtuple2 p1 p2) (serialize_dtuple2 s1 s2)
= zero_copy_parse_dtuple2' j1 w1 sq w2

inline_for_extraction
fn read_and_zero_copy_parse_dtuple2
  (#tl #th1: Type)
  (#th2: th1 -> Type)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (j1: jumper p1)
  (w1: leaf_reader s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (#s2: (x: th1) -> serializer (p2 x))
  (w2: (xh: th1) -> zero_copy_parse (vmatch_dep_proj2 vmatch xh) (s2 xh))
: zero_copy_parse #tl #(dtuple2 th1 th2) vmatch #(and_then_kind k1 k2) #(parse_dtuple2 p1 p2) (serialize_dtuple2 s1 s2)
= (input: _)
  (#pm: _)
  (#v: _)
{
  let (input1, input2) = split_dtuple2 s1 j1 s2 input;
  unfold (split_dtuple2_post s1 s2 input pm v (input1, input2));
  unfold (split_dtuple2_post' s1 s2 input pm v input1 input2);
  let v1 = w1 input1;
  Trade.elim_hyp_l _ _ _;
  let res = w2 v1 input2;
  rewrite each (dfst v) as v1;
  Trade.trans (vmatch_dep_proj2 vmatch v1 res _) _ _;
  Trade.rewrite_with_trade
    (vmatch_dep_proj2 vmatch v1 res _)
    (vmatch res v);
  Trade.trans (vmatch res v) _ _;
  res
}

inline_for_extraction
fn compute_remaining_size_nondep_then
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

inline_for_extraction
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
  with v1 . assert (pts_to out v1);
  Trade.elim _ _;
  let x2 = f2 x' x;
  let res2 = w2 x2 #(Ghost.hide (snd x)) out res1;
  with v2 . assert (pts_to out v2);
  Seq.slice_slice v1 0 (SZ.v res1) (SZ.v offset) (SZ.v res1);
  Seq.slice_slice v1 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v res2) 0 (SZ.v res1 - SZ.v offset);
  Seq.slice_slice v2 0 (SZ.v res1) 0 (SZ.v offset);
  Trade.elim _ _;
  res2
}

let vmatch_pair
  (#tl1 #tl2 #th1 #th2: Type0)
  (vmatch1: tl1 -> th1 -> slprop)
  (vmatch2: tl2 -> th2 -> slprop)
  (xl: (tl1 & tl2))
  (xh: (th1 & th2))
: Tot slprop
= vmatch1 (fst xl) (fst xh) ** vmatch2 (snd xl) (snd xh)

inline_for_extraction
fn l2r_write_nondep_then_direct_proj1
  (#tl1 #tl2 #th1 #th2: Type0)
  (vmatch1: tl1 -> th1 -> slprop)
  (vmatch2: tl2 -> th2 -> slprop)
  (xl: (tl1 & tl2))
  (xh: erased (th1 & th2))
requires
      (vmatch_pair vmatch1 vmatch2 xl xh)
returns xl1: tl1
ensures
  vmatch1 xl1 (fst xh) ** trade (vmatch1 xl1 (fst xh)) (vmatch_pair vmatch1 vmatch2 xl xh)
{
  norewrite let (res, _) = xl;
  Trade.rewrite_with_trade
    (vmatch_pair vmatch1 vmatch2 xl xh)
    (vmatch1 res (fst xh) ** vmatch2 (snd xl) (snd xh));
  Trade.elim_hyp_r _ _ _;
  res
}

inline_for_extraction
fn l2r_write_nondep_then_direct_proj2
  (#tl1 #tl2 #th1 #th2: Type0)
  (vmatch1: tl1 -> th1 -> slprop)
  (vmatch2: tl2 -> th2 -> slprop)
  (xl: (tl1 & tl2))
  (xh: erased (th1 & th2))
requires
  (vmatch_pair vmatch1 vmatch2 xl xh)
returns xl2: tl2
ensures
  vmatch2 xl2 (snd xh) ** trade (vmatch2 xl2 (snd xh)) (vmatch_pair vmatch1 vmatch2 xl xh)
{
  norewrite let (_, res) = xl;
  Trade.rewrite_with_trade
    (vmatch_pair vmatch1 vmatch2 xl xh)
    (vmatch1 (fst xl) (fst xh) ** vmatch2 res (snd xh));
  Trade.elim_hyp_l _ _ _;
  res
}

inline_for_extraction
let l2r_write_nondep_then_direct
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
: l2r_writer #_ #(th1 & th2) (vmatch_pair vmatch1 vmatch2) #(and_then_kind k1 k2) #(nondep_then p1 p2) (serialize_nondep_then s1 s2)
= l2r_write_nondep_then
    w1
    sq
    w2
    _
    (l2r_write_nondep_then_direct_proj1 vmatch1 vmatch2)
    (l2r_write_nondep_then_direct_proj2 vmatch1 vmatch2)

inline_for_extraction
fn zero_copy_parse_nondep_then
  (#tl1 #tl2 #th1 #th2: Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#s1: serializer p1)
  (j1: jumper p1)
  (w1: zero_copy_parse vmatch1 s1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#vmatch2: tl2 -> th2 -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 th2)
  (#s2: serializer p2)
  (w2: zero_copy_parse vmatch2 s2)
: zero_copy_parse #_ #(th1 & th2) (vmatch_pair vmatch1 vmatch2) #(and_then_kind k1 k2) #(nondep_then p1 p2) (serialize_nondep_then s1 s2)
= (input: _)
  (#pm: _)
  (#v: _)
{
  let (input1, input2) = split_nondep_then s1 j1 s2 input;
  unfold (split_nondep_then_post s1 s2 input pm v (input1, input2));
  unfold (split_nondep_then_post' s1 s2 input pm v input1 input2);
  let res1 = w1 input1;
  Trade.trans_hyp_l (vmatch1 res1 _) _ _ _;
  let res2 = w2 input2;
  Trade.trans_hyp_r _ (vmatch2 res2 _) _ _;
  Trade.rewrite_with_trade
    (vmatch1 res1 _ ** vmatch2 res2 _)
    (vmatch_pair vmatch1 vmatch2 (res1, res2) v);
  Trade.trans (vmatch_pair vmatch1 vmatch2 (res1, res2) v) (vmatch1 res1 (fst v) ** vmatch2 res2 (snd v)) _;
  (res1, res2)
}

inline_for_extraction
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

inline_for_extraction
fn leaf_compute_remaining_size_synth
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (w: leaf_compute_remaining_size s1)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
  (f1': ((x2: t2) -> (x1: t1 { x1 == f1 x2 })))
: leaf_compute_remaining_size #t2 #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
=
  (x: _)
  (out: _)
  (#v: _)
{
  serialize_synth_eq p1 f2 s1 f1 () x;
  w (f1' x) out
}

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

inline_for_extraction
let leaf_compute_remaining_size_synth'
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (w: leaf_compute_remaining_size s1)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> Tot t1) { synth_inverse f2 f1 })
: leaf_compute_remaining_size #t2 #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= leaf_compute_remaining_size_synth w f2 f1 (mk_synth f1)

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
fn compute_remaining_size_synth
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

inline_for_extraction
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

inline_for_extraction
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

inline_for_extraction
fn zero_copy_parse_synth
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (#tl: Type0) (#vmatch: tl -> t1 -> slprop) (r: zero_copy_parse vmatch s1)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
: zero_copy_parse #_ #_ (vmatch_synth vmatch f1) #_ #_ (serialize_synth p1 f2 s1 f1 ())
= (input: slice byte)
  (#pm: _)
  (#v: _)
{
  pts_to_serialized_synth_l2r_trade s1 f2 f1 input;
  let res = r input;
  Trade.trans (vmatch res (f1 v)) _ _;
  Trade.rewrite_with_trade
    (vmatch res (f1 v))
    (vmatch_synth vmatch f1 res v);
  Trade.trans (vmatch_synth vmatch f1 res v) (vmatch res (f1 v)) _;
  res
}

inline_for_extraction
fn zero_copy_parse_synth_recip
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#s1: serializer p1) (#tl: Type0)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
  (#vmatch2: tl -> t2 -> slprop) (r: zero_copy_parse (vmatch_synth vmatch2 f2) s1)
: zero_copy_parse #_ #_ vmatch2 #_ #_ (serialize_synth p1 f2 s1 f1 ())
= (input: slice byte)
  (#pm: _)
  (#v: _)
{
  pts_to_serialized_synth_l2r_trade s1 f2 f1 input;
  let res = r input;
  Trade.trans (vmatch_synth vmatch2 f2 res (f1 v)) _ _;
  Trade.rewrite_with_trade
    (vmatch_synth vmatch2 f2 res (f1 v))
    (vmatch2 res v);
  Trade.trans (vmatch2 res v) _ _;
  res
}

inline_for_extraction
fn compute_remaining_size_synth_recip
  (#t: Type0) (#t1: Type0) (#t2: Type0)
  (vmatch: t -> t2 -> slprop)
  (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: compute_remaining_size (vmatch_synth vmatch f2) s1)
: compute_remaining_size #t #t2 vmatch #k1 #(parse_synth p1 f2) (serialize_synth p1 f2 s1 f1 ())
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  serialize_synth_eq p1 f2 s1 f1 () x;
  Trade.rewrite_with_trade
    (vmatch x' x)
    (vmatch x' (f2 (f1 x)));
  fold (vmatch_synth vmatch f2 x' (f1 x));
  let res = w x' out;
  unfold (vmatch_synth vmatch f2 x' (f1 x));
  Trade.elim _ _;
  res
}

let vmatch_filter
  (#tl: Type0)
  (#th: Type0)
  (vmatch: tl -> th -> slprop)
  (f: th -> GTot bool)
: Tot (tl -> parse_filter_refine f -> slprop)
= vmatch


#set-options "--print_universes --print_implicits"

inline_for_extraction
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

inline_for_extraction
fn leaf_compute_remaining_size_filter
  (#t1: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: leaf_compute_remaining_size #t1 s1)
  (f: (t1 -> GTot bool))
: leaf_compute_remaining_size #(parse_filter_refine u#0 f) #(parse_filter_kind k1) #(parse_filter p1 f) (serialize_filter s1 f)
= (x: _)
  (out: _)
  (#v: _)
{
  w x out
}

inline_for_extraction
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

inline_for_extraction
fn compute_remaining_size_filter
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

inline_for_extraction
fn zero_copy_parse_filter
  (#t: Type0) (#t1: Type0)
  (vmatch: t -> t1 -> slprop)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1) (w: zero_copy_parse #t #t1 vmatch s1)
  (f: (t1 -> GTot bool))
: zero_copy_parse #t #(parse_filter_refine u#0 f) (vmatch_filter vmatch f) #(parse_filter_kind k1) #(parse_filter p1 f) (serialize_filter s1 f)
= (input: _)
  (#pm: _)
  (#v: _)
{
  pts_to_serialized_filter_elim_trade s1 f input;
  let res = w input;
  with v' . assert (vmatch res v');
  Trade.trans (vmatch res v') _ _;
  Trade.rewrite_with_trade
    (vmatch res v')
    (vmatch_filter vmatch f res v);
  Trade.trans _ (vmatch res v') _;
  res
}

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

inline_for_extraction
fn compute_remaining_size_filter_recip
  (#t: Type0) (#t1: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1)
  (f: (t1 -> GTot bool))
  (vmatch: t -> parse_filter_refine f -> slprop)
  (w: compute_remaining_size (vmatch_filter_recip f vmatch) s1)
: compute_remaining_size #t #(parse_filter_refine u#0 f) vmatch #(parse_filter_kind k1) #(parse_filter p1 f) (serialize_filter s1 f)
= (x': _)
  (#x: _)
  (out: _)
  (#v: _)
{
  fold (vmatch_filter_recip f vmatch x' x);
  let res = w x' #(Ghost.hide (Ghost.reveal x)) out;
  unfold (vmatch_filter_recip f vmatch x' x);
  with xh . assert (vmatch x' xh);
  rewrite (vmatch x' xh) as (vmatch x' x);
  res
}

inline_for_extraction
fn zero_copy_parse_filter_recip
  (#t: Type0) (#t1: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (#s1: serializer p1)
  (f: (t1 -> GTot bool))
  (vmatch: t -> parse_filter_refine f -> slprop)
  (w: zero_copy_parse (vmatch_filter_recip f vmatch) s1)
: zero_copy_parse #t #(parse_filter_refine u#0 f) vmatch #(parse_filter_kind k1) #(parse_filter p1 f) (serialize_filter s1 f)
= (input: _)
  (#pm: _)
  (#v: _)
{
  pts_to_serialized_filter_elim_trade s1 f input;
  let res = w input;
  with v' . assert (vmatch_filter_recip f vmatch res v');
  Trade.trans (vmatch_filter_recip f vmatch res v') _ _;
  unfold (vmatch_filter_recip f vmatch res v');
  with v'' . assert (vmatch res v'');
  rewrite (vmatch res v'') as (vmatch res v);
  intro
    (Trade.trade
      (vmatch res v)
      (vmatch_filter_recip f vmatch res v')
    )
    #emp
    fn _
  {
    fold (vmatch_filter_recip f vmatch res v')
  };
  Trade.trans (vmatch res v) _ _;
  res
}

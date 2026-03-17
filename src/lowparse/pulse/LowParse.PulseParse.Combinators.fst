module LowParse.PulseParse.Combinators
#lang-pulse
include LowParse.Spec.Combinators
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base

(* ret / empty *)

inline_for_extraction
fn leaf_read_ret
  (#t: Type0)
  (x: t)
  (v_unique: (v' : t) -> Lemma (x == v'))
: PPB.leaf_reader #t #parse_ret_kind (parse_ret x)
= (input: slice byte)
  (#pm: _)
  (#v: _)
{
  v_unique v;
  x
}

inline_for_extraction
let read_ret
  (#t: Type0)
  (x: t)
  (v_unique: (v' : t) -> Lemma (x == v'))
: Tot (PPB.reader (parse_ret x))
= PPB.reader_of_leaf_reader (leaf_read_ret x v_unique)

inline_for_extraction
let leaf_read_empty : PPB.leaf_reader parse_empty = leaf_read_ret () (fun _ -> ())

inline_for_extraction
let read_empty : PPB.reader parse_empty = PPB.reader_of_leaf_reader leaf_read_empty

(* pts_to_parsed synth combinators *)

ghost
fn pts_to_parsed_synth_intro
  (#t #t': Type0)
  (#k: parser_kind)
  (p: parser k t)
  (f: (t -> GTot t') { k.parser_kind_injective ==> synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires PPB.pts_to_parsed p input #pm v
  ensures PPB.pts_to_parsed (parse_synth p f) input #pm (f v)
{
  unfold (PPB.pts_to_parsed p input #pm v);
  with w . assert (pts_to input #pm w);
  parse_synth_eq p f w;
  fold (PPB.pts_to_parsed (parse_synth p f) input #pm (f v))
}

ghost
fn pts_to_parsed_synth_elim
  (#t #t': Type0)
  (#k: parser_kind)
  (p: parser k t)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (v: t)
  requires PPB.pts_to_parsed (parse_synth p f) input #pm (f v)
  ensures PPB.pts_to_parsed p input #pm v
{
  unfold (PPB.pts_to_parsed (parse_synth p f) input #pm (f v));
  with w . assert (pts_to input #pm w);
  parse_synth_eq p f w;
  fold (PPB.pts_to_parsed p input #pm v)
}

ghost
fn pts_to_parsed_synth_trade
  (#t #t': Type0)
  (#k: parser_kind)
  (p: parser k t)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires PPB.pts_to_parsed p input #pm v
  ensures PPB.pts_to_parsed (parse_synth p f) input #pm (f v) **
    trade (PPB.pts_to_parsed (parse_synth p f) input #pm (f v))
          (PPB.pts_to_parsed p input #pm v)
{
  pts_to_parsed_synth_intro p f f' input;
  intro
    (Trade.trade
      (PPB.pts_to_parsed (parse_synth p f) input #pm (f v))
      (PPB.pts_to_parsed p input #pm v)
    )
    #emp
    fn _ {
      pts_to_parsed_synth_elim p f f' input v
    };
}

ghost
fn pts_to_parsed_synth_l2r
  (#t #t': Type0)
  (#k: parser_kind)
  (p: parser k t)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t')
  requires PPB.pts_to_parsed (parse_synth p f) input #pm v
  ensures PPB.pts_to_parsed p input #pm (f' v)
{
  unfold (PPB.pts_to_parsed (parse_synth p f) input #pm v);
  with w . assert (pts_to input #pm w);
  parse_synth_eq p f w;
  let v1 = Ghost.hide (fst (Some?.v (parse p w)));
  assert pure (f v1 == v);
  assert pure (f (f' v) == v);
  fold (PPB.pts_to_parsed p input #pm (f' v))
}

ghost
fn pts_to_parsed_synth_r2l
  (#t #t': Type0)
  (#k: parser_kind)
  (p: parser k t)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (v: t')
  requires PPB.pts_to_parsed p input #pm (f' v)
  ensures PPB.pts_to_parsed (parse_synth p f) input #pm v
{
  unfold (PPB.pts_to_parsed p input #pm (f' v));
  with w . assert (pts_to input #pm w);
  parse_synth_eq p f w;
  fold (PPB.pts_to_parsed (parse_synth p f) input #pm v)
}

ghost
fn pts_to_parsed_synth_l2r_trade
  (#t #t': Type0)
  (#k: parser_kind)
  (p: parser k t)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t')
  requires PPB.pts_to_parsed (parse_synth p f) input #pm v
  ensures PPB.pts_to_parsed p input #pm (f' v) **
    trade (PPB.pts_to_parsed p input #pm (f' v))
          (PPB.pts_to_parsed (parse_synth p f) input #pm v)
{
  pts_to_parsed_synth_l2r p f f' input;
  intro
    (Trade.trade
      (PPB.pts_to_parsed p input #pm (f' v))
      (PPB.pts_to_parsed (parse_synth p f) input #pm v)
    )
    #emp
    fn _ {
      pts_to_parsed_synth_r2l p f f' input v
    };
}

(* pts_to_parsed filter combinators *)

ghost
fn pts_to_parsed_filter_intro
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (f: (t -> GTot bool))
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires PPB.pts_to_parsed p input #pm v ** pure (f v == true)
  ensures exists* (v': parse_filter_refine f) .
    PPB.pts_to_parsed (parse_filter p f) input #pm v' ** pure ((v' <: t) == v)
{
  unfold (PPB.pts_to_parsed p input #pm v);
  with w . assert (pts_to input #pm w);
  parse_filter_eq p f w;
  fold (PPB.pts_to_parsed (parse_filter p f) input #pm (v <: parse_filter_refine f))
}

ghost
fn pts_to_parsed_filter_elim
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (f: (t -> GTot bool))
  (input: slice byte)
  (#pm: perm)
  (#v: parse_filter_refine f)
  requires PPB.pts_to_parsed (parse_filter p f) input #pm v
  ensures PPB.pts_to_parsed p input #pm v
{
  unfold (PPB.pts_to_parsed (parse_filter p f) input #pm v);
  with w . assert (pts_to input #pm w);
  parse_filter_eq p f w;
  fold (PPB.pts_to_parsed p input #pm (v <: t))
}

ghost
fn pts_to_parsed_filter_elim_trade
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (f: (t -> GTot bool))
  (input: slice byte)
  (#pm: perm)
  (#v: parse_filter_refine f)
  requires PPB.pts_to_parsed (parse_filter p f) input #pm v
  ensures exists* (v': t) .
    PPB.pts_to_parsed p input #pm v' **
    Trade.trade (PPB.pts_to_parsed p input #pm v')
                (PPB.pts_to_parsed (parse_filter p f) input #pm v) **
    pure (v' == (v <: t))
{
  pts_to_parsed_filter_elim p f input;
  intro
    (Trade.trade
      (PPB.pts_to_parsed p input #pm (v <: t))
      (PPB.pts_to_parsed (parse_filter p f) input #pm v)
    )
    #emp
    fn _ {
      pts_to_parsed_filter_intro p f input
    };
}

(* read combinators *)

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
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (r: PPB.reader p1)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 })
  (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
  (f2': ((x: t1) -> read_synth_cont_t (f2 x)))
: PPB.reader #t2 #k1 (parse_synth p1 f2)
= (input: slice byte)
  (#pm: _)
  (#v: _)
  (t': Type0)
  (g: _)
{
  pts_to_parsed_synth_l2r_trade p1 f2 f1 input;
  let res = r input #pm #(f1 v) t' (read_synth_cont f2 f2' (f1 v) t' g);
  Trade.elim _ _;
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
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (r: PPB.reader p1)
  (#t2: Type0) (f2: (t1 -> Tot t2) { synth_injective f2 })
  (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
: PPB.reader #t2 #k1 (parse_synth p1 f2)
= read_synth r f2 f1 (fun x -> read_synth_cont_init (f2 x))

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
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (r: PPB.reader p1)
  (f: (t1 -> GTot bool))
: PPB.reader #(parse_filter_refine f) #(parse_filter_kind k1) (parse_filter p1 f)
= (input: slice byte)
  (#pm: _)
  (#v: _)
  (t': Type0)
  (g: _)
{
  pts_to_parsed_filter_elim p1 f input;
  let res = r input #pm #(Ghost.hide (Ghost.reveal v)) t' (read_filter_cont f v t' g);
  pts_to_parsed_filter_intro p1 f input;
  res
}

(* validate combinators *)

inline_for_extraction
fn validate_filter
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: LPS.validator p)
  (r: PPB.leaf_reader p)
  (f: (t -> GTot bool))
  (f': (x: t) -> (y: bool { y == f x }))
  (_: squash (k.parser_kind_subkind == Some ParserStrong))
: LPS.validator #_ #(parse_filter_kind k) (parse_filter p f)
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
    let x = PPB.read_parsed_from_validator_success r input offset off;
    f' x
  } else {
    false
  }
}

inline_for_extraction
let validate_filter'
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: LPS.validator p)
  (r: PPB.leaf_reader p)
  (f: (t -> bool))
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
: LPS.validator #_ #(parse_filter_kind k) (parse_filter p f)
= validate_filter w r f (fun x -> f x) sq

inline_for_extraction
fn validate_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (v1: LPS.validator p1)
  (r1: PPB.leaf_reader p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: ((x: t1) -> parser k2 (t2 x)))
  (v2: ((x: t1) -> LPS.validator (p2 x)))
  (_: squash (k1.parser_kind_subkind == Some ParserStrong))
: LPS.validator #(dtuple2 t1 t2) #(and_then_kind k1 k2) (parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2)
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
    let x = PPB.read_parsed_from_validator_success r1 input offset off;
    v2 x input poffset
  } else {
    false
  }
}

inline_for_extraction
fn jump_dtuple2
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (v1: LPS.jumper p1)
  (r1: PPB.leaf_reader p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (v2: (x: t1) -> LPS.jumper (p2 x))
  (_: squash (k1.parser_kind_subkind == Some ParserStrong))
: LPS.jumper #(dtuple2 t1 t2) #(and_then_kind k1 k2) (parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parse_dtuple2_eq p1 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  pts_to_len input;
  let off1 = v1 input offset;
  let x = PPB.read_parsed_from_validator_success r1 input offset off1;
  v2 x input off1
}

(* validate_false: always fails *)

inline_for_extraction
fn validate_false ()
: LPS.validator #_ #parse_false_kind parse_false
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  false
}

(* validate_strengthen: strengthen the parser kind *)

inline_for_extraction
let validate_strengthen
  (k2: parser_kind)
  (#k1: Ghost.erased parser_kind)
  (#t: Type0)
  (#p1: parser k1 t)
  (v1: LPS.validator p1)
  (sq: squash (parser_kind_prop k2 p1))
: LPS.validator (strengthen k2 p1)
= LPS.validate_ext v1 (strengthen k2 p1)

(* validate_lift_parser: lift a thunked parser *)

inline_for_extraction
let validate_lift_parser
  (#k: parser_kind)
  (#t: Type0)
  (p: unit -> GTot (parser k t))
  (v: LPS.validator #t #k (p ()))
: LPS.validator #t #k (lift_parser p)
= LPS.validate_ext v (lift_parser p)

(* validate_filter_ret: filter on parse_ret, no reader needed *)

inline_for_extraction
fn validate_filter_ret
  (#t: Type0)
  (r: t)
  (f: (t -> GTot bool))
  (f': (x: t) -> (y: bool { y == f x }))
: LPS.validator (parse_filter (parse_ret r) f)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parse_filter_eq (parse_ret r) f (Seq.slice v (SZ.v offset) (Seq.length v));
  f' r
}

(* validate_filter_and_then: validate filter then dependent parsing *)

inline_for_extraction
fn validate_filter_and_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (v1: LPS.validator p1)
  (r1: PPB.leaf_reader p1)
  (f: (t1 -> GTot bool))
  (f': (x: t1) -> (y: bool { y == f x }))
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: ((x: t1 { f x == true }) -> parser k2 t2))
  (v2: ((x: t1 { f x == true }) -> LPS.validator (p2 x)))
  (u: squash (
    k1.parser_kind_subkind == Some ParserStrong /\
    ((and_then_kind (parse_filter_kind k1) k2).parser_kind_injective ==> and_then_cases_injective p2)
  ))
: LPS.validator #_ #(and_then_kind (parse_filter_kind k1) k2) (parse_filter p1 f `and_then` p2)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  and_then_eq (parse_filter p1 f) p2 sinput;
  parse_filter_eq p1 f sinput;
  let offset = !poffset;
  let is_valid = v1 input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r1 input offset off;
    if f' x {
      v2 x input poffset
    } else {
      false
    }
  } else {
    false
  }
}

(* validate_synth: validate a parser composed with a synthesis function *)

inline_for_extraction
fn validate_synth
  (#t #t': Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: LPS.validator p)
  (f: (t -> GTot t') { synth_injective f })
: LPS.validator #t' #k (parse_synth p f)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  parse_synth_eq p f (Seq.slice v (SZ.v offset) (Seq.length v));
  w input poffset #offset #pm #v
}

(* validate_nondep_then: validate two independent parsers in sequence *)

inline_for_extraction
fn validate_nondep_then
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (v1: LPS.validator p1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (v2: LPS.validator p2)
: LPS.validator #(t1 & t2) #(and_then_kind k1 k2) (nondep_then #k1 #t1 p1 #k2 #t2 p2)
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

(* validate_compose_context: change the key type indexing a parser family *)

inline_for_extraction
let validate_compose_context
  (#pk: parser_kind)
  (#kt1 #kt2: Type0)
  (f: (kt2 -> Tot kt1))
  (t: (kt1 -> Tot Type0))
  (p: ((k: kt1) -> Tot (parser pk (t k))))
  (v: ((k: kt1) -> Tot (LPS.validator (p k))))
  (k: kt2)
: Tot (LPS.validator (p (f k)))
= v (f k)

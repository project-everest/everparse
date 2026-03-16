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

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
include LowParse.CLens

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
  (#k: Ghost.erased parser_kind)
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
  (#k: Ghost.erased parser_kind)
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
  (#k: Ghost.erased parser_kind)
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
  (#k: Ghost.erased parser_kind)
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
  (#k: Ghost.erased parser_kind)
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
  (#k: Ghost.erased parser_kind)
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
  (#k: Ghost.erased parser_kind)
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
  (#k: Ghost.erased parser_kind)
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
  (#k: Ghost.erased parser_kind)
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

inline_for_extraction
fn read_false ()
: PPB.leaf_reader #_ #parse_false_kind parse_false
=
  (input: slice byte)
  (#pm: _)
  (#v: Ghost.erased (squash False))
{
  let _ = Ghost.reveal v;
  ()
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
  (#k: Ghost.erased parser_kind)
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
  (#k1: Ghost.erased parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (v1: LPS.validator p1)
  (r1: PPB.leaf_reader p1)
  (f: (t1 -> GTot bool))
  (f': (x: t1) -> (y: bool { y == f x }))
  (#k2: Ghost.erased parser_kind)
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

(* split_nondep_then: split a pts_to_parsed for nondep_then into two sub-slices *)

let split_nondep_then_post
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (p2: parser k2 t2)
  (input: slice byte) (pm: perm) (v: Ghost.erased (t1 & t2))
  (res: (slice byte & slice byte))
: slprop
= PPB.pts_to_parsed p1 (fst res) #(pm /. 2.0R) (fst v) **
  PPB.pts_to_parsed p2 (snd res) #(pm /. 2.0R) (snd v) **
  Trade.trade
    (PPB.pts_to_parsed p1 (fst res) #(pm /. 2.0R) (fst v) **
     PPB.pts_to_parsed p2 (snd res) #(pm /. 2.0R) (snd v))
    (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v)

inline_for_extraction
fn split_nondep_then
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (j1: LPS.jumper p1)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  requires PPB.pts_to_parsed (nondep_then p1 p2) input #pm v
  returns res: (slice byte & slice byte)
  ensures split_nondep_then_post p1 p2 input pm v res
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  let gv1 = Ghost.hide (fst (Ghost.reveal v));
  let gv2 = Ghost.hide (snd (Ghost.reveal v));
  PPB.pts_to_parsed_intro p1 input1 gv1;
  PPB.pts_to_parsed_intro p2 input2 gv2;
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1 ** PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  fold (split_nondep_then_post p1 p2 input pm v (input1, input2));
  (input1, input2)
}

(* leaf_read_nondep_then: read a non-dependent pair using split *)

inline_for_extraction
fn leaf_read_nondep_then
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (r1: PPB.leaf_reader p1)
  (j1: LPS.jumper p1)
  (r2: PPB.leaf_reader p2)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
: PPB.leaf_reader #(t1 & t2) #(and_then_kind k1 k2) (nondep_then p1 p2)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  let gv1 = Ghost.hide (fst (Ghost.reveal v));
  let gv2 = Ghost.hide (snd (Ghost.reveal v));
  PPB.pts_to_parsed_intro p1 input1 gv1;
  PPB.pts_to_parsed_intro p2 input2 gv2;
  let a = r1 input1;
  let b = r2 input2;
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input2 #pm wb2);
  Trade.elim
    (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1 ** PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2)
    (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2);
  Trade.elim
    (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2)
    (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  (a, b)
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

inline_for_extraction
let jump_compose_context
  (#pk: parser_kind)
  (#kt1 #kt2: Type0)
  (f: (kt2 -> Tot kt1))
  (t: (kt1 -> Tot Type0))
  (p: ((k: kt1) -> Tot (parser pk (t k))))
  (j: ((k: kt1) -> Tot (LPS.jumper (p k))))
  (k: kt2)
: Tot (LPS.jumper (p (f k)))
= j (f k)

(* zero_copy_parse combinators *)

inline_for_extraction
fn zero_copy_parse_synth
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#tl: Type0) (#vmatch: tl -> t1 -> slprop) (r: PPB.zero_copy_parse vmatch p1)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
: PPB.zero_copy_parse #_ #_ (LPC.vmatch_synth vmatch f1) #_ (parse_synth p1 f2)
= (input: slice byte)
  (#pm: _)
  (#v: _)
{
  pts_to_parsed_synth_l2r_trade p1 f2 f1 input;
  let res = r input;
  Trade.trans (vmatch res (f1 v)) _ _;
  Trade.rewrite_with_trade
    (vmatch res (f1 v))
    (LPC.vmatch_synth vmatch f1 res v);
  Trade.trans (LPC.vmatch_synth vmatch f1 res v) (vmatch res (f1 v)) _;
  res
}

inline_for_extraction
fn zero_copy_parse_filter
  (#t: Type0) (#t1: Type0)
  (vmatch: t -> t1 -> slprop)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (w: PPB.zero_copy_parse #t #t1 vmatch p1)
  (f: (t1 -> GTot bool))
: PPB.zero_copy_parse #t #(parse_filter_refine u#0 f) (LPC.vmatch_filter vmatch f) #(parse_filter_kind k1) (parse_filter p1 f)
= (input: _)
  (#pm: _)
  (#v: _)
{
  pts_to_parsed_filter_elim_trade p1 f input;
  let res = w input;
  with v' . assert (vmatch res v');
  Trade.trans (vmatch res v') _ _;
  Trade.rewrite_with_trade
    (vmatch res v')
    (LPC.vmatch_filter vmatch f res v);
  Trade.trans _ (vmatch res v') _;
  res
}

inline_for_extraction
fn zero_copy_parse_nondep_then
  (#tl1 #tl2 #th1 #th2: Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#vmatch2: tl2 -> th2 -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 th2)
  (j1: LPS.jumper p1)
  (w1: PPB.zero_copy_parse vmatch1 p1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (w2: PPB.zero_copy_parse vmatch2 p2)
: PPB.zero_copy_parse #_ #(th1 & th2) (LPC.vmatch_pair vmatch1 vmatch2) #(and_then_kind k1 k2) (nondep_then p1 p2)
= (input: _)
  (#pm: _)
  (#v: _)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  nondep_then_eq #k1 #th1 p1 #k2 #th2 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  let gv1 = Ghost.hide (fst (Ghost.reveal v));
  let gv2 = Ghost.hide (snd (Ghost.reveal v));
  PPB.pts_to_parsed_intro p1 input1 gv1;
  PPB.pts_to_parsed_intro p2 input2 gv2;
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1 ** PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  let res1 = w1 input1;
  Trade.trans_hyp_l (vmatch1 res1 _) _ _ _;
  let res2 = w2 input2;
  Trade.trans_hyp_r _ (vmatch2 res2 _) _ _;
  Trade.rewrite_with_trade
    (vmatch1 res1 _ ** vmatch2 res2 _)
    (LPC.vmatch_pair vmatch1 vmatch2 (res1, res2) v);
  Trade.trans (LPC.vmatch_pair vmatch1 vmatch2 (res1, res2) v) _ _;
  (res1, res2)
}

inline_for_extraction
fn zero_copy_parse_dtuple2
  (#tl1 #tl2 #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#vmatch2: (x: th1) -> tl2 -> th2 x -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (j1: LPS.jumper p1)
  (w1: PPB.zero_copy_parse vmatch1 p1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (w2: (xh: Ghost.erased th1) -> PPB.zero_copy_parse (vmatch2 xh) (p2 xh))
: PPB.zero_copy_parse #(LPC.cpair tl1 tl2) #(dtuple2 th1 th2) (LPC.vmatch_dep_prod vmatch1 vmatch2) #(and_then_kind k1 k2) (parse_dtuple2 p1 p2)
= (input: _)
  (#pm: _)
  (#v: _)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_dtuple2_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed (parse_dtuple2 p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  let gdv1 = Ghost.hide (dfst (Ghost.reveal v));
  let gdv2 = Ghost.hide (dsnd (Ghost.reveal v));
  PPB.pts_to_parsed_intro p1 input1 gdv1;
  PPB.pts_to_parsed_intro (p2 gdv1) input2 gdv2;
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gdv1) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed (p2 gdv1) input2 #(pm /. 2.0R) gdv2) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gdv1 ** PPB.pts_to_parsed (p2 gdv1) input2 #(pm /. 2.0R) gdv2) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed (parse_dtuple2 p1 p2) input #pm v);
  let res1 = w1 input1;
  with v1 . assert (vmatch1 res1 v1);
  Trade.trans_hyp_l (vmatch1 res1 _) _ _ _;
  let res2 = w2 v1 input2;
  Trade.trans_hyp_r _ (vmatch2 v1 res2 _) _ _;
  let res : LPC.cpair tl1 tl2 = (| res1, res2 |);
  Trade.rewrite_with_trade
    (vmatch1 res1 v1 ** vmatch2 v1 res2 _)
    (LPC.vmatch_dep_prod vmatch1 vmatch2 res v);
  Trade.trans (LPC.vmatch_dep_prod vmatch1 vmatch2 res v) _ _;
  res
}

inline_for_extraction
fn zero_copy_parse_fst
  (#tl1 #th1 #th2: Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#k2: Ghost.erased parser_kind)
  (p2: parser k2 th2)
  (j1: LPS.jumper p1)
  (w1: PPB.zero_copy_parse vmatch1 p1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
: PPB.zero_copy_parse #tl1 #(th1 & th2) (LPC.vmatch_synth vmatch1 fst) #(and_then_kind k1 k2) (nondep_then p1 p2)
= (input: _)
  (#pm: _)
  (#v: _)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  nondep_then_eq #k1 #th1 p1 #k2 #th2 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  let gv1 = Ghost.hide (fst (Ghost.reveal v));
  let gv2 = Ghost.hide (snd (Ghost.reveal v));
  PPB.pts_to_parsed_intro p1 input1 gv1;
  PPB.pts_to_parsed_intro p2 input2 gv2;
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1 ** PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  let res = w1 input1;
  Trade.trans_hyp_l (vmatch1 res _) _ _ _;
  Trade.elim_hyp_r (vmatch1 res _) (PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  Trade.rewrite_with_trade
    (vmatch1 res _)
    (LPC.vmatch_synth vmatch1 fst res v);
  Trade.trans (LPC.vmatch_synth vmatch1 fst res v) _ _;
  res
}

inline_for_extraction
fn zero_copy_parse_snd
  (#tl2 #th1 #th2: Type)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#vmatch2: tl2 -> th2 -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 th2)
  (j1: LPS.jumper p1)
  (w2: PPB.zero_copy_parse vmatch2 p2)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
: PPB.zero_copy_parse #tl2 #(th1 & th2) (LPC.vmatch_synth vmatch2 snd) #(and_then_kind k1 k2) (nondep_then p1 p2)
= (input: _)
  (#pm: _)
  (#v: _)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  nondep_then_eq #k1 #th1 p1 #k2 #th2 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  let gv1 = Ghost.hide (fst (Ghost.reveal v));
  let gv2 = Ghost.hide (snd (Ghost.reveal v));
  PPB.pts_to_parsed_intro p1 input1 gv1;
  PPB.pts_to_parsed_intro p2 input2 gv2;
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1 ** PPB.pts_to_parsed p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  let res = w2 input2;
  Trade.trans_hyp_r _ (vmatch2 res _) _ _;
  Trade.elim_hyp_l (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gv1) _ (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  Trade.rewrite_with_trade
    (vmatch2 res _)
    (LPC.vmatch_synth vmatch2 snd res v);
  Trade.trans (LPC.vmatch_synth vmatch2 snd res v) _ _;
  res
}

inline_for_extraction
fn zero_copy_parse_dtuple2_fst
  (#tl1 #th1: Type)
  (#th2: th1 -> Type)
  (#vmatch1: tl1 -> th1 -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (j1: LPS.jumper p1)
  (w1: PPB.zero_copy_parse vmatch1 p1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
: PPB.zero_copy_parse #tl1 #(dtuple2 th1 th2) (LPC.vmatch_synth vmatch1 dfst) #(and_then_kind k1 k2) (parse_dtuple2 p1 p2)
= (input: _)
  (#pm: _)
  (#v: _)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_dtuple2_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed (parse_dtuple2 p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  let gdv1 = Ghost.hide (dfst (Ghost.reveal v));
  let gdv2 = Ghost.hide (dsnd (Ghost.reveal v));
  PPB.pts_to_parsed_intro p1 input1 gdv1;
  PPB.pts_to_parsed_intro (p2 gdv1) input2 gdv2;
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gdv1) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed (p2 gdv1) input2 #(pm /. 2.0R) gdv2) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) gdv1 ** PPB.pts_to_parsed (p2 gdv1) input2 #(pm /. 2.0R) gdv2) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed (parse_dtuple2 p1 p2) input #pm v);
  let res = w1 input1;
  Trade.trans_hyp_l (vmatch1 res _) _ _ _;
  Trade.elim_hyp_r (vmatch1 res _) (PPB.pts_to_parsed (p2 gdv1) input2 #(pm /. 2.0R) gdv2) (PPB.pts_to_parsed (parse_dtuple2 p1 p2) input #pm v);
  Trade.rewrite_with_trade
    (vmatch1 res _)
    (LPC.vmatch_synth vmatch1 dfst res v);
  Trade.trans (LPC.vmatch_synth vmatch1 dfst res v) _ _;
  res
}

inline_for_extraction
fn read_and_zero_copy_parse_dtuple2
  (#tl #th1: Type)
  (#th2: th1 -> Type)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (j1: LPS.jumper p1)
  (r1: PPB.leaf_reader p1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (w2: (xh: th1) -> PPB.zero_copy_parse (LPC.vmatch_dep_proj2 vmatch xh) (p2 xh))
: PPB.zero_copy_parse #tl #(dtuple2 th1 th2) vmatch #(and_then_kind k1 k2) (parse_dtuple2 p1 p2)
= (input: _)
  (#pm: _)
  (#v: _)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_dtuple2_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed (parse_dtuple2 p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  PPB.pts_to_parsed_intro p1 input1 (dfst v);
  PPB.pts_to_parsed_intro (p2 (dfst v)) input2 (dsnd v);
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) (dfst v)) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed (p2 (dfst v)) input2 #(pm /. 2.0R) (dsnd v)) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) (dfst v) ** PPB.pts_to_parsed (p2 (dfst v)) input2 #(pm /. 2.0R) (dsnd v)) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed (parse_dtuple2 p1 p2) input #pm v);
  let v1 = r1 input1;
  Trade.elim_hyp_l _ _ _;
  rewrite each (dfst v) as v1;
  let res = w2 v1 input2;
  Trade.trans (LPC.vmatch_dep_proj2 vmatch v1 res _) _ _;
  Trade.rewrite_with_trade
    (LPC.vmatch_dep_proj2 vmatch v1 res _)
    (vmatch res v);
  Trade.trans (vmatch res v) _ _;
  res
}

(* accessor combinators *)

let clens_synth_inv
  (#t1 #t2: Type)
  (f: (t1 -> GTot t2) { synth_injective f })
  (g: (t2 -> GTot t1) { synth_inverse f g })
: Tot (clens t2 t1)
= {
  clens_cond = (fun _ -> True);
  clens_get = g;
}

let clens_synth_fwd
  (#t1 #t2: Type)
  (f: (t1 -> GTot t2))
  (g: (t2 -> GTot t1))
: Tot (clens t1 t2)
= {
  clens_cond = (fun _ -> True);
  clens_get = f;
}

inline_for_extraction
fn accessor_id (#k: Ghost.erased parser_kind) (#t: Type0) (p: parser k t)
: PPB.accessor p p (clens_id t)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  Trade.refl (PPB.pts_to_parsed p input #pm v);
  input
}

inline_for_extraction
fn accessor_compose
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (#p2: parser k2 t2)
  (#k3: Ghost.erased parser_kind) (#t3: Type0) (#p3: parser k3 t3)
  (#cl12: clens t1 t2)
  (#cl23: clens t2 t3)
  (a12: PPB.accessor p1 p2 cl12)
  (a23: PPB.accessor p2 p3 cl23)
  (sq: squash (clens_compose_strong_pre cl12 cl23))
: PPB.accessor p1 p3 (clens_compose_strong cl12 cl23)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t1)
{
  let mid = a12 input;
  with v2 pm2 . assert (PPB.pts_to_parsed p2 mid #pm2 v2);
  let result = a23 mid;
  with v3 pm3 . assert (PPB.pts_to_parsed p3 result #pm3 v3);
  Trade.trans
    (PPB.pts_to_parsed p3 result #pm3 v3)
    (PPB.pts_to_parsed p2 mid #pm2 v2)
    (PPB.pts_to_parsed p1 input #pm v);
  result
}

inline_for_extraction
fn accessor_fst
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (#p2: parser k2 t2)
  (j1: LPS.jumper p1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (nondep_then p1 p2) p1 (clens_fst t1 t2)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
{
  let res = split_nondep_then j1 input sq;
  unfold (split_nondep_then_post p1 p2 input pm v res);
  Trade.elim_hyp_r
    (PPB.pts_to_parsed p1 (fst res) #(pm /. 2.0R) (fst v))
    (PPB.pts_to_parsed p2 (snd res) #(pm /. 2.0R) (snd v))
    (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  fst res
}

inline_for_extraction
fn accessor_snd
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (#p2: parser k2 t2)
  (j1: LPS.jumper p1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (nondep_then p1 p2) p2 (clens_snd t1 t2)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
{
  let res = split_nondep_then j1 input sq;
  unfold (split_nondep_then_post p1 p2 input pm v res);
  Trade.elim_hyp_l
    (PPB.pts_to_parsed p1 (fst res) #(pm /. 2.0R) (fst v))
    (PPB.pts_to_parsed p2 (snd res) #(pm /. 2.0R) (snd v))
    (PPB.pts_to_parsed (nondep_then p1 p2) input #pm v);
  snd res
}

inline_for_extraction
fn accessor_synth
  (#k: Ghost.erased parser_kind) (#t1 #t2: Type0) (#p: parser k t1)
  (f: (t1 -> GTot t2) { synth_injective f })
  (g: (t2 -> GTot t1) { synth_inverse f g })
: PPB.accessor (parse_synth p f) p (clens_synth_inv f g)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t2)
{
  pts_to_parsed_synth_l2r_trade p f g input;
  input
}

inline_for_extraction
let accessor_synth_inv
  (#k: Ghost.erased parser_kind) (#t1 #t2: Type0) (#p: parser k t1)
  (f: (t1 -> GTot t2) { synth_injective f })
  (g: (t2 -> GTot t1) { synth_inverse f g })
: PPB.accessor (parse_synth p f) p (clens_synth_inv f g)
= accessor_synth f g

inline_for_extraction
fn accessor_synth_fwd
  (#k: Ghost.erased parser_kind) (#t1 #t2: Type0) (#p: parser k t1)
  (f: (t1 -> GTot t2) { synth_injective f })
  (g: (t2 -> GTot t1) { synth_inverse f g })
: PPB.accessor p (parse_synth p f) (clens_synth_fwd f g)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t1)
{
  pts_to_parsed_synth_trade p f g input;
  input
}

inline_for_extraction
fn accessor_ext
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (a: PPB.accessor p1 p2 cl)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl cl'))
: PPB.accessor p1 p2 cl'
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t1)
{
  let result = a input;
  with v2 pm' . assert (PPB.pts_to_parsed p2 result #pm' v2);
  result
}

inline_for_extraction
let accessor_compose_strong
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (#p2: parser k2 t2)
  (#k3: Ghost.erased parser_kind) (#t3: Type0) (#p3: parser k3 t3)
  (#cl12: clens t1 t2)
  (#cl23: clens t2 t3)
  (a12: PPB.accessor p1 p2 cl12)
  (a23: PPB.accessor p2 p3 cl23)
  (sq: squash (clens_compose_strong_pre cl12 cl23))
: PPB.accessor p1 p3 (clens_compose_strong cl12 cl23)
= accessor_compose a12 a23 sq

inline_for_extraction
let accessor_fst_then
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (p2: parser k2 t2)
  (#k': Ghost.erased parser_kind) (#t': Type0) (#p': parser k' t')
  (#cl: clens t1 t')
  (a: PPB.accessor p1 p' cl)
  (j1: LPS.jumper p1)
  (sq1: squash (k1.parser_kind_subkind == Some ParserStrong))
  (sq2: squash (clens_compose_strong_pre (clens_fst t1 t2) cl))
: PPB.accessor (nondep_then p1 p2) p' (clens_compose_strong (clens_fst t1 t2) cl)
= accessor_compose (accessor_fst j1 sq1) a sq2

inline_for_extraction
let accessor_then_fst
  (#k0: Ghost.erased parser_kind) (#t0: Type0) (#p0: parser k0 t0)
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (#p2: parser k2 t2)
  (#cl: clens t0 (t1 & t2))
  (a: PPB.accessor p0 (nondep_then p1 p2) cl)
  (j1: LPS.jumper p1)
  (sq1: squash (k1.parser_kind_subkind == Some ParserStrong))
  (sq2: squash (clens_compose_strong_pre cl (clens_fst t1 t2)))
: PPB.accessor p0 p1 (clens_compose_strong cl (clens_fst t1 t2))
= accessor_compose a (accessor_fst j1 sq1) sq2

inline_for_extraction
let accessor_then_snd
  (#k0: Ghost.erased parser_kind) (#t0: Type0) (#p0: parser k0 t0)
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (#p2: parser k2 t2)
  (#cl: clens t0 (t1 & t2))
  (a: PPB.accessor p0 (nondep_then p1 p2) cl)
  (j1: LPS.jumper p1)
  (sq1: squash (k1.parser_kind_subkind == Some ParserStrong))
  (sq2: squash (clens_compose_strong_pre cl (clens_snd t1 t2)))
: PPB.accessor p0 p2 (clens_compose_strong cl (clens_snd t1 t2))
= accessor_compose a (accessor_snd j1 sq1) sq2

(* ========== Tagged union accessor combinators ========== *)

let clens_tagged_union_tag
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
: Tot (clens data_t tag_t)
= {
  clens_cond = (fun _ -> True);
  clens_get = tag_of_data;
}

let clens_tagged_union_payload
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (t: tag_t)
: Tot (clens data_t (refine_with_tag tag_of_data t))
= {
  clens_cond = (fun d -> tag_of_data d == t);
  clens_get = (fun (d: data_t) -> (d <: refine_with_tag tag_of_data t));
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn accessor_tagged_union_tag
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type0)
  (pt: parser kt tag_t)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (j: LPS.jumper pt)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_tagged_union pt tag_of_data p) pt (clens_tagged_union_tag tag_of_data)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased data_t)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_tagged_union_eq pt tag_of_data p bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt pt;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  let off = j input 0sz;
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_r (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_tag #pm wb_tag) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_tagged_union pt tag_of_data p) input #pm v);
  parse_strong_prefix pt bytes wb_tag;
  PPB.pts_to_parsed_intro pt input_tag (tag_of_data v);
  Trade.trans (PPB.pts_to_parsed pt input_tag #(pm /. 2.0R) (tag_of_data v)) (S.pts_to input_tag #pm wb_tag) (PPB.pts_to_parsed (parse_tagged_union pt tag_of_data p) input #pm v);
  input_tag
}

inline_for_extraction
fn accessor_tagged_union_payload
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type0)
  (#pt: parser kt tag_t)
  (jt: LPS.jumper pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (t: tag_t)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_tagged_union pt tag_of_data p) (p t) (clens_tagged_union_payload tag_of_data t)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased data_t)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_tagged_union_eq pt tag_of_data p bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt pt;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  let off = jt input 0sz;
  let payload_bytes = Ghost.hide (Seq.slice bytes (SZ.v off) (Seq.length bytes));
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_tagged_union pt tag_of_data p) input #pm v);
  Seq.lemma_eq_elim wb_payload (Ghost.reveal payload_bytes);
  PPB.pts_to_parsed_intro (p t) input_payload (Ghost.reveal v);
  Trade.trans (PPB.pts_to_parsed (p t) input_payload #(pm /. 2.0R) (Ghost.reveal v)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_tagged_union pt tag_of_data p) input #pm v);
  input_payload
}

#pop-options

(* ========== dtuple2 accessor combinators ========== *)

let clens_dtuple2_snd
  (#t1: Type)
  (#t2: t1 -> Type)
  (x1: t1)
: Tot (clens (dtuple2 t1 t2) (t2 x1))
= {
  clens_cond = (fun (d: dtuple2 t1 t2) -> dfst d == x1);
  clens_get = (fun (d: dtuple2 t1 t2) ->
    (dsnd d <: Ghost (t2 x1) (requires (dfst d == x1)) (ensures fun _ -> True)));
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn accessor_dtuple2_snd
  (#k1: Ghost.erased parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (j1: LPS.jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: (t1 -> Tot Type0))
  (p2: (x: t1) -> Tot (parser k2 (t2 x)))
  (x1: Ghost.erased t1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_dtuple2 p1 p2) (p2 (Ghost.reveal x1)) (clens_dtuple2_snd (Ghost.reveal x1))
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1 t2))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_dtuple2_eq p1 p2 bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv k1 p1;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  let off = j1 input 0sz;
  let payload_bytes = Ghost.hide (Seq.slice bytes (SZ.v off) (Seq.length bytes));
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_dtuple2 p1 p2) input #pm v);
  Seq.lemma_eq_elim wb_payload (Ghost.reveal payload_bytes);
  PPB.pts_to_parsed_intro (p2 (Ghost.reveal x1)) input_payload (dsnd v);
  Trade.trans (PPB.pts_to_parsed (p2 (Ghost.reveal x1)) input_payload #(pm /. 2.0R) (dsnd v)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_dtuple2 p1 p2) input #pm v);
  input_payload
}

#pop-options

(* ========== zero_copy_parse_strong_prefix combinators ========== *)

#push-options "--z3rlimit 20"

ghost
fn pts_to_parsed_strong_prefix_synth_l2r
  (#t #t': Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
  (input: slice byte)
  (#pm: perm)
  (#v: t')
  requires PPB.pts_to_parsed_strong_prefix (parse_synth p f) input #pm v
  ensures PPB.pts_to_parsed_strong_prefix p input #pm (f' v) **
    Trade.trade (PPB.pts_to_parsed_strong_prefix p input #pm (f' v))
               (PPB.pts_to_parsed_strong_prefix (parse_synth p f) input #pm v)
{
  unfold (PPB.pts_to_parsed_strong_prefix (parse_synth p f) input #pm v);
  with w . assert (S.pts_to input #pm w);
  parse_synth_eq p f w;
  let v1 = Ghost.hide (fst (Some?.v (parse p w)));
  assert pure (f v1 == v);
  assert pure (f (f' v) == v);
  fold (PPB.pts_to_parsed_strong_prefix p input #pm (f' v));
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix p input #pm (f' v))
      (PPB.pts_to_parsed_strong_prefix (parse_synth p f) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix p input #pm (f' v));
      with w' . assert (S.pts_to input #pm w');
      parse_synth_eq p f w';
      fold (PPB.pts_to_parsed_strong_prefix (parse_synth p f) input #pm v)
    };
}

#pop-options

inline_for_extraction
fn zero_copy_parse_strong_prefix_synth
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (#p1: parser k1 t1) (#tl: Type0) (#vmatch: tl -> t1 -> slprop) (r: PPB.zero_copy_parse_strong_prefix vmatch p1)
  (#t2: Type0) (f2: (t1 -> GTot t2) { synth_injective f2 }) (f1: (t2 -> GTot t1) { synth_inverse f2 f1 })
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
: PPB.zero_copy_parse_strong_prefix #_ #_ (LPC.vmatch_synth vmatch f1) #_ (parse_synth p1 f2)
= (input: slice byte)
  (#pm: _)
  (#v: _)
{
  pts_to_parsed_strong_prefix_synth_l2r p1 f2 f1 input;
  let res = r input;
  Trade.trans (vmatch res (f1 v)) _ _;
  Trade.rewrite_with_trade
    (vmatch res (f1 v))
    (LPC.vmatch_synth vmatch f1 res v);
  Trade.trans (LPC.vmatch_synth vmatch f1 res v) (vmatch res (f1 v)) _;
  res
}

ghost
fn pts_to_parsed_strong_prefix_filter_elim
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (f: (t -> GTot bool))
  (input: slice byte)
  (#pm: perm)
  (#v: parse_filter_refine f)
  requires PPB.pts_to_parsed_strong_prefix (parse_filter p f) input #pm v
  ensures PPB.pts_to_parsed_strong_prefix p input #pm (v <: t) **
    Trade.trade (PPB.pts_to_parsed_strong_prefix p input #pm (v <: t))
               (PPB.pts_to_parsed_strong_prefix (parse_filter p f) input #pm v)
{
  unfold (PPB.pts_to_parsed_strong_prefix (parse_filter p f) input #pm v);
  with w . assert (S.pts_to input #pm w);
  parse_filter_eq p f w;
  fold (PPB.pts_to_parsed_strong_prefix p input #pm (v <: t));
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix p input #pm (v <: t))
      (PPB.pts_to_parsed_strong_prefix (parse_filter p f) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix p input #pm (v <: t));
      with w' . assert (S.pts_to input #pm w');
      parse_filter_eq p f w';
      fold (PPB.pts_to_parsed_strong_prefix (parse_filter p f) input #pm v)
    };
}

inline_for_extraction
fn zero_copy_parse_strong_prefix_filter
  (#t: Type0) (#t1: Type0)
  (vmatch: t -> t1 -> slprop)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1) (w: PPB.zero_copy_parse_strong_prefix #t #t1 vmatch p1)
  (f: (t1 -> GTot bool))
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
: PPB.zero_copy_parse_strong_prefix #t #(parse_filter_refine u#0 f) (LPC.vmatch_filter vmatch f) #(parse_filter_kind k1) (parse_filter p1 f)
= (input: _)
  (#pm: _)
  (#v: _)
{
  pts_to_parsed_strong_prefix_filter_elim p1 f input;
  let res = w input;
  with v' . assert (vmatch res v');
  Trade.trans (vmatch res v') _ _;
  Trade.rewrite_with_trade
    (vmatch res v')
    (LPC.vmatch_filter vmatch f res v);
  Trade.trans _ (vmatch res v') _;
  res
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn read_and_zero_copy_parse_strong_prefix_dtuple2
  (#tl #th1: Type)
  (#th2: th1 -> Type)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 th1)
  (#vmatch: tl -> dtuple2 th1 th2 -> slprop)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: th1) -> parser k2 (th2 x))
  (j1: LPS.jumper p1)
  (r1: PPB.leaf_reader p1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (w2: (xh: th1) -> PPB.zero_copy_parse_strong_prefix (LPC.vmatch_dep_proj2 vmatch xh) (p2 xh))
: PPB.zero_copy_parse_strong_prefix #tl #(dtuple2 th1 th2) vmatch #(and_then_kind k1 k2) (parse_dtuple2 p1 p2)
= (input: _)
  (#pm: _)
  (#v: _)
{
  PPB.pts_to_parsed_strong_prefix_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_dtuple2_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  PPB.pts_to_parsed_intro p1 input1 (dfst v);
  PPB.pts_to_parsed_strong_prefix_intro (p2 (dfst v)) input2 (dsnd v);
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) (dfst v)) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed_strong_prefix (p2 (dfst v)) input2 #(pm /. 2.0R) (dsnd v)) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) (dfst v) ** PPB.pts_to_parsed_strong_prefix (p2 (dfst v)) input2 #(pm /. 2.0R) (dsnd v)) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v);
  let v1 = r1 input1;
  Trade.elim_hyp_l _ _ _;
  rewrite each (dfst v) as v1;
  let res = w2 v1 input2;
  Trade.trans (LPC.vmatch_dep_proj2 vmatch v1 res _) _ _;
  Trade.rewrite_with_trade
    (LPC.vmatch_dep_proj2 vmatch v1 res _)
    (vmatch res v);
  Trade.trans (vmatch res v) _ _;
  res
}

#pop-options

(* ========== split_nondep_then for pts_to_parsed_strong_prefix ========== *)

let split_nondep_then_strong_prefix_post
  (#k1: Ghost.erased parser_kind) (#t1: Type0) (p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) (p2: parser k2 t2)
  (input: slice byte) (pm: perm) (v: Ghost.erased (t1 & t2))
  (res: (slice byte & slice byte))
: slprop
= PPB.pts_to_parsed_strong_prefix p1 (fst res) #(pm /. 2.0R) (fst v) **
  PPB.pts_to_parsed_strong_prefix p2 (snd res) #(pm /. 2.0R) (snd v) **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix p1 (fst res) #(pm /. 2.0R) (fst v) **
     PPB.pts_to_parsed_strong_prefix p2 (snd res) #(pm /. 2.0R) (snd v))
    (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v)

inline_for_extraction
fn split_nondep_then_strong_prefix
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (j1: LPS.jumper p1)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong /\ k2.parser_kind_subkind == Some ParserStrong))
  requires PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v
  returns res: (slice byte & slice byte)
  ensures split_nondep_then_strong_prefix_post p1 p2 input pm v res
{
  PPB.pts_to_parsed_strong_prefix_elim input;
  with w . assert (S.pts_to input #pm w);
  nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  let gv1 = Ghost.hide (fst (Ghost.reveal v));
  let gv2 = Ghost.hide (snd (Ghost.reveal v));
  PPB.pts_to_parsed_strong_prefix_intro p1 input1 gv1;
  PPB.pts_to_parsed_strong_prefix_intro p2 input2 gv2;
  Trade.prod (PPB.pts_to_parsed_strong_prefix p1 input1 #(pm /. 2.0R) gv1) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed_strong_prefix p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed_strong_prefix p1 input1 #(pm /. 2.0R) gv1 ** PPB.pts_to_parsed_strong_prefix p2 input2 #(pm /. 2.0R) gv2) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v);
  rewrite each gv1 as (fst (Ghost.reveal v));
  rewrite each gv2 as (snd (Ghost.reveal v));
  fold (split_nondep_then_strong_prefix_post p1 p2 input pm v (input1, input2));
  (input1, input2)
}

(* pts_to_parsed_strong_prefix_nondep_then_assoc_l2r: reassociate (p1 ** p2) ** p3 -> p1 ** (p2 ** p3) *)

let nondep_then_assoc_l2r_parse_eq
  (#k1: parser_kind) (#t1: Type) (p1: parser k1 t1)
  (#k2: parser_kind) (#t2: Type) (p2: parser k2 t2)
  (#k3: parser_kind) (#t3: Type) (p3: parser k3 t3)
  (w: bytes)
: Lemma
  (requires
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    k3.parser_kind_subkind == Some ParserStrong /\
    Some? (parse (nondep_then (nondep_then p1 p2) p3) w)
  )
  (ensures (
    Some? (parse (nondep_then p1 (nondep_then p2 p3)) w) /\
    (let Some (((v1, v2), v3), n) = parse (nondep_then (nondep_then p1 p2) p3) w in
     parse (nondep_then p1 (nondep_then p2 p3)) w == Some ((v1, (v2, v3)), n))
  ))
= nondep_then_eq (nondep_then p1 p2) p3 w;
  nondep_then_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  parser_kind_prop_equiv k2 p2;
  nondep_then_eq p2 p3 (Seq.slice w (snd (Some?.v (parse p1 w))) (Seq.length w));
  nondep_then_eq p1 (nondep_then p2 p3) w

let nondep_then_assoc_r2l_parse_eq
  (#k1: parser_kind) (#t1: Type) (p1: parser k1 t1)
  (#k2: parser_kind) (#t2: Type) (p2: parser k2 t2)
  (#k3: parser_kind) (#t3: Type) (p3: parser k3 t3)
  (w: bytes)
: Lemma
  (requires
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    k3.parser_kind_subkind == Some ParserStrong /\
    Some? (parse (nondep_then p1 (nondep_then p2 p3)) w)
  )
  (ensures (
    Some? (parse (nondep_then (nondep_then p1 p2) p3) w) /\
    (let Some ((v1, (v2, v3)), n) = parse (nondep_then p1 (nondep_then p2 p3)) w in
     parse (nondep_then (nondep_then p1 p2) p3) w == Some (((v1, v2), v3), n))
  ))
= nondep_then_eq p1 (nondep_then p2 p3) w;
  parser_kind_prop_equiv k1 p1;
  nondep_then_eq p2 p3 (Seq.slice w (snd (Some?.v (parse p1 w))) (Seq.length w));
  parser_kind_prop_equiv k2 p2;
  nondep_then_eq (nondep_then p1 p2) p3 w;
  nondep_then_eq p1 p2 w

ghost
fn pts_to_parsed_strong_prefix_nondep_then_assoc_l2r
  (#t1: Type0) (#t2: Type0) (#t3: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#p2: parser k2 t2)
  (#k3: Ghost.erased parser_kind) (#p3: parser k3 t3)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased ((t1 & t2) & t3))
  (sq: squash (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    k3.parser_kind_subkind == Some ParserStrong
  ))
requires
  PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v
ensures exists* v' .
  PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v' **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v')
    (PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v) **
  pure (v' == (fst (fst v), (snd (fst v), snd v)))
{
  unfold (PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v);
  with w . assert (S.pts_to input #pm w);
  nondep_then_assoc_l2r_parse_eq p1 p2 p3 w;
  let v' : Ghost.erased (t1 & (t2 & t3)) = Ghost.hide (fst (fst (Ghost.reveal v)), (snd (fst (Ghost.reveal v)), snd (Ghost.reveal v)));
  fold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v')
      (PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v');
      with w2 . assert (S.pts_to input #pm w2);
      nondep_then_assoc_r2l_parse_eq p1 p2 p3 w2;
      fold (PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v)
    };
}

(* pts_to_parsed_strong_prefix_ext_trade: ghost rewrite between extensionally-equal parsers *)

ghost
fn pts_to_parsed_strong_prefix_ext_trade
  (#t: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t)
  (#k2: Ghost.erased parser_kind) (#p2: parser k2 t)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (sq: squash (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    (forall x . parse p1 x == parse p2 x)
  ))
requires
  PPB.pts_to_parsed_strong_prefix p1 input #pm v
ensures
  PPB.pts_to_parsed_strong_prefix p2 input #pm v **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix p2 input #pm v)
    (PPB.pts_to_parsed_strong_prefix p1 input #pm v)
{
  unfold (PPB.pts_to_parsed_strong_prefix p1 input #pm v);
  fold (PPB.pts_to_parsed_strong_prefix p2 input #pm v);
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix p2 input #pm v)
      (PPB.pts_to_parsed_strong_prefix p1 input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix p2 input #pm v);
      fold (PPB.pts_to_parsed_strong_prefix p1 input #pm v)
    };
}

(* pts_to_parsed_strong_prefix_ext_trade_gen: ghost rewrite between extensionally-equal parsers with different types *)

let pts_to_parsed_strong_prefix_ext_trade_gen_precond
  (#k1: parser_kind) (#t1: Type) (p1: parser k1 t1)
  (#k2: parser_kind) (#t2: Type) (p2: parser k2 t2)
: Tot prop
= k1.parser_kind_subkind == Some ParserStrong /\
  k2.parser_kind_subkind == Some ParserStrong /\
  t1 == t2 /\
  (forall x . parse p1 x == parse p2 x)

let pts_to_parsed_strong_prefix_ext_trade_gen_post
  (t1 t2: Type)
  (v1: t1) (v2: t2)
: Tot prop
= t1 == t2 /\ v1 == coerce_eq () v2

ghost
fn pts_to_parsed_strong_prefix_ext_trade_gen
  (#t1 #t2: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#p2: parser k2 t2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t1)
  (sq: squash (
    pts_to_parsed_strong_prefix_ext_trade_gen_precond p1 p2
  ))
requires
  PPB.pts_to_parsed_strong_prefix p1 input #pm v
ensures exists* v2 .
  PPB.pts_to_parsed_strong_prefix p2 input #pm v2 **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix p2 input #pm v2)
    (PPB.pts_to_parsed_strong_prefix p1 input #pm v) **
  pure (pts_to_parsed_strong_prefix_ext_trade_gen_post t1 t2 v v2)
{
  unfold (PPB.pts_to_parsed_strong_prefix p1 input #pm v);
  with w . assert (S.pts_to input #pm w);
  rewrite each t1 as t2;
  fold (PPB.pts_to_parsed_strong_prefix p2 input #pm (coerce_eq () (Ghost.reveal v)));
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix p2 input #pm (coerce_eq () (Ghost.reveal v)))
      (PPB.pts_to_parsed_strong_prefix p1 input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix p2 input #pm (coerce_eq () (Ghost.reveal v)));
      rewrite each t2 as t1;
      fold (PPB.pts_to_parsed_strong_prefix p1 input #pm v)
    };
}

(* split_nondep_then_strong_prefix'': split with extensionally-equal parser *)

let split_nondep_then_strong_prefix''_precond
  (#t0 #t1 #t2: Type0)
  (#k0: parser_kind)
  (p0: parser k0 t0)
  (#k1: parser_kind)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (p2: parser k2 t2)
: Tot prop
= t0 == (t1 & t2) /\
  k0.parser_kind_subkind == Some ParserStrong /\
  k1.parser_kind_subkind == Some ParserStrong /\
  k2.parser_kind_subkind == Some ParserStrong /\
  (forall b . parse p0 b == parse (nondep_then p1 p2) b)

let split_nondep_then_strong_prefix''_postcond
  (#t0 #t1 #t2: Type)
  (v: t0)
  (v1: t1)
  (v2: t2)
: Tot prop
= t0 == (t1 & t2) /\
  v == coerce_eq () (v1, v2)

inline_for_extraction
fn split_nondep_then_strong_prefix''
  (#t0 #t1 #t2: Type0)
  (#k0: Ghost.erased parser_kind)
  (#p0: parser k0 t0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (j1: LPS.jumper p1)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t0)
  (sq: squash (
    split_nondep_then_strong_prefix''_precond p0 p1 p2
  ))
  requires PPB.pts_to_parsed_strong_prefix p0 input #pm v
  returns res: (slice byte & slice byte)
  ensures (
  let (left, right) = res in
  exists* v1 v2 .
  PPB.pts_to_parsed_strong_prefix p1 left #(pm /. 2.0R) v1 **
  PPB.pts_to_parsed_strong_prefix p2 right #(pm /. 2.0R) v2 **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix p1 left #(pm /. 2.0R) v1 **
     PPB.pts_to_parsed_strong_prefix p2 right #(pm /. 2.0R) v2)
    (PPB.pts_to_parsed_strong_prefix p0 input #pm v) **
  pure (split_nondep_then_strong_prefix''_postcond (Ghost.reveal v) v1 v2)
  )
{
  pts_to_parsed_strong_prefix_ext_trade_gen #t0 #(t1 & t2) #k0 #p0 #(and_then_kind k1 k2) #(nondep_then p1 p2) input ();
  with v' . assert (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v');
  let (left, right) = split_nondep_then_strong_prefix j1 input ();
  unfold (split_nondep_then_strong_prefix_post p1 p2 input pm v' (left, right));
  Trade.trans
    (PPB.pts_to_parsed_strong_prefix p1 left #(pm /. 2.0R) (fst (Ghost.reveal v')) **
     PPB.pts_to_parsed_strong_prefix p2 right #(pm /. 2.0R) (snd (Ghost.reveal v')))
    (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v')
    (PPB.pts_to_parsed_strong_prefix p0 input #pm v);
  (left, right)
}

(* ========== split_dtuple2 for pts_to_parsed_strong_prefix ========== *)

let split_dtuple2_strong_prefix_post
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#p2: (x: t1) -> parser k2 (t2 x))
  (input: slice byte) (pm: perm) (v: Ghost.erased (dtuple2 t1 t2))
  (res: (slice byte & slice byte))
: slprop
= let (left, right) = res in
  PPB.pts_to_parsed p1 left #(pm /. 2.0R) (dfst v) **
  PPB.pts_to_parsed_strong_prefix (p2 (dfst v)) right #(pm /. 2.0R) (dsnd v) **
  Trade.trade
    (PPB.pts_to_parsed p1 left #(pm /. 2.0R) (dfst v) **
     PPB.pts_to_parsed_strong_prefix (p2 (dfst v)) right #(pm /. 2.0R) (dsnd v))
    (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v)

inline_for_extraction
fn split_dtuple2_strong_prefix
  (#t1: Type0)
  (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (j1: LPS.jumper p1)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1 t2))
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong /\ k2.parser_kind_subkind == Some ParserStrong))
  requires PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v
  returns res: (slice byte & slice byte)
  ensures split_dtuple2_strong_prefix_post #t1 #t2 #k1 #p1 #k2 #p2 input pm v res
{
  PPB.pts_to_parsed_strong_prefix_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_dtuple2_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  PPB.pts_to_parsed_intro p1 input1 (dfst v);
  PPB.pts_to_parsed_strong_prefix_intro (p2 (dfst v)) input2 (dsnd v);
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) (dfst v)) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed_strong_prefix (p2 (dfst v)) input2 #(pm /. 2.0R) (dsnd v)) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) (dfst v) ** PPB.pts_to_parsed_strong_prefix (p2 (dfst v)) input2 #(pm /. 2.0R) (dsnd v)) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v);
  fold (split_dtuple2_strong_prefix_post #t1 #t2 #k1 #p1 #k2 #p2 input pm v (input1, input2));
  (input1, input2)
}

(* ========== dtuple2_as_nondep_then for pts_to_parsed_strong_prefix ========== *)

ghost
fn pts_to_parsed_strong_prefix_dtuple2_as_nondep_then
  (#t1: Type0) (#t2: t1 -> Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#p2: (x: t1) -> parser k2 (t2 x))
  (input: slice byte) (#pm: perm) (#v: Ghost.erased (dtuple2 t1 t2))
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong /\ k2.parser_kind_subkind == Some ParserStrong))
requires PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v
ensures exists* v' .
  PPB.pts_to_parsed_strong_prefix (nondep_then p1 (p2 (dfst v))) input #pm v' **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (p2 (dfst v))) input #pm v')
    (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v) **
  pure (fst v' == dfst v /\ snd v' == dsnd v)
{
  unfold (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v);
  with w . assert (S.pts_to input #pm w);
  parse_dtuple2_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  nondep_then_eq p1 (p2 (dfst v)) w;
  let v' : Ghost.erased (t1 & t2 (dfst v)) = Ghost.hide (dfst (Ghost.reveal v), dsnd (Ghost.reveal v));
  fold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (p2 (dfst v))) input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (p2 (dfst v))) input #pm v')
      (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (p2 (dfst v))) input #pm v');
      with w2 . assert (S.pts_to input #pm w2);
      nondep_then_eq p1 (p2 (dfst v)) w2;
      parser_kind_prop_equiv k1 p1;
      parse_dtuple2_eq p1 p2 w2;
      fold (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v)
    };
}

(* ========== nondep_then_assoc_r2l for pts_to_parsed_strong_prefix ========== *)

ghost
fn pts_to_parsed_strong_prefix_nondep_then_assoc_r2l
  (#t1: Type0) (#t2: Type0) (#t3: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#p2: parser k2 t2)
  (#k3: Ghost.erased parser_kind) (#p3: parser k3 t3)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & (t2 & t3)))
  (sq: squash (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    k3.parser_kind_subkind == Some ParserStrong
  ))
requires
  PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v
ensures exists* v' .
  PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v' **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v')
    (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v) **
  pure (v' == ((fst v, fst (snd v)), snd (snd v)))
{
  unfold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v);
  with w . assert (S.pts_to input #pm w);
  nondep_then_assoc_r2l_parse_eq p1 p2 p3 w;
  let v' : Ghost.erased ((t1 & t2) & t3) = Ghost.hide ((fst (Ghost.reveal v), fst (snd (Ghost.reveal v))), snd (snd (Ghost.reveal v)));
  fold (PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v')
      (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix (nondep_then (nondep_then p1 p2) p3) input #pm v');
      with w2 . assert (S.pts_to input #pm w2);
      nondep_then_assoc_l2r_parse_eq p1 p2 p3 w2;
      fold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then p2 p3)) input #pm v)
    };
}

(* ========== ext_nondep_then_left for pts_to_parsed_strong_prefix ========== *)

ghost
fn pts_to_parsed_strong_prefix_ext_nondep_then_left
  (#t1 #t2 #t3: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#p2: parser k2 t2)
  (#k3: Ghost.erased parser_kind) (#p3: parser k3 t3)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t3))
  (sq: squash (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    k3.parser_kind_subkind == Some ParserStrong /\
    t1 == t2 /\
    (forall x . parse p1 x == parse p2 x)
  ))
requires PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v
ensures exists* v' .
  PPB.pts_to_parsed_strong_prefix (nondep_then p2 p3) input #pm v' **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix (nondep_then p2 p3) input #pm v')
    (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v) **
  pure (t1 == t2 /\ v == v')
{
  unfold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v);
  with w . assert (S.pts_to input #pm w);
  nondep_then_eq p1 p3 w;
  nondep_then_eq p2 p3 w;
  fold (PPB.pts_to_parsed_strong_prefix (nondep_then p2 p3) input #pm v);
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix (nondep_then p2 p3) input #pm v)
      (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix (nondep_then p2 p3) input #pm v);
      with w2 . assert (S.pts_to input #pm w2);
      nondep_then_eq p2 p3 w2;
      nondep_then_eq p1 p3 w2;
      fold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v)
    };
}

(* ========== ext_nondep_then_right for pts_to_parsed_strong_prefix ========== *)

ghost
fn pts_to_parsed_strong_prefix_ext_nondep_then_right
  (#t1 #t2 #t3: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#p2: parser k2 t2)
  (#k3: Ghost.erased parser_kind) (#p3: parser k3 t3)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  (sq: squash (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    k3.parser_kind_subkind == Some ParserStrong /\
    t2 == t3 /\
    (forall x . parse p2 x == parse p3 x)
  ))
requires PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v
ensures exists* v' .
  PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v' **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v')
    (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v) **
  pure (t2 == t3 /\ v == v')
{
  unfold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v);
  with w . assert (S.pts_to input #pm w);
  nondep_then_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  nondep_then_eq p1 p3 w;
  fold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v);
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v)
      (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p3) input #pm v);
      with w2 . assert (S.pts_to input #pm w2);
      nondep_then_eq p1 p3 w2;
      parser_kind_prop_equiv k1 p1;
      nondep_then_eq p1 p2 w2;
      fold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 p2) input #pm v)
    };
}

(* ========== dtuple2_nondep_then_assoc_l2r for pts_to_parsed_strong_prefix ========== *)

ghost
fn pts_to_parsed_strong_prefix_dtuple2_nondep_then_assoc_l2r
  (#t1: Type0) (#t2: t1 -> Type0) (#t3: Type0)
  (#k1: Ghost.erased parser_kind) (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#p2: ((x: t1) -> parser k2 (t2 x)))
  (#k3: Ghost.erased parser_kind) (#p3: parser k3 t3)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1 t2 & t3))
  (sq: squash (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    k3.parser_kind_subkind == Some ParserStrong
  ))
requires PPB.pts_to_parsed_strong_prefix (nondep_then (parse_dtuple2 p1 p2) p3) input #pm v
ensures exists* v' .
  PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then (p2 (dfst (fst v))) p3)) input #pm v' **
  Trade.trade
    (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then (p2 (dfst (fst v))) p3)) input #pm v')
    (PPB.pts_to_parsed_strong_prefix (nondep_then (parse_dtuple2 p1 p2) p3) input #pm v) **
  pure (fst v' == dfst (fst v) /\ fst (snd v') == dsnd (fst v) /\ snd (snd v') == snd v)
{
  unfold (PPB.pts_to_parsed_strong_prefix (nondep_then (parse_dtuple2 p1 p2) p3) input #pm v);
  with w . assert (S.pts_to input #pm w);
  nondep_then_eq (parse_dtuple2 p1 p2) p3 w;
  parse_dtuple2_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  parser_kind_prop_equiv k2 (p2 (dfst (fst (Ghost.reveal v))));
  nondep_then_eq p1 (nondep_then (p2 (dfst (fst (Ghost.reveal v)))) p3) w;
  nondep_then_eq (p2 (dfst (fst (Ghost.reveal v)))) p3 (Seq.slice w (snd (Some?.v (parse p1 w))) (Seq.length w));
  let v' : Ghost.erased (t1 & (t2 (dfst (fst (Ghost.reveal v))) & t3)) = Ghost.hide (dfst (fst (Ghost.reveal v)), (dsnd (fst (Ghost.reveal v)), snd (Ghost.reveal v)));
  fold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then (p2 (dfst (fst (Ghost.reveal v)))) p3)) input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then (p2 (dfst (fst (Ghost.reveal v)))) p3)) input #pm v')
      (PPB.pts_to_parsed_strong_prefix (nondep_then (parse_dtuple2 p1 p2) p3) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed_strong_prefix (nondep_then p1 (nondep_then (p2 (dfst (fst (Ghost.reveal v)))) p3)) input #pm v');
      with w2 . assert (S.pts_to input #pm w2);
      nondep_then_eq p1 (nondep_then (p2 (dfst (fst (Ghost.reveal v)))) p3) w2;
      parser_kind_prop_equiv k1 p1;
      nondep_then_eq (p2 (dfst (fst (Ghost.reveal v)))) p3 (Seq.slice w2 (snd (Some?.v (parse p1 w2))) (Seq.length w2));
      parser_kind_prop_equiv k2 (p2 (dfst (fst (Ghost.reveal v))));
      nondep_then_eq (parse_dtuple2 p1 p2) p3 w2;
      parse_dtuple2_eq p1 p2 w2;
      fold (PPB.pts_to_parsed_strong_prefix (nondep_then (parse_dtuple2 p1 p2) p3) input #pm v)
    };
}

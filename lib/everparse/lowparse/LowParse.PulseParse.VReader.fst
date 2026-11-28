module LowParse.PulseParse.VReader
#lang-pulse
include LowParse.Spec.Combinators
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base

(* A validating reader validates its input and, on success, returns the
   parsed value, in a single pass. This is convenient for small strong
   parsers built with `and_then` (e.g. ASN.1 identifiers), whose
   validators need to read the value of the first component anyway.
   Validators, jumpers and leaf readers are all derived from a validating
   reader. *)

let vreader_postcond (#k: parser_kind) (#t: Type) (p: parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t) (res: option t) : GTot prop =
  SZ.v offset <= Seq.length v /\
  SZ.v off <= Seq.length v /\ (
  match parse p (Seq.slice v (SZ.v offset) (Seq.length v)), res with
  | None, None -> True
  | Some (x, consumed), Some y -> x == y /\ SZ.v off == SZ.v offset + consumed
  | _ -> False
  )

inline_for_extraction
let vreader (#t: Type0) (#k: parser_kind) (p: parser k t) : Tot Type =
  (input: slice byte) ->
  (poffset: R.ref SZ.t) ->
  (#offset: Ghost.erased SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt (option t)
    (pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v))
    (fun res -> pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (vreader_postcond p offset v off res)))

inline_for_extraction
fn vread_ext
  (#t: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (r1: vreader p1)
  (#k2: Ghost.erased parser_kind)
  (p2: parser k2 t { forall x . parse p1 x == parse p2 x })
: vreader #t #k2 p2
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  r1 input poffset
}

let vread_map_prop
  (#k1: parser_kind) (#t1: Type) (p1: parser k1 t1)
  (#t2: Type) (f: t1 -> t2)
  (#k2: parser_kind) (p2: parser k2 t2)
: Tot prop
= forall (b: bytes) . match parse p1 b, parse p2 b with
  | None, None -> True
  | Some (x, l), Some (y, l') -> f x == y /\ l == l'
  | _ -> False

(* Map a function over the result of a validating reader, provided that
   the target parser agrees with the source parser on consumed bytes and
   maps values with that function *)
inline_for_extraction
fn vread_map
  (#t1: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (r1: vreader p1)
  (#t2: Type0)
  (f: (t1 -> t2))
  (#k2: Ghost.erased parser_kind)
  (p2: parser k2 t2)
  (u: squash (vread_map_prop p1 f p2))
: vreader #t2 #k2 p2
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let res = r1 input poffset;
  match res {
    None -> { None #t2 }
    Some x -> { Some (f x) }
  }
}

inline_for_extraction
fn vread_of_validator
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (v1: LPS.validator p)
  (r1: PPB.leaf_reader p)
  (u: squash (k.parser_kind_subkind == Some ParserStrong))
: vreader #t #k p
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let offset = !poffset;
  let is_valid = v1 input poffset;
  if is_valid {
    let off = !poffset;
    let x = PPB.read_parsed_from_validator_success r1 input offset off;
    Some x
  } else {
    None #t
  }
}

inline_for_extraction
fn vread_ret
  (#t: Type0)
  (x: t)
: vreader #t #parse_ret_kind (parse_ret x)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  Some x
}

inline_for_extraction
fn vread_fail
  (k: Ghost.erased parser_kind { fail_parser_kind_precond k })
  (t: Type0)
: vreader #t #k (fail_parser k t)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  None #t
}

inline_for_extraction
fn vread_weaken
  (#t: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (k2: Ghost.erased parser_kind)
  (r1: vreader p1)
  (u: squash (k2 `is_weaker_than` k1))
: vreader #t #(Ghost.reveal k2) (weaken k2 p1)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  r1 input poffset
}

inline_for_extraction
fn vread_synth
  (#k1: Ghost.erased parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser k1 t1)
  (r1: vreader p1)
  (f2: (t1 -> Tot t2))
  (u: squash (synth_injective f2))
: vreader #t2 #(Ghost.reveal k1) (parse_synth p1 f2)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parse_synth_eq p1 f2 (Seq.slice v (SZ.v offset) (Seq.length v));
  let res = r1 input poffset;
  match res {
    None -> { None #t2 }
    Some x -> { Some (f2 x) }
  }
}

inline_for_extraction
fn vread_filter
  (#k1: Ghost.erased parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (r1: vreader p1)
  (f: (t1 -> Tot bool))
: vreader #(parse_filter_refine f) #(parse_filter_kind k1) (parse_filter p1 f)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parse_filter_eq p1 f (Seq.slice v (SZ.v offset) (Seq.length v));
  let res = r1 input poffset;
  match res {
    None -> { None #(parse_filter_refine f) }
    Some x -> {
      if f x {
        Some #(parse_filter_refine f) x
      } else {
        None #(parse_filter_refine f)
      }
    }
  }
}

inline_for_extraction
fn vread_and_then
  (#k1: Ghost.erased parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (r1: vreader p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type0)
  (#p2: (t1 -> parser k2 t2))
  (r2: ((x: t1) -> vreader (p2 x)))
  (u: squash (
    (and_then_kind k1 k2).parser_kind_injective ==> and_then_cases_injective p2
  ))
: vreader #t2 #(and_then_kind k1 k2) (p1 `and_then` p2)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  and_then_eq p1 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  let res = r1 input poffset;
  match res {
    None -> { None #t2 }
    Some x -> { r2 x input poffset }
  }
}

inline_for_extraction
fn vread_nondep_then
  (#k1: Ghost.erased parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (r1: vreader p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (r2: vreader p2)
: vreader #(t1 & t2) #(and_then_kind k1 k2) (p1 `nondep_then` p2)
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  nondep_then_eq p1 p2 (Seq.slice v (SZ.v offset) (Seq.length v));
  let res1 = r1 input poffset;
  match res1 {
    None -> { None #(t1 & t2) }
    Some x1 -> {
      let res2 = r2 input poffset;
      match res2 {
        None -> { None #(t1 & t2) }
        Some x2 -> { Some (x1, x2) }
      }
    }
  }
}

inline_for_extraction
fn ifthenelse_vreader
  (#t: Type0) (#k: Ghost.erased parser_kind) (p: parser k t)
  (cond: bool)
  (rtrue: squash (cond == true) -> vreader p)
  (rfalse: squash (cond == false) -> vreader p)
: vreader #t #k p
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  if cond {
    rtrue () input poffset
  } else {
    rfalse () input poffset
  }
}

(* Bind a computed value inside the reader body, so that extraction does
   not leave a `let` outside the function *)

inline_for_extraction
fn vread_let
  (#t: Type0) (#k: Ghost.erased parser_kind) (p: parser k t)
  (#a: Type0)
  (x: a)
  (r: (y: a { y == x }) -> vreader p)
: vreader #t #k p
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let y : (y: a { y == x }) = x;
  r y input poffset
}

(* Derived validators, jumpers and leaf readers *)

inline_for_extraction
fn validate_of_vreader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: vreader p)
: LPS.validator #t #k p
=
  (input: slice byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let res = r input poffset;
  Some? res
}

inline_for_extraction
fn jump_of_vreader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: vreader p)
: LPS.jumper #t #k p
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let mut poffset = offset;
  let res = r input poffset;
  !poffset
}

inline_for_extraction
fn leaf_read_of_vreader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: vreader p)
: PPB.leaf_reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  assert (pure (Seq.equal (Seq.slice w 0 (Seq.length w)) w));
  let mut poffset = 0sz;
  let res = r input poffset;
  Trade.elim _ _;
  Some?.v res
}

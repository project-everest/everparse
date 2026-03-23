module LowParseExample2
#lang-pulse
(* Ported from LowParse.SLow-based test.
   Original used parse32/serialize32 (SLow). We keep the spec parts
   and add a trivial Pulse main for extraction.
   The SLow parts (parse32, serialize32, size32) are dropped. *)

include LowParse.Spec.Combinators
include LowParse.Spec.Bytes
include LowParse.Spec.VLData
include LowParse.Spec.List
open Pulse.Lib.Pervasives
open LowParse.Spec.Base

module B32 = FStar.Bytes
module U32 = FStar.UInt32
module I32 = FStar.Int32

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

type t = {
  b: (b: B32.bytes { B32.length b <= 65535 } );
}

inline_for_extraction
let synth_t
  (x: parse_bounded_vlbytes_t 0 65535)
: Tot t
= { b = x }

let synth_t_inj
  ()
: Lemma
  (synth_injective synth_t)
= ()

let parse_t_spec : parser _ t =
  synth_t_inj ();
  parse_bounded_vlbytes 0 65535 `parse_synth` synth_t

inline_for_extraction
let synth_t_recip
  (x: t)
: Tot (parse_bounded_vlbytes_t 0 65535)
= x.b

let synth_t_recip_inv
  ()
: Lemma
  (synth_inverse synth_t synth_t_recip)
= ()

let serialize_t_spec : serializer parse_t_spec =
  synth_t_inj ();
  synth_t_recip_inv ();
  serialize_synth
    _
    synth_t
    (serialize_bounded_vlbytes 0 65535)
    synth_t_recip
    ()

let t'_l_serializable (x: list t) : GTot Type0 =
  parse_bounded_vldata_strong_pred 0 255 (serialize_list _ serialize_t_spec) x

inline_for_extraction
let synth_t'
  (x: parse_bounded_vldata_strong_t 0 255 (serialize_list _ serialize_t_spec))
: Tot (l: list t { t'_l_serializable l })
= x

let synth_t'_inj () : Lemma
  (synth_injective synth_t')
= ()

let parse_t'_spec : parser _ (l: list t { t'_l_serializable l }) =
  synth_t'_inj ();
  parse_bounded_vldata_strong 0 255 (serialize_list _ serialize_t_spec)
  `parse_synth`
  synth_t'

inline_for_extraction
let synth_t'_recip
  (x: (l: list t { t'_l_serializable l }))
: Tot (parse_bounded_vldata_strong_t 0 255 (serialize_list _ serialize_t_spec))
= x

let synth_t'_recip_inv () : Lemma
  (synth_inverse synth_t' synth_t'_recip)
= ()

let serialize_t'_spec : serializer parse_t'_spec =
  synth_t'_inj ();
  synth_t'_recip_inv ();
  serialize_synth
    _
    synth_t'
    (serialize_bounded_vldata_strong 0 255 (serialize_list _ serialize_t_spec))
    synth_t'_recip
    ()

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }

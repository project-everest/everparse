module LowParseExample11
#lang-pulse
(* Ported from vclist test.
   Original used parse_vclist with BCVLI encoding.
   Demonstrates: validate_t, jump_t, leaf_read_bcvli, and read_6th
   (access 6th element of a validated vclist). *)

include LowParse.Spec.VCList
include LowParse.Spec.BCVLI
include LowParse.Spec.Int
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module LPI = LowParse.Pulse.Int
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module PPVCL = LowParse.PulseParse.VCList
module PPBCVLI = LowParse.PulseParse.BCVLI
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module L = FStar.List.Tot
module I32 = FStar.Int32

type elem = U32.t

type t = (l: list elem { let ln = L.length l in 10 <= ln /\ ln <= 1000 })

inline_for_extraction
let parse_t_kind : parser_kind = strong_parser_kind 11 5005 None

let parse_t' = parse_vclist 10 1000 parse_bcvli parse_bcvli

let kind_eq : squash (get_parser_kind parse_t' == parse_t_kind) =
  _ by (FStar.Tactics.trefl ())

let type_eq : squash (t == vlarray elem 10 1000) = _ by (FStar.Tactics.trefl ())

let parse_t : parser parse_t_kind t = parse_t'

let serialize_t : serializer parse_t = serialize_vclist 10 1000 serialize_bcvli serialize_bcvli

(* PulseParse leaf_readers for bounded_integer_le and bcvli *)

module PPBI = LowParse.PulseParse.BoundedInt

let fits_u64_squash (_: unit) : Lemma (FStar.SizeT.fits_u64) = assume (FStar.SizeT.fits_u64)

inline_for_extraction noextract
let r_ble1 = PPBI.leaf_read_bounded_integer_le_1

inline_for_extraction noextract
let r_ble2 = PPBI.leaf_read_bounded_integer_le_2

inline_for_extraction noextract
let r_ble4 = PPBI.leaf_read_bounded_integer_le_4

inline_for_extraction noextract
let leaf_read_bcvli : PPB.leaf_reader parse_bcvli =
  PPBCVLI.leaf_read_bcvli r_ble1 r_ble2 r_ble4

(* Pulse validator and jumper *)

inline_for_extraction
let validate_t : LPS.validator parse_t =
  fits_u64_squash ();
  PPVCL.validate_vclist 10ul 1000ul (PPBCVLI.validate_bcvli r_ble1 r_ble2 r_ble4) leaf_read_bcvli (PPBCVLI.validate_bcvli r_ble1 r_ble2 r_ble4) ()

inline_for_extraction
let jump_t : LPS.jumper parse_t =
  fits_u64_squash ();
  PPVCL.jump_vclist 10ul 1000ul (PPBCVLI.jump_bcvli r_ble1) leaf_read_bcvli (PPBCVLI.jump_bcvli r_ble1) ()

(* read_t: read an entire validated t value *)

inline_for_extraction noextract
let leaf_read_u32 : PPB.leaf_reader parse_u32 =
  PPB.leaf_reader_of_serialized (LPI.read_u32' ())

(* Helper: establish that jumping past elements in a nlist is valid *)
let nlist_nth_jump_lemma
  (n: nat)
  (b: bytes)
  (i: nat { i < n })
: Lemma
  (requires (Some? (parse (parse_nlist n parse_bcvli) b)))
  (ensures (
    let Some (l, _) = parse (parse_nlist n parse_bcvli) b in
    Some? (parse parse_bcvli b) /\
    (let Some (_, consumed) = parse parse_bcvli b in
     consumed <= Seq.length b /\
     (i = 0 ==> fst (Some?.v (parse parse_bcvli b)) == L.index l 0) /\
     (i > 0 ==>
       Some? (parse (parse_nlist (n - 1) parse_bcvli) (Seq.slice b consumed (Seq.length b))) /\
       fst (Some?.v (parse (parse_nlist (n - 1) parse_bcvli) (Seq.slice b consumed (Seq.length b)))) == L.tl l))))
  (decreases n)
= parse_nlist_eq n parse_bcvli b;
  parser_kind_prop_equiv parse_bcvli_kind parse_bcvli

(* read_6th: read the 6th element of a validated vclist.
   Jump past the length, then skip 6 elements, then read the 7th.
   Following the Low* pattern: jump_bcvli (length), jump_bcvli × 6, read_bcvli. *)

#push-options "--z3rlimit 128 --fuel 8 --ifuel 4"

fn read_6th
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (offset: SZ.t)
  (off: SZ.t)
  (_: squash (LPS.validator_success parse_t offset v off))
  requires S.pts_to input #pm v
  returns res: U32.t
  ensures S.pts_to input #pm v
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_vclist_eq 10 1000 parse_bcvli parse_bcvli sinput;

  let pos0 = PPBCVLI.jump_bcvli r_ble1 input offset;
  let payload = Ghost.hide (Seq.slice v (SZ.v pos0) (Seq.length v));
  Seq.lemma_eq_elim (Ghost.reveal payload)
    (Seq.slice sinput (SZ.v pos0 - SZ.v offset) (Seq.length sinput));

  let gn = Ghost.hide (
    let Some (len, _) = parse parse_bcvli sinput in
    U32.v len
  );

  nlist_nth_jump_lemma gn payload 6;
  let pos1 = PPBCVLI.jump_bcvli r_ble1 input pos0;
  Seq.lemma_eq_elim
    (Seq.slice (Ghost.reveal payload) (SZ.v pos1 - SZ.v pos0) (Seq.length (Ghost.reveal payload)))
    (Seq.slice v (SZ.v pos1) (Seq.length v));

  nlist_nth_jump_lemma (gn - 1) (Seq.slice v (SZ.v pos1) (Seq.length v)) 5;
  let pos2 = PPBCVLI.jump_bcvli r_ble1 input pos1;
  Seq.lemma_eq_elim
    (Seq.slice (Seq.slice v (SZ.v pos1) (Seq.length v)) (SZ.v pos2 - SZ.v pos1) (Seq.length (Seq.slice v (SZ.v pos1) (Seq.length v))))
    (Seq.slice v (SZ.v pos2) (Seq.length v));

  nlist_nth_jump_lemma (gn - 2) (Seq.slice v (SZ.v pos2) (Seq.length v)) 4;
  let pos3 = PPBCVLI.jump_bcvli r_ble1 input pos2;
  Seq.lemma_eq_elim
    (Seq.slice (Seq.slice v (SZ.v pos2) (Seq.length v)) (SZ.v pos3 - SZ.v pos2) (Seq.length (Seq.slice v (SZ.v pos2) (Seq.length v))))
    (Seq.slice v (SZ.v pos3) (Seq.length v));

  nlist_nth_jump_lemma (gn - 3) (Seq.slice v (SZ.v pos3) (Seq.length v)) 3;
  let pos4 = PPBCVLI.jump_bcvli r_ble1 input pos3;
  Seq.lemma_eq_elim
    (Seq.slice (Seq.slice v (SZ.v pos3) (Seq.length v)) (SZ.v pos4 - SZ.v pos3) (Seq.length (Seq.slice v (SZ.v pos3) (Seq.length v))))
    (Seq.slice v (SZ.v pos4) (Seq.length v));

  nlist_nth_jump_lemma (gn - 4) (Seq.slice v (SZ.v pos4) (Seq.length v)) 2;
  let pos5 = PPBCVLI.jump_bcvli r_ble1 input pos4;
  Seq.lemma_eq_elim
    (Seq.slice (Seq.slice v (SZ.v pos4) (Seq.length v)) (SZ.v pos5 - SZ.v pos4) (Seq.length (Seq.slice v (SZ.v pos4) (Seq.length v))))
    (Seq.slice v (SZ.v pos5) (Seq.length v));

  nlist_nth_jump_lemma (gn - 5) (Seq.slice v (SZ.v pos5) (Seq.length v)) 1;
  let pos6 = PPBCVLI.jump_bcvli r_ble1 input pos5;
  Seq.lemma_eq_elim
    (Seq.slice (Seq.slice v (SZ.v pos5) (Seq.length v)) (SZ.v pos6 - SZ.v pos5) (Seq.length (Seq.slice v (SZ.v pos5) (Seq.length v))))
    (Seq.slice v (SZ.v pos6) (Seq.length v));

  nlist_nth_jump_lemma (gn - 6) (Seq.slice v (SZ.v pos6) (Seq.length v)) 0;
  let pos7 = PPBCVLI.jump_bcvli r_ble1 input pos6;
  PPB.read_parsed_from_validator_success leaf_read_bcvli input pos6 pos7
}

#pop-options

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }

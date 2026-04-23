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

(* read_6th: read the 6th element of a validated vclist.
   Uses accessor_vclist_payload to get the nlist payload,
   then accessor_nlist_nth to access element 6, then leaf_read_bcvli. *)

module PPVCL = LowParse.PulseParse.VCList

let parse_t_ext_sq : squash (LPS.pts_to_serialized_ext_trade_gen_precond parse_t
  (parse_synth
    (parse_dtuple2
      (parse_vclist_dtuple2_tag_parser 10 1000 parse_bcvli)
      (parse_vclist_dtuple2_payload_parser 10 1000 parse_bcvli))
    (parse_vclist_dtuple2_synth 10 1000 #U32.t))) =
  Classical.forall_intro (parse_vclist_dtuple2_eq 10 1000 parse_bcvli #_ #_ parse_bcvli)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

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
  (* Get pts_to_parsed for the whole vclist *)
  let input' = PPB.peek_trade_gen parse_t input offset off;
  with v0 pm0 . assert (PPB.pts_to_parsed parse_t input' #pm0 v0);

  (* accessor_vclist_payload: get the nlist payload *)
  let gn : Ghost.erased nat = Ghost.hide (L.length v0);
  assert (pure ((PPVCL.clens_vclist_payload 10 1000 #U32.t gn).clens_cond v0));
  rewrite (PPB.pts_to_parsed parse_t input' #pm0 v0)
    as (PPB.pts_to_parsed (parse_vclist 10 1000 parse_bcvli parse_bcvli) input' #pm0 v0);
  let nlist_slice = PPVCL.accessor_vclist_payload
    (Ghost.hide 10) (Ghost.hide 1000)
    (PPBCVLI.jump_bcvli r_ble1)
    gn
    ()
    input';
  with vn pmn . assert (PPB.pts_to_parsed (parse_nlist gn parse_bcvli) nlist_slice #pmn vn);
  with vn_trade . assert (Trade.trade
    (PPB.pts_to_parsed (parse_nlist gn parse_bcvli) nlist_slice #pmn vn)
    (PPB.pts_to_parsed (parse_vclist 10 1000 parse_bcvli parse_bcvli) input' #pm0 vn_trade));
  rewrite
    (Trade.trade
      (PPB.pts_to_parsed (parse_nlist gn parse_bcvli) nlist_slice #pmn vn)
      (PPB.pts_to_parsed (parse_vclist 10 1000 parse_bcvli parse_bcvli) input' #pm0 vn_trade))
    as
    (Trade.trade
      (PPB.pts_to_parsed (parse_nlist gn parse_bcvli) nlist_slice #pmn vn)
      (PPB.pts_to_parsed parse_t input' #pm0 v0));
  Trade.trans _ (PPB.pts_to_parsed parse_t input' #pm0 v0) (S.pts_to input #pm v);

  (* accessor_nlist_nth: get the 6th element *)
  let i6 : (i0: SZ.t { SZ.v i0 < gn }) = SZ.uint_to_t 6;
  let elem_slice = PPVCL.accessor_nlist_nth () (PPBCVLI.jump_bcvli r_ble1) gn i6 nlist_slice;
  with ve pme . assert (PPB.pts_to_parsed parse_bcvli elem_slice #pme ve);
  Trade.trans _ (PPB.pts_to_parsed (parse_nlist gn parse_bcvli) nlist_slice #pmn vn) (S.pts_to input #pm v);

  (* Read the element *)
  let res = leaf_read_bcvli elem_slice;
  Trade.elim (PPB.pts_to_parsed parse_bcvli elem_slice #pme ve) (S.pts_to input #pm v);
  res
}

#pop-options

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }

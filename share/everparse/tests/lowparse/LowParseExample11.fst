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
   Uses accessor combinators to decompose the vclist:
   parse_t ≡ parse_synth (parse_dtuple2 tag_parser nlist_parser) dsnd
   Then accessor_synth to unwrap, accessor_snd to get the nlist,
   accessor_parser_ext to unwrap weaken,
   and accessor_nlist_nth to access the 6th element. *)

module PPVCL = LowParse.PulseParse.VCList
module PPC = LowParse.PulseParse.Combinators
include LowParse.CLens

(* Jumper for the tag parser *)
inline_for_extraction noextract
let jump_tag : LPS.jumper (parse_vclist_dtuple2_tag_parser 10 1000 parse_bcvli) =
  fits_u64_squash ();
  LPC.jump_synth
    (LPC.jump_filter (PPBCVLI.jump_bcvli r_ble1) (bounded_count_prop 10 1000))
    (synth_bounded_count 10 1000)

let parse_t_dtuple2 =
  parse_dtuple2
    (parse_vclist_dtuple2_tag_parser 10 1000 parse_bcvli)
    (parse_vclist_dtuple2_payload_parser 10 1000 parse_bcvli)

let synth_t_dtuple2_injective ()
: Lemma (synth_injective (parse_vclist_dtuple2_synth 10 1000 #U32.t))
= ()

let synth_t_dtuple2_recip
  (x: vlarray U32.t 10 1000)
: GTot (dtuple2 (bounded_count 10 1000) (fun (n: bounded_count 10 1000) -> nlist (U32.v n) U32.t))
= (| U32.uint_to_t (L.length x), x |)

let synth_t_dtuple2_inverse ()
: Lemma (synth_inverse (parse_vclist_dtuple2_synth 10 1000 #U32.t) synth_t_dtuple2_recip)
= ()

let parse_t_ext_sq : squash (LPS.pts_to_serialized_ext_trade_gen_precond parse_t
  (parse_synth parse_t_dtuple2 (parse_vclist_dtuple2_synth 10 1000 #U32.t))) =
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

  (* Step 1: accessor_parser_ext from parse_t to parse_synth parse_t_dtuple2 synth *)
  let s1 = PPB.accessor_parser_ext
    parse_t
    (parse_synth parse_t_dtuple2 (parse_vclist_dtuple2_synth 10 1000 #U32.t))
    parse_t_ext_sq
    input';
  with v1 pm1 . assert (PPB.pts_to_parsed (parse_synth parse_t_dtuple2 (parse_vclist_dtuple2_synth 10 1000)) s1 #pm1 v1);
  Trade.trans _ (PPB.pts_to_parsed parse_t input' #pm0 v0) (S.pts_to input #pm v);

  (* Step 2: accessor_synth to unwrap and get the dtuple2 *)
  synth_t_dtuple2_injective ();
  synth_t_dtuple2_inverse ();
  let s2 = PPC.accessor_synth
    (parse_vclist_dtuple2_synth 10 1000 #U32.t)
    synth_t_dtuple2_recip
    s1;
  with v2 pm2 . assert (PPB.pts_to_parsed parse_t_dtuple2 s2 #pm2 v2);
  Trade.trans _ (PPB.pts_to_parsed (parse_synth parse_t_dtuple2 (parse_vclist_dtuple2_synth 10 1000)) s1 #pm1 v1) (S.pts_to input #pm v);

  (* Step 3: accessor_dtuple2_snd to get the nlist payload *)
  let gn : Ghost.erased (bounded_count 10 1000) = Ghost.hide (dfst v2);
  let s3 = PPC.accessor_dtuple2_snd jump_tag (parse_vclist_dtuple2_payload_parser 10 1000 parse_bcvli) gn () s2;
  Trade.trans _ (PPB.pts_to_parsed parse_t_dtuple2 s2 #pm2 v2) (S.pts_to input #pm v);

  (* Step 4: reinterpret as parse_nlist via pts_to_parsed_ext_trade_gen *)
  let gn_nat : Ghost.erased nat = Ghost.hide (U32.v (Ghost.reveal gn));
  with v3 pm3 . assert (PPB.pts_to_parsed (parse_vclist_dtuple2_payload_parser 10 1000 parse_bcvli (Ghost.reveal gn)) s3 #pm3 v3);
  PPB.pts_to_parsed_ext_trade_gen (parse_nlist gn_nat parse_bcvli) s3;
  with v4 . assert (PPB.pts_to_parsed (parse_nlist gn_nat parse_bcvli) s3 #pm3 v4);
  Trade.trans
    (PPB.pts_to_parsed (parse_nlist gn_nat parse_bcvli) s3 #pm3 v4)
    (PPB.pts_to_parsed (parse_vclist_dtuple2_payload_parser 10 1000 parse_bcvli (Ghost.reveal gn)) s3 #pm3 v3)
    (S.pts_to input #pm v);

  (* Step 5: accessor_nlist_nth to get the 6th element *)
  let i6 : (i0: SZ.t { SZ.v i0 < gn_nat }) = SZ.uint_to_t 6;
  let s5 = PPVCL.accessor_nlist_nth () (PPBCVLI.jump_bcvli r_ble1) gn_nat i6 s3;
  with v5 pm5 . assert (PPB.pts_to_parsed parse_bcvli s5 #pm5 v5);
  Trade.trans _ (PPB.pts_to_parsed (parse_nlist gn_nat parse_bcvli) s3 #pm3 v4) (S.pts_to input #pm v);

  (* Step 6: Read the element *)
  let res = leaf_read_bcvli s5;
  Trade.elim (PPB.pts_to_parsed parse_bcvli s5 #pm5 v5) (S.pts_to input #pm v);
  res
}

#pop-options

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }

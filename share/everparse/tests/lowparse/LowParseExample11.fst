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
   Uses accessor_parser_ext to bridge from parse_t to the nlist payload,
   then accessor_nlist_nth to access element 6, then leaf_read_bcvli.
   Follows the Low* pattern: vclist_elim → jump past length → access nth element. *)

module PPVCL = LowParse.PulseParse.VCList
module PPC = LowParse.PulseParse.Combinators
module PPITE = LowParse.PulseParse.IfThenElse

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

(* Spec lemma: parse_t at the nlist payload level *)
let parse_t_nlist_payload_eq
  (input: bytes)
: Lemma
  (requires Some? (parse parse_t input))
  (ensures (
    Some? (parse parse_bcvli input) /\
    (let Some (len, consumed_tag) = parse parse_bcvli input in
     let input' = Seq.slice input consumed_tag (Seq.length input) in
     let n = U32.v len in
     10 <= n /\ n <= 1000 /\
     Some? (parse (parse_nlist n parse_bcvli) input') /\
     (let Some (nlist_val, consumed_nlist) = parse (parse_nlist n parse_bcvli) input' in
      consumed_tag + consumed_nlist == snd (Some?.v (parse parse_t input)) /\
      nlist_val == (fst (Some?.v (parse parse_t input)) <: list U32.t)))))
= parse_vclist_eq 10 1000 parse_bcvli parse_bcvli input;
  let Some (len, consumed_tag) = parse parse_bcvli input in
  let input' = Seq.slice input consumed_tag (Seq.length input) in
  parse_synth_eq (parse_nlist (U32.v len) parse_bcvli) (synth_vclist_payload 10 1000 len) input'

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
  parse_t_nlist_payload_eq sinput;
  parser_kind_prop_equiv parse_bcvli_kind parse_bcvli;

  (* Get pts_to_parsed for the whole vclist *)
  let input' = PPB.peek_trade_gen parse_t input offset off;
  with v0 pm0 . assert (PPB.pts_to_parsed parse_t input' #pm0 v0);

  (* Use accessor_ifthenelse_payload' to skip the length prefix and get the nlist payload.
     parse_t = ((bcvli filter ...) synth ...) and_then payload
     The tag parser is (bcvli filter synth), payload is parse_vclist_payload.
     We use the generic approach: jump past the tag, get the payload sub-slice. *)
  let gn : Ghost.erased nat = Ghost.hide (
    let Some (len, _) = parse parse_bcvli sinput in
    U32.v len
  );
  let nlist_slice = PPITE.accessor_ifthenelse_payload'
    #parse_t_kind
    #parse_bcvli_kind
    #(parse_nlist_kind gn parse_bcvli_kind)
    #U32.t
    #t
    #(nlist gn U32.t)
    parse_bcvli
    parse_t
    (parse_nlist gn parse_bcvli)
    (fun (v: t) -> (v <: nlist gn U32.t))
    (PPBCVLI.jump_bcvli r_ble1)
    ()
    (fun w -> parse_t_nlist_payload_eq w)
    input';
  with vn pmn . assert (PPB.pts_to_parsed (parse_nlist gn parse_bcvli) nlist_slice #pmn vn);
  Trade.trans _ (PPB.pts_to_parsed parse_t input' #pm0 v0) (S.pts_to input #pm v);

  (* Use accessor_nlist_nth to get the 6th element *)
  let i6 : (i0: SZ.t { SZ.v i0 < gn }) = SZ.uint_to_t 6;
  let elem_slice = PPVCL.accessor_nlist_nth () (PPBCVLI.jump_bcvli r_ble1) gn i6 nlist_slice;
  with ve pme . assert (PPB.pts_to_parsed parse_bcvli elem_slice #pme ve);
  Trade.trans _ (PPB.pts_to_parsed (parse_nlist gn parse_bcvli) nlist_slice #pmn vn) (S.pts_to input #pm v);

  (* Read the element *)
  let res = leaf_read_bcvli elem_slice;

  (* Chain trades back to original *)
  Trade.elim (PPB.pts_to_parsed parse_bcvli elem_slice #pme ve)
    (S.pts_to input #pm v);
  res
}

#pop-options

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }

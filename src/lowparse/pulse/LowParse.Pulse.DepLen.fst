module LowParse.Pulse.DepLen
#lang-pulse
include LowParse.Spec.DepLen
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module U32 = FStar.UInt32

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_deplen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#hk: parser_kind)
  (#ht: Type0)
  (#hp: parser hk ht)
  (#hs: serializer hp)
  (hv: LPS.validator hp)
  (hr: LPS.leaf_reader hs)
  (dlf: ht -> Tot (bounded_int32 min max))
  (#pk: parser_kind)
  (#pt: Type0)
  (#pp: parser pk pt)
  (ps: serializer pp)
  (pv: LPS.validator pp)
  (_: squash (hk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.validator (parse_deplen min max hp dlf ps)
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_deplen_unfold2 min max hp dlf ps sinput;
  pts_to_len input;
  let offset_val = !poffset;
  let is_valid_h = hv input poffset;
  if is_valid_h {
    let off1 = !poffset;
    let h_val = LPS.read_from_validator_success hr input offset_val off1;
    let payload_len = dlf h_val;
    FStar.SizeT.fits_u64_implies_fits_32 ();
    let payload_len_sz = SZ.uint32_to_sizet payload_len;
    let input_len = len input;
    let remaining = SZ.sub input_len off1;
    if SZ.lt remaining payload_len_sz {
      poffset := offset_val;
      false
    } else {
      let payload_end = SZ.add off1 payload_len_sz;
      let input1, input2 = split_trade input payload_end;
      with v2 . assert (pts_to input2 #pm v2);
      Trade.elim_hyp_r (pts_to input1 #pm _) (pts_to input2 #pm v2) (pts_to input #pm v);
      Seq.lemma_eq_elim
        (Seq.slice sinput (SZ.v off1 - SZ.v offset_val) (SZ.v off1 - SZ.v offset_val + U32.v payload_len))
        (Seq.slice v (SZ.v off1) (SZ.v payload_end));
      let is_valid_p = pv input1 poffset;
      if is_valid_p {
        let off2 = !poffset;
        Trade.elim (pts_to input1 #pm _) (pts_to input #pm v);
        if (off2 = payload_end) {
          serializer_correct_implies_complete pp ps;
          true
        } else {
          poffset := offset_val;
          false
        }
      } else {
        Trade.elim (pts_to input1 #pm _) (pts_to input #pm v);
        poffset := offset_val;
        false
      }
    }
  } else {
    false
  }
}

#pop-options

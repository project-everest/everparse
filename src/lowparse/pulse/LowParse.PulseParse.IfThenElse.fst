module LowParse.PulseParse.IfThenElse
#lang-pulse
include LowParse.Spec.IfThenElse
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_ifthenelse
  (p: parse_ifthenelse_param)
  (vt: LPS.validator p.parse_ifthenelse_tag_parser)
  (r: PPB.leaf_reader p.parse_ifthenelse_tag_parser)
  (vp: (b: bool) -> Tot (LPS.validator (dsnd (p.parse_ifthenelse_payload_parser b))))
  (_: squash (p.parse_ifthenelse_tag_kind.parser_kind_subkind == Some ParserStrong))
: LPS.validator (parse_ifthenelse p)
=
  (input: S.slice byte)
  (poffset: ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_ifthenelse_eq p sinput;
  let offset_val = !poffset;
  let is_valid_tag = vt input poffset;
  if is_valid_tag {
    let off = !poffset;
    let t = PPB.read_parsed_from_validator_success r input offset_val off;
    let b = p.parse_ifthenelse_tag_cond t;
    Seq.lemma_eq_elim
      (Seq.slice sinput (SZ.v off - SZ.v offset_val) (Seq.length sinput))
      (Seq.slice v (SZ.v off) (Seq.length v));
    if b {
      vp true input poffset
    } else {
      vp false input poffset
    }
  } else {
    false
  }
}

inline_for_extraction
fn jump_ifthenelse
  (p: parse_ifthenelse_param)
  (jt: LPS.jumper p.parse_ifthenelse_tag_parser)
  (r: PPB.leaf_reader p.parse_ifthenelse_tag_parser)
  (jp: (b: bool) -> Tot (LPS.jumper (dsnd (p.parse_ifthenelse_payload_parser b))))
  (_: squash (p.parse_ifthenelse_tag_kind.parser_kind_subkind == Some ParserStrong))
: LPS.jumper (parse_ifthenelse p)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_ifthenelse_eq p sinput;
  pts_to_len input;
  let off = jt input offset;
  let t = PPB.read_parsed_from_validator_success r input offset off;
  let b = p.parse_ifthenelse_tag_cond t;
  Seq.lemma_eq_elim
    (Seq.slice sinput (SZ.v off - SZ.v offset) (Seq.length sinput))
    (Seq.slice v (SZ.v off) (Seq.length v));
  if b {
    jp true input off
  } else {
    jp false input off
  }
}

#pop-options

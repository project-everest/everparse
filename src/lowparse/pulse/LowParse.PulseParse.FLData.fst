module LowParse.PulseParse.FLData
#lang-pulse
include LowParse.Spec.FLData
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
include LowParse.CLens

inline_for_extraction
fn validate_fldata
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (sz: SZ.t)
: LPS.validator #t #(parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  pts_to_len input;
  let offset_val = !poffset;
  let remaining = SZ.sub (len input) offset_val;
  if SZ.lt remaining sz {
    false
  } else {
    let split_point = SZ.add offset_val sz;
    let input1, input2 = split_trade input split_point;
    with v2 . assert (pts_to input2 #pm v2);
    Trade.elim_hyp_r (pts_to input1 #pm _) (pts_to input2 #pm v2) (pts_to input #pm v_bytes);
    let is_valid = v input1 poffset;
    if is_valid {
      let off = !poffset;
      Trade.elim (pts_to input1 #pm _) (pts_to input #pm v_bytes);
      if (off = split_point) {
        true
      } else {
        false
      }
    } else {
      Trade.elim (pts_to input1 #pm _) (pts_to input #pm v_bytes);
      false
    }
  }
}

inline_for_extraction
let validate_fldata_gen
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (sz: SZ.t)
: LPS.validator #t #(parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz))
= validate_fldata v sz

inline_for_extraction
let validate_fldata_consumes_all
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (sz: SZ.t)
  (_: squash (k.parser_kind_subkind == Some ParserConsumesAll))
: LPS.validator #t #(parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz))
= validate_fldata v sz

inline_for_extraction
fn validate_fldata_strong
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (sz: SZ.t)
: LPS.validator #(parse_fldata_strong_t s (SZ.v sz)) #(parse_fldata_kind (SZ.v sz) k) (parse_fldata_strong s (SZ.v sz))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  validate_fldata v sz input poffset
}

inline_for_extraction
fn jump_fldata
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: SZ.t)
: LPS.jumper #t #(parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz))
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parser_kind_prop_equiv (parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz));
  pts_to_len input;
  SZ.add offset sz
}

inline_for_extraction
fn jump_fldata_strong
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: SZ.t)
: LPS.jumper #(parse_fldata_strong_t s (SZ.v sz)) #(parse_fldata_kind (SZ.v sz) k) (parse_fldata_strong s (SZ.v sz))
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parser_kind_prop_equiv (parse_fldata_kind (SZ.v sz) k) (parse_fldata_strong s (SZ.v sz));
  pts_to_len input;
  SZ.add offset sz
}

#push-options "--z3rlimit 32"

ghost
fn pts_to_parsed_fldata_payload_trade
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (n: nat)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires PPB.pts_to_parsed (parse_fldata p n) input #pm v
  ensures PPB.pts_to_parsed p input #pm v **
    Trade.trade (PPB.pts_to_parsed p input #pm v)
                (PPB.pts_to_parsed (parse_fldata p n) input #pm v)
{
  unfold (PPB.pts_to_parsed (parse_fldata p n) input #pm v);
  with w . assert (S.pts_to input #pm w);
  S.pts_to_len input;
  parser_kind_prop_equiv (parse_fldata_kind n k) (parse_fldata p n);
  parser_kind_prop_equiv k p;
  Seq.lemma_eq_elim (Seq.slice w 0 (Seq.length w)) w;
  fold (PPB.pts_to_parsed p input #pm v);
  intro
    (Trade.trade
      (PPB.pts_to_parsed p input #pm v)
      (PPB.pts_to_parsed (parse_fldata p n) input #pm v)
    )
    #(pure (SZ.v (S.len input) == n))
    fn _ {
      unfold (PPB.pts_to_parsed p input #pm v);
      with w' . assert (S.pts_to input #pm w');
      S.pts_to_len input;
      parser_kind_prop_equiv (parse_fldata_kind n k) (parse_fldata p n);
      parser_kind_prop_equiv k p;
      Seq.lemma_eq_elim (Seq.slice w' 0 (Seq.length w')) w';
      fold (PPB.pts_to_parsed (parse_fldata p n) input #pm v)
    }
}

inline_for_extraction
fn zero_copy_parse_fldata
  (#tl #t: Type0) (#vmatch: tl -> t -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t)
  (w: PPB.zero_copy_parse vmatch p)
  (n: SZ.t)
: PPB.zero_copy_parse vmatch (parse_fldata p (SZ.v n))
= (input: _) (#pm: _) (#v: _)
{
  pts_to_parsed_fldata_payload_trade p (SZ.v n) input;
  let res = w input;
  Trade.trans (vmatch res v) _ _;
  res
}

#pop-options

(* accessor_fldata: access the payload of fixed-length data *)

inline_for_extraction
fn accessor_fldata
  (#k: Ghost.erased parser_kind) (#t: Type0) (p: parser k t)
  (n: Ghost.erased nat)
: PPB.accessor (parse_fldata p n) p (clens_id t)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  pts_to_parsed_fldata_payload_trade p n input;
  input
}

(* accessor_fldata_strong: access the payload of strong fixed-length data *)

let clens_fldata_strong
  (#k: parser_kind) (#t: Type) (#p: parser k t)
  (s: serializer p) (sz: nat)
: Tot (clens (parse_fldata_strong_t s sz) t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (x: parse_fldata_strong_t s sz) -> (x <: t));
}

#push-options "--z3rlimit 32"

ghost
fn pts_to_parsed_fldata_strong_payload_trade
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (s: serializer p)
  (n: nat)
  (input: slice byte)
  (#pm: perm)
  (#v: parse_fldata_strong_t s n)
  requires PPB.pts_to_parsed (parse_fldata_strong s n) input #pm v
  ensures PPB.pts_to_parsed p input #pm (v <: t) **
    Trade.trade (PPB.pts_to_parsed p input #pm (v <: t))
                (PPB.pts_to_parsed (parse_fldata_strong s n) input #pm v)
{
  unfold (PPB.pts_to_parsed (parse_fldata_strong s n) input #pm v);
  with w . assert (S.pts_to input #pm w);
  S.pts_to_len input;
  parser_kind_prop_equiv (parse_fldata_kind n k) (parse_fldata_strong s n);
  parser_kind_prop_equiv (parse_fldata_kind n k) (parse_fldata p n);
  parser_kind_prop_equiv k p;
  Seq.lemma_eq_elim (Seq.slice w 0 (Seq.length w)) w;
  fold (PPB.pts_to_parsed p input #pm (v <: t));
  intro
    (Trade.trade
      (PPB.pts_to_parsed p input #pm (v <: t))
      (PPB.pts_to_parsed (parse_fldata_strong s n) input #pm v)
    )
    #(pure (SZ.v (S.len input) == n))
    fn _ {
      unfold (PPB.pts_to_parsed p input #pm (v <: t));
      with w' . assert (S.pts_to input #pm w');
      S.pts_to_len input;
      parser_kind_prop_equiv (parse_fldata_kind n k) (parse_fldata_strong s n);
      parser_kind_prop_equiv (parse_fldata_kind n k) (parse_fldata p n);
      parser_kind_prop_equiv k p;
      Seq.lemma_eq_elim (Seq.slice w' 0 (Seq.length w')) w';
      parse_fldata_strong_correct s n w' (Seq.length w') (Ghost.reveal v <: t);
      fold (PPB.pts_to_parsed (parse_fldata_strong s n) input #pm v)
    }
}

inline_for_extraction
fn accessor_fldata_strong
  (#k: Ghost.erased parser_kind) (#t: Type0) (#p: parser k t)
  (s: serializer p)
  (n: Ghost.erased nat)
: PPB.accessor (parse_fldata_strong s n) p (clens_fldata_strong s n)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_fldata_strong_t s n))
{
  pts_to_parsed_fldata_strong_payload_trade s n input;
  input
}

#pop-options

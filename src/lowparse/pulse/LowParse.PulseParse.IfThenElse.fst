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

(* ========== IfThenElse accessor combinators ========== *)

include LowParse.CLens

let clens_ifthenelse_tag
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
: Tot (clens p.parse_ifthenelse_t p.parse_ifthenelse_tag_t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (x: p.parse_ifthenelse_t) -> dfst (s.serialize_ifthenelse_synth_recip x));
}

let clens_ifthenelse_payload
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (b: bool)
: Tot (clens p.parse_ifthenelse_t (p.parse_ifthenelse_payload_t b))
= {
  clens_cond = (fun (x: p.parse_ifthenelse_t) -> p.parse_ifthenelse_tag_cond (dfst (s.serialize_ifthenelse_synth_recip x)) == b);
  clens_get = (fun (x: p.parse_ifthenelse_t) ->
    (dsnd (s.serialize_ifthenelse_synth_recip x) <: Ghost (p.parse_ifthenelse_payload_t b)
      (requires (p.parse_ifthenelse_tag_cond (dfst (s.serialize_ifthenelse_synth_recip x)) == b))
      (ensures (fun _ -> True))));
}

#push-options "--z3rlimit 128"

(* IfThenElse accessor implementations.
   We abstract parser kinds and types to avoid Pulse's uvar solver limitation
   with computed parser kinds (parse_ifthenelse_kind). The tag accessor uses
   a generic tag_of_data function; the payload accessor uses generic parsers.
   Callers instantiate with the concrete IfThenElse parsers and proofs. *)

inline_for_extraction
fn accessor_ifthenelse_tag
  (#kp: Ghost.erased parser_kind)
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type0)
  (#data_t: Type0)
  (pt: parser kt tag_t)
  (pp: parser kp data_t)
  (tag_of_data: (data_t -> GTot tag_t))
  (j: LPS.jumper pt)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
  (parse_tag_eq: (input: bytes) -> Lemma
    (requires (Some? (parse pp input)))
    (ensures (Some? (parse pt input) /\ tag_of_data (fst (Some?.v (parse pp input))) == fst (Some?.v (parse pt input)))))
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased data_t)
  requires PPB.pts_to_parsed pp input #pm v
  returns result: S.slice byte
  ensures exists* v2 pm' .
    PPB.pts_to_parsed pt result #pm' v2 **
    pure (v2 == tag_of_data v) **
    Trade.trade
      (PPB.pts_to_parsed pt result #pm' v2)
      (PPB.pts_to_parsed pp input #pm v)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_tag_eq bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt pt;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  let off = j input 0sz;
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_r (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_tag #pm wb_tag) (S.pts_to input #pm bytes) (PPB.pts_to_parsed pp input #pm v);
  parse_strong_prefix pt bytes wb_tag;
  PPB.pts_to_parsed_intro pt input_tag (tag_of_data v);
  Trade.trans (PPB.pts_to_parsed pt input_tag #(pm /. 2.0R) (tag_of_data v)) (S.pts_to input_tag #pm wb_tag) (PPB.pts_to_parsed pp input #pm v);
  input_tag
}

inline_for_extraction
fn accessor_ifthenelse_payload'
  (#kp: Ghost.erased parser_kind)
  (#kt: Ghost.erased parser_kind)
  (#kpl: Ghost.erased parser_kind)
  (#tag_t: Type0)
  (#data_t: Type0)
  (#payload_t: Type0)
  (pt: parser kt tag_t)
  (pp: parser kp data_t)
  (ppl: parser kpl payload_t)
  (payload_of_data: (data_t -> GTot payload_t))
  (j: LPS.jumper pt)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
  (parse_payload_eq: (input: bytes) -> Lemma
    (requires (Some? (parse pp input)))
    (ensures (match parse pt input with
    | None -> False
    | Some (_, consumed) ->
      let input' = Seq.slice input consumed (Seq.length input) in
      Some? (parse ppl input') /\
      payload_of_data (fst (Some?.v (parse pp input))) == fst (Some?.v (parse ppl input')) /\
      consumed + snd (Some?.v (parse ppl input')) == snd (Some?.v (parse pp input)))))
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased data_t)
  requires PPB.pts_to_parsed pp input #pm v
  returns result: S.slice byte
  ensures exists* v2 pm' .
    PPB.pts_to_parsed ppl result #pm' v2 **
    pure (v2 == payload_of_data v) **
    Trade.trade
      (PPB.pts_to_parsed ppl result #pm' v2)
      (PPB.pts_to_parsed pp input #pm v)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_payload_eq bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt pt;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  let off = j input 0sz;
  let payload_bytes = Ghost.hide (Seq.slice bytes (SZ.v off) (Seq.length bytes));
  let gx = Ghost.hide (fst (Some?.v (parse ppl payload_bytes)));
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed pp input #pm v);
  Seq.lemma_eq_elim wb_payload (Ghost.reveal payload_bytes);
  PPB.pts_to_parsed_intro ppl input_payload gx;
  Trade.trans (PPB.pts_to_parsed ppl input_payload #(pm /. 2.0R) gx) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed pp input #pm v);
  input_payload
}

#pop-options

(* ========== Serializer-free IfThenElse accessor ========== *)

(* Type alias for synth_recip function (no serializer needed) *)
let ifthenelse_synth_recip_t (p: parse_ifthenelse_param) =
  p.parse_ifthenelse_t -> GTot (t: p.parse_ifthenelse_tag_t & p.parse_ifthenelse_payload_t (p.parse_ifthenelse_tag_cond t))

(* clens definitions using synth_recip directly *)

let clens_ifthenelse_tag_of
  (p: parse_ifthenelse_param)
  (synth_recip: ifthenelse_synth_recip_t p)
: Tot (clens p.parse_ifthenelse_t p.parse_ifthenelse_tag_t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (x: p.parse_ifthenelse_t) -> dfst (synth_recip x));
}

let clens_ifthenelse_payload_of
  (p: parse_ifthenelse_param)
  (synth_recip: ifthenelse_synth_recip_t p)
  (b: bool)
: Tot (clens p.parse_ifthenelse_t (p.parse_ifthenelse_payload_t b))
= {
  clens_cond = (fun (x: p.parse_ifthenelse_t) -> p.parse_ifthenelse_tag_cond (dfst (synth_recip x)) == b);
  clens_get = (fun (x: p.parse_ifthenelse_t) ->
    (dsnd (synth_recip x) <: Ghost (p.parse_ifthenelse_payload_t b)
      (requires (p.parse_ifthenelse_tag_cond (dfst (synth_recip x)) == b))
      (ensures (fun _ -> True))));
}

(* Helper: synth_recip applied to synth gives identity *)
let ifthenelse_synth_recip_inverse
  (p: parse_ifthenelse_param)
  (synth_recip: ifthenelse_synth_recip_t p)
  (synth_inverse: (x: p.parse_ifthenelse_t) -> Lemma
    (let (| t, y |) = synth_recip x in p.parse_ifthenelse_synth t y == x))
  (tg: p.parse_ifthenelse_tag_t)
  (pl: p.parse_ifthenelse_payload_t (p.parse_ifthenelse_tag_cond tg))
: Lemma (synth_recip (p.parse_ifthenelse_synth tg pl) == (| tg, pl |))
= synth_inverse (p.parse_ifthenelse_synth tg pl);
  let (| tg', pl' |) = synth_recip (p.parse_ifthenelse_synth tg pl) in
  p.parse_ifthenelse_synth_injective tg pl tg' pl'

(* Spec lemma: when parse_ifthenelse succeeds and the tag condition matches b,
   the payload parser for b succeeds and its result matches dsnd (synth_recip v) *)
let ifthenelse_payload_parse_eq
  (p: parse_ifthenelse_param)
  (synth_recip: ifthenelse_synth_recip_t p)
  (synth_inverse: (x: p.parse_ifthenelse_t) -> Lemma
    (let (| t, y |) = synth_recip x in p.parse_ifthenelse_synth t y == x))
  (b: bool)
  (input: bytes)
: Lemma
  (match parse (parse_ifthenelse p) input with
   | None -> True
   | Some (v, total_consumed) ->
     p.parse_ifthenelse_tag_cond (dfst (synth_recip v)) = b ==>
     (Some? (parse p.parse_ifthenelse_tag_parser input) /\
      (let consumed = snd (Some?.v (parse p.parse_ifthenelse_tag_parser input)) in
       let input' = Seq.slice input consumed (Seq.length input) in
       Some? (parse (dsnd (p.parse_ifthenelse_payload_parser b)) input') /\
       consumed + snd (Some?.v (parse (dsnd (p.parse_ifthenelse_payload_parser b)) input')) == total_consumed /\
       fst (Some?.v (parse (dsnd (p.parse_ifthenelse_payload_parser b)) input')) ==
         coerce (p.parse_ifthenelse_payload_t b) (dsnd (synth_recip v)))))
= match parse (parse_ifthenelse p) input with
  | None -> ()
  | Some (v, _) ->
    if p.parse_ifthenelse_tag_cond (dfst (synth_recip v)) = b then begin
      parse_ifthenelse_eq p input;
      let Some (tg, consumed) = parse p.parse_ifthenelse_tag_parser input in
      let input' = Seq.slice input consumed (Seq.length input) in
      let b' = p.parse_ifthenelse_tag_cond tg in
      let Some (pl, _) = parse (dsnd (p.parse_ifthenelse_payload_parser b')) input' in
      synth_inverse v;
      let (| t, y |) = synth_recip v in
      p.parse_ifthenelse_synth_injective tg pl t y
    end else ()

(* Accessor: given pts_to_parsed for a parse_ifthenelse value whose tag matches b,
   return a sub-slice containing the payload parsed by payload_parser b *)

#push-options "--z3rlimit 128"

inline_for_extraction
fn accessor_ifthenelse_payload
  (p: parse_ifthenelse_param)
  (synth_recip: ifthenelse_synth_recip_t p)
  (synth_inverse: (x: p.parse_ifthenelse_t) -> Lemma
    (let (| t, y |) = synth_recip x in p.parse_ifthenelse_synth t y == x))
  (j: LPS.jumper p.parse_ifthenelse_tag_parser)
  (b: bool)
  (sq: squash (p.parse_ifthenelse_tag_kind.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload_of p synth_recip b)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased p.parse_ifthenelse_t)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  ifthenelse_payload_parse_eq p synth_recip synth_inverse b w;
  S.pts_to_len input;
  parser_kind_prop_equiv p.parse_ifthenelse_tag_kind p.parse_ifthenelse_tag_parser;
  Seq.lemma_eq_elim (Seq.slice w 0 (Seq.length w)) w;
  let off = j input 0sz;
  let payload_bytes = Ghost.hide (Seq.slice w (SZ.v off) (Seq.length w));
  let gx = Ghost.hide (fst (Some?.v (parse (dsnd (p.parse_ifthenelse_payload_parser b)) payload_bytes)));
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm w);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm w) (PPB.pts_to_parsed (parse_ifthenelse p) input #pm v);
  Seq.lemma_eq_elim wb_payload (Ghost.reveal payload_bytes);
  PPB.pts_to_parsed_intro (dsnd (p.parse_ifthenelse_payload_parser b)) input_payload gx;
  Trade.trans (PPB.pts_to_parsed (dsnd (p.parse_ifthenelse_payload_parser b)) input_payload #(pm /. 2.0R) gx) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_ifthenelse p) input #pm v);
  input_payload
}

#pop-options

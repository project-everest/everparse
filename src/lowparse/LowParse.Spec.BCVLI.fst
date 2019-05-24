module LowParse.Spec.BCVLI
open LowParse.Spec.Combinators // for parse_ret

module U32 = FStar.UInt32
module Seq = FStar.Seq

inline_for_extraction
let parse_bcvli_payload_kind = {
  parser_kind_low = 0;
  parser_kind_high = Some 4;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let parse_bcvli_payload (x: bounded_integer 1) : Tot (parser parse_bcvli_payload_kind U32.t) =
  if U32.v x <= 252 then weaken parse_bcvli_payload_kind (parse_ret (x <: U32.t)) else
  if U32.v x = 253 then weaken parse_bcvli_payload_kind ((parse_bounded_integer_le 2 `parse_filter` (fun x -> U32.v x >= 253)) `parse_synth` (fun x -> (x <: U32.t))) else
  if U32.v x = 254 then weaken parse_bcvli_payload_kind ((parse_bounded_integer_le 4 `parse_filter` (fun x -> U32.v x >= 65536)) `parse_synth` (fun x -> (x <: U32.t))) else
  fail_parser parse_bcvli_payload_kind U32.t

#push-options "--z3rlimit 32"

let parse_bcvli_payload_and_then_cases_injective : squash (and_then_cases_injective parse_bcvli_payload) =
  and_then_cases_injective_intro parse_bcvli_payload (fun x1 x2 b1 b2 ->
    parse_synth_eq (parse_bounded_integer_le 2 `parse_filter` (fun x -> U32.v x >= 253)) (fun x -> (x <: U32.t)) b1;
    parse_synth_eq (parse_bounded_integer_le 2 `parse_filter` (fun x -> U32.v x >= 253)) (fun x -> (x <: U32.t)) b2;
    parse_synth_eq (parse_bounded_integer_le 4 `parse_filter` (fun x -> U32.v x >= 65536)) (fun x -> (x <: U32.t)) b1;
    parse_synth_eq (parse_bounded_integer_le 4 `parse_filter` (fun x -> U32.v x >= 65536)) (fun x -> (x <: U32.t)) b2
  )

#pop-options

let parse_bcvli : parser parse_bcvli_kind U32.t =
  parse_bounded_integer_le 1 `and_then` parse_bcvli_payload

let parse_bcvli_eq
b
= and_then_eq (parse_bounded_integer_le 1) parse_bcvli_payload b;
  match parse (parse_bounded_integer_le 1) b with
  | None -> ()
  | Some (x32, consumed_x) ->
    let b' = Seq.slice b consumed_x (Seq.length b) in
    parse_synth_eq (parse_bounded_integer_le 2 `parse_filter` (fun x -> U32.v x >= 253)) (fun x -> (x <: U32.t)) b';
    parse_filter_eq (parse_bounded_integer_le 2) (fun x -> U32.v x >= 253) b';
    parse_synth_eq (parse_bounded_integer_le 4 `parse_filter` (fun x -> U32.v x >= 65536)) (fun x -> (x <: U32.t)) b';
    parse_filter_eq (parse_bounded_integer_le 4) (fun x -> U32.v x >= 65536) b'

let bare_serialize_bcvli (x: U32.t) : GTot bytes =
  let c1 : bounded_integer 1 =
    if U32.v x <= 252 then
      x
    else if U32.v x <= 65535 then
      253ul
    else
      254ul
  in
  Seq.append
    (serialize (serialize_bounded_integer_le 1) c1)
    (
      if U32.v c1 <= 252 then Seq.empty else
      if U32.v c1 = 253 then serialize (serialize_bounded_integer_le 2) x else
      serialize (serialize_bounded_integer_le 4) x
    )

#push-options "--z3rlimit 32"

let bare_serialize_bcvli_correct : squash
  (serializer_correct parse_bcvli bare_serialize_bcvli)
= let prf (x: U32.t) : Lemma
    (let y = bare_serialize_bcvli x in
     parse parse_bcvli y == Some (x, Seq.length y))
  = let y = bare_serialize_bcvli x in
    let c1 : bounded_integer 1 =
      if U32.v x <= 252 then
        x
      else if U32.v x <= 65535 then
        253ul
      else
        254ul
    in
    let sc1 = serialize (serialize_bounded_integer_le 1) c1 in
    parse_strong_prefix (parse_bounded_integer_le 1) sc1 y;
    let y' = Seq.slice y (Seq.length sc1) (Seq.length y) in
    parse_bcvli_eq y;
    if U32.v c1 <= 252 then begin
      assert (y `Seq.equal` sc1)
    end else if U32.v c1 = 253 then begin
      assert (U32.v x <= 65535);
      assert (y' `Seq.equal` serialize (serialize_bounded_integer_le 2) x)
    end else begin
      assert (y' `Seq.equal` serialize (serialize_bounded_integer_le 4) x)
    end
  in
  Classical.forall_intro (Classical.move_requires prf)

#pop-options

let serialize_bcvli : serializer parse_bcvli = bare_serialize_bcvli

let serialize_bcvli_eq x = ()

let parse_bounded_bcvli'
  (min: nat)
  (max: nat { min <= max })
: Tot (parser (parse_filter_kind parse_bcvli_kind) (bounded_int32 min max))
= parse_filter parse_bcvli (in_bounds min max)

let parse_bounded_bcvli_size_correct
  (min: nat)
  (max: nat { min <= max })
: Lemma
  (parse_bounded_bcvli_size min `parses_at_least` parse_bounded_bcvli' min max /\
    parse_bounded_bcvli_size max `parses_at_most` parse_bounded_bcvli' min max)
= Classical.forall_intro (parse_filter_eq parse_bcvli (in_bounds min max));
  Classical.forall_intro parse_bcvli_eq;
  parser_kind_prop_equiv (parse_bounded_integer_kind 1) (parse_bounded_integer_le 1);
  parser_kind_prop_equiv (parse_bounded_integer_kind 2) (parse_bounded_integer_le 2);
  parser_kind_prop_equiv (parse_bounded_integer_kind 4) (parse_bounded_integer_le 4)

let parse_bounded_bcvli_kind_correct
  (min: nat)
  (max: nat { min <= max })
: Lemma
  (parser_kind_prop (parse_bounded_bcvli_kind min max) (parse_bounded_bcvli' min max))
= parse_bounded_bcvli_size_correct min max;
  parser_kind_prop_equiv (parse_filter_kind parse_bcvli_kind) (parse_bounded_bcvli' min max);
  parser_kind_prop_equiv (parse_bounded_bcvli_kind min max) (parse_bounded_bcvli' min max)

let parse_bounded_bcvli
  min max
= parse_bounded_bcvli_kind_correct min max;
  strengthen (parse_bounded_bcvli_kind min max) (parse_bounded_bcvli' min max)

let parse_bounded_bcvli_eq
  min max input
= parse_filter_eq parse_bcvli (in_bounds min max) input;
  parse_bcvli_eq input

let serialize_bounded_bcvli
  min max
= assert_norm (parse_filter_refine (in_bounds min max) == bounded_int32 min max);
  serialize_ext
    _
    (serialize_filter serialize_bcvli (in_bounds min max))
    (parse_bounded_bcvli min max)

let serialize_bounded_bcvli_eq
  min max x
= ()

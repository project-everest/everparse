module LowParseExample.Aux

module LP = LowParse.SLow
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module L = FStar.List.Tot

noeq
type t =
  | A of (U8.t * U8.t)
  | B of U16.t

type cases =
  | Case_A
  | Case_B

inline_for_extraction
let case_enum : LP.enum cases U8.t =
  [@inline_let]
  let e : list (cases * U8.t) = [
    Case_A, 18uy;
    Case_B, 42uy;
  ]
  in
  [@inline_let]
  let _ : squash (L.noRepeats (L.map fst e) /\ L.noRepeats (L.map snd e)) =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in
  e

inline_for_extraction
let cases_of_t
  (x: t)
: Tot cases
= match x with
  | A _ -> Case_A
  | B _ -> Case_B

inline_for_extraction
let t_sum
= LP.make_sum case_enum cases_of_t

inline_for_extraction
let synth_case_A (z: (U8.t * U8.t)) : Tot (LP.sum_cases t_sum Case_A) =
  [@inline_let]
  let res : t = A z in
  [@inline_let]
  let _ : squash (LP.sum_tag_of_data t_sum res == Case_A) =
    assert_norm (LP.sum_tag_of_data t_sum res == Case_A)
  in
  res

inline_for_extraction
let synth_case_B (z: (U16.t)) : Tot (LP.sum_cases t_sum Case_B) =
  [@inline_let]
  let res : t = B z in
  [@inline_let]
  let _ : squash (LP.sum_tag_of_data t_sum res == Case_B) =
    assert_norm (LP.sum_tag_of_data t_sum res == Case_B)
  in
  res
  
let parse_cases
  (x: LP.sum_key t_sum)
: Tot (LP.parser LP.parse_u16_kind  (LP.sum_cases t_sum x))
= match x with
  | Case_A ->
    LP.parse_synth (LP.parse_u8 `LP.nondep_then` LP.parse_u8) synth_case_A
  | Case_B ->
    LP.parse_synth LP.parse_u16 synth_case_B

inline_for_extraction
let parse32_cases
  (x: LP.sum_key t_sum)
: Tot (LP.parser32 (parse_cases x))
= match x with
  | Case_A ->
    LP.parse32_synth
      _
      synth_case_A
      (fun x -> synth_case_A x)
      (LP.parse32_nondep_then LP.parse32_u8 LP.parse32_u8)
      ()
  | Case_B ->
    LP.parse32_synth
      _
      synth_case_B
      (fun x -> synth_case_B x)
      LP.parse32_u16
      ()

let parse_t : LP.parser _ t =
  LP.parse_sum t_sum LP.parse_u8 parse_cases

inline_for_extraction
let parse32_t
: LP.parser32 parse_t
= FStar.Tactics.synth_by_tactic
    (LP.parse32_sum_tac
      t_sum
      LP.parse32_u8
      parse32_cases
      parse_t
      ()
    )

module LowParse.Spec.RecursiveGen

open LowParse.Spec.Combinators
open LowParse.Spec.Fuel

module Seq = FStar.Seq

let parse_rec_gen_aux_ext
  (p: parse_rec_gen_param)
  (ih1 ih2: tot_parser (parse_rec_gen_kind p.header_kind) p.t)
  (b: bytes)
  (prf: (
    (b': bytes { Seq.length b' < Seq.length b }) -> // IMPORTANT: lt, not leq, to make induction work
    Lemma
    (parse ih1 b' == parse ih2 b')
  ))
: Lemma
  (parse (parse_rec_gen_aux p ih1) b == parse (parse_rec_gen_aux p ih2) b)
= p.synth_inj;
  tot_parse_synth_eq (parse_rec_gen_alt p ih1) p.synth_ b;
  tot_parse_synth_eq (parse_rec_gen_alt p ih2) p.synth_ b;
  match parse p.parse_header b with
  | None -> ()
  | Some (h, consumed) ->
    parser_kind_prop_equiv p.header_kind p.parse_header;
    let b' = Seq.slice b consumed (Seq.length b) in
    Classical.forall_intro (Classical.move_requires prf);
    assert (parse_rec_gen_ih_agree ih1 ih2 b');
    p.payload_ext ih1 ih2 h b'

let rec parse_rec_gen_step
  (p: parse_rec_gen_param)
  (n: nat)
: Tot (tot_parser (parse_rec_gen_kind p.header_kind) p.t)
= if n = 0
  then tot_fail_parser _ _
  else parse_rec_gen_aux p (parse_rec_gen_step p (n - 1))

let closure
  (b: bytes)
: Tot (n: nat { Seq.length b < n })
= Seq.length b + 1

let rec parse_rec_gen_step_ext_gen
  (p: parse_rec_gen_param)
  (fuel: nat)
  (fuel': nat { fuel <= fuel' })
  (input: bytes { Seq.length input < fuel })
: Lemma
  (ensures (parse (parse_rec_gen_step p fuel) input == parse (parse_rec_gen_step p fuel') input))
  (decreases fuel)
= parse_rec_gen_aux_ext
    p
    (parse_rec_gen_step p (fuel - 1))
    (parse_rec_gen_step p (fuel' - 1))
    input
    (fun input' ->
      parse_rec_gen_step_ext_gen p (fuel - 1) (fuel' - 1) input'
    )

let parse_rec_gen_step_ext
  (p: parse_rec_gen_param)
  (fuel: nat)
  (input: bytes { Seq.length input < fuel })
: Lemma
  (ensures (parse (parse_rec_gen_step p fuel) input == parse (parse_rec_gen_step p (closure input)) input))
= parse_rec_gen_step_ext_gen p (closure input) fuel input

let parse_rec_gen
  p
= tot_close_by_fuel (parse_rec_gen_step p) closure (parse_rec_gen_step_ext p)

let parse_rec_gen_eq
  p b
= let c = closure b in
  let q = parse_rec_gen_step p (c - 1) in
  assert (parse (parse_rec_gen p) b == parse (parse_rec_gen_aux p q) b);
  parse_rec_gen_aux_ext p q (parse_rec_gen p) b (fun input' ->
    parse_rec_gen_step_ext p (c - 1) input'
  )

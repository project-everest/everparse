module CBOR.SteelST.SimpleValue
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Type

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let destr_cbor_simple_value
  #p #va c
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Simple_value c' _ ->
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_simple_value0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_simple_value0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs _ ->
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_serialized0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse CborST.parse_raw_data_item a _) cs.cbor_serialized_payload;
    let c' = CborST.read_simple_value cs.cbor_serialized_payload in
    elim_implies
      (raw_data_item_match_serialized0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'

let size_comp_for_simple_value
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Simple? va })
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let c' = destr_cbor_simple_value c in
    let res = CBOR.SteelST.Raw.Write.size_comp_simple_value c' sz perr in
    let _ = gen_elim () in
    return res

let l2r_writer_for_simple_value
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Simple? va })
: Tot (cbor_l2r_writer_for va c)
= fun out ->
    let c' = destr_cbor_simple_value c in
    let res = CBOR.SteelST.Raw.Write.l2r_write_simple_value c' out in
    let _ = gen_elim () in
    return res

let constr_cbor_simple_value
  value
= let fp = GR.alloc () in
  [@@inline_let]
  let c = CBOR_Case_Simple_value value fp in
  noop ();
  rewrite
    (raw_data_item_match_simple_value0 full_perm c (Cbor.Simple value))
    (raw_data_item_match full_perm c (Cbor.Simple value));
  return c

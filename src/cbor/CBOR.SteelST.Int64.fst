module CBOR.SteelST.Int64
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Type

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let destr_cbor_int64
  #p #va c
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 c' fp ->
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_int0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_int0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs fp ->
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_serialized0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse CborST.parse_raw_data_item a _) cs.cbor_serialized_payload;
    let typ = CborST.read_major_type cs.cbor_serialized_payload in
    let value = CborST.read_int64 cs.cbor_serialized_payload in
    let c' : cbor_int = {
      cbor_int_type = typ;
      cbor_int_value = value;
    }
    in
    noop ();
    elim_implies
      (raw_data_item_match_serialized0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'

let size_comp_for_int64
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Int64? va })
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let c' = destr_cbor_int64 c in
    let res = CBOR.SteelST.Raw.Write.size_comp_int64 c'.cbor_int_type c'.cbor_int_value sz perr in
    let _ = gen_elim () in
    return res

let l2r_writer_for_int64
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Int64? va })
: Tot (cbor_l2r_writer_for va c)
= fun out ->
    let c' = destr_cbor_int64 c in
    let res = CBOR.SteelST.Raw.Write.l2r_write_int64 c'.cbor_int_type c'.cbor_int_value out in
    let _ = gen_elim () in
    return res

let constr_cbor_int64
  ty value
= let fp = GR.alloc () in
  [@@inline_let]
  let c = CBOR_Case_Int64 ({ cbor_int_type = ty; cbor_int_value = value }) fp in
  noop ();
  rewrite
    (raw_data_item_match_int0 full_perm c (Cbor.Int64 ty value))
    (raw_data_item_match full_perm c (Cbor.Int64 ty value));
  return c

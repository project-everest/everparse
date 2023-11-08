module CBOR.SteelST.String
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Type

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let destr_cbor_string
  #p #va c
= raw_data_item_match_get_case c;
  if CBOR_Case_String? c
  then begin
    noop ();
    noop ();
    let CBOR_Case_String c' fp p' = c in
    rewrite_with_implies
      (raw_data_item_match p c (Ghost.reveal va))
      (raw_data_item_match_string0 p c (Ghost.reveal va));
    let _ = gen_elim () in
    let vc' = vpattern_erased (A.pts_to _ _) in
    let np = p `prod_perm` p' in
    rewrite (A.pts_to _ _ _) (A.pts_to c'.cbor_string_payload np vc');
    intro_implies
      (A.pts_to c'.cbor_string_payload np vc')
      (raw_data_item_match_string0 p c (Ghost.reveal va))
      (GR.pts_to _ _ _)
      (fun _ ->
        noop ();
        noop ()
      );
    implies_trans
      (A.pts_to c'.cbor_string_payload np vc')
      (raw_data_item_match_string0 p c (Ghost.reveal va))
      (raw_data_item_match p c (Ghost.reveal va));
    return c'
  end else begin
    noop ();
    noop ();
    let cs = destr_cbor_serialized c in
    let _ = gen_elim () in
    let typ = CborST.read_major_type cs.cbor_serialized_payload in
    let len = CborST.read_argument_as_uint64 cs.cbor_serialized_payload in
    let lpayload = CborST.focus_string cs.cbor_serialized_payload in
    let _ = gen_elim () in
    implies_trans
      (LPA.arrayptr _ _)
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match _ _ _);
    let payload = LPA.elim_arrayptr_with_implies lpayload in
    let _ = gen_elim () in
    implies_trans
      (A.pts_to payload _ _)
      (LPA.arrayptr _ _)
      (raw_data_item_match _ _ _);
    [@@inline_let]
    let c' : cbor_string = {
      cbor_string_type = typ;
      cbor_string_length = len;
      cbor_string_payload = payload;
    }
    in
    vpattern_rewrite_with_implies
      (fun a -> A.pts_to a _ _)
      c'.cbor_string_payload;
    implies_trans
      (A.pts_to _ _ _)
      (A.pts_to _ _ _)
      (raw_data_item_match _ _ _);
    return c'
  end

#push-options "--z3rlimit 64"
#restart-solver

let size_comp_for_string
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.String? va })
: Tot (cbor_size_comp_for va c)
= fun #p sz perr ->
    let _ = A.intro_fits_u64 () in
    let c' = destr_cbor_string c in
    let _ = gen_elim () in
    let res = CBOR.SteelST.Raw.Write.size_comp_string c'.cbor_string_type c'.cbor_string_length (Cbor.String?.v va) sz perr in
    let _ = gen_elim () in
    elim_implies
      (A.pts_to _ _ _)
      (raw_data_item_match p _ _);
    return res

let serialize_cbor_string_eq
  (c: Cbor.raw_data_item { Cbor.String? c })
: Lemma
  (
    let s0 = LPS.serialize CborST.serialize_raw_data_item c in
    let s1 = LPS.serialize CborST.serialize_header (CborST.uint64_as_argument (Cbor.String?.typ c) (U64.uint_to_t (Seq.length (Cbor.String?.v c)))) in
    s0 == s1 `Seq.append` Cbor.String?.v c
  )
= CborST.serialize_raw_data_item_aux_correct c;
  LPS.serialize_synth_eq
    _
    CborST.synth_raw_data_item
    (LPS.serialize_dtuple2 CborST.serialize_header CborST.serialize_content)
    CborST.synth_raw_data_item_recip
    ()
    c;
  LPS.serialize_dtuple2_eq CborST.serialize_header CborST.serialize_content (CborST.synth_raw_data_item_recip c)

let l2r_write_cbor_string
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {Cbor.String? va})
: Tot (cbor_l2r_writer_for va c)
= fun #p #vout out ->
  let _ = A.intro_fits_u64 () in
  serialize_cbor_string_eq va;
  noop ();
  let c' = destr_cbor_string c in
  let _ = gen_elim () in
  let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header c'.cbor_string_type c'.cbor_string_length out in
  let _ = gen_elim () in
  let _ = LPS.elim_aparse_with_serializer CborST.serialize_header res in
  let len = SZ.uint64_to_sizet c'.cbor_string_length in
  let res_pl = LW.split out len in
  let _ = gen_elim () in
  let vout' = vpattern_replace (LW.vp out) in
  let vres_pl = vpattern (LPA.arrayptr res_pl) in
  let res_pl_a = LPA.elim_arrayptr res_pl in
  vpattern_rewrite (fun p -> A.pts_to res_pl_a p _) full_perm;
  A.pts_to_length c'.cbor_string_payload _;
  A.pts_to_length res_pl_a _;
  let _ = A.memcpy c'.cbor_string_payload res_pl_a len in
  let res_pl = LPA.intro_arrayptr res_pl_a in
  let _ = gen_elim () in
  let vres_pl' = vpattern (LPA.arrayptr res_pl) in
  LPA.array_equal (LPA.array_of vres_pl) (LPA.array_of vres_pl');
  noop ();
  let _ = LPA.join res res_pl in
  let vres = LPS.intro_aparse_with_serializer CborST.serialize_raw_data_item va res in
  elim_implies
    (A.pts_to _ _ _)
    (raw_data_item_match p c (Ghost.reveal va));
  assert_ (cbor_l2r_writer_for_post p va c vout out res vres vout'); // FIXME: WHY WHY WHY?
  return res

#pop-options

let constr_cbor_string
  #va #p typ a len
= let fp = GR.alloc () in
  [@@inline_let]
  let c' = CBOR_Case_String
    ({
      cbor_string_type = typ;
      cbor_string_payload = a;
      cbor_string_length = len;
    })
    fp
    p
  in
  noop ();
  rewrite_with_implies
    (raw_data_item_match_string0 full_perm c' (Cbor.String typ va))
    (raw_data_item_match full_perm c' (Cbor.String typ va));
  intro_implies
    (raw_data_item_match_string0 full_perm c' (Cbor.String typ va))
    (A.pts_to a p va)
    emp
    (fun _ ->
      let _ = gen_elim () in
      GR.free _;
      rewrite (A.pts_to _ _ _) (A.pts_to a p va)
    );
  implies_trans
    (raw_data_item_match full_perm c' (Cbor.String typ (va)))
    (raw_data_item_match_string0 full_perm c' (Cbor.String typ (va)))
    (A.pts_to a p va);
  return c'

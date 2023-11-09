module CBOR.SteelST.Tagged
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Match
open CBOR.SteelST.Type.Def

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let destr_cbor_tagged0
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_tagged0
    (raw_data_item_match p a v)
    (fun res ->
      R.pts_to res.cbor_tagged0_payload p res.footprint `star`
      raw_data_item_match p res.footprint (maybe_cbor_tagged_payload v) `star`
      ((R.pts_to res.cbor_tagged0_payload p res.footprint `star`
        raw_data_item_match p res.footprint (maybe_cbor_tagged_payload v)) `implies_`
        raw_data_item_match p a v
      )
    )
    (CBOR_Case_Tagged? a)
    (fun res ->
      a == CBOR_Case_Tagged res /\
      Cbor.Tagged? v /\
      res.cbor_tagged0_tag == Cbor.Tagged?.tag v
    )
= raw_data_item_match_get_case _;
  let _ : squash (Cbor.Tagged? v) = () in
  let g_tag = Ghost.hide (Cbor.Tagged?.tag v) in
  let g_payload = Ghost.hide (Cbor.Tagged?.v v) in
  let CBOR_Case_Tagged res = a in
  rewrite_with_implies
    (raw_data_item_match p a v)
    (raw_data_item_match p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload));
  rewrite_with_implies_with_tactic
    (raw_data_item_match p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload))
    (raw_data_item_match_tagged0 p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload) (raw_data_item_match p));
  implies_trans
    (raw_data_item_match_tagged0 p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload) (raw_data_item_match p))
    (raw_data_item_match p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload))
    (raw_data_item_match p a v);
  let _ = gen_elim () in
  let _ : squash (res.cbor_tagged0_tag == Ghost.reveal g_tag) = () in
  let _ : squash (maybe_cbor_tagged_payload v == Ghost.reveal g_payload) = () in
  let _ : squash (Ghost.reveal g_payload << Cbor.Tagged g_tag g_payload) = () in // FIXME: WHY WHY WHY?
  rewrite (R.pts_to _ _ _) (R.pts_to res.cbor_tagged0_payload p res.footprint);
  rewrite (raw_data_item_match p _ _) (raw_data_item_match p res.footprint (maybe_cbor_tagged_payload v));
  intro_implies
    (R.pts_to res.cbor_tagged0_payload p res.footprint `star`
      raw_data_item_match p res.footprint (maybe_cbor_tagged_payload v))
    (raw_data_item_match p a v)
    (raw_data_item_match_tagged0 p _ _ (raw_data_item_match p) `implies_` raw_data_item_match p a _)
    (fun _ ->
      elim_implies
        (raw_data_item_match_tagged0 p (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload) (raw_data_item_match p))
        (raw_data_item_match p a _)
    );
  return res

#push-options "--z3rlimit 64"
#restart-solver

let destr_cbor_tagged
  #p #v a
=
  raw_data_item_match_get_case a;
  match a with
  | CBOR_Case_Tagged _ ->
    let r = destr_cbor_tagged0 a in
    let pl = R.read r.cbor_tagged0_payload in
    implies_consumes_l
      (R.pts_to _ _ _)
      (raw_data_item_match _ _ _)
      (raw_data_item_match _ _ _);
    let res = {
      cbor_tagged_tag = r.cbor_tagged0_tag;
      cbor_tagged_payload = pl;
    }
    in
    vpattern_rewrite_with_implies
      (fun pl -> raw_data_item_match p pl _)
      res.cbor_tagged_payload;
    implies_trans
      (raw_data_item_match p _ (maybe_cbor_tagged_payload v))
      (raw_data_item_match p _ (maybe_cbor_tagged_payload v))
      (raw_data_item_match p a v);
    return res
  | _ ->
    raw_data_item_match_perm_le_full_perm a;
    let s = destr_cbor_serialized a in
    let _ = gen_elim () in
    let tag = CBOR.SteelST.Raw.read_argument_as_uint64 s.cbor_serialized_payload in
    let s' = CBOR.SteelST.Raw.Read.focus_tagged s.cbor_serialized_payload in
    let _ = gen_elim () in
    implies_trans
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match p _ _);
    let sz = LPS.get_parsed_size CborST.jump_raw_data_item s' in
    let pl = read_valid_cbor_from_buffer_with_size_strong p s' sz in
    implies_trans
      (raw_data_item_match p _ _)
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match p _ _);
    [@@inline_let]
    let res = {
      cbor_tagged_tag = tag;
      cbor_tagged_payload = pl;
    }
    in
    rewrite_with_implies
      (raw_data_item_match p _ _)
      (raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v));
    implies_trans
      (raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v))
      (raw_data_item_match p _ _)
      (raw_data_item_match p a v);
    return res

let constr_cbor_tagged
  #c' #v' tag a
= [@@inline_let]
  let res_tg = {
    cbor_tagged0_tag = tag;
    cbor_tagged0_payload = a;
    footprint = c';
  }
  in
  [@@inline_let]
  let prf () : squash (Ghost.reveal v' << Cbor.Tagged tag v') =
    let w = Cbor.Tagged tag v' in
    match w with
    | Cbor.Tagged _ v_ -> assert (v_ << w)
  in
  [@@inline_let]
  let _ = prf () in
  noop ();
  rewrite_with_implies_with_tactic
    (raw_data_item_match_tagged0 full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v') (raw_data_item_match full_perm))
    (raw_data_item_match full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v'));
  intro_implies
    (raw_data_item_match_tagged0 full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v') (raw_data_item_match full_perm))
    (R.pts_to a full_perm c' `star`
      raw_data_item_match full_perm c' v')
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite
        (R.pts_to _ _ _)
        (R.pts_to a full_perm c');
      rewrite
        (raw_data_item_match full_perm _ _)
        (raw_data_item_match full_perm c' v')
    );
  implies_trans
    (raw_data_item_match full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v'))
    (raw_data_item_match_tagged0 full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v') (raw_data_item_match full_perm))
    (R.pts_to a full_perm c' `star`
      raw_data_item_match full_perm c' v');
  [@@inline_let]
  let res = CBOR_Case_Tagged res_tg in
  rewrite_with_implies
    (raw_data_item_match full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v'))
    (raw_data_item_match full_perm res (Cbor.Tagged tag v'));
  implies_trans
    (raw_data_item_match full_perm res (Cbor.Tagged tag v'))
    (raw_data_item_match full_perm (CBOR_Case_Tagged res_tg) (Cbor.Tagged tag v'))
    (R.pts_to a full_perm c' `star`
      raw_data_item_match full_perm c' v');
  return res

let serialize_cbor_tagged_eq
  (c: Cbor.raw_data_item { Cbor.Tagged? c })
: Lemma
  (
    let s0 = LPS.serialize CborST.serialize_raw_data_item c in
    let s1 = LPS.serialize CborST.serialize_header (CborST.uint64_as_argument Cbor.major_type_tagged (Cbor.Tagged?.tag c)) in
    let s2 = LPS.serialize CborST.serialize_raw_data_item (Cbor.Tagged?.v c) in
    s0 == s1 `Seq.append` s2 /\ Seq.length s0 == Seq.length s1 + Seq.length s2
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

inline_for_extraction
noextract
let size_comp_for_tagged
  (size:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_size_comp_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Tagged? c})
: Tot (cbor_size_comp_for va c)
= fun #p sz perr ->
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Tagged? va) = () in
    serialize_cbor_tagged_eq va;
    let c' = destr_cbor_tagged c in
    let sz1 = CBOR.SteelST.Raw.Write.size_comp_uint64_header Cbor.major_type_tagged c'.cbor_tagged_tag sz perr in
    let _ = gen_elim () in
    let err1 = R.read perr in
    if err1
    then begin
      noop ();
      elim_implies
        (raw_data_item_match p _ _)
        (raw_data_item_match p _ _);
      return sz1
    end else begin
      noop ();
      let sz2 = size _ c'.cbor_tagged_payload sz1 perr in
      let _ = gen_elim () in
      elim_implies
        (raw_data_item_match p _ _)
        (raw_data_item_match p _ _);
      return sz2
    end

inline_for_extraction
noextract
let l2r_writer_for_tagged
  (write:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_l2r_writer_for va c
  )
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Tagged? c})
: Tot (cbor_l2r_writer_for va c)
= fun #p #vout out ->
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Tagged? va) = () in
    serialize_cbor_tagged_eq va;
    let c' = destr_cbor_tagged c in
    let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header Cbor.major_type_tagged c'.cbor_tagged_tag out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer CborST.serialize_header res in
    let res_pl = write _ c'.cbor_tagged_payload out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer CborST.serialize_raw_data_item res_pl in
    let _ = LPA.join res res_pl in
    let vres = LPS.intro_aparse_with_serializer CborST.serialize_raw_data_item va res in
    let vout' = vpattern_replace (LW.vp out) in
    elim_implies
      (raw_data_item_match p _ _)
      (raw_data_item_match p _ _);
    assert_ (cbor_l2r_writer_for_post p va c vout out res vres vout'); // FIXME: WHY WHY WHY?
    return res


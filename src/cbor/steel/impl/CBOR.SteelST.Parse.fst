module CBOR.SteelST.Parse
open Steel.ST.OnRange
open Steel.ST.GenElim
friend CBOR.SteelST.Match
open CBOR.SteelST.Type.Def

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let serialize_cbor_error
  (x: Seq.seq U8.t)
: Lemma
  (requires (LPS.parse CborST.parse_raw_data_item x == None))
  (ensures (cbor_read_error_postcond x))
= let prf
    (v: Cbor.raw_data_item)
    (suff: Seq.seq U8.t)
  : Lemma
    (requires (x == Cbor.serialize_cbor v `Seq.append` suff))
    (ensures False)
  = LPS.parse_strong_prefix CborST.parse_raw_data_item (Cbor.serialize_cbor v) x
  in
  Classical.forall_intro_2 (fun v suff -> Classical.move_requires (prf v) suff)

#push-options "--z3rlimit 64"
#restart-solver

let cbor_read'
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (a: A.array U8.t)
  (sz: SZ.t)
: ST cbor_read_t
    (A.pts_to a p va)
    (fun res -> cbor_read_post a p va res)
    (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    (fun res ->
      res.cbor_read_is_success == true ==> CBOR_Case_Serialized? res.cbor_read_payload
    )
= A.pts_to_length a _;
  let a' = LPA.intro_arrayptr_with_implies a in
  let _ = gen_elim () in
  let va' = vpattern (LPA.arrayptr a') in
  vpattern_rewrite_with_implies (LPA.arrayptr a') va';
  implies_trans
    (LPA.arrayptr a' va')
    (LPA.arrayptr a' _)
    (A.pts_to a p va);
  let res = R.with_local 0ul #_ #(res: cbor_read_t {
      res.cbor_read_is_success == true ==> CBOR_Case_Serialized? res.cbor_read_payload
  }) (fun perr ->
    let sz' = CborST.validate_raw_data_item a' sz perr in
    let _ = gen_elim () in
    let err = R.read perr in
    if err = 0ul
    then begin
      noop ();
      LPS.parsed_data_is_serialize CborST.serialize_raw_data_item va;
      let rem' = LPS.peek_strong_with_size_with_implies CborST.parse_raw_data_item a' sz' in
      let _ = gen_elim () in
      implies_trans
        (LPS.aparse CborST.parse_raw_data_item a' _ `star` LPA.arrayptr rem' _)
        (LPA.arrayptr a' _)
        (A.pts_to a p va);
      let vpl = vpattern (LPS.aparse CborST.parse_raw_data_item a') in
      let vrem = vpattern (LPA.arrayptr rem') in
      let rem = LPA.elim_arrayptr_with_implies rem' in
      A.pts_to_length rem _;
      vpattern_rewrite_with_implies (fun p -> A.pts_to rem p _) p;
      implies_trans
        (A.pts_to rem p _)
        (A.pts_to rem _ _)
        (LPA.arrayptr rem' _);
      implies_trans_r1 
        (LPS.aparse CborST.parse_raw_data_item a' _)
        (A.pts_to rem p _)
        (LPA.arrayptr rem' _)
        (A.pts_to a p va);
      let c = read_valid_cbor_from_buffer_with_size_strong full_perm a' sz' in
      implies_trans_l1
        (raw_data_item_match full_perm c _)
        (LPS.aparse CborST.parse_raw_data_item a' _)
        (A.pts_to rem p _)
        (A.pts_to a p va);
      [@@inline_let]
      let res = {
        cbor_read_is_success = true;
        cbor_read_payload = c;
        cbor_read_remainder = rem;
        cbor_read_remainder_length = sz `SZ.sub` sz';
      }
      in
      vpattern_rewrite_with_implies
        (fun c -> raw_data_item_match full_perm c _)
        res.cbor_read_payload;
      implies_trans_l1
        (raw_data_item_match full_perm res.cbor_read_payload _)
        (raw_data_item_match full_perm c _)
        (A.pts_to rem p _)
        (A.pts_to a p va);
      vpattern_rewrite_with_implies
        (fun rem -> A.pts_to rem p _)
        res.cbor_read_remainder;
      implies_trans_r1
        (raw_data_item_match full_perm res.cbor_read_payload _)
        (A.pts_to res.cbor_read_remainder _ _)
        (A.pts_to rem _ _)
        (A.pts_to a p va);
      rewrite
        (cbor_read_success_post a p va res)
        (cbor_read_post a p va res);
      return res
    end else begin
      noop ();
      serialize_cbor_error va;
      [@@inline_let]
      let res = {
        cbor_read_is_success = false;
        cbor_read_payload = cbor_dummy;
        cbor_read_remainder = a;
        cbor_read_remainder_length = sz;
      }
      in
      noop ();
      elim_implies
        (LPA.arrayptr a' va')
        (A.pts_to a p va);
      rewrite
        (cbor_read_error_post a p va)
        (cbor_read_post a p va res);
      return res
    end
  )
  in
  return res

#pop-options

let cbor_read
  #va #p a sz
= cbor_read' a sz

let serialize_deterministically_encoded_cbor_error
  (x: Seq.seq U8.t)
  (c: cbor_read_t)
  (v0: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Lemma
  (requires (
    cbor_read_success_postcond x c v0 rem /\
    Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v0 == false
  ))
  (ensures (cbor_read_deterministically_encoded_error_postcond x))
= Cbor.serialize_cbor_with_test_correct v0 rem (fun c' _ -> Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order c' == true)

let cbor_read_deterministically_encoded
  #va #p a sz
= A.pts_to_length a _;
  let _ = A.intro_fits_u64 () in
  let res = cbor_read' a sz in
  if not res.cbor_read_is_success
  then begin
    rewrite
      (cbor_read_post a p va res)
      (cbor_read_error_post a p va);
    let _ = gen_elim () in
    rewrite
      (cbor_read_deterministically_encoded_error_post a p va)
      (cbor_read_deterministically_encoded_post a p va res);
    return res
  end else begin
    rewrite
      (cbor_read_post a p va res)
      (cbor_read_success_post a p va res);
    let _ = gen_elim () in
    let s = destr_cbor_serialized res.cbor_read_payload in
    let _ = gen_elim () in
    let test = CBOR.SteelST.Raw.Map.check_raw_data_item
      (CBOR.SteelST.Raw.Map.check_data_item_wf_head CBOR.SteelST.Raw.Map.deterministically_encoded_cbor_map_key_order_impl ())
      s.cbor_serialized_payload
    in
    elim_implies
      (LPS.aparse CborST.parse_raw_data_item _ _)
      (raw_data_item_match full_perm _ _);
    if test
    then begin
      noop ();
      noop (); // FIXME: WHY WHY WHY do I need that many noop()s ?
      rewrite
        (cbor_read_deterministically_encoded_success_post a p va res)
        (cbor_read_deterministically_encoded_post a p va res);
      return res
    end else begin
      let v = vpattern_erased (raw_data_item_match full_perm _) in
      let rem = vpattern_erased (A.pts_to _ _) in
      serialize_deterministically_encoded_cbor_error va res v rem;
      elim_implies
        (raw_data_item_match full_perm _ _ `star` A.pts_to _ _ _)
        (A.pts_to a p va);
      [@@inline_let]
      let res = {
        res with cbor_read_is_success = false
      }
      in
      rewrite
        (cbor_read_deterministically_encoded_error_post a p va)
        (cbor_read_deterministically_encoded_post a p va res);
      return res
    end
  end

module CBOR.SteelST
open Steel.ST.OnRange
open Steel.ST.GenElim

(* Serializers for individual cases *)
friend CBOR.SteelST.Int64
friend CBOR.SteelST.SimpleValue
friend CBOR.SteelST.String
friend CBOR.SteelST.Tagged
friend CBOR.SteelST.Array
friend CBOR.SteelST.Map
open CBOR.SteelST.Type.Def

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let cbor_get_major_type
  #p #v a
= raw_data_item_match_get_case a;
  match a with
  | CBOR_Case_Map _ _ ->
    noop ();
    return Cbor.major_type_map
  | CBOR_Case_Array _ _ ->
    noop ();
    return Cbor.major_type_array
  | CBOR_Case_Tagged _ ->
    noop ();
    return Cbor.major_type_tagged
  | CBOR_Case_Simple_value _ _ ->
    noop ();
    return Cbor.major_type_simple_value
  | CBOR_Case_String _ _ _ ->
    let s = destr_cbor_string a in
    let _ = gen_elim () in
    elim_implies (A.pts_to _ _ _) (raw_data_item_match p _ _);
    return s.cbor_string_type
  | CBOR_Case_Int64 _ _ ->
    let i = destr_cbor_int64 a in
    return i.cbor_int_type
  | _ ->
    let s = destr_cbor_serialized a in
    let _ = gen_elim () in
    let res = CborST.read_major_type s.cbor_serialized_payload in
    elim_implies (LPS.aparse CborST.parse_raw_data_item _ _) (raw_data_item_match p _ _);
    return res

let rec cbor_size_comp
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (#p: perm)
  (sz: SZ.t)
  (perr: R.ref bool)
: STT SZ.t // FIXME: WHY WHY WHY do I need to expand the type annotation to avoid the termination check?
    (raw_data_item_match p c (Ghost.reveal va) `star`
      R.pts_to perr full_perm false
    )
    (fun res ->
      raw_data_item_match p c (Ghost.reveal va) `star`
      exists_ (fun err ->
        R.pts_to perr full_perm err `star`
        pure (LowParse.SteelST.Write.size_comp_for_post CborST.serialize_raw_data_item va sz res err)
    ))
=
  raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 _ _ -> size_comp_for_int64 va c sz perr
  | CBOR_Case_Simple_value _ _ -> size_comp_for_simple_value va c sz perr
  | CBOR_Case_String _ _ _ -> size_comp_for_string va c sz perr
  | CBOR_Case_Tagged _ -> size_comp_for_tagged cbor_size_comp va c sz perr
  | CBOR_Case_Array _ _ -> size_comp_for_array cbor_size_comp va c sz perr
  | CBOR_Case_Map _ _ -> size_comp_for_map cbor_size_comp va c sz perr
  | _ -> size_comp_for_serialized c sz perr

let rec cbor_l2r_write
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (#p: perm)
  (#vout: LPA.array LPS.byte)
  (out: LW.t)
: ST LPS.byte_array // FIXME: WHY WHY WHY do I need to expand the type annotation to avoid the ptermination check?
    (raw_data_item_match p c (Ghost.reveal va) `star`
      LW.vp out vout
    )
    (fun res -> exists_ (fun (vres: LPS.v CborST.parse_raw_data_item_kind Cbor.raw_data_item) -> exists_ (fun (vout': LPA.array LPS.byte) ->
      cbor_l2r_writer_for_post p va c vout out res vres vout'
    )))
    (Seq.length (LPS.serialize CborST.serialize_raw_data_item va) <= LPA.length vout)
    (fun _ -> True)
=
  raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 _ _ -> l2r_writer_for_int64 va c out
  | CBOR_Case_Simple_value _ _ -> l2r_writer_for_simple_value va c out
  | CBOR_Case_String _ _ _ -> l2r_write_cbor_string va c out
  | CBOR_Case_Tagged _ -> l2r_writer_for_tagged cbor_l2r_write c out
  | CBOR_Case_Array _ _ -> l2r_writer_for_array cbor_l2r_write va c out
  | CBOR_Case_Map _ _ -> l2r_writer_for_map cbor_l2r_write va c out
  | _ -> l2r_writer_for_serialized c out

let write_cbor
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (#vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (sz: SZ.t)
: ST SZ.t
    (raw_data_item_match p c (Ghost.reveal va) `star`
      A.pts_to out full_perm vout
    )
    (fun res -> 
      raw_data_item_match p c (Ghost.reveal va) `star`
      exists_ (write_cbor_post va c vout out res)
    )
    (SZ.v sz == A.length out)
    (fun _ -> True)
= A.pts_to_length out _;
  R.with_local false (fun perr ->
    let sz' = cbor_size_comp va c sz perr in
    let _ = gen_elim () in
    let err = R.read perr in
    if err
    then begin
      noop ();
      noop ();
      return 0sz
    end else begin
      noop ();
      let a = LPA.intro_arrayptr out in
      let _ = gen_elim () in
      let va' = vpattern_replace (LPA.arrayptr a) in
      R.with_local sz (fun psz ->
      R.with_local a (fun pa ->
        let res = sz `SZ.sub` sz' in
        let w = LW.intro_vp #_ #_ #a pa psz in
        let lhs = cbor_l2r_write va c w in
        let _ = gen_elim () in
        let rhs = LW.elim_vp w in
        let _ = gen_elim () in
        let _ = LPS.elim_aparse_with_serializer CborST.serialize_raw_data_item lhs in
        let _ = LPA.join lhs rhs in
        let _ = LPA.elim_arrayptr lhs in
        let vout' = vpattern_replace_erased (A.pts_to _ _) in
        rewrite (A.pts_to _ _ _) (A.pts_to out full_perm vout');
        return res
      ))
    end
  )

module Sign
#lang-pulse
open Pulse
open COSE.Format

let specnint_of_int (i: int { - pow2 64 <= i /\ i < 0 }) : GTot spect_evercddl_nint_pretty =
  Mkspect_evercddl_nint_pretty0 (UInt64.uint_to_t (-i-1))

let specuint_of_int (i: int { 0 <= i /\ i < pow2 64 }) : GTot spect_evercddl_uint_pretty =
  Mkspect_evercddl_uint_pretty0 (UInt64.uint_to_t i)

let specint_of_int (i: int { -pow2 64 <= i /\ i < pow2 64 }) : GTot spect_evercddl_int_pretty =
  if i >= 0 then
    Mkspect_evercddl_int_pretty0 (specuint_of_int i)
  else
    Mkspect_evercddl_int_pretty1 (specnint_of_int i)

inline_for_extraction
let i32_to_u64_safe (i: Int32.t { Int32.v i >= 0 }) : j:UInt64.t { UInt64.v j == Int32.v i } =
  Math.Lemmas.pow2_lt_compat 64 31;
  Math.Lemmas.small_mod (Int32.v i) (pow2 64);
  Int.Cast.int32_to_uint64 i

let specint_of_i32 (i: Int32.t) : GTot spect_evercddl_int_pretty =
  Math.Lemmas.pow2_lt_compat 64 31;
  specint_of_int (Int32.v i)

let rel_evercddl_uint_eq a b : squash (rel_evercddl_uint a b == pure (Mkevercddl_uint_pretty0?._x0 a == Mkspect_evercddl_uint_pretty0?._x0 b)) = ()
let rel_evercddl_nint_eq a b : squash (rel_evercddl_nint a b == pure (Mkevercddl_nint_pretty0?._x0 a == Mkspect_evercddl_nint_pretty0?._x0 b)) = ()

let rel_evercddl_int_eq a b : squash (rel_evercddl_int a b ==
  (match a, b with
   | Mkevercddl_int_pretty0 a, Mkspect_evercddl_int_pretty0 b -> rel_evercddl_uint a b
   | Mkevercddl_int_pretty1 a, Mkspect_evercddl_int_pretty1 b -> rel_evercddl_nint a b
   | _ -> pure False)) =
  ()

ghost fn rw_r #a #b (h: squash (a == b)) requires a ensures b { rewrite a as b }
ghost fn rw_l #a #b (h: squash (a == b)) requires b ensures a { rewrite b as a }

let i32_lt_iff a b : squash (Int32.lt a b <==> Int32.v a < Int32.v b) = ()

fn mk_int (i: Int32.t)
  returns j: evercddl_int_pretty
  ensures rel_evercddl_int j (specint_of_i32 i)
{
  if Int32.lt i 0l {
    i32_lt_iff i 0l; assert pure (Int32.v i < Int32.v 0l);
    let k = Int32.sub (-1l) i;
    let j = i32_to_u64_safe k;
    Math.Lemmas.pow2_lt_compat 64 31;
    rw_l (rel_evercddl_nint_eq (Mkevercddl_nint_pretty0 j) (specnint_of_int (Int32.v i)));
    rw_l (rel_evercddl_int_eq (Mkevercddl_int_pretty1 (Mkevercddl_nint_pretty0 j)) (Mkspect_evercddl_int_pretty1 (specnint_of_int (Int32.v i))));
    rewrite each Mkspect_evercddl_int_pretty1 (specnint_of_int (Int32.v i)) as specint_of_i32 i;
    Mkevercddl_int_pretty1 (Mkevercddl_nint_pretty0 j)
  } else {
    let j = i32_to_u64_safe i;
    rw_l (rel_evercddl_uint_eq (Mkevercddl_uint_pretty0 j) (specuint_of_int (UInt64.v j)));
    rw_l (rel_evercddl_int_eq (Mkevercddl_int_pretty0 (Mkevercddl_uint_pretty0 j)) (Mkspect_evercddl_int_pretty0 (specuint_of_int (UInt64.v j))));
    rewrite each Mkspect_evercddl_int_pretty0 (specuint_of_int (UInt64.v j)) as specint_of_i32 i;
    Mkevercddl_int_pretty0 (Mkevercddl_uint_pretty0 j)
  }
}

open CDDL.Pulse.Types

let rel_sig_structure_eq (a: evercddl_Sig_structure_pretty) (b: spect_evercddl_Sig_structure_pretty) :
  squash (rel_evercddl_Sig_structure a b == (match a, b with
    | Mkevercddl_Sig_structure_pretty0 context body_protected rest,
      Mkspect_evercddl_Sig_structure_pretty0 vcontext vbody_protected vrest ->
        rel_either rel_unit rel_unit context vcontext **
        (rel_evercddl_empty_or_serialized_map body_protected vbody_protected **
          (match rest, vrest with
            | Inr (aad, payload), Inr (vaad, vpayload) ->
              rel_evercddl_bstr aad vaad ** rel_evercddl_bstr payload vpayload
            | Inl (sign_protected, (aad, payload)), Inl (vsign_protected, (vaad, vpayload)) ->
              rel_evercddl_empty_or_serialized_map sign_protected vsign_protected **
                (rel_evercddl_bstr aad vaad ** rel_evercddl_bstr payload vpayload)
            | _ -> pure False)))) =
  ()

inline_for_extraction
let signature1: either unit unit = Inr ()

let mk_sig_structure_spec
    (phdr: spect_evercddl_empty_or_serialized_map_pretty)
    (aad payload: spect_evercddl_bstr_pretty)
    : GTot spect_evercddl_Sig_structure_pretty =
  Mkspect_evercddl_Sig_structure_pretty0 signature1 phdr (Inr (aad, payload))

open Pulse.Lib.Trade

ghost fn norm_r p s
  requires p
  ensures norm s p
{
  norm_spec s p;
  rewrite p as norm s p
}

let unfold_plus p lids =
  norm_r p [delta_only lids; iota; primops]

fn mk_sig_structure phdr aad payload
  (#vphdr: erased _)
  (#vaad: erased _)
  (#vpayload: erased _)
  requires rel_evercddl_empty_or_serialized_map phdr vphdr
  requires rel_evercddl_bstr aad vaad
  requires rel_evercddl_bstr payload vpayload
  returns r: evercddl_Sig_structure_pretty
  ensures rel_evercddl_Sig_structure r (mk_sig_structure_spec vphdr vaad vpayload)
  ensures trade (rel_evercddl_Sig_structure r (mk_sig_structure_spec vphdr vaad vpayload))
    (rel_evercddl_empty_or_serialized_map phdr vphdr ** rel_evercddl_bstr aad vaad ** rel_evercddl_bstr payload vpayload)
{
  rewrite emp as rel_either rel_unit rel_unit signature1 signature1;
  rw_l (rel_sig_structure_eq (Mkevercddl_Sig_structure_pretty0 signature1 phdr (Inr (aad, payload)))
    (Mkspect_evercddl_Sig_structure_pretty0 signature1 vphdr (Inr (reveal vaad, reveal vpayload))));
  with res vres. assert rel_evercddl_Sig_structure res vres;
  rewrite each vres as mk_sig_structure_spec vphdr vaad vpayload;

  ghost fn aux ()
    requires emp ** rel_evercddl_Sig_structure res (mk_sig_structure_spec vphdr vaad vpayload)
    ensures rel_evercddl_empty_or_serialized_map phdr vphdr ** rel_evercddl_bstr aad vaad ** rel_evercddl_bstr payload vpayload
  {
    unfold_plus (rel_evercddl_Sig_structure _ _) [`%mk_sig_structure_spec];
    rw_r (rel_sig_structure_eq _ _);
    rewrite rel_either rel_unit rel_unit signature1 signature1 as emp;
  };
  intro_trade _ _ _ aux;

  res
}

open EverCrypt.Ed25519
module AP = Pulse.Lib.ArrayPtr

let to_be_signed_spec
    (phdr: spect_evercddl_empty_or_serialized_map_pretty)
    (aad payload: spect_evercddl_bstr_pretty)
    (tbs: Seq.seq UInt8.t) =
  let open CDDL.Pulse.Bundle.Base in
  bundle_Sig_structure''.b_spec.serializable (mk_sig_structure_spec phdr aad payload) /\
  Seq.equal tbs (CBOR.Spec.API.Format.cbor_det_serialize (bundle_Sig_structure''.b_spec.serializer (mk_sig_structure_spec phdr aad payload)))

module Vec = Pulse.Lib.Vec
module S = Pulse.Lib.Slice

inline_for_extraction
let sz_to_u32_safe (i: SizeT.t { SizeT.v i < pow2 32 }) : j:UInt32.t { UInt32.v j == SizeT.v i } =
  Math.Lemmas.small_mod (SizeT.v i) (pow2 32);
  SizeT.sizet_to_uint32 i

assume val abort () : stt unit emp (fun _ -> pure False)

fn create_sig privkey phdr aad payload (sigbuf: AP.ptr UInt8.t)
    (#vphdr: erased _) (#vaad: erased _) (#vpayload: erased _) (#pprivkey: erased _)
    (#vprivkey: erased (Seq.seq UInt8.t) { Seq.length vprivkey == 32 })
  requires AP.pts_to privkey #pprivkey vprivkey
  requires rel_evercddl_empty_or_serialized_map phdr vphdr
  requires rel_evercddl_bstr aad vaad
  requires rel_evercddl_bstr payload vpayload
  requires exists* vsigbuf. pts_to sigbuf vsigbuf ** pure (Seq.length vsigbuf == 64)
  ensures AP.pts_to privkey #pprivkey vprivkey
  ensures rel_evercddl_empty_or_serialized_map phdr vphdr
  ensures rel_evercddl_bstr aad vaad
  ensures rel_evercddl_bstr payload vpayload
  ensures exists* tbs.
    AP.pts_to sigbuf (spec_ed25519_sign vprivkey tbs) **
    pure (to_be_signed_spec vphdr vaad vpayload tbs)
{
  let sz = 1024sz;
  assert pure (SizeT.v sz <= 1024);
  let arr = Vec.alloc 0uy sz;
  Seq.lemma_create_len (SizeT.v sz) 0uy; //?!?
  Vec.to_array_pts_to arr;
  let outbuf = S.from_array (Vec.vec_to_array arr) sz;
  S.pts_to_len _;
  assert pure (S.len outbuf == sz);
  let sig_struct = mk_sig_structure phdr aad payload;
  let written = serialize_Sig_structure' sig_struct outbuf;
  S.pts_to_len _;
  assert pure (SizeT.v written <= SizeT.v sz);
  assert pure (SizeT.v written <= 1024);
  assert_norm (1024 < pow2 32);
  elim_trade _ _;
  if (written = 0sz) {
    abort ();
    with vsigbuf. rewrite AP.pts_to sigbuf vsigbuf as AP.pts_to sigbuf (spec_ed25519_sign vprivkey vsigbuf);
    with voutbuf. rewrite S.pts_to outbuf voutbuf ** S.is_from_array (Vec.vec_to_array arr) outbuf as emp;
  } else {
    let tbs = Pulse.Lib.Slice.Util.subslice_trade outbuf 0sz written;
    with vtbs. assert S.pts_to tbs vtbs ** pure (to_be_signed_spec vphdr vaad vpayload vtbs);
    S.pts_to_len _;
    let tbs' = S.slice_to_arrayptr_intro tbs;
    sign sigbuf privkey (sz_to_u32_safe written) tbs';
    S.slice_to_arrayptr_elim tbs';
    Pulse.Lib.Trade.elim_trade _ _;
    S.to_array outbuf;
    Vec.to_vec_pts_to arr;
    Vec.free arr;
  }
}

let rel_inl_map =
  (CDDL.Pulse.Types.rel_slice_of_table (CDDL.Pulse.Bundle.Base.mk_eq_test_bij
                    COSE.Format.spect_aux_env25_type_2_pretty_right
                    COSE.Format.spect_aux_env25_type_2_pretty_left
                    COSE.Format.spect_aux_env25_type_2_pretty_left_right
                    COSE.Format.spect_aux_env25_type_2_pretty_right_left
                    (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_label_pretty_right
                        COSE.Format.spect_evercddl_label_pretty_left
                        COSE.Format.spect_evercddl_label_pretty_left_right
                        COSE.Format.spect_evercddl_label_pretty_right_left
                        (CDDL.Spec.EqTest.either_eq (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_int_pretty_right
                                COSE.Format.spect_evercddl_int_pretty_left
                                COSE.Format.spect_evercddl_int_pretty_left_right
                                COSE.Format.spect_evercddl_int_pretty_right_left
                                (CDDL.Spec.EqTest.either_eq (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_uint_pretty_right
                                        COSE.Format.spect_evercddl_uint_pretty_left
                                        COSE.Format.spect_evercddl_uint_pretty_left_right
                                        COSE.Format.spect_evercddl_uint_pretty_right_left
                                        (CDDL.Spec.EqTest.eqtype_eq FStar.UInt64.t))
                                    (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_nint_pretty_right
                                        COSE.Format.spect_evercddl_nint_pretty_left
                                        COSE.Format.spect_evercddl_nint_pretty_left_right
                                        COSE.Format.spect_evercddl_nint_pretty_right_left
                                        (CDDL.Spec.EqTest.eqtype_eq FStar.UInt64.t))))
                            (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_tstr_pretty_right
                                COSE.Format.spect_evercddl_tstr_pretty_left
                                COSE.Format.spect_evercddl_tstr_pretty_left_right
                                COSE.Format.spect_evercddl_tstr_pretty_right_left
                                (CDDL.Spec.EqTest.eqtype_eq (FStar.Seq.Base.seq FStar.UInt8.t))))))
                COSE.Format.rel_aux_env25_type_2
                COSE.Format.rel_aux_env25_type_4)

let dummy_map_val () : aux_env25_type_2_pretty & aux_env25_type_4_pretty =
  let zero: evercddl_int_pretty = Mkevercddl_int_pretty0 (Mkevercddl_uint_pretty0 0uL) in
  Mkaux_env25_type_2_pretty0 (Mkevercddl_label_pretty0 zero),
  Mkaux_env25_type_4_pretty0 (Mkevercddl_values_pretty0 (Mkevercddl_any_pretty0
    { c = CBOR.Pulse.API.Det.Type.dummy_cbor_det_t (); p = 0.5R }))

let assert_norm' (p: prop) : Pure (squash p) (requires normalize p) (ensures fun _ -> True) = ()

let rel_inl_map_eq x y = assert_norm' (rel_inl_map x y == 
  (exists* l . rel_slice_of_list (rel_pair rel_aux_env25_type_2 rel_aux_env25_type_4) false x l **
      pure (y == map_of_list_pair ((CDDL.Pulse.Bundle.Base.mk_eq_test_bij
                    COSE.Format.spect_aux_env25_type_2_pretty_right
                    COSE.Format.spect_aux_env25_type_2_pretty_left
                    COSE.Format.spect_aux_env25_type_2_pretty_left_right
                    COSE.Format.spect_aux_env25_type_2_pretty_right_left
                    (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_label_pretty_right
                        COSE.Format.spect_evercddl_label_pretty_left
                        COSE.Format.spect_evercddl_label_pretty_left_right
                        COSE.Format.spect_evercddl_label_pretty_right_left
                        (CDDL.Spec.EqTest.either_eq (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_int_pretty_right
                                COSE.Format.spect_evercddl_int_pretty_left
                                COSE.Format.spect_evercddl_int_pretty_left_right
                                COSE.Format.spect_evercddl_int_pretty_right_left
                                (CDDL.Spec.EqTest.either_eq (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_uint_pretty_right
                                        COSE.Format.spect_evercddl_uint_pretty_left
                                        COSE.Format.spect_evercddl_uint_pretty_left_right
                                        COSE.Format.spect_evercddl_uint_pretty_right_left
                                        (CDDL.Spec.EqTest.eqtype_eq FStar.UInt64.t))
                                    (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_nint_pretty_right
                                        COSE.Format.spect_evercddl_nint_pretty_left
                                        COSE.Format.spect_evercddl_nint_pretty_left_right
                                        COSE.Format.spect_evercddl_nint_pretty_right_left
                                        (CDDL.Spec.EqTest.eqtype_eq FStar.UInt64.t))))
                            (CDDL.Pulse.Bundle.Base.mk_eq_test_bij COSE.Format.spect_evercddl_tstr_pretty_right
                                COSE.Format.spect_evercddl_tstr_pretty_left
                                COSE.Format.spect_evercddl_tstr_pretty_left_right
                                COSE.Format.spect_evercddl_tstr_pretty_right_left
                                (CDDL.Spec.EqTest.eqtype_eq (FStar.Seq.Base.seq FStar.UInt8.t))))))
      ) l)))

module V = Pulse.Lib.Vec

let sign1_phdrs_spec (alg: Int32.t) =
  Mkspect_evercddl_empty_or_serialized_map_pretty0
    (Mkspect_evercddl_header_map_pretty0
      (Some (Inl (specint_of_i32 alg)))
      None None None (Inr (Inr (None, None)))
      (CDDL.Spec.Map.empty _ _))

let rel_map_sign1_phdrs_eq (alg: Int32.t) alg' rest =
  assert_norm' (rel_evercddl_empty_or_serialized_map (Mkevercddl_empty_or_serialized_map_pretty0
    (Mkevercddl_header_map_pretty0 (Some (Inl alg')) None None None (Inr (Inr (None, None)))
      (Inl { s = rest; p=1.0R })))
    (sign1_phdrs_spec alg) ==
    (((((rel_evercddl_int alg' (specint_of_i32 alg) **
      emp) ** emp) ** emp) ** (emp ** emp)) **
      rel_inl_map { s = rest; p=1.0R } (CDDL.Spec.Map.empty _ _)))

fn mk_phdrs (alg: Int32.t)
  returns res: evercddl_empty_or_serialized_map_pretty
  ensures rel_evercddl_empty_or_serialized_map res (sign1_phdrs_spec alg)
{
  let alg' = mk_int alg;
  let rest = V.alloc (dummy_map_val ()) 0sz;
  V.to_array_pts_to rest;
  let rest2 = S.from_array (V.vec_to_array rest) 0sz;
  Pulse.Lib.SeqMatch.seq_list_match_nil_intro (Seq.Base.create 0 (dummy_map_val ())) []
      (rel_pair rel_aux_env25_type_2 rel_aux_env25_type_4);
  fold rel_slice_of_list (rel_pair rel_aux_env25_type_2 rel_aux_env25_type_4) false
      (Mkslice rest2 1.0R) [];
  rw_l (rel_inl_map_eq {s = rest2; p=1.0R} (CDDL.Spec.Map.empty _ _));
  rw_l (rel_map_sign1_phdrs_eq alg alg' _);
  with res. assert rel_evercddl_empty_or_serialized_map res (sign1_phdrs_spec alg);
  drop_ (S.is_from_array (V.vec_to_array rest) rest2); // TODO leak

  let alg'':
        FStar.Tactics.PrettifyType.named "intkey1"
              (FStar.Pervasives.either COSE.Format.evercddl_int_pretty
                  COSE.Format.evercddl_tstr_pretty)
  = Inl alg';
  let foo:
  FStar.Pervasives.either (FStar.Tactics.PrettifyType.named "intkey6"
                  COSE.Format.evercddl_bstr_pretty &
                FStar.Tactics.PrettifyType.named "intkey5"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey5"
                          COSE.Format.evercddl_everparsenomatch_pretty)))
              (FStar.Tactics.PrettifyType.named "intkey6"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey6"
                          COSE.Format.evercddl_everparsenomatch_pretty)) &
                FStar.Tactics.PrettifyType.named "intkey5"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey5"
                          COSE.Format.evercddl_everparsenomatch_pretty)))
  = Inr (None, None);
  let foo':
        FStar.Pervasives.either (FStar.Tactics.PrettifyType.named "intkey5"
              COSE.Format.evercddl_bstr_pretty &
            FStar.Tactics.PrettifyType.named "intkey6"
              (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey6"
                      COSE.Format.evercddl_everparsenomatch_pretty)))
          (FStar.Pervasives.either (FStar.Tactics.PrettifyType.named "intkey6"
                  COSE.Format.evercddl_bstr_pretty &
                FStar.Tactics.PrettifyType.named "intkey5"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey5"
                          COSE.Format.evercddl_everparsenomatch_pretty)))
              (FStar.Tactics.PrettifyType.named "intkey6"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey6"
                          COSE.Format.evercddl_everparsenomatch_pretty)) &
                FStar.Tactics.PrettifyType.named "intkey5"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey5"
                          COSE.Format.evercddl_everparsenomatch_pretty))))
   = Inr foo;
  let bar':
        FStar.Pervasives.either (CDDL.Pulse.Types.slice (COSE.Format.aux_env25_type_2_pretty &
                COSE.Format.aux_env25_type_4_pretty))
          (CDDL.Pulse.Parse.MapGroup.map_iterator_t CBOR.Pulse.API.Det.Type.cbor_det_map_iterator_t
              COSE.Format.aux_env25_type_2_pretty
              COSE.Format.aux_env25_type_4_pretty
              CBOR.Pulse.API.Det.C.cbor_det_match
              (CDDL.Pulse.Iterator.Base.mk_spec COSE.Format.rel_aux_env25_type_2)
              (CDDL.Pulse.Iterator.Base.mk_spec COSE.Format.rel_aux_env25_type_4))
  = Inl { s = rest2; p=1.0R };
  rewrite each res as Mkevercddl_empty_or_serialized_map_pretty0 (Mkevercddl_header_map_pretty0 (Some alg'') None None None foo' bar');
  Mkevercddl_empty_or_serialized_map_pretty0 (Mkevercddl_header_map_pretty0 (Some alg'') None None None foo' bar')
}

let sign1_emphdrs_spec () : GTot _ =
    (Mkspect_evercddl_header_map_pretty0
      None None None None (Inr (Inr (None, None)))
      (CDDL.Spec.Map.empty _ _))

let rel_map_sign1_emphdrs_eq rest =
  assert_norm' (rel_evercddl_header_map (
    (Mkevercddl_header_map_pretty0 None None None None (Inr (Inr (None, None)))
      (Inl { s = rest; p=1.0R })))
    (sign1_emphdrs_spec ()) ==
    (((((emp ** emp) ** emp) ** emp) ** (emp ** emp)) **
      rel_inl_map { s = rest; p=1.0R } (CDDL.Spec.Map.empty _ _)))

fn mk_emphdrs ()
  returns res: evercddl_header_map_pretty
  ensures rel_evercddl_header_map res (sign1_emphdrs_spec ())
{
  // let alg' = mk_int alg;
  let rest = V.alloc (dummy_map_val ()) 0sz;
  V.to_array_pts_to rest;
  let rest2 = S.from_array (V.vec_to_array rest) 0sz;
  Pulse.Lib.SeqMatch.seq_list_match_nil_intro (Seq.Base.create 0 (dummy_map_val ())) []
      (rel_pair rel_aux_env25_type_2 rel_aux_env25_type_4);
  fold rel_slice_of_list (rel_pair rel_aux_env25_type_2 rel_aux_env25_type_4) false
      (Mkslice rest2 1.0R) [];
  rw_l (rel_inl_map_eq {s = rest2; p=1.0R} (CDDL.Spec.Map.empty _ _));
  rw_l (rel_map_sign1_emphdrs_eq _);
  with res. assert rel_evercddl_header_map res (sign1_emphdrs_spec ());
  drop_ (S.is_from_array (V.vec_to_array rest) rest2); // TODO leak
  let foo:
  FStar.Pervasives.either (FStar.Tactics.PrettifyType.named "intkey6"
                  COSE.Format.evercddl_bstr_pretty &
                FStar.Tactics.PrettifyType.named "intkey5"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey5"
                          COSE.Format.evercddl_everparsenomatch_pretty)))
              (FStar.Tactics.PrettifyType.named "intkey6"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey6"
                          COSE.Format.evercddl_everparsenomatch_pretty)) &
                FStar.Tactics.PrettifyType.named "intkey5"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey5"
                          COSE.Format.evercddl_everparsenomatch_pretty)))
  = Inr (None, None);
  let foo':
        FStar.Pervasives.either (FStar.Tactics.PrettifyType.named "intkey5"
              COSE.Format.evercddl_bstr_pretty &
            FStar.Tactics.PrettifyType.named "intkey6"
              (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey6"
                      COSE.Format.evercddl_everparsenomatch_pretty)))
          (FStar.Pervasives.either (FStar.Tactics.PrettifyType.named "intkey6"
                  COSE.Format.evercddl_bstr_pretty &
                FStar.Tactics.PrettifyType.named "intkey5"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey5"
                          COSE.Format.evercddl_everparsenomatch_pretty)))
              (FStar.Tactics.PrettifyType.named "intkey6"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey6"
                          COSE.Format.evercddl_everparsenomatch_pretty)) &
                FStar.Tactics.PrettifyType.named "intkey5"
                  (FStar.Pervasives.Native.option (FStar.Tactics.PrettifyType.named "intkey5"
                          COSE.Format.evercddl_everparsenomatch_pretty))))
   = Inr foo;
  let bar':
        FStar.Pervasives.either (CDDL.Pulse.Types.slice (COSE.Format.aux_env25_type_2_pretty &
                COSE.Format.aux_env25_type_4_pretty))
          (CDDL.Pulse.Parse.MapGroup.map_iterator_t CBOR.Pulse.API.Det.Type.cbor_det_map_iterator_t
              COSE.Format.aux_env25_type_2_pretty
              COSE.Format.aux_env25_type_4_pretty
              CBOR.Pulse.API.Det.C.cbor_det_match
              (CDDL.Pulse.Iterator.Base.mk_spec COSE.Format.rel_aux_env25_type_2)
              (CDDL.Pulse.Iterator.Base.mk_spec COSE.Format.rel_aux_env25_type_4))
  = Inl { s = rest2; p=1.0R };
  rewrite each res as (Mkevercddl_header_map_pretty0 None None None None foo' bar');
  (Mkevercddl_header_map_pretty0 None None None None foo' bar')
}

let sign1_tagged_spec (alg: Int32.t) uhdr payload sig =
  Mkspect_evercddl_COSE_Sign1_Tagged_pretty0 (Mkspect_evercddl_COSE_Sign1_pretty0
    (sign1_phdrs_spec alg) uhdr (Inl payload) sig)

// #push-options "--print_implicits"

let rel_sign1_tagged_eq1 phdr uhdr payload sig vphdr vuhdr vpayload vsig =
  assert_norm' (rel_evercddl_COSE_Sign1_Tagged
      (Mkevercddl_COSE_Sign1_Tagged_pretty0
        (Mkevercddl_COSE_Sign1_pretty0 phdr uhdr (Inl payload) sig))
      (Mkspect_evercddl_COSE_Sign1_Tagged_pretty0 (Mkspect_evercddl_COSE_Sign1_pretty0
        vphdr vuhdr (Inl vpayload) vsig)) ==
  (rel_evercddl_empty_or_serialized_map phdr vphdr **
    rel_evercddl_header_map uhdr vuhdr) **
    (rel_evercddl_bstr payload vpayload ** rel_evercddl_bstr sig vsig))

fn sign1 privkey uhdr aad payload (outbuf: S.slice UInt8.t)
    #pprivkey (#vprivkey: erased (Seq.seq UInt8.t) { Seq.length vprivkey == 32 })
    (#vuhdr: erased _) (#vaad: erased _) (#vpayload: erased _)
    (#voutbuf: erased _)
  requires AP.pts_to privkey #pprivkey vprivkey
  requires rel_evercddl_header_map uhdr vuhdr
  requires rel_evercddl_bstr aad vaad
  requires rel_evercddl_bstr payload vpayload
  requires pts_to outbuf voutbuf

  returns outbuf_sz: SizeT.t
  ensures AP.pts_to privkey #pprivkey vprivkey
  // TODO leak leak
  ensures rel_evercddl_header_map uhdr vuhdr
  ensures rel_evercddl_bstr aad vaad
  ensures rel_evercddl_bstr payload vpayload
  ensures exists* voutbuf. pts_to outbuf voutbuf ** pure (SizeT.v outbuf_sz <= Seq.length voutbuf)
  //  ** pure (SizeT.lt 0sz outbuf_sz ==> Seq.slice voutbuf 0 (SizeT.v outbuf_sz) == _)
{
  let alg: Int32.t = -8l;
  let phdr = mk_phdrs alg;
  let mut sigbuf = [| 0uy; 64sz |];
  Seq.lemma_create_len (SizeT.v 64sz) 0uy; //?!?
  let sigbuf2 = AP.from_array sigbuf;
  create_sig privkey phdr aad payload sigbuf2;
  AP.to_array sigbuf2 sigbuf #_ #(spec_ed25519_sign vprivkey _);
  // let uhdr = mk_emphdrs ();
  rw_l (rel_sign1_tagged_eq1 phdr _ payload _ (sign1_phdrs_spec alg) _ vpayload _);
  let outbuf_sz = serialize_COSE_Sign1_Tagged' _ outbuf;
  rw_r (rel_sign1_tagged_eq1 phdr _ payload _ (sign1_phdrs_spec alg) _ vpayload _);
  drop_ (rel_evercddl_empty_or_serialized_map phdr _);
  if (outbuf_sz = 0sz) { abort (); 0sz } else {
    outbuf_sz;
  }
}

let rel_bstr_eq (x: evercddl_bstr_pretty) (y: spect_evercddl_bstr_pretty) =
  assert_norm' (rel_evercddl_bstr x y ==
    (match x, y with
    | Mkevercddl_bstr_pretty0 { s; p }, Mkspect_evercddl_bstr_pretty0 y ->
      pts_to s #p y ** pure (false == false))
    // pts_to x._x0.s #x._x0.p y._x0 ** pure (false == false)
    )

fn sign1_simple privkey payload (outbuf: S.slice UInt8.t)
    #pprivkey (#vprivkey: erased (Seq.seq UInt8.t) { Seq.length vprivkey == 32 })
    (#vpayload: erased _)
    (#voutbuf: erased _)
  requires AP.pts_to privkey #pprivkey vprivkey
  requires rel_evercddl_bstr payload vpayload
  requires pts_to outbuf voutbuf

  returns outbuf_sz: SizeT.t
  ensures AP.pts_to privkey #pprivkey vprivkey
  // TODO leak leak
  // ensures rel_evercddl_empty_or_serialized_map uhdr vuhdr
  ensures rel_evercddl_bstr payload vpayload
  ensures exists* voutbuf. S.pts_to outbuf voutbuf ** pure (SizeT.v outbuf_sz <= Seq.length voutbuf)
  //  ** pure (SizeT.lt 0sz outbuf_sz ==> Seq.slice voutbuf 0 (SizeT.v outbuf_sz) == _)
{
  let uhdr = mk_emphdrs ();
  let mut aadbuf = [| 0uy; 0sz |];
  let aadslice = S.from_array aadbuf 0sz;
  with aad. assert pure ((aad <: evercddl_bstr_pretty) == Mkevercddl_bstr_pretty0 { s = aadslice; p = 1.0R });
  rw_l (rel_bstr_eq aad (Mkspect_evercddl_bstr_pretty0 _));
  let res = sign1 privkey uhdr aad payload outbuf;
  rw_r (rel_bstr_eq aad (Mkspect_evercddl_bstr_pretty0 _));
  S.to_array aadslice;
  drop_ (rel_evercddl_header_map uhdr _); // TODO leak
  res
}

fn main () returns exitcode: Int32.t { 0l }
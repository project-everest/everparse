module CommonPulse
#lang-pulse
open Pulse
open COSE.Format
open Pulse.Lib.Trade
open Pulse.Lib.Trade.Util
open EverCrypt.Ed25519
// module AP = Pulse.Lib.ArrayPtr
module S = Pulse.Lib.Slice
module V = Pulse.Lib.Vec
module A = Pulse.Lib.Array
open CDDL.Pulse.Types

[@@pulse_unfold]
let borrows (what from: slprop) : slprop =
  what ** trade what from

let specnint_of_int (i: int { - pow2 64 <= i /\ i < 0 }) : GTot spect_evercddl_nint_pretty =
  Mkspect_evercddl_nint_pretty0 (UInt64.uint_to_t (-i-1))

let specuint_of_int (i: int { 0 <= i /\ i < pow2 64 }) : GTot spect_evercddl_uint_pretty =
  Mkspect_evercddl_uint_pretty0 (UInt64.uint_to_t i)

let specint_of_int (i: int { -pow2 64 <= i /\ i < pow2 64 }) : GTot spect_evercddl_int_pretty =
  if i >= 0 then
    Mkspect_evercddl_int_pretty0 (specuint_of_int i)
  else
    Mkspect_evercddl_int_pretty1 (specnint_of_int i)

inline_for_extraction noextract
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

inline_for_extraction noextract
let signature1: either unit unit = Inr ()

let mk_sig_structure_spec
    (phdr: spect_evercddl_empty_or_serialized_map_pretty)
    (aad payload: spect_evercddl_bstr_pretty)
    : GTot spect_evercddl_Sig_structure_pretty =
  Mkspect_evercddl_Sig_structure_pretty0 signature1 phdr (Inr (aad, payload))

ghost fn norm_r p s
  requires p
  ensures norm s p
{
  norm_spec s p;
  rewrite p as norm s p
}

let unfold_plus p lids =
  norm_r p [delta_only lids; iota; primops]

inline_for_extraction noextract
fn mk_sig_structure phdr aad payload
  (#vphdr: erased _)
  (#vaad: erased _)
  (#vpayload: erased _)
  requires rel_evercddl_empty_or_serialized_map phdr vphdr
  requires rel_evercddl_bstr aad vaad
  requires rel_evercddl_bstr payload vpayload
  returns r: evercddl_Sig_structure_pretty
  ensures borrows (rel_evercddl_Sig_structure r (mk_sig_structure_spec vphdr vaad vpayload))
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

let ser_to #t #st (s: CDDL.Spec.Base.spec t st true) (x: st) y =
  s.serializable x /\ Seq.equal y (CBOR.Spec.API.Format.cbor_det_serialize (s.serializer x))

let ser_to_inj #t #st s x y y' :
    Lemma (requires ser_to #t #st s x y /\ ser_to s x y') (ensures y == y')
      [SMTPat (ser_to s x y); SMTPat (ser_to s x y')] =
  ()

let to_be_signed_spec
    (phdr: spect_evercddl_empty_or_serialized_map_pretty)
    (aad payload: spect_evercddl_bstr_pretty)
    (tbs: Seq.seq UInt8.t)
    : prop =
  ser_to bundle_Sig_structure''.b_spec (mk_sig_structure_spec phdr aad payload) tbs

inline_for_extraction noextract
let sz_to_u32_safe (i: SizeT.t { SizeT.v i < pow2 32 }) : j:UInt32.t { UInt32.v j == SizeT.v i } =
  Math.Lemmas.small_mod (SizeT.v i) (pow2 32);
  SizeT.sizet_to_uint32 i

open CommonAbort { abort }

fn create_sig privkey phdr aad payload (sigbuf: S.slice UInt8.t)
    (#vphdr: erased _) (#vaad: erased _) (#vpayload: erased _) (#pprivkey: erased _)
    (#vprivkey: erased (Seq.seq UInt8.t) { Seq.length vprivkey == 32 })
  requires S.pts_to privkey #pprivkey vprivkey
  requires rel_evercddl_empty_or_serialized_map phdr vphdr
  requires rel_evercddl_bstr aad vaad
  requires rel_evercddl_bstr payload vpayload
  requires exists* vsigbuf. pts_to sigbuf vsigbuf ** pure (Seq.length vsigbuf == 64)
  ensures S.pts_to privkey #pprivkey vprivkey
  ensures rel_evercddl_empty_or_serialized_map phdr vphdr
  ensures rel_evercddl_bstr aad vaad
  ensures rel_evercddl_bstr payload vpayload
  ensures exists* tbs.
    S.pts_to sigbuf (spec_ed25519_sign vprivkey tbs) **
    pure (to_be_signed_spec vphdr vaad vpayload tbs)
{
  let sz = 1024sz;
  assert pure (SizeT.v sz <= 1024);
  let arr = V.alloc 0uy sz;
  Seq.lemma_create_len (SizeT.v sz) 0uy; //?!?
  V.to_array_pts_to arr;
  let outbuf = S.from_array (V.vec_to_array arr) sz;
  S.pts_to_len outbuf;
  assert pure (S.len outbuf == sz);
  let sig_struct = mk_sig_structure phdr aad payload;
  let written = serialize_Sig_structure' sig_struct outbuf;
  S.pts_to_len outbuf;
  assert pure (SizeT.v written <= SizeT.v sz);
  assert pure (SizeT.v written <= 1024);
  assert_norm (1024 < pow2 32);
  elim_trade _ _;
  if (written = 0sz) {
    abort ();
    with vsigbuf. rewrite S.pts_to sigbuf vsigbuf as S.pts_to sigbuf (spec_ed25519_sign vprivkey vsigbuf);
    with voutbuf. rewrite S.pts_to outbuf voutbuf ** S.is_from_array (V.vec_to_array arr) outbuf as emp;
  } else {
    let tbs = Pulse.Lib.Slice.Util.subslice_trade outbuf 0sz written;
    with vtbs. assert S.pts_to tbs vtbs ** pure (to_be_signed_spec vphdr vaad vpayload vtbs);
    S.pts_to_len tbs;
    sign () sigbuf privkey tbs;
    elim_trade _ _;
    S.to_array outbuf;
    V.to_vec_pts_to arr;
    V.free arr;
  }
}

let rel_inl_map =
(rel_slice_of_table (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_label_pretty_right
                      spect_evercddl_label_pretty_left
                      spect_evercddl_label_pretty_left_right
                      spect_evercddl_label_pretty_right_left
                      (CDDL.Spec.EqTest.either_eq (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_int_pretty_right
                              spect_evercddl_int_pretty_left
                              spect_evercddl_int_pretty_left_right
                              spect_evercddl_int_pretty_right_left
                              (CDDL.Spec.EqTest.either_eq (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_uint_pretty_right
                                      spect_evercddl_uint_pretty_left
                                      spect_evercddl_uint_pretty_left_right
                                      spect_evercddl_uint_pretty_right_left
                                      (CDDL.Spec.EqTest.eqtype_eq UInt64.t))
                                  (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_nint_pretty_right
                                      spect_evercddl_nint_pretty_left
                                      spect_evercddl_nint_pretty_left_right
                                      spect_evercddl_nint_pretty_right_left
                                      (CDDL.Spec.EqTest.eqtype_eq UInt64.t))))
                          (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_tstr_pretty_right
                              spect_evercddl_tstr_pretty_left
                              spect_evercddl_tstr_pretty_left_right
                              spect_evercddl_tstr_pretty_right_left
                              (CDDL.Spec.EqTest.eqtype_eq (Seq.Base.seq UInt8.t)))))
                  rel_evercddl_label
                  rel_evercddl_values)

let dummy_map_val () : evercddl_label_pretty & evercddl_values_pretty =
  Mkevercddl_label_pretty0
    (Mkevercddl_int_pretty0 (Mkevercddl_uint_pretty0 0uL)),
  Mkevercddl_values_pretty0 (Mkevercddl_any_pretty0
    { c = CBOR.Pulse.API.Det.Rust.dummy_cbor_det_t (); p = 0.5R })

let assert_norm' (p: prop) : Pure (squash p) (requires normalize p) (ensures fun _ -> True) = ()

let rel_inl_map_eq (x: slice (evercddl_label_pretty & evercddl_values_pretty)) y = assert_norm' (rel_inl_map x y == 
  (exists* l .
    (exists* s . pts_to x.s #x.p s ** Pulse.Lib.SeqMatch.seq_list_match s l (rel_pair rel_evercddl_label rel_evercddl_values) ** pure (false == false)) **
      pure (y == map_of_list_pair
      (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_label_pretty_right
                      spect_evercddl_label_pretty_left
                      spect_evercddl_label_pretty_left_right
                      spect_evercddl_label_pretty_right_left
                      (CDDL.Spec.EqTest.either_eq (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_int_pretty_right
                              spect_evercddl_int_pretty_left
                              spect_evercddl_int_pretty_left_right
                              spect_evercddl_int_pretty_right_left
                              (CDDL.Spec.EqTest.either_eq (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_uint_pretty_right
                                      spect_evercddl_uint_pretty_left
                                      spect_evercddl_uint_pretty_left_right
                                      spect_evercddl_uint_pretty_right_left
                                      (CDDL.Spec.EqTest.eqtype_eq UInt64.t))
                                  (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_nint_pretty_right
                                      spect_evercddl_nint_pretty_left
                                      spect_evercddl_nint_pretty_left_right
                                      spect_evercddl_nint_pretty_right_left
                                      (CDDL.Spec.EqTest.eqtype_eq UInt64.t))))
                          (CDDL.Pulse.Bundle.Base.mk_eq_test_bij spect_evercddl_tstr_pretty_right
                              spect_evercddl_tstr_pretty_left
                              spect_evercddl_tstr_pretty_left_right
                              spect_evercddl_tstr_pretty_right_left
                              (CDDL.Spec.EqTest.eqtype_eq (Seq.Base.seq UInt8.t)))))
      l)))

let sign1_phdrs_spec (alg: Int32.t) =
  Mkspect_evercddl_empty_or_serialized_map_pretty0
    (Mkspect_evercddl_header_map_pretty0
      (Some (Inl (specint_of_i32 alg)))
      None None None (Inr (Inr (None, None)))
      (CDDL.Spec.Map.empty _ _))

let rel_map_sign1_phdrs_eq (alg: Int32.t) alg' s =
  assert_norm' (rel_evercddl_empty_or_serialized_map (Mkevercddl_empty_or_serialized_map_pretty0
    (Mkevercddl_header_map_pretty0 (Some (Inl alg')) None None None (Inr (Inr (None, None)))
      (Inl s)))
    (sign1_phdrs_spec alg) ==
    (((((rel_evercddl_int alg' (specint_of_i32 alg) **
      emp) ** emp) ** emp) ** (emp ** emp)) **
      rel_inl_map s (CDDL.Spec.Map.empty _ _)))

inline_for_extraction
fn mk_phdrs (alg: Int32.t) (rest: A.larray (evercddl_label_pretty & evercddl_values_pretty) 0)
    #prest (#vrest: erased _)
  requires pts_to rest #prest vrest
  returns res: evercddl_empty_or_serialized_map_pretty
  ensures borrows (rel_evercddl_empty_or_serialized_map res (sign1_phdrs_spec alg))
    (pts_to rest #prest vrest)
{
  let alg' = mk_int alg;
  A.pts_to_len rest;
  let rest2 = S.from_array rest 0sz;
  Pulse.Lib.SeqMatch.seq_list_match_nil_intro (Seq.Base.create 0 (dummy_map_val ())) []
      (rel_pair rel_evercddl_label rel_evercddl_values);
  assert pure (Seq.Base.create 0 (dummy_map_val ()) `Seq.equal` vrest);
  rw_l (rel_inl_map_eq {s = rest2; p=prest} (CDDL.Spec.Map.empty _ _));
  rw_l (rel_map_sign1_phdrs_eq alg alg' _);
  with res. assert rel_evercddl_empty_or_serialized_map res (sign1_phdrs_spec alg);
  ghost fn aux ()
    requires S.is_from_array rest rest2 ** rel_evercddl_empty_or_serialized_map res (sign1_phdrs_spec alg)
    ensures pts_to rest #prest vrest
  {
    rw_r (rel_map_sign1_phdrs_eq alg alg' _);
    rw_r (rel_inl_map_eq {s = rest2; p=prest} (CDDL.Spec.Map.empty _ _));
    S.to_array rest2;
    A.pts_to_len rest;
    with vrest'. assert pts_to rest #prest vrest';
    assert pure (Seq.equal vrest' vrest);
    drop_ (
      Pulse.Lib.SeqMatch.seq_list_match _ _ (rel_pair rel_evercddl_label rel_evercddl_values) **
      rel_evercddl_int alg' (specint_of_i32 alg)
    );
  };
  intro_trade _ _ _ aux;
  res
}

let sign1_emphdrs_spec () : GTot _ =
    (Mkspect_evercddl_header_map_pretty0
      None None None None (Inr (Inr (None, None)))
      (CDDL.Spec.Map.empty _ _))

let rel_map_sign1_emphdrs_eq s =
  assert_norm' (rel_evercddl_header_map (
    (Mkevercddl_header_map_pretty0 None None None None (Inr (Inr (None, None)))
      (Inl s)))
    (sign1_emphdrs_spec ()) ==
    (((((emp ** emp) ** emp) ** emp) ** (emp ** emp)) **
      rel_inl_map s (CDDL.Spec.Map.empty _ _)))

inline_for_extraction noextract
fn mk_emphdrs (rest: A.larray (evercddl_label_pretty & evercddl_values_pretty) 0)
    #prest (#vrest: erased _)
  requires pts_to rest #prest vrest
  returns res: evercddl_header_map_pretty
  ensures borrows (rel_evercddl_header_map res (sign1_emphdrs_spec ())) (pts_to rest #prest vrest)
{
  A.pts_to_len rest;
  assert pure (Seq.equal vrest (Seq.create 0 (dummy_map_val ())));
  let rest2 = S.from_array rest 0sz;
  Pulse.Lib.SeqMatch.seq_list_match_nil_intro (Seq.Base.create 0 (dummy_map_val ())) []
      (rel_pair rel_evercddl_label rel_evercddl_values);
  rw_l (rel_inl_map_eq {s = rest2; p=prest} (CDDL.Spec.Map.empty _ _));
  rw_l (rel_map_sign1_emphdrs_eq _);
  with res. assert rel_evercddl_header_map res (sign1_emphdrs_spec ());

  ghost fn aux ()
    requires S.is_from_array rest rest2 ** rel_evercddl_header_map res (sign1_emphdrs_spec ())
    ensures pts_to rest #prest vrest
  {
    rw_r (rel_map_sign1_emphdrs_eq _);
    rw_r (rel_inl_map_eq {s = rest2; p=prest} (CDDL.Spec.Map.empty _ _));
    S.to_array rest2;
    A.pts_to_len rest;
    with vrest'. assert pts_to rest #prest vrest';
    assert pure (Seq.equal vrest' vrest);
    drop_ (
      Pulse.Lib.SeqMatch.seq_list_match _ _ (rel_pair rel_evercddl_label rel_evercddl_values)
    );
  };
  intro_trade _ _ _ aux;

  res
}

let sign1_tagged_spec (alg: Int32.t) uhdr payload sig =
  Mkspect_evercddl_COSE_Sign1_Tagged_pretty0 (Mkspect_evercddl_COSE_Sign1_pretty0
    (sign1_phdrs_spec alg) uhdr (Inl payload) sig)

let rel_sign1_tagged_eq1 phdr uhdr payload sig vphdr vuhdr vpayload vsig =
  assert_norm' (rel_evercddl_COSE_Sign1_Tagged
      (Mkevercddl_COSE_Sign1_Tagged_pretty0
        (Mkevercddl_COSE_Sign1_pretty0 phdr uhdr (Inl payload) sig))
      (Mkspect_evercddl_COSE_Sign1_Tagged_pretty0 (Mkspect_evercddl_COSE_Sign1_pretty0
        vphdr vuhdr (Inl vpayload) vsig)) ==
  (rel_evercddl_empty_or_serialized_map phdr vphdr **
    rel_evercddl_header_map uhdr vuhdr) **
    (rel_evercddl_bstr payload vpayload ** rel_evercddl_bstr sig vsig))

let rel_bstr_eq (x: evercddl_bstr_pretty) (y: spect_evercddl_bstr_pretty) =
  assert_norm' (rel_evercddl_bstr x y ==
    (match x, y with
    | Mkevercddl_bstr_pretty0 { s; p }, Mkspect_evercddl_bstr_pretty0 y ->
      pts_to s #p y ** pure (false == false))
    )

ghost fn rw_r_wt #a #b (h: squash (a == b)) requires a ensures b ** trade b a { rewrite_with_trade a b }
ghost fn rw_l_wt #a #b (h: squash (a == b)) requires b ensures a ** trade a b { rewrite_with_trade b a }

let sign1_spec
    privkey
    (uhdr: spect_evercddl_header_map_pretty)
    (aad payload: spect_evercddl_bstr_pretty)
    (msg: Seq.seq UInt8.t)
    : prop =
  let phdr = sign1_phdrs_spec (-8l) in
  exists tbs. to_be_signed_spec phdr aad payload tbs /\
  ser_to bundle_COSE_Sign1_Tagged''.b_spec
    (Mkspect_evercddl_COSE_Sign1_Tagged_pretty0 (Mkspect_evercddl_COSE_Sign1_pretty0
        phdr uhdr (Inl payload) { _x0 = spec_ed25519_sign privkey tbs }))
    msg

ghost fn trade_exists (#t: Type0) (p: t->slprop) x
  ensures trade (p x) (exists* y. p y)
{
  ghost fn aux ()
    requires emp ** p x
    ensures exists* y. p y
  { () };
  intro_trade _ _ _ aux;
}

inline_for_extraction // Karamel's lifetime support is massively lacking
fn sign1 privkey uhdr aad payload (outbuf: S.slice UInt8.t)
    #pprivkey (#vprivkey: erased (Seq.seq UInt8.t) { Seq.length vprivkey == 32 })
    (#vuhdr: erased _) (#vaad: erased _) (#vpayload: erased _)
  requires S.pts_to privkey #pprivkey vprivkey
  requires rel_evercddl_header_map uhdr vuhdr
  requires rel_evercddl_bstr aad vaad
  requires rel_evercddl_bstr payload vpayload
  requires exists* voutbuf. pts_to outbuf voutbuf

  returns out: S.slice UInt8.t
  ensures S.pts_to privkey #pprivkey vprivkey
  ensures rel_evercddl_header_map uhdr vuhdr
  ensures rel_evercddl_bstr aad vaad
  ensures rel_evercddl_bstr payload vpayload
  ensures exists* msg.
    borrows (S.pts_to out msg) (exists* voutbuf. pts_to outbuf voutbuf) **
    pure (sign1_spec vprivkey vuhdr vaad vpayload msg)
{
  let alg: Int32.t = -8l;
  let mut phdrauxbuf = [| dummy_map_val (); 0sz |];
  let phdr = mk_phdrs alg phdrauxbuf;
  let mut sigbuf = [| 0uy; 64sz |];
  Seq.lemma_create_len (SizeT.v 64sz) 0uy; //?!?
  let sigbuf2 = S.from_array sigbuf 64sz;
  create_sig privkey phdr aad payload sigbuf2;
  // S.to_array sigbuf2 #_ #(spec_ed25519_sign vprivkey _);
  with tbs. assert S.pts_to sigbuf2 (spec_ed25519_sign vprivkey tbs);
  // let sigbuf3 = S.from_array sigbuf 64sz;
  with sigbuf4. assert pure ((sigbuf4 <: evercddl_bstr_pretty) == { _x0 = { p = 1.0R; s = sigbuf2 } });
  rw_l_wt (rel_bstr_eq sigbuf4 { _x0 = spec_ed25519_sign vprivkey tbs });
  rw_l_wt (rel_sign1_tagged_eq1 phdr _ payload sigbuf4 (sign1_phdrs_spec alg) _ vpayload _);
  let outbuf_sz = serialize_COSE_Sign1_Tagged' _ outbuf;
  elim_trade (rel_evercddl_COSE_Sign1_Tagged _ _) _;
  elim_trade (rel_evercddl_bstr sigbuf4 { _x0 = spec_ed25519_sign vprivkey tbs }) _;
  S.to_array sigbuf2;
  elim_trade _ _;
  with voutbuf. assert S.pts_to outbuf voutbuf;
  trade_exists (S.pts_to outbuf) voutbuf;
  if (outbuf_sz = 0sz) {
    abort ();
    assert S.pts_to outbuf (spec_ed25519_sign vprivkey tbs);
    outbuf
  } else {
    let out = Pulse.Lib.Slice.Util.subslice_trade outbuf 0sz outbuf_sz;
    trade_compose _ (S.pts_to outbuf _) _;
    out;
  }
}

fn sign1_simple privkey payload (outbuf: S.slice UInt8.t)
    #pprivkey (#vprivkey: erased (Seq.seq UInt8.t) { Seq.length vprivkey == 32 })
    (#vpayload: erased _)
    (#voutbuf: erased _)
  requires S.pts_to privkey #pprivkey vprivkey
  requires rel_evercddl_bstr payload vpayload
  requires pts_to outbuf voutbuf

  returns out: S.slice UInt8.t
  ensures S.pts_to privkey #pprivkey vprivkey
  ensures rel_evercddl_bstr payload vpayload
  ensures exists* msg.
    borrows (S.pts_to out msg) (exists* voutbuf. pts_to outbuf voutbuf) **
    pure (sign1_spec vprivkey (sign1_emphdrs_spec ()) { _x0 = Seq.create 0 0uy } vpayload msg)
{
  let mut uhdrauxbuf = [| dummy_map_val (); 0sz |];
  let uhdr = mk_emphdrs uhdrauxbuf;
  let mut aadbuf = [| 0uy; 0sz |];
  let aadslice = S.from_array aadbuf 0sz;
  with aad. assert pure ((aad <: evercddl_bstr_pretty) == Mkevercddl_bstr_pretty0 { s = aadslice; p = 1.0R });
  rw_l (rel_bstr_eq aad (Mkspect_evercddl_bstr_pretty0 _));
  let res = sign1 privkey uhdr aad payload outbuf;
  with msg. assert pts_to res msg;
  rw_r (rel_bstr_eq aad (Mkspect_evercddl_bstr_pretty0 _));
  S.to_array aadslice;
  elim_trade _ (A.pts_to uhdrauxbuf _);
  res
}

fn verify_sig pubkey phdr aad payload (sigbuf: S.slice UInt8.t)
    (#vphdr: erased _) (#vaad: erased _) (#vpayload: erased _) (#ppubkey: erased _)
    #psigbuf (#vsigbuf: erased (Seq.seq UInt8.t) { Seq.length vsigbuf == 64 })
    (#vpubkey: erased (Seq.seq UInt8.t) { Seq.length vpubkey == 32 })
  requires S.pts_to pubkey #ppubkey vpubkey
  requires rel_evercddl_empty_or_serialized_map phdr vphdr
  requires rel_evercddl_bstr aad vaad
  requires rel_evercddl_bstr payload vpayload
  requires pts_to sigbuf #psigbuf vsigbuf
  returns success: bool
  ensures S.pts_to pubkey #ppubkey vpubkey
  ensures rel_evercddl_empty_or_serialized_map phdr vphdr
  ensures rel_evercddl_bstr aad vaad
  ensures rel_evercddl_bstr payload vpayload
  ensures pts_to sigbuf #psigbuf vsigbuf
  ensures pure (success <==> (exists tbs. to_be_signed_spec vphdr vaad vpayload tbs /\ spec_ed25519_verify vpubkey tbs vsigbuf))
{
  let sz = 1024sz;
  assert pure (SizeT.v sz <= 1024);
  let arr = V.alloc 0uy sz;
  Seq.lemma_create_len (SizeT.v sz) 0uy; //?!?
  V.to_array_pts_to arr;
  let outbuf = S.from_array (V.vec_to_array arr) sz;
  S.pts_to_len outbuf;
  assert pure (S.len outbuf == sz);
  let sig_struct = mk_sig_structure phdr aad payload;
  let written = serialize_Sig_structure' sig_struct outbuf;
  S.pts_to_len outbuf;
  assert pure (SizeT.v written <= SizeT.v sz);
  assert pure (SizeT.v written <= 1024);
  assert_norm (1024 < pow2 32);
  elim_trade _ _;
  if (written = 0sz) {
    abort ();
    with w. rewrite S.pts_to outbuf w ** S.is_from_array (V.vec_to_array arr) outbuf as emp;
    false
  } else {
    let tbs = Pulse.Lib.Slice.Util.subslice_trade outbuf 0sz written;
    with vtbs. assert S.pts_to tbs vtbs ** pure (to_be_signed_spec vphdr vaad vpayload vtbs);
    S.pts_to_len tbs;
    let success = verify () pubkey tbs sigbuf;
    elim_trade _ _;
    S.to_array outbuf;
    V.to_vec_pts_to arr;
    V.free arr;
    success
  }
}

let rel_sign1_tagged_eq (a: evercddl_COSE_Sign1_Tagged_pretty) (b: spect_evercddl_COSE_Sign1_Tagged_pretty) =
  assert_norm' (rel_evercddl_COSE_Sign1_Tagged a b ==
    ((COSE.Format.rel_evercddl_empty_or_serialized_map a._x0.protected b._x0._x0 **
            COSE.Format.rel_evercddl_header_map a._x0.unprotected b._x0._x1) **
        ((CDDL.Pulse.Types.rel_either COSE.Format.rel_evercddl_bstr
                COSE.Format.rel_evercddl_nil a._x0.payload b._x0._x2) **
            COSE.Format.rel_evercddl_bstr a._x0.signature b._x0._x3))
    )

let rel_bstr_eq' (x: evercddl_bstr_pretty) (y: spect_evercddl_bstr_pretty) =
  assert_norm' (rel_evercddl_bstr x y ==
      pts_to x._x0.s #x._x0.p y._x0 ** pure (false == false))

inline_for_extraction noextract
let sixty_four: v: SizeT.t { SizeT.v v == 64 } = 64sz

inline_for_extraction noextract
fn verify1_core pubkey aad (msg: evercddl_COSE_Sign1_Tagged_pretty { Inl? msg._x0.payload })
    #ppubkey (#vpubkey: erased (Seq.seq UInt8.t) { Seq.length vpubkey == 32 })
    (#vaad: erased _) (#vmsg: erased spect_evercddl_COSE_Sign1_Tagged_pretty { Inl? (reveal vmsg)._x0._x2 })
  requires S.pts_to pubkey #ppubkey vpubkey
  requires rel_evercddl_COSE_Sign1_Tagged msg vmsg
  requires rel_evercddl_bstr aad vaad

  returns success: bool
  ensures S.pts_to pubkey #ppubkey vpubkey
  ensures rel_evercddl_COSE_Sign1_Tagged msg vmsg
  ensures rel_evercddl_bstr aad vaad
  ensures pure (success <==>
      (let sig = (reveal vmsg)._x0._x3._x0 in
        Seq.length sig == 64 /\
        exists (tbs: Seq.seq UInt8.t{Seq.length tbs <= max_size_t}).
        to_be_signed_spec (reveal vmsg)._x0._x0 vaad (Inl?.v (reveal vmsg)._x0._x2) tbs /\
        spec_ed25519_verify vpubkey tbs sig))
{
  rw_r_wt (rel_sign1_tagged_eq _ _);
  rw_r_wt (rel_bstr_eq' msg._x0.signature _);
  rewrite_with_trade
    (rel_either rel_evercddl_bstr rel_evercddl_nil msg._x0.payload (reveal vmsg)._x0._x2)
    (rel_evercddl_bstr (Inl?.v msg._x0.payload) (Inl?.v (reveal vmsg)._x0._x2));
  let sig = msg._x0.signature._x0.s;
  rewrite each msg._x0.signature._x0.s as sig;
  S.pts_to_len sig;
  with vsig. assert S.pts_to sig #msg._x0.signature._x0.p vsig;
  if (S.len sig = sixty_four) {
    assert pure (S.len sig == sixty_four);
    assert pure (SizeT.v (S.len sig) == 64);
    assert pure (Seq.length vsig == 64);
    let success = verify_sig pubkey msg._x0.protected aad (Inl?.v msg._x0.payload) sig;
    elim_trade _ (rel_evercddl_bstr msg._x0.signature _);
    elim_trade _ (rel_either rel_evercddl_bstr rel_evercddl_nil msg._x0.payload (reveal vmsg)._x0._x2);
    elim_trade _ (rel_evercddl_COSE_Sign1_Tagged msg vmsg);
    success
  } else {
    elim_trade _ (rel_evercddl_bstr msg._x0.signature _);
    elim_trade _ (rel_either rel_evercddl_bstr rel_evercddl_nil msg._x0.payload (reveal vmsg)._x0._x2);
    elim_trade _ (rel_evercddl_COSE_Sign1_Tagged msg vmsg);
    assert pure (Seq.length vsig =!= 64);
    assert pure ((reveal vmsg)._x0._x3._x0 == vsig);
    false
  }
}

inline_for_extraction noextract
fn borrow_payload
    (msg: evercddl_COSE_Sign1_Tagged_pretty { Inl? msg._x0.payload })
    (#vmsg: erased spect_evercddl_COSE_Sign1_Tagged_pretty { Inl? (reveal vmsg)._x0._x2 })
  requires rel_evercddl_COSE_Sign1_Tagged msg vmsg
  returns payload: S.slice UInt8.t
  ensures
    borrows (pts_to payload #((Inl?.v msg._x0.payload)._x0.p) (Inl?.v (reveal vmsg)._x0._x2)._x0)
      (rel_evercddl_COSE_Sign1_Tagged msg vmsg)
{
  rw_r (rel_sign1_tagged_eq _ _);
  rewrite_with_trade
    (rel_either rel_evercddl_bstr rel_evercddl_nil msg._x0.payload (reveal vmsg)._x0._x2)
    (rel_evercddl_bstr (Inl?.v msg._x0.payload) (Inl?.v (reveal vmsg)._x0._x2));
  rw_r (rel_bstr_eq' (Inl?.v msg._x0.payload) _);
  ghost fn aux ()
    requires
      rel_evercddl_bstr msg._x0.signature (reveal vmsg)._x0._x3 **
      rel_evercddl_empty_or_serialized_map msg._x0.protected (reveal vmsg)._x0._x0 **
      rel_evercddl_header_map msg._x0.unprotected (reveal vmsg)._x0._x1 **
      trade (rel_evercddl_bstr (Inl?.v msg._x0.payload) (Inl?.v (reveal vmsg)._x0._x2))
        (rel_either rel_evercddl_bstr
            rel_evercddl_nil
            msg._x0.payload
            (reveal vmsg)._x0._x2)
    requires S.pts_to (Inl?.v msg._x0.payload)._x0.s #(Inl?.v msg._x0.payload)._x0.p
      (Inl?.v (reveal vmsg)._x0._x2)._x0
    ensures rel_evercddl_COSE_Sign1_Tagged msg vmsg
  {
    rw_l (rel_bstr_eq' (Inl?.v msg._x0.payload) _);
    elim_trade _ _;
    rw_l (rel_sign1_tagged_eq _ _);
  };
  intro_trade _ _ _ aux;
  (Inl?.v msg._x0.payload)._x0.s
}

noextract
let parses_from #t #st (s: CDDL.Spec.Base.spec t st true) (x: st) y : prop =
  match CBOR.Spec.API.Format.cbor_det_parse y with
  | Some (c, len) -> len == Seq.length y /\ t c /\ s.parser c == x
  | None -> False

let good_signature (pubkey: Seq.seq UInt8.t { Seq.length pubkey == 32 })
    (msg: Seq.seq UInt8.t) (aad: Seq.seq UInt8.t) (payload: Seq.seq UInt8.t) : prop =
  exists (vmsg: spect_evercddl_COSE_Sign1_Tagged_pretty) tbs.
  parses_from bundle_COSE_Sign1_Tagged''.b_spec vmsg msg /\
  vmsg._x0._x2 == Inl (Mkspect_evercddl_bstr_pretty0 payload) /\
  Seq.length vmsg._x0._x3._x0 == 64 /\
  to_be_signed_spec vmsg._x0._x0 { _x0 = aad } { _x0 = payload } tbs /\
  spec_ed25519_verify pubkey tbs vmsg._x0._x3._x0

#push-options "--z3rlimit 32"

let int_eq_of_diff_zero (a b: int) : Lemma (requires a - b == 0) (ensures a == b) = ()

#pop-options

let nat_eq_of_diff_zero (a b: nat) : Lemma (requires a - b == 0) (ensures a == b) =
  int_eq_of_diff_zero a b

inline_for_extraction // Karamel's lifetime support is massively lacking
fn verify1 pubkey aad msg
    #ppubkey (#vpubkey: erased (Seq.seq UInt8.t) { Seq.length vpubkey == 32 })
    (#vaad: erased _) #pmsg (#vmsg: erased _)
  requires S.pts_to pubkey #ppubkey vpubkey
  requires S.pts_to #UInt8.t msg #pmsg vmsg
  requires rel_evercddl_bstr aad vaad

  returns payload: option (S.slice UInt8.t)

  ensures S.pts_to pubkey #ppubkey vpubkey
  ensures rel_evercddl_bstr aad vaad
  ensures
    (match payload with
    | Some payload ->
      exists* ppayload vpayload.
        borrows (S.pts_to payload #ppayload vpayload) (S.pts_to msg #pmsg vmsg) **
        pure (good_signature vpubkey vmsg (reveal vaad)._x0 vpayload)
    | None -> S.pts_to msg #pmsg vmsg)
{
  let res = validate_and_parse_COSE_Sign1_Tagged msg;
  match res {
    None -> {
      unfold CDDL.Pulse.Parse.Base.validate_and_parse_post;
      None
    }
    Some res -> {
      match res {
        (x, rem) -> {
          unfold CDDL.Pulse.Parse.Base.validate_and_parse_post;
          unfold CDDL.Pulse.Parse.Base.validate_and_parse_post_some bundle_COSE_Sign1_Tagged.b_spec.CDDL.Spec.Base.parser
            rel_evercddl_COSE_Sign1_Tagged msg pmsg vmsg x rem;
          with y. assert rel_evercddl_COSE_Sign1_Tagged x y;
          with wr. assert pts_to rem #pmsg wr;

          rw_r_wt (rel_sign1_tagged_eq _ _);
          rel_either_cases _ _ _ _;
          elim_trade _ (rel_evercddl_COSE_Sign1_Tagged _ _);

          if (S.len rem = 0sz && Inl? x._x0.payload) {
            let len = hide (Some?.v (CBOR.Spec.API.Format.cbor_det_parse vmsg))._2;
            S.pts_to_len rem;
            assert pure (Seq.length wr == 0);
            Seq.lemma_len_slice vmsg len (Seq.length vmsg);
            nat_eq_of_diff_zero (Seq.length vmsg) len;
            assert pure (parses_from bundle_COSE_Sign1_Tagged''.b_spec y vmsg);
            let success = verify1_core pubkey aad x;
            if (success) {
              let payload = borrow_payload x;
              elim_hyp_r _ _ _;
              trade_compose _ (rel_evercddl_COSE_Sign1_Tagged _ _) _;
              Some payload
            } else {
              elim_trade _ (S.pts_to msg #pmsg vmsg);
              None
            }
          } else {
            elim_trade _ (S.pts_to msg #pmsg vmsg);
            None
          }
        }
      }
    }
  }
}

fn verify1_simple pubkey msg
    #ppubkey (#vpubkey: erased (Seq.seq UInt8.t) { Seq.length vpubkey == 32 })
    #pmsg (#vmsg: erased _)
  requires S.pts_to pubkey #ppubkey vpubkey
  requires S.pts_to #UInt8.t msg #pmsg vmsg

  returns payload: option (S.slice UInt8.t)
  ensures S.pts_to pubkey #ppubkey vpubkey
  ensures
    (match payload with
    | Some payload ->
      exists* ppayload vpayload.
        borrows (S.pts_to payload #ppayload vpayload) (S.pts_to msg #pmsg vmsg) **
        pure (good_signature vpubkey vmsg (Seq.create 0 0uy) vpayload)
    | None -> S.pts_to msg #pmsg vmsg)
{
  let mut aadbuf = [| 0uy; 0sz |];
  let aadslice = S.from_array aadbuf 0sz;
  with aad. assert pure ((aad <: evercddl_bstr_pretty) == Mkevercddl_bstr_pretty0 { s = aadslice; p = 1.0R });
  rw_l (rel_bstr_eq aad (Mkspect_evercddl_bstr_pretty0 _));
  let res = verify1 pubkey aad msg;
  rw_r (rel_bstr_eq aad (Mkspect_evercddl_bstr_pretty0 _));
  S.to_array aadslice;
  res
}

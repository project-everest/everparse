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

fn mk_sig_structure phdr aad payload #vphdr #vaad #vpayload
  requires rel_evercddl_empty_or_serialized_map phdr vphdr
  requires rel_evercddl_bstr aad vaad
  requires rel_evercddl_bstr payload vpayload
  returns r: _
  ensures rel_evercddl_Sig_structure r (mk_sig_structure_spec vphdr vaad vpayload)
  ensures pure (r.context == signature1)
  ensures pure (r.body_protected == phdr)
  ensures pure (r._x0 == Inr (aad, payload))
{
  rewrite emp as rel_either rel_unit rel_unit signature1 signature1;
  rw_l (rel_sig_structure_eq (Mkevercddl_Sig_structure_pretty0 signature1 phdr (Inr (aad, payload)))
    (Mkspect_evercddl_Sig_structure_pretty0 signature1 vphdr (Inr (vaad, vpayload))));
  with res vres. assert rel_evercddl_Sig_structure res vres;
  rewrite each vres as mk_sig_structure_spec vphdr vaad vpayload;
  res
}

ghost fn norm_r p s
  requires p
  ensures norm s p
{
  norm_spec s p;
  rewrite p as norm s p
}

let unfold_plus p lids =
  norm_r p [delta_only lids; iota; primops]

ghost fn free_mk_sig_structure
    (ss: evercddl_Sig_structure_pretty { ss.context == signature1 })
    (phdr: _ { ss.body_protected == phdr })
    aad (payload: _ { ss._x0 == Inr (aad, payload) })
    #vphdr #vaad #vpayload
  requires rel_evercddl_Sig_structure ss (mk_sig_structure_spec vphdr vaad vpayload)
  ensures rel_evercddl_empty_or_serialized_map phdr vphdr
  ensures rel_evercddl_bstr aad vaad
  ensures rel_evercddl_bstr payload vpayload
{
  rewrite each ss as (Mkevercddl_Sig_structure_pretty0 signature1 phdr (Inr (aad, payload)));
  unfold_plus (rel_evercddl_Sig_structure _ _) [`%mk_sig_structure_spec];
  rw_r (rel_sig_structure_eq _ _);
  rewrite rel_either rel_unit rel_unit signature1 signature1 as emp;
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
    #vphdr #vaad #vpayload #pprivkey (#vprivkey: erased (Seq.seq UInt8.t) { Seq.length vprivkey == 32 })
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
  free_mk_sig_structure sig_struct phdr aad payload;
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

fn main () returns exitcode: Int32.t { 0l }
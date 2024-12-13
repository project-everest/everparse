module CBORTest.Base
open CBOR.Spec.Constants
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module SM = Pulse.Lib.SeqMatch.Util
module Trade = Pulse.Lib.Trade.Util
module Spec = CBOR.Spec.API.Format
module I32 = FStar.Int32
module S = Pulse.Lib.Slice
module Base = CBOR.Pulse.API.Base
module SU = Pulse.Lib.Slice.Util

inline_for_extraction
noextract [@@noextract_to "krml"]
let letter (x: U8.t { 1 <= U8.v x /\ U8.v x <= 26 }) : U8.t =
  U8.add 96uy x

#push-options "--fuel 8 --z3rlimit 16"

noextract [@@noextract_to "krml"]
let spec_bar () : Pure (Seq.seq U8.t)
  (requires True)
  (ensures fun v ->
    Seq.length v = 3 /\
    Seq.index v 0 == letter 2uy /\
    Seq.index v 1 == letter 1uy /\
    Seq.index v 2 == letter 18uy /\
    CBOR.Spec.API.UTF8.correct v
  )
= let v = Seq.seq_of_list [letter 2uy; letter 1uy; letter 18uy] in
  CBOR.Spec.API.UTF8.ascii_is_utf8 v;
  v

noextract [@@noextract_to "krml"]
let spec_test_on
  (x: Spec.cbor)
: Tot prop
= match Spec.unpack x with
  | Spec.CArray [_; _; xm] ->
    begin match Spec.unpack xm with
    | Spec.CMap m ->
      begin match Spec.cbor_map_get m (Spec.pack (Spec.CString cbor_major_type_text_string (spec_bar ()))) with
      | Some xv ->
        begin match Spec.unpack xv with
        | Spec.CInt64 ty v -> ty == cbor_major_type_neg_int64 /\ v == 42uL
        | _ -> False
        end
      | _ -> False
      end
    | _ -> False
    end
  | _ -> False

inline_for_extraction
noextract [@@noextract_to "krml"]
let exit_success : I32.t = 0l

inline_for_extraction
noextract [@@noextract_to "krml"]
let exit_serialization_failure : I32.t = 1l

inline_for_extraction
noextract [@@noextract_to "krml"]
let exit_impossible : I32.t = 2l

inline_for_extraction
```pulse
fn slice_from_array_trade
  (#t: Type) (a: A.array t) (#p: perm) (alen: SZ.t) (#v: Ghost.erased (Seq.seq t))
  requires
    (pts_to a #p v ** pure (SZ.v alen == A.length a))
  returns s: S.slice t
  ensures
    (pts_to s #p v **
      Trade.trade
        (pts_to s #p v)
        (pts_to a #p v)
    )
{
  let s = S.from_array a alen;
  ghost fn aux (_: unit)
    requires S.is_from_array a s ** pts_to s #p v
    ensures pts_to a #p v
  {
    S.to_array s
  };
  Trade.intro _ _ _ aux;
  s
}
```

inline_for_extraction
noextract [@@noextract_to "krml"]
#restart-solver
```pulse
fn test_on
  (#cbor_t: Type0)
  (cbor_match: perm -> cbor_t -> Spec.cbor -> slprop)
  (cbor_major_type: Base.get_major_type_t cbor_match)
  (cbor_get_array_length: Base.get_array_length_t cbor_match)
  (cbor_get_array_item: Base.get_array_item_t cbor_match)
  (cbor_mk_string: Base.mk_string_t cbor_match)
  (cbor_map_get_gen: Base.map_get_t cbor_match)
  (cbor_read_uint64: Base.read_uint64_t cbor_match)
  (test: cbor_t)
  (#p: perm)
  (#v: Ghost.erased Spec.cbor)
requires
  cbor_match p test v **
  pure (spec_test_on v)
returns res: I32.t
ensures
  cbor_match p test v **
  pure (res == exit_success)
{
  let ty = cbor_major_type test;
  if (ty <> cbor_major_type_array) {
    exit_impossible
  } else {
    let len = cbor_get_array_length test;
    if (len <> 3uL) {
      exit_impossible
    } else {
      let m = cbor_get_array_item test 2uL;
      let ty = cbor_major_type m;
      if (ty <> cbor_major_type_map) {
        Trade.elim (cbor_match _ m _) _;
        exit_impossible
      } else {
        let mut bar_payload = [| letter 2uy; 3sz |];
        bar_payload.(1sz) <- letter 1uy;
        bar_payload.(2sz) <- letter 18uy;
        with s . assert (A.pts_to bar_payload s);
        assert (pure (Seq.equal s (spec_bar ())));
        let bar_payload_as_slice = slice_from_array_trade bar_payload 3sz;
        let bar = cbor_mk_string cbor_major_type_text_string bar_payload_as_slice;
        Trade.trans (cbor_match _ bar _) _ _;
        let ov = cbor_map_get_gen m bar;
        with pm vm vk . assert (Base.map_get_post cbor_match m pm vm vk ov);
        Trade.elim (cbor_match _ bar _) _;
        match ov {
          None -> {
            rewrite (Base.map_get_post cbor_match m pm vm vk ov)
              as (Base.map_get_post_none cbor_match m pm vm vk);
            unfold (Base.map_get_post_none cbor_match m pm vm vk);
            Trade.elim (cbor_match _ m _) _;
            exit_impossible
          }
          Some v -> {
            rewrite (Base.map_get_post cbor_match m pm vm vk ov)
              as (Base.map_get_post_some cbor_match m pm vm vk v);
            unfold (Base.map_get_post_some cbor_match m pm vm vk v);
            let ty = cbor_major_type v;
            if (ty <> cbor_major_type_neg_int64) {
              Trade.elim (cbor_match _ v _) _;
              Trade.elim (cbor_match _ m _) _;
              exit_impossible
            } else {
              let i = cbor_read_uint64 v;
              Trade.elim (cbor_match _ v _) _;
              Trade.elim (cbor_match _ m _) _;
              if (i <> 42uL) {
                exit_impossible
              } else {
                exit_success
              }
            }
          }
        }
      }
    }
  }
}
```

#pop-options

let cbor_det_serialize_inj_strong
  (x1 x2: Spec.cbor)
  (y1 y2: Seq.seq U8.t)
: Lemma
  (requires (Spec.cbor_det_serialize x1 `Seq.append` y1 == Spec.cbor_det_serialize x2 `Seq.append` y2))
  (ensures (x1 == x2 /\ y1 == y2))
  [SMTPat (Spec.cbor_det_serialize x1 `Seq.append` y1); SMTPat (Spec.cbor_det_serialize x2 `Seq.append` y2)]
= Spec.cbor_det_serialize_inj_strong x1 x2 y1 y2

inline_for_extraction
noextract [@@noextract_to "krml"]
let res_post
  (res: I32.t)
: Tot prop
= res == exit_success \/ res == exit_serialization_failure

inline_for_extraction
noextract [@@noextract_to "krml"]
let res_t = (res: I32.t { res_post res })

inline_for_extraction
noextract [@@noextract_to "krml"]
let intro_res_post_success : res_t = exit_success

inline_for_extraction
noextract [@@noextract_to "krml"]
let intro_res_post_serialization_failure : res_t = exit_serialization_failure

inline_for_extraction
noextract [@@noextract_to "krml"]
let intro_res_post_impossible (_: squash False) : res_t = exit_impossible

#push-options "--fuel 8 --z3rlimit 128"

#restart-solver
inline_for_extraction
noextract [@@noextract_to "krml"]
```pulse
fn aux
  (#cbor_t: Type0)
  (#cbor_match: perm -> cbor_t -> Spec.cbor -> slprop)
  (cbor_major_type: Base.get_major_type_t cbor_match)
  (cbor_equal: Base.equal_t cbor_match)
  (cbor_parse_from_slice: Base.cbor_det_parse_t cbor_match)
  (cbor_serialize_to_slice: Base.cbor_det_serialize_t cbor_match)
  (cbor_get_array_length: Base.get_array_length_t cbor_match)
  (cbor_get_array_item: Base.get_array_item_t cbor_match)
  (cbor_mk_string: Base.mk_string_t cbor_match)
  (cbor_map_get_gen: Base.map_get_t cbor_match)
  (cbor_read_uint64: Base.read_uint64_t cbor_match)
  (test: cbor_t)
  (#p: perm)
  (#v: Ghost.erased Spec.cbor)
requires
  cbor_match p test v **
  pure (spec_test_on v)
returns res: res_t
ensures
  cbor_match p test v
{
  let res = test_on
    cbor_match
    cbor_major_type 
    cbor_get_array_length
    cbor_get_array_item
    cbor_mk_string
    cbor_map_get_gen
    cbor_read_uint64
    test;
  if (res <> exit_success) {
    intro_res_post_impossible ()
  } else {
    let max_size = 32sz;
    let mut output_bytes = [| 0xFFuy; max_size |];
    let out1 = S.from_array output_bytes max_size;
    let osize1 = cbor_serialize_to_slice test out1;
    match osize1 {
      None -> {
        S.to_array out1;
        intro_res_post_serialization_failure // I cannot prove that this case cannot happen
      }
      Some size1 -> {
        with v1 . assert (pts_to out1 v1);
//        Seq.lemma_split v1 (SZ.v size1);
        let ps1 = cbor_parse_from_slice out1;
        match ps1 {
          None -> {
            unfold (Base.cbor_det_parse_post cbor_match out1 1.0R v1 None);
            S.to_array out1;
            intro_res_post_impossible ()
          }
          Some sr1 -> {
            let Mktuple2 test1 r1 = sr1;
            unfold (Base.cbor_det_parse_post cbor_match out1 1.0R v1 (Some (test1, r1)));
            unfold (Base.cbor_det_parse_post_some cbor_match out1 1.0R v1 test1 r1);
            let eq1 = cbor_equal test1 test;
            if (not eq1) {
              Trade.elim (cbor_match _ test1 _) _;
              S.to_array out1;
              intro_res_post_impossible ()
            } else {
              admit ()
            }
          }
        }
      }
    }
  }
}
```

#restart-solver
inline_for_extraction
noextract [@@noextract_to "krml"]
```pulse
fn main
  (#cbor_t: Type0)
  (#cbor_map_entry_t: Type0)
  (cbor_match: perm -> cbor_t -> Spec.cbor -> slprop)
  (cbor_map_entry_match: perm -> cbor_map_entry_t -> (Spec.cbor & Spec.cbor) -> slprop)
  (cbor_major_type: Base.get_major_type_t cbor_match)
  (cbor_equal: Base.equal_t cbor_match)
  (cbor_parse_from_slice: Base.cbor_det_parse_t cbor_match)
  (cbor_serialize_to_slice: Base.cbor_det_serialize_t cbor_match)
  (cbor_mk_string: Base.mk_string_t cbor_match)
  (cbor_mk_array: Base.mk_array_t cbor_match)
  (cbor_get_array_length: Base.get_array_length_t cbor_match)
  (cbor_get_array_item: Base.get_array_item_t cbor_match)
  (cbor_mk_tagged: Base.mk_tagged_t cbor_match)
  (cbor_mk_int64: Base.mk_int64_t cbor_match)
  (cbor_elim_int64: Base.elim_int64_t cbor_match)
  (cbor_read_uint64: Base.read_uint64_t cbor_match)
  (cbor_mk_map_from_array: Base.mk_map_from_array_t cbor_match cbor_map_entry_match)
  (cbor_map_get_gen: Base.map_get_t cbor_match)
  (cbor_mk_map_entry: Base.mk_map_entry_t cbor_match cbor_map_entry_match)
requires emp
returns res: res_t
ensures emp
{
  Classical.forall_intro (Classical.move_requires CBOR.Spec.API.UTF8.ascii_is_utf8);
  let mut foo0 = [| letter 6uy; 3sz |];
  foo0.(1sz) <- letter 15uy;
  foo0.(2sz) <- letter 15uy;
  with foo_v . assert (A.pts_to foo0 foo_v);
  let foo_slice = slice_from_array_trade foo0 3sz;
  let foo = cbor_mk_string cbor_major_type_text_string foo_slice;
  Trade.trans (cbor_match _ foo _) _ _;
  let i18 = Base.mk_int64_trade _ cbor_mk_int64 cbor_elim_int64 cbor_major_type_uint64 18uL;
  let foo_i18 = cbor_mk_map_entry foo i18;
  Trade.trans_concl_l (cbor_map_entry_match 1.0R foo_i18 _) _ _ _;
  Trade.trans_concl_r (cbor_map_entry_match 1.0R foo_i18 _) _ _ _;
  let mut map_entries = [| foo_i18; 3sz |];
  let mut bar0 = [| letter 2uy; 3sz |];
  bar0.(1sz) <- letter 1uy;
  bar0.(2sz) <- letter 18uy;
  with bar_v . assert (A.pts_to bar0 bar_v);
  assert (pure (~ (Seq.index foo_v 0 == Seq.index bar_v 0))); // necessary to prove that foo <> bar
  assert (pure (Seq.equal bar_v (spec_bar ())));
  let bar_slice = slice_from_array_trade bar0 3sz;
  let bar = cbor_mk_string cbor_major_type_text_string bar_slice;
  Trade.trans (cbor_match _ bar _) _ _;
  let i42 = Base.mk_int64_trade _ cbor_mk_int64 cbor_elim_int64 cbor_major_type_neg_int64 42uL;
  let bar_i42 = cbor_mk_map_entry bar i42;
  Trade.trans_concl_l (cbor_map_entry_match 1.0R bar_i42 _) _ _ _;
  Trade.trans_concl_r (cbor_map_entry_match 1.0R bar_i42 _) _ _ _;
  map_entries.(1sz) <- bar_i42;
  let i1729 = Base.mk_int64_trade _ cbor_mk_int64 cbor_elim_int64 cbor_major_type_uint64 1729uL;
  let mut quux0 = [| letter 17uy; 4sz |];
  quux0.(1sz) <- letter 21uy;
  quux0.(2sz) <- letter 21uy;
  quux0.(3sz) <- letter 24uy;
  let quux_slice = slice_from_array_trade quux0 4sz;
  let quux = cbor_mk_string cbor_major_type_text_string quux_slice;
  Trade.trans (cbor_match _ quux _) _ _;
  let i1729_quux = cbor_mk_map_entry i1729 quux;
  Trade.trans_concl_l (cbor_map_entry_match 1.0R i1729_quux _) _ _ _;
  Trade.trans_concl_r (cbor_map_entry_match 1.0R i1729_quux _) _ _ _;
  map_entries.(2sz) <- i1729_quux;
  SM.seq_list_match_singleton_intro_trade i1729_quux _ (cbor_map_entry_match 1.0R);
  Trade.trans _ (cbor_map_entry_match 1.0R i1729_quux _) _;
  SM.seq_list_match_cons_intro_trade bar_i42 _ _ _ (cbor_map_entry_match 1.0R);
  Trade.trans_concl_r _ (cbor_map_entry_match 1.0R bar_i42 _) _ _;
  Trade.trans_concl_l _ (cbor_map_entry_match 1.0R bar_i42 _) _ _;
  SM.seq_list_match_cons_intro_trade foo_i18 _ _ _ (cbor_map_entry_match 1.0R);
  Trade.trans_concl_r _ (cbor_map_entry_match 1.0R foo_i18 _) _ _;
  Trade.trans_concl_l _ (cbor_map_entry_match 1.0R foo_i18 _) _ _;
  let map = Base.mk_map_from_array' cbor_mk_map_from_array map_entries 3uL _;
  Trade.trans_concl_r (cbor_match _ map _) _ _ _;
  let myint0 = Base.mk_int64_trade _ cbor_mk_int64 cbor_elim_int64 cbor_major_type_uint64 2uL;
  let mut myint = myint0;
  let array_entry0 = cbor_mk_tagged 1234uL myint;
  Trade.trans_concl_r (cbor_match _ array_entry0 _) _ _ _;
  let mut array_entry1_payload = [| 18uy; 4sz |];
  array_entry1_payload.(1sz) <- 42uy;
  array_entry1_payload.(2sz) <- 17uy;
  array_entry1_payload.(3sz) <- 29uy;
  let array_entry1_slice = slice_from_array_trade array_entry1_payload 4sz;
  let array_entry1 = cbor_mk_string cbor_major_type_byte_string array_entry1_slice;
  Trade.trans (cbor_match _ array_entry1 _) _ _;
  let mut array = [| array_entry0; 3sz |];
  array.(1sz) <- array_entry1;
  array.(2sz) <- map;
  SM.seq_list_match_singleton_intro_trade map _ (cbor_match 1.0R);
  Trade.trans _ (cbor_match 1.0R map _) _;
  SM.seq_list_match_cons_intro_trade array_entry1 _ _ _ (cbor_match 1.0R);
  Trade.trans_concl_r _ (cbor_match 1.0R array_entry1 _) _ _;
  Trade.trans_concl_l _ (cbor_match 1.0R array_entry1 _) _ _;
  SM.seq_list_match_cons_intro_trade array_entry0 _ _ _ (cbor_match 1.0R);
  Trade.trans_concl_r _ (cbor_match 1.0R array_entry0 _) _ _;
  Trade.trans_concl_l _ (cbor_match 1.0R array_entry0 _) _ _;
  let array_as_slice = slice_from_array_trade array 3sz;
  S.pts_to_len array_as_slice;
  let test = Base.mk_array' cbor_mk_array array_as_slice _;
  Trade.trans_concl_l (cbor_match _ test _) _ _ _;
  Trade.trans_concl_r (cbor_match _ test _) _ _ _;
  let res = aux
    cbor_major_type
    cbor_equal
    cbor_parse_from_slice
    cbor_serialize_to_slice
    cbor_get_array_length
    cbor_get_array_item
    cbor_mk_string
    cbor_map_get_gen
    cbor_read_uint64
    test;
  Trade.elim (cbor_match _ test _) _;
  res
}
```

(*


    let size = cbor_det_size test max_size;
    if (size = 0sz) {
      Trade.elim (cbor_match _ test _) _;
      intro_res_post_serialization_failure // I cannot prove that this case cannot happen
    } else {
      let out1 = S.from_array output_bytes max_size;
      S.pts_to_len out1;
      let size' = cbor_det_serialize_to_slice test out1;
      if (size' <> size) {
        S.to_array out1;
        Trade.elim (cbor_match _ test _) _;
        intro_res_post_impossible ()
      } else {
        admit ()
      }
    }


        let size' = cbor_det_validate_from_slice out1;
        if (size' <> size) {
          S.to_array out1;
          Trade.elim (cbor_match _ test _) _;
          intro_res_post_impossible ()
        } else {
          with w . assert (pts_to out1 w);
          Seq.lemma_split w (SZ.v size');
          let test1 = cbor_det_parse_from_slice out1 size';
          let b = cbor_equal test test1;
          if (not b) {
            Trade.elim (cbor_match _ test1 _) _;
            S.to_array out1;
            Trade.elim (cbor_match _ test _) _;
            intro_res_post_impossible ()
          } else {
            let res = test_on test1;
            Trade.elim (cbor_match _ test1 _) _;
            if (res <> exit_success) {
              S.to_array out1;
              Trade.elim (cbor_match _ test _) _;
              intro_res_post_impossible ()
            } else {
              let Mktuple2 out2 out3 = S.split out1 size';
              Seq.append_empty_r (Seq.slice w 0 (SZ.v size'));
              let test2 = cbor_det_parse_from_slice out2 size';
              let b = cbor_equal test test2;
              if (not b) {
                 Trade.elim (cbor_match _ test2 _) _;
                 S.join out2 out3 out1;
                 S.to_array out1;
                 Trade.elim (cbor_match _ test _) _;
                 intro_res_post_impossible ()
              } else {
                let res = test_on test2;
                Trade.elim (cbor_match _ test2 _) _;
                S.join out2 out3 out1;
                S.to_array out1;
                Trade.elim (cbor_match _ test _) _;
                if (res <> exit_success) {
                   intro_res_post_impossible ()
                } else {
                  intro_res_post_success
                }
              }
            }
          }
        }
      }
    }
  }
}
```
*)

#pop-options

module CBORTest
open CBOR.Spec.Constants
open CBOR.Pulse.API.Det.C
module C = C
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module SM = Pulse.Lib.SeqMatch.Util
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
noextract [@@noextract_to "krml"]
let letter (x: U8.t { 1 <= U8.v x /\ U8.v x <= 26 }) : U8.t =
  U8.add 96uy x

#push-options "--fuel 8 --z3rlimit 16"

#restart-solver
```pulse
fn main (_: unit)
requires emp
returns res: C.exit_code
ensures pure (res == C.EXIT_SUCCESS)
{
  Classical.forall_intro (Classical.move_requires CBOR.Spec.API.UTF8.ascii_is_utf8);
  let mut foo0 = [| letter 6uy; 3sz |];
  foo0.(1sz) <- letter 15uy;
  foo0.(2sz) <- letter 15uy;
  with foo_v . assert (A.pts_to foo0 foo_v);
  let foo = cbor_det_mk_string_from_array () cbor_major_type_text_string foo0 3uL;
  let i18 = cbor_det_mk_int64' cbor_major_type_uint64 18uL;
  let foo_i18 = cbor_det_mk_map_entry () foo i18;
  Trade.trans_concl_l (cbor_det_map_entry_match 1.0R foo_i18 _) _ _ _;
  Trade.trans_concl_r (cbor_det_map_entry_match 1.0R foo_i18 _) _ _ _;
  let mut map_entries = [| foo_i18; 3sz |];
  let mut bar0 = [| letter 2uy; 3sz |];
  bar0.(1sz) <- letter 1uy;
  bar0.(2sz) <- letter 18uy;
  with bar_v . assert (A.pts_to bar0 bar_v);
  assert (pure (~ (Seq.index foo_v 0 == Seq.index bar_v 0))); // necessary to prove that foo <> bar
  let bar = cbor_det_mk_string_from_array () cbor_major_type_text_string bar0 3uL;
  let i42 = cbor_det_mk_int64' cbor_major_type_neg_int64 42uL;
  let bar_i42 = cbor_det_mk_map_entry () bar i42;
  Trade.trans_concl_l (cbor_det_map_entry_match 1.0R bar_i42 _) _ _ _;
  Trade.trans_concl_r (cbor_det_map_entry_match 1.0R bar_i42 _) _ _ _;
  map_entries.(1sz) <- bar_i42;
  let i1729 = cbor_det_mk_int64' cbor_major_type_uint64 1729uL;
  let mut quux0 = [| letter 17uy; 4sz |];
  quux0.(1sz) <- letter 21uy;
  quux0.(2sz) <- letter 21uy;
  quux0.(3sz) <- letter 24uy;
  let quux = cbor_det_mk_string_from_array () cbor_major_type_text_string quux0 4uL;
  let i1729_quux = cbor_det_mk_map_entry () i1729 quux;
  Trade.trans_concl_l (cbor_det_map_entry_match 1.0R i1729_quux _) _ _ _;
  Trade.trans_concl_r (cbor_det_map_entry_match 1.0R i1729_quux _) _ _ _;
  map_entries.(2sz) <- i1729_quux;
  SM.seq_list_match_singleton_intro_trade i1729_quux _ (cbor_det_map_entry_match 1.0R);
  Trade.trans _ (cbor_det_map_entry_match 1.0R i1729_quux _) _;
  SM.seq_list_match_cons_intro_trade bar_i42 _ _ _ (cbor_det_map_entry_match 1.0R);
  Trade.trans_concl_r _ (cbor_det_map_entry_match 1.0R bar_i42 _) _ _;
  Trade.trans_concl_l _ (cbor_det_map_entry_match 1.0R bar_i42 _) _ _;
  SM.seq_list_match_cons_intro_trade foo_i18 _ _ _ (cbor_det_map_entry_match 1.0R);
  Trade.trans_concl_r _ (cbor_det_map_entry_match 1.0R foo_i18 _) _ _;
  Trade.trans_concl_l _ (cbor_det_map_entry_match 1.0R foo_i18 _) _ _;
  let map = cbor_det_mk_map_from_array' map_entries 3uL _;
  Trade.trans_concl_r (cbor_det_match _ map _) _ _ _;
  let myint0 = cbor_det_mk_int64' cbor_major_type_uint64 2uL;
  let mut myint = myint0;
  let array_entry0 = cbor_det_mk_tagged () 1234uL myint;
  Trade.trans_concl_r (cbor_det_match _ array_entry0 _) _ _ _;
  let mut array_entry1_payload = [| 18uy; 4sz |];
  array_entry1_payload.(1sz) <- 42uy;
  array_entry1_payload.(2sz) <- 17uy;
  array_entry1_payload.(3sz) <- 29uy;
  let array_entry1 = cbor_det_mk_string_from_array () cbor_major_type_byte_string array_entry1_payload 4uL;
  let mut array = [| array_entry0; 3sz |];
  array.(1sz) <- array_entry1;
  array.(2sz) <- map;
  SM.seq_list_match_singleton_intro_trade map _ (cbor_det_match 1.0R);
  Trade.trans _ (cbor_det_match 1.0R map _) _;
  SM.seq_list_match_cons_intro_trade array_entry1 _ _ _ (cbor_det_match 1.0R);
  Trade.trans_concl_r _ (cbor_det_match 1.0R array_entry1 _) _ _;
  Trade.trans_concl_l _ (cbor_det_match 1.0R array_entry1 _) _ _;
  SM.seq_list_match_cons_intro_trade array_entry0 _ _ _ (cbor_det_match 1.0R);
  Trade.trans_concl_r _ (cbor_det_match 1.0R array_entry0 _) _ _;
  Trade.trans_concl_l _ (cbor_det_match 1.0R array_entry0 _) _ _;
  let test = cbor_det_mk_array_from_array' array 3uL _;
  Trade.trans_concl_r (cbor_det_match _ test _) _ _ _;

  Trade.elim _ _;
  C.EXIT_SUCCESS
}
```

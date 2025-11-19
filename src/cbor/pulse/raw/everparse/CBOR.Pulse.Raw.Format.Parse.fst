module CBOR.Pulse.Raw.Format.Parse
#lang-pulse
open CBOR.Pulse.Raw.EverParse.Serialized.Base
friend CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Format
open LowParse.Spec.Base
open LowParse.Pulse.Base

module CompareBytes = CBOR.Pulse.Raw.Compare.Bytes

#push-options "--split_queries no --fuel 0 --ifuel 0"
#push-options "--z3rlimit_factor 4"
let parse_fail_no_serialize
  (v: Seq.seq U8.t)
: Lemma
  (requires (None? (parse parse_raw_data_item v)))
  (ensures (~ (exists v1 v2 . v == serialize_cbor v1 `Seq.append` v2)))
= introduce forall v1 v2.
    (v == serialize_cbor v1 `Seq.append` v2) ==> False
  with introduce _ ==> _
  with _ . (
    parse_strong_prefix #parse_raw_data_item_kind #raw_data_item parse_raw_data_item (serialize_cbor v1) v
  )
#pop-options

let cbor_validate_aux
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Lemma
  (requires validate_nonempty_post parse_raw_data_item 0sz v res)
  (ensures (
      if SZ.v res = 0
      then (~ (exists v1 v2 . v == serialize_cbor v1 `Seq.append` v2))
      else exists v1 v2 . v == serialize_cbor v1 `Seq.append` v2 /\
        SZ.v res == Seq.length (serialize_cbor v1)
  ))
= assert (v == Seq.slice v 0 (Seq.length v));
  if SZ.v res = 0
  then parse_fail_no_serialize v
  else begin
    let Some (v', consumed) = parse parse_raw_data_item v in
    parsed_data_is_serialize #parse_raw_data_item_kind #raw_data_item #parse_raw_data_item serialize_raw_data_item v;
    assert (v == serialize_cbor v' `Seq.append` Seq.slice v (SZ.v res) (Seq.length v))
  end

fn cbor_validate
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  requires pts_to input #pm v
  returns res: SZ.t
  ensures pts_to input #pm v ** pure (
      if SZ.v res = 0
      then (~ (exists v1 v2 . Ghost.reveal v == serialize_cbor v1 `Seq.append` v2))
      else exists v1 v2 . Ghost.reveal v == serialize_cbor v1 `Seq.append` v2 /\ SZ.v res == Seq.length (serialize_cbor v1)
  )
{
  let res = validate_nonempty (validate_raw_data_item (assume SZ.fits_u64)) input 0sz;
  cbor_validate_aux res v;
  res
}

let cbor_parse_aux
  (len: SZ.t)
  (v: Seq.seq U8.t)
: Lemma
  (requires
      exists v1 v2 . v == serialize_cbor v1 `Seq.append` v2 /\ SZ.v len == Seq.length (serialize_cbor v1)
  )
  (ensures (validator_success parse_raw_data_item 0sz v len /\ (
    match parse parse_raw_data_item v with
    | None -> False
    | Some (v', consumed) -> SZ.v len == consumed /\
      Seq.slice v 0 (SZ.v len) == serialize_cbor v'
  )))
= match parse parse_raw_data_item v with
  | None -> parse_fail_no_serialize v
  | Some (v', consumed) ->
    parsed_data_is_serialize #parse_raw_data_item_kind #raw_data_item #parse_raw_data_item serialize_raw_data_item v;
    Seq.lemma_split v consumed;
    Seq.lemma_append_inj
      (Seq.slice v 0 consumed)
      (Seq.slice v consumed (Seq.length v))
      (serialize_raw_data_item v')
      (Seq.slice v consumed (Seq.length v));
    let prf
      (v1: raw_data_item)
      (v2: Seq.seq U8.t)
    : Lemma
      (requires (v == serialize_cbor v1 `Seq.append` v2))
      (ensures (v1 == v'))
    = parsed_data_is_serialize #parse_raw_data_item_kind #raw_data_item #parse_raw_data_item serialize_raw_data_item v;
      serialize_strong_prefix serialize_raw_data_item v1 v' v2 (Seq.slice v consumed (Seq.length v))
    in
    Classical.forall_intro_2 (fun v1 v2 -> Classical.move_requires (prf v1) v2);
    ()

module Trade = Pulse.Lib.Trade.Util

#push-options "--z3rlimit 16"

#restart-solver

inline_for_extraction
fn impl_holds_on_raw_data_item
  (f64: squash SZ.fits_u64)
  (p: Ghost.erased (raw_data_item -> bool))
  (impl_p: LowParse.Pulse.Recursive.impl_pred_t serialize_raw_data_item_param p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased raw_data_item)
  requires pts_to_serialized serialize_raw_data_item input #pm v
  returns res: bool
  ensures pts_to_serialized serialize_raw_data_item input #pm v ** pure (res == holds_on_raw_data_item p v)
{
  LowParse.Pulse.Recursive.impl_pred_recursive serialize_raw_data_item_param (jump_leaf ()) (jump_recursive_step_count_leaf f64) (holds_on_raw_data_item_pred p) impl_p input
}

module U64 = FStar.UInt64
module U8 = FStar.UInt8

#restart-solver
#push-options "--fuel 1"
let impl_raw_uint64_optimal
  (x: raw_uint64)
: Pure bool
    (requires True)
    (ensures fun res -> res == CBOR.Spec.Raw.Optimal.raw_uint64_optimal x)
= if
    (x.value `U64.lte` FStar.Int.Cast.uint8_to_uint64 max_simple_value_additional_info) = (x.size = 0uy)
  then
    if x.size `U8.lte` 1uy
    then true
    else if x.size = 2uy
    then 256uL `U64.lte` x.value
    else if x.size = 3uy
    then 65536uL `U64.lte` x.value
    else begin
      assert (x.size = 4uy);
      4294967296uL `U64.lte` x.value
    end
  else false
#pop-options
#pop-options
#pop-options

#push-options "--z3rlimit 32"

let synth_nlist_recursive_cons_injective
  (p: LowParse.Spec.Recursive.parse_recursive_param)
  (n: pos)
: Lemma
  (LowParse.Pulse.Combinators.synth_injective (LowParse.Pulse.Recursive.synth_nlist_recursive_cons p n))
  [SMTPat (LowParse.Pulse.Combinators.synth_injective (LowParse.Pulse.Recursive.synth_nlist_recursive_cons p n))]
= LowParse.Pulse.Recursive.synth_nlist_recursive_cons_injective p n

let synth_nlist_recursive_cons_recip_inverse
  (#p: LowParse.Spec.Recursive.parse_recursive_param)
  (s: LowParse.Spec.Recursive.serialize_recursive_param p)
  (n: pos)
: Lemma
  (LowParse.Pulse.Combinators.synth_inverse (LowParse.Pulse.Recursive.synth_nlist_recursive_cons p n) (LowParse.Pulse.Recursive.synth_nlist_recursive_cons_recip s n))
  [SMTPat (LowParse.Pulse.Combinators.synth_inverse (LowParse.Pulse.Recursive.synth_nlist_recursive_cons p n) (LowParse.Pulse.Recursive.synth_nlist_recursive_cons_recip s n))]
= LowParse.Pulse.Recursive.synth_nlist_recursive_cons_recip_inverse #p s n


#restart-solver
#push-options "--fuel 1 --ifuel 0"
ghost fn pts_to_serialized_nlist_raw_data_item_head_header
  (a: slice byte)
  (n: pos)
  (#pm: perm)
  (#va: LowParse.Spec.VCList.nlist n raw_data_item)
requires
  pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va
ensures exists* (l: leaf) (h: header) v' .
  pts_to_serialized
    (LowParse.Spec.Combinators.serialize_nondep_then
      serialize_header
      (LowParse.Spec.Combinators.serialize_nondep_then
        (serialize_leaf_content h)
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n l)
      )
    )
    a #pm v' **
  Trade.trade
    (pts_to_serialized
      (LowParse.Spec.Combinators.serialize_nondep_then
        serialize_header
        (LowParse.Spec.Combinators.serialize_nondep_then
          (serialize_leaf_content h)
          (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n l)
        )
      )
      a #pm v'
    )
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va) **
  pure (
    h == get_raw_data_item_header (List.Tot.hd va) /\
    l == dfst (synth_raw_data_item_from_alt_recip (List.Tot.hd va)) /\
    fst v' == h /\
    fst (snd v') == (dsnd l) /\
    (fst (snd (snd v')) <: list raw_data_item) == (dsnd (synth_raw_data_item_from_alt_recip (List.Tot.hd va)) <: list raw_data_item) /\
    (snd (snd (snd v')) <: list raw_data_item) == List.Tot.tl va
  )
{
  pts_to_serialized_ext_trade
    (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param)))
    (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons serialize_raw_data_item_param n)
    a;
  pts_to_serialized_ext_trade_gen
    (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons serialize_raw_data_item_param n)
    (LowParse.Spec.Combinators.serialize_synth
        (LowParse.Spec.Combinators.parse_dtuple2 (parser_of_tot_parser parse_raw_data_item_param.parse_header) (LowParse.Pulse.Recursive.parse_nlist_recursive_cons_payload parse_raw_data_item_param n))
        (LowParse.Pulse.Recursive.synth_nlist_recursive_cons parse_raw_data_item_param n)
        (LowParse.Spec.Combinators.serialize_dtuple2 (serializer_of_tot_serializer serialize_raw_data_item_param.serialize_header) (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n))
        (LowParse.Pulse.Recursive.synth_nlist_recursive_cons_recip serialize_raw_data_item_param n)
        ()
    )
    a;
  Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
  LowParse.Pulse.Combinators.pts_to_serialized_synth_l2r_trade
    (LowParse.Spec.Combinators.serialize_dtuple2 (serializer_of_tot_serializer serialize_raw_data_item_param.serialize_header) (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n))
    (LowParse.Pulse.Recursive.synth_nlist_recursive_cons parse_raw_data_item_param n)
    (LowParse.Pulse.Recursive.synth_nlist_recursive_cons_recip serialize_raw_data_item_param n)
    a;
  Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
  with v . assert (pts_to_serialized (LowParse.Pulse.Combinators.serialize_dtuple2 (serializer_of_tot_serializer serialize_raw_data_item_param.serialize_header) (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n)) a #pm v);
  LowParse.Pulse.Combinators.pts_to_serialized_dtuple2_as_nondep_then
    (serializer_of_tot_serializer serialize_raw_data_item_param.serialize_header)
    (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n)
    a;
  Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
  LowParse.Pulse.Combinators.pts_to_serialized_ext_nondep_then_left
    (serializer_of_tot_serializer serialize_raw_data_item_param.serialize_header)
    (LowParse.Pulse.Combinators.serialize_dtuple2 serialize_header serialize_leaf_content)
    (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n (dfst v))
    a;
  Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
  LowParse.Pulse.Combinators.pts_to_serialized_dtuple2_nondep_then_assoc_l2r
    serialize_header
    serialize_leaf_content
    (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param n (dfst v))
    a;
  Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
}

open LowParse.Pulse.Combinators

inline_for_extraction
fn nondep_then_fst_tot_kind
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  requires pts_to_serialized (serialize_nondep_then s1 s2) input #pm v
  returns res: slice byte
  ensures pts_to_serialized s1 res #pm (fst v) **
    trade (pts_to_serialized s1 res #pm (fst v)) (pts_to_serialized (serialize_nondep_then s1 s2) input #pm v)
{
  nondep_then_fst s1 j1 s2 input
}
#pop-options
#restart-solver

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
inline_for_extraction
let get_raw_data_item_optimal (va:erased raw_data_item) (h:header { h == get_raw_data_item_header va })
: b:bool { b ==  R.raw_data_item_ints_optimal_elem va }
= if get_header_major_type h = cbor_major_type_simple_value then true
  else impl_raw_uint64_optimal (argument_as_raw_uint64 (get_header_initial_byte h) (get_header_long_argument h))
#pop-options

#push-options "--query_stats --fuel 1 --ifuel 1 --z3rlimit_factor 2"
fn cbor_raw_ints_optimal (_: unit) : LowParse.Pulse.Recursive.impl_pred_t u#0 u#0 #_ serialize_raw_data_item_param R.raw_data_item_ints_optimal_elem
= (a: _)
  (n: _)
  (#pm: _)
  (#va: _)
{
  pts_to_serialized_nlist_raw_data_item_head_header a (SZ.v n);
  with l gh v' . assert (
  pts_to_serialized
    (LowParse.Spec.Combinators.serialize_nondep_then
      serialize_header
      (LowParse.Spec.Combinators.serialize_nondep_then
        (serialize_leaf_content gh)
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l)
      )
    )
    a #pm v'
  );
  let input1 = nondep_then_fst_tot_kind serialize_header (jump_header ()) // FIXME: WHY WHY WHY do the kinds need to be total here?
      (LowParse.Spec.Combinators.serialize_nondep_then
        (serialize_leaf_content gh)
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l)
      )
    a;
  Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
  let h = read_header () input1;
  let res = get_raw_data_item_optimal (List.Tot.hd va) h;
  Trade.elim _ _;
  res
}
#pop-options

fn impl_deterministically_encoded_cbor_map_key_order (_: unit)
: LowParse.Pulse.VCList.impl_order_t #_ #_ #_ (serialize_raw_data_item) (deterministically_encoded_cbor_map_key_order)
= (a1: _)
  (a2: _)
  (#p1: _)
  (#p2: _)
  (#v1: _)
  (#v2: _)
{
  deterministically_encoded_cbor_map_key_order_spec (v1) (v2);
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  unfold (pts_to_serialized serialize_raw_data_item a1 #p1 (v1));
  unfold (pts_to_serialized serialize_raw_data_item a2 #p2 (v2));
  let res = CompareBytes.lex_compare_bytes a1 a2;
  fold (pts_to_serialized serialize_raw_data_item a1 #p1 (v1));
  fold (pts_to_serialized serialize_raw_data_item a2 #p2 (v2));
  FStar.Int16.lt res 0s
}

let rec sorted2
  (#t: Type)
  (order: t -> t -> bool)
  (l: list t)
: Tot bool
  (decreases l)
= match l with
  | [] -> true
  | [_] -> false
  | _ :: _ :: [] -> true
  | _ :: _ :: _ :: [] -> false
  | a :: _ :: b :: c :: q ->
    if order a b
    then sorted2 order (b :: c :: q)
    else false

let rec sorted2_correct
  (#t: Type)
  (order: t -> t -> bool)
  (n: nat)
  (l: LowParse.Spec.VCList.nlist n (t & t))
: Lemma
  (ensures (List.Tot.sorted (map_entry_order order _) l == sorted2 order (list_of_pair_list t n l)))
  (decreases l)
= match l with
  | [] -> ()
  | [_] -> ()
  | _ :: b :: q -> sorted2_correct order (n - 1) (b :: q)

inline_for_extraction
fn split_nondep_then_tot_kind
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  requires pts_to_serialized (serialize_nondep_then s1 s2) input #pm v
  returns res: (slice byte & slice byte)
  ensures split_nondep_then_post s1 s2 input pm v res
{
  split_nondep_then s1 j1 s2 input
}

module GR = Pulse.Lib.GhostReference
module Ref = Pulse.Lib.Reference

#push-options "--z3rlimit 32"

#restart-solver
#push-options "--z3rlimit_factor 4 --query_stats --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn cbor_raw_sorted (sq: squash SZ.fits_u64) : LowParse.Pulse.Recursive.impl_pred_t u#0 u#0 #_ serialize_raw_data_item_param (R.raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order)
= (a: _)
  (n: _)
  (#pm: _)
  (#va: _)
{
  pts_to_serialized_nlist_raw_data_item_head_header a (SZ.v n);
  with l gh v' . assert (
  pts_to_serialized
    (LowParse.Spec.Combinators.serialize_nondep_then
      serialize_header
      (LowParse.Spec.Combinators.serialize_nondep_then
        (serialize_leaf_content gh)
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l)
      )
    )
    a #pm v'
  );
  let input1, input2 = split_nondep_then_tot_kind serialize_header (jump_header ()) // FIXME: WHY WHY WHY do the kinds need to be total here?
      (LowParse.Spec.Combinators.serialize_nondep_then
        (serialize_leaf_content gh)
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l)
      )
    a;
  unfold (split_nondep_then_post
    serialize_header
      (LowParse.Spec.Combinators.serialize_nondep_then
        (serialize_leaf_content gh)
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l)
      )
      a pm v' (input1, input2)
  );
  unfold (split_nondep_then_post'
    serialize_header
      (LowParse.Spec.Combinators.serialize_nondep_then
        (serialize_leaf_content gh)
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l)
      )
      a pm v' input1 input2
  );
  Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
  let h = read_header () input1;
  if (get_header_major_type h = cbor_major_type_map) {
    let nbpairs = argument_as_uint64 (get_header_initial_byte h) (get_header_long_argument h);
    if (U64.lt nbpairs 2uL) {
      Trade.elim _ _;
      true
    } else {
      Trade.elim_hyp_l _ _ _;
      let input3 = nondep_then_snd
        (serialize_leaf_content gh)
        (jump_leaf_content () h)
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l)
        input2;
      Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
      with v3 . assert (pts_to_serialized (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l) input3 #pm v3);
      let l0 : Ghost.erased (list (raw_data_item & raw_data_item)) = Ghost.hide (Map?.v (List.Tot.hd va));
      assert (pure (list_of_pair_list raw_data_item (U64.v nbpairs) l0 == fst v3));
      sorted2_correct deterministically_encoded_cbor_map_key_order (U64.v nbpairs) l0;
      let n' : erased nat = SZ.v n - 1;
      let k : Ghost.erased parser_kind = Ghost.hide (LowParse.Spec.VCList.parse_nlist_kind n' parse_raw_data_item_kind);
      let p : parser k (LowParse.Spec.VCList.nlist n' raw_data_item) = coerce_eq () ( LowParse.Spec.VCList.parse_nlist n' (parser_of_tot_parser (LowParse.Spec.Recursive.parse_recursive parse_raw_data_item_param)));
      let s : serializer p = LowParse.Spec.VCList.serialize_nlist n' (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param));
      pts_to_serialized_ext_trade_gen
        (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l)
        (LowParse.Spec.Combinators.serialize_nondep_then
          (LowParse.Spec.VCList.serialize_nlist (U64.v nbpairs + U64.v nbpairs) serialize_raw_data_item)
          s
        )
        input3;
      Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
      let hd4, input4 = LowParse.Pulse.VCList.nlist_hd_tl_nondep_then_left
        serialize_raw_data_item
        ()
        (jump_raw_data_item ())
        (U64.v nbpairs + U64.v nbpairs)
        ()
        s
        input3;
      Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
      let input5 = LowParse.Pulse.VCList.nlist_tl_nondep_then_left
        serialize_raw_data_item
        ()
        (jump_raw_data_item ())
        (U64.v nbpairs + U64.v nbpairs - 1)
        ()
        s
        input4;
      Trade.trans_hyp_r _ _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
      let mut pkey = hd4;
      let pvalue = GR.alloc (snd (List.Tot.hd l0));
      let pairs : U64.t = U64.sub nbpairs 1uL;
      let mut ppairs = pairs;
      let mut ptail = input5;
      let mut pres = true;
      while (
        let res = !pres;
        let pairs = !ppairs;
        (res && (U64.gt pairs 0uL))
      ) invariant b . exists* skey vkey vvalue vpairs stail vn vtail vres .
        Ref.pts_to pkey skey **
        pts_to_serialized serialize_raw_data_item skey #pm vkey **
        GR.pts_to pvalue vvalue **
        Ref.pts_to ppairs vpairs **
        Ref.pts_to ptail stail **
        Ref.pts_to pres vres **
        pts_to_serialized (serialize_nondep_then (LowParse.Spec.VCList.serialize_nlist vn serialize_raw_data_item) s) stail #pm vtail **
        Trade.trade
          (pts_to_serialized serialize_raw_data_item skey #pm vkey ** pts_to_serialized (serialize_nondep_then (LowParse.Spec.VCList.serialize_nlist vn serialize_raw_data_item) s) stail #pm vtail)
          (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va) **
        pure (
          vn == U64.v vpairs + U64.v vpairs /\
          List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l0 == (vres && sorted2 deterministically_encoded_cbor_map_key_order (vkey :: vvalue :: fst vtail))
        ) ** pure (
          b == (vres && Cons? (fst vtail))
        )
      {
        with vn stail vtail . assert (pts_to_serialized (serialize_nondep_then (LowParse.Spec.VCList.serialize_nlist vn serialize_raw_data_item) s) stail #pm vtail);
        let tail = !ptail;
        Trade.rewrite_with_trade
          (pts_to_serialized (serialize_nondep_then (LowParse.Spec.VCList.serialize_nlist vn serialize_raw_data_item) s) stail #pm vtail)
          (pts_to_serialized (serialize_nondep_then (LowParse.Spec.VCList.serialize_nlist vn serialize_raw_data_item) s) tail #pm vtail);
        Trade.trans_hyp_r _ _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
        let key2, tail2 = LowParse.Pulse.VCList.nlist_hd_tl_nondep_then_left serialize_raw_data_item () (jump_raw_data_item ()) vn () s tail;
        with skey . assert (Pulse.Lib.Reference.pts_to pkey skey);
        let key1 = !pkey;
        rewrite each skey as key1;
        let res = impl_deterministically_encoded_cbor_map_key_order () key1 key2;
        if res {
          Trade.elim_hyp_l _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
          Trade.trans _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
          let tail' = LowParse.Pulse.VCList.nlist_tl_nondep_then_left serialize_raw_data_item () (jump_raw_data_item ()) (vn - 1) () s tail2;
          Trade.trans_hyp_r _ _ _ (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
          pkey := key2;
          GR.op_Colon_Equals pvalue (List.Tot.hd (List.Tot.tl (fst vtail)));
          let pairs = !ppairs;
          let pairs' : U64.t = U64.sub pairs 1uL;
          ppairs := pairs';
          ptail := tail';
        } else {
          Trade.elim _ (pts_to_serialized (serialize_nondep_then (LowParse.Spec.VCList.serialize_nlist vn serialize_raw_data_item) s) tail #pm vtail);
          pres := false;
        }
      };
      GR.free pvalue;
      Trade.elim _ _;
      !pres
    }
  } else {
    Trade.elim _ _;
    true
  }
}

#pop-options

#restart-solver

let cbor_validate_det_success
  (v: Seq.seq U8.t)
  (len: SZ.t)
  (v': raw_data_item)
: Lemma
  (requires (
    validator_success parse_raw_data_item 0sz v len /\
    parse parse_raw_data_item (Seq.slice v 0 (Seq.length v)) == Some (v', SZ.v len - 0) /\
    holds_on_raw_data_item R.raw_data_item_ints_optimal_elem v' /\
    holds_on_raw_data_item (R.raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order) v'
  ))
  (ensures
    cbor_validate_det_post v len
  )
= Seq.lemma_split v (SZ.v len);
  let v2 = Seq.slice v (SZ.v len) (Seq.length v) in
  parse_injective parse_raw_data_item (Seq.slice v 0 (Seq.length v)) (serialize_cbor v');
  serialize_length serialize_raw_data_item v';
  assert (Ghost.reveal v == serialize_cbor v' `Seq.append` v2)

let cbor_validate_det_fail
  (v: Seq.seq U8.t)
  (v1': raw_data_item)
  (v2': Seq.seq U8.t)
: Lemma
  (requires (
    Ghost.reveal v == serialize_cbor v1' `Seq.append` v2' /\
    (~ (R.raw_data_item_ints_optimal v1' /\ R.raw_data_item_sorted deterministically_encoded_cbor_map_key_order v1'))
  ))
  (ensures (
    cbor_validate_det_post v 0sz
  ))
= let aux
    (v1: raw_data_item)
    (v2: Seq.seq U8.t)
  : Lemma
    (requires Ghost.reveal v == serialize_cbor v1 `Seq.append` v2 /\ R.raw_data_item_ints_optimal v1 /\ R.raw_data_item_sorted deterministically_encoded_cbor_map_key_order v1)
    (ensures False)
  = serialize_cbor_inj v1 v1' v2 v2' 
  in
  Classical.forall_intro_2 (fun v1 v2 -> Classical.move_requires (aux v1) v2)

#restart-solver

fn cbor_validate_det'
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  requires pts_to input #pm v
  returns res: (res: SZ.t { cbor_validate_det_post v res })
  ensures pts_to input #pm v
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let len = cbor_validate input;
  if (len = 0sz) {
    len
  } else {
    cbor_parse_aux len v;
    Seq.lemma_split v (SZ.v len);
    let input1 = peek_trade_gen serialize_raw_data_item input 0sz len;
    with v1 . assert (pts_to_serialized serialize_raw_data_item input1 #pm v1);
    let mut check = false;
    let check1 = impl_holds_on_raw_data_item f64 R.raw_data_item_ints_optimal_elem (cbor_raw_ints_optimal ()) input1;
    if (not check1) {
      cbor_validate_det_fail v v1 (Seq.slice v (SZ.v len) (Seq.length v));
      Trade.elim _ _;
      0sz
    } else {
      let check2 = impl_holds_on_raw_data_item f64 (R.raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order) (cbor_raw_sorted f64) input1;
      Trade.elim _ _;
      if (not check2) {
        cbor_validate_det_fail v v1 (Seq.slice v (SZ.v len) (Seq.length v));
        0sz
      } else {
        let sq : squash (cbor_validate_det_post v len) = cbor_validate_det_success v len v1;
        len
      }
    }
  }
}

fn cbor_validate_det
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  requires pts_to input #pm v
  returns res: SZ.t
  ensures pts_to input #pm v ** pure (cbor_validate_det_post v res)
{
  let res = cbor_validate_det' input;
  res
}

#pop-options

fn cbor_parse
  (input: slice U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  requires (pts_to input #pm v ** pure (
      exists v1 v2 . Ghost.reveal v == serialize_cbor v1 `Seq.append` v2 /\ SZ.v len == Seq.length (serialize_cbor v1)
    ))
  returns res: cbor_raw
  ensures
    (exists* v' .
      cbor_match 1.0R res v' **
      trade (cbor_match 1.0R res v') (pts_to input #pm v) ** pure (
        SZ.v len <= Seq.length v /\
        Seq.slice v 0 (SZ.v len) == serialize_cbor v'
    ))
{
  cbor_parse_aux len v;
  let input1 = peek_trade_gen serialize_raw_data_item input 0sz len;
  let res = cbor_read input1;
  Trade.trans _ _ (pts_to input #pm v);
  res
}

#restart-solver

let cbor_jump_aux_pre
  (off: SZ.t)
  (c: raw_data_item)
  (v: Seq.seq U8.t)
: Lemma
  (requires (
    SZ.v off + Seq.length (serialize_cbor c) <= Seq.length v /\
    Seq.slice v (SZ.v off) (SZ.v off + Seq.length (serialize_cbor c)) `Seq.equal` serialize_cbor c
  ))
  (ensures (
    jumper_pre parse_raw_data_item off v
  ))
= parse_strong_prefix parse_raw_data_item (serialize_cbor c) (Seq.slice v (SZ.v off) (Seq.length v))

let cbor_jump_aux_post
  (off: SZ.t)
  (c: raw_data_item)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Lemma
  (requires (
    SZ.v off + Seq.length (serialize_cbor c) <= Seq.length v /\
    Seq.slice v (SZ.v off) (SZ.v off + Seq.length (serialize_cbor c)) `Seq.equal` serialize_cbor c /\
    jumper_pre parse_raw_data_item off v /\
    validator_success parse_raw_data_item off v res
  ))
  (ensures (
    SZ.v res == SZ.v off + Seq.length (serialize_cbor c)
  ))
= parse_strong_prefix parse_raw_data_item (serialize_cbor c) (Seq.slice v (SZ.v off) (Seq.length v))

fn cbor_jump
  (_: unit)
: cbor_jump_t
=
  (input: slice U8.t)
  (off: SZ.t)
  (c: Ghost.erased raw_data_item)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let sq: squash (SZ.fits_u64) = assume (SZ.fits_u64);
  cbor_jump_aux_pre off c v;
  let res = jump_raw_data_item () input off;
  cbor_jump_aux_post off c v res;
  res
}

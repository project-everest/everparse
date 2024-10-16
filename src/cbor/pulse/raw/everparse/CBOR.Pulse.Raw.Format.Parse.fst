module CBOR.Pulse.Raw.Format.Parse
open CBOR.Pulse.Raw.EverParse.Serialized.Base
friend CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Format
open LowParse.Spec.Base
open LowParse.Pulse.Base

module CompareBytes = CBOR.Pulse.Raw.Compare.Bytes

let parse_fail_no_serialize
  (v: Seq.seq U8.t)
: Lemma
  (requires (None? (parse parse_raw_data_item v)))
  (ensures (~ (exists v1 v2 . v == serialize_cbor v1 `Seq.append` v2)))
= 
    let prf
      (v1: _)
      (v2: _)
    : Lemma
      (requires (v == serialize_cbor v1 `Seq.append` v2))
      (ensures False)
    = parse_strong_prefix #parse_raw_data_item_kind #raw_data_item parse_raw_data_item (serialize_cbor v1) v
    in
    Classical.forall_intro_2 (fun x y -> Classical.move_requires (prf x) y)

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

```pulse
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
```

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
let coerce_impl_pred_serialize_raw_data_item
  (p: Ghost.erased (raw_data_item -> bool))
  (impl_p: LowParse.Pulse.Recursive.impl_pred_t serialize_raw_data_item p)
: LowParse.Pulse.Recursive.impl_pred_t (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param)) (holds_on_raw_data_item_pred p).base
= impl_p

inline_for_extraction
```pulse
fn impl_holds_on_raw_data_item
  (f64: squash SZ.fits_u64)
  (p: Ghost.erased (raw_data_item -> bool))
  (impl_p: LowParse.Pulse.Recursive.impl_pred_t serialize_raw_data_item p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased raw_data_item)
  requires pts_to_serialized serialize_raw_data_item input #pm v
  returns res: bool
  ensures pts_to_serialized serialize_raw_data_item input #pm v ** pure (res == holds_on_raw_data_item p v)
{
  LowParse.Pulse.Recursive.impl_pred_recursive serialize_raw_data_item_param (jump_ext (jump_raw_data_item f64) (parser_of_tot_parser (LowParse.Spec.Recursive.parse_recursive parse_raw_data_item_param))) (jump_leaf ()) (jump_recursive_step_count_leaf f64) (holds_on_raw_data_item_pred p) (coerce_impl_pred_serialize_raw_data_item p impl_p) input
}
```

module U64 = FStar.UInt64
module U8 = FStar.UInt8

#restart-solver

let impl_raw_uint64_optimal
  (x: raw_uint64)
: Pure bool
    (requires True)
    (ensures fun res -> res == raw_uint64_optimal x)
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

```pulse
fn cbor_raw_ints_optimal (_: unit) : LowParse.Pulse.Recursive.impl_pred_t #_ #_ #_ serialize_raw_data_item R.raw_data_item_ints_optimal_elem
= (a: _)
  (#pm: _)
  (#va: _)
{
  Classical.forall_intro parse_raw_data_item_eq;
  pts_to_serialized_ext_trade
    serialize_raw_data_item
    serialize_raw_data_item_aux
    a;
  LowParse.Pulse.Combinators.pts_to_serialized_synth_l2r_trade
    (LowParse.Spec.Combinators.serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item
    synth_raw_data_item_recip
    a;
  Trade.trans _ _ (pts_to_serialized serialize_raw_data_item a #pm va);
  let input1 = LowParse.Pulse.Combinators.dtuple2_dfst serialize_header (jump_header ()) serialize_content a;
  Trade.trans _ _ (pts_to_serialized serialize_raw_data_item a #pm va);
  let h = read_header () input1;
  let res = if get_header_major_type h = cbor_major_type_simple_value then true else impl_raw_uint64_optimal (argument_as_raw_uint64 (get_header_initial_byte h) (get_header_long_argument h));
  Trade.elim _ _;
  res
}
```

```pulse
fn impl_deterministically_encoded_cbor_map_key_order (_: unit)
: LowParse.Pulse.VCList.impl_order_t #_ #_ #_ (LowParse.Pulse.Combinators.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) (map_entry_order deterministically_encoded_cbor_map_key_order raw_data_item)
= (a1: _)
  (a2: _)
  (#p1: _)
  (#p2: _)
  (#v1: _)
  (#v2: _)
{
  deterministically_encoded_cbor_map_key_order_spec (fst v1) (fst v2);
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let k1 = LowParse.Pulse.Combinators.nondep_then_fst serialize_raw_data_item (jump_raw_data_item f64) serialize_raw_data_item a1;
  let k2 = LowParse.Pulse.Combinators.nondep_then_fst serialize_raw_data_item (jump_raw_data_item f64) serialize_raw_data_item a2;
  unfold (pts_to_serialized serialize_raw_data_item k1 #p1 (fst v1));
  unfold (pts_to_serialized serialize_raw_data_item k2 #p2 (fst v2));
  let res = CompareBytes.lex_compare_bytes k1 k2;
  fold (pts_to_serialized serialize_raw_data_item k1 #p1 (fst v1));
  Trade.elim (pts_to_serialized serialize_raw_data_item k1 #p1 (fst v1)) _;
  fold (pts_to_serialized serialize_raw_data_item k2 #p2 (fst v2));
  Trade.elim (pts_to_serialized serialize_raw_data_item k2 #p2 (fst v2)) _;
  FStar.Int16.lt res 0s
}
```

```pulse
fn cbor_raw_sorted (sq: squash SZ.fits_u64) : LowParse.Pulse.Recursive.impl_pred_t #_ #_ #_ serialize_raw_data_item (R.raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order)
= (a: _)
  (#pm: _)
  (#va: _)
{
  Classical.forall_intro parse_raw_data_item_eq;
  pts_to_serialized_ext_trade
    serialize_raw_data_item
    serialize_raw_data_item_aux
    a;
  LowParse.Pulse.Combinators.pts_to_serialized_synth_l2r_trade
    (LowParse.Spec.Combinators.serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item
    synth_raw_data_item_recip
    a;
  Trade.trans _ _ (pts_to_serialized serialize_raw_data_item a #pm va);
  with va' . assert (pts_to_serialized (LowParse.Spec.Combinators.serialize_dtuple2 serialize_header serialize_content) a #pm va');
  let spl = LowParse.Pulse.Combinators.split_dtuple2 serialize_header (jump_header ()) serialize_content a;
  match spl {
    SlicePair ah ap -> {
      unfold (LowParse.Pulse.Combinators.split_dtuple2_post serialize_header serialize_content a pm va' spl);
      unfold (LowParse.Pulse.Combinators.split_dtuple2_post' serialize_header serialize_content a pm va' ah ap);
      Trade.trans _ _ (pts_to_serialized serialize_raw_data_item a #pm va);
      let h = read_header () ah;
      if (get_header_major_type h = cbor_major_type_map) {
        Trade.elim_hyp_l _ _ _;
        with vp . assert (pts_to_serialized (serialize_content h) ap #pm vp);
        let n = get_header_argument_as_uint64 h;
        let k : Ghost.erased parser_kind = LowParse.Spec.Combinators.and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind;
        let p : parser k (raw_data_item & raw_data_item) = LowParse.Spec.Combinators.nondep_then parse_raw_data_item parse_raw_data_item;
        let s : serializer p = LowParse.Spec.Combinators.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item;
        pts_to_serialized_ext_trade
          (serialize_content h)
          (LowParse.Spec.VCList.serialize_nlist (SZ.v (SZ.uint64_to_sizet n)) s)
          ap;
        Trade.trans _ _ (pts_to_serialized serialize_raw_data_item a #pm va);
        let res = LowParse.Pulse.VCList.nlist_sorted s () (LowParse.Pulse.Combinators.jump_nondep_then (jump_raw_data_item sq) (jump_raw_data_item sq)) (map_entry_order deterministically_encoded_cbor_map_key_order raw_data_item) (impl_deterministically_encoded_cbor_map_key_order ()) (SZ.uint64_to_sizet n) ap;
        Trade.elim _ _;
        res
      } else {
        Trade.elim _ _;
        true
      }
    }
  }
}
```

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

```pulse
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
```

```pulse
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
```

#pop-options

```pulse
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
```

module CBOR.Pulse.Raw.Parse
open CBOR.Pulse.Raw.Serialized.Base
friend CBOR.Spec.Raw.Order
open CBOR.Spec.Raw.Format
open CBOR.Pulse.Raw.Format
open LowParse.Spec.Base
open LowParse.Pulse.Base

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
      tot_serialize_strong_prefix serialize_raw_data_item v1 v' v2 (Seq.slice v consumed (Seq.length v))
    in
    Classical.forall_intro_2 (fun v1 v2 -> Classical.move_requires (prf v1) v2);
    ()

module Trade = Pulse.Lib.Trade.Util

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
  let res = CBOR.Pulse.Raw.Serialized.Base.cbor_read input1;
  Trade.trans _ _ (pts_to input #pm v);
  res
}
```

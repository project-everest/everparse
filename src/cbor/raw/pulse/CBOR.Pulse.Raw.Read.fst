module CBOR.Pulse.Raw.Read
include CBOR.Pulse.Raw.Match
open CBOR.Pulse.Raw.Serialized
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Trade = Pulse.Lib.Trade.Util

```pulse
ghost
fn cbor_match_tagged_elim
  (c: cbor_tagged)
  (p: perm)
  (r: raw_data_item { Tagged? r })
  requires
    cbor_match_tagged c p r cbor_match
  ensures exists* c' . R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
    cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r) **
    trade
      (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
        cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r))
      (cbor_match_tagged c p r cbor_match)
{
  unfold (cbor_match_tagged c p r cbor_match);
  with c' . assert (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
    cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r));
  ghost fn aux (_: unit)
    requires emp ** (R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_ref_perm) c' **
      cbor_match (p `perm_mul` c.cbor_tagged_payload_perm) c' (Tagged?.v r))
    ensures cbor_match_tagged c p r cbor_match
  {
    fold (cbor_match_tagged c p r cbor_match)
  };
  intro_trade _ _ _ aux
}
```

let cbor_match_eq_tagged
  (pm: perm)
  (ct: cbor_tagged)
  (r: raw_data_item)
: Lemma
  (requires (Tagged? r))
  (ensures 
    (cbor_match pm (CBOR_Case_Tagged ct) r ==
    cbor_match_tagged ct pm r cbor_match
  ))
=
  let Tagged tag v = r in
  assert_norm (
    cbor_match pm (CBOR_Case_Tagged ct) (Tagged tag v) ==
      cbor_match_tagged ct pm (Tagged tag v) cbor_match
  )

```pulse
fn cbor_match_tagged_get_payload
  (c: cbor_raw)
  (#pm: perm)
  (#r: Ghost.erased raw_data_item { Tagged? r })
  requires cbor_match pm c r
  returns res: cbor_raw
  ensures exists* pm' .
    cbor_match pm' res (Tagged?.v r) **
    trade
      (cbor_match pm' res (Tagged?.v r))
      (cbor_match pm c r)
{
  cbor_match_cases c;
  if (CBOR_Case_Serialized_Tagged? c) {
    let cs = CBOR_Case_Serialized_Tagged?.v c;
    Trade.rewrite_with_trade
      (cbor_match pm c r)
      (cbor_match_serialized_tagged cs pm r);
    let res = cbor_match_serialized_tagged_get_payload cs;
    Trade.trans _ _ (cbor_match pm c r);
    res
  } else {
    let ct = CBOR_Case_Tagged?.v c;
    cbor_match_eq_tagged pm ct r;
    Trade.rewrite_with_trade
      (cbor_match pm c r)
      (cbor_match_tagged ct pm r cbor_match);
    cbor_match_tagged_elim ct pm r;
    Trade.trans _ _ (cbor_match pm c r);
    let res = !ct.cbor_tagged_ptr;
    Trade.elim_hyp_l _ _ (cbor_match pm c r);
    res
  }
}
```

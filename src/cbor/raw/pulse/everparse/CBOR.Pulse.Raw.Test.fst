module CBOR.Pulse.Raw.Test
open LowParse.Spec.Base
open CBOR.Spec.Raw.Format
open CBOR.Pulse.Raw.Format
open LowParse.Pulse.Util
open LowParse.Pulse.Base
open Pulse.Lib.Slice
module SZ = FStar.SizeT

```pulse
fn test (#pm: perm) (#v: Ghost.erased bytes) (s: slice byte)
  requires pts_to s #pm v ** pure (exists off . validator_success test_parse 0sz v off)
  returns _: SZ.t
  ensures pts_to s #pm v
{
//  validate_nonempty (validate_and_read_elim validate_header) s 0sz
//  validate_nonempty (validate_and_read_elim validate_initial_byte) s 0sz
  test_jump s 0sz
}
```

type c_initial_byte = {
  major_type: major_type_t;
  additional_info: additional_info_t;
  prf: squash (initial_byte_wf (major_type, (additional_info, ())));
}

inline_for_extraction
noextract
let synth_c_initial_byte
  (x: initial_byte)
: Tot c_initial_byte
= match x with
  (major_type, (additional_info, _)) -> {
    major_type = major_type;
    additional_info = additional_info;
    prf = ();
  }

let _ : squash (LowParse.Spec.Combinators.synth_injective synth_c_initial_byte) = ()

inline_for_extraction
noextract
let synth_c_initial_byte_recip
  (x: c_initial_byte)
: Tot initial_byte
= (x.major_type, (x.additional_info, ()))

let _ : squash (LowParse.Spec.Combinators.synth_inverse synth_c_initial_byte synth_c_initial_byte_recip) = ()

```pulse
fn test2 (#pm: perm) (#v: Ghost.erased initial_byte) (s: slice byte)
  requires pts_to_serialized serialize_initial_byte s  #pm v
  returns _: major_type_t
  ensures pts_to_serialized serialize_initial_byte s #pm v
{
  LowParse.Pulse.Combinators.pts_to_serialized_synth_stick serialize_initial_byte synth_c_initial_byte synth_c_initial_byte_recip s;
  let x = pure_read (LowParse.Pulse.Combinators.pure_read_synth' pure_read_initial_byte synth_c_initial_byte synth_c_initial_byte_recip) s;
  elim_stick _ _;
  x.major_type
}
```

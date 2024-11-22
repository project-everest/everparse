module CBORTest
open CBOR.Spec.Constants
open CBOR.Pulse.API.Det.C
module C = C
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array

```pulse
fn main (_: unit)
requires emp
returns res: C.exit_code
ensures pure (res == C.EXIT_SUCCESS)
{
  let dummy_cbor = cbor_det_mk_int64 () cbor_major_type_uint64 18uL;
  drop_ (cbor_det_match _ dummy_cbor _);
  C.EXIT_SUCCESS
}
```

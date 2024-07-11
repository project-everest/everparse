module CBOR.Pulse.Raw.Test
open LowParse.Spec.Base
open CBOR.Pulse.Raw.Format
open LowParse.Pulse.Util
open LowParse.Pulse.Base
open Pulse.Lib.Slice
module SZ = FStar.SizeT

```pulse
fn test (#pm: perm) (#v: Ghost.erased bytes) (s: slice byte)
  requires pts_to s #pm v
  returns _: SZ.t
  ensures pts_to s #pm v
{
//  validate_nonempty (validate_and_read_elim validate_header) s 0sz
  validate_nonempty (validate_and_read_elim validate_initial_byte) s 0sz
}
```

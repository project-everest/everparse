module CBOR.Pulse.API.UTF8

include CBOR.Spec.API.UTF8
open Pulse.Lib.Pervasives
let impl_utf8_correct = CBOR.Pulse.Raw.EverParse.UTF8.impl_correct

module AnonUnion.OutputTypes

open FStar.HyperStack.ST
open Prelude
open Actions
module B = LowStar.Buffer
noextract
val output_loc:eloc


val p__OPOINT:Type0


val set_OPOINT_deref_z (_: p__OPOINT) (_: (___UINT32)) (_: unit)
    : Stack unit (fun _ -> True) (fun h0 _ h1 -> B.modifies output_loc h0 h1)


val set_OPOINT_deref_y (_: p__OPOINT) (_: (___UINT8)) (_: unit)
    : Stack unit (fun _ -> True) (fun h0 _ h1 -> B.modifies output_loc h0 h1)


val set_OPOINT_deref_x (_: p__OPOINT) (_: (___UINT8)) (_: unit)
    : Stack unit (fun _ -> True) (fun h0 _ h1 -> B.modifies output_loc h0 h1)


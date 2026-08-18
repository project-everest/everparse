module CBOR.Spec.Raw.Format.MapPair
open CBOR.Spec.Util
open CBOR.Spec.API.Type

val map_pair_order: (cbor_map & cbor_map) -> (cbor_map & cbor_map) -> bool

val map_pair_order_irrefl: squash (order_irrefl map_pair_order)

val map_pair_order_trans: squash (order_trans map_pair_order)

val map_pair_order_total: squash (forall x1 x2 . (x1 == x2 \/ map_pair_order x1 x2 \/ map_pair_order x2 x1))

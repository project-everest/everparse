module CBOR.Spec.API.MapPairSet
module S = CBOR.Spec.Raw.Set

let f : S.order elt = CBOR.Spec.Raw.Format.MapPair.map_pair_order

let t = S.t f

let cardinality = S.cardinality

let mem = S.mem

let ext = S.ext

let empty = S.empty _

let mem_empty = S.mem_empty f

let cardinality_empty = S.cardinality_empty f

let singleton = S.singleton _

let mem_singleton = S.mem_singleton f

let cardinality_singleton = S.cardinality_singleton f

let union = S.union

let mem_union = S.mem_union

let cardinality_union = S.cardinality_union

let filter = S.filter

let mem_filter = S.mem_filter

let as_list = S.as_list

let no_repeats_as_list = S.no_repeats_as_list

let mem_as_list = S.mem_as_list

let length_as_list = S.length_as_list

let fold phi = S.fold phi

let fold_ext phi = S.fold_ext phi

let fold_eq phi = S.fold_eq phi

let fold_eq_idem phi = S.fold_eq_idem phi



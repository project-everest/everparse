module CDDL.Pulse.Iterator.Array
include CDDL.Pulse.Iterator.Base
include CDDL.Pulse.Parse.Base
open Pulse.Lib.Pervasives

module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.Base
module SM = Pulse.Lib.SeqMatch

noeq
type array_iterator_t (#cbor: Type0) (vmatch: perm -> cbor -> Cbor.cbor -> slprop) (cbor_array_iterator_t: Type0) (impl_elt: Type0) (spec: Ghost.erased (src_elt: Type0 & rel impl_elt src_elt)) : Type0 = {
  contents: cbor_array_iterator_t;
  pm: perm;
  ty: Ghost.erased Spec.typ;
  ser: Ghost.erased (dfst spec -> bool);
  ps: Ghost.erased (Spec.parser_spec ty (dfst spec) ser);
  impl_parse: impl_zero_copy_parse vmatch ps (dsnd spec);
}

let rel_array_iterator
  (#cbor: Type0) (vmatch: perm -> cbor -> Cbor.cbor -> slprop) (#cbor_array_iterator_t: Type0) (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list Cbor.cbor -> slprop) (#impl_elt: Type0) (#src_elt: Type0) (r: rel impl_elt src_elt) :
    rel (array_iterator_t vmatch cbor_array_iterator_t impl_elt (mk_spec r)) (list src_elt)
= mk_rel (fun i s -> exists* l . cbor_array_iterator_match i.pm i.contents l **
    pure (
      List.Tot.map (apply_parser i.ps) l == List.Tot.map Some s
    )
  )

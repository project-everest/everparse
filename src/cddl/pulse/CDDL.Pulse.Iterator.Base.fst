module CDDL.Pulse.Iterator.Base
include CDDL.Pulse.Types
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.Base

let type_spec (impl_elt: Type0) = dtuple2 Type0 (rel impl_elt)

let mk_spec
  (#impl_elt: Type0)
  (#src_elt: Type0)
  (r: rel impl_elt src_elt)
: Tot (Ghost.erased (type_spec impl_elt))
= Ghost.hide (| _, r |)

let apply_parser
  (#spec: Type0)
  (#ty: Spec.typ)
  (#ser: spec -> bool)
  (ps: Spec.parser_spec ty spec ser)
  (x: Cbor.cbor)
: Tot (option spec)
= if ty x
  then Some (ps x)
  else None

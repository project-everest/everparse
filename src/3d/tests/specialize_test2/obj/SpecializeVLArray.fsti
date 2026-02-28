module SpecializeVLArray
open EverParse3d.Prelude
open EverParse3d.Actions.All
open EverParse3d.Interpreter
open SpecializeVLArray.ExternalAPI
module T = FStar.Tactics
module A = EverParse3d.Actions.All
module P = EverParse3d.Prelude
#set-options "--fuel 0 --ifuel 0 --ext optimize_let_vc"

[@@ noextract_to "krml"]
inline_for_extraction noextract
val kind__UNKNOWN_HEADERS:P.parser_kind true P.WeakKindStrongPrefix

[@@ noextract_to "krml"]
noextract
val def'__UNKNOWN_HEADERS
      (___Requestor32: (___Bool))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
    : typ kind__UNKNOWN_HEADERS
      (NonTrivial
        (A.conj_inv (A.copy_buffer_inv ___UnknownHeaderProbe)
            (A.copy_buffer_inv ___UnknownHeaderProbe)))
      Trivial
      (NonTrivial
        (A.eloc_union (A.copy_buffer_loc ___UnknownHeaderProbe)
            (A.copy_buffer_loc ___UnknownHeaderProbe)))
      true
      false

val validate__UNKNOWN_HEADERS
      (___Requestor32: (___Bool))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
    : validator_of (def'__UNKNOWN_HEADERS ___Requestor32 ___UnknownHeaderCount ___UnknownHeaderProbe
      )

[@@ specialize; noextract_to "krml"]
noextract
val dtyp__UNKNOWN_HEADERS
      (___Requestor32: (___Bool))
      (___UnknownHeaderCount: (___UINT16))
      (___UnknownHeaderProbe: (___EVERPARSE_COPY_BUFFER_T))
    : dtyp_of (def'__UNKNOWN_HEADERS ___Requestor32 ___UnknownHeaderCount ___UnknownHeaderProbe)


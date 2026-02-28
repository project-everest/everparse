module SpecializeTaggedUnionArray
open EverParse3d.Prelude
open EverParse3d.Actions.All
open EverParse3d.Interpreter
open SpecializeTaggedUnionArray.ExternalAPI
module T = FStar.Tactics
module A = EverParse3d.Actions.All
module P = EverParse3d.Prelude
#set-options "--fuel 0 --ifuel 0 --ext optimize_let_vc"

[@@ noextract_to "krml"]
inline_for_extraction noextract
val kind__MAIN:P.parser_kind true P.WeakKindStrongPrefix

[@@ noextract_to "krml"]
noextract
val def'__MAIN
      (___Requestor32: (___Bool))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
    : typ kind__MAIN
      (NonTrivial (A.conj_inv (A.copy_buffer_inv ___Out) (A.copy_buffer_inv ___Out)))
      Trivial
      (NonTrivial (A.eloc_union (A.copy_buffer_loc ___Out) (A.copy_buffer_loc ___Out)))
      true
      false

val validate__MAIN
      (___Requestor32: (___Bool))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
    : validator_of (def'__MAIN ___Requestor32 ___Count ___Out)

[@@ specialize; noextract_to "krml"]
noextract
val dtyp__MAIN
      (___Requestor32: (___Bool))
      (___Count: (___UINT16))
      (___Out: (___EVERPARSE_COPY_BUFFER_T))
    : dtyp_of (def'__MAIN ___Requestor32 ___Count ___Out)


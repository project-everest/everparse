module EverParse3d.InputBuffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LPL = LowParse.Low.Base
module R = EverParse3d.Readable
module G = FStar.Ghost
module Aux = EverParse3d.InputBuffer.Aux

open LowParse.Low.Base

let input_buffer_t = Aux.input_buffer

let slice_of #len x =
  { LPL.base = dfst x; LPL.len = len }

let perm_of x = dsnd x

let truncate_input_buffer #len0 x len =
  match x with
  | (| base, perm |) -> (| base, perm |)

let drop sl from to =
  match sl with
  | (| base, perm |) ->
    R.drop perm from to

(* TODO: remove the slice here *)
let read_with_perm #k #t #p r j #len sl pos =
  match sl with
  | (| base, _ |) ->
  [@inline_let] let sl' : LPL.slice triv triv = { LPL.base = base; LPL.len = len } in
  let pos' = j sl' pos in
  drop sl pos pos' ;
  r sl' pos

let puint8 = B.buffer LPL.byte

let offset sl off =
  match sl with
  | (| base, _ |) ->
  B.moffset triv base off

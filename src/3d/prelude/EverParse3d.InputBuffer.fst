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

let slice_of #len x = { LPL.base = x.Aux.base; LPL.len = len }

let perm_of x = x.Aux.perm

let truncate_input_buffer #len0 x len =
  { Aux.base = x.Aux.base; Aux.perm = x.Aux.perm; }

let drop sl from to =
  R.drop sl.Aux.perm from to

(* TODO: remove the slice here *)
let read_with_perm #k #t #p r j #len sl pos =
  [@inline_let] let sl' : LPL.slice triv triv = { LPL.base = sl.Aux.base; LPL.len = len } in
  let pos' = j sl' pos in
  drop sl pos pos' ;
  r sl' pos

let puint8 = B.buffer LPL.byte

let offset sl off =
  B.moffset triv sl.Aux.base off

module EverParse3d.InputBuffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LPL = LowParse.Low.Base
module R = EverParse3d.Readable
module G = FStar.Ghost

open LowParse.Low.Base

noeq
inline_for_extraction
type input_buffer_t' = {
  slice: LPL.slice triv triv;
  perm: R.perm slice.LPL.base;
}

let input_buffer_t = input_buffer_t'

let slice_of x = x.slice

let slice_length x = x.slice.LPL.len

let perm_of x = x.perm

let truncate_input_buffer x len = {
  slice = { base = x.slice.LPL.base; len = len; };
  perm = x.perm;
}

let scrub sl from to =
  R.scrub sl.perm from to

let read_with_perm #k #t #p r j sl pos =
  let pos' = j sl.slice pos in
  scrub sl pos pos' ;
  r sl.slice pos

let puint8 = B.buffer LPL.byte

let offset sl off =
  B.moffset triv sl.slice.base off

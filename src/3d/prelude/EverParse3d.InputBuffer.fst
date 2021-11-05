module EverParse3d.InputBuffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LPL = LowParse.Low.Base
module R = EverParse3d.Readable
module G = FStar.Ghost

open LowParse.Low.Base

inline_for_extraction
noextract
let base_t (len: U32.t)
= (base: B.buffer LPL.byte { U32.v len <= B.length base })

inline_for_extraction
noextract
noeq
type input_buffer_perm (len: U32.t) = 
{
  p_base: Ghost.erased (base_t len);
  p_perm: R.perm p_base;
}

let input_buffer_t len =
  (p: (base_t len & input_buffer_perm len) { Ghost.reveal (snd p).p_base == fst p })

let slice_of #len x =
  { LPL.base = fst x; LPL.len = len }

let perm_of x = (snd x).p_perm

let truncate_input_buffer #len0 x len =
  match x with
  | (base, perm) ->
    [@inline_let]
    let base' : base_t len = base in
    [@inline_let]
    let perm' : R.perm base' = perm.p_perm in
    (base, ({ p_base = base'; p_perm = perm' }))

let drop sl from to =
  match sl with
  | (base, perm) ->
    R.drop (perm.p_perm <: R.perm base) from to

(* TODO: remove the slice here *)
let read_with_perm #k #t #p r j #len sl pos =
  match sl with
  | (base, _) ->
  [@inline_let] let sl' : LPL.slice triv triv = { LPL.base = base; LPL.len = len } in
  let pos' = j sl' pos in
  drop sl pos pos' ;
  r sl' pos

let puint8 = B.buffer LPL.byte

let offset sl off =
  match sl with
  | (base, _) ->
  B.moffset triv base off

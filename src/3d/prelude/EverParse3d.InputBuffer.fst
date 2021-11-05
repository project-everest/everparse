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

let drop sl from to =
  match sl with
  | (base, perm) ->
    R.drop (perm.p_perm <: R.perm base) from to

(* TODO: remove the slice here *)
let read_with_perm #k #t #p r #len sl pos =
  match sl with
  | (base, _) ->
  [@inline_let] let sl' : LPL.slice triv triv = { LPL.base = base; LPL.len = len } in
  let h0 = HST.get () in
  let pos' = Ghost.hide (LPL.get_valid_pos p h0 sl' pos) in
  let res = r sl' pos in
  let h1 = HST.get () in
  R.valid_perm_frame h0 (perm_of sl) B.loc_none h1;
  R.preserved_split (perm_of sl) 0ul pos (B.len base) h0 h1;
  R.preserved_split (perm_of sl) pos pos' (B.len base) h0 h1;
  drop sl pos pos' ;
  let h2 = HST.get () in
  R.preserved_trans (perm_of sl) 0ul pos h0 h1 h2;
  R.preserved_trans (perm_of sl) pos' (B.len base) h0 h1 h2;
  res

let puint8 = B.buffer LPL.byte

let offset sl off =
  match sl with
  | (base, _) ->
  B.moffset triv base off

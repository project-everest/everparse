module EverParse3d.InputBuffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LPL = LowParse.Low.Base
module R = EverParse3d.Readable
module G = FStar.Ghost

open LowParse.Low.Base

let input_buffer_t len =
  (base: B.buffer LPL.byte { U32.v len <= B.length base })

let slice_of #len x =
  { LPL.base = x; LPL.len = len }

let drop #len base from to perm_of =
    R.drop #byte #base perm_of from to

(* TODO: remove the slice here *)
let read_with_perm #k #t #p r #len base pos n perm_of =
  let h0 = HST.get () in
  LPL.valid_facts p h0 (slice_of base) pos;
  LPL.parser_kind_prop_equiv k p;
  [@inline_let] let sl' : LPL.slice triv triv = { LPL.base = base; LPL.len = pos `U32.add` n } in
  LPL.parse_strong_prefix p (LPL.bytes_of_slice_from h0 (slice_of base) pos) (LPL.bytes_of_slice_from h0 sl' pos);
  LPL.valid_facts p h0 sl' pos;
  let pos' = Ghost.hide (LPL.get_valid_pos p h0 sl' pos) in
  let res = r sl' pos in
  let h1 = HST.get () in
  R.valid_perm_frame h0 perm_of B.loc_none h1;
  R.preserved_split perm_of 0ul pos (B.len base) h0 h1;
  R.preserved_split perm_of pos pos' (B.len base) h0 h1;
  drop base pos pos' perm_of ;
  let h2 = HST.get () in
  R.preserved_trans perm_of 0ul pos h0 h1 h2;
  R.preserved_trans perm_of pos' (B.len base) h0 h1 h2;
  res

let puint8 = B.buffer LPL.byte

let offset base off perm_of =
  B.moffset triv base off

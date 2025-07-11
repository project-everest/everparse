module EverParse3d.AppCtxt
module B = LowStar.Buffer
module HS = FStar.HyperStack
module U64 = FStar.UInt64
module U8 = FStar.UInt8
open LowStar.Buffer
open FStar.HyperStack.ST
val region : HS.rid
let app_ctxt = x:B.pointer U8.t { B.frameOf x == region }
let loc_of (x:app_ctxt) : GTot B.loc = B.loc_buffer x
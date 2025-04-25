module EverParse3d.AppCtxt
module B = LowStar.Buffer
module HS = FStar.HyperStack
module U64 = FStar.UInt64
module U8 = FStar.UInt8
open LowStar.Buffer
open FStar.HyperStack.ST
val region : HS.rid
let app_ctxt = x:B.pointer U8.t { B.frameOf x == region }
// val action_ghost_ptr (x:app_ctxt) : GTot (y:B.pointer U8.t {
//   loc_disjoint (B.loc_buffer x) (B.loc_buffer y) /\
//   B.frameOf y == region
// })
let loc_of (x:app_ctxt) : GTot B.loc = B.loc_buffer x
// let ghost_loc_of (x:app_ctxt) : GTot B.loc = B.loc_buffer (action_ghost_ptr x)
let properties (x:app_ctxt)
  : Lemma (
      B.loc_region_only true region `loc_includes` loc_of x /\
      // B.loc_region_only true region `loc_includes` ghost_loc_of x /\
      B.address_liveness_insensitive_locs `B.loc_includes` loc_of x 
      // /\
      // B.address_liveness_insensitive_locs `B.loc_includes` ghost_loc_of x /\
      // loc_disjoint (loc_of x) (ghost_loc_of x)
    )
  = ()

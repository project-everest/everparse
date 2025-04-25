module EverParse3d.Actions.Common
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps
module B = LowStar.Buffer
module I = EverParse3d.InputStream.Base
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module AppCtxt = EverParse3d.AppCtxt
module LPE = EverParse3d.ErrorCode
open FStar.FunctionalExtensionality
module B = LowStar.Buffer
module U8 = FStar.UInt8
module F = FStar.FunctionalExtensionality
module U64 = FStar.UInt64
let eloc = (l: FStar.Ghost.erased B.loc { B.address_liveness_insensitive_locs `B.loc_includes` l })
let eloc_none : eloc = B.loc_none
  
let app_ctxt = AppCtxt.app_ctxt

let app_loc (x:AppCtxt.app_ctxt) (l:eloc) : eloc = 

  AppCtxt.loc_of x `loc_union` l

inline_for_extraction
noextract
let input_buffer_t = EverParse3d.InputStream.All.t

let app_ctxt_error_pre (ctxt:app_ctxt) (l:loc) (h:HS.mem) =
  B.live h ctxt /\
  AppCtxt.loc_of ctxt `loc_disjoint` l

inline_for_extraction
let error_handler = 
    typename:string ->
    fieldname:string ->
    error_reason:string ->
    error_code:U64.t ->
    ctxt: app_ctxt ->
    sl: input_buffer_t ->
    pos: LPE.pos_t ->
    Stack unit
      (requires fun h ->
        I.live sl h /\
        app_ctxt_error_pre ctxt (I.footprint sl) h /\
        U64.v pos <= Seq.length (I.get_read sl h)
      )
      (ensures fun h0 _ h1 ->
        let sl = Ghost.reveal sl in
        modifies (app_loc ctxt eloc_none) h0 h1 /\
        B.live h1 ctxt)

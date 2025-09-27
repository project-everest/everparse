module EverParse3d.ProbeActions
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.All
module B = LowStar.Buffer
module HS = FStar.HyperStack
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open EverParse3d.CopyBuffer
open LowStar.Buffer
open LowStar.BufferOps
open FStar.HyperStack.ST
open EverParse3d.Actions.Common


inline_for_extraction
noextract
val probe_fn_incremental : Type0

inline_for_extraction
noextract
val init_probe_dest_t : Type0

inline_for_extraction
val write_at_offset_t (t:Type0) (n:U64.t) : Type0

inline_for_extraction
noextract
val probe_and_read_at_offset_t (t:Type0) (size_t:U64.t) : Type0

inline_for_extraction
let probe_and_read_at_offset_uint8 = probe_and_read_at_offset_t U8.t 1uL
inline_for_extraction
let probe_and_read_at_offset_uint16 = probe_and_read_at_offset_t U16.t 2uL
inline_for_extraction
let probe_and_read_at_offset_uint32 = probe_and_read_at_offset_t U32.t 4uL
inline_for_extraction
let probe_and_read_at_offset_uint64 = probe_and_read_at_offset_t U64.t 8uL
inline_for_extraction
let write_at_offset_uint8 = write_at_offset_t U8.t 1uL
inline_for_extraction
let write_at_offset_uint16 = write_at_offset_t U16.t 2uL
inline_for_extraction
let write_at_offset_uint32 = write_at_offset_t U32.t 4uL
inline_for_extraction
let write_at_offset_uint64 = write_at_offset_t U64.t 8uL

inline_for_extraction
val probe_m (a:Type0) (requires_unread_dest:bool) (expect_zero_offsets:bool) : Type0

inline_for_extraction
noextract
val probe_fn_incremental_as_probe_m (f:probe_fn_incremental) (bytes_to_read:U64.t)
: probe_m unit true false

inline_for_extraction
noextract
val init_probe_m (probe_struct_name:string) (f:init_probe_dest_t)
: probe_m unit false false

inline_for_extraction
noextract
val init_probe_size
: probe_m U64.t true false

inline_for_extraction
noextract
val write_at_offset_m (#t:Type0) (#w:U64.t { w <> 0uL }) (f:write_at_offset_t t w) (v:t)
: probe_m unit true false

inline_for_extraction
noextract
val probe_and_read_at_offset_m (#t:Type0) (#s:U64.t { s <> 0uL }) (reader:probe_and_read_at_offset_t t s)
: probe_m t true false

inline_for_extraction
noextract
val seq_probe_m (#a:Type) (detail:string) (dflt:a) (m1:probe_m unit true false) (m2:probe_m a true false)
: probe_m a true false

inline_for_extraction
noextract
val bind_probe_m (#a #b:Type) (detail:string) (dflt:b) (m1:probe_m a true false) (m2:a -> probe_m b true false)
: probe_m b true false

inline_for_extraction
noextract
val probe_and_copy_init_sz (f:probe_fn_incremental)
: probe_m unit true false

inline_for_extraction
noextract
val return_probe_m (#a:Type) (v:a)
: probe_m a true false

inline_for_extraction
noextract
val skip_read (bytes_to_skip:U64.t)
: probe_m unit true false

inline_for_extraction
noextract
val skip_write (bytes_to_skip:U64.t)
: probe_m unit true false


inline_for_extraction
noextract
val fail
: probe_m unit true false

inline_for_extraction
noextract
val if_then_else (b:bool) (m0 m1:probe_m unit true false)
: probe_m unit true false

inline_for_extraction
noextract
val probe_array (byte_len:U64.t) (probe_elem:probe_m unit true false)
: probe_m unit true false

inline_for_extraction
noextract
let pure_external_action t =
  unit -> Stack t (fun _ -> True) (fun h0 _ h1 -> h0==h1)

inline_for_extraction
noextract
val lift_pure_external_action (#a:Type) (f:pure_external_action a)
: probe_m a true false

inline_for_extraction
noextract
val init_and_probe 
      (#mz:bool)
      (struct_name:string)
      (init:init_probe_dest_t)
      (probe:probe_m unit true mz)
: probe_m unit false mz

inline_for_extraction
noextract
val run_probe_m (#any:bool) 
  (m:probe_m unit false any)
  (tn fn det:string)
  (ctxt:app_ctxt)
  (err:error_handler)
  (src:U64.t)
  (sz:U64.t)
  (dest:copy_buffer_t)
: Stack U64.t
    (fun h0 ->
      let sl = stream_of dest in
      app_ctxt_error_pre ctxt (I.footprint sl) h0 /\
      I.live sl h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      I.live sl h1 /\
      B.live h1 ctxt /\
      modifies (app_loc ctxt (I.footprint sl)) h0 h1 /\
      (b <> 0uL ==> Seq.length (I.get_read sl h1) == 0))

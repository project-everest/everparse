module EverParse3d.ProbeActions
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open EverParse3d.CopyBuffer
module CB = EverParse3d.CopyBuffer
open Pulse.Lib.Pervasives
open EverParse3d.Actions.Common


inline_for_extraction
noextract
val probe_fn_incremental
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
: Type0

inline_for_extraction
noextract
val init_probe_dest_t
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
: Type0

inline_for_extraction
val write_at_offset_t
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (t:Type0) (n:U64.t) : Type0

inline_for_extraction
noextract
val probe_and_read_at_offset_t
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
(t:Type0) (size_t:U64.t) : Type0

inline_for_extraction
let probe_and_read_at_offset_uint8
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
= probe_and_read_at_offset_t #copy_buffer_t #base_t #len_t #pos_t U8.t 1uL
inline_for_extraction
let probe_and_read_at_offset_uint16
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
= probe_and_read_at_offset_t #copy_buffer_t #base_t #len_t #pos_t U16.t 2uL
inline_for_extraction
let probe_and_read_at_offset_uint32
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
= probe_and_read_at_offset_t #copy_buffer_t #base_t #len_t #pos_t U32.t 4uL
inline_for_extraction
let probe_and_read_at_offset_uint64
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
= probe_and_read_at_offset_t #copy_buffer_t #base_t #len_t #pos_t U64.t 8uL
inline_for_extraction
let write_at_offset_uint8
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
= write_at_offset_t #copy_buffer_t #base_t #len_t #pos_t U8.t 1uL
inline_for_extraction
let write_at_offset_uint16
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
= write_at_offset_t #copy_buffer_t #base_t #len_t #pos_t U16.t 2uL
inline_for_extraction
let write_at_offset_uint32
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
= write_at_offset_t #copy_buffer_t #base_t #len_t #pos_t U32.t 4uL
inline_for_extraction
let write_at_offset_uint64
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
= write_at_offset_t #copy_buffer_t #base_t #len_t #pos_t U64.t 8uL

inline_for_extraction
val probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (a:Type0) (requires_unread_dest:bool) (expect_zero_offsets:bool) (use_error_handler:bool) : Type0

inline_for_extraction
noextract
val probe_fn_incremental_as_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
(#use_error_handler:bool) (f:probe_fn_incremental #copy_buffer_t #base_t #len_t #pos_t) (bytes_to_read:U64.t)
: probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler

inline_for_extraction
noextract
val init_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
(#use_error_handler:bool) (probe_struct_name:string) (f:init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t)
: probe_m #_ #_ #_ #_ #inst #cbinst unit false false use_error_handler

inline_for_extraction
noextract
val init_probe_size
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool)
: probe_m #_ #_ #_ #_ #inst #cbinst U64.t true false use_error_handler

inline_for_extraction
noextract
val write_at_offset_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (#t:Type0) (#w:U64.t { w <> 0uL }) (f:write_at_offset_t #copy_buffer_t #base_t #len_t #pos_t t w) (v:t)
: probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler

inline_for_extraction
noextract
val probe_and_read_at_offset_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (#t:Type0) (#s:U64.t { s <> 0uL }) (reader:probe_and_read_at_offset_t #copy_buffer_t #base_t #len_t #pos_t t s)
: probe_m #_ #_ #_ #_ #inst #cbinst t true false use_error_handler

inline_for_extraction
noextract
val seq_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (#a:Type) (detail:string) (dflt:a) (m1:probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler) (m2:probe_m #_ #_ #_ #_ #inst #cbinst a true false use_error_handler)
: probe_m #_ #_ #_ #_ #inst #cbinst a true false use_error_handler

inline_for_extraction
noextract
val bind_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (#a #b:Type) (detail:string) (dflt:b) (m1:probe_m #_ #_ #_ #_ #inst #cbinst a true false use_error_handler) (m2:a -> probe_m #_ #_ #_ #_ #inst #cbinst b true false use_error_handler)
: probe_m #_ #_ #_ #_ #inst #cbinst b true false use_error_handler

inline_for_extraction
noextract
val probe_and_copy_init_sz
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (f:probe_fn_incremental #copy_buffer_t #base_t #len_t #pos_t)
: probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler

inline_for_extraction
noextract
val return_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (#a:Type) (v:a)
: probe_m #_ #_ #_ #_ #inst #cbinst a true false use_error_handler

inline_for_extraction
noextract
val skip_read
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (bytes_to_skip:U64.t)
: probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler

inline_for_extraction
noextract
val skip_write
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (bytes_to_skip:U64.t)
: probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler

inline_for_extraction
noextract
val fail
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool)
: probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler

inline_for_extraction
noextract
val if_then_else
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (b:bool) (m0 m1:probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler)
: probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler

inline_for_extraction
noextract
val probe_array
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (byte_len:U64.t) (probe_elem:probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler)
: probe_m #_ #_ #_ #_ #inst #cbinst unit true false use_error_handler

inline_for_extraction
noextract
let pure_external_action t =
  unit -> stt t emp (fun _ -> emp)

inline_for_extraction
noextract
val lift_pure_external_action
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (#use_error_handler:bool) (#a:Type) (f:pure_external_action a)
: probe_m #_ #_ #_ #_ #inst #cbinst a true false use_error_handler

inline_for_extraction
noextract
val init_and_probe 
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cbinst: copy_buffer copy_buffer_t base_t len_t pos_t |}
      (#use_error_handler:bool)
      (#mz:bool)
      (struct_name:string)
      (init:init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t)
      (probe:probe_m #_ #_ #_ #_ #inst #cbinst unit true mz use_error_handler)
: probe_m #_ #_ #_ #_ #inst #cbinst unit false mz use_error_handler

inline_for_extraction
noextract
val run_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (#any:bool) 
  (m:probe_m #_ #_ #_ #_ #inst #cb_inst unit false any use_error_handler)
  (tn fn det:string)
  (ctxt:app_ctxt)
  (err:(if use_error_handler then error_handler #_ #_ #_ #inst else unit))
  (src:U64.t)
  (sz:U64.t)
  (dest:copy_buffer_t)
: stt U64.t
    (exists* v_ctxt contents_dest v_dest .
      pts_to ctxt v_ctxt **
      CB.pts_to #_ #_ #_ #_ #_ #cb_inst dest contents_dest v_dest
    )
    (fun b -> exists* v_ctxt' contents_dest' v_dest' .
      pts_to ctxt v_ctxt' **
      CB.pts_to #_ #_ #_ #_ #_ #cb_inst dest contents_dest' v_dest' **
      pure (b <> 0uL ==> contents_dest' == v_dest')
    )

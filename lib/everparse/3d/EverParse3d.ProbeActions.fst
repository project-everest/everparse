module EverParse3d.ProbeActions
#lang-pulse

let probe_fn_incremental
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
= 
  bytes_to_read:U64.t ->
  read_offset:U64.t ->
  write_offset:U64.t ->
  src:U64.t ->
  dest:copy_buffer_t ->
  contents_dest: Ghost.erased (Seq.seq U8.t) ->
  v_dest: Ghost.erased (Seq.seq U8.t) ->
  stt bool
    (CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest v_dest **
      pure (Ghost.reveal contents_dest == Ghost.reveal v_dest))
    (fun b -> exists* contents_dest' v_dest' .
      CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest' v_dest' **
      pure
      (contents_dest' == v_dest' /\
       (b ==> (
        UInt.fits (U64.v read_offset + U64.v bytes_to_read) 64 /\
        UInt.fits (U64.v write_offset + U64.v bytes_to_read) 64
       ))))

inline_for_extraction
noextract
let init_probe_dest_t
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
=
  struct_name:string ->
  sz:U64.t ->
  dest:copy_buffer_t ->
  stt bool
    (exists* contents_dest v_dest .
      CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest v_dest
    )
    (fun b -> exists* contents_dest' .
      CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest' contents_dest'
    )

inline_for_extraction
let write_at_offset_t
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
(t:Type0) (n:U64.t) =
  v:t ->
  write_offset:U64.t ->
  dest:copy_buffer_t ->
  contents_dest: Ghost.erased (Seq.seq U8.t) ->
  v_dest: Ghost.erased (Seq.seq U8.t) ->
  stt bool
    (CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest v_dest **
      pure (Ghost.reveal contents_dest == Ghost.reveal v_dest))
    (fun b -> exists* contents_dest' v_dest' .
      CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest' v_dest' **
      pure
      (contents_dest' == v_dest' /\
       (b ==> UInt.fits (U64.v write_offset + U64.v n) 64)))

inline_for_extraction
let coerce_value_t (t0 t1:Type0) = t0 -> t1

inline_for_extraction
noextract
let probe_and_read_at_offset_t
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (t:Type0) (size_t:U64.t) =
  failed:ref bool ->
  read_offset:U64.t ->
  src:U64.t ->
  dest:copy_buffer_t ->
  contents_dest: Ghost.erased (Seq.seq U8.t) ->
  v_dest: Ghost.erased (Seq.seq U8.t) ->
  stt t
    (pts_to failed false **
      CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest v_dest **
      pure (Ghost.reveal contents_dest == Ghost.reveal v_dest))
    (fun _ -> exists* has_failed contents_dest' v_dest' .
      pts_to failed has_failed **
      CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest' v_dest' **
      pure (
        contents_dest' == v_dest' /\
        (not has_failed ==> U64.fits (U64.v read_offset + U64.v size_t))
      ))

inline_for_extraction
type probe_m_result a = a

unfold
let probe_m_pre
    (requires_unread_dest:bool)
    (expect_zero_offsets:bool)
    (v_read_offset: U64.t)
    (v_write_offset: U64.t)
    (v_failed: bool)
    (contents_dest v_dest: Seq.seq U8.t)
: prop
=
  (v_failed == false) /\
  (expect_zero_offsets ==>
    v_read_offset == 0uL /\
    v_write_offset == 0uL) /\
  (requires_unread_dest ==> contents_dest == v_dest)

unfold
let probe_m_post
    (r0 r1: U64.t)
    (w0 w1 : U64.t)
    (contents_dest' v_dest': Seq.seq U8.t)
: prop
=
  contents_dest' == v_dest' /\
  (
    U64.v w1 >= U64.v w0 /\
    U64.v r1 >= U64.v r0
  )

inline_for_extraction
let probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  a (requires_unread_dest:bool) (expect_zero_offsets:bool) (use_error_handler:bool) =
  typename:string ->
  fieldname:string ->
  fielddetail:string ->
  ctxt: app_ctxt ->
  error_handler_fn : (if use_error_handler then error_handler #_ #_ #_ #inst else unit) ->
  read_offset:ref U64.t ->
  write_offset:ref U64.t ->
  failed:ref bool ->
  src:U64.t ->
  init_probe_sz:U64.t ->
  dest:copy_buffer_t ->
  v_read_offset: Ghost.erased U64.t ->
  v_write_offset: Ghost.erased U64.t ->
  stt (probe_m_result a)
    (exists* v_ctxt v_failed contents_dest v_dest .
      pts_to ctxt v_ctxt **
      pts_to failed v_failed **
      pts_to read_offset v_read_offset **
      pts_to write_offset v_write_offset **
      CB.pts_to #_ #base_t #len_t #pos_t #_ #cb_inst dest contents_dest v_dest **
      pure
    (probe_m_pre
      requires_unread_dest expect_zero_offsets v_read_offset v_write_offset v_failed contents_dest v_dest)
    )
    (fun _ -> exists* v_ctxt' v_read_offset' v_write_offset' v_failed' contents_dest' v_dest' .
      pts_to ctxt v_ctxt' **
      pts_to failed v_failed' **
      pts_to read_offset v_read_offset' **
      pts_to write_offset v_write_offset' **
      CB.pts_to #_ #base_t #len_t #pos_t #_ #cb_inst dest contents_dest' v_dest' **
      pure
    (probe_m_post
      v_read_offset v_read_offset' v_write_offset v_write_offset' contents_dest' v_dest')
    )

(* Report an error either through the dynamic error-handler callback
   (`err`, when `use_error_handler` is set) or through the
   `EVERPARSE_ERROR_HANDLER_MACRO` C macro (`error_handler_macro`,
   otherwise).  This is the probe-monad counterpart of the branch used
   by `EverParse3d.Actions.Base.validate_with_error_handler`, and is
   what lets the probe combinators drop the function-pointer argument
   (it becomes `unit`, erased by KaRaMeL) under
   `--use_error_handler_macro`.

   As in the validators, the macro is passed in as an argument rather
   than looked up by linking: each input-stream backend module owns its
   own `[@@CMacro] assume val error_handler_macro`, and the 3D frontend
   instantiates this argument accordingly. *)
inline_for_extraction
noextract
fn handle_probe_error
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
      (#use_error_handler:bool)
      (error_handler_macro: error_handler #base_t #len_t #pos_t)
      (err : (if use_error_handler then error_handler #base_t #len_t #pos_t else unit))
      (tn fn_ det:string)
      (ctxt:app_ctxt)
      (dest:copy_buffer_t)
      (contents_dest v_dest: Ghost.erased (Seq.seq U8.t))
requires exists* v_ctxt .
      pts_to ctxt v_ctxt **
      CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest v_dest
ensures exists* v_ctxt' .
      pts_to ctxt v_ctxt' **
      CB.pts_to #_ #base_t #len_t #pos_t dest contents_dest v_dest
{
  rewrite (CB.pts_to #_ #base_t #len_t #pos_t #inst #cb_inst dest contents_dest v_dest)
    as (I.pts_to #base_t #len_t #pos_t
          (CB.base_of #_ #base_t #len_t #pos_t dest)
          (CB.len_of #_ #base_t #len_t #pos_t dest)
          (CB.pos_of #_ #base_t #len_t #pos_t dest)
          contents_dest v_dest);
  ((if use_error_handler then err else error_handler_macro) <: error_handler #base_t #len_t #pos_t #inst)
    tn fn_ det 0uy ctxt
      (CB.base_of #_ #base_t #len_t #pos_t dest)
      (CB.len_of #_ #base_t #len_t #pos_t dest)
      (CB.pos_of #_ #base_t #len_t #pos_t dest)
      contents_dest v_dest;
  rewrite (I.pts_to #base_t #len_t #pos_t
          (CB.base_of #_ #base_t #len_t #pos_t dest)
          (CB.len_of #_ #base_t #len_t #pos_t dest)
          (CB.pos_of #_ #base_t #len_t #pos_t dest)
          contents_dest v_dest)
    as (CB.pts_to #_ #base_t #len_t #pos_t #inst #cb_inst dest contents_dest v_dest);
}

inline_for_extraction
noextract
fn probe_fn_incremental_as_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (f:probe_fn_incremental #copy_buffer_t #base_t #len_t #pos_t) (bytes_to_read:U64.t)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (_sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
    let rd = !read_offset;
    let wr = !write_offset;
    let ok = f bytes_to_read rd wr src dest _ _;
    if (ok) {
      read_offset := U64.(rd +^ bytes_to_read);
      write_offset := U64.(wr +^ bytes_to_read)
    } else {
      failed := true
    }
}

inline_for_extraction
noextract
fn init_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (struct_name:string) (f:init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit false false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  let ok = f struct_name sz dest;
  if (ok) {
    ()
  } else {
    failed := true
  }
}

inline_for_extraction
noextract
fn init_probe_size
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool)
: probe_m #copy_buffer_t #base_t #len_t #pos_t U64.t true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  sz
}

inline_for_extraction
noextract
fn write_at_offset_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (#t:Type0) (#w:U64.t { w <> 0uL })
  (f:write_at_offset_t #copy_buffer_t #base_t #len_t #pos_t t w) (v:t)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  let wr = !write_offset;
  let ok = f v wr dest _ _;
  if (ok) {
    write_offset := U64.(wr +^ w)
  } else {
    failed := true
  }
}

inline_for_extraction
noextract
fn probe_and_read_at_offset_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (#t:Type0) (#s:U64.t { s <> 0uL })
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
  (reader:probe_and_read_at_offset_t #copy_buffer_t #base_t #len_t #pos_t t s)
: probe_m #copy_buffer_t #base_t #len_t #pos_t t true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  let rd = !read_offset;
  let v = reader failed rd src dest _ _;
  let has_failed = !failed;
  if (has_failed) {
    handle_probe_error #_ #base_t #len_t #pos_t error_handler_macro err tn fn_ fd ctxt dest _ _;
    v
  } else {
    read_offset := U64.(rd +^ s);
    v
  }
}

inline_for_extraction
noextract
fn seq_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (#a:Type0)
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
  (detail:string) (dflt:a)
  (m1:probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler)
  (m2:probe_m #copy_buffer_t #base_t #len_t #pos_t a true false use_error_handler)
: probe_m #copy_buffer_t #base_t #len_t #pos_t a true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  m1 tn fn_ fd ctxt err read_offset write_offset failed src sz dest _ _;
  let has_failed = !failed;
  if (has_failed) {
    handle_probe_error #_ #base_t #len_t #pos_t error_handler_macro err tn fn_ detail ctxt dest _ _;
    dflt
  } else {
    m2 tn fn_ fd ctxt err read_offset write_offset failed src sz dest _ _
  }
}

inline_for_extraction
noextract
fn bind_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (#a #b:Type0)
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
  (detail:string) (dflt:b)
  (m1:probe_m #copy_buffer_t #base_t #len_t #pos_t a true false use_error_handler)
  (m2:a -> probe_m #copy_buffer_t #base_t #len_t #pos_t b true false use_error_handler)
: probe_m #copy_buffer_t #base_t #len_t #pos_t b true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  let res1 = m1 tn fn_ fd ctxt err read_offset write_offset failed src sz dest _ _;
  let has_failed = !failed;
  if (has_failed) {
    handle_probe_error #_ #base_t #len_t #pos_t error_handler_macro err tn fn_ detail ctxt dest _ _;
    dflt
  } else {
    let m2' = m2 res1;
    m2' tn fn_ fd ctxt err read_offset write_offset failed src sz dest _ _
  }
}

inline_for_extraction
noextract
let probe_and_copy_init_sz
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool)
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
  (f:probe_fn_incremental #copy_buffer_t #base_t #len_t #pos_t)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler
= bind_probe_m #copy_buffer_t #base_t #len_t #pos_t
   error_handler_macro
   "probe_and_copy_init_sz"
    ()
    init_probe_size
    (probe_fn_incremental_as_probe_m f)

inline_for_extraction
noextract
fn return_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (#a:Type0) (v:a)
: probe_m #copy_buffer_t #base_t #len_t #pos_t a true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  v
}

inline_for_extraction
let check_overflow_add (x:U64.t) (y:U64.t)
: bool
= let open U64 in
  x <=^ (0xffffffffffffffffuL -^ y)

inline_for_extraction
noextract
fn skip_read
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (bytes_to_skip:U64.t)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  let rd = !read_offset;
  if (check_overflow_add rd bytes_to_skip) {
    read_offset := U64.(rd +^ bytes_to_skip)
  } else {
    failed := true
  }
}

inline_for_extraction
noextract
fn skip_write
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (bytes_to_skip:U64.t)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  let wr = !write_offset;
  if (check_overflow_add wr bytes_to_skip) {
    write_offset := U64.(wr +^ bytes_to_skip)
  } else {
    failed := true
  }
}

inline_for_extraction
noextract
fn fail
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  failed := true
}

inline_for_extraction
noextract
fn if_then_else
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (b:bool)
  (m0 m1:probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  if (b) {
    m0 tn fn_ fd ctxt err read_offset write_offset failed src sz dest _ _
  } else {
    m1 tn fn_ fd ctxt err read_offset write_offset failed src sz dest _ _
  }
}

#push-options "--z3rlimit 32 --fuel 0 --ifuel 1"

inline_for_extraction
noextract
fn probe_array
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool)
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
  (byte_len:U64.t)
  (probe_elem:probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  let mut ctr = byte_len;
  let mut stop = false;
  while (not !stop)
  invariant exists* vctr vstop v_ctxt' v_ro' v_wo' v_failed' contents_dest' v_dest' .
    pts_to ctr vctr **
    pts_to stop vstop **
    pts_to ctxt v_ctxt' **
    pts_to failed v_failed' **
    pts_to read_offset v_ro' **
    pts_to write_offset v_wo' **
    CB.pts_to #_ #base_t #len_t #pos_t #_ #cb_inst dest contents_dest' v_dest' **
    pure (
      contents_dest' == v_dest' /\
      U64.v v_ro' >= U64.v (Ghost.reveal v_read_offset) /\
      U64.v v_wo' >= U64.v (Ghost.reveal v_write_offset)
    )
  {
    let c0 = !ctr;
    let hf0 = !failed;
    if (hf0) {
      stop := true
    } else {
      if (c0 = 0uL) {
        stop := true
      } else {
        let r0 = !read_offset;
        probe_elem tn fn_ fd ctxt err read_offset write_offset failed src sz dest _ _;
        let hf1 = !failed;
        let r1 = !read_offset;
        if (hf1) {
          stop := true
        } else {
          if (r1 = r0) {
            handle_probe_error #_ #base_t #len_t #pos_t error_handler_macro err tn fn_ fd ctxt dest _ _;
            failed := true;
            stop := true
          } else {
            let bytes_read = U64.(r1 -^ r0);
            if (U64.lt c0 bytes_read) {
              handle_probe_error #_ #base_t #len_t #pos_t error_handler_macro err tn fn_ fd ctxt dest _ _;
              failed := true;
              stop := true
            } else {
              ctr := U64.(c0 -^ bytes_read)
            }
          }
        }
      }
    }
  };
  ()
}

#pop-options

inline_for_extraction
noextract
fn lift_pure_external_action
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (#a:Type0) (f:pure_external_action a)
: probe_m #copy_buffer_t #base_t #len_t #pos_t a true false use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  f ()
}

inline_for_extraction
noextract
fn init_and_probe
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
      (#use_error_handler:bool)
      (#mz:bool)
      (struct_name:string)
      (init:init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t)
      (probe:probe_m #copy_buffer_t #base_t #len_t #pos_t unit true mz use_error_handler)
: probe_m #copy_buffer_t #base_t #len_t #pos_t unit false mz use_error_handler
=
  (tn: _)
  (fn_: _)
  (fd: _)
  (ctxt: _)
  (err: _)
  (read_offset: _)
  (write_offset: _)
  (failed: _)
  (src: _)
  (sz: _)
  (dest: _)
  (v_read_offset: _)
  (v_write_offset: _)
{
  let ok = init struct_name sz dest;
  if (ok) {
    probe tn fn_ fd ctxt err read_offset write_offset failed src sz dest _ _
  } else {
    failed := true
  }
}

#push-options "--z3rlimit 32"

inline_for_extraction
noextract
fn run_probe_m
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#use_error_handler:bool) (#any:bool)
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
  (m:probe_m #copy_buffer_t #base_t #len_t #pos_t unit false any use_error_handler)
  (tn fn_ det:string)
  (ctxt:app_ctxt)
  (err:(if use_error_handler then error_handler #base_t #len_t #pos_t #inst else unit))
  (src:U64.t)
  (sz:U64.t)
  (dest:copy_buffer_t)
requires
    (exists* v_ctxt contents_dest v_dest .
      pts_to ctxt v_ctxt **
      CB.pts_to #_ #base_t #len_t #pos_t #_ #cb_inst dest contents_dest v_dest
    )
returns b: U64.t
ensures
    (exists* v_ctxt' contents_dest' v_dest' .
      pts_to ctxt v_ctxt' **
      CB.pts_to #_ #base_t #len_t #pos_t #_ #cb_inst dest contents_dest' v_dest' **
      pure (b <> 0uL ==> contents_dest' == v_dest')
    )
{
  let mut read_offset = 0uL;
  let mut write_offset = 0uL;
  let mut failed = false;
  m tn fn_ det ctxt err read_offset write_offset failed src sz dest _ _;
  let wr = !write_offset;
  let has_failed = !failed;
  if (has_failed) {
    handle_probe_error #_ #base_t #len_t #pos_t error_handler_macro err tn fn_ det ctxt dest _ _;
    0uL
  } else {
    wr
  }
}

#pop-options

inline_for_extraction
noextract
fn as_u64_identity_impl (x: U64.t) (_: unit)
requires emp
returns r: U64.t
ensures emp
{
  x
}

let as_u64_identity x = as_u64_identity_impl x

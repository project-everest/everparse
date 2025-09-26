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

let live_and_unread (dest:copy_buffer_t) h =
  let sl = stream_of dest in
  I.live sl h /\
  Seq.length (I.get_read sl h) == 0

let probe_fn_incremental = 
  bytes_to_read:U64.t ->
  read_offset:U64.t ->
  write_offset:U64.t ->
  src:U64.t ->
  dest:copy_buffer_t ->
  Stack bool
    (fun h0 ->
      live_and_unread dest h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      live_and_unread dest h1 /\
      (if b
       then (
        UInt.fits (U64.v read_offset + U64.v bytes_to_read) 64 /\
        UInt.fits (U64.v write_offset + U64.v bytes_to_read) 64 /\
        modifies (I.footprint sl) h0 h1
       )
       else (
        h0 == h1
       )))

inline_for_extraction
noextract
let init_probe_dest_t =
  sz:U64.t ->
  dest:copy_buffer_t ->
  Stack bool
    (fun h0 ->
      I.live (stream_of dest) h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      live_and_unread dest h1 /\
      modifies (I.footprint sl) h0 h1)

inline_for_extraction
let write_at_offset_t (t:Type0) (n:U64.t) =
  v:t ->
  write_offset:U64.t ->
  dest:copy_buffer_t ->
  Stack bool
    (fun h0 ->
      live_and_unread dest h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      live_and_unread dest h1 /\
      (if b
       then (
        UInt.fits (U64.v write_offset + U64.v n) 64 /\
        modifies (I.footprint sl) h0 h1
       )
       else (
        h0 == h1
       )))

inline_for_extraction
let coerce_value_t (t0 t1:Type0) = t0 -> t1

inline_for_extraction
noextract
let probe_and_read_at_offset_t (t:Type0) (size_t:U64.t) =
  failed:B.pointer bool ->
  read_offset:U64.t ->
  src:U64.t ->
  dest:copy_buffer_t ->
  Stack t
    (fun h0 ->
      let sl = stream_of dest in
      B.live h0 failed /\
      B.get h0 failed 0 == false /\
      live_and_unread dest h0)
    (fun h0 _ h1 ->
      live_and_unread dest h1 /\
      B.live h1 failed /\ 
      B.modifies (B.loc_buffer failed) h0 h1 /\ (
        let has_failed = B.get h1 failed 0 in
        not has_failed ==> U64.fits (U64.v read_offset + U64.v size_t)
      ))

inline_for_extraction
type probe_m_result a = a

unfold
let probe_m_pre
    (requires_unread_dest:bool)
    (expect_zero_offsets:bool) 
    (ctxt:app_ctxt)
    (read_offset:B.pointer U64.t)
    (write_offset:B.pointer U64.t)
    (failed:B.pointer bool)
    (src:U64.t)
    (dest:copy_buffer_t) 
    (h0:HS.mem)
: prop
= let sl = stream_of dest in
  let locs = 
    B.loc_union
      (B.loc_union
        (B.loc_buffer failed) 
        (B.loc_union
          (B.loc_buffer read_offset)
          (B.loc_buffer write_offset)))
      (loc_of dest)
  in  
  B.live h0 read_offset /\
  B.live h0 write_offset /\
  B.live h0 failed /\
  B.disjoint read_offset write_offset /\
  B.disjoint read_offset failed /\
  B.disjoint write_offset failed /\
  app_ctxt_error_pre ctxt locs h0 /\
  B.loc_disjoint
    (B.loc_union
      (B.loc_buffer failed) 
      (B.loc_union
        (B.loc_buffer read_offset)
        (B.loc_buffer write_offset)))
    (loc_of dest) /\
  (B.get h0 failed 0 == false) /\
  I.live sl h0 /\
  (expect_zero_offsets ==>
    B.get h0 read_offset 0 == 0uL /\
    B.get h0 write_offset 0 == 0uL) /\
  (requires_unread_dest ==> Seq.length (I.get_read sl h0) == 0)

unfold
let probe_m_post
    (#a:Type)
    (requires_unread_dest:bool)
    (expect_zero_offsets:bool) 
    (ctxt:app_ctxt)
    (read_offset:B.pointer U64.t)
    (write_offset:B.pointer U64.t)
    (failed:B.pointer bool)
    (src:U64.t)
    (dest:copy_buffer_t) 
    (h0:HS.mem)
    (res:a)
    (h1:HS.mem)
: prop
= let sl = stream_of dest in
  let locs = 
    B.loc_union
      (B.loc_union
        (B.loc_buffer failed) 
        (B.loc_union
          (B.loc_buffer read_offset)
          (B.loc_buffer write_offset)))
      (loc_of dest)
  in  
  live_and_unread dest h1 /\
  B.live h1 read_offset /\
  B.live h1 write_offset /\
  B.live h1 failed /\
  app_ctxt_error_pre ctxt locs h1 /\
  (
    let r0 = B.get h0 read_offset 0 in
    let r1 = B.get h1 read_offset 0 in
    let w0 = B.get h0 write_offset 0 in
    let w1 = B.get h1 write_offset 0 in
    let has_failed = B.get h1 failed 0 in
    U64.(w1 >=^ w0) /\
    U64.(r1 >=^ r0) /\
    modifies (app_loc ctxt locs) h0 h1)

inline_for_extraction
let probe_m a (requires_unread_dest:bool) (expect_zero_offsets:bool) =
  typename:string ->
  fieldname:string ->
  fielddetail:string ->
  ctxt: app_ctxt ->
  error_handler_fn : error_handler ->
  read_offset:B.pointer U64.t ->
  write_offset:B.pointer U64.t ->
  failed:B.pointer bool ->
  src:U64.t ->
  init_probe_sz:U64.t ->
  dest:copy_buffer_t ->
  Stack (probe_m_result a)
    (probe_m_pre 
      requires_unread_dest expect_zero_offsets ctxt read_offset write_offset failed src dest)
    (probe_m_post
      requires_unread_dest expect_zero_offsets ctxt read_offset write_offset failed src dest)

inline_for_extraction
noextract
let probe_fn_incremental_as_probe_m (f:probe_fn_incremental) (bytes_to_read:U64.t)
: probe_m unit true false
= fun _ _ _ ctxt err read_offset write_offset failed src _sz dest ->
    let h0  = get () in
    let rd = !*read_offset in
    let wr = !*write_offset in
    let ok = f bytes_to_read rd wr src dest in
    let h1 = get () in
    if ok
    then (
      read_offset *= U64.(rd +^ bytes_to_read);
      write_offset *= U64.(wr +^ bytes_to_read)
    )
    else (
      failed *= true
    )

inline_for_extraction
noextract
let init_probe_m (f:init_probe_dest_t)
: probe_m unit false false
= fun _ _ _ ctxt err read_offset write_offset failed src sz dest ->
    let ok = f sz dest in
    if ok
    then ()
    else (
      failed *= true
    )

inline_for_extraction
noextract
let init_probe_size
: probe_m U64.t true false
= fun _ _ _ ctxt err read_offset write_offset failed src sz dest ->
    sz

inline_for_extraction
noextract
let write_at_offset_m (#t:Type0) (#w:U64.t { w <> 0uL }) (f:write_at_offset_t t w) (v:t)
: probe_m unit true false
= fun _ _ _ ctxt err read_offset write_offset failed src _sz dest ->
    let wr = !*write_offset in
    let ok = f v wr dest in
    if ok
    then (
      write_offset *= U64.(wr +^ w)
    )
    else (
      failed *= true
    )


inline_for_extraction
noextract
let probe_and_read_at_offset_m (#t:Type0) (#s:U64.t { s <> 0uL }) (reader:probe_and_read_at_offset_t t s)
: probe_m t true false
= fun tn fn det ctxt err read_offset write_offset failed src _sz dest ->
    let rd = !*read_offset in
    let v = reader failed rd src dest in
    let has_failed = !*failed in
    if has_failed
    then (
      err tn fn det 0uL ctxt (CopyBuffer.stream_of dest) 0uL;
      v
    )
    else (
      read_offset *= U64.(rd +^ s);
      v
    )

inline_for_extraction
noextract
let seq_probe_m (#a:Type) (detail:string) (dflt:a) (m1:probe_m unit true false) (m2:probe_m a true false)
: probe_m a true false
= fun tn fn det ctxt err read_offset write_offset failed src sz dest ->
    let res1 = m1 tn fn det ctxt err read_offset write_offset failed src sz dest in
    let has_failed = !*failed in
    if has_failed
    then (
      err tn fn detail 0uL ctxt (CopyBuffer.stream_of dest) 0uL;
      dflt
    )
    else m2 tn fn det ctxt err read_offset write_offset failed src sz dest

inline_for_extraction
noextract
let bind_probe_m (#a #b:Type) (detail:string) (dflt:b) (m1:probe_m a true false) (m2:a -> probe_m b true false)
: probe_m b true false
= fun tn fn det ctxt err read_offset write_offset failed src sz dest ->
    let res1 = m1 tn fn det ctxt err read_offset write_offset failed src sz dest in
    let has_failed = !*failed in
    if has_failed 
    then (
      err tn fn detail 0uL ctxt (CopyBuffer.stream_of dest) 0uL;
      dflt
    )
    else m2 res1 tn fn det ctxt err read_offset write_offset failed src sz dest

inline_for_extraction
noextract
let probe_and_copy_init_sz (f:probe_fn_incremental)
: probe_m unit true false
= bind_probe_m 
   "probe_and_copy_init_sz"
    ()
    init_probe_size
    (probe_fn_incremental_as_probe_m f)

inline_for_extraction
noextract
let return_probe_m (#a:Type) (v:a)
: probe_m a true false
= fun _ _ _ ctxt err read_offset write_offset failed src sz dest -> v

inline_for_extraction
let check_overflow_add (x:U64.t) (y:U64.t)
: bool
= let open U64 in
  x <=^ (0xffffffffffffffffuL -^ y)

inline_for_extraction
noextract
let skip_read (bytes_to_skip:U64.t)
: probe_m unit true false
= fun _ _ _ ctxt err read_offset write_offset failed src sz dest ->
    let rd = !*read_offset in
    if check_overflow_add rd bytes_to_skip
    then (
      read_offset *= U64.(rd +^ bytes_to_skip)
    )
    else (
      failed *= true
    )  

inline_for_extraction
noextract
let skip_write (bytes_to_skip:U64.t)
: probe_m unit true false
= fun _ _ _ ctxt err read_offset write_offset failed src sz dest ->
    let wr = !*write_offset in
    if check_overflow_add wr bytes_to_skip
    then (
      write_offset *= U64.(wr +^ bytes_to_skip)
    )
    else (
      failed *= true
    )  

inline_for_extraction
noextract
let fail
: probe_m unit true false
= fun _ _ _ ctxt err read_offset write_offset failed src sz dest ->
    failed *= true

inline_for_extraction
noextract
let if_then_else (b:bool) (m0 m1:probe_m unit true false)
: probe_m unit true false
= fun tn fn det ctxt err read_offset write_offset failed src sz dest ->
    if b
    then m0 tn fn det ctxt err read_offset write_offset failed src sz dest
    else m1 tn fn det ctxt err read_offset write_offset failed src sz dest

module HST = FStar.HyperStack.ST
module CL = C.Loops
#push-options "--z3rlimit_factor 2 --ifuel 0 --fuel 0 --split_queries no"

unfold
let array_inv
    (requires_unread_dest:bool)
    (expect_zero_offsets:bool) 
    (ctxt:app_ctxt) 
    (read_offset:B.pointer U64.t)
    (write_offset:B.pointer U64.t)
    (failed:B.pointer bool)
    (src:U64.t)
    (dest:copy_buffer_t) 
    (not_failed_yet:bool)
    (byte_len:U64.t)
    (ctr:B.pointer U64.t)
    (hpre:HS.mem)
    (h0:HS.mem)
: prop
= let sl = stream_of dest in
  let locs =
    (B.loc_union
      (B.loc_buffer ctr)
      (B.loc_union
        (B.loc_buffer failed) 
        (B.loc_union
          (B.loc_buffer read_offset)
          (B.loc_buffer write_offset))))
  in
  app_ctxt_error_pre ctxt (loc_union locs (I.footprint sl)) h0 /\
  B.live h0 ctr /\
  B.live h0 read_offset /\
  B.live h0 write_offset /\
  B.live h0 failed /\
  B.disjoint read_offset write_offset /\
  B.disjoint read_offset failed /\
  B.disjoint write_offset failed /\
  B.loc_disjoint locs (loc_of dest) /\
  (not_failed_yet ==> B.get h0 failed 0 == false) /\
  I.live sl h0 /\
  U64.(B.get h0 ctr 0 <=^ byte_len) /\
  (expect_zero_offsets ==>
    B.get h0 read_offset 0 == 0uL /\
    B.get h0 write_offset 0 == 0uL) /\
  (requires_unread_dest ==> Seq.length (I.get_read sl h0) == 0) /\
  modifies (app_loc ctxt (B.loc_union locs (I.footprint sl))) hpre h0 /\
  (let r0 = B.get hpre read_offset 0 in
   let r1 = B.get h0 read_offset 0 in
   let w0 = B.get hpre write_offset 0 in
   let w1 = B.get h0 write_offset 0 in
   U64.(w1 >=^ w0) /\
   U64.(r1 >=^ r0) /\
  (B.get h0 failed 0 == false ==> (
   let bytes_read_so_far = U64.(r1 -^ r0) in
   let remaining_bytes = B.get h0 ctr 0 in
   U64.v bytes_read_so_far + U64.v remaining_bytes == U64.v byte_len)))
 
#push-options "--z3rlimit_factor 8 --ifuel 2 --fuel 0 --split_queries no --query_stats"
inline_for_extraction
noextract
let probe_array_aux (byte_len:U64.t) (probe_elem:probe_m unit true false)
  (tn fn det:string)
  (ctxt:AppCtxt.app_ctxt)
  (err:error_handler)
  (read_offset:B.pointer U64.t)
  (write_offset:B.pointer U64.t)
  (failed:B.pointer bool)
  (src:U64.t)
  (sz:U64.t)
  (dest:copy_buffer_t)
: Stack (probe_m_result unit)
    (fun h0 -> probe_m_pre true false ctxt read_offset write_offset failed src dest h0)
    (fun h0 x h1 -> probe_m_post true false ctxt read_offset write_offset failed src dest h0 x h1)
=   CopyBuffer.properties dest;
    let h0 = HST.get () in
    HST.push_frame ();
    let h01 = HST.get () in
    fresh_frame_modifies h0 h01;
    let ctr = alloca #U64.t byte_len 1ul in
    let hpre = HST.get () in
    let test_pre (not_failed_yet:bool) (h:HS.mem) : Type0 =
      array_inv 
        true false ctxt read_offset write_offset failed src dest
        not_failed_yet byte_len ctr hpre h
    in
    let test_post (b:bool) (h:HS.mem) : Type0 =
      array_inv 
        true false ctxt read_offset write_offset failed src dest
        b byte_len ctr hpre h /\
      (b <==> U64.v (B.get h ctr 0) > 0 /\ (B.get h failed 0 == false))
    in
    [@@inline_let]
    let test ()
      : Stack bool (fun h -> test_pre false h) (fun h0 x h1 -> test_post x h1)
      = let c = !*ctr in
        let has_failed = !*failed in
        let ww = !*write_offset in
        let rr = !*read_offset in
        (c <> 0uL && not has_failed)
    in
    [@@inline_let]
    let body ()
      : Stack unit 
        (fun h -> test_post true h)
        (fun h0 _ h1 -> test_pre false h1)
      = let r0 = !*read_offset in
        probe_elem tn fn det ctxt err read_offset write_offset failed src sz dest;
        let has_failed = !*failed in
        let r1 = !*read_offset in
        assert (U64.v r1 >= U64.v r0);
        let bytes_read = U64.(r1 -^ r0) in
        let c = !*ctr in
        if has_failed
        || bytes_read = 0uL
        || U64.(c <^ bytes_read)
        then (
          err tn fn det 0uL ctxt (CopyBuffer.stream_of dest) 0uL;
          failed *= true;
          ()
        )
        else (
          ctr *= U64.(c -^ bytes_read);
          ()
        )
    in
    C.Loops.while #(test_pre false) #test_post test body;
    let h1 = HST.get () in
    assert ( //if not faild, then we have advanced in the read buffer by exactly byte_len
      let has_failed = B.get h1 failed 0 in
      let c = B.get h1 ctr 0 in
      let r1 = B.get h1 read_offset 0 in
      let r0 = B.get hpre read_offset 0 in
      not has_failed ==> c==0uL /\ U64.(r1 -^ r0 == byte_len)
    );
    pop_frame();
    let h2 = HST.get () in
    // assert (live_and_unread dest h2);
    // assert (probe_m_post true false read_offset write_offset failed src dest h0 () h1);
    // assert (probe_m_post true false read_offset write_offset failed src dest h0 () h2);    
    ()
#pop-options

inline_for_extraction
noextract
let probe_array (byte_len:U64.t) (probe_elem:probe_m unit true false)
: probe_m unit true false
= probe_array_aux byte_len probe_elem

inline_for_extraction
noextract
let lift_pure_external_action (#a:Type) (f:pure_external_action a)
: probe_m a true false
= fun _ _ _ ctxt err read_offset write_offset failed src sz dest -> f()

inline_for_extraction
noextract
let init_and_probe
      (#mz:bool)
      (init:init_probe_dest_t)
      (probe:probe_m unit true mz)
: probe_m unit false mz
= fun tn fn det ctxt err read_offset write_offset failed src sz dest ->
    let ok = init sz dest in
    if ok
    then (
      probe tn fn det ctxt err read_offset write_offset failed src sz dest
    )
    else (
      failed *= true
    )

#pop-options

#push-options "--z3rlimit_factor 8 --split_queries no"

inline_for_extraction
noextract
let run_probe_m (#any:bool) 
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
= EverParse3d.CopyBuffer.properties dest;
  push_frame();
    let read_offset = alloca 0uL 1ul in
    let write_offset = alloca 0uL 1ul in
    let failed = alloca false 1ul in
    m tn fn det ctxt err read_offset write_offset failed src sz dest;
    let wr = !*write_offset in
    let has_failed = !*failed in
  pop_frame();
  if has_failed
  then (
    err tn fn det 0uL ctxt (CopyBuffer.stream_of dest) 0uL;
    0uL
  )
  else wr

#pop-options

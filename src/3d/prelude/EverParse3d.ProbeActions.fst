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

let probe_fn = src:U64.t -> len:U64.t -> dest:copy_buffer_t ->
  Stack bool
    (fun h0 ->
      I.live (stream_of dest) h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      I.live sl h1 /\
      (if b
       then (
        Seq.length (I.get_read sl h1) == 0 /\
        modifies (I.footprint sl) h0 h1
       )
       else (
        h0 == h1
       )))

let probe_fn_incremental = 
  bytes_to_read:U64.t ->
  read_offset:U64.t ->
  write_offset:U64.t ->
  src:U64.t ->
  dest:copy_buffer_t ->
  Stack bool
    (fun h0 ->
      I.live (stream_of dest) h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      I.live sl h1 /\
      Seq.length (I.get_read sl h1) == 0 /\
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
let write_at_offset_t (t:Type0) (n:U64.t) =
  v:t ->
  write_offset:U64.t ->
  dest:copy_buffer_t ->
  Stack bool
    (fun h0 ->
      I.live (stream_of dest) h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      I.live sl h1 /\
      Seq.length (I.get_read sl h1) == 0 /\
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
let probe_and_read_at_offset_t (t:Type0) (size_t:U64.t) =
  failed:B.pointer bool ->
  read_offset:U64.t ->
  src:U64.t ->
  Stack t
    (fun h0 ->
      B.live h0 failed /\
      B.get h0 failed 0 == false)
    (fun h0 _ h1 ->
      B.live h1 failed /\ 
      B.modifies (B.loc_buffer failed) h0 h1 /\ (
        let has_failed = B.get h1 failed 0 in
        not has_failed ==> U64.fits (U64.v read_offset + U64.v size_t)
      ))

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
type probe_m_result a = a

inline_for_extraction
let probe_m a =
  read_offset:B.pointer U64.t ->
  write_offset:B.pointer U64.t ->
  failed:B.pointer bool ->
  src:U64.t ->
  dest:copy_buffer_t ->
  Stack (probe_m_result a)
    (fun h0 ->
      B.live h0 read_offset /\
      B.live h0 write_offset /\
      B.live h0 failed /\
      B.disjoint read_offset write_offset /\
      B.disjoint read_offset failed /\
      B.disjoint write_offset failed /\
      B.loc_disjoint
        (B.loc_union
          (B.loc_buffer failed) 
          (B.loc_union
            (B.loc_buffer read_offset)
            (B.loc_buffer write_offset)))
        (loc_of dest) /\
      B.get h0 failed 0 == false /\
      I.live (stream_of dest) h0)
    (fun h0 res h1 ->
      let sl = stream_of dest in
      I.live sl h1 /\
      B.live h1 read_offset /\
      B.live h1 write_offset /\
      B.live h1 failed /\
      (
        let r0 = B.get h0 read_offset 0 in
        let r1 = B.get h1 read_offset 0 in
        let w0 = B.get h0 write_offset 0 in
        let w1 = B.get h1 write_offset 0 in
        let has_failed = B.get h1 failed 0 in
        U64.(w1 >=^ w0) /\
        U64.(r1 >=^ r0) /\
        (w0=w1 ==> Seq.length (I.get_read sl h1) == Seq.length (I.get_read sl h0)) /\
        (w0<>w1 ==> Seq.length (I.get_read sl h1) == 0) /\
        modifies 
            (B.loc_union 
              (B.loc_union 
                (B.loc_buffer failed)
                (B.loc_union 
                  (B.loc_buffer read_offset)
                  (B.loc_buffer write_offset)))
              (I.footprint sl)) h0 h1))

inline_for_extraction
noextract
let probe_fn_incremental_as_probe_m (f:probe_fn_incremental) (bytes_to_read:U64.t { bytes_to_read <> 0uL}) 
: probe_m unit
= fun read_offset write_offset failed src dest ->
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
let write_at_offset_m (#t:Type0) (#w:U64.t { w <> 0uL }) (f:write_at_offset_t t w) (v:t)
: probe_m unit
= fun read_offset write_offset failed src dest ->
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
: probe_m t
= fun read_offset write_offset failed src dest ->
    let rd = !*read_offset in
    let v = reader failed rd src in
    let has_failed = !*failed in
    if has_failed then v
    else (
      read_offset *= U64.(rd +^ s);
      v
    )

inline_for_extraction
noextract
let seq_probe_m (#a:Type) (dflt:a) (m1:probe_m unit) (m2:probe_m a)
: probe_m a
= fun read_offset write_offset failed src dest ->
    let res1 = m1 read_offset write_offset failed src dest in
    let has_failed = !*failed in
    if has_failed
    then dflt
    else m2 read_offset write_offset failed src dest

inline_for_extraction
noextract
let bind_probe_m (#a #b:Type) (dflt:b) (m1:probe_m a) (m2:a -> probe_m b)
: probe_m b
= fun read_offset write_offset failed src dest ->
    let res1 = m1 read_offset write_offset failed src dest in
    let has_failed = !*failed in
    if has_failed then dflt
    else m2 res1 read_offset write_offset failed src dest

inline_for_extraction
noextract
let return_probe_m (#a:Type) (v:a)
: probe_m a
= fun read_offset write_offset failed src dest -> v

inline_for_extraction
let check_overflow_add (x:U64.t) (y:U64.t)
: bool
= let open U64 in
  x <=^ (0xffffffffffffffffuL -^ y)

inline_for_extraction
noextract
let skip (bytes_to_skip:U64.t)
: probe_m unit
= fun read_offset write_offset failed src dest ->
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
let fail
: probe_m unit
= fun read_offset write_offset failed src dest ->
    failed *= true

inline_for_extraction
noextract
let if_then_else (b:bool) (m0 m1:probe_m unit)
: probe_m unit
= fun read_offset write_offset failed src dest ->
    if b
    then m0 read_offset write_offset failed src dest
    else m1 read_offset write_offset failed src dest
 
let pure_external_action t =
  unit -> Stack t (fun _ -> True) (fun h0 _ h1 -> h0==h1)

inline_for_extraction
noextract
let lift_pure_external_action (#a:Type) (f:pure_external_action a)
: probe_m a
= fun read_offset write_offset failed src dest -> f()

let probe_read_t0_and_write_t1
    (t0 t1:Type0)
    (size_t0:U64.t { size_t0 <> 0uL })
    (size_t1:U64.t { size_t1 <> 0uL })
    (reader:probe_and_read_at_offset_t t0 size_t0)
    (writer:write_at_offset_t t1 size_t1)
    (coerce_t0_t1:coerce_value_t t0 t1)
: probe_m unit
= bind_probe_m ()
    (probe_and_read_at_offset_m reader)
    (fun v -> write_at_offset_m writer (coerce_t0_t1 v)) 


inline_for_extraction
let probe_fn_as_probe_m (bytes_to_read:U64.t) (f:probe_fn)
: probe_m unit
= fun read_offset write_offset failed src dest ->
    let rd = !*read_offset in
    let wr = !*write_offset in
    if rd <> 0uL
    || wr <> 0uL
    || bytes_to_read = 0uL
    then (
      failed *= true
    )
    else ( 
      let h0 = get () in
      let ok = f src bytes_to_read dest in
      let h1 = get () in
      if ok
      then (
        read_offset *= bytes_to_read;
        write_offset *= bytes_to_read;
        ()
      )
      else (
        failed *= true
      )
    )

inline_for_extraction
noextract
let run_probe_m (m:probe_m unit) (src:U64.t) (dest:copy_buffer_t)
: Stack U64.t
    (fun h0 ->
      let sl = stream_of dest in
      I.live sl h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      I.live sl h1 /\
      modifies (I.footprint sl) h0 h1 /\
      (b <> 0uL ==> Seq.length (I.get_read sl h1) == 0))
= EverParse3d.CopyBuffer.properties dest;
  push_frame();
    let read_offset = alloca 0uL 1ul in
    let write_offset = alloca 0uL 1ul in
    let failed = alloca false 1ul in
    m read_offset write_offset failed src dest;
    let wr = !*write_offset in
    let has_failed = !*failed in
    let res = 
      if has_failed
      then 0uL
      else !*write_offset
    in
  pop_frame();
  res
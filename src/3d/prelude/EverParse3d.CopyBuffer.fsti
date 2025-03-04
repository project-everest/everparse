module EverParse3d.CopyBuffer
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.All
module B = LowStar.Buffer
module HS = FStar.HyperStack
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open LowStar.Buffer
open FStar.HyperStack.ST
val region : HS.rid

val copy_buffer_t : Type0

val stream_of : copy_buffer_t -> I.t
val stream_len (c:copy_buffer_t) : I.tlen (stream_of c)


let loc_of (x:copy_buffer_t) : GTot B.loc =
  I.footprint (stream_of x)

let inv (x:copy_buffer_t) (h:HS.mem) = I.live (stream_of x) h

let liveness_preserved (x:copy_buffer_t) =
  let sl = stream_of x in
  forall l h0 h1. {:pattern (modifies l h0 h1)}
    (I.live sl h0 /\
     B.modifies l h0 h1 /\
     address_liveness_insensitive_locs `loc_includes` l) ==>
    I.live sl h1

val properties (x:copy_buffer_t)
  : Lemma (
      liveness_preserved x /\
      B.loc_region_only true region `loc_includes` loc_of x /\
      region `HS.disjoint` AppCtxt.region
    )


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
  read_offset:U64.t ->
  src:U64.t ->
  Stack (option t)
    (fun h0 -> True)
    (fun h0 _ h1 -> 
      U64.fits (U64.v read_offset + U64.v size_t) /\
      h0 == h1)

type probe_m_result = {
  next_read_offset:  U64.t;
  next_write_offset: U64.t;
  failed: bool;
}

inline_for_extraction
let probe_m =
  read_offset:U64.t ->
  write_offset:U64.t ->
  src:U64.t ->
  dest:copy_buffer_t ->
  Stack probe_m_result
    (fun h0 ->
      I.live (stream_of dest) h0)
    (fun h0 res h1 ->
      let sl = stream_of dest in
      I.live sl h1 /\
      U64.(res.next_write_offset >=^ write_offset) /\
      U64.(res.next_read_offset >=^ read_offset) /\
      (if res.next_write_offset <> write_offset
       then
        modifies (I.footprint sl) h0 h1 /\
        (not res.failed ==> Seq.length (I.get_read sl h1) == 0)
      else h0 == h1))

inline_for_extraction
noextract
let probe_fn_incremental_as_probe_m (f:probe_fn_incremental) (bytes_to_read:U64.t { bytes_to_read <> 0uL}) 
: probe_m
= fun read_offset write_offset src dest ->
    let h0  = get () in
    let ok = f bytes_to_read read_offset write_offset src dest in
    let h1 = get () in
    if ok
    then
      {
        next_read_offset  = U64.(read_offset +^ bytes_to_read);
        next_write_offset = U64.(write_offset +^ bytes_to_read);
        failed = false 
      }
    else
      {
        next_read_offset  = read_offset;
        next_write_offset = write_offset;
        failed = true 
      }

inline_for_extraction
noextract
let write_at_offset_m (#t:Type0) (#w:U64.t { w <> 0uL }) (f:write_at_offset_t t w) (v:t)
: probe_m
= fun read_offset write_offset src dest ->
    let ok = f v write_offset dest in
    if ok
    then (
      {
        next_read_offset  = read_offset;
        next_write_offset = U64.(write_offset +^ w);
        failed = false
      }
    )
    else (
      {
        next_read_offset  = read_offset;
        next_write_offset = write_offset;
        failed = true
      }
    )

inline_for_extraction
noextract
let probe_read_t0_and_write_t1
    (t0 t1:Type0)
    (size_t0:U64.t { size_t0 <> 0uL })
    (size_t1:U64.t { size_t1 <> 0uL })
    (reader:probe_and_read_at_offset_t t0 size_t0)
    (writer:write_at_offset_t t1 size_t1)
    (coerce_t0_t1:coerce_value_t t0 t1)
: probe_m
= fun read_offset write_offset src dest ->
    let h0 = get () in
    let v = reader read_offset src in
    let h1 = get () in
    assert (h0 == h1);
    match v with
    | None ->
      { next_read_offset = read_offset; next_write_offset = write_offset; failed = true }
    | Some v ->
      let ok = writer (coerce_t0_t1 v) write_offset dest in
      if ok
      then 
        { next_read_offset = U64.(read_offset +^ size_t0); next_write_offset = U64.(write_offset +^ size_t1); failed = false }
      else
        { next_read_offset = read_offset; next_write_offset = write_offset; failed = true }

inline_for_extraction
noextract
let seq_probe_m (m1:probe_m) (m2:probe_m)
: probe_m
= fun read_offset write_offset src dest ->
    let res1 = m1 read_offset write_offset src dest in
    if res1.failed
    then res1
    else m2 res1.next_read_offset res1.next_write_offset src dest

inline_for_extraction
let check_overflow_add (x:U64.t) (y:U64.t)
: bool
= let open U64 in
  x <=^ (0xffffffffffffffffuL -^ y)

inline_for_extraction
let probe_fn_as_probe_m (bytes_to_read:U64.t { bytes_to_read <> 0uL}) (f:probe_fn)
: probe_m
= fun read_offset write_offset src dest ->
    if read_offset <> 0uL
    || write_offset <> 0uL
    then { next_read_offset = read_offset; next_write_offset = write_offset; failed = true }
    else ( 
      let h0 = get () in
      let ok = f src bytes_to_read dest in
      let h1 = get () in
      if ok
      then
        {
          next_read_offset  = bytes_to_read;
          next_write_offset = bytes_to_read;
          failed = false
        }
      else
        {
          next_read_offset  = read_offset;
          next_write_offset = write_offset;
          failed = true
        }
    )

inline_for_extraction
noextract
let run_probe_m (m:probe_m) (src:U64.t) (dest:copy_buffer_t)
: Stack U64.t
    (fun h0 ->
      let sl = stream_of dest in
      I.live sl h0)
    (fun h0 b h1 ->
      let sl = stream_of dest in
      I.live sl h1 /\
      modifies (I.footprint sl) h0 h1 /\
      (b <> 0uL ==> Seq.length (I.get_read sl h1) == 0))
= let res = m 0uL 0uL src dest in
  if res.failed
  then 0uL
  else res.next_write_offset
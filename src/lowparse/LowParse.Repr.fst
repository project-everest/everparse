(*
  Copyright 2015--2019 INRIA and Microsoft Corporation

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

  Authors: T. Ramananandro, A. Rastogi, N. Swamy, A. Fromherz
*)
module LowParse.Repr

module LP = LowParse.Low.Base
module LS = LowParse.SLow.Base
module B = LowStar.Buffer
module HS = FStar.HyperStack
module C = LowStar.ConstBuffer
module U32 = FStar.UInt32

open FStar.Integers
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module I = LowStar.ImmutableBuffer

(* Summary:

   A pointer-based representation type.

   See
   https://github.com/mitls/mitls-papers/wiki/The-Memory-Model-of-miTLS#pointer-based-transient-reprs

   Calling it LowParse.Ptr since it should eventually move to everparse/src/lowparse
 *)

inline_for_extraction let const_buffer = C.const_buffer LP.byte

/// `strong_parser_kind`: We restrict our attention to the
/// representation of types whose parsers have the strong-prefix
/// property.
let strong_parser_kind =
    k:LP.parser_kind{
      LP.(k.parser_kind_subkind == Some ParserStrong)
    }

let preorder (c:C.const_buffer LP.byte) = C.qbuf_pre (C.as_qbuf c)

let mut_p = LowStar.Buffer.trivial_preorder LP.byte


(*** Pointer-based Representation types ***)

/// `meta t`: Each representation is associated with
/// specification metadata that records
///
///  -- the parser(s) that defines its wire format
///  -- the represented value
///  -- the bytes of its wire format
///
///  We retain both the value and its wire format for convenience.
///
///  An alternative would be to also retain here a serializer and then
///  compute the bytes when needed from the serializer. But that's a
///  bit heavy
[@erasable]
noeq
type meta (t:Type) = {
  parser_kind: strong_parser_kind;
  parser:LP.parser parser_kind t;
  parser32:LS.parser32 parser;
  v: t;
  len: uint_32;
  repr_bytes: Seq.lseq LP.byte (U32.v len);
  meta_ok: squash (LowParse.Spec.Base.parse parser repr_bytes == Some (v, U32.v len))//  /\
                   // 0ul < len /\
                   // len < LP.validator_max_length)
}

/// `repr_ptr t`: The main type of this module.
///
///   * The const pointer `b` refers to a representation of `t`
///
///   * The representation is described by erased the `meta` field
///
/// Temporary fields:
///
///   * At this stage, we also keep a real high-level value (vv). We
///     plan to gradually access instead its ghost (.meta.v) and
///     eventually get rid of it to lower implicit heap allocations.
///
///   * We also retain a concrete length field to facilitate using the
///     LowParse APIs for accessors and jumpers, which are oriented
///     towards using slices rather than pointers. As those APIs
///     change, we will remove the length field.
noeq
type repr_ptr (t:Type) =
  | Ptr: b:C.const_buffer LP.byte ->
         meta:meta t ->
         vv:t { U32.v meta.len == C.length b /\
                       vv == meta.v } ->
       repr_ptr t

let region_of #t (p:repr_ptr t) : GTot HS.rid = B.frameOf (C.cast p.b)

let value #t (p:repr_ptr t) : GTot t = p.meta.v

let repr_ptr_p (t:Type) (#k:strong_parser_kind) (parser:LP.parser k t) =
  p:repr_ptr t{ p.meta.parser_kind == k /\ p.meta.parser == parser }

let sub_ptr (p2:repr_ptr 'a) (p1: repr_ptr 'b) =
  exists pos len. Ptr?.b p2 `C.const_sub_buffer pos len` Ptr?.b p1

let intro_sub_ptr (x:repr_ptr 'a) (y:repr_ptr 'b) (from to:uint_32)
  : Lemma
    (requires
       to >= from /\
       Ptr?.b x `C.const_sub_buffer from (to - from)` Ptr?.b y)
    (ensures
      x `sub_ptr` y)
  = ()

(*** Validity ***)

/// `valid' r h`:
///   We define validity in two stages:
///
///   First, we provide `valid'`, a transparent definition and then
///   turn it `abstract` by the `valid` predicate just below.
///
///   Validity encapsulates three related LowParse properties:notions:
///
///    1. The underlying pointer contains a valid wire-format
///    (`valid_pos`)
///
///    2. The ghost value associated with the `repr` is the
///        parsed value of the wire format.
///
///    3. The bytes of the slice are indeed the representation of the
///       ghost value in wire format

unfold
let valid' (#t:Type) (p:repr_ptr t) (h:HS.mem) =
  let meta = p.meta in
  let b = C.cast p.b in
  LP.bvalid_content_pos meta.parser h b 0ul meta.v meta.len /\
  meta.repr_bytes == LP.bytes_of_buffer_from_to h b 0ul meta.len

/// `valid`: abstract validity
abstract
let valid (#t:Type) (p:repr_ptr t) (h:HS.mem)
  = valid' p h

/// `reveal_valid`:
///   An explicit lemma exposes the definition of `valid`
let reveal_valid ()
  : Lemma (forall (t:Type) (p:repr_ptr t) (h:HS.mem).
              {:pattern (valid #t p h)}
           valid #t p h <==> valid' #t p h)
  = ()

let valid_repr_bytes
  (#t:Type) (p:repr_ptr t) (h:HS.mem) (s: LP.serializer p.meta.parser)
: Lemma
  (requires (valid p h))
  (ensures (
    p.meta.repr_bytes == LP.serialize s p.meta.v
  ))
= LP.parse_serialize s p.meta.v;
  LP.parse_injective p.meta.parser (LP.serialize s p.meta.v) p.meta.repr_bytes

/// `fp r`: The memory footprint of a repr_ptr is the underlying pointer
let fp #t (p:repr_ptr t)
  : GTot B.loc
  = C.loc_buffer p.b

/// `frame_valid`:
///    A framing principle for `valid r h`
///    It is invariant under footprint-preserving heap updates
let frame_valid #t (p:repr_ptr t) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      valid p h0 /\
      B.modifies l h0 h1 /\
      B.loc_disjoint (fp p) l)
    (ensures
      valid p h1)
    [SMTPat (valid p h1);
     SMTPat (B.modifies l h0 h1)]
  = ()

(***  Contructors ***)
/// `mk b from to p`:
///    Constructing a `repr_ptr` from a const_buffer
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
#set-options "--z3rlimit 20"
inline_for_extraction noextract
let mk_from_const_buffer
         (#k:strong_parser_kind) #t (#parser:LP.parser k t)
         (parser32:LS.parser32 parser)
         (jumper:LP.jumper parser)
         (b: C.const_buffer LP.byte)
         (from:uint_32)
  : Stack (repr_ptr_p t parser)
    (requires fun h ->
      LP.bvalid parser h (C.cast b) from)
    (ensures fun h0 p h1 ->
      B.(modifies loc_none h0 h1) /\
      valid p h1 /\
      p.meta.v == LP.bcontents parser h1 (C.cast b) from /\
      p.b `C.const_sub_buffer from p.meta.len` b)
  = let h = get () in
    let bb = C.cast b in
    let to = Ghost.hide (LP.bget_valid_pos parser h bb from) in
    LP.contents_exact_eq parser h (LP.slice_of_buffer bb) from (Ghost.reveal to);
    let meta :meta t = {
        parser_kind = _;
        parser = parser;
        parser32 = parser32;
        v = LP.bcontents parser h bb from;
        len = to - from;
        repr_bytes = LP.bytes_of_buffer_from_to h bb from to;
        meta_ok = ()
    } in
    let sub_b = C.sub b from (to - from) in
    let value =
      // Compute [.v]; this code will eventually disappear
      let to' : (to' : U32.t { to' == Ghost.reveal to }) = jumper (C.cast b) from in
      let sub_b_bytes = FStar.Bytes.of_buffer (to' - from) (C.cast sub_b) in
      let Some (v, _) = parser32 sub_b_bytes in
      v
    in
    let p = Ptr sub_b meta value in
    let h1 = get () in
    let bb' = C.cast sub_b in
    LP.bvalid_facts p.meta.parser h1 bb from; //elim valid_pos slice
    LP.bvalid_facts p.meta.parser h1 bb' 0ul; //intro valid_pos slice'
    p

/// `mk b from to p`:
///    Constructing a `repr_ptr` from a buffer
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
inline_for_extraction
noextract
let mk (#k:strong_parser_kind) #t (#parser:LP.parser k t)
       (parser32:LS.parser32 parser)
       (jumper:LP.jumper parser)
       #q
       (b:B.mbuffer LP.byte (C.q_preorder q LP.byte) (C.q_preorder q LP.byte))
       (from:uint_32)
  : Stack (repr_ptr_p t parser)
    (requires fun h ->
      LP.bvalid parser h b from)
    (ensures fun h0 p h1 ->
      B.(modifies loc_none h0 h1) /\
      valid p h1 /\
      p.b `C.const_sub_buffer from p.meta.len` (C.of_qbuf b) /\
      p.meta.v == LP.bcontents parser h1 b from)
  = let c = C.of_qbuf b in
    mk_from_const_buffer parser32 jumper c from

/// A high-level constructor, taking a value instead of a slice.
///
/// Can we remove the `noextract` for the time being? Can we
/// `optimize` it so that vv is assigned x? It will take us a while to
/// lower all message writing.
inline_for_extraction
noextract
let mk_from_serialize
    (#k:strong_parser_kind) #t (#parser:LP.parser k t) (#serializer: LP.serializer parser)
    (parser32: LS.parser32 parser) (serializer32: LS.serializer32 serializer)
    (size32: LS.size32 serializer)
    (jumper:LP.jumper parser)
    (b:LP.slice mut_p mut_p)
    (from:uint_32 { from <= b.LP.len })
    (x: t)
  : Stack (option (repr_ptr_p t parser))
    (requires fun h ->
       LP.live_slice h b)
    (ensures fun h0 popt h1 ->
       B.modifies (LP.loc_slice_from b from) h0 h1 /\
       (match popt with
       | None ->
         (* not enough space in output slice *)
         Seq.length (LP.serialize serializer x) > FStar.UInt32.v (b.LP.len - from)
       | Some p ->
         let size = size32 x in
         valid p h1 /\
         U32.v from + U32.v size <= U32.v b.LP.len /\
         p.meta.len == size /\
         p.b == C.gsub (C.of_buffer b.LP.base) from size /\
         p.meta.v == x))
  = let size = size32 x in
    let len = b.LP.len - from in
    if len < size
    then None
    else begin
      let bytes = serializer32 x in
      assert (size == FStar.Bytes.len bytes);
      let dst = B.sub b.LP.base from size in
      (if size > 0ul then FStar.Bytes.store_bytes bytes dst);
      let to = from + size in
      let h = get () in
      LP.serialize_valid_exact serializer h b x from to;
      LP.valid_bvalid_strong_prefix parser h b from;
      LP.parse_serialize serializer x;
      let r = mk parser32 jumper b.LP.base from in
      let h' = ST.get () in
      valid_repr_bytes r h' serializer;
      Some r
    end

(*** Destructors ***)


/// Computes the length in bytes of the representation
/// Using a LowParse "jumper"
let length #t (p: repr_ptr t) (j:LP.jumper p.meta.parser)
  : Stack U32.t
    (requires fun h ->
      valid p h)
    (ensures fun h n h' ->
      B.modifies B.loc_none h h' /\
      n == p.meta.len)
  = j (C.cast p.b) 0ul

/// `to_bytes`: for intermediate purposes only, extract bytes from the repr
let to_bytes #t (p: repr_ptr t) (len:uint_32)
  : Stack FStar.Bytes.bytes
    (requires fun h ->
      valid p h /\
      len == p.meta.len
    )
    (ensures fun h x h' ->
      B.modifies B.loc_none h h' /\
      FStar.Bytes.reveal x == p.meta.repr_bytes /\
      FStar.Bytes.len x == p.meta.len
    )
  = FStar.Bytes.of_buffer len (C.cast p.b)


(*** Stable Representations ***)

(*
   By copying a representation into an immutable buffer `i`,
   we obtain a stable representation, which remains valid so long
   as the `i` remains live.

   We achieve this by relying on support for monotonic state provided
   by Low*, as described in the POPL '18 paper "Recalling a Witness"

   TODO: The feature also relies on an as yet unimplemented feature to
         atomically allocate and initialize a buffer to a chosen
         value. This will soon be added to the LowStar library.
*)


/// `valid_if_live`: A pure predicate on `r:repr_ptr t` that states that
/// so long as the underlying buffer is live in a given state `h`,
/// `p` is valid in that state
let valid_if_live #t (p:repr_ptr t) =
  C.qbuf_qual (C.as_qbuf p.b) == C.IMMUTABLE /\
  (let i : I.ibuffer LP.byte = C.as_mbuf p.b in
   let m = p.meta in
   i `I.value_is` Ghost.hide m.repr_bytes /\
   (exists (h:HS.mem).{:pattern valid p h}
      m.repr_bytes == B.as_seq h i /\
      valid p h /\
      (forall h'.
        C.live h' p.b /\
        B.as_seq h i `Seq.equal` B.as_seq h' i ==>
        valid p h')))

/// `stable_repr_ptr t`: A representation that is valid if its buffer is
/// live
let stable_repr_ptr t= p:repr_ptr t { valid_if_live p }


/// `valid_if_live_intro` :
///    An internal lemma to introduce `valid_if_live`

// Note: the next proof is flaky and occasionally enters a triggering
// vortex with the notorious FStar.Seq.Properties.slice_slice
// Removing that from the context makes the proof instantaneous
#push-options "--max_ifuel 1 --initial_ifuel 1 \
                --using_facts_from '* -FStar.Seq.Properties.slice_slice'"
let valid_if_live_intro #t (r:repr_ptr t) (h:HS.mem)
  : Lemma
    (requires (
      C.qbuf_qual (C.as_qbuf r.b) == C.IMMUTABLE /\
      valid r h /\
      (let i : I.ibuffer LP.byte = C.as_mbuf r.b in
       let m = r.meta in
       B.as_seq h i == m.repr_bytes /\
       i `I.value_is` Ghost.hide m.repr_bytes)))
    (ensures
      valid_if_live r)
  = let i : I.ibuffer LP.byte = C.as_mbuf r.b in
    let aux (h':HS.mem)
        : Lemma
          (requires
            C.live h' r.b /\
            B.as_seq h i `Seq.equal` B.as_seq h' i)
          (ensures
            valid r h')
          [SMTPat (valid r h')]
        = let m = r.meta in
          LP.valid_ext_intro m.parser h (LP.slice_of_buffer (C.cast r.b)) 0ul h' (LP.slice_of_buffer (C.cast r.b)) 0ul
    in
    ()

let sub_ptr_stable (#t0 #t1:_) (r0:repr_ptr t0) (r1:repr_ptr t1) (h:HS.mem)
  : Lemma
    (requires
      r0 `sub_ptr` r1 /\
      valid_if_live r1 /\
      valid r1 h /\
      valid r0 h)
    (ensures
      valid_if_live r0 /\
      (let b0 = C.cast r0.b in
       let b1 = C.cast r1.b in
       B.frameOf b0 == B.frameOf b1 /\
      (B.region_lifetime_buf b1 ==>
       B.region_lifetime_buf b0)))
    [SMTPat (r0 `sub_ptr` r1);
     SMTPat (valid_if_live r1);
     SMTPat (valid r0 h)]
  = let b0 : I.ibuffer LP.byte = C.cast r0.b in
    let b1 : I.ibuffer LP.byte = C.cast r1.b in
    assert (I.value_is b1 (Ghost.hide r1.meta.repr_bytes));
    assert (Seq.length r1.meta.repr_bytes == B.length b1);
    let aux (i len:U32.t)
      : Lemma
        (requires
          r0.b `C.const_sub_buffer i len` r1.b)
        (ensures
          I.value_is b0 (Ghost.hide r0.meta.repr_bytes))
        [SMTPat (r0.b `C.const_sub_buffer i len` r1.b)]
      = I.sub_ptr_value_is b0 b1 h i len r1.meta.repr_bytes
    in
    B.region_lifetime_sub #_ #_ #_ #(I.immutable_preorder _) b1 b0;
    valid_if_live_intro r0 h

/// `recall_stable_repr_ptr` Main lemma: if the underlying buffer is live
///    then a stable repr_ptr is valid
let recall_stable_repr_ptr #t (r:stable_repr_ptr t)
  : Stack unit
    (requires fun h ->
      C.live h r.b)
    (ensures fun h0 _ h1 ->
      h0 == h1 /\
      valid r h1)
  = let h1 = get () in
    let i = C.to_ibuffer r.b in
    let aux (h:HS.mem)
      : Lemma
        (requires
          valid r h /\
          B.as_seq h i == B.as_seq h1 i)
        (ensures
          valid r h1)
        [SMTPat (valid r h)]
      = let m = r.meta in
        LP.valid_ext_intro m.parser h (LP.slice_of_buffer (C.cast r.b)) 0ul h1 (LP.slice_of_buffer (C.cast r.b)) 0ul
     in
     let es =
       let m = r.meta in
       Ghost.hide m.repr_bytes
     in
     I.recall_value i es

let is_stable_in_region #t (p:repr_ptr t) =
  let r = B.frameOf (C.cast p.b) in
  valid_if_live p /\
  B.frameOf (C.cast p.b) == r /\
  B.region_lifetime_buf (C.cast p.b)

let stable_region_repr_ptr (r:ST.drgn) (t:Type) =
  p:repr_ptr t {
    is_stable_in_region p /\
    B.frameOf (C.cast p.b) == ST.rid_of_drgn r
  }

let recall_stable_region_repr_ptr #t (r:ST.drgn) (p:stable_region_repr_ptr r t)
  : Stack unit
    (requires fun h ->
      HS.live_region h (ST.rid_of_drgn r))
    (ensures fun h0 _ h1 ->
      h0 == h1 /\
      valid p h1)
  = B.recall (C.cast p.b);
    recall_stable_repr_ptr p

private
let ralloc_and_blit (r:ST.drgn) (src:C.const_buffer LP.byte) (len:U32.t)
  : ST (b:C.const_buffer LP.byte)
    (requires fun h0 ->
      HS.live_region h0 (ST.rid_of_drgn r) /\
      U32.v len == C.length src /\
      C.live h0 src)
    (ensures fun h0 b h1 ->
      let c = C.as_qbuf b in
      let s = Seq.slice (C.as_seq h0 src) 0 (U32.v len) in
      let r = ST.rid_of_drgn r in
      C.qbuf_qual c == C.IMMUTABLE /\
      B.alloc_post_mem_common (C.to_ibuffer b) h0 h1 s /\
      C.to_ibuffer b `I.value_is` s /\
      B.region_lifetime_buf (C.cast b) /\
      B.frameOf (C.cast b) == r)
  = let src_buf = C.cast src in
    assume (U32.v len > 0);
    let b : I.ibuffer LP.byte = B.mmalloc_drgn_and_blit r src_buf 0ul len in
    let h0 = get() in
    B.witness_p b (I.seq_eq (Ghost.hide (Seq.slice (B.as_seq h0 src_buf) 0 (U32.v len))));
    C.of_ibuffer b


/// `stash`: Main stateful operation
///    Copies a repr_ptr into a fresh stable repr_ptr in the given region
let stash (rgn:ST.drgn) #t (r:repr_ptr t) (len:uint_32{len == r.meta.len})
  : ST (stable_region_repr_ptr rgn t)
   (requires fun h ->
     valid r h /\
     HS.live_region h (ST.rid_of_drgn rgn))
   (ensures fun h0 r' h1 ->
     B.modifies B.loc_none h0 h1 /\
     valid r' h1 /\
     r.meta == r'.meta)
 = let buf' = ralloc_and_blit rgn r.b len in
   let h = get () in
   let _ =
     LP.bvalid_facts r.meta.parser h (C.cast r.b) 0ul; //elim valid_pos slice
     LP.bvalid_facts r.meta.parser h (C.cast buf') 0ul //intro valid_pos slice'
   in
   let p = Ptr buf' r.meta r.vv in
   valid_if_live_intro p h;
   p

(*** Accessing fields of ptrs ***)

/// Instances of field_accessor should be marked `unfold`
/// so that we get compact verification conditions for the lens conditions
/// and to inline the code for extraction
noeq inline_for_extraction
type field_accessor (#k1 #k2:strong_parser_kind)
                    (#t1 #t2:Type)
                    (p1 : LP.parser k1 t1)
                    (p2 : LP.parser k2 t2) =
  | FieldAccessor :
     (#cl: LP.clens t1 t2) ->
     (#g: LP.gaccessor p1 p2 cl) ->
     (acc:LP.accessor g) ->
     (jump:LP.jumper p2) ->
     (p2': LS.parser32 p2) ->
     field_accessor p1 p2

unfold noextract
let field_accessor_comp (#k1 #k2 #k3:strong_parser_kind)
                        (#t1 #t2 #t3:Type)
                        (#p1 : LP.parser k1 t1)
                        (#p2 : LP.parser k2 t2)
                        (#p3 : LP.parser k3 t3)
                        (f12 : field_accessor p1 p2)
                        (f23 : field_accessor p2 p3)
   : field_accessor p1 p3
   =
   [@inline_let] let FieldAccessor acc12 j2 p2' = f12 in
   [@inline_let] let FieldAccessor acc23 j3 p3' = f23 in
   [@inline_let] let acc13 = LP.accessor_compose acc12 acc23 () in
     FieldAccessor acc13 j3 p3'

unfold noextract
let field_accessor_t
      (#k1:strong_parser_kind) #t1 (#p1:LP.parser k1 t1)
      (#k2: strong_parser_kind) (#t2:Type) (#p2:LP.parser k2 t2)
      (f:field_accessor p1 p2)
   =  p:repr_ptr_p t1 p1 ->
      Stack (repr_ptr_p t2 p2)
      (requires fun h ->
         valid p h /\
         f.cl.LP.clens_cond p.meta.v)
      (ensures fun h0 (q:repr_ptr_p t2 p2) h1 ->
        f.cl.LP.clens_cond p.meta.v /\
        B.modifies B.loc_none h0 h1 /\
        valid q h1 /\
        value q == f.cl.LP.clens_get (value p) /\
        q `sub_ptr` p /\
        region_of q == region_of p)

inline_for_extraction
let get_field (#k1:strong_parser_kind) #t1 (#p1:LP.parser k1 t1)
              (#k2: strong_parser_kind) (#t2:Type) (#p2:LP.parser k2 t2)
              (f:field_accessor p1 p2)
   : field_accessor_t f
   = fun p ->
     [@inline_let] 
     let FieldAccessor acc jump p2' = f in
     let pos = acc (C.cast p.b) 0ul in
     let q = mk p2' jump (C.cast p.b) pos in
     let h = get () in
     assert (q.b `C.const_sub_buffer pos q.meta.len` p.b);
     assert (q `sub_ptr` p); //needed to trigger the sub_ptr_stable lemma
     assert (is_stable_in_region p ==> is_stable_in_region q);
     q

/// Instances of field_reader should be marked `unfold`
/// so that we get compact verification conditions for the lens conditions
/// and to inline the code for extraction
noeq
type field_reader (#k1:strong_parser_kind)
                  (#t1:Type)
                  (p1 : LP.parser k1 t1)
                  (t2:Type) =
  | FieldReader :
     (#k2: strong_parser_kind) ->
     (#p2: LP.parser k2 t2) ->
     (#cl: LP.clens t1 t2) ->
     (#g: LP.gaccessor p1 p2 cl) ->
     (acc:LP.accessor g) ->
     (reader: LP.leaf_reader p2) ->
     field_reader p1 t2


unfold
let field_reader_t
      (#k1:strong_parser_kind) #t1 (#p1:LP.parser k1 t1)
      (#t2:Type)
      (f:field_reader p1 t2)
  =  p:repr_ptr_p t1 p1 ->
     Stack t2
     (requires fun h ->
       valid p h /\
       f.cl.LP.clens_cond p.meta.v)
     (ensures fun h0 pv h1 ->
       B.modifies B.loc_none h0 h1 /\
       pv == f.cl.LP.clens_get (value p))

inline_for_extraction
let read_field (#k1:strong_parser_kind) (#t1:_) (#p1:LP.parser k1 t1)
               #t2 (f:field_reader p1 t2)
  : field_reader_t f
  = fun p ->
    [@inline_let]
    let FieldReader acc reader = f in
    let pos = acc (C.cast p.b) 0ul in
    reader (C.cast p.b) pos

(*** Positional representation types ***)

/// `index b` is the type of valid indexes into `b`
let index (b: C.const_buffer LP.byte)= i:uint_32{ U32.v i <= C.length b }

noeq
type repr_pos (t:Type) (b:C.const_buffer LP.byte) =
  | Pos: start_pos:index b ->
         meta:meta t ->
         vv_pos:t //temporary
                       { U32.v start_pos + U32.v meta.len <= C.length b /\
                        vv_pos == meta.v  } ->
         repr_pos t b

let value_pos #t #b (r:repr_pos t b) : GTot t = r.meta.v

let as_ptr_spec #t #b (p:repr_pos t b)
  : GTot (repr_ptr t)
  = Ptr (C.gsub b p.start_pos ((Pos?.meta p).len))
        (Pos?.meta p)
        (Pos?.vv_pos p)


let const_buffer_of_repr_pos #t #b (r:repr_pos t b)
  : GTot (C.const_buffer LP.byte)
  = C.gsub b r.start_pos r.meta.len

/// `repr_pos_p`, the analog of `repr_ptr_p`
let repr_pos_p (t:Type) (b: C.const_buffer LP.byte) #k (parser:LP.parser k t) =
  r:repr_pos t b {
    r.meta.parser_kind == k /\
    r.meta.parser == parser
  }

(*** Validity ***)
/// `valid`: abstract validity
let valid_repr_pos (#t:Type) (#b: C.const_buffer LP.byte) (r:repr_pos t b) (h:HS.mem)
  = valid (as_ptr_spec r) h /\
    C.live h b

/// `fp r`: The memory footprint of a repr_pos is the
///         sub-slice b.[from, to)
let fp_pos #t (#b: C.const_buffer LP.byte) (r:repr_pos t b)
  : GTot B.loc
  = fp (as_ptr_spec r)

/// `frame_valid`:
///    A framing principle for `valid r h`
///    It is invariant under footprint-preserving heap updates
let frame_valid_repr_pos #t #b (r:repr_pos t b) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      valid_repr_pos r h0 /\
      B.modifies l h0 h1 /\
      B.loc_disjoint (fp_pos r) l)
    (ensures
      valid_repr_pos r h1)
    [SMTPat (valid_repr_pos r h1);
     SMTPat (B.modifies l h0 h1)]
  = ()

(*** Operations on repr_pos ***)

/// End position
let end_pos #t #b (r:repr_pos t b)
  : GTot (index b)
  = r.start_pos + r.meta.len

abstract
let valid_repr_pos_elim
  (#t: Type)
  (#b: _)
  (r: repr_pos t b)
  (h: HS.mem)
: Lemma
  (requires (
    valid_repr_pos r h
  ))
  (ensures (
    LP.bvalid_content_pos r.meta.parser h (C.cast b) r.start_pos r.meta.v (end_pos r)
  ))
= let p : repr_ptr t = as_ptr_spec r in
  LP.bvalid_facts r.meta.parser h (C.cast (Ptr?.b p)) 0ul;
  LP.bvalid_facts r.meta.parser h (C.cast b) r.start_pos;
  LP.parse_strong_prefix r.meta.parser (LP.bytes_of_buffer_from h (C.cast (Ptr?.b p)) 0ul) (LP.bytes_of_buffer_from h (C.cast b) r.start_pos)

/// Mostly just by inheriting operations on pointers
let as_ptr #t #b (r:repr_pos t b)
  : Stack (repr_ptr t)
    (requires fun h ->
      valid_repr_pos r h)
    (ensures fun h0 ptr h1 ->
      ptr == as_ptr_spec r /\
      h0 == h1)
  = let b = C.sub b r.start_pos (Ghost.hide r.meta.len) in
    let m = r.meta in
    let v = r.vv_pos in
    Ptr b m v

let as_repr_pos #t (b: C.const_buffer LP.byte) (from:index b) (to: Ghost.erased (index b)) (p:repr_ptr t)
  : Pure (repr_pos t b)
    (requires
      from <= to /\
      Ptr?.b p  == C.gsub b from (to - from))
    (ensures fun r ->
      p == as_ptr_spec r)
  = Pos from (Ptr?.meta p) (Ptr?.vv p)

/// `mk_repr_pos b from to p`:
///    Constructing a `repr_pos` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
inline_for_extraction
let mk_repr_pos (#k:strong_parser_kind) #t (#parser:LP.parser k t)
                (parser32:LS.parser32 parser)
                (jumper:LP.jumper parser)
                (b: B.mbuffer LP.byte mut_p mut_p)
                (from:index (C.of_qbuf b))
  : Stack (repr_pos_p t (C.of_qbuf b) parser)
    (requires fun h ->
      LP.bvalid parser h b from)
    (ensures fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      valid_repr_pos r h1 /\
      r.start_pos = from /\
      r.vv_pos == LP.bcontents parser h1 b from)
  = let h = ST.get () in
    let to = Ghost.hide (LP.bget_valid_pos parser h b from) in
    let r = mk parser32 jumper b from in
    LP.bvalid_facts parser h b from;
    LP.parse_injective parser (LP.bytes_of_buffer_from h b from) ((Ptr?.meta r).repr_bytes);
    as_repr_pos (C.of_qbuf b) from to r

/// `mk b from to p`:
///    Constructing a `repr_pos` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
inline_for_extraction
let mk_repr_pos_from_const_buffer
         (#k:strong_parser_kind) #t (#parser:LP.parser k t)
         (parser32:LS.parser32 parser)
         (jumper:LP.jumper parser)
         (b: C.const_buffer LP.byte)
         (from:index b)
  : Stack (repr_pos_p t b parser)
    (requires fun h ->
      LP.bvalid parser h (C.cast b) from)
    (ensures fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      valid_repr_pos r h1 /\
      r.start_pos = from /\
      r.vv_pos == LP.bcontents parser h1 (C.cast b) from)
  = let h = ST.get () in
    let to = Ghost.hide (LP.bget_valid_pos parser h (C.cast b) from) in
    let r = mk_from_const_buffer  parser32 jumper b from in
    LP.bvalid_facts parser h (C.cast b) from;
    LP.parse_injective parser (LP.bytes_of_buffer_from h (C.cast b) from) ((Ptr?.meta r).repr_bytes);
    as_repr_pos b from to r

/// A high-level constructor, taking a value instead of a slice.
///
/// Can we remove the `noextract` for the time being? Can we
/// `optimize` it so that vv is assigned x? It will take us a while to
/// lower all message writing.
inline_for_extraction
noextract
let mk_repr_pos_from_serialize
  (#k:strong_parser_kind) #t (#parser:LP.parser k t) (#serializer: LP.serializer parser)
  (parser32: LS.parser32 parser) (serializer32: LS.serializer32 serializer)
  (size32: LS.size32 serializer)
  (jumper:LP.jumper parser)
  (b:LP.slice mut_p mut_p{ LP.(b.len <= validator_max_length) })
  (from: U32.t { from <= b.LP.len })
  (x: t)
: Stack (option (repr_pos_p t (C.of_qbuf b.LP.base) parser))
    (requires fun h ->
      LP.live_slice h b)
    (ensures fun h0 r h1 ->
      B.modifies (LP.loc_slice_from b from) h0 h1 /\
      begin match r with
      | None ->
        (* not enough space in output slice *)
        Seq.length (LP.serialize serializer x) > U32.v b.LP.len - FStar.UInt32.v from
      | Some r ->
        valid_repr_pos r h1 /\
        r.start_pos == from /\
        r.vv_pos == x /\
        v (end_pos r) = v from + v (size32 x)
      end
    )
= let size = size32 x in
  match (mk_from_serialize parser32 serializer32 size32 jumper b from x) with
  | None -> None
  | Some p -> Some (as_repr_pos (C.of_qbuf b.LP.base) from (from + size) p)

/// Accessors on positional reprs
unfold
let field_accessor_pos_post (#b:C.const_buffer LP.byte) (#t1:Type) (p:repr_pos t1 b)
                            (#k2: strong_parser_kind)
                            (#t2:Type)
                            (#p2: LP.parser k2 t2)
                            (f:field_accessor p.meta.parser p2) =
   fun h0 (q:repr_pos_p t2 b p2) h1 ->
      let cl = FieldAccessor?.cl f in
      cl.LP.clens_cond p.meta.v /\
      B.modifies B.loc_none h0 h1 /\
      valid_repr_pos q h1 /\
      value_pos q == cl.LP.clens_get (value_pos p)

unfold
let get_field_pos_t (#k1: strong_parser_kind) (#t1: Type) (#p1: LP.parser k1 t1)
                    (#k2: strong_parser_kind) (#t2: Type) (#p2: LP.parser k2 t2)
                    (f:field_accessor p1 p2)
   = (#b: _) ->
     (pp:repr_pos_p t1 b p1) ->
    Stack (repr_pos_p t2 b p2)
     (requires fun h ->
       let cl = FieldAccessor?.cl f in
       valid_repr_pos pp h /\
       cl.LP.clens_cond pp.meta.v)
     (ensures
       field_accessor_pos_post pp f)


inline_for_extraction
let get_field_pos (#k1: strong_parser_kind) (#t1: Type) (#p1: LP.parser k1 t1)
                  (#k2: strong_parser_kind) (#t2: Type) (#p2: LP.parser k2 t2)
                  (f:field_accessor p1 p2)
 : get_field_pos_t f
 = fun #b pp ->
    [@inline_let]
    let FieldAccessor acc jump p2' = f in
    let h = ST.get () in
    valid_repr_pos_elim pp h;
    let pos = acc (C.cast b) pp.start_pos in
    mk_repr_pos_from_const_buffer p2' jump b pos

unfold
let read_field_pos_t (#k1: strong_parser_kind) (#t1: Type) (#p1: LP.parser k1 t1)
                     #t2 (f:field_reader p1 t2)
  = (#b:_) ->
    (p:repr_pos_p t1 b p1) ->
    Stack t2
    (requires fun h ->
      valid_repr_pos p h /\
      f.cl.LP.clens_cond p.meta.v)
    (ensures fun h0 pv h1 ->
      B.modifies B.loc_none h0 h1 /\
      pv == f.cl.LP.clens_get (value_pos p))

inline_for_extraction
let read_field_pos (#k1: strong_parser_kind) (#t1: Type) (#p1: LP.parser k1 t1)
                   #t2 (f:field_reader p1 t2)
   : read_field_pos_t f
   = fun #b p ->
     read_field f (as_ptr p)

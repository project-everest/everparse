module CBOR.Pulse.Raw.EverParse.Det.Serialize

open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* ============================================================
   Postconditions over raw_data_item.
   ============================================================ *)

noextract [@@noextract_to "krml"]
let cbor_serialize_tag_postcond
  (tag: raw_uint64)
  (output: S.slice U8.t)
  (res: SZ.t)
  (v': Seq.seq U8.t)
: Tot prop
= let s = serialize_cbor_tag tag in
  let len = Seq.length s in
  SZ.v (S.len output) == Seq.length v' /\
  SZ.v res <= Seq.length v' /\
  (res == 0sz <==> len > Seq.length v') /\
  (len <= Seq.length v' ==> Seq.slice v' 0 (SZ.v res) == s)

let cbor_serialize_array_precond
  (len: raw_uint64)
  (l: list raw_data_item)
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= SZ.v off <= Seq.length v /\
  Seq.slice v 0 (SZ.v off) == serialize_cbor_list l /\
  List.Tot.length l == U64.v len.value

let cbor_serialize_array_postcond
  (len: raw_uint64)
  (l: list raw_data_item)
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= List.Tot.length l == U64.v len.value /\
  SZ.v res <= Seq.length v /\
  (res == 0sz <==> Seq.length (serialize_cbor (Array len l)) > Seq.length v) /\
  (SZ.v res > 0 ==> Seq.slice v 0 (SZ.v res) `Seq.equal` serialize_cbor (Array len l))

let cbor_serialize_string_precond
  (ty: major_type_byte_string_or_text_string)
  (off: raw_uint64)
  (v: Seq.seq U8.t)
: Tot prop
= U64.v off.value <= Seq.length v /\
  (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct (Seq.slice v 0 (U64.v off.value)))

let cbor_serialize_string_postcond
  (ty: major_type_byte_string_or_text_string)
  (off: raw_uint64)
  (v: Seq.seq U8.t)
  (res: SZ.t)
  (v': Seq.seq U8.t)
: Tot prop
= cbor_serialize_string_precond ty off v /\
  begin let l = Seq.slice v 0 (U64.v off.value) in
  Seq.length v' == Seq.length v /\
  SZ.v res <= Seq.length v' /\
  (res == 0sz <==> Seq.length (serialize_cbor (String ty off l)) > Seq.length v') /\
  (SZ.v res > 0 ==> Seq.slice v' 0 (SZ.v res) `Seq.equal` serialize_cbor (String ty off l))
  end

inline_for_extraction
let cbor_serialize_string_t =
  (ty: major_type_byte_string_or_text_string) ->
  (off: raw_uint64) ->
  (out: S.slice U8.t) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
  (pts_to out v **
    pure (cbor_serialize_string_precond ty off v)
  )
  (fun res -> exists* v' .
    pts_to out v' **
    pure (cbor_serialize_string_postcond ty off v res v')
  )

let cbor_serialize_map_precond
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= SZ.v off <= Seq.length v /\
  Seq.slice v 0 (SZ.v off) == serialize_cbor_map l /\
  List.Tot.length l == U64.v len.value

let cbor_serialize_map_postcond
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= List.Tot.length l == U64.v len.value /\
  SZ.v res <= Seq.length v /\
  (res == 0sz <==> Seq.length (serialize_cbor (Map len l)) > Seq.length v) /\
  (SZ.v res > 0 ==> Seq.slice v 0 (SZ.v res) `Seq.equal` serialize_cbor (Map len l))

(* Operations *)

val cbor_serialize_tag
  (tag: raw_uint64)
  (output: S.slice U8.t)
: stt SZ.t
  (exists* v . pts_to output v)
  (fun res -> exists* v . pts_to output v ** pure (cbor_serialize_tag_postcond tag output res v))

val cbor_serialize_array
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list raw_data_item))
  (off: SZ.t)
: stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_serialize_array_precond len l off v)
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_serialize_array_postcond len l res v)
  )

val cbor_serialize_string (_: unit) : cbor_serialize_string_t

val cbor_serialize_map
  (len: raw_uint64)
  (out: S.slice U8.t)
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off: SZ.t)
: stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_serialize_map_precond len l off v)
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_serialize_map_postcond len l res v)
  )

(* TODO: cbor_raw_map_insert: in-place insert a key/value pair into the
   canonical sorted entry list of an already-serialized map. Legacy version
   in raw/old/CBOR.Pulse.Raw.Insert.fst (~370 lines) needs to be ported
   to the new EverParse stack.

   Status of port investigation (multiple sessions):

   ✓ All structural pieces compile (cbor_jump_append wrapping
     Validate.jump_raw_data_item via parse_strong_prefix; the inv,
     inv_not_success, _equiv lemmas; the while-loop body shape).

   ✓ Identified the missing spec equation lemma:
       let cbor_map_insert_cons_lt
         (kv': raw_data_item & raw_data_item)
         (q: list (raw_data_item & raw_data_item))
         (kv: raw_data_item & raw_data_item)
       : Lemma (ensures (
           CBOR.Spec.Raw.Map.map_entry_compare cbor_compare kv' kv < 0 ==>
             cbor_map_insert (kv' :: q) kv ==
               (match cbor_map_insert q kv with
                | None -> None
                | Some l' -> Some (kv' :: l'))))
       = ()
     This + a list cons-decomposition lemma
       let list_cons_hd_tl (#a:Type) (l:list a)
       : Lemma (requires (Cons? l))
               (ensures (l == List.Tot.hd l :: List.Tot.tl l))
       = ()
     are needed because the loop destructures l2 via Ghost.hide on
     List.Tot.hd / List.Tot.tl, and SMT does not auto-reduce
     map_insert (kv' :: q) kv without explicit syntactic cons.

   ✗ Even with the two lemmas in place, the loop invariant re-establishment
     after the c<0 branch hits z3rlimit ceilings: each verification query for
     this branch takes 130s+ and is killed at default rlimit 192. The proof
     state at this point carries ~10 facts about slice splits/joins
     (is_split predicates from S.split), the cbor_raw_map_insert_inv
     unfolding (which is a 5-clause conjunction including a 4-arm match),
     plus several Seq.append associativity/length facts. This causes Z3 to
     time out before reaching the core spec-equation proof.

   The remaining work to land this is purely **proof engineering**:
   factor the c<0 branch into a separate Pulse fn with its own pre/post,
   so the loop body's proof state is small. Estimate: 1-2 hour task.

   Once the cbor_raw_map_insert function lands in this module, the
   API-level cbor_det_serialize_map_insert wrapper in Det.Impl is ~5 lines:
       cbor_serialize_map_nil ();   // for the empty-list edge case
       SpecRaw.mk_det_raw_cbor_map_raw_snoc m key value;
       cbor_raw_map_insert
         out
         (SpecRaw.mk_det_raw_cbor_map_raw m)
         off2 (SpecRaw.mk_det_raw_cbor key)
         off3 (SpecRaw.mk_det_raw_cbor value) *)

module CBOR.SteelST
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

(* The C datatype for CBOR objects *)

noeq
type cbor_int = {
  cbor_int_type: Cbor.major_type_uint64_or_neg_int64;
  cbor_int_value: U64.t;
}

noeq
type cbor_string = {
  cbor_string_type: Cbor.major_type_byte_string_or_text_string;
  cbor_string_length: U64.t;
  cbor_string_payload: A.array U8.t;
}

val cbor_map_entry: Type0

val cbor: Type0

inline_for_extraction
noextract
val dummy_cbor : cbor

inline_for_extraction
noextract
val cbor_map_entry_key: cbor_map_entry -> cbor

inline_for_extraction
noextract
val cbor_map_entry_value: cbor_map_entry -> cbor

val cbor_map_entry_key_value_inj
  (m1 m2: cbor_map_entry)
: Lemma
  (requires (
    cbor_map_entry_key m1 == cbor_map_entry_key m2 /\
    cbor_map_entry_value m1 == cbor_map_entry_value m2
  ))
  (ensures (m1 == m2))
  [SMTPatOr [
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_value m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_value m2)];
  ]]

inline_for_extraction
noextract
val mk_cbor_map_entry
  (key: cbor)
  (value: cbor)
: Pure cbor_map_entry
  (requires True)
  (ensures (fun res ->
    cbor_map_entry_key res == key /\
    cbor_map_entry_value res == value
  ))

(* Relating a CBOR C object with a CBOR high-level value *)

noextract
let fstp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a1 = fst x

noextract
let sndp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a2 = snd x

[@@__reduce__]
let raw_data_item_map_entry_match1
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v1 }) -> vprop))
: Tot vprop
= raw_data_item_match (cbor_map_entry_key c1) (fstp v1) `star`
  raw_data_item_match (cbor_map_entry_value c1) (sndp v1)

val raw_data_item_match
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop

let raw_data_item_array_match
  (p: perm)
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= SM.seq_list_match c v (raw_data_item_match p)

[@@__reduce__]
let raw_data_item_map_entry_match
  (p: perm)
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
= raw_data_item_map_entry_match1 c1 v1 (raw_data_item_match p)

let raw_data_item_map_match
  (p: perm)
  (c: Seq.seq cbor_map_entry)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
  (decreases v)
= SM.seq_list_match c v (raw_data_item_map_entry_match p)

(* Parsing *)

noeq
type read_cbor_success_t = {
  read_cbor_payload: cbor;
  read_cbor_remainder: A.array U8.t;
  read_cbor_remainder_length: SZ.t;
}

noeq
type read_cbor_t =
| ParseError
| ParseSuccess of read_cbor_success_t

noextract
let read_cbor_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= SZ.v c.read_cbor_remainder_length == Seq.length rem /\
  va `Seq.equal` (Cbor.serialize_cbor v `Seq.append` rem)

[@@__reduce__]
let read_cbor_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match full_perm c.read_cbor_payload v `star`
    A.pts_to c.read_cbor_remainder p rem `star`
    ((raw_data_item_match full_perm c.read_cbor_payload v `star` A.pts_to c.read_cbor_remainder p rem) `implies_`
      A.pts_to a p va) `star`
    pure (read_cbor_success_postcond va c v rem)
  ))

noextract
let read_cbor_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . ~ (Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff)

[@@__reduce__]
let read_cbor_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a p va `star` pure (read_cbor_error_postcond va)

let read_cbor_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: read_cbor_t)
: Tot vprop
= match res with
  | ParseError -> read_cbor_error_post a p va
  | ParseSuccess c -> read_cbor_success_post a p va c

val read_cbor
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (a: A.array U8.t)
  (sz: SZ.t)
: ST read_cbor_t
    (A.pts_to a p va)
    (fun res -> read_cbor_post a p va res)
    (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    (fun _ -> True)

noextract
let read_deterministically_encoded_cbor_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= read_cbor_success_postcond va c v rem /\
  Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == true

[@@__reduce__]
let read_deterministically_encoded_cbor_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match full_perm c.read_cbor_payload v `star`
    A.pts_to c.read_cbor_remainder p rem `star`
    ((raw_data_item_match full_perm c.read_cbor_payload v `star` A.pts_to c.read_cbor_remainder p rem) `implies_`
      A.pts_to a p va) `star`
    pure (read_deterministically_encoded_cbor_success_postcond va c v rem)
  ))

noextract
let read_deterministically_encoded_cbor_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff ==> Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == false

[@@__reduce__]
let read_deterministically_encoded_cbor_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a p va `star` pure (read_deterministically_encoded_cbor_error_postcond va)

let read_deterministically_encoded_cbor_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: read_cbor_t)
: Tot vprop
= match res with
  | ParseError -> read_deterministically_encoded_cbor_error_post a p va
  | ParseSuccess c -> read_deterministically_encoded_cbor_success_post a p va c

val read_deterministically_encoded_cbor
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (a: A.array U8.t)
  (sz: SZ.t)
: ST read_cbor_t
    (A.pts_to a p va)
    (fun res -> read_deterministically_encoded_cbor_post a p va res)
    (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    (fun _ -> True)

(* Destructors and constructors *)

val destr_cbor_int64
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_int
    (raw_data_item_match p c (Ghost.reveal va))
    (fun _ -> raw_data_item_match p c (Ghost.reveal va))
    (Cbor.Int64? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Int64 c'.cbor_int_type c'.cbor_int_value
    )

val constr_cbor_int64
  (ty: Cbor.major_type_uint64_or_neg_int64)
  (value: U64.t)
: STT cbor
    emp
    (fun c -> raw_data_item_match full_perm c (Cbor.Int64 ty value))

val destr_cbor_simple_value
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST Cbor.simple_value
    (raw_data_item_match p c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match p c (Ghost.reveal va)
    )
    (Cbor.Simple? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Simple c'
    )

val constr_cbor_simple_value
  (value: Cbor.simple_value)
: STT cbor
    emp
    (fun c -> raw_data_item_match full_perm c (Cbor.Simple value))

val destr_cbor_string
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {Cbor.String? va})
: STT cbor_string
    (raw_data_item_match p c (Ghost.reveal va))
    (fun c' -> exists_ (fun vc' -> exists_ (fun p' ->
      A.pts_to c'.cbor_string_payload p' vc' `star`
      (A.pts_to c'.cbor_string_payload p' vc' `implies_` raw_data_item_match p c (Ghost.reveal va)) `star`
      pure (
        U64.v c'.cbor_string_length == Seq.length vc' /\
        c'.cbor_string_type == Cbor.String?.typ va /\
        vc' == Cbor.String?.v va
    ))))

val constr_cbor_string
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (typ: Cbor.major_type_byte_string_or_text_string)
  (a: A.array U8.t)
  (len: U64.t {
    U64.v len == Seq.length va
  })
: STT cbor
    (A.pts_to a p va)
    (fun c' ->
      raw_data_item_match full_perm c' (Cbor.String typ va) `star`
      (raw_data_item_match full_perm c' (Cbor.String typ va) `implies_`
        A.pts_to a p va
      )
    )

val constr_cbor_array
  (#c': Ghost.erased (Seq.seq cbor))
  (#v': Ghost.erased (list Cbor.raw_data_item))
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: STT cbor
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match full_perm c' v')
    (fun res ->
      raw_data_item_match full_perm res (Cbor.Array v') `star`
      (raw_data_item_match full_perm res (Cbor.Array v') `implies_`
        (A.pts_to a full_perm c' `star`
          raw_data_item_array_match full_perm c' v')
      )
    )

[@@__reduce__]
let maybe_cbor_array
  (v: Cbor.raw_data_item)
: GTot (list Cbor.raw_data_item)
= match v with
  | Cbor.Array l -> l
  | _ -> []

val cbor_array_length
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST U64.t
    (raw_data_item_match p a v)
    (fun _ -> raw_data_item_match p a v)
    (Cbor.Array? v)
    (fun res ->
      Cbor.Array? v /\
      U64.v res == List.Tot.length (Cbor.Array?.v v)
    )

val cbor_array_index
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
  (i: SZ.t {
    Cbor.Array? v /\
    SZ.v i < List.Tot.length (Cbor.Array?.v v)
  })
: STT cbor
    (raw_data_item_match p a v)
    (fun a' ->
      raw_data_item_match p a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `star`
      (raw_data_item_match p a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `implies_`
        raw_data_item_match p a v)
    )

val cbor_array_iterator_t: Type0

val dummy_cbor_array_iterator: cbor_array_iterator_t

val cbor_array_iterator_match
  (p: perm)
  (i: cbor_array_iterator_t)
  (l: list Cbor.raw_data_item)
: Tot vprop

val cbor_array_iterator_init
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { Cbor.Array? v })
: STT cbor_array_iterator_t
    (raw_data_item_match p a v)
    (fun i ->
      cbor_array_iterator_match p i (Cbor.Array?.v v) `star`
      (cbor_array_iterator_match p i (Cbor.Array?.v v) `implies_`
        raw_data_item_match p a v)
    )

val cbor_array_iterator_is_done
  (#p: perm)
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (i: cbor_array_iterator_t)
: ST bool
    (cbor_array_iterator_match p i l)
    (fun _ -> cbor_array_iterator_match p i l)
    True
    (fun res -> res == Nil? l)

val cbor_array_iterator_next
  (#p: perm)
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (#i: Ghost.erased cbor_array_iterator_t)
  (pi: R.ref cbor_array_iterator_t { Cons? l })
: STT cbor
    (R.pts_to pi full_perm i `star` cbor_array_iterator_match p i l)
    (fun c -> exists_ (fun i' ->
      R.pts_to pi full_perm i' `star`
      raw_data_item_match p c (List.Tot.hd l) `star`
      cbor_array_iterator_match p i' (List.Tot.tl l) `star`
      ((raw_data_item_match p c (List.Tot.hd l) `star`
        cbor_array_iterator_match p i' (List.Tot.tl l)) `implies_`
        cbor_array_iterator_match p i l
      )
    ))

val read_cbor_array
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
  (#vdest: Ghost.erased (Seq.seq cbor))
  (dest: A.array cbor) // it is the user's responsibility to allocate the array properly
  (len: U64.t)
: ST (A.array cbor)
    (raw_data_item_match p a v `star`
      A.pts_to dest full_perm vdest
    )
    (fun res -> exists_ (fun vres ->
      A.pts_to res p vres `star`
      raw_data_item_array_match p vres (maybe_cbor_array v) `star`
      ((A.pts_to res p vres `star`
        raw_data_item_array_match p vres (maybe_cbor_array v)) `implies_` (
        raw_data_item_match p a v `star`
        (exists_ (A.pts_to dest full_perm))
      ))
    ))
    (Cbor.Array? v /\
      (U64.v len == A.length dest \/ U64.v len == Seq.length vdest) /\
      U64.v len == List.Tot.length (Cbor.Array?.v v)
    )
    (fun res ->
      Cbor.Array? v /\
      U64.v len == A.length dest /\
      U64.v len == A.length res
    )

[@@__reduce__]
let maybe_cbor_tagged_tag
  (v: Cbor.raw_data_item)
: GTot U64.t
= match v with
  | Cbor.Tagged t _ -> t
  | _ -> 0uL // dummy

let dummy_raw_data_item : Ghost.erased Cbor.raw_data_item =
  Cbor.Int64 Cbor.major_type_uint64 0uL

[@@__reduce__]
let maybe_cbor_tagged_payload
  (v: Cbor.raw_data_item)
: GTot Cbor.raw_data_item
= match v with
  | Cbor.Tagged _ l -> l
  | _ -> dummy_raw_data_item

noeq
type cbor_tagged = {
  cbor_tagged_tag: U64.t;
  cbor_tagged_payload: cbor;
}

val destr_cbor_tagged
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_tagged
    (raw_data_item_match p a v)
    (fun res ->
      raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v) `star`
      (raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v) `implies_`
        raw_data_item_match p a v
      )
    )
    (Cbor.Tagged? v)
    (fun res ->
      Cbor.Tagged? v /\
      res.cbor_tagged_tag == Cbor.Tagged?.tag v
    )

val constr_cbor_tagged
  (#c': Ghost.erased (cbor))
  (#v': Ghost.erased (Cbor.raw_data_item))
  (tag: U64.t)
  (a: R.ref cbor)
: STT cbor
    (R.pts_to a full_perm c' `star`
      raw_data_item_match full_perm c' v')
    (fun res ->
      raw_data_item_match full_perm res (Cbor.Tagged tag v') `star`
      (raw_data_item_match full_perm res (Cbor.Tagged tag v') `implies_`
        (R.pts_to a full_perm c' `star`
          raw_data_item_match full_perm c' v')
      )
    )

val constr_cbor_map
  (#c': Ghost.erased (Seq.seq cbor_map_entry))
  (#v': Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (a: A.array cbor_map_entry)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: STT cbor
    (A.pts_to a full_perm c' `star`
      raw_data_item_map_match full_perm c' v')
    (fun res ->
      raw_data_item_match full_perm res (Cbor.Map v') `star`
      (raw_data_item_match full_perm res (Cbor.Map v') `implies_`
        (A.pts_to a full_perm c' `star`
          raw_data_item_map_match full_perm c' v')
      )
    )

val cbor_map_length
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST U64.t
    (raw_data_item_match p a v)
    (fun _ -> raw_data_item_match p a v)
    (Cbor.Map? v)
    (fun res ->
      Cbor.Map? v /\
      U64.v res == List.Tot.length (Cbor.Map?.v v)
    )

val cbor_map_iterator_t: Type0

val dummy_cbor_map_iterator: cbor_map_iterator_t

val cbor_map_iterator_match
  (p: perm)
  (i: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop

val cbor_map_iterator_init
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { Cbor.Map? v })
: STT cbor_map_iterator_t
    (raw_data_item_match p a v)
    (fun i ->
      cbor_map_iterator_match p i (Cbor.Map?.v v) `star`
      (cbor_map_iterator_match p i (Cbor.Map?.v v) `implies_`
        raw_data_item_match p a v)
    )

val cbor_map_iterator_is_done
  (#p: perm)
  (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (i: cbor_map_iterator_t)
: ST bool
    (cbor_map_iterator_match p i l)
    (fun _ -> cbor_map_iterator_match p i l)
    True
    (fun res -> res == Nil? l)

val cbor_map_iterator_next
  (#p: perm)
  (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (#i: Ghost.erased cbor_map_iterator_t)
  (pi: R.ref cbor_map_iterator_t { Cons? l })
: STT cbor_map_entry
    (R.pts_to pi full_perm i `star` cbor_map_iterator_match p i l)
    (fun c -> exists_ (fun i' ->
      R.pts_to pi full_perm i' `star`
      raw_data_item_map_entry_match p c (List.Tot.hd l) `star`
      cbor_map_iterator_match p i' (List.Tot.tl l) `star`
      ((raw_data_item_map_entry_match p c (List.Tot.hd l) `star`
        cbor_map_iterator_match p i' (List.Tot.tl l)) `implies_`
        cbor_map_iterator_match p i l
      )
    ))

val cbor_get_major_type
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST Cbor.major_type_t
    (raw_data_item_match p a v)
    (fun _ -> raw_data_item_match p a v)
    True
    (fun res -> res == Cbor.get_major_type v)

val cbor_is_equal
  (#p1: perm)
  (#v1: Ghost.erased Cbor.raw_data_item)
  (a1: cbor)
  (#p2: perm)
  (#v2: Ghost.erased Cbor.raw_data_item)
  (a2: cbor)
: ST bool
    (raw_data_item_match p1 a1 v1 `star` raw_data_item_match p2 a2 v2)
    (fun _ -> raw_data_item_match p1 a1 v1 `star` raw_data_item_match p2 a2 v2)
    True
    (fun res -> (~ (Cbor.Tagged? v1 \/ Cbor.Array? v1 \/ Cbor.Map? v1)) ==> (res == true <==> v1 == v2)) // TODO: underspecified for tagged, arrays and maps, complete those missing cases

noeq
type cbor_map_get_t =
| Found of cbor
| NotFound

[@@__reduce__]
let cbor_map_get_post_not_found
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item { Cbor.Map? vmap })
  (map: cbor)
: Tot vprop
= raw_data_item_match p map vmap `star` pure (Cbor.list_ghost_assoc vkey (Cbor.Map?.v vmap) == None)

[@@__reduce__]
let cbor_map_get_post_found
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item { Cbor.Map? vmap })
  (map: cbor)
  (value: cbor)
: Tot vprop
= exists_ (fun vvalue ->
    raw_data_item_match p value vvalue `star`
    (raw_data_item_match p value vvalue `implies_` raw_data_item_match p map vmap) `star`
    pure (Cbor.list_ghost_assoc vkey (Cbor.Map?.v vmap) == Some vvalue)
  )

let cbor_map_get_post
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor { Cbor.Map? vmap })
  (res: cbor_map_get_t)
: Tot vprop
= match res with
  | NotFound -> cbor_map_get_post_not_found p vkey vmap map
  | Found value -> cbor_map_get_post_found p vkey vmap map value

val cbor_map_get
  (#pkey: perm)
  (#vkey: Ghost.erased Cbor.raw_data_item)
  (key: cbor)
  (#pmap: perm)
  (#vmap: Ghost.erased Cbor.raw_data_item)
  (map: cbor { Cbor.Map? vmap })
: ST cbor_map_get_t
    (raw_data_item_match pkey key vkey `star` raw_data_item_match pmap map vmap)
    (fun res -> raw_data_item_match pkey key vkey `star` cbor_map_get_post pmap vkey vmap map res)
    (~ (Cbor.Tagged? vkey \/ Cbor.Array? vkey \/ Cbor.Map? vkey))
    (fun res -> Found? res == Some? (Cbor.list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap)))

(* Serialization *)

noextract
let write_cbor_postcond
  (va: Cbor.raw_data_item)
  (out: A.array U8.t)
  (vout': Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
= let s = Cbor.serialize_cbor va in
  Seq.length vout' == A.length out /\
  (res = 0sz <==> Seq.length s > Seq.length vout') /\
  (res <> 0sz ==> (
    SZ.v res == Seq.length s /\
    Seq.slice vout' 0 (Seq.length s) `Seq.equal` s
  ))

[@@__reduce__]
let write_cbor_post
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (res: SZ.t)
  (vout': Seq.seq U8.t)
: Tot vprop
= 
  A.pts_to out full_perm vout' `star`
  pure (write_cbor_postcond va out vout' res)

val write_cbor
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (#vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (sz: SZ.t)
: ST SZ.t
    (raw_data_item_match p c (Ghost.reveal va) `star`
      A.pts_to out full_perm vout
    )
    (fun res -> 
      raw_data_item_match p c (Ghost.reveal va) `star`
      exists_ (write_cbor_post va c vout out res)
    )
    (SZ.v sz == A.length out)
    (fun _ -> True)

val cbor_gather
  (#opened: _)
  (c: cbor)
  (v1 v2: Cbor.raw_data_item)
  (p1 p2: perm)
: STGhost unit opened
    (raw_data_item_match p1 c v1 `star` raw_data_item_match p2 c v2)
    (fun _ -> raw_data_item_match (p1 `sum_perm` p2) c v1)
    True
    (fun _ -> v1 == v2)

val cbor_share
  (#opened: _)
  (c: cbor)
  (v1: Cbor.raw_data_item)
  (p p1 p2: perm)
: STGhost unit opened
    (raw_data_item_match p c v1)
    (fun _ -> raw_data_item_match p1 c v1 `star` raw_data_item_match p2 c v1)
    (p == p1 `sum_perm` p2)
    (fun _ -> True)

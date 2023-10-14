module CBOR.SteelST
open Steel.ST.OnRange
open Steel.ST.GenElim

module Cbor = CBOR.SteelST.Raw
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module R = Steel.ST.Reference
module A = Steel.ST.Array
module LW = LowParse.SteelST.L2ROutput.IntroElim

noeq
type cbor_int = {
  typ: Cbor.major_type_uint64_or_neg_int64;
  value: U64.t;
}

noeq
type cbor_string = {
  typ: Cbor.major_type_byte_string_or_text_string;
  byte_length: U64.t;
  payload: A.array U8.t;
  permission: perm;
}

noeq
type cbor_serialized = {
  byte_size: SZ.t;
  payload: LPS.byte_array;
  footprint: LPA.array LPS.byte; // ghost
}

noeq
type cbor_tagged = {
  tag: U64.t;
  payload: R.ref cbor;
  footprint: Ghost.erased cbor;
}

and cbor_array = {
  count: U64.t;
  payload: A.array cbor;
  footprint: Ghost.erased (Seq.seq cbor);
}

and cbor_map_entry = {
  key: cbor;
  value: cbor;
}

and cbor_map = {
  entry_count: U64.t;
  payload: A.array cbor_map_entry;
  footprint: Ghost.erased (Seq.seq cbor_map_entry);
}

and cbor =
| CBOR_Case_Int64 of cbor_int
| CBOR_Case_String of cbor_string
| CBOR_Case_Tagged of cbor_tagged
| CBOR_Case_Array of cbor_array
| CBOR_Case_Map of cbor_map
| CBOR_Case_Simple_value of Cbor.simple_value
| CBOR_Case_Serialized of cbor_serialized

let dummy_cbor : cbor = CBOR_Case_Simple_value 0uy

let raw_data_item_match_serialized_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: LPS.byte_array)
  (w: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Serialized c ->
    c.byte_size == LPA.len (LPS.array_of w) /\
    c.payload == a /\
    c.footprint == LPS.array_of w /\
    w.LPS.contents == v
  | _ -> False

[@@__reduce__]
let raw_data_item_match_serialized0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun (a: LPS.byte_array) -> exists_ (fun (w: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item) ->
    LPS.aparse Cbor.parse_raw_data_item a w `star`
    pure (
      raw_data_item_match_serialized_prop c v a w
    )
  ))

let raw_data_item_match_simple_value_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Simple_value c -> v == Cbor.Simple c
  | _ -> False

[@@__reduce__]
let raw_data_item_match_simple_value0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= pure (raw_data_item_match_simple_value_prop c v)

let raw_data_item_match_int_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Int64 c -> v == Cbor.Int64 c.typ c.value
  | _ -> False

[@@__reduce__]
let raw_data_item_match_int0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= pure (raw_data_item_match_int_prop c v)

let raw_data_item_match_string_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: A.array U8.t)
  (p: perm)
  (w: Seq.seq U8.t)
: Tot prop
= match c with
  | CBOR_Case_String c ->
    U64.v c.byte_length == Seq.length w /\
    v == Cbor.String c.typ w /\
    c.permission == p /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_string0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun a -> exists_ (fun p -> exists_ (fun w ->
    A.pts_to a p w `star`
    pure (raw_data_item_match_string_prop c v a p w)
  )))

unfold
let raw_data_item_match_tagged_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: R.ref cbor)
  (c': cbor)
  (v': Cbor.raw_data_item)
: Tot prop
= match v, c with
  | Cbor.Tagged tag v2, CBOR_Case_Tagged c ->
    c.tag == tag /\
    Ghost.reveal c.footprint == c' /\
    v2 == v' /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_tagged0
  (c: cbor)
  (v: Cbor.raw_data_item)
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun a -> exists_ (fun c' -> exists_ (fun v' ->
    R.pts_to a full_perm c' `star`
    raw_data_item_match c' v' `star`
    pure (raw_data_item_match_tagged_prop c v a c' v')
  )))

let raw_data_item_match_array_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (s: Seq.seq cbor)
  (a: A.array cbor)
: GTot prop
= match c, v with
  | CBOR_Case_Array c, Cbor.Array l ->
    U64.v c.count == List.Tot.length l /\
    Ghost.reveal c.footprint == s /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_array0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Array? v })
  (raw_data_item_array_match: (Seq.seq cbor -> (v': list Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: A.array cbor) -> exists_ (fun (c': Seq.seq cbor) ->
    A.pts_to a full_perm c' `star`
    raw_data_item_array_match c' (Cbor.Array?.v v) `star`
    pure (
      raw_data_item_match_array_prop c v c' a
    )
  ))

let raw_data_item_match_map_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: A.array cbor_map_entry)
  (s: Seq.seq cbor_map_entry)
: GTot prop
= match c, v with
  | CBOR_Case_Map c, Cbor.Map l ->
    U64.v c.entry_count == List.Tot.length l /\
    Ghost.reveal c.footprint == s /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_map0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Map? v })
  (raw_data_item_map_match: (Seq.seq cbor_map_entry -> (v': list (Cbor.raw_data_item & Cbor.raw_data_item) { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: A.array cbor_map_entry) -> exists_ (fun (c': Seq.seq cbor_map_entry) ->
    A.pts_to a full_perm c' `star`
    raw_data_item_map_match c' (Cbor.Map?.v v) `star`
    pure (
      raw_data_item_match_map_prop c v a c'
    )
  ))

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
= raw_data_item_match c1.key (fstp v1) `star`
  raw_data_item_match c1.value (sndp v1)

[@@__reduce__]
let raw_data_item_map_entry_match0
  (raw_data_item_match: (cbor -> Cbor.raw_data_item -> vprop))
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
= raw_data_item_map_entry_match1 c1 v1 raw_data_item_match

let raw_data_item_map_entry_match
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << l }) -> vprop))
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item) { v1 << l })
: Tot vprop
= raw_data_item_map_entry_match1 c1 v1 raw_data_item_match

let rec raw_data_item_match
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= match c, v with
  | CBOR_Case_Serialized _, _ -> raw_data_item_match_serialized0 c v
  | CBOR_Case_Simple_value _, Cbor.Simple _ -> raw_data_item_match_simple_value0 c v
  | CBOR_Case_Int64 _, Cbor.Int64 _ _ -> raw_data_item_match_int0 c v
  | CBOR_Case_String _, Cbor.String _ _ -> raw_data_item_match_string0 c v
  | CBOR_Case_Array _, Cbor.Array _ -> raw_data_item_match_array0 c v raw_data_item_array_match
  | CBOR_Case_Map _, Cbor.Map _ -> raw_data_item_match_map0 c v raw_data_item_map_match
  | CBOR_Case_Tagged _, Cbor.Tagged _ _ -> raw_data_item_match_tagged0 c v raw_data_item_match
  | _ -> pure False

and raw_data_item_array_match
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= LPS.seq_list_match c v raw_data_item_match

and raw_data_item_map_match
  (c: Seq.seq cbor_map_entry)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
  (decreases v)
= LPS.seq_list_match c v (raw_data_item_map_entry_match v raw_data_item_match)

#set-options "--ide_id_info_off"

let raw_data_item_match_get_case
  (#opened: _)
  (#v: Cbor.raw_data_item)
  (c: cbor)
: STGhost unit opened
    (raw_data_item_match c v)
    (fun _ -> raw_data_item_match c v)
    True
    (fun _ -> match c, v with
    | CBOR_Case_Serialized _, _
    | CBOR_Case_Array _, Cbor.Array _
    | CBOR_Case_Int64 _, Cbor.Int64 _ _
    | CBOR_Case_Map _, Cbor.Map _
    | CBOR_Case_Simple_value _, Cbor.Simple _
    | CBOR_Case_String _, Cbor.String _ _
    | CBOR_Case_Tagged _, Cbor.Tagged _ _
      -> True
    | _ -> False
    )
= match c, v with
    | CBOR_Case_Serialized _, _
    | CBOR_Case_Array _, Cbor.Array _
    | CBOR_Case_Int64 _, Cbor.Int64 _ _
    | CBOR_Case_Map _, Cbor.Map _
    | CBOR_Case_Simple_value _, Cbor.Simple _
    | CBOR_Case_String _, Cbor.String _ _
    | CBOR_Case_Tagged _, Cbor.Tagged _ _
      -> noop ()
    | _ ->
      rewrite (raw_data_item_match c v) (pure False);
      let _ = gen_elim () in
      rewrite emp (raw_data_item_match c v)

let dummy_raw_data_item : Ghost.erased Cbor.raw_data_item =
  Cbor.Int64 Cbor.major_type_uint64 0uL

let raw_data_item_match_array_intro
  (#opened: _)
  (#c': Seq.seq cbor)
  (#v': list Cbor.raw_data_item)
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: STGhostT unit opened
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v')
    (fun _ ->
      raw_data_item_match
        (CBOR_Case_Array ({
          count = len;
          payload = a;
          footprint = c';
        }))
        (Cbor.Array v')
    )
= noop ();
  rewrite_with_tactic
    (raw_data_item_match_array0
      (CBOR_Case_Array ({
        count = len;
        payload = a;
        footprint = c';
      }))
      (Cbor.Array v')
      raw_data_item_array_match
    )
    (raw_data_item_match _ _)

let raw_data_item_match_array_elim
  (#opened: _)
  (a: cbor_array)
  (v: Cbor.raw_data_item)
: STGhost (squash (Cbor.Array? v)) opened
    (raw_data_item_match (CBOR_Case_Array a) v)
    (fun _ ->
      A.pts_to a.payload full_perm a.footprint `star`
      raw_data_item_array_match a.footprint (Cbor.Array?.v v)
    )
    True
    (fun _ -> U64.v a.count == List.Tot.length (Cbor.Array?.v v))
= raw_data_item_match_get_case _;
  let sq : squash (Cbor.Array? v) = () in
  let Cbor.Array v' = v in
  vpattern_rewrite (raw_data_item_match _) (Cbor.Array v');
  rewrite_with_tactic
    (raw_data_item_match _ _)
    (raw_data_item_match_array0 (CBOR_Case_Array a) (Cbor.Array v') raw_data_item_array_match);
  let _ = gen_elim () in
  rewrite (A.pts_to _ _ _) (A.pts_to a.payload full_perm a.footprint);
  rewrite (raw_data_item_array_match _ _) (raw_data_item_array_match a.footprint (Cbor.Array?.v v));
  sq

let constr_cbor_array
  (#c': Ghost.erased (Seq.seq cbor))
  (#v': Ghost.erased (list Cbor.raw_data_item))
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: ST cbor
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v')
    (fun res ->
      raw_data_item_match res (Cbor.Array v') `star`
      (raw_data_item_match res (Cbor.Array v') `implies_`
        (A.pts_to a full_perm c' `star`
          raw_data_item_array_match c' v')
      )
    )
    True
    (fun res ->
      res == CBOR_Case_Array ({
        payload = a;
        count = len;
        footprint = c';
      })
    )
= [@@inline_let]
  let ares : cbor_array = {
    count = len;
    payload = a;
    footprint = c';
  }
  in
  [@@inline_let]
  let res = CBOR_Case_Array ares in
  raw_data_item_match_array_intro a len;
  rewrite (raw_data_item_match _ _) (raw_data_item_match res (Cbor.Array v'));
  intro_implies
    (raw_data_item_match res (Cbor.Array v'))
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v'
    )
    emp
    (fun _ ->
      rewrite (raw_data_item_match _ _) (raw_data_item_match (CBOR_Case_Array ares) (Cbor.Array v'));
      let _ = raw_data_item_match_array_elim _ _ in
      rewrite (A.pts_to _ _ _) (A.pts_to a full_perm c');
      rewrite (raw_data_item_array_match _ _) (raw_data_item_array_match c' v')
    );
  return res

[@@__reduce__]
let maybe_cbor_array
  (v: Cbor.raw_data_item)
: GTot (list Cbor.raw_data_item)
= match v with
  | Cbor.Array l -> l
  | _ -> []

let destr_cbor_array
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_array
    (raw_data_item_match a v)
    (fun res ->
      A.pts_to res.payload full_perm res.footprint `star`
      raw_data_item_array_match res.footprint (maybe_cbor_array v) `star`
      ((A.pts_to res.payload full_perm res.footprint `star`
        raw_data_item_array_match res.footprint (maybe_cbor_array v)) `implies_`
        raw_data_item_match a v
      )
    )
    (CBOR_Case_Array? a)
    (fun res ->
      a == CBOR_Case_Array res /\
      Cbor.Array? v /\
      U64.v res.count == List.Tot.length (Cbor.Array?.v v)
    )
= raw_data_item_match_get_case _;
  let CBOR_Case_Array res = a in
  vpattern_rewrite
    (fun a -> raw_data_item_match a _)
    (CBOR_Case_Array res);
  let _ = raw_data_item_match_array_elim _ _ in
  vpattern_rewrite (raw_data_item_array_match _) (maybe_cbor_array v);
  intro_implies
    (A.pts_to res.payload full_perm res.footprint `star`
      raw_data_item_array_match res.footprint (maybe_cbor_array v))
    (raw_data_item_match a v)
    emp
    (fun _ ->
      raw_data_item_match_array_intro _ res.count;
      rewrite (raw_data_item_match _ _) (raw_data_item_match _ _)
    );
  return res

let read_valid_cbor_from_buffer_with_size_strong
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
  (alen: SZ.t)
: ST cbor
    (LPS.aparse Cbor.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match c' va.contents `star`
      (raw_data_item_match c' va.contents `implies_` LPS.aparse Cbor.parse_raw_data_item a va)
    )
    (alen == LPA.len (LPS.array_of va))
    (fun c' -> CBOR_Case_Serialized? c')
= [@@inline_let]
  let c_pl : cbor_serialized = ({
    byte_size = alen;
    payload = a;
    footprint = LPS.array_of va;
  })
  in
  [@@inline_let]
  let c' = CBOR_Case_Serialized c_pl in
  noop ();
  rewrite_with_implies
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c_pl) va.contents)
    (raw_data_item_match c' va.contents);
  intro_implies
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c_pl) va.contents)
    (LPS.aparse Cbor.parse_raw_data_item a va)
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite (LPS.aparse Cbor.parse_raw_data_item _ _) (LPS.aparse Cbor.parse_raw_data_item a va) // works thanks to c_pl.footprint
    );
  implies_trans
    (raw_data_item_match c' va.contents)
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c_pl) va.contents)
    (LPS.aparse Cbor.parse_raw_data_item a va);
  return c'

let read_valid_cbor_from_buffer_with_size
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
  (alen: SZ.t)
: ST cbor
    (LPS.aparse Cbor.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match c' va.contents
    )
    (alen == LPA.len (LPS.array_of va))
    (fun c' -> CBOR_Case_Serialized? c')
= let c' = read_valid_cbor_from_buffer_with_size_strong a alen in
  drop (_ `implies_` _);
  return c'

let read_valid_cbor_from_buffer
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
: STT cbor
    (LPS.aparse Cbor.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match c' va.contents
    )
= let alen = LPS.get_parsed_size Cbor.jump_raw_data_item a in
  read_valid_cbor_from_buffer_with_size a alen

let destr_cbor_serialized
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_serialized
    (raw_data_item_match c va)
    (fun c' -> exists_ (fun vc ->
      LPS.aparse Cbor.parse_raw_data_item c'.payload vc `star`
      (LPS.aparse Cbor.parse_raw_data_item c'.payload vc `implies_`
        raw_data_item_match c va
      ) `star`
      pure (
        vc.LPS.contents == Ghost.reveal va /\
        LPA.length (LPS.array_of vc) == SZ.v c'.byte_size
    )))
    (CBOR_Case_Serialized? c)
    (fun _ -> True)
= let CBOR_Case_Serialized c' = c in
  rewrite_with_implies
    (raw_data_item_match c va)
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c') va);
  let _ = gen_elim () in
  let vc = vpattern_replace (LPS.aparse Cbor.parse_raw_data_item _) in
  vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) c'.payload;
  intro_implies
    (LPS.aparse Cbor.parse_raw_data_item c'.payload vc)
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c') va)
    emp
    (fun _ ->
      noop (); noop () // FIXME: WHY WHY WHY do I need an explicit bind here?
    );
  implies_trans
    (LPS.aparse Cbor.parse_raw_data_item c'.payload vc)
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c') va)
    (raw_data_item_match c va);
  return c'

inline_for_extraction
noextract
let cbor_size_comp_for
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: Tot Type
= (sz: SZ.t) ->
  (perr: R.ref bool) ->
  STT SZ.t
    (raw_data_item_match c (Ghost.reveal va) `star`
      R.pts_to perr full_perm false
    )
    (fun res ->
      raw_data_item_match c (Ghost.reveal va) `star`
      exists_ (fun err ->
        R.pts_to perr full_perm err `star`
        pure (LowParse.SteelST.Write.size_comp_for_post Cbor.serialize_raw_data_item va sz res err)
    ))

noextract
unfold
let l2r_write_cbor_post
  (va: Ghost.erased Cbor.raw_data_item)
  (vout: LPA.array LPS.byte)
  (vres: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (vout': LPA.array LPS.byte)
: Tot prop
=  
       LPA.merge_into (LPS.array_of vres) vout' vout /\
       vres.LPS.contents == Ghost.reveal va

[@@__reduce__]
let cbor_l2r_writer_for_post
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (vout: LPA.array LPS.byte)
  (out: LW.t)
  (res: LPS.byte_array)
  (vres: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (vout': LPA.array LPS.byte)
: Tot vprop
=
  raw_data_item_match c (Ghost.reveal va) `star`
  LPS.aparse Cbor.parse_raw_data_item res vres `star`
  LW.vp out vout' `star`
  pure (
    l2r_write_cbor_post va vout vres vout'
  )

inline_for_extraction
noextract
let cbor_l2r_writer_for
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: Tot Type
= (#vout: LPA.array LPS.byte) ->
  (out: LW.t) ->
  ST LPS.byte_array
    (raw_data_item_match c (Ghost.reveal va) `star`
      LW.vp out vout
    )
    (fun res -> exists_ (fun (vres: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item) -> exists_ (fun (vout': LPA.array LPS.byte) ->
      cbor_l2r_writer_for_post va c vout out res vres vout'
    )))
    (Seq.length (LPS.serialize Cbor.serialize_raw_data_item va) <= LPA.length vout)
    (fun _ -> True)

let size_comp_for_serialized
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Serialized? c})
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let c' = destr_cbor_serialized c in
    let _ = gen_elim () in
    LPS.aparse_serialized_length Cbor.serialize_raw_data_item _;
    elim_implies
      (LPS.aparse Cbor.parse_raw_data_item _ _)
      (raw_data_item_match _ _);
    if c'.byte_size `SZ.gt` sz
    then begin
      noop ();
      R.write perr true;
      return sz
    end else begin
      [@@inline_let]
      let res = sz `SZ.sub` c'.byte_size in
      noop ();
      return res
    end

let l2r_writer_for_serialized
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Serialized? c})
: Tot (cbor_l2r_writer_for va c)
= fun #vout out ->
    let c' = destr_cbor_serialized c in
    let _ = gen_elim () in
    LPS.aparse_serialized_length Cbor.serialize_raw_data_item _;
    let _ = LPS.elim_aparse_with_implies Cbor.parse_raw_data_item c'.payload in
    implies_trans
      (LPA.arrayptr c'.payload _)
      (LPS.aparse Cbor.parse_raw_data_item _ _)
      (raw_data_item_match _ _);
    let res = LW.split out c'.byte_size in
    let _ = gen_elim () in
    let vout' = vpattern_replace (LW.vp out) in
    let _ = LPA.copy c'.payload res c'.byte_size in
    let vres = LPS.intro_aparse Cbor.parse_raw_data_item res in
    elim_implies
      (LPA.arrayptr c'.payload _)
      (raw_data_item_match _ _);
    assert_ (cbor_l2r_writer_for_post va c vout out res vres vout'); // FIXME: WHY WHY WHY?
    return res

let read_cbor_int64
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_int
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> raw_data_item_match c (Ghost.reveal va))
    (Cbor.Int64? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Int64 c'.typ c'.value
    )
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 c' ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_int0 c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_int0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) cs.payload;
    let typ = Cbor.read_major_type cs.payload in
    let value = Cbor.read_int64 cs.payload in
    let c' : cbor_int = {
      typ = typ;
      value = value;
    }
    in
    noop ();
    elim_implies
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'

let destr_cbor_int64
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_int
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va) `star`
      (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va) `implies_` raw_data_item_match c (Ghost.reveal va))
    )
    (Cbor.Int64? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Int64 c'.typ c'.value
    )
= let c' = read_cbor_int64 c in
  rewrite
    (raw_data_item_match_int0 (CBOR_Case_Int64 c') (Ghost.reveal va))
    (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va));
  intro_implies
    (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> drop (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va)));
  return c'

let size_comp_for_int64
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Int64? va })
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let c' = read_cbor_int64 c in
    let res = CBOR.SteelST.Raw.Write.size_comp_int64 c'.typ c'.value sz perr in
    let _ = gen_elim () in
    return res

let l2r_writer_for_int64
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Int64? va })
: Tot (cbor_l2r_writer_for va c)
= fun out ->
    let c' = read_cbor_int64 c in
    let res = CBOR.SteelST.Raw.Write.l2r_write_int64 c'.typ c'.value out in
    let _ = gen_elim () in
    return res

let constr_cbor_int64
  (ty: Cbor.major_type_uint64_or_neg_int64)
  (value: U64.t)
: ST cbor
    emp
    (fun c -> raw_data_item_match c (Cbor.Int64 ty value))
    True
    (fun c -> c == CBOR_Case_Int64 ({ typ = ty; value = value }))
= [@@inline_let]
  let c = CBOR_Case_Int64 ({ typ = ty; value = value }) in
  noop ();
  rewrite
    (raw_data_item_match_int0 c (Cbor.Int64 ty value))
    (raw_data_item_match c (Cbor.Int64 ty value));
  return c

let read_cbor_simple_value
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST Cbor.simple_value
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match c (Ghost.reveal va)
    )
    (Cbor.Simple? (Ghost.reveal va))
    (fun c' -> Ghost.reveal va == Cbor.Simple c')
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Simple_value c' ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_simple_value0 c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_simple_value0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) cs.payload;
    let c' = Cbor.read_simple_value cs.payload in
    elim_implies
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'

let destr_cbor_simple_value
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST Cbor.simple_value
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va) `star`
      (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va) `implies_` raw_data_item_match c (Ghost.reveal va))
    )
    (Cbor.Simple? (Ghost.reveal va))
    (fun c' -> Ghost.reveal va == Cbor.Simple c')
= let c' = read_cbor_simple_value c in
  rewrite
    (raw_data_item_match_simple_value0 (CBOR_Case_Simple_value c') (Ghost.reveal va))
    (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va));
  intro_implies
    (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> drop (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va)));
  return c'

let size_comp_for_simple_value
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Simple? va })
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let c' = read_cbor_simple_value c in
    let res = CBOR.SteelST.Raw.Write.size_comp_simple_value c' sz perr in
    let _ = gen_elim () in
    return res

let l2r_writer_for_simple_value
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.Simple? va })
: Tot (cbor_l2r_writer_for va c)
= fun out ->
    let c' = read_cbor_simple_value c in
    let res = CBOR.SteelST.Raw.Write.l2r_write_simple_value c' out in
    let _ = gen_elim () in
    return res

let constr_cbor_simple_value
  (value: Cbor.simple_value)
: ST cbor
    emp
    (fun c -> raw_data_item_match c (Cbor.Simple value))
    True
    (fun c -> c == CBOR_Case_Simple_value value)
= [@@inline_let]
  let c = CBOR_Case_Simple_value value in
  noop ();
  rewrite
    (raw_data_item_match_simple_value0 c (Cbor.Simple value))
    (raw_data_item_match c (Cbor.Simple value));
  return c

let destr_cbor_string'
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_string
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va) `star`
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va) `implies_` raw_data_item_match c (Ghost.reveal va))
    )
    (Cbor.String? (Ghost.reveal va))
    (fun _ -> True)
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_String c' ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) cs.payload;
    let va' = vpattern_replace (LPS.aparse Cbor.parse_raw_data_item _) in
    let typ = Cbor.read_major_type cs.payload in
    let len = Cbor.read_argument_as_uint64 cs.payload in
    let lpayload = Cbor.focus_string cs.payload in
    let _ = gen_elim () in
    let payload = LPA.elim_arrayptr_with_implies lpayload in
    let _ = gen_elim () in
    implies_trans
      (A.pts_to _ _ _)
      (LPA.arrayptr _ _)
      (LPS.aparse Cbor.parse_raw_data_item _ _);
    let vpl = vpattern_replace_erased (fun vpl -> A.pts_to payload _ vpl `star` (A.pts_to payload _ vpl `implies_` LPS.aparse Cbor.parse_raw_data_item cs.payload va')) in
    let vperm = vpattern_replace (fun vperm -> A.pts_to payload vperm _ `star` (A.pts_to payload vperm _ `implies_` LPS.aparse Cbor.parse_raw_data_item cs.payload va')) in
    let c' : cbor_string = {
      typ = typ;
      byte_length = len;
      payload = payload;
      permission = vperm;
    }
    in
    noop ();
    intro_implies
      (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (A.pts_to payload vperm vpl `implies_` LPS.aparse Cbor.parse_raw_data_item cs.payload va')
      (fun _ ->
        let _ = gen_elim () in
        rewrite (A.pts_to _ _ _) (A.pts_to payload vperm vpl);
        elim_implies
          (A.pts_to payload vperm vpl)
          (LPS.aparse Cbor.parse_raw_data_item cs.payload va');
        noop ()
      );
    rewrite_with_implies
      (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va));
    implies_trans
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    implies_trans
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'

let destr_cbor_string
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {Cbor.String? va})
: STT cbor_string
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' -> exists_ (fun vc' ->
      A.pts_to c'.payload c'.permission vc' `star`
      (A.pts_to c'.payload c'.permission vc' `implies_` raw_data_item_match c (Ghost.reveal va)) `star`
      pure (
        U64.v c'.byte_length == Seq.length vc' /\
        c'.typ == Cbor.String?.typ va /\
        vc' == Cbor.String?.v va
    )))
= let c' = destr_cbor_string' c in
  rewrite_with_implies
    (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
    (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va));
  let _ = gen_elim () in
  vpattern_rewrite (fun a -> A.pts_to a _ _) c'.payload;
  vpattern_rewrite (fun p -> A.pts_to _ p _) c'.permission;
  let vc' = vpattern_replace_erased (A.pts_to _ _) in
  intro_implies
    (A.pts_to c'.payload c'.permission vc')
    (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
    (pure (raw_data_item_match_string_prop (CBOR_Case_String c') (Ghost.reveal va) c'.payload c'.permission vc')) // FIXME: WHY WHY WHY?
    (fun _ ->
      noop ()
    );
  implies_trans
    (A.pts_to c'.payload c'.permission vc')
    (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
    (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va));
  implies_trans
    (A.pts_to c'.payload c'.permission vc')
    (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va));
  intro_exists (Ghost.reveal vc') (fun vc' -> // FIXME: WHY WHY WHY?
    A.pts_to c'.payload c'.permission vc' `star`
      (A.pts_to c'.payload c'.permission vc' `implies_` raw_data_item_match c (Ghost.reveal va)) `star`
      pure (
        U64.v c'.byte_length == Seq.length vc' /\
        c'.typ == Cbor.String?.typ va /\
        vc' == Cbor.String?.v va
    )  
  );
  return c'

#push-options "--z3rlimit 64"
#restart-solver

let size_comp_for_string
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor { Cbor.String? va })
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let _ = A.intro_fits_u64 () in
    let c' = destr_cbor_string c in
    let _ = gen_elim () in
    let res = CBOR.SteelST.Raw.Write.size_comp_string c'.typ c'.byte_length (Cbor.String?.v va) sz perr in
    let _ = gen_elim () in
    elim_implies
      (A.pts_to _ _ _)
      (raw_data_item_match _ _);
    return res

let serialize_cbor_string_eq
  (c: Cbor.raw_data_item { Cbor.String? c })
: Lemma
  (
    let s0 = LPS.serialize Cbor.serialize_raw_data_item c in
    let s1 = LPS.serialize Cbor.serialize_header (Cbor.uint64_as_argument (Cbor.String?.typ c) (U64.uint_to_t (Seq.length (Cbor.String?.v c)))) in
    s0 == s1 `Seq.append` Cbor.String?.v c
  )
= Cbor.serialize_raw_data_item_aux_correct c;
  LPS.serialize_synth_eq
    _
    Cbor.synth_raw_data_item
    (LPS.serialize_dtuple2 Cbor.serialize_header Cbor.serialize_content)
    Cbor.synth_raw_data_item_recip
    ()
    c;
  LPS.serialize_dtuple2_eq Cbor.serialize_header Cbor.serialize_content (Cbor.synth_raw_data_item_recip c)

let l2r_write_cbor_string
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {Cbor.String? va})
: Tot (cbor_l2r_writer_for va c)
= fun #vout out ->
  let _ = A.intro_fits_u64 () in
  serialize_cbor_string_eq va;
  noop ();
  let c' = destr_cbor_string c in
  let _ = gen_elim () in
  let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header c'.typ c'.byte_length out in
  let _ = gen_elim () in
  let _ = LPS.elim_aparse_with_serializer Cbor.serialize_header res in
  let len = SZ.uint64_to_sizet c'.byte_length in
  let res_pl = LW.split out len in
  let _ = gen_elim () in
  let vout' = vpattern_replace (LW.vp out) in
  let vres_pl = vpattern (LPA.arrayptr res_pl) in
  let res_pl_a = LPA.elim_arrayptr res_pl in
  vpattern_rewrite (fun p -> A.pts_to res_pl_a p _) full_perm;
  A.pts_to_length c'.payload _;
  A.pts_to_length res_pl_a _;
  let _ = A.memcpy c'.payload res_pl_a len in
  let res_pl = LPA.intro_arrayptr res_pl_a in
  let _ = gen_elim () in
  let vres_pl' = vpattern (LPA.arrayptr res_pl) in
  LPA.array_equal (LPA.array_of vres_pl) (LPA.array_of vres_pl');
  noop ();
  let _ = LPA.join res res_pl in
  let vres = LPS.intro_aparse_with_serializer Cbor.serialize_raw_data_item va res in
  elim_implies
    (A.pts_to _ _ _)
    (raw_data_item_match c (Ghost.reveal va));
  assert_ (cbor_l2r_writer_for_post va c vout out res vres vout'); // FIXME: WHY WHY WHY?
  return res

#pop-options

let constr_cbor_string
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
      raw_data_item_match c' (Cbor.String typ va) `star`
      (raw_data_item_match c' (Cbor.String typ va) `implies_`
        A.pts_to a p va
      )
    )
= [@@inline_let]
  let c' = CBOR_Case_String ({
    typ = typ;
    payload = a;
    byte_length = len;
    permission = p;
  })
  in
  noop ();
  rewrite_with_implies
    (raw_data_item_match_string0 c' (Cbor.String typ va))
    (raw_data_item_match c' (Cbor.String typ va));
  intro_implies
    (raw_data_item_match_string0 c' (Cbor.String typ va))
    (A.pts_to a p va)
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite (A.pts_to _ _ _) (A.pts_to a p va)
    );
  implies_trans
    (raw_data_item_match c' (Cbor.String typ (va)))
    (raw_data_item_match_string0 c' (Cbor.String typ (va)))
    (A.pts_to a p va);
  return c'

inline_for_extraction
noextract
let read_cbor_array_payload
  (n0: U64.t)
  (vl0: LPS.v (LowParse.Spec.VCList.parse_nlist_kind (U64.v n0) Cbor.parse_raw_data_item_kind) (LowParse.Spec.VCList.nlist (U64.v n0) Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (#va0: Ghost.erased (Seq.seq cbor))
  (a0: A.array cbor)
: ST (Ghost.erased (Seq.seq cbor))
    (A.pts_to a0 full_perm va0 `star`
      LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0
    )
    (fun res ->
      A.pts_to a0 full_perm res `star`
      raw_data_item_array_match res vl0.contents `star`
      (raw_data_item_array_match res vl0.contents `implies_`
        LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0
      )
    )
    (A.length a0 == U64.v n0 /\
      SZ.fits_u64
    )
    (fun _ -> True)
=
  let n0_as_sz = SZ.uint64_to_sizet n0 in
  let vl = LPS.rewrite_aparse_with_implies l0 (LPS.parse_nlist (SZ.v n0_as_sz) Cbor.parse_raw_data_item) in
  let res = LPS.read_array_payload_from_nlist Cbor.jump_raw_data_item raw_data_item_match (fun a alen -> read_valid_cbor_from_buffer_with_size_strong a alen) n0_as_sz l0 a0 in
  implies_trans
    (LPS.seq_list_match res vl.contents raw_data_item_match)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (SZ.v n0_as_sz) Cbor.parse_raw_data_item) l0 vl)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0);
  rewrite_with_implies_with_tactic
    (LPS.seq_list_match res vl.contents raw_data_item_match)
    (raw_data_item_array_match res vl.contents);
  implies_trans
    (raw_data_item_array_match res vl.contents)
    (LPS.seq_list_match res vl.contents raw_data_item_match)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0);
  rewrite_with_implies
    (raw_data_item_array_match res vl.contents)
    (raw_data_item_array_match res vl0.contents);
  implies_trans
    (raw_data_item_array_match res vl0.contents)
    (raw_data_item_array_match res vl.contents)
    (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0);
  return res

[@@__reduce__]
let read_cbor_array_post_success
  (c: cbor_array)
: Tot vprop
= exists_ (A.pts_to c.payload full_perm) `star`
  pure (
    A.is_full_array c.payload
  )

let read_cbor_array_post
  (input: cbor)
  (res: cbor)
: Tot vprop
= if CBOR_Case_Serialized? input && CBOR_Case_Array? res
  then read_cbor_array_post_success (CBOR_Case_Array?._0 res)
  else emp

inline_for_extraction
noextract
let read_cbor_array_noop
  (#obj: Ghost.erased Cbor.raw_data_item)
  (input: cbor)
: STT cbor
    (raw_data_item_match input obj)
    (fun res ->
      raw_data_item_match res obj `star`
      (raw_data_item_match res obj `implies_`
        (raw_data_item_match input obj `star` read_cbor_array_post input res)
      )
    )
= implies_with_tactic (raw_data_item_match input obj) (raw_data_item_match input obj);
  rewrite emp (read_cbor_array_post input input);
  implies_concl_r (raw_data_item_match input obj) (raw_data_item_match input obj) (read_cbor_array_post input input);
  return input

let array_pts_to_or_null
  (#t: Type)
  (a: A.array t)
  (v: Seq.seq t)
: Tot vprop
= if A.is_null a
  then emp
  else A.pts_to a full_perm v

assume val cbor_array_alloc
  (init: cbor)
  (n: SZ.t)
: ST (A.array cbor)
    emp
    (fun res -> array_pts_to_or_null res (Seq.create (SZ.v n) init))
    True
    (fun res ->
      if A.is_null res
      then True
      else A.length res == SZ.v n /\ A.is_full_array res
    )

let read_cbor_array
  (#obj: Ghost.erased Cbor.raw_data_item)
  (input: cbor)
: ST cbor
    (raw_data_item_match input obj)
    (fun res ->
      raw_data_item_match res obj `star`
      (raw_data_item_match res obj `implies_`
        (raw_data_item_match input obj `star` read_cbor_array_post input res)
      )
    )
    (Cbor.Array? obj)
    (fun _ -> True)
= raw_data_item_match_get_case input;
  match input with
  | CBOR_Case_Array _ -> read_cbor_array_noop input
  | CBOR_Case_Serialized s ->
      rewrite_with_implies
        (raw_data_item_match input obj)
        (raw_data_item_match_serialized0 input obj);
      let _ = gen_elim () in
      vpattern_rewrite_with_implies
        (fun a -> LPS.aparse Cbor.parse_raw_data_item a _)
        s.payload;
      intro_implies
        (LPS.aparse Cbor.parse_raw_data_item s.payload _)
        (raw_data_item_match_serialized0 input obj)
        (LPS.aparse Cbor.parse_raw_data_item s.payload _ `implies_`
          LPS.aparse Cbor.parse_raw_data_item _ _
        )
        (fun _ ->
          elim_implies
            (LPS.aparse Cbor.parse_raw_data_item s.payload _)
            (LPS.aparse Cbor.parse_raw_data_item _ _);
          noop ()
        );
      implies_trans
        (LPS.aparse Cbor.parse_raw_data_item s.payload _)
        (raw_data_item_match_serialized0 input obj)
        (raw_data_item_match input obj);
      R.with_local 0uL (fun plen ->
      R.with_local s.payload (fun pa ->
        let w = CBOR.SteelST.Raw.Array.focus_array plen pa s.payload in
        implies_trans
          (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.a _)
          (LPS.aparse Cbor.parse_raw_data_item s.payload _)
          (raw_data_item_match input obj);
        let len = R.read plen in
        let _ = A.intro_fits_u64 () in
        let a0 = cbor_array_alloc dummy_cbor (SZ.uint64_to_sizet len) in
        if (A.is_null a0)
        then begin
          noop ();
          rewrite
            (array_pts_to_or_null a0 _)
            emp;
          elim_implies
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.a _)
            (raw_data_item_match input obj);
          let res = read_cbor_array_noop input in
          return res
        end else begin
          noop ();
          rewrite
            (array_pts_to_or_null a0 _)
            (A.pts_to a0 full_perm (Seq.create (U64.v len) dummy_cbor));
          let vl = LPS.rewrite_aparse_with_implies
            w.a
            (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item)
          in
          let a = R.read pa in
          vpattern_rewrite_with_implies
            (fun a -> LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            a;
          implies_trans
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) _ _)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) _ _);
          implies_trans
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) _ _)
            (raw_data_item_match input obj);
          let va = read_cbor_array_payload len vl a a0 in
          implies_trans
            (raw_data_item_array_match va vl.contents)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            (raw_data_item_match input obj);
          let res = constr_cbor_array a0 len in
          vpattern_rewrite
            (fun ar -> raw_data_item_match _ ar `star` (raw_data_item_match _ ar `implies_` (A.pts_to _ _ _ `star` raw_data_item_array_match _ _)))
            obj;
          intro_implies
            (A.pts_to a0 full_perm va `star` raw_data_item_array_match va vl.contents)
            (raw_data_item_array_match va vl.contents `star` read_cbor_array_post input res)
            emp
            (fun _ ->
              vpattern_rewrite (fun a0 -> A.pts_to a0 _ _) (CBOR_Case_Array?._0 res).payload;
              rewrite (read_cbor_array_post_success (CBOR_Case_Array?._0 res)) (read_cbor_array_post input res)
            );
          implies_reg_r
            (raw_data_item_array_match va vl.contents)
            (raw_data_item_match input obj)
            (read_cbor_array_post input res);
          implies_trans
            (raw_data_item_match res obj)
            (A.pts_to a0 full_perm va `star` raw_data_item_array_match va vl.contents)
            (raw_data_item_array_match va vl.contents `star` read_cbor_array_post input res);
          implies_trans
            (raw_data_item_match res obj)
            (raw_data_item_array_match va vl.contents `star` read_cbor_array_post input res)
            (raw_data_item_match input obj `star` read_cbor_array_post input res);
          return res
        end
      ))

#push-options "--split_queries always"
#restart-solver

let serialize_cbor_array_eq
  (c: Cbor.raw_data_item { Cbor.Array? c })
: Lemma
  (
    let s0 = LPS.serialize Cbor.serialize_raw_data_item c in
    let s1 = LPS.serialize Cbor.serialize_header (Cbor.uint64_as_argument Cbor.major_type_array (U64.uint_to_t (List.Tot.length (Cbor.Array?.v c)))) in
    let s2 = LPS.serialize (LPS.serialize_nlist (List.Tot.length (Cbor.Array?.v c)) Cbor.serialize_raw_data_item) (Cbor.Array?.v c) in
    s0 == s1 `Seq.append` s2 /\ Seq.length s0 == Seq.length s1 + Seq.length s2
  )
= Cbor.serialize_raw_data_item_aux_correct c;
  LPS.serialize_synth_eq
    _
    Cbor.synth_raw_data_item
    (LPS.serialize_dtuple2 Cbor.serialize_header Cbor.serialize_content)
    Cbor.synth_raw_data_item_recip
    ()
    c;
  LPS.serialize_dtuple2_eq Cbor.serialize_header Cbor.serialize_content (Cbor.synth_raw_data_item_recip c)

#pop-options

#push-options "--z3rlimit 64"
#restart-solver

inline_for_extraction
noextract
let size_comp_for_array
  (size:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_size_comp_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Array? c})
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let _ = A.intro_fits_u64 () in
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Array? va) = () in
    serialize_cbor_array_eq va;
    let c' = destr_cbor_array c in
    let l = Ghost.hide (maybe_cbor_array va) in
    assert (Ghost.reveal l == Cbor.Array?.v va);
    rewrite_with_implies_with_tactic
      (raw_data_item_array_match _ _)
      (LPS.seq_list_match c'.footprint l raw_data_item_match);
    implies_trans_r1
      (A.pts_to _ _ _)
      (LPS.seq_list_match c'.footprint l raw_data_item_match)
      (raw_data_item_array_match _ _)
      (raw_data_item_match _ _);
    LPS.seq_list_match_length raw_data_item_match _ _;
    A.pts_to_length _ _;
    let sz1 = CBOR.SteelST.Raw.Write.size_comp_uint64_header Cbor.major_type_array c'.count sz perr in
    let _ = gen_elim () in
    let err1 = R.read perr in
    if err1
    then begin
      noop ();
      elim_implies
        (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l raw_data_item_match)
        (raw_data_item_match _ _);
      return sz1
    end else begin
      noop ();
      let sz2 = LPS.array_payload_as_nlist_size
        Cbor.serialize_raw_data_item
        raw_data_item_match
        (fun x y sz perr ->
          let res = size y x sz perr in
          let _ = gen_elim () in
          return res
        )
        #c'.footprint
        #l
        (SZ.uint64_to_sizet c'.count)
        c'.payload
        sz1
        perr
      in
      let _ = gen_elim () in
      elim_implies
        (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l raw_data_item_match)
        (raw_data_item_match _ _);
      return sz2
    end

#restart-solver

inline_for_extraction
noextract
let l2r_writer_for_array
  (write:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_l2r_writer_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Array? c})
: Tot (cbor_l2r_writer_for va c)
= fun #vout out ->
    let _ = A.intro_fits_u64 () in
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Array? va) = () in
    serialize_cbor_array_eq va;
    let c' = destr_cbor_array c in
    let l = Ghost.hide (maybe_cbor_array va) in
    assert (Ghost.reveal l == Cbor.Array?.v va);
    rewrite_with_implies_with_tactic
      (raw_data_item_array_match _ _)
      (LPS.seq_list_match c'.footprint l raw_data_item_match);
    implies_trans_r1
      (A.pts_to _ _ _)
      (LPS.seq_list_match c'.footprint l raw_data_item_match)
      (raw_data_item_array_match _ _)
      (raw_data_item_match _ _);
    LPS.seq_list_match_length raw_data_item_match _ _;
    A.pts_to_length _ _;
    let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header Cbor.major_type_array c'.count out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer Cbor.serialize_header res in
    let res_pl = LPS.l2r_write_array_payload_as_nlist
      Cbor.serialize_raw_data_item
      raw_data_item_match
      (fun x y out ->
         let res = write y x out in
         let _ = gen_elim () in
         return res
      )
      #c'.footprint
      #l
      (SZ.uint64_to_sizet c'.count)
      c'.payload
      out
    in
    let _ = gen_elim () in
    let vout' = vpattern_replace (LW.vp out) in
    let _ = LPS.elim_aparse_with_serializer (LPS.serialize_nlist (SZ.v (SZ.uint64_to_sizet c'.count)) Cbor.serialize_raw_data_item) res_pl in
    let _ = LPA.join res res_pl in
    let _ = gen_elim () in
    let vres = LPS.intro_aparse_with_serializer Cbor.serialize_raw_data_item va res in
    elim_implies
      (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l raw_data_item_match)
      (raw_data_item_match _ _);
    assert_ (cbor_l2r_writer_for_post va c vout out res vres vout'); // FIXME: WHY WHY WHY?
    return res

#pop-options

[@@__reduce__]
let maybe_cbor_tagged_tag
  (v: Cbor.raw_data_item)
: GTot U64.t
= match v with
  | Cbor.Tagged t _ -> t
  | _ -> 0uL // dummy

[@@__reduce__]
let maybe_cbor_tagged_payload
  (v: Cbor.raw_data_item)
: GTot Cbor.raw_data_item
= match v with
  | Cbor.Tagged _ l -> l
  | _ -> dummy_raw_data_item

let destr_cbor_tagged
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_tagged
    (raw_data_item_match a v)
    (fun res ->
      R.pts_to res.payload full_perm res.footprint `star`
      raw_data_item_match res.footprint (maybe_cbor_tagged_payload v) `star`
      ((R.pts_to res.payload full_perm res.footprint `star`
        raw_data_item_match res.footprint (maybe_cbor_tagged_payload v)) `implies_`
        raw_data_item_match a v
      )
    )
    (CBOR_Case_Tagged? a)
    (fun res ->
      a == CBOR_Case_Tagged res /\
      Cbor.Tagged? v /\
      res.tag == Cbor.Tagged?.tag v
    )
= raw_data_item_match_get_case _;
  let _ : squash (Cbor.Tagged? v) = () in
  let g_tag = Ghost.hide (Cbor.Tagged?.tag v) in
  let g_payload = Ghost.hide (Cbor.Tagged?.v v) in
  let CBOR_Case_Tagged res = a in
  rewrite_with_implies
    (raw_data_item_match a v)
    (raw_data_item_match (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload));
  rewrite_with_implies_with_tactic
    (raw_data_item_match (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload))
    (raw_data_item_match_tagged0 (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload) raw_data_item_match);
  implies_trans
    (raw_data_item_match_tagged0 (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload) raw_data_item_match)
    (raw_data_item_match (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload))
    (raw_data_item_match a v);
  let _ = gen_elim () in
  let _ : squash (res.tag == Ghost.reveal g_tag) = () in
  let _ : squash (maybe_cbor_tagged_payload v == Ghost.reveal g_payload) = () in
  let _ : squash (Ghost.reveal g_payload << Cbor.Tagged g_tag g_payload) = () in // FIXME: WHY WHY WHY?
  rewrite (R.pts_to _ _ _) (R.pts_to res.payload full_perm res.footprint);
  rewrite (raw_data_item_match _ _) (raw_data_item_match res.footprint (maybe_cbor_tagged_payload v));
  intro_implies
    (R.pts_to res.payload full_perm res.footprint `star`
      raw_data_item_match res.footprint (maybe_cbor_tagged_payload v))
    (raw_data_item_match a v)
    (raw_data_item_match_tagged0 _ _ raw_data_item_match `implies_` raw_data_item_match a _)
    (fun _ ->
      elim_implies
        (raw_data_item_match_tagged0 (CBOR_Case_Tagged res) (Cbor.Tagged g_tag g_payload) raw_data_item_match)
        (raw_data_item_match a _)
    );
  return res

#push-options "--z3rlimit 64"
#restart-solver

let serialize_cbor_tagged_eq
  (c: Cbor.raw_data_item { Cbor.Tagged? c })
: Lemma
  (
    let s0 = LPS.serialize Cbor.serialize_raw_data_item c in
    let s1 = LPS.serialize Cbor.serialize_header (Cbor.uint64_as_argument Cbor.major_type_tagged (Cbor.Tagged?.tag c)) in
    let s2 = LPS.serialize Cbor.serialize_raw_data_item (Cbor.Tagged?.v c) in
    s0 == s1 `Seq.append` s2 /\ Seq.length s0 == Seq.length s1 + Seq.length s2
  )
= Cbor.serialize_raw_data_item_aux_correct c;
  LPS.serialize_synth_eq
    _
    Cbor.synth_raw_data_item
    (LPS.serialize_dtuple2 Cbor.serialize_header Cbor.serialize_content)
    Cbor.synth_raw_data_item_recip
    ()
    c;
  LPS.serialize_dtuple2_eq Cbor.serialize_header Cbor.serialize_content (Cbor.synth_raw_data_item_recip c)

inline_for_extraction
noextract
let size_comp_for_tagged
  (size:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_size_comp_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Tagged? c})
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Tagged? va) = () in
    serialize_cbor_tagged_eq va;
    let c' = destr_cbor_tagged c in
    let sz1 = CBOR.SteelST.Raw.Write.size_comp_uint64_header Cbor.major_type_tagged c'.tag sz perr in
    let _ = gen_elim () in
    let err1 = R.read perr in
    if err1
    then begin
      noop ();
      elim_implies
        (R.pts_to _ _ _ `star` raw_data_item_match _ _)
        (raw_data_item_match _ _);
      return sz1
    end else begin
      noop ();
      let pl = R.read c'.payload in
      vpattern_rewrite_with_implies
        (fun pl -> raw_data_item_match pl _)
        pl;
      let sz2 = size _ pl sz1 perr in
      let _ = gen_elim () in
      elim_implies
        (raw_data_item_match pl _)
        (raw_data_item_match _ _);
      elim_implies
        (R.pts_to _ _ _ `star` raw_data_item_match _ _)
        (raw_data_item_match _ _);
      return sz2
    end

inline_for_extraction
noextract
let l2r_writer_for_tagged
  (write:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_l2r_writer_for va c
  )
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Tagged? c})
: Tot (cbor_l2r_writer_for va c)
= fun #vout out ->
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Tagged? va) = () in
    serialize_cbor_tagged_eq va;
    let c' = destr_cbor_tagged c in
    let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header Cbor.major_type_tagged c'.tag out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer Cbor.serialize_header res in
    let pl = R.read c'.payload in
    vpattern_rewrite_with_implies
      (fun pl -> raw_data_item_match pl _)
      pl;
    let res_pl = write _ pl out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer Cbor.serialize_raw_data_item res_pl in
    let _ = LPA.join res res_pl in
    let vres = LPS.intro_aparse_with_serializer Cbor.serialize_raw_data_item va res in
    let vout' = vpattern_replace (LW.vp out) in
    elim_implies
      (raw_data_item_match pl _)
      (raw_data_item_match _ _);
    elim_implies
      (R.pts_to _ _ _ `star` raw_data_item_match _ _)
      (raw_data_item_match _ _);
    assert_ (cbor_l2r_writer_for_post va c vout out res vres vout'); // FIXME: WHY WHY WHY?
    return res

#pop-options

[@@__reduce__]
let maybe_cbor_map
  (v: Cbor.raw_data_item)
: GTot (list (Cbor.raw_data_item & Cbor.raw_data_item))
= match v with
  | Cbor.Map l -> l
  | _ -> []

let destr_cbor_map
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_map
    (raw_data_item_match a v)
    (fun res ->
      A.pts_to res.payload full_perm res.footprint `star`
      LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match0 raw_data_item_match) `star`
      ((A.pts_to res.payload full_perm res.footprint `star`
        LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match0 raw_data_item_match)) `implies_`
        raw_data_item_match a v
      )
    )
    (CBOR_Case_Map? a)
    (fun res ->
      a == CBOR_Case_Map res /\
      Cbor.Map? v /\
      U64.v res.entry_count == List.Tot.length (Cbor.Map?.v v)
    )
= raw_data_item_match_get_case _;
  let sq : squash (Cbor.Map? v) = () in
  let CBOR_Case_Map res = a in
  rewrite_with_implies
    (raw_data_item_match _ _)
    (raw_data_item_match (CBOR_Case_Map res) (Cbor.Map (maybe_cbor_map v)));
  rewrite_with_implies_with_tactic
    (raw_data_item_match (CBOR_Case_Map res) (Cbor.Map (maybe_cbor_map v)))
    (raw_data_item_match_map0 (CBOR_Case_Map res) (Cbor.Map (maybe_cbor_map v)) raw_data_item_map_match);
  implies_trans
    (raw_data_item_match_map0 (CBOR_Case_Map res) (Cbor.Map (maybe_cbor_map v)) raw_data_item_map_match)
    (raw_data_item_match (CBOR_Case_Map res) (Cbor.Map (maybe_cbor_map v)))
    (raw_data_item_match _ _);
  let _ = gen_elim () in
  rewrite
    (A.pts_to _ _ _)
    (A.pts_to res.payload full_perm res.footprint);
  rewrite
    (raw_data_item_map_match _ _)
    (raw_data_item_map_match res.footprint (maybe_cbor_map v));
  rewrite_with_tactic
    (raw_data_item_map_match res.footprint (maybe_cbor_map v))
    (LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match (maybe_cbor_map v) raw_data_item_match));
  LPS.seq_list_match_weaken
    res.footprint (maybe_cbor_map v)
    (raw_data_item_map_entry_match (maybe_cbor_map v) raw_data_item_match)
    (raw_data_item_map_entry_match0 raw_data_item_match)
    (fun x y ->
      rewrite
        (raw_data_item_map_entry_match (maybe_cbor_map v) raw_data_item_match x y)
        (raw_data_item_map_entry_match0 raw_data_item_match x y)
    );
  intro_implies
    (A.pts_to res.payload full_perm res.footprint `star`
      LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match0 raw_data_item_match))
    (raw_data_item_match a v)
    (raw_data_item_match_map0 (CBOR_Case_Map res) (Cbor.Map (maybe_cbor_map v)) raw_data_item_map_match `implies_`
      raw_data_item_match a v)
    (fun _ ->
      LPS.seq_list_match_weaken
        res.footprint (maybe_cbor_map v)
        (raw_data_item_map_entry_match0 raw_data_item_match)
        (raw_data_item_map_entry_match (maybe_cbor_map v) raw_data_item_match)
        (fun x y ->
          rewrite
            (raw_data_item_map_entry_match0 raw_data_item_match x y)
            (raw_data_item_map_entry_match (maybe_cbor_map v) raw_data_item_match x y)
        );
      rewrite_with_tactic
        (LPS.seq_list_match res.footprint (maybe_cbor_map v) (raw_data_item_map_entry_match (maybe_cbor_map v) raw_data_item_match))
        (raw_data_item_map_match res.footprint (maybe_cbor_map v));
      rewrite
        (raw_data_item_map_match res.footprint (maybe_cbor_map v)) 
        (raw_data_item_map_match res.footprint (Cbor.Map?.v (Cbor.Map (maybe_cbor_map v))));
      elim_implies
        (raw_data_item_match_map0 _ _ raw_data_item_map_match)
        (raw_data_item_match a v)
    );
  return res

inline_for_extraction
noextract
let size_comp_for_map_entry
  (size:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_size_comp_for va c
  )
  (va: Ghost.erased (Cbor.raw_data_item & Cbor.raw_data_item))
  (c: cbor_map_entry)
  (sz: SZ.t)
  (perr: R.ref bool)
: STT SZ.t
    (raw_data_item_map_entry_match0 raw_data_item_match c (Ghost.reveal va) `star`
      R.pts_to perr full_perm false
    )
    (fun res ->
      raw_data_item_map_entry_match0 raw_data_item_match c (Ghost.reveal va) `star`
      exists_ (fun err ->
        R.pts_to perr full_perm err `star`
        pure (LowParse.SteelST.Write.size_comp_for_post (LPS.serialize_nondep_then Cbor.serialize_raw_data_item Cbor.serialize_raw_data_item) va sz res err)
    ))
= LPS.serialize_nondep_then_eq Cbor.serialize_raw_data_item Cbor.serialize_raw_data_item va;
  let sz1 = size _ c.key sz perr in
  let _ = gen_elim () in
  let err = R.read perr in
  if err
  then begin
    noop ();
    noop ();
    return sz1
  end else begin
    noop ();
    let sz2 = size _ c.value sz1 perr in
    let _ = gen_elim () in
    noop ();
    return sz2
  end

#push-options "--z3rlimit 64"
#restart-solver

let serialize_cbor_map_eq
  (c: Cbor.raw_data_item { Cbor.Map? c })
: Lemma
  (
    let s0 = LPS.serialize Cbor.serialize_raw_data_item c in
    let s1 = LPS.serialize Cbor.serialize_header (Cbor.uint64_as_argument Cbor.major_type_map (U64.uint_to_t (List.Tot.length (Cbor.Map?.v c)))) in
    let s2 = LPS.serialize (LPS.serialize_nlist (List.Tot.length (Cbor.Map?.v c)) (LPS.serialize_nondep_then Cbor.serialize_raw_data_item Cbor.serialize_raw_data_item)) (Cbor.Map?.v c) in
    s0 == s1 `Seq.append` s2 /\ Seq.length s0 == Seq.length s1 + Seq.length s2
  )
= Cbor.serialize_raw_data_item_aux_correct c;
  LPS.serialize_synth_eq
    _
    Cbor.synth_raw_data_item
    (LPS.serialize_dtuple2 Cbor.serialize_header Cbor.serialize_content)
    Cbor.synth_raw_data_item_recip
    ()
    c;
  LPS.serialize_dtuple2_eq Cbor.serialize_header Cbor.serialize_content (Cbor.synth_raw_data_item_recip c)

inline_for_extraction
noextract
let size_comp_for_map
  (size:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_size_comp_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Map? c})
: Tot (cbor_size_comp_for va c)
= fun sz perr ->
    let _ = A.intro_fits_u64 () in
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Map? va) = () in
    serialize_cbor_map_eq va;
    let c' = destr_cbor_map c in
    let l = Ghost.hide (maybe_cbor_map va) in
    assert (Ghost.reveal l == Cbor.Map?.v va);
    rewrite_with_implies
      (LPS.seq_list_match c'.footprint _ (raw_data_item_map_entry_match0 raw_data_item_match))
      (LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match0 raw_data_item_match));
    implies_trans_r1
      (A.pts_to _ _ _)
      (LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match0 raw_data_item_match))
      (LPS.seq_list_match c'.footprint _ (raw_data_item_map_entry_match0 raw_data_item_match))
      (raw_data_item_match _ _);
    LPS.seq_list_match_length (raw_data_item_map_entry_match0 raw_data_item_match) _ _;
    A.pts_to_length _ _;
    let sz1 = CBOR.SteelST.Raw.Write.size_comp_uint64_header Cbor.major_type_map c'.entry_count sz perr in
    let _ = gen_elim () in
    let err1 = R.read perr in
    if err1
    then begin
      noop ();
      elim_implies
        (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match0 raw_data_item_match))
        (raw_data_item_match _ _);
      return sz1
    end else begin
      noop ();
      let sz2 = LPS.array_payload_as_nlist_size
        (LPS.serialize_nondep_then Cbor.serialize_raw_data_item Cbor.serialize_raw_data_item)
        (raw_data_item_map_entry_match0 raw_data_item_match)
        (fun x y sz perr ->
          let res = size_comp_for_map_entry size y x sz perr in
          let _ = gen_elim () in
          return res
        )
        #c'.footprint
        #l
        (SZ.uint64_to_sizet c'.entry_count)
        c'.payload
        sz1
        perr
      in
      let _ = gen_elim () in
      elim_implies
        (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match0 raw_data_item_match))
        (raw_data_item_match _ _);
      return sz2
    end

noextract
unfold
let l2r_write_map_entry_post
  (va: Ghost.erased (Cbor.raw_data_item & Cbor.raw_data_item))
  (vout: LPA.array LPS.byte)
  (vres: LPS.v (LPS.and_then_kind Cbor.parse_raw_data_item_kind Cbor.parse_raw_data_item_kind) (Cbor.raw_data_item & Cbor.raw_data_item))
  (vout': LPA.array LPS.byte)
: Tot prop
=  
       LPA.merge_into (LPS.array_of vres) vout' vout /\
       vres.LPS.contents == Ghost.reveal va

[@@__reduce__]
let l2r_writer_for_map_entry_post
  (va: Ghost.erased (Cbor.raw_data_item & Cbor.raw_data_item))
  (c: cbor_map_entry)
  (vout: LPA.array LPS.byte)
  (out: LW.t)
  (res: LPS.byte_array)
  (vres: LPS.v (LPS.and_then_kind Cbor.parse_raw_data_item_kind Cbor.parse_raw_data_item_kind) (Cbor.raw_data_item & Cbor.raw_data_item))
  (vout': LPA.array LPS.byte)
: Tot vprop
=
  raw_data_item_map_entry_match0 raw_data_item_match c (Ghost.reveal va) `star`
  LPS.aparse (LPS.nondep_then Cbor.parse_raw_data_item Cbor.parse_raw_data_item) res vres `star`
  LW.vp out vout' `star`
  pure (
    l2r_write_map_entry_post va vout vres vout'
  )

inline_for_extraction
noextract
let l2r_writer_for_map_entry
  (write:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_l2r_writer_for va c
  )
  (va: Ghost.erased (Cbor.raw_data_item & Cbor.raw_data_item))
  (c: cbor_map_entry)
  (#vout: LPA.array LPS.byte)
  (out: LW.t)
: ST LPS.byte_array
    (raw_data_item_map_entry_match0 raw_data_item_match c (Ghost.reveal va) `star`
      LW.vp out vout
    )
    (fun res -> exists_ (fun vres -> exists_ (fun vout' ->
      l2r_writer_for_map_entry_post va c vout out res vres vout'
    )))
    (Seq.length (LPS.serialize (LPS.serialize_nondep_then Cbor.serialize_raw_data_item Cbor.serialize_raw_data_item) va) <= LPA.length vout)
    (fun _ -> True)
= LPS.serialize_nondep_then_eq Cbor.serialize_raw_data_item Cbor.serialize_raw_data_item va;
  noop ();
  let res = write _ c.key out in
  let _ = gen_elim () in
  let _ = LPS.elim_aparse_with_serializer Cbor.serialize_raw_data_item res in
  let res_pl = write _ c.value out in
  let _ = gen_elim () in
  let vout' = vpattern_replace (LW.vp out) in
  let _ = LPS.elim_aparse_with_serializer Cbor.serialize_raw_data_item res_pl in
  let _ = LPA.join res res_pl in
  let vres = LPS.intro_aparse_with_serializer (LPS.serialize_nondep_then Cbor.serialize_raw_data_item Cbor.serialize_raw_data_item) va res in
  assert_ (l2r_writer_for_map_entry_post va c vout out res vres vout');
  return res

inline_for_extraction
noextract
let l2r_writer_for_map
  (write:
    (va: Ghost.erased Cbor.raw_data_item) ->
    (c: cbor) ->
    cbor_l2r_writer_for va c
  )
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {CBOR_Case_Map? c})
: Tot (cbor_l2r_writer_for va c)
= fun #vout out ->
    let _ = A.intro_fits_u64 () in
    raw_data_item_match_get_case c;
    let _ : squash (Cbor.Map? va) = () in
    serialize_cbor_map_eq va;
    let c' = destr_cbor_map c in
    let l = Ghost.hide (maybe_cbor_map va) in
    assert (Ghost.reveal l == Cbor.Map?.v va);
    rewrite_with_implies
      (LPS.seq_list_match c'.footprint _ (raw_data_item_map_entry_match0 raw_data_item_match))
      (LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match0 raw_data_item_match));
    implies_trans_r1
      (A.pts_to _ _ _)
      (LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match0 raw_data_item_match))
      (LPS.seq_list_match c'.footprint _ (raw_data_item_map_entry_match0 raw_data_item_match))
      (raw_data_item_match _ _);
    LPS.seq_list_match_length (raw_data_item_map_entry_match0 raw_data_item_match) _ _;
    A.pts_to_length _ _;
    let res = CBOR.SteelST.Raw.Write.l2r_write_uint64_header Cbor.major_type_map c'.entry_count out in
    let _ = gen_elim () in
    let _ = LPS.elim_aparse_with_serializer Cbor.serialize_header res in
    let res_pl = LPS.l2r_write_array_payload_as_nlist
      (LPS.serialize_nondep_then Cbor.serialize_raw_data_item Cbor.serialize_raw_data_item)
      (raw_data_item_map_entry_match0 raw_data_item_match)
      (fun x y out ->
         let res = l2r_writer_for_map_entry write y x out in
         let _ = gen_elim () in
         return res
      )
      #c'.footprint
      #l
      (SZ.uint64_to_sizet c'.entry_count)
      c'.payload
      out
    in
    let _ = gen_elim () in
    let vout' = vpattern_replace (LW.vp out) in
    let _ = LPS.elim_aparse_with_serializer (LPS.serialize_nlist (SZ.v (SZ.uint64_to_sizet c'.entry_count)) (LPS.serialize_nondep_then Cbor.serialize_raw_data_item Cbor.serialize_raw_data_item)) res_pl in
    let _ = LPA.join res res_pl in
    let _ = gen_elim () in
    let vres = LPS.intro_aparse_with_serializer Cbor.serialize_raw_data_item va res in
    elim_implies
      (A.pts_to _ _ _ `star` LPS.seq_list_match c'.footprint l (raw_data_item_map_entry_match0 raw_data_item_match))
      (raw_data_item_match _ _);
    assert_ (cbor_l2r_writer_for_post va c vout out res vres vout'); // FIXME: WHY WHY WHY?
    return res

#pop-options

let rec cbor_size_comp
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (sz: SZ.t)
  (perr: R.ref bool)
: STT SZ.t // FIXME: WHY WHY WHY do I need to expand the type annotation to avoid the termination check?
    (raw_data_item_match c (Ghost.reveal va) `star`
      R.pts_to perr full_perm false
    )
    (fun res ->
      raw_data_item_match c (Ghost.reveal va) `star`
      exists_ (fun err ->
        R.pts_to perr full_perm err `star`
        pure (LowParse.SteelST.Write.size_comp_for_post Cbor.serialize_raw_data_item va sz res err)
    ))
=
  raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 _ -> size_comp_for_int64 va c sz perr
  | CBOR_Case_Simple_value _ -> size_comp_for_simple_value va c sz perr
  | CBOR_Case_String _ -> size_comp_for_string va c sz perr
  | CBOR_Case_Tagged _ -> size_comp_for_tagged cbor_size_comp va c sz perr
  | CBOR_Case_Array _ -> size_comp_for_array cbor_size_comp va c sz perr
  | CBOR_Case_Map _ -> size_comp_for_map cbor_size_comp va c sz perr
  | _ -> size_comp_for_serialized c sz perr

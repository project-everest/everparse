module CBOR.Pulse.Raw.EverParse.Insert
#lang-pulse

friend CBOR.Spec.Raw.Format

open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module I16 = FStar.Int16
module Validate = CBOR.Pulse.Raw.EverParse.Validate
module GR = Pulse.Lib.GhostReference
module R = Pulse.Lib.Reference
module CBytes = CBOR.Pulse.Raw.Compare.Bytes
module Swap = Pulse.Lib.Swap.Slice

(* ============================================================
   Pure helper lemmas
   ============================================================ *)

let list_cons_hd_tl (#a: Type) (l: list a)
: Lemma
    (requires (Cons? l))
    (ensures (l == List.Tot.hd l :: List.Tot.tl l))
= ()

let cbor_map_insert_cons_lt
  (kv': (raw_data_item & raw_data_item))
  (q: list (raw_data_item & raw_data_item))
  (kv: (raw_data_item & raw_data_item))
: Lemma
    (ensures (
      CBOR.Spec.Raw.Map.map_entry_compare cbor_compare kv' kv < 0 ==>
        cbor_map_insert (kv' :: q) kv ==
          (match cbor_map_insert q kv with
           | None -> None
           | Some l' -> Some (kv' :: l'))))
= ()

let cbor_map_insert_cons_gt
  (kv': (raw_data_item & raw_data_item))
  (q: list (raw_data_item & raw_data_item))
  (kv: (raw_data_item & raw_data_item))
: Lemma
    (ensures (
      CBOR.Spec.Raw.Map.map_entry_compare cbor_compare kv' kv > 0 ==>
        cbor_map_insert (kv' :: q) kv == Some (kv :: kv' :: q)))
= ()

let cbor_map_insert_cons_eq
  (kv': (raw_data_item & raw_data_item))
  (q: list (raw_data_item & raw_data_item))
  (kv: (raw_data_item & raw_data_item))
: Lemma
    (ensures (
      CBOR.Spec.Raw.Map.map_entry_compare cbor_compare kv' kv = 0 ==>
        cbor_map_insert (kv' :: q) kv == None))
= ()

(* ============================================================
   cbor_jump_append: jump past one serialized item
   ============================================================ *)

inline_for_extraction
fn cbor_jump_append
  (input: S.slice U8.t)
  (c: Ghost.erased raw_data_item)
  (v: Ghost.erased (Seq.seq U8.t))
  (#pm: perm)
  (#v': Ghost.erased (Seq.seq U8.t))
  requires
    pts_to input #pm v' **
    pure (
      Ghost.reveal v' == Seq.append (serialize_cbor c) (Ghost.reveal v) /\
      SZ.fits_u64
    )
  returns res: SZ.t
  ensures
    pts_to input #pm v' **
    pure (
      SZ.v res == Seq.length (serialize_cbor c)
    )
{
  let f64 : squash SZ.fits_u64 = ();
  serialize_parse_cbor c;
  LowParse.Spec.Base.parse_strong_prefix
    parse_raw_data_item
    (serialize_cbor c)
    (Ghost.reveal v');
  assert (pure (Seq.slice (Ghost.reveal v') 0 (Seq.length (Ghost.reveal v')) `Seq.equal` Ghost.reveal v'));
  let res = Validate.jump_raw_data_item f64 input 0sz;
  res
}

let serialize_cbor_map_cons_equiv
  (m: list (raw_data_item & raw_data_item))
: Lemma
  (Cons? m <==> Seq.length (serialize_cbor_map m) > 0)
= match m with
  | [] -> serialize_cbor_map_nil ()
  | (key, value) :: q ->
    serialize_cbor_map_cons key value q;
    serialize_cbor_nonempty key

(* ============================================================
   Out-inv invariants and equivalence
   ============================================================ *)

let cbor_raw_map_insert_out_inv
  (off1: SZ.t)
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Tot prop
= let sm = serialize_cbor_map m in
  let sk = serialize_cbor key in
  let sv = serialize_cbor value in
  SZ.v off1 + Seq.length sm == SZ.v off2 /\
  SZ.v off2 + Seq.length sk == SZ.v off3 /\
  SZ.v off3 + Seq.length sv == Seq.length v /\
  Seq.slice v (SZ.v off1) (SZ.v off2) `Seq.equal` sm /\
  Seq.slice v (SZ.v off2) (SZ.v off3) `Seq.equal` sk /\
  Seq.slice v (SZ.v off3) (Seq.length v) `Seq.equal` sv

let cbor_raw_map_insert_out_inv_elim
  (off1: SZ.t)
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Lemma
  (requires (cbor_raw_map_insert_out_inv off1 m off2 key off3 value v))
  (ensures (
    let sm = serialize_cbor_map m in
    let sk = serialize_cbor key in
    let sv = serialize_cbor value in
    SZ.v off1 + Seq.length sm == SZ.v off2 /\
    SZ.v off2 + Seq.length sk == SZ.v off3 /\
    SZ.v off3 + Seq.length sv == Seq.length v /\
    Seq.slice v (SZ.v off1) (SZ.v off2) `Seq.equal` sm /\
    Seq.slice v (SZ.v off2) (SZ.v off3) `Seq.equal` sk /\
    Seq.slice v (SZ.v off3) (Seq.length v) `Seq.equal` sv
  ))
= ()

let cbor_raw_map_insert_out_inv_intro
  (off1: SZ.t)
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Lemma
  (requires (
    let sm = serialize_cbor_map m in
    let sk = serialize_cbor key in
    let sv = serialize_cbor value in
    SZ.v off1 + Seq.length sm == SZ.v off2 /\
    SZ.v off2 + Seq.length sk == SZ.v off3 /\
    SZ.v off3 + Seq.length sv == Seq.length v /\
    Seq.slice v (SZ.v off1) (SZ.v off2) `Seq.equal` sm /\
    Seq.slice v (SZ.v off2) (SZ.v off3) `Seq.equal` sk /\
    Seq.slice v (SZ.v off3) (Seq.length v) `Seq.equal` sv
  ))
  (ensures (cbor_raw_map_insert_out_inv off1 m off2 key off3 value v))
= ()

let cbor_raw_map_insert_out_inv'
  (off1: SZ.t)
  (m: (list (raw_data_item & raw_data_item)))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Tot prop
= let sm = serialize_cbor_map m in
  let sk = serialize_cbor key in
  let sv = serialize_cbor value in
  SZ.v off1 + Seq.length sm == SZ.v off2 /\
  SZ.v off2 + Seq.length sk == SZ.v off3 /\
  SZ.v off3 + Seq.length sv == Seq.length v /\
  Seq.slice v (SZ.v off1) (Seq.length v) `Seq.equal`
    (sm `Seq.append` (sk `Seq.append` sv))

let seq_slice_append
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures
    Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1 /\
    Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2) `Seq.equal` s2
  )
= ()

#push-options "--z3rlimit 64 --split_queries always"

#restart-solver

let cbor_raw_map_insert_out_inv_equiv
  (off1: SZ.t)
  (m: (list (raw_data_item & raw_data_item)))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Lemma
  (cbor_raw_map_insert_out_inv off1 m off2 key off3 value v <==>
    cbor_raw_map_insert_out_inv' off1 m off2 key off3 value v
  )
= let sm = serialize_cbor_map m in
  let sk = serialize_cbor key in
  let sv = serialize_cbor value in
  if
    SZ.v off1 + Seq.length sm = SZ.v off2 &&
    SZ.v off2 + Seq.length sk = SZ.v off3 &&
    SZ.v off3 + Seq.length sv = Seq.length v
  then begin
    seq_slice_append sm (Seq.append sk sv);
    seq_slice_append sk sv;
    Seq.slice_slice v (SZ.v off1) (Seq.length v) 0 (Seq.length sm);
    Seq.slice_slice v (SZ.v off1) (Seq.length v) (Seq.length sm) (Seq.length sm + Seq.length (Seq.append sk sv));
    Seq.lemma_split (Seq.slice v (SZ.v off1) (Seq.length v)) (SZ.v off2 - SZ.v off1);
    Seq.slice_slice v (SZ.v off2) (Seq.length v) 0 (Seq.length sk);
    Seq.slice_slice v (SZ.v off2) (Seq.length v) (Seq.length sk) (Seq.length sk + Seq.length sv);
    Seq.lemma_split (Seq.slice v (SZ.v off2) (Seq.length v)) (SZ.v off3 - SZ.v off2);
    ()
  end
  else
    ()

#pop-options

let cbor_raw_map_insert_post
  (m: list (raw_data_item & raw_data_item))
  (key: raw_data_item)
  (value: raw_data_item)
  (res: bool)
  (v': Seq.seq U8.t)
: Tot prop
= match cbor_map_insert m (key, value) with
  | None -> res == false
  | Some m' -> res == true /\ v' == serialize_cbor_map m'

type cbor_raw_map_insert_result =
  | CFailure
  | CInProgress
  | CSuccess

let cbor_raw_map_insert_post_intro_some
  (m: list (raw_data_item & raw_data_item))
  (key: raw_data_item)
  (value: raw_data_item)
  (res: bool)
  (v: Seq.seq U8.t)
  (m': list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    cbor_map_insert m (key, value) == Some m' /\
    res == true /\
    v == serialize_cbor_map m'
  ))
  (ensures (cbor_raw_map_insert_post m key value res v))
= ()

let cbor_raw_map_insert_post_intro_none
  (m: list (raw_data_item & raw_data_item))
  (key: raw_data_item)
  (value: raw_data_item)
  (res: bool)
  (v: Seq.seq U8.t)
: Lemma
  (requires (
    cbor_map_insert m (key, value) == None /\
    res == false
  ))
  (ensures (cbor_raw_map_insert_post m key value res v))
= ()

let cbor_raw_map_insert_post_elim
  (m: list (raw_data_item & raw_data_item))
  (key: raw_data_item)
  (value: raw_data_item)
  (res: bool)
  (v': Seq.seq U8.t)
: Lemma
  (requires (cbor_raw_map_insert_post m key value res v'))
  (ensures (
    match cbor_map_insert m (key, value) with
    | None -> res == false
    | Some m' -> res == true /\ v' == serialize_cbor_map m'
  ))
= ()

unfold
let cbor_raw_map_insert_inv_not_success
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
  (l1 l2: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (res: cbor_raw_map_insert_result)
: Tot prop
=
      let om' = cbor_map_insert m (key, value) in
      let om2' = cbor_map_insert l2 (key, value) in
      let sl1 = serialize_cbor_map l1 in
      cbor_raw_map_insert_out_inv off l2 off2 key off3 value v /\
      Seq.length sl1 == SZ.v off /\
      Seq.slice v 0 (SZ.v off) `Seq.equal` sl1 /\
      Some? om' == (CInProgress? res && Some? om2') /\
      begin match om', om2' with
      | None, None -> True
      | Some m', Some m2' -> m' == List.Tot.append l1 m2'
      | _ -> False
      end

unfold
let cbor_raw_map_insert_inv'
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
  (l1 l2: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (res: cbor_raw_map_insert_result)
: Tot prop
=
  if res = CSuccess
  then cbor_raw_map_insert_post m key value true v
  else cbor_raw_map_insert_inv_not_success m off2 key off3 value v l1 l2 off res

unfold
let cbor_raw_map_insert_inv = cbor_raw_map_insert_inv'

let seq_append_assoc_1_23_4
  (#t: Type)
  (s1 s2 s3 s4: Seq.seq t)
: Lemma
  (Seq.append s1 (Seq.append (Seq.append s2 s3) s4) `Seq.equal`
    Seq.append (Seq.append s1 s2) (Seq.append s3 s4)
  )
= ()

(* ============================================================
   Pure proof obligation discharge for the c<0 case.
   Given the new state after the lt-branch's joins, this lemma
   discharges the loop invariant for the next iteration.
   Extracted as a pure F* lemma to avoid SMT overload in Pulse.
   ============================================================ *)

#push-options "--z3rlimit 128 --split_queries always"

#restart-solver

let cbor_raw_map_insert_lt_step
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
  (l1 l2: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (kv': (raw_data_item & raw_data_item))
  (l2': list (raw_data_item & raw_data_item))
  (offk offq: SZ.t)
  (off': SZ.t)
: Lemma
  (requires (
    cbor_raw_map_insert_inv_not_success m off2 key off3 value v l1 l2 off CInProgress /\
    Cons? l2 /\
    l2 == kv' :: l2' /\
    cbor_compare (fst kv') key < 0 /\
    SZ.v offk == Seq.length (serialize_cbor (fst kv')) /\
    SZ.v offq == Seq.length (serialize_cbor (snd kv')) /\
    SZ.v off' == SZ.v off + SZ.v offk + SZ.v offq
  ))
  (ensures (
    cbor_raw_map_insert_inv_not_success m off2 key off3 value v
      (List.Tot.append l1 [kv']) l2' off' CInProgress
  ))
=
  let key' = fst kv' in
  let value' = snd kv' in
  let lkv' = [kv'] in
  let l1' = List.Tot.append l1 lkv' in
  let slkv' = Seq.append (serialize_cbor key') (serialize_cbor value') in
  let sl1 = serialize_cbor_map l1 in
  let sl2 = serialize_cbor_map l2 in
  let sl2' = serialize_cbor_map l2' in
  let sl1' = Seq.append sl1 slkv' in
  let sk = serialize_cbor key in
  let sv = serialize_cbor value in

  // Length and serialize_cbor_map of the new prefix
  serialize_cbor_map_singleton key' value';
  serialize_cbor_map_append l1 lkv';
  assert (serialize_cbor_map l1' == sl1');
  Seq.lemma_len_append sl1 slkv';

  // Length: SZ.v off' == Seq.length sl1'
  assert (SZ.v off' == Seq.length sl1');

  // serialize_cbor_map l2 == slkv' ++ sl2'
  cbor_raw_map_insert_out_inv_elim off l2 off2 key off3 value v;
  serialize_cbor_map_cons key' value' l2';
  assert (sl2 == Seq.append slkv' sl2');
  Seq.lemma_len_append slkv' sl2';

  // From prev inv: SZ.v off + Seq.length (serialize_cbor_map l2) == SZ.v off2
  // hence SZ.v off' + Seq.length sl2' == SZ.v off2
  assert (SZ.v off' + Seq.length sl2' == SZ.v off2);

  // Establish slice v 0 off' `Seq.equal` sl1' and slice v off' off2 `Seq.equal` sl2'
  // We have:
  //   slice v 0 off `Seq.equal` sl1
  //   slice v off off2 `Seq.equal` sl2 == slkv' ++ sl2'
  // Hence slice v off (off + offk + offq) == slkv' and slice v (off + offk + offq) off2 == sl2'.
  Seq.lemma_split (Seq.slice v (SZ.v off) (SZ.v off2)) (SZ.v offk + SZ.v offq);
  Seq.slice_slice v (SZ.v off) (SZ.v off2) 0 (SZ.v offk + SZ.v offq);
  Seq.slice_slice v (SZ.v off) (SZ.v off2) (SZ.v offk + SZ.v offq) (SZ.v off2 - SZ.v off);
  assert (Seq.slice v (SZ.v off) (SZ.v off') `Seq.equal` slkv');
  assert (Seq.slice v (SZ.v off') (SZ.v off2) `Seq.equal` sl2');

  // slice v 0 off' = (slice v 0 off) ++ (slice v off off')
  Seq.lemma_split (Seq.slice v 0 (SZ.v off')) (SZ.v off);
  Seq.slice_slice v 0 (SZ.v off') 0 (SZ.v off);
  Seq.slice_slice v 0 (SZ.v off') (SZ.v off) (SZ.v off');
  assert (Seq.slice v 0 (SZ.v off') `Seq.equal` sl1');

  // slice v off' (length v) = (slice v off' off2) ++ (slice v off2 (length v))
  //                         = sl2' ++ (sk ++ sv)
  Seq.lemma_split (Seq.slice v (SZ.v off') (Seq.length v)) (SZ.v off2 - SZ.v off');
  Seq.slice_slice v (SZ.v off') (Seq.length v) 0 (SZ.v off2 - SZ.v off');
  Seq.slice_slice v (SZ.v off') (Seq.length v) (SZ.v off2 - SZ.v off') (Seq.length v - SZ.v off');
  Seq.lemma_split (Seq.slice v (SZ.v off2) (Seq.length v)) (SZ.v off3 - SZ.v off2);
  Seq.slice_slice v (SZ.v off2) (Seq.length v) 0 (SZ.v off3 - SZ.v off2);
  Seq.slice_slice v (SZ.v off2) (Seq.length v) (SZ.v off3 - SZ.v off2) (Seq.length v - SZ.v off2);
  assert (Seq.slice v (SZ.v off') (Seq.length v) `Seq.equal` Seq.append sl2' (Seq.append sk sv));

  // out_inv' on v at off'
  assert (cbor_raw_map_insert_out_inv' off' l2' off2 key off3 value v);
  cbor_raw_map_insert_out_inv_equiv off' l2' off2 key off3 value v;
  assert (cbor_raw_map_insert_out_inv off' l2' off2 key off3 value v);

  // Connect cbor_map_insert l2 to cbor_map_insert l2' via cons_lt
  cbor_map_insert_cons_lt kv' l2' (key, value);

  // Append associativity for the contents equation
  List.Tot.append_assoc l1 lkv'
    (match cbor_map_insert l2' (key, value) with | Some r -> r | None -> []);
  ()

#pop-options

(* ============================================================
   Main loop driver
   ============================================================ *)

#push-options "--z3rlimit 256 --split_queries always"

#restart-solver

fn cbor_raw_map_insert
  (out: S.slice U8.t)
  (m: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off2: SZ.t)
  (key: Ghost.erased raw_data_item)
  (off3: SZ.t)
  (value: Ghost.erased raw_data_item)
  (#v: Ghost.erased (Seq.seq U8.t))
requires pts_to out v ** pure (cbor_raw_map_insert_out_inv 0sz m off2 key off3 value v)
returns res: bool
ensures exists* v' .
  pts_to out v' **
  pure (cbor_raw_map_insert_post m key value res v')
{
  let f64 : squash SZ.fits_u64 = assume (SZ.fits_u64);
  serialize_cbor_map_nil ();
  let pl1 = GR.alloc (Nil #(raw_data_item & raw_data_item));
  let pl2 = GR.alloc (Ghost.reveal m);
  let mut poff = 0sz;
  let mut pres = CInProgress;
  while (
    let res = !pres;
    let off = !poff;
    (CInProgress? res && SZ.lt off off2)
  ) invariant exists* v l1 l2 off res . (
    pts_to out v **
    GR.pts_to pl1 l1 **
    GR.pts_to pl2 l2 **
    R.pts_to poff off **
    R.pts_to pres res **
    pure (
      cbor_raw_map_insert_inv m off2 key off3 value v l1 l2 off res
    )
  ) {
    with l1 . assert (GR.pts_to pl1 l1);
    with l2 . assert (GR.pts_to pl2 l2);
    with v . assert (pts_to out v);
    pts_to_len out;
    let off = !poff;
    Seq.lemma_split v (SZ.v off);
    // Make the loop inv visible as inv_not_success
    assert (pure (cbor_raw_map_insert_inv_not_success
                    m off2 key off3 value v l1 l2 off CInProgress));
    cbor_raw_map_insert_out_inv_elim off l2 off2 key off3 value v;
    let sp_top = S.split out off;
    match sp_top { Mktuple2 out1 out2kv -> {
      let sl1 = Ghost.hide (serialize_cbor_map l1);
      Seq.lemma_split (Seq.slice v (SZ.v off) (Seq.length v)) (SZ.v off2 - SZ.v off);
      let sp_kv = S.split out2kv (SZ.sub off2 off);
      match sp_kv { Mktuple2 out2 outkv -> {
        Seq.lemma_split (Seq.slice v (SZ.v off2) (Seq.length v)) (SZ.v off3 - SZ.v off2);
        let sp_v = S.split outkv (SZ.sub off3 off2);
        match sp_v { Mktuple2 outk outv -> {
          serialize_cbor_map_cons_equiv l2;
          list_cons_hd_tl l2;
          let kv' = Ghost.hide (List.Tot.hd l2);
          let key' = Ghost.hide (fst kv');
          let value' = Ghost.hide (snd kv');
          let l2' = Ghost.hide (List.Tot.tl l2);
          serialize_cbor_map_cons key' value' l2';
          Seq.append_assoc (serialize_cbor key') (serialize_cbor value') (serialize_cbor_map l2');
          seq_slice_append (serialize_cbor key') (Seq.append (serialize_cbor value') (serialize_cbor_map l2'));
          let offk = cbor_jump_append out2 key' (Seq.append (serialize_cbor value') (serialize_cbor_map l2'));
          let sp_k = S.split out2 offk;
          match sp_k { Mktuple2 outk' outvq -> {
            cbor_compare_correct key' key;
            let c = CBytes.lex_compare_bytes outk' outk;
            serialize_cbor_map_singleton key' value';
            let sk = Ghost.hide (serialize_cbor key);
            let sv = Ghost.hide (serialize_cbor value);
            let slkv = Ghost.hide (Seq.append sk sv);
            if (I16.lt c 0s) {
              seq_slice_append (serialize_cbor value') (serialize_cbor_map l2');
              let offq = cbor_jump_append outvq value' (serialize_cbor_map l2');
              S.join outk outv outkv;
              S.join outk' outvq out2;
              S.join out2 outkv out2kv;
              S.join out1 out2kv out;
              let off' = SZ.add off (SZ.add offk offq);
              poff := off';
              with vctnt . assert (pts_to out vctnt);
              // Bridge: vctnt is the post-join concat of slices, equal to v.
              Seq.slice_slice (Ghost.reveal v) (SZ.v off) (Seq.length (Ghost.reveal v)) 0 (SZ.v off2 - SZ.v off);
              Seq.slice_slice (Ghost.reveal v) (SZ.v off) (Seq.length (Ghost.reveal v)) (SZ.v off2 - SZ.v off) (Seq.length (Ghost.reveal v) - SZ.v off);
              Seq.slice_slice (Ghost.reveal v) (SZ.v off2) (Seq.length (Ghost.reveal v)) 0 (SZ.v off3 - SZ.v off2);
              Seq.slice_slice (Ghost.reveal v) (SZ.v off2) (Seq.length (Ghost.reveal v)) (SZ.v off3 - SZ.v off2) (Seq.length (Ghost.reveal v) - SZ.v off2);
              assert (pure (Seq.equal vctnt (Ghost.reveal v)));
              rewrite each vctnt as (Ghost.reveal v);
              cbor_raw_map_insert_lt_step
                (Ghost.reveal m) off2 (Ghost.reveal key) off3 (Ghost.reveal value)
                (Ghost.reveal v) (Ghost.reveal l1) (Ghost.reveal l2) off
                (Ghost.reveal kv') (Ghost.reveal l2')
                offk offq off';
              GR.op_Colon_Equals pl1 (List.Tot.append l1 [Ghost.reveal kv']);
              GR.op_Colon_Equals pl2 l2';
              ()
            } else if (I16.gt c 0s) {
              S.join outk' outvq out2;
              S.join outk outv outkv;
              S.join out2 outkv out2kv;
              let sl2 = Ghost.hide (serialize_cbor_map l2);
              with vctnt2 . assert (pts_to out2kv vctnt2);
              serialize_cbor_map_cons key' value' l2';
              // Bridge vctnt2 to sl2 ++ slkv
              Seq.lemma_split (Seq.slice (Ghost.reveal v) (SZ.v off) (Seq.length (Ghost.reveal v))) (SZ.v off2 - SZ.v off);
              Seq.lemma_split (Seq.slice (Ghost.reveal v) (SZ.v off2) (Seq.length (Ghost.reveal v))) (SZ.v off3 - SZ.v off2);
              Seq.slice_slice (Ghost.reveal v) (SZ.v off) (Seq.length (Ghost.reveal v)) 0 (SZ.v off2 - SZ.v off);
              Seq.slice_slice (Ghost.reveal v) (SZ.v off) (Seq.length (Ghost.reveal v)) (SZ.v off2 - SZ.v off) (Seq.length (Ghost.reveal v) - SZ.v off);
              Seq.slice_slice (Ghost.reveal v) (SZ.v off2) (Seq.length (Ghost.reveal v)) 0 (SZ.v off3 - SZ.v off2);
              Seq.slice_slice (Ghost.reveal v) (SZ.v off2) (Seq.length (Ghost.reveal v)) (SZ.v off3 - SZ.v off2) (Seq.length (Ghost.reveal v) - SZ.v off2);
              assert (pure (Seq.equal vctnt2 (Seq.slice (Ghost.reveal v) (SZ.v off) (Seq.length (Ghost.reveal v)))));
              assert (pure (Seq.equal vctnt2 (Seq.append (Ghost.reveal sl2) (Ghost.reveal slkv))));
              rewrite each vctnt2 as (Seq.append (Ghost.reveal sl2) (Ghost.reveal slkv));
              Swap.slice_swap' out2kv (SZ.sub off2 off) sl2 slkv;
              serialize_cbor_map_cons key value l2;
              serialize_cbor_map_append l1 ((Ghost.reveal key, Ghost.reveal value) :: l2);
              cbor_map_insert_cons_gt (Ghost.reveal kv') l2' (Ghost.reveal key, Ghost.reveal value);
              S.join out1 out2kv out;
              pres := CSuccess
            } else {
              S.join outk' outvq out2;
              S.join outk outv outkv;
              S.join out2 outkv out2kv;
              S.join out1 out2kv out;
              cbor_map_insert_cons_eq (Ghost.reveal kv') l2' (Ghost.reveal key, Ghost.reveal value);
              pres := CFailure
            }
          }}
        }}
      }}
    }}
  };
  let res = !pres;
  with l1 . assert (GR.pts_to pl1 l1);
  with l2 . assert (GR.pts_to pl2 l2);
  with v . assert (pts_to out v);
  with off1 . assert (R.pts_to poff off1);
  GR.free pl1;
  GR.free pl2;
  match res {
    CSuccess -> {
      // The CSuccess inv is precisely cbor_raw_map_insert_post m key value true v.
      assert (pure (cbor_raw_map_insert_post m key value true v));
      true
    }
    CFailure -> {
      // CFailure inv: cbor_map_insert m (key, value) == None.
      assert (pure (cbor_map_insert m (Ghost.reveal key, Ghost.reveal value) == None));
      cbor_raw_map_insert_post_intro_none m (Ghost.reveal key) (Ghost.reveal value) false v;
      false
    }
    CInProgress -> {
      // Loop exit with CInProgress means off1 >= off2; combined with the inv's
      // off1 + |serialize_cbor_map l2| == off2, we get off1 == off2 and l2 == [].
      cbor_raw_map_insert_out_inv_elim off1 l2 off2 key off3 value v;
      serialize_cbor_map_cons_equiv l2;
      assert (pure (l2 == []));
      // Now cbor_map_insert m (key, value) == Some (l1 ++ [(key, value)]).
      assert (pure (cbor_map_insert m (Ghost.reveal key, Ghost.reveal value) ==
                    Some (List.Tot.append l1 [(Ghost.reveal key, Ghost.reveal value)])));
      // Build the bytes equation: v == sl1 ++ (sk ++ sv) == serialize_cbor_map (l1 ++ [(k,v)]).
      serialize_cbor_map_singleton key value;
      serialize_cbor_map_append l1 [(Ghost.reveal key, Ghost.reveal value)];
      // The out_inv at off1 with l2=[] gives: slice v off1 (length v) `Seq.equal` (sk ++ sv)
      serialize_cbor_map_nil ();
      assert (pure (Seq.equal (serialize_cbor_map l2) Seq.empty));
      assert (pure (Seq.slice v (SZ.v off1) (Seq.length v) `Seq.equal`
                    Seq.append (serialize_cbor key) (serialize_cbor value)));
      Seq.lemma_split v (SZ.v off1);
      assert (pure (Seq.equal v
                    (serialize_cbor_map (List.Tot.append l1 [(Ghost.reveal key, Ghost.reveal value)]))));
      assert (pure (v ==
                    serialize_cbor_map (List.Tot.append l1 [(Ghost.reveal key, Ghost.reveal value)])));
      cbor_raw_map_insert_post_intro_some m (Ghost.reveal key) (Ghost.reveal value) true v
        (List.Tot.append l1 [(Ghost.reveal key, Ghost.reveal value)]);
      true
    }
  }
}

#pop-options

module CDDL.Pulse.Serialize.Gen.ArrayGroup
include CDDL.Pulse.Serialize.Gen.Base
include CDDL.Pulse.Parse.ArrayGroup
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base

let rec cbor_parse_list (p: bare_cbor_parser) (n: nat) (x: Seq.seq U8.t) : Pure (option (list cbor & nat))
  (requires True)
  (ensures (fun res -> match res with
  | None -> True
  | Some (res, n) -> n <= Seq.length x /\ (Cons? res <==> n > 0)
  ))
  (decreases n)
= if n = 0
  then Some ([], 0)
  else match p x with
  | None -> None
  | Some (a, na) ->
    match cbor_parse_list p (n - 1) (Seq.slice x na (Seq.length x)) with
    | None -> None
    | Some (q, nq) -> Some (a :: q, na + nq)

let rec cbor_parse_list_prefix (p: cbor_parser) (n: nat) (x1 x2: Seq.seq U8.t) : Lemma
  (ensures (match cbor_parse_list p n x1 with
  | None -> True
  | Some (_, n1) -> (n1 <= Seq.length x2 /\ Seq.slice x1 0 n1 == Seq.slice x2 0 n1) ==> cbor_parse_list p n x2 == cbor_parse_list p n x1
  ))
  (decreases n)
= if n = 0
  then ()
  else match p x1 with
  | None -> ()
  | Some (_, na) ->
    let x1' = Seq.slice x1 na (Seq.length x1) in
    match cbor_parse_list p (n - 1) x1' with
    | None -> ()
    | Some (_, nq) ->
      let n1 = na + nq in
      if n1 <= Seq.length x2 && Seq.slice x1 0 n1 = Seq.slice x2 0 n1
      then begin
        Seq.slice_slice x1 0 n1 0 na;
        Seq.slice_slice x2 0 n1 0 na;
        assert (cbor_parse_prefix_prop' p x1 x2);
        assert (Seq.slice x1 0 na == Seq.slice x2 0 na);
        assert (Seq.length x2 >= na);
        assert (p x1 == p x2);
        Seq.slice_slice x1 0 n1 na n1;
        Seq.slice_slice x2 0 n1 na n1;
        assert (Seq.slice x1' 0 nq == Seq.slice x1 na n1);
        let x2' = Seq.slice x2 na (Seq.length x2) in
        assert (Seq.slice x2' 0 nq == Seq.slice x2 na n1);
        assert (Seq.slice x1' 0 nq == Seq.slice x2' 0 nq);
        cbor_parse_list_prefix p (n - 1) x1' (Seq.slice x2 na (Seq.length x2));
        ()
      end
      else ()

let rec cbor_det_parse_list_serialize_list (l: list Cbor.cbor) : Lemma
  (ensures cbor_parse_list cbor_det_parse (List.Tot.length l) (Cbor.cbor_det_serialize_list l) == Some (l, Seq.length (Cbor.cbor_det_serialize_list l)))
  (decreases l)
= match l with
  | [] ->
    Cbor.cbor_det_serialize_list_nil ();
    ()
  | a :: q ->
    Cbor.cbor_det_serialize_list_cons a q;
    cbor_det_parse_list_serialize_list q;
    let s = Cbor.cbor_det_serialize_list l in
    let n1 = Seq.length (Cbor.cbor_det_serialize a) in
    assert (Seq.equal (Seq.slice s n1 (Seq.length s)) (Cbor.cbor_det_serialize_list q));
    Cbor.cbor_det_serialize_parse a;
    Cbor.cbor_det_parse_prefix (Cbor.cbor_det_serialize a) (Cbor.cbor_det_serialize_list l);
    ()

let rec cbor_det_serialize_list_parse_list (n: nat) (s: Seq.seq U8.t) : Lemma
  (ensures (match cbor_parse_list cbor_det_parse n s with
  | None -> True
  | Some (l, len) -> n == List.Tot.length l /\
    Seq.slice s 0 len == Cbor.cbor_det_serialize_list l
  ))
  (decreases n)
= if n = 0
  then
    Cbor.cbor_det_serialize_list_nil ()
  else match cbor_det_parse s with
  | None -> ()
  | Some (a, len1) ->
    let s' = (Seq.slice s len1 (Seq.length s))  in
    match cbor_parse_list cbor_det_parse (n - 1) s' with
    | None -> ()
    | Some (q, len2) ->
      Cbor.cbor_det_serialize_list_cons a q;
      cbor_det_serialize_list_parse_list (n - 1) s';
      let len = len1 + len2 in
      assert (Seq.slice s 0 len `Seq.equal` Cbor.cbor_det_serialize_list (a :: q));
      ()

let cbor_det_parse_list_serialize_list_equiv (n: nat) (s: Seq.seq U8.t) (l: list cbor) (len: nat) : Lemma
  (cbor_parse_list cbor_det_parse n s == Some (l, len) <==> (n == List.Tot.length l /\ len <= Seq.length s /\ Seq.slice s 0 len == Cbor.cbor_det_serialize_list l))
= 
  if cbor_parse_list cbor_det_parse n s = Some (l, len)
  then begin
    cbor_det_serialize_list_parse_list n s;
    ()
  end
  else if (n = List.Tot.length l && len <= Seq.length s && Seq.slice s 0 len = Cbor.cbor_det_serialize_list l)
  then begin
    cbor_det_parse_list_serialize_list l;
    cbor_parse_list_prefix cbor_det_parse n (Seq.slice s 0 len) s;
    ()
  end
  else ()

let cbor_array_min_length
  (#p: cbor_parser)
  (ml: cbor_min_length p)
  (l: list cbor)
: Tot nat
= CBOR.Spec.Util.list_sum ml l

let rec cbor_array_max_length
  (#p: cbor_parser)
  (ml: cbor_max_length p)
  (l: list cbor)
: Tot (option nat)
  (decreases l)
= match l with
  | [] -> Some 0
  | a :: q ->
    match ml a with
    | None -> None
    | Some na ->
      match cbor_array_max_length ml q with
      | None -> None
      | Some nq -> Some (na + nq)

let impl_serialize_array_group_pre
  (p: cbor_parser)
  (count: U64.t)
  (size: SZ.t)
  (l: list Cbor.cbor)
  (w: Seq.seq U8.t)
: Tot prop
= List.Tot.length l == U64.v count /\
  SZ.v size <= Seq.length w /\
  cbor_parse_list p (U64.v count) (Seq.slice w 0 (SZ.v size)) == Some (l, SZ.v size)

let impl_serialize_array_group_requires
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (s: ag_spec t tgt inj)
  (v: tgt)
: Tot bool
= s.ag_serializable v &&
  FStar.UInt.fits (List.Tot.length l + List.Tot.length (s.ag_serializer v)) 64

let impl_serialize_array_group_valid
  (#p: cbor_parser)
  (f: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (s: ag_spec t tgt inj)
  (v: tgt)
  (len: nat)
: Tot bool
= impl_serialize_array_group_requires l s v &&
  Some? (cbor_array_max_length f (s.ag_serializer v)) &&
  len >= Some?.v (cbor_array_max_length f (s.ag_serializer v))

let impl_serialize_array_group_invalid
  (#p: cbor_parser)
  (f: cbor_min_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (s: ag_spec t tgt inj)
  (v: tgt)
  (len: nat)
: Tot bool
= impl_serialize_array_group_requires l s v &&
  len < (cbor_array_min_length f (s.ag_serializer v))

let impl_serialize_array_group_post
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (count: U64.t)
  (size: SZ.t)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (s: ag_spec t tgt inj)
  (v: tgt)
  (w: Seq.seq U8.t)
  (res: bool)
: Tot prop
= (impl_serialize_array_group_valid lmax l s v (Seq.length w) ==> res == true) /\
  (impl_serialize_array_group_invalid lmin l s v (Seq.length w) ==> res == false) /\
  (res == true ==> (
    impl_serialize_array_group_requires l s v /\
    impl_serialize_array_group_pre p count size (List.Tot.append l (s.ag_serializer v)) w
  ))

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
    (#t: array_group None)
    (#tgt: Type0)
    (#inj: bool)
    (s: ag_spec t tgt inj)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
  (c: impl_tgt) ->
  (#v: Ghost.erased tgt) ->
  (out: S.slice U8.t) ->
  (out_count: R.ref U64.t) ->
  (out_size: R.ref SZ.t) ->
  (l: Ghost.erased (list Cbor.cbor)) ->
  stt bool
    (exists* w count size . r c v ** pts_to out w ** pts_to out_count count ** pts_to out_size size **
      pure (impl_serialize_array_group_pre p count size l w)
    )
    (fun res -> exists* w count' size' . r c v ** pts_to out w ** pts_to out_count count' ** pts_to out_size size' ** pure (
      impl_serialize_array_group_post lmin lmax count' size' l s v w res
    ))

let impl_serialize_array_group_t_eq
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
    (#t: array_group None)
    (#tgt: Type0)
    (#inj: bool)
    (s: ag_spec t tgt inj)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
    (impl_tgt2: Type0)
    (ieq: squash (impl_tgt == impl_tgt2))
: Tot (squash (impl_serialize_array_group lmin lmax s #impl_tgt r == impl_serialize_array_group lmin lmax s #impl_tgt2 (coerce_rel r impl_tgt2 ieq)))
= ()

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_det_serialize_array
   (cbor_det_serialize_array: cbor_det_serialize_array_t)
    (# [@@@erasable] t: Ghost.erased (array_group None))
    (# [@@@erasable] tgt: Type0)
    (# [@@@erasable] inj: Ghost.erased bool)
    (# [@@@erasable] s: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (# [@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_array_group cbor_det_min_length cbor_det_max_length s r)
: impl_serialize #_ cbor_det_min_length cbor_det_max_length #_ #_ #_ (spec_array_group s) #_ r

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_ext
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_array_group lmin lmax ps r)
    (#[@@@erasable]t': Ghost.erased (array_group None))
    (#[@@@erasable] inj': Ghost.erased bool)
    ([@@@erasable]ps': Ghost.erased (ag_spec t' tgt inj'))
    ([@@@erasable]sq: squash (
      (Ghost.reveal inj == true \/ Ghost.reveal inj' == true) /\
      array_group_equiv t' t /\
      (forall (x: list cbor) . array_group_parser_spec_refinement (Ghost.reveal t') x ==> ((ps'.ag_parser x <: tgt) == ps.ag_parser x))
    ))
: impl_serialize_array_group lmin lmax #(Ghost.reveal t') #tgt #inj' (Ghost.reveal ps') #impl_tgt r

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_bij
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_array_group lmin lmax ps r)
    (#[@@@erasable]tgt' : Type0)
    ([@@@erasable]f12: Ghost.erased (tgt -> tgt'))
    ([@@@erasable]f21: Ghost.erased (tgt' -> tgt))
    ([@@@erasable]fprf_21_12: (x: tgt) -> squash (Ghost.reveal f21 (Ghost.reveal f12 x) == x))
    ([@@@erasable]fprf_12_21: (x: tgt') -> squash (Ghost.reveal f12 (Ghost.reveal f21 x) == x))
    (#impl_tgt' : Type0)
    (g12: (impl_tgt -> impl_tgt'))
    (g21: (impl_tgt' -> impl_tgt))
    ([@@@erasable]gprf_21_12: (x: impl_tgt) -> squash (g21 (g12 x) == x))
    ([@@@erasable]gprf_12_21: (x: impl_tgt') -> squash (g12 (g21 x) == x))
: impl_serialize_array_group lmin lmax #(Ghost.reveal t) #tgt' #inj (ag_spec_inj ps f12 f21 fprf_21_12 fprf_12_21) #impl_tgt' (rel_fun r g21 f21)

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_item
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize lmin lmax ps r)
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_item ps) #_ r

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_concat
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (ag_spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_array_group lmin lmax ps2 r2)
    (sq: squash (
      array_group_concat_unique_weak t1 t2
    ))
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_concat ps1 ps2) #_ (rel_pair r1 r2)

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_choice
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (ag_spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_array_group lmin lmax ps2 r2)
    (sq: squash (
      array_group_disjoint t1 t2
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_choice ps1 ps2) #_ (rel_either r1 r2)

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_choice'
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (ag_spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_array_group lmin lmax ps2 r2)
    (sq: squash (
      array_group_disjoint t1 (close_array_group t2)
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_choice' ps1 ps2) #_ (rel_either r1 r2)

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_zero_or_one
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_zero_or_one ps1) #_ (rel_option r1)

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_zero_or_more
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type)
  (#[@@@erasable]cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_zero_or_more ps1) #_ (rel_either_left (rel_slice_of_list r1 false) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1)))

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_one_or_more
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type)
  (#[@@@erasable]cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group #_ lmin lmax #_ #_ #_ (ag_spec_one_or_more ps1) #_ (rel_either_left (rel_slice_of_list r1 false) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1)))

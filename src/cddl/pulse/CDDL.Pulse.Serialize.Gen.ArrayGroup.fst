module CDDL.Pulse.Serialize.Gen.ArrayGroup
#lang-pulse
module SM = Pulse.Lib.SeqMatch.Util
module GR = Pulse.Lib.GhostReference

(* Helper lemmas *)

let rec cbor_parse_list_snoc
  (p: cbor_parser)
  (n: nat)
  (s: Seq.seq U8.t)
: Lemma
  (requires (
    Some? (cbor_parse_list p n s) /\
    (let Some (l, n_bytes) = cbor_parse_list p n s in
     n_bytes <= Seq.length s /\
     Some? (p (Seq.slice s n_bytes (Seq.length s))))
  ))
  (ensures (
    let Some (l, n_bytes) = cbor_parse_list p n s in
    let Some (x, m) = p (Seq.slice s n_bytes (Seq.length s)) in
    cbor_parse_list p (n + 1) s == Some (List.Tot.append l [x], n_bytes + m)
  ))
  (decreases n)
= if n = 0
  then
    Seq.lemma_eq_elim (Seq.slice s 0 (Seq.length s)) s
  else
    match p s with
    | None -> ()
    | Some (a, na) ->
      let s' = Seq.slice s na (Seq.length s) in
      match cbor_parse_list p (n - 1) s' with
      | None -> ()
      | Some (q, nq) ->
        Seq.slice_slice s na (Seq.length s) nq (Seq.length s - na);
        cbor_parse_list_snoc p (n - 1) s'

let rec cbor_array_max_length_append
  (#p: cbor_parser)
  (f: cbor_max_length p)
  (l1 l2: list cbor)
: Lemma
  (ensures (
    match cbor_array_max_length f l1, cbor_array_max_length f l2 with
    | Some n1, Some n2 -> cbor_array_max_length f (List.Tot.append l1 l2) == Some (n1 + n2)
    | None, _ -> cbor_array_max_length f (List.Tot.append l1 l2) == None
    | _, None -> cbor_array_max_length f (List.Tot.append l1 l2) == None
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a :: q -> cbor_array_max_length_append f q l2

let cbor_array_min_length_append
  (#p: cbor_parser)
  (f: cbor_min_length p)
  (l1 l2: list cbor)
: Lemma
  (ensures (cbor_array_min_length f (List.Tot.append l1 l2) == cbor_array_min_length f l1 + cbor_array_min_length f l2))
= CBOR.Spec.Util.list_sum_append f l1 l2

inline_for_extraction noextract [@@noextract_to "krml";
  FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
]
let pow2_64_m1 : U64.t = U64.uint_to_t (pow2 64 - 1)

let pow2_64_m1_eq : squash (U64.v pow2_64_m1 == pow2 64 - 1) = _ by (
  FStar.Tactics.norm [delta; zeta; iota; primops];
  FStar.Tactics.trefl ()
)

let list_append_length_pat
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (List.Tot.length (List.Tot.append l1 l2) == List.Tot.length l1 + List.Tot.length l2)
  [SMTPat (List.Tot.append l1 l2)]
= List.Tot.append_length l1 l2

let list_append_assoc_pat
  (#t: Type)
  (l1 l2 l3: list t)
: Lemma
  (ensures (List.Tot.append l1 (List.Tot.append l2 l3) == List.Tot.append (List.Tot.append l1 l2) l3))
  [SMTPatOr [
    [SMTPat (List.Tot.append l1 (List.Tot.append l2 l3))];
    [SMTPat (List.Tot.append (List.Tot.append l1 l2) l3)];
  ]]
= List.Tot.append_assoc l1 l2 l3

let list_append_nil_r_pat
  (#t: Type)
  (l1: list t)
: Lemma
  (List.Tot.append l1 [] == l1)
  [SMTPat (List.Tot.append l1 [])]
= List.Tot.append_l_nil l1

(* Parse list lemmas *)

#push-options "--z3rlimit_factor 32 --fuel 2 --ifuel 1"

let rec cbor_parse_list_split
  (p: cbor_parser)
  (n1 n2: nat)
  (s: Seq.seq U8.t)
: Lemma
  (requires (
    Some? (cbor_parse_list p n1 s) /\
    (let Some (_, pos1) = cbor_parse_list p n1 s in pos1 <= Seq.length s)
  ))
  (ensures (
    let Some (l1, pos1) = cbor_parse_list p n1 s in
    cbor_parse_list p (n1 + n2) s ==
    (match cbor_parse_list p n2 (Seq.slice s pos1 (Seq.length s)) with
     | None -> None
     | Some (l2, pos2) -> Some (List.Tot.append l1 l2, pos1 + pos2))
  ))
  (decreases n1)
= if n1 = 0
  then begin
    Seq.lemma_eq_elim (Seq.slice s 0 (Seq.length s)) s;
    match cbor_parse_list p n2 s with
    | None -> ()
    | Some _ -> ()
  end
  else match p s with
  | None -> ()
  | Some (x, nx) ->
    let s' = Seq.slice s nx (Seq.length s) in
    match cbor_parse_list p (n1 - 1) s' with
    | None -> ()
    | Some (l1', pos1') ->
      assert (pos1' <= Seq.length s');
      cbor_parse_list_split p (n1 - 1) n2 s';
      Seq.slice_slice s nx (Seq.length s) pos1' (Seq.length s - nx);
      assert (Seq.slice s' pos1' (Seq.length s') == Seq.slice s (nx + pos1') (Seq.length s));
      assert (n1 - 1 + n2 == n1 + n2 - 1);
      match cbor_parse_list p n2 (Seq.slice s' pos1' (Seq.length s')) with
      | None -> ()
      | Some (l2, pos2) -> ()

let rec cbor_parse_list_max_length
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (n: nat)
  (s: Seq.seq U8.t)
: Lemma
  (ensures (match cbor_parse_list p n s with
  | None -> True
  | Some (l, pos) ->
    match cbor_array_max_length lmax l with
    | None -> True
    | Some max -> pos <= max
  ))
  (decreases n)
= if n = 0 then ()
  else match p s with
  | None -> ()
  | Some (x, nx) ->
    let s' = Seq.slice s nx (Seq.length s) in
    cbor_parse_list_max_length lmax (n - 1) s';
    match cbor_parse_list p (n - 1) s' with
    | None -> ()
    | Some (l', pos') ->
      match lmax x, cbor_array_max_length lmax l' with
      | Some nx_max, Some max' ->
        assert (cbor_max_length_prop p lmax);
        assert (nx <= nx_max)
      | _ -> ()

let rec cbor_parse_list_min_length
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (n: nat)
  (s: Seq.seq U8.t)
: Lemma
  (ensures (match cbor_parse_list p n s with
  | None -> True
  | Some (l, pos) -> pos >= cbor_array_min_length lmin l
  ))
  (decreases n)
= if n = 0 then ()
  else match p s with
  | None -> ()
  | Some (x, nx) ->
    let s' = Seq.slice s nx (Seq.length s) in
    cbor_parse_list_min_length lmin (n - 1) s';
    match cbor_parse_list p (n - 1) s' with
    | None -> ()
    | Some (l', pos') ->
      assert (cbor_min_length_prop p lmin);
      assert (nx >= lmin x)

let rec cbor_parse_list_prefix_of_concat
  (p: cbor_parser)
  (n1 n2: nat)
  (s: Seq.seq U8.t)
: Lemma
  (ensures (
    match cbor_parse_list p (n1 + n2) s with
    | None -> True
    | Some _ ->
      Some? (cbor_parse_list p n1 s) /\
      (let Some (l1, pos1) = cbor_parse_list p n1 s in
       let Some (_, pos) = cbor_parse_list p (n1 + n2) s in
       pos1 <= pos)
  ))
  (decreases n1)
= if n1 = 0 then ()
  else match p s with
  | None -> ()
  | Some (x, nx) ->
    cbor_parse_list_prefix_of_concat p (n1 - 1) n2 (Seq.slice s nx (Seq.length s))

#pop-options

let cbor_parse_list_bounds
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (n: nat)
  (s: Seq.seq U8.t)
: Lemma
  (ensures (match cbor_parse_list p n s with
  | None -> True
  | Some (l, pos) ->
    pos >= cbor_array_min_length lmin l /\
    (match cbor_array_max_length lmax l with
     | None -> True
     | Some max -> pos <= max)
  ))
= cbor_parse_list_max_length lmax n s;
  cbor_parse_list_min_length lmin n s

let impl_serialize_array_group_size_before_le_size1
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (#t1: array_group None) (#tgt1: Type0) (#inj1: bool)
  (ps1: ag_spec t1 tgt1 inj1)
  (l: list Cbor.cbor)
  (v1: tgt1)
  (count0: U64.t) (count1: U64.t) (size1: SZ.t) (size_before: SZ.t)
  (w0 w1: Seq.seq U8.t)
: Lemma
  (requires (
    impl_serialize_array_group_pre p count0 size_before l w0 /\
    Seq.length w0 == Seq.length w1 /\
    impl_serialize_array_group_post lmin lmax count1 size1 size_before l ps1 v1 w0 w1 true
  ))
  (ensures (
    SZ.v size_before <= SZ.v size1
  ))
= let ser1 = ps1.ag_serializer v1 in
  let n1 = List.Tot.length ser1 in
  assert (U64.v count1 == List.Tot.length l + n1);
  list_append_length_pat l ser1;
  cbor_parse_list_prefix_of_concat p (U64.v count0) n1 (Seq.slice w1 0 (SZ.v size1));
  let Some (l', pos1') = cbor_parse_list p (U64.v count0) (Seq.slice w1 0 (SZ.v size1)) in
  assert (pos1' <= SZ.v size1);
  assert (Seq.equal (Seq.slice w0 0 (SZ.v size_before)) (Seq.slice w1 0 (SZ.v size_before)));
  Seq.slice_slice w1 0 (SZ.v size_before) 0 (SZ.v size_before);
  if SZ.v size_before <= SZ.v size1
  then ()
  else begin
    Seq.slice_slice w1 0 (SZ.v size_before) 0 (SZ.v size1);
    cbor_parse_list_prefix p (U64.v count0) (Seq.slice w1 0 (SZ.v size1)) (Seq.slice w1 0 (SZ.v size_before));
    assert (false)
  end

#push-options "--z3rlimit_factor 64 --fuel 2 --ifuel 2"

(* Proves that after serializing with ps1, the bytes consumed
   are bounded by max/min length of the serialized items *)
let impl_serialize_array_group_concat_suffix_bounds
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (#t1: array_group None) (#tgt1: Type0) (#inj1: bool)
  (ps1: ag_spec t1 tgt1 inj1)
  (l: list Cbor.cbor)
  (v1: tgt1)
  (count0: U64.t) (count1: U64.t) (size1: SZ.t) (size_before: SZ.t)
  (w0 w1: Seq.seq U8.t)
: Lemma
  (requires (
    ps1.ag_serializable v1 /\
    impl_serialize_array_group_pre p count0 size_before l w0 /\
    Seq.length w0 == Seq.length w1 /\
    impl_serialize_array_group_post lmin lmax count1 size1 size_before l ps1 v1 w0 w1 true
  ))
  (ensures (
    SZ.v size_before <= SZ.v size1 /\
    SZ.v size1 - SZ.v size_before >= cbor_array_min_length lmin (ps1.ag_serializer v1) /\
    (match cbor_array_max_length lmax (ps1.ag_serializer v1) with
     | None -> True
     | Some max -> SZ.v size1 - SZ.v size_before <= max)
  ))
= impl_serialize_array_group_size_before_le_size1 lmin lmax ps1 l v1 count0 count1 size1 size_before w0 w1;
  let ser1 = ps1.ag_serializer v1 in
  let n1 = List.Tot.length ser1 in
  list_append_length_pat l ser1;
  let s_w1 = Seq.slice w1 0 (SZ.v size1) in
  cbor_parse_list_prefix_of_concat p (U64.v count0) n1 s_w1;
  Seq.slice_slice w1 0 (SZ.v size_before) 0 (SZ.v size_before);
  Seq.slice_slice w1 0 (SZ.v size1) 0 (SZ.v size_before);
  cbor_parse_list_prefix p (U64.v count0) (Seq.slice w1 0 (SZ.v size_before)) s_w1;
  cbor_parse_list_split p (U64.v count0) n1 s_w1;
  let suffix = Seq.slice s_w1 (SZ.v size_before) (Seq.length s_w1) in
  cbor_parse_list_bounds lmin lmax n1 suffix;
  match cbor_parse_list p n1 suffix with
  | None -> ()
  | Some (l2, pos2) ->
    List.Tot.append_inv_head l l2 ser1

#pop-options

(* Concat helpers *)

#push-options "--z3rlimit_factor 64 --fuel 2 --ifuel 2"

let impl_serialize_array_group_concat_false_helper
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (#t1: array_group None) (#tgt1: Type0) (#inj1: bool)
  (ps1: ag_spec t1 tgt1 inj1)
  (#t2: array_group None) (#tgt2: Type0) (#inj2: bool)
  (ps2: ag_spec t2 tgt2 inj2 { array_group_concat_unique_weak t1 t2 })
  (l: list Cbor.cbor)
  (v: (tgt1 & tgt2))
  (count: U64.t) (size: SZ.t) (size_before: SZ.t)
  (w0 w: Seq.seq U8.t)
: Lemma
  (requires (
    impl_serialize_array_group_post lmin lmax count size size_before l ps1 (fst v) w0 w false
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_concat ps1 ps2) v w0 w false
  ))
= let ps = ag_spec_concat ps1 ps2 in
  if ps.ag_serializable v
  then begin
    cbor_array_max_length_append lmax (ps1.ag_serializer (fst v)) (ps2.ag_serializer (snd v));
    cbor_array_min_length_append lmin (ps1.ag_serializer (fst v)) (ps2.ag_serializer (snd v));
    list_append_length_pat (ps1.ag_serializer (fst v)) (ps2.ag_serializer (snd v))
  end

let impl_serialize_array_group_concat_true_helper
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (#t1: array_group None) (#tgt1: Type0) (#inj1: bool)
  (ps1: ag_spec t1 tgt1 inj1)
  (#t2: array_group None) (#tgt2: Type0) (#inj2: bool)
  (ps2: ag_spec t2 tgt2 inj2 { array_group_concat_unique_weak t1 t2 })
  (l: list Cbor.cbor)
  (v: (tgt1 & tgt2))
  (count0: U64.t)
  (count1: U64.t) (size1: SZ.t) (size_before: SZ.t)
  (w0 w1: Seq.seq U8.t)
  (count2: U64.t) (size2: SZ.t)
  (w2: Seq.seq U8.t)
  (res2: bool)
: Lemma
  (requires (
    impl_serialize_array_group_pre p count0 size_before l w0 /\
    Seq.length w0 == Seq.length w1 /\
    Seq.length w1 == Seq.length w2 /\
    impl_serialize_array_group_post lmin lmax count1 size1 size_before l ps1 (fst v) w0 w1 true /\
    impl_serialize_array_group_post lmin lmax count2 size2 size1 (List.Tot.append l (ps1.ag_serializer (fst v))) ps2 (snd v) w1 w2 res2
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax count2 size2 size_before l (ag_spec_concat ps1 ps2) v w0 w2 res2
  ))
= let ps = ag_spec_concat ps1 ps2 in
  impl_serialize_array_group_size_before_le_size1 lmin lmax ps1 l (fst v) count0 count1 size1 size_before w0 w1;
  (* Part 3: prefix preservation w0 -> w2 via w1 *)
  Seq.slice_slice w2 0 (SZ.v size1) 0 (SZ.v size_before);
  Seq.slice_slice w1 0 (SZ.v size1) 0 (SZ.v size_before);
  (* valid/invalid implications for concat *)
  if ps.ag_serializable v
  then begin
    let ser1 = ps1.ag_serializer (fst v) in
    let ser2 = ps2.ag_serializer (snd v) in
    cbor_array_max_length_append lmax ser1 ser2;
    cbor_array_min_length_append lmin ser1 ser2;
    list_append_length_pat ser1 ser2;
    list_append_length_pat l (ps.ag_serializer v);
    list_append_length_pat l ser1;
    List.Tot.append_assoc l ser1 ser2;
    impl_serialize_array_group_concat_suffix_bounds lmin lmax ps1 l (fst v) count0 count1 size1 size_before w0 w1
  end;
  (* Part 4: res2 == true ==> concat requirements *)
  if res2
  then begin
    let ser1 = ps1.ag_serializer (fst v) in
    let ser2 = ps2.ag_serializer (snd v) in
    list_append_length_pat l ser1;
    List.Tot.append_assoc l ser1 ser2
  end

#pop-options

(* impl_det_serialize_array *)

let rec cbor_array_max_length_det_eq
  (l: list Cbor.cbor)
: Lemma
  (ensures cbor_array_max_length cbor_det_max_length l == Some (Seq.length (Cbor.cbor_det_serialize_list l)))
  (decreases l)
= match l with
  | [] -> Cbor.cbor_det_serialize_list_nil ()
  | hd :: tl ->
    cbor_array_max_length_det_eq tl;
    Cbor.cbor_det_serialize_list_cons hd tl

let impl_det_serialize_array_false_helper
  (#t: array_group None) (#tgt: Type0) (#inj: bool)
  (s: ag_spec t tgt inj)
  (v: tgt)
  (count: U64.t) (size: SZ.t) (w0 w: Seq.seq U8.t)
: Lemma
  (requires (
    impl_serialize_array_group_post cbor_det_min_length cbor_det_max_length count size 0sz [] s v w0 w false
  ))
  (ensures (
    impl_serialize_post cbor_det_min_length cbor_det_max_length (spec_array_group s) v w 0sz
  ))
= if (spec_array_group s).serializable v
  then begin
    cbor_array_max_length_det_eq (s.ag_serializer v);
    Classical.forall_intro (Classical.move_requires Cbor.cbor_det_serialize_array_length_gt_list)
  end

let impl_det_serialize_array_true_helper
  (#t: array_group None) (#tgt: Type0) (#inj: bool)
  (s: ag_spec t tgt inj)
  (v: tgt)
  (count: U64.t) (size: SZ.t) (w0 w: Seq.seq U8.t)
  (res: SZ.t)
  (w': Seq.seq U8.t)
: Lemma
  (requires (
    impl_serialize_array_group_post cbor_det_min_length cbor_det_max_length count size 0sz [] s v w0 w true /\
    CBOR.Pulse.API.Base.cbor_det_serialize_array_postcond (s.ag_serializer v) res w'
  ))
  (ensures (
    impl_serialize_post cbor_det_min_length cbor_det_max_length (spec_array_group s) v w' res
  ))
= if SZ.v res > 0
  then begin
    cbor_det_parse_equiv (Seq.slice w' 0 (SZ.v res)) (Cbor.pack (Cbor.CArray (s.ag_serializer v))) (SZ.v res);
    ()
  end

#push-options "--z3rlimit_factor 16 --fuel 1 --ifuel 1"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_det_serialize_array
   (cbor_det_serialize_array: cbor_det_serialize_array_t)
    (# [@@@erasable] t: Ghost.erased (array_group None))
    (# [@@@erasable] tgt: Type0)
    (# [@@@erasable] inj: Ghost.erased bool)
    (# [@@@erasable] s: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (# [@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_array_group cbor_det_min_length cbor_det_max_length s r)
: impl_serialize #_ cbor_det_min_length cbor_det_max_length #_ #_ #_ (spec_array_group s) #_ r
=
  (c: _)
  (#v: _)
  (out: _)
{
  let mut pcount = 0uL;
  let mut psize = 0sz;
  Cbor.cbor_det_serialize_list_nil ();
  with w0 . assert (pts_to out w0);
  let res = i c out pcount psize [];
  if (res) {
    let size = !psize;
    let count = !pcount;
    with w . assert (pts_to out w);
    cbor_det_serialize_list_parse_list (U64.v count) (Seq.slice w 0 (SZ.v size));
    Classical.forall_intro (Classical.move_requires Cbor.cbor_det_serialize_array_length_gt_list);
    let res2 = cbor_det_serialize_array count out (s.ag_serializer v) size;
    with w' . assert (pts_to out w');
    impl_det_serialize_array_true_helper s v count size w0 w res2 w';
    res2
  } else {
    with w . assert (pts_to out w);
    with count . assert (pts_to pcount count);
    with size . assert (pts_to psize size);
    impl_det_serialize_array_false_helper s v count size w0 w;
    0sz
  }
}

#pop-options

(* impl_serialize_array_group_ext *)

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 2"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_ext
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
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  i c out out_count out_size l
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_bij
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
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  let c' = g21 c;
  Trade.rewrite_with_trade
    (rel_fun r g21 f21 c v)
    (r c' (Ghost.reveal f21 v));
  let res = i c' #(Ghost.reveal f21 v) out out_count out_size l;
  Trade.elim _ _;
  res
}

let seq_slice_append
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures
    Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1 /\
    Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2) `Seq.equal` s2
  )
= ()

#push-options "--fuel 2 --ifuel 2"

let impl_serialize_array_group_item_correct
    (#p: cbor_parser)
    (lmin: cbor_min_length p)
    (lmax: cbor_max_length p)
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (ps: spec t tgt inj)
    (v: tgt)
: Lemma
  (
    (ps.serializable v ==> (
      cbor_array_max_length lmax ((ag_spec_item ps).ag_serializer v) == lmax (ps.serializer v) /\
      cbor_array_min_length lmin ((ag_spec_item ps).ag_serializer v) == lmin (ps.serializer v)
    ))
  )
= ()

#pop-options

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1 --split_queries always"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_item
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
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  assume (pure (SZ.fits_u64));
  let count = !out_count;
  if (U64.lt count pow2_64_m1) {
    let size = !out_size;
    with w . assert (pts_to out w);
    S.pts_to_len out;
    Seq.lemma_split w (SZ.v size);
    let (out0, out1) = S.split out size;
    S.pts_to_len out1;
    let size1 = i c out1;
    with w1 . assert (pts_to out1 w1);
    S.pts_to_len out1;
    seq_slice_append (Seq.slice w 0 (SZ.v size)) w1;
    S.join _ _ out;
    with w_new . assert (pts_to out w_new);
    S.pts_to_len out;
    impl_serialize_array_group_item_correct lmin lmax ps v;
    if (size1 = 0sz) {
      false
    } else {
      Seq.lemma_eq_elim (Seq.slice w_new 0 (SZ.v size)) (Seq.slice w 0 (SZ.v size));
      Seq.lemma_eq_elim (Seq.slice w_new (SZ.v size) (SZ.v size + Seq.length w1)) w1;
      Seq.slice_slice w_new 0 (SZ.v size + SZ.v size1) 0 (SZ.v size);
      Seq.slice_slice w_new 0 (SZ.v size + SZ.v size1) (SZ.v size) (SZ.v size + SZ.v size1);
      Seq.slice_slice w_new (SZ.v size) (SZ.v size + Seq.length w1) 0 (SZ.v size1);
      cbor_parse_list_prefix p (U64.v count) (Seq.slice w 0 (SZ.v size)) (Seq.slice w_new 0 (SZ.v size + SZ.v size1));
      cbor_parse_list_snoc p (U64.v count) (Seq.slice w_new 0 (SZ.v size + SZ.v size1));
      list_append_length_pat l ((ag_spec_item ps).ag_serializer v);
      out_count := U64.add count 1uL;
      out_size := SZ.add size size1;
      true
    }
  } else {
    false
  }
}

#pop-options

#push-options "--z3rlimit_factor 32 --fuel 2 --ifuel 2"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_concat
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
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  norewrite let (c1, c2) = c;
  Trade.rewrite_with_trade (rel_pair r1 r2 c v) (r1 c1 (fst v) ** r2 c2 (snd v));
  let count0 = R.read out_count;
  S.pts_to_len out;
  let res1 = i1 c1 out out_count out_size l;
  S.pts_to_len out;
  if (res1) {
    with w1 . assert (pts_to out w1);
    with count1 . assert (pts_to out_count count1);
    with size1_val . assert (pts_to out_size size1_val);
    S.pts_to_len out;
    let res2 = i2 c2 out out_count out_size (List.Tot.append l (ps1.ag_serializer (fst v)));
    with w2 . assert (pts_to out w2);
    with count2 . assert (pts_to out_count count2);
    with size2_val . assert (pts_to out_size size2_val);
    Trade.elim _ _;
    S.pts_to_len out;
    assert (pure (Seq.length w0 == Seq.length w1));
    assert (pure (Seq.length w1 == Seq.length w2));
    impl_serialize_array_group_concat_true_helper lmin lmax ps1 ps2 l v count0 count1 size1_val size_before w0 w1 count2 size2_val w2 res2;
    res2
  } else {
    with w1 . assert (pts_to out w1);
    with count1 . assert (pts_to out_count count1);
    with size1_val . assert (pts_to out_size size1_val);
    Trade.elim _ _;
    impl_serialize_array_group_concat_false_helper lmin lmax ps1 ps2 l v count1 size1_val size_before w0 w1;
    false
  }
}

#pop-options

(* impl_serialize_array_group_choice *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_choice
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
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  rel_either_cases r1 r2 c v;
  match c {
    norewrite
    Inl c1 -> {
      Trade.rewrite_with_trade (rel_either r1 r2 c v) (r1 c1 (Inl?.v v));
      let res = i1 c1 out out_count out_size l;
      Trade.elim _ _;
      res
    }
    norewrite
    Inr c2 -> {
      Trade.rewrite_with_trade (rel_either r1 r2 c v) (r2 c2 (Inr?.v v));
      let res = i2 c2 out out_count out_size l;
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_close_intro
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
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_close_intro ps1) #_ r1
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  i1 c out out_count out_size l
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_close_elim
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec (close_array_group t1) tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group lmin lmax ps1 r1)
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_close_elim ps1) #_ r1
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  i1 c out out_count out_size l
}

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_ext'
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
    ([@@@erasable]t': Ghost.erased (array_group None))
    ([@@@erasable]sq: squash (
      array_group_equiv t' t
    ))
: impl_serialize_array_group lmin lmax #(Ghost.reveal t') #tgt #inj (ag_spec_ext ps t') #impl_tgt r
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  i c out out_count out_size l
}

#pop-options

(* impl_serialize_array_group_choice' *)

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_choice'
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
= impl_serialize_array_group_close_elim
    (impl_serialize_array_group_ext'
      (impl_serialize_array_group_close_intro
        (impl_serialize_array_group_choice
          i1
          (impl_serialize_array_group_close_intro i2)
          ()
        )
      )
      (close_array_group (array_group_choice t1 t2))
      ()
    )

(* impl_serialize_array_group_zero_or_one *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_zero_or_one
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
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  rel_option_cases r1 c v;
  match c {
    norewrite
    Some c1 -> {
      Trade.rewrite_with_trade (rel_option r1 c v) (r1 c1 (Some?.v v));
      let res = i1 c1 out out_count out_size l;
      Trade.elim _ _;
      res
    }
    norewrite
    None -> {
      true
    }
  }
}

(* Helpers for zero_or_more *)

let rec ag_spec_zero_or_more_size_append
  (#target: Type)
  (p: target -> nat)
  (l1 l2: list target)
: Lemma
  (ensures (ag_spec_zero_or_more_size p (List.Tot.append l1 l2) == ag_spec_zero_or_more_size p l1 + ag_spec_zero_or_more_size p l2))
  (decreases l1)
= match l1 with
  | [] -> ()
  | hd :: tl -> ag_spec_zero_or_more_size_append p tl l2

#push-options "--fuel 4 --ifuel 4 --z3rlimit_factor 4 --split_queries always"
#restart-solver
let rec ag_spec_zero_or_more_serializer_append
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (ps1: (ag_spec source target inj) {
    array_group_concat_unique_strong source source
  })
  (l1 l2: list target)
: Lemma
  (requires (
    ag_spec_zero_or_more_serializable ps1.ag_serializable l1 /\
    ag_spec_zero_or_more_serializable ps1.ag_serializable l2
  ))
  (ensures (
    ag_spec_zero_or_more_serializable ps1.ag_serializable l1 /\
    ag_spec_zero_or_more_serializable ps1.ag_serializable l2 /\
    ag_spec_zero_or_more_serializable ps1.ag_serializable (List.Tot.append l1 l2) /\
    (ag_spec_zero_or_more ps1).ag_serializer (List.Tot.append l1 l2) ==
      List.Tot.append
        ((ag_spec_zero_or_more ps1).ag_serializer l1)
        ((ag_spec_zero_or_more ps1).ag_serializer l2)
  ))
  (decreases l1)
= 
  match l1 with
  | [] -> ()
  | hd :: tl ->
    ag_spec_zero_or_more_serializer_append ps1 tl l2
#pop-options

let ag_serializable_zero_or_more_append
    (#t1: (array_group None))
    (#tgt1: Type0)
    (#inj1: bool)
    (ps1: (ag_spec t1 tgt1 inj1))
    (l1 l2: list tgt1)
: Lemma
  (requires (array_group_is_nonempty t1 /\ array_group_concat_unique_strong t1 t1))
  (ensures (
    array_group_is_nonempty t1 /\ array_group_concat_unique_strong t1 t1 /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_size (List.Tot.append l1 l2) == ps.ag_size l1 + ps.ag_size l2 /\
    ps.ag_serializable (List.Tot.append l1 l2) == (ps.ag_serializable l1 && ps.ag_serializable l2)) /\
    ((ps.ag_serializable l1 /\ ps.ag_serializable l2) ==>
      ps.ag_serializer (List.Tot.append l1 l2) == List.Tot.append (ps.ag_serializer l1) (ps.ag_serializer l2)
    )
  )))
= ag_spec_zero_or_more_size_append ps1.ag_size l1 l2;
  List.Tot.for_all_append ps1.ag_serializable l1 l2;
  let ps = ag_spec_zero_or_more ps1 in
  if ps.ag_serializable l1 && ps.ag_serializable l2
  then begin
    ag_spec_zero_or_more_serializer_append ps1 l1 l2
  end;
  ()

#push-options "--z3rlimit_factor 32 --fuel 4 --ifuel 4 --split_queries always"
#restart-solver

let rec ag_spec_zero_or_more_serializer_cons_aux
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (ps1: (ag_spec source target inj) {
    array_group_concat_unique_strong source source
  })
  (l1: list target { (ag_spec_zero_or_more ps1).ag_serializable l1 })
  (l2: list target { (ag_spec_zero_or_more ps1).ag_serializable l2 })
: Lemma
  (ensures (
    let ps = ag_spec_zero_or_more ps1 in
    ps.ag_serializable (List.Tot.append l1 l2) /\
    ps.ag_serializer (List.Tot.append l1 l2) == List.Tot.append (ps.ag_serializer l1) (ps.ag_serializer l2) /\
    (Cons? l1 ==> (
      ps1.ag_serializable (List.Tot.hd l1) /\
      ps.ag_serializable (List.Tot.tl l1) /\
      ps.ag_serializer l1 == List.Tot.append (ps1.ag_serializer (List.Tot.hd l1)) (ps.ag_serializer (List.Tot.tl l1))
    ))
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | hd :: tl ->
    ag_spec_zero_or_more_serializer_cons_aux ps1 tl l2

let ag_spec_zero_or_more_serializer_cons
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (ps1: (ag_spec source target inj) {
    array_group_concat_unique_strong source source
  })
  (x: target)
  (l2: list target)
: Lemma
  (requires (
    let ps = ag_spec_zero_or_more ps1 in
    ps1.ag_serializable x /\
    ps.ag_serializable l2
  ))
  (ensures (
    let ps = ag_spec_zero_or_more ps1 in
    ps.ag_serializable (x :: l2) /\
    ps.ag_serializer (x :: l2) == List.Tot.append (ps1.ag_serializer x) (ps.ag_serializer l2)
  ))
= let ps = ag_spec_zero_or_more ps1 in
  List.Tot.for_all_append ps1.ag_serializable [x] l2;
  ag_spec_zero_or_more_serializer_cons_aux ps1 [x] l2;
  // cons_aux gives: ps.ag_serializer [x] == ps1.ag_serializer x ++ ps.ag_serializer []
  // And: ps.ag_serializer (x :: l2) == ps.ag_serializer [x] ++ ps.ag_serializer l2
  List.Tot.append_l_nil (ps1.ag_serializer x)

#pop-options

(* Helpers for zero_or_more *)

#push-options "--fuel 4 --ifuel 4 --z3rlimit_factor 16"
#restart-solver

let impl_serialize_array_group_valid_zero_or_more_item
  (#p: cbor_parser)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (len: int)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1
  ))))
  (ensures (
    let ps = ag_spec_zero_or_more ps1 in (
    impl_serialize_array_group_valid lmax l ps (List.Tot.append l1 (x :: l2)) len == true ==>
    impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x len == true
  )))
= let ps = ag_spec_zero_or_more ps1 in
  if not (impl_serialize_array_group_valid lmax l ps (List.Tot.append l1 (x :: l2)) len)
  then ()
  else begin
    List.Tot.for_all_append ps1.ag_serializable l1 (x :: l2);
    assert (ps1.ag_serializable x);
    assert (ps.ag_serializable l2);
    ag_serializable_zero_or_more_append ps1 l1 (x :: l2);
    assert (ps.ag_serializable (x :: l2));
    ag_spec_zero_or_more_serializer_append ps1 l1 (x :: l2);
    ag_spec_zero_or_more_serializer_cons ps1 x l2;
    List.Tot.append_length (ps.ag_serializer l1) (ps.ag_serializer (x :: l2));
    List.Tot.append_length (ps1.ag_serializer x) (ps.ag_serializer l2);
    List.Tot.append_length l (ps.ag_serializer (List.Tot.append l1 (x :: l2)));
    List.Tot.append_length l (ps.ag_serializer l1);
    List.Tot.append_length (List.Tot.append l (ps.ag_serializer l1)) (ps1.ag_serializer x);
    cbor_array_max_length_append lmax (ps.ag_serializer l1) (ps.ag_serializer (x :: l2));
    let ser_xcl2 = ps.ag_serializer (x :: l2) in
    let ser_x = ps1.ag_serializer x in
    let ser_l2 = ps.ag_serializer l2 in
    assert (ser_xcl2 == List.Tot.append ser_x ser_l2);
    cbor_array_max_length_append lmax ser_x ser_l2;
    assert (cbor_array_max_length lmax ser_xcl2 == cbor_array_max_length lmax (List.Tot.append ser_x ser_l2));
    assert (Some? (cbor_array_max_length lmax (ps.ag_serializer (List.Tot.append l1 (x :: l2)))));
    assert (Some? (cbor_array_max_length lmax (ps.ag_serializer l1)));
    assert (Some? (cbor_array_max_length lmax ser_xcl2));
    assert (Some? (cbor_array_max_length lmax ser_x));
    assert (Some? (cbor_array_max_length lmax ser_l2));
    let max_x = Some?.v (cbor_array_max_length lmax ser_x) in
    let max_l2v = Some?.v (cbor_array_max_length lmax ser_l2) in
    assert (cbor_array_max_length lmax (List.Tot.append ser_x ser_l2) == Some (max_x + max_l2v));
    let max_xcl2 = Some?.v (cbor_array_max_length lmax ser_xcl2) in
    assert (max_xcl2 == max_x + max_l2v);
    assert (max_xcl2 >= max_x);
    let max_all = Some?.v (cbor_array_max_length lmax (ps.ag_serializer (List.Tot.append l1 (x :: l2)))) in
    let max_l1 = Some?.v (cbor_array_max_length lmax (ps.ag_serializer l1)) in
    assert (max_all == max_l1 + max_xcl2);
    norm_spec [delta_only [`%impl_serialize_array_group_valid; `%impl_serialize_array_group_requires]; iota; zeta] (impl_serialize_array_group_valid lmax l ps (List.Tot.append l1 (x :: l2)) len);
    assert (len >= max_x);
    assert (FStar.UInt.fits (List.Tot.length (List.Tot.append l (ps.ag_serializer l1)) + List.Tot.length (ps1.ag_serializer x)) 64);
    norm_spec [delta_only [`%impl_serialize_array_group_valid; `%impl_serialize_array_group_requires]; iota; zeta] (impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x len);
    ()
  end

let impl_serialize_array_group_post_zero_or_more_extend
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (count: U64.t)
  (size: SZ.t)
  (size_prev: SZ.t)
  (count_prev: U64.t)
  (size_before_overall: SZ.t)
  (w0 w_prev w: Seq.seq U8.t)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    impl_serialize_array_group_pre p count_prev size_prev (List.Tot.append l (ps.ag_serializer l1)) w_prev /\
    Seq.length w_prev == Seq.length w /\
    impl_serialize_array_group_post lmin lmax count size size_prev (List.Tot.append l (ps.ag_serializer l1)) ps1 x w_prev w true /\
    SZ.v size_before_overall <= SZ.v size_prev /\
    Seq.length w0 == Seq.length w_prev /\
    SZ.v size_before_overall <= Seq.length w0 /\
    Seq.equal (Seq.slice w0 0 (SZ.v size_before_overall)) (Seq.slice w_prev 0 (SZ.v size_before_overall))
  ))))
  (ensures (
    let ps = ag_spec_zero_or_more ps1 in
    let l1' = List.Tot.append l1 [x] in (
    ps.ag_serializable l1' /\
    impl_serialize_array_group_pre p count size (List.Tot.append l (ps.ag_serializer l1')) w /\
    SZ.v size_prev <= SZ.v size /\
    SZ.v size_before_overall <= SZ.v size /\
    SZ.v size_before_overall <= Seq.length w /\
    Seq.equal (Seq.slice w0 0 (SZ.v size_before_overall)) (Seq.slice w 0 (SZ.v size_before_overall))
  )))
= let ps = ag_spec_zero_or_more ps1 in
  ag_serializable_zero_or_more_append ps1 l1 [x];
  ag_spec_zero_or_more_serializer_cons ps1 x ([] #tgt);
  assert_norm ((ag_spec_zero_or_more ps1).ag_serializer ([] #tgt) == ([] #Cbor.cbor));
  List.Tot.append_l_nil (ps1.ag_serializer x);
  assert (ps.ag_serializer [x] == ps1.ag_serializer x);
  ag_spec_zero_or_more_serializer_append ps1 l1 [x];
  assert (ps.ag_serializer (List.Tot.append l1 [x]) == List.Tot.append (ps.ag_serializer l1) (ps1.ag_serializer x));
  List.Tot.append_assoc l (ps.ag_serializer l1) (ps1.ag_serializer x);
  assert (List.Tot.append l (ps.ag_serializer (List.Tot.append l1 [x])) == List.Tot.append (List.Tot.append l (ps.ag_serializer l1)) (ps1.ag_serializer x));
  ag_spec_zero_or_more_size_append ps1.ag_size l1 [x];
  List.Tot.append_length l (ps.ag_serializer l1);
  List.Tot.append_length l (ps.ag_serializer (List.Tot.append l1 [x]));
  List.Tot.append_length (List.Tot.append l (ps.ag_serializer l1)) (ps1.ag_serializer x);
  norm_spec [delta_only [`%impl_serialize_array_group_post; `%impl_serialize_array_group_valid; `%impl_serialize_array_group_invalid; `%impl_serialize_array_group_requires; `%impl_serialize_array_group_pre]; iota; zeta] (impl_serialize_array_group_post lmin lmax count size size_prev (List.Tot.append l (ps.ag_serializer l1)) ps1 x w_prev w true);
  impl_serialize_array_group_size_before_le_size1 lmin lmax ps1 (List.Tot.append l (ps.ag_serializer l1)) x count_prev count size size_prev w_prev w;
  assert (SZ.v size_before_overall <= Seq.length w0);
  assert (SZ.v size_before_overall <= SZ.v size_prev);
  assert (SZ.v size_prev <= Seq.length w);
  assert (SZ.v size_before_overall <= Seq.length w);
  assert (SZ.v size_before_overall <= Seq.length w_prev);
  assert (Seq.equal (Seq.slice w_prev 0 (SZ.v size_prev)) (Seq.slice w 0 (SZ.v size_prev)));
  assert (forall (i: nat) . i < SZ.v size_before_overall ==> (
    i < SZ.v size_prev /\
    Seq.index (Seq.slice w_prev 0 (SZ.v size_prev)) i == Seq.index (Seq.slice w 0 (SZ.v size_prev)) i
  ));
  Seq.lemma_eq_intro (Seq.slice w_prev 0 (SZ.v size_before_overall)) (Seq.slice w 0 (SZ.v size_before_overall));
  Seq.lemma_eq_intro (Seq.slice w0 0 (SZ.v size_before_overall)) (Seq.slice w 0 (SZ.v size_before_overall))

let impl_serialize_array_group_valid_zero_or_more_false_budget
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (v: list tgt)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (count0: U64.t)
  (size_before: SZ.t)
  (count_inv: U64.t)
  (size_inv: SZ.t)
  (w0 w_inv: Seq.seq U8.t)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    v == List.Tot.append l1 (x :: l2) /\
    ps.ag_serializable l1 /\
    impl_serialize_array_group_pre p count0 size_before l w0 /\
    Seq.length w0 == Seq.length w_inv /\
    SZ.v size_before <= SZ.v size_inv /\
    SZ.v size_before <= Seq.length w0 /\
    SZ.v size_before <= Seq.length w_inv /\
    Seq.equal (Seq.slice w0 0 (SZ.v size_before)) (Seq.slice w_inv 0 (SZ.v size_before)) /\
    impl_serialize_array_group_pre p count_inv size_inv (List.Tot.append l (ps.ag_serializer l1)) w_inv /\
    impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x (Seq.length w_inv - SZ.v size_inv) == false
  ))))
  (ensures (
    impl_serialize_array_group_valid lmax l (ag_spec_zero_or_more ps1) v (Seq.length w0 - SZ.v size_before) == false
  ))
= let ps = ag_spec_zero_or_more ps1 in
  if not (impl_serialize_array_group_valid lmax l ps (List.Tot.append l1 (x :: l2)) (Seq.length w0 - SZ.v size_before))
  then ()
  else begin
    (* Step 1: Use item helper BEFORE norm_spec so the implication fires *)
    impl_serialize_array_group_valid_zero_or_more_item lmax l ps1 l1 x l2 (Seq.length w0 - SZ.v size_before);
    assert (impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x (Seq.length w0 - SZ.v size_before) == true);

    (* Step 2: Establish serializable and serializer equalities *)
    List.Tot.for_all_append ps1.ag_serializable l1 (x :: l2);
    ag_serializable_zero_or_more_append ps1 l1 (x :: l2);
    ag_spec_zero_or_more_serializer_append ps1 l1 (x :: l2);
    ag_spec_zero_or_more_serializer_cons ps1 x l2;
    let ser_l1 = ps.ag_serializer l1 in
    let ser_x = ps1.ag_serializer x in
    let ser_l2 = ps.ag_serializer l2 in
    let ser_xcl2 = ps.ag_serializer (x :: l2) in
    List.Tot.append_length (ps.ag_serializer l1) (ps.ag_serializer (x :: l2));
    List.Tot.append_length (ps1.ag_serializer x) (ps.ag_serializer l2);
    List.Tot.append_length l (ps.ag_serializer (List.Tot.append l1 (x :: l2)));
    List.Tot.append_length l ser_l1;
    List.Tot.append_length (List.Tot.append l ser_l1) ser_x;
    cbor_array_max_length_append lmax ser_l1 ser_xcl2;
    cbor_array_max_length_append lmax ser_x ser_l2;

    (* Step 3: Unfold valid(total) to get len_0 >= max(total), and valid(item) for both lengths *)
    norm_spec [delta_only [`%impl_serialize_array_group_valid; `%impl_serialize_array_group_requires]; iota; zeta] (impl_serialize_array_group_valid lmax l ps (List.Tot.append l1 (x :: l2)) (Seq.length w0 - SZ.v size_before));
    norm_spec [delta_only [`%impl_serialize_array_group_valid; `%impl_serialize_array_group_requires]; iota; zeta] (impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x (Seq.length w0 - SZ.v size_before));
    norm_spec [delta_only [`%impl_serialize_array_group_valid; `%impl_serialize_array_group_requires]; iota; zeta] (impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x (Seq.length w_inv - SZ.v size_inv));

    (* Step 4: Parse analysis for budget *)
    norm_spec [delta_only [`%impl_serialize_array_group_pre]; iota; zeta] (impl_serialize_array_group_pre p count0 size_before l w0);
    norm_spec [delta_only [`%impl_serialize_array_group_pre]; iota; zeta] (impl_serialize_array_group_pre p count_inv size_inv (List.Tot.append l ser_l1) w_inv);
    let n_l1 = List.Tot.length ser_l1 in
    let s_w_inv = Seq.slice w_inv 0 (SZ.v size_inv) in
    Seq.slice_slice w0 0 (SZ.v size_before) 0 (SZ.v size_before);
    Seq.slice_slice w_inv 0 (SZ.v size_inv) 0 (SZ.v size_before);
    Seq.lemma_eq_elim (Seq.slice w0 0 (SZ.v size_before)) (Seq.slice w_inv 0 (SZ.v size_before));
    cbor_parse_list_prefix p (U64.v count0) (Seq.slice w0 0 (SZ.v size_before)) s_w_inv;
    cbor_parse_list_split p (U64.v count0) n_l1 s_w_inv;
    let suffix = Seq.slice s_w_inv (SZ.v size_before) (Seq.length s_w_inv) in
    cbor_parse_list_bounds lmin lmax n_l1 suffix;
    let delta = SZ.v size_inv - SZ.v size_before in
    begin match cbor_parse_list p n_l1 suffix with
    | None -> ()
    | Some (l2, pos2) ->
      List.Tot.append_inv_head l l2 ser_l1;
      assert (l2 == ser_l1);
      assert (pos2 == delta)
    end;

    (* Step 5: Derive contradiction with explicit arithmetic *)
    let max_x = Some?.v (cbor_array_max_length lmax ser_x) in
    assert (Seq.length w0 - SZ.v size_before >= max_x);
    assert (Seq.length w_inv - SZ.v size_inv < max_x);
    assert (Seq.length w0 == Seq.length w_inv);
    let len_0 = Seq.length w0 - SZ.v size_before in
    let len_item = Seq.length w_inv - SZ.v size_inv in
    assert (len_item == len_0 - delta);
    assert (Some? (cbor_array_max_length lmax ser_l1));
    assert (Some? (cbor_array_max_length lmax ser_xcl2));
    assert (Some? (cbor_array_max_length lmax ser_l2));
    let max_l1 = Some?.v (cbor_array_max_length lmax ser_l1) in
    let max_xcl2 = Some?.v (cbor_array_max_length lmax ser_xcl2) in
    assert (max_xcl2 >= max_x);
    assert (len_0 >= max_l1 + max_xcl2);
    assert (len_0 >= max_l1 + max_x);
    assert (delta <= max_l1);
    assert (len_item >= max_x);
    assert (false)
  end

#pop-options

#push-options "--fuel 4 --ifuel 4 --z3rlimit_factor 16"
#restart-solver

let impl_serialize_array_group_post_zero_or_more_false
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (v: list tgt)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (count0: U64.t)
  (size_before_overall: SZ.t)
  (count_inv: U64.t)
  (size_inv: SZ.t)
  (count_item: U64.t)
  (size_item: SZ.t)
  (w0 w_inv w_new: Seq.seq U8.t)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    v == List.Tot.append l1 (x :: l2) /\
    ps.ag_serializable l1 /\
    impl_serialize_array_group_pre p count0 size_before_overall l w0 /\
    Seq.length w0 == Seq.length w_inv /\
    Seq.length w_inv == Seq.length w_new /\
    SZ.v size_before_overall <= SZ.v size_inv /\
    SZ.v size_before_overall <= Seq.length w0 /\
    SZ.v size_before_overall <= Seq.length w_inv /\
    Seq.equal (Seq.slice w0 0 (SZ.v size_before_overall)) (Seq.slice w_inv 0 (SZ.v size_before_overall)) /\
    impl_serialize_array_group_pre p count_inv size_inv (List.Tot.append l (ps.ag_serializer l1)) w_inv /\
    impl_serialize_array_group_post lmin lmax count_item size_item size_inv (List.Tot.append l (ps.ag_serializer l1)) ps1 x w_inv w_new false
  ))))
  (ensures (
    impl_serialize_array_group_valid lmax l (ag_spec_zero_or_more ps1) v (Seq.length w0 - SZ.v size_before_overall) == false /\
    SZ.v size_before_overall <= Seq.length w_new /\
    Seq.equal (Seq.slice w0 0 (SZ.v size_before_overall)) (Seq.slice w_new 0 (SZ.v size_before_overall))
  ))
= let ps = ag_spec_zero_or_more ps1 in
  norm_spec [delta_only [`%impl_serialize_array_group_post; `%impl_serialize_array_group_valid; `%impl_serialize_array_group_invalid; `%impl_serialize_array_group_requires; `%impl_serialize_array_group_pre]; iota; zeta] (impl_serialize_array_group_post lmin lmax count_item size_item size_inv (List.Tot.append l (ps.ag_serializer l1)) ps1 x w_inv w_new false);
  assert (impl_serialize_array_group_valid lmax (List.Tot.append l (ps.ag_serializer l1)) ps1 x (Seq.length w_inv - SZ.v size_inv) == false);
  impl_serialize_array_group_valid_zero_or_more_false_budget lmin lmax l ps1 v l1 x l2 count0 size_before_overall count_inv size_inv w0 w_inv;
  assert (SZ.v size_inv <= Seq.length w_inv);
  assert (SZ.v size_inv <= Seq.length w_new);
  assert (Seq.equal (Seq.slice w_inv 0 (SZ.v size_inv)) (Seq.slice w_new 0 (SZ.v size_inv)));
  assert (SZ.v size_before_overall <= Seq.length w_new);
  assert (forall (i: nat) . i < SZ.v size_before_overall ==> (
    i < SZ.v size_inv /\
    Seq.index (Seq.slice w_inv 0 (SZ.v size_inv)) i == Seq.index (Seq.slice w_new 0 (SZ.v size_inv)) i
  ));
  Seq.lemma_eq_intro (Seq.slice w_inv 0 (SZ.v size_before_overall)) (Seq.slice w_new 0 (SZ.v size_before_overall));
  Seq.lemma_eq_intro (Seq.slice w0 0 (SZ.v size_before_overall)) (Seq.slice w_new 0 (SZ.v size_before_overall))

#pop-options

#push-options "--fuel 4 --ifuel 4"
#restart-solver

let ag_spec_zero_or_more_serializer_nil
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (p: ag_spec source target inj {
    array_group_concat_unique_strong source source
  })
: Lemma
  ((ag_spec_zero_or_more p).ag_serializer ([] #target) == ([] #cbor))
= assert_norm ((ag_spec_zero_or_more p).ag_serializer ([] #target) == ([] #cbor))

#pop-options

#push-options "--z3rlimit_factor 64 --fuel 2 --ifuel 2 --split_queries always"
#restart-solver

let impl_serialize_array_group_post_zero_or_more_exit
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (v: list tgt)
  (l1: list tgt)
  (l2: list tgt)
  (count0: U64.t)
  (size_before: SZ.t)
  (count: U64.t)
  (size: SZ.t)
  (w0 w: Seq.seq U8.t)
  (res: bool)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    v == List.Tot.append l1 l2 /\
    ps.ag_serializable l1 /\
    impl_serialize_array_group_pre p count0 size_before l w0 /\
    Seq.length w == Seq.length w0 /\
    SZ.v size_before <= Seq.length w0 /\
    SZ.v size_before <= Seq.length w /\
    Seq.equal (Seq.slice w0 0 (SZ.v size_before)) (Seq.slice w 0 (SZ.v size_before)) /\
    (impl_serialize_array_group_valid lmax l ps v (Seq.length w - SZ.v size_before) == true ==> res == true) /\
    (res == true ==>
      impl_serialize_array_group_pre p count size (l `List.Tot.append` ps.ag_serializer l1) w /\
      SZ.v size_before <= SZ.v size
    ) /\
    (res == true ==> l2 == [])
  ))))
  (ensures (
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_zero_or_more ps1) v w0 w res
  ))
= let ps = ag_spec_zero_or_more ps1 in
  norm_spec [delta_only [`%impl_serialize_array_group_post; `%impl_serialize_array_group_valid; `%impl_serialize_array_group_invalid; `%impl_serialize_array_group_requires; `%impl_serialize_array_group_pre]; iota; zeta] (impl_serialize_array_group_post lmin lmax count size size_before l ps v w0 w res);
  norm_spec [delta_only [`%impl_serialize_array_group_valid; `%impl_serialize_array_group_requires]; iota; zeta] (impl_serialize_array_group_valid lmax l ps v (Seq.length w - SZ.v size_before));
  if res then begin
    List.Tot.append_l_nil l1;
    norm_spec [delta_only [`%impl_serialize_array_group_pre]; iota; zeta] (impl_serialize_array_group_pre p count0 size_before l w0);
    norm_spec [delta_only [`%impl_serialize_array_group_pre]; iota; zeta] (impl_serialize_array_group_pre p count size (l `List.Tot.append` ps.ag_serializer l1) w);
    let ser_v = ps.ag_serializer v in
    let n_v = List.Tot.length ser_v in
    list_append_length_pat l ser_v;
    let s_w = Seq.slice w 0 (SZ.v size) in
    Seq.slice_slice w0 0 (SZ.v size_before) 0 (SZ.v size_before);
    Seq.slice_slice w 0 (SZ.v size) 0 (SZ.v size_before);
    cbor_parse_list_prefix p (U64.v count0) (Seq.slice w0 0 (SZ.v size_before)) s_w;
    cbor_parse_list_split p (U64.v count0) n_v s_w;
    let suffix = Seq.slice s_w (SZ.v size_before) (Seq.length s_w) in
    cbor_parse_list_bounds lmin lmax n_v suffix;
    match cbor_parse_list p n_v suffix with
    | None -> ()
    | Some (l_parsed, pos_parsed) ->
      List.Tot.append_inv_head l l_parsed ser_v
  end

#pop-options

#push-options "--z3rlimit_factor 16 --fuel 1 --ifuel 1 --split_queries always"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_zero_or_more_slice
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
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_zero_or_more ps1) #_ (rel_slice_of_list r1 false)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  let ps = Ghost.hide (ag_spec_zero_or_more ps1);
  unfold (rel_slice_of_list r1 false c v);
  with s . assert (pts_to c.s #c.p s ** SM.seq_list_match s v r1);
  intro
    (Trade.trade
      (pts_to c.s #c.p s ** SM.seq_list_match s v r1)
      (rel_slice_of_list r1 false c v)
    )
    #emp
    fn _
  {
    fold (rel_slice_of_list r1 false c v)
  };
  let pl1 : GR.ref (list tgt1) = GR.alloc (Nil #tgt1);
  with count0 . assert (pts_to out_count count0);
  let mut pres = true;
  let mut pi = 0sz;
  let slen = S.len c.s;
  ag_spec_zero_or_more_serializer_nil ps1;
  while (
    let res = !pres;
    let i = !pi;
    S.pts_to_len c.s;
    (res && SZ.lt i slen)
  ) invariant exists* l1 res i s2 l2 w count size . (
    GR.pts_to pl1 l1 **
    pts_to c.s #c.p s **
    pts_to pi i **
    SM.seq_list_match s2 l2 r1 **
    pts_to pres res **
    pts_to out w **
    pts_to out_count count **
    pts_to out_size size **
    Trade.trade
      (pts_to c.s #c.p s ** SM.seq_list_match s2 l2 r1)
      (rel_slice_of_list r1 false c v)
      **
    pure (
      SZ.v i <= Seq.length s /\
      Seq.equal s2 (Seq.slice s (SZ.v i) (Seq.length s)) /\
      Ghost.reveal v == List.Tot.append l1 l2 /\
      ps.ag_serializable l1 /\
      Seq.length w == Seq.length w0 /\
      SZ.v size_before <= Seq.length w0 /\
      SZ.v size_before <= Seq.length w /\
      Seq.equal (Seq.slice w0 0 (SZ.v size_before)) (Seq.slice w 0 (SZ.v size_before)) /\
      (impl_serialize_array_group_valid lmax l ps v (Seq.length w - SZ.v size_before) == true ==> res == true) /\
      (res == true ==>
        impl_serialize_array_group_pre p count size (l `List.Tot.append` ps.ag_serializer l1) w /\
        SZ.v size_before <= SZ.v size
      )
    )
  ) {
    with s2 l2 . assert (SM.seq_list_match s2 l2 r1);
    S.pts_to_len c.s;
    SM.seq_list_match_length r1 s2 l2;
    let _ = SM.seq_list_match_cons_elim_trade s2 l2 r1;
    with s2' l2' . assert (SM.seq_list_match s2' l2' r1);
    let y = Ghost.hide (List.Tot.hd l2);
    let i = !pi;
    let x = S.op_Array_Access c.s i;
    Trade.rewrite_with_trade (r1 _ _) (r1 x y);
    Trade.trans_hyp_l (r1 x y) _ _ _;
    with l1 . assert (GR.pts_to pl1 l1);
    with w_inv . assert (pts_to out w_inv);
    with count_inv . assert (pts_to out_count count_inv);
    with size_inv . assert (pts_to out_size size_inv);
    S.pts_to_len out;
    let res = i1 x out out_count out_size (List.Tot.append l (ps.ag_serializer l1));
    with w_new . assert (pts_to out w_new);
    S.pts_to_len c.s;
    S.pts_to_len out;
    ag_serializable_zero_or_more_append ps1 l1 l2;
    if (res) {
      ag_serializable_zero_or_more_append ps1 l1 [Ghost.reveal y];
      let i' = SZ.add i 1sz;
      pi := i';
      let l1' = Ghost.hide (List.Tot.append l1 [Ghost.reveal y]);
      GR.op_Colon_Equals pl1 l1';
      Trade.elim_hyp_l (r1 _ _) _ _;
      Trade.trans_hyp_r _ _ _ (rel_slice_of_list r1 false c v);
      with gcount . assert (pts_to out_count gcount);
      with gsize . assert (pts_to out_size gsize);
      impl_serialize_array_group_post_zero_or_more_extend lmin lmax l ps1 l1 (Ghost.reveal y) gcount gsize size_inv count_inv size_before w0 w_inv w_new;
      assert (pure (Seq.equal s2' (Seq.slice s (SZ.v i') (Seq.length s))));
      assert (pure (Cons? l2));
      assert (pure (Ghost.reveal l2 == Ghost.reveal y :: l2'));
      List.Tot.Properties.append_l_cons (Ghost.reveal y) l2' l1;
      assert (pure (Ghost.reveal v == List.Tot.append l1' l2'));
      assert (pure (ps.ag_serializable l1'));
      ()
    } else {
      Trade.elim _ (SM.seq_list_match s2 l2 r1);
      with gcount . assert (pts_to out_count gcount);
      with gsize . assert (pts_to out_size gsize);
      assert (pure (Cons? l2));
      assert (pure (Ghost.reveal l2 == Ghost.reveal y :: l2'));
      impl_serialize_array_group_post_zero_or_more_false lmin lmax l ps1 v l1 (Ghost.reveal y) l2' count0 size_before count_inv size_inv gcount gsize w0 w_inv w_new;
      pres := false;
      ()
    }
  };
  with l1_g . assert (GR.pts_to pl1 l1_g);
  with s2_g l2_g . assert (SM.seq_list_match s2_g l2_g r1);
  SM.seq_list_match_length r1 s2_g l2_g;
  Trade.elim _ _;
  GR.free pl1;
  with w_post . assert (pts_to out w_post);
  with count_post . assert (pts_to out_count count_post);
  with size_post . assert (pts_to out_size size_post);
  let ret = !pres;
  impl_serialize_array_group_post_zero_or_more_exit lmin lmax l ps1 v l1_g l2_g count0 size_before count_post size_post w0 w_post ret;
  ret
}

#pop-options

(* impl_serialize_array_group_zero_or_more_iterator *)

let impl_serialize_array_group_post_zero_or_more_exit_false
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (v: list tgt)
  (count: U64.t)
  (size size_before: SZ.t)
  (w0 w: Seq.seq U8.t)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\
    impl_serialize_array_group_valid lmax l (ag_spec_zero_or_more ps1) v (Seq.length w - SZ.v size_before) == false /\
    Seq.length w == Seq.length w0 /\
    SZ.v size_before <= Seq.length w0 /\
    SZ.v size_before <= Seq.length w /\
    Seq.equal (Seq.slice w0 0 (SZ.v size_before)) (Seq.slice w 0 (SZ.v size_before))
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_zero_or_more ps1) v w0 w false
  ))
= norm_spec [delta_only [`%impl_serialize_array_group_post; `%impl_serialize_array_group_valid; `%impl_serialize_array_group_invalid; `%impl_serialize_array_group_requires; `%impl_serialize_array_group_pre]; iota; zeta] (impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_zero_or_more ps1) v w0 w false);
  norm_spec [delta_only [`%impl_serialize_array_group_valid; `%impl_serialize_array_group_requires]; iota; zeta] (impl_serialize_array_group_valid lmax l (ag_spec_zero_or_more ps1) v (Seq.length w - SZ.v size_before))

let impl_serialize_array_group_zero_or_more_iterator_t
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (#cbor_array_iterator_t: Type)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
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
=
  impl_serialize_array_group lmin lmax #_ #(list tgt1) #_ (ag_spec_zero_or_more ps1) #(array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1)) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1))

#push-options "--z3rlimit_factor 16 --fuel 1 --ifuel 1 --split_queries always"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_zero_or_more_iterator
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
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
: impl_serialize_array_group_zero_or_more_iterator_t lmin lmax #cbor_array_iterator_t cbor_array_iterator_match #t1 #tgt1 #inj1 #ps1 #impl_tgt1 #r1 i1 sq
=
    (c0: array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1))
    (#v: Ghost.erased (list tgt1))
    (out: S.slice U8.t)
    (out_count: R.ref U64.t)
    (out_size: R.ref SZ.t)
    (#w0: _)
    (#size_before: _)
    (l: Ghost.erased (list Cbor.cbor))
{
  let ps = Ghost.hide (ag_spec_zero_or_more ps1);
  let mut pc = c0;
  let pl1 : GR.ref (list tgt1) = GR.alloc (Nil #tgt1);
  with count0 . assert (pts_to out_count count0);
  let mut pres = true;
  ag_spec_zero_or_more_serializer_nil ps1;
  Trade.refl (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v);
  while (
    with gc l2 . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc l2);
    let c = !pc;
    rewrite each gc as c;
    let em = cddl_array_iterator_is_empty is_empty impl_tgt1 _ c;
    let res = !pres;
    (res && not em)
  ) invariant exists* l1 c res l2 w count size . (
    GR.pts_to pl1 l1 **
    pts_to pc c **
    rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c l2 **
    pts_to pres res **
    pts_to out w **
    pts_to out_count count **
    pts_to out_size size **
    Trade.trade
      (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c l2)
      (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v)
      **
    pure (
      (res == true ==> Ghost.reveal v == List.Tot.append l1 l2) /\
      ps.ag_serializable l1 /\
      Seq.length w == Seq.length w0 /\
      SZ.v size_before <= Seq.length w0 /\
      SZ.v size_before <= Seq.length w /\
      Seq.equal (Seq.slice w0 0 (SZ.v size_before)) (Seq.slice w 0 (SZ.v size_before)) /\
      (impl_serialize_array_group_valid lmax l ps v (Seq.length w - SZ.v size_before) == true ==> res == true) /\
      (res == true ==>
        impl_serialize_array_group_pre p count size (l `List.Tot.append` ps.ag_serializer l1) w /\
        SZ.v size_before <= SZ.v size
      )
    )
  ) {
    with gc l2 . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc l2);
    let x : impl_tgt1 = cddl_array_iterator_next length share gather truncate impl_tgt1 _ pc;
    with gc' l2' . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc' l2');
    let z : Ghost.erased tgt1 = Ghost.hide (List.Tot.hd l2);
    Trade.rewrite_with_trade (dsnd (Iterator.mk_spec r1) _ _) (r1 x z);
    Trade.trans_hyp_l (r1 x z) _ _ _;
    with l1 . assert (GR.pts_to pl1 l1);
    with w_inv . assert (pts_to out w_inv);
    with count_inv . assert (pts_to out_count count_inv);
    with size_inv . assert (pts_to out_size size_inv);
    S.pts_to_len out;
    assert (pure (Ghost.reveal v == List.Tot.append l1 l2));
    let res = i1 x out out_count out_size (List.Tot.append l (ps.ag_serializer l1));
    with w_new . assert (pts_to out w_new);
    S.pts_to_len out;
    ag_serializable_zero_or_more_append ps1 l1 l2;
    if (res) {
      ag_serializable_zero_or_more_append ps1 l1 [Ghost.reveal z];
      let l1' = Ghost.hide (List.Tot.append l1 [Ghost.reveal z]);
      GR.op_Colon_Equals pl1 l1';
      Trade.elim_hyp_l (r1 _ _) _ _;
      Trade.trans _ _ (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v);
      with gcount . assert (pts_to out_count gcount);
      with gsize . assert (pts_to out_size gsize);
      impl_serialize_array_group_post_zero_or_more_extend lmin lmax l ps1 l1 (Ghost.reveal z) gcount gsize size_inv count_inv size_before w0 w_inv w_new;
      assert (pure (Cons? l2));
      assert (pure (Ghost.reveal l2 == Ghost.reveal z :: l2'));
      List.Tot.Properties.append_l_cons (Ghost.reveal z) l2' l1;
      assert (pure (Ghost.reveal v == List.Tot.append l1' l2'));
      assert (pure (ps.ag_serializable l1'));
      ()
    } else {
      Trade.elim_hyp_l (r1 _ _) _ _;
      Trade.trans _ _ (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v);
      with gcount . assert (pts_to out_count gcount);
      with gsize . assert (pts_to out_size gsize);
      assert (pure (Cons? l2));
      impl_serialize_array_group_post_zero_or_more_false lmin lmax l ps1 v l1 (Ghost.reveal z) l2' count0 size_before count_inv size_inv gcount gsize w0 w_inv w_new;
      pres := false
    }
  };
  with l1_g . assert (GR.pts_to pl1 l1_g);
  with gc_g l2_g . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc_g l2_g);
  Trade.elim _ _;
  GR.free pl1;
  with w_post . assert (pts_to out w_post);
  with count_post . assert (pts_to out_count count_post);
  with size_post . assert (pts_to out_size size_post);
  let ret = !pres;
  if (ret) {
    impl_serialize_array_group_post_zero_or_more_exit lmin lmax l ps1 v l1_g l2_g count0 size_before count_post size_post w0 w_post ret;
    ret
  } else {
    impl_serialize_array_group_post_zero_or_more_exit_false lmin lmax l ps1 v count_post size_post size_before w0 w_post;
    ret
  }
}

#pop-options

(* impl_serialize_array_group_either_left *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_either_left
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
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt1)
    (i2: impl_serialize_array_group lmin lmax ps1 r2)
: impl_serialize_array_group lmin lmax #_ #_ #_ (ps1) #_ (rel_either_left r1 r2)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  match c {
    norewrite
    Inl c1 -> {
      Trade.rewrite_with_trade (rel_either_left r1 r2 c v) (r1 c1 v);
      let res = i1 c1 out out_count out_size l;
      Trade.elim _ _;
      res
    }
    norewrite
    Inr c2 -> {
      Trade.rewrite_with_trade (rel_either_left r1 r2 c v) (r2 c2 v);
      let res = i2 c2 out out_count out_size l;
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_zero_or_more
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
= impl_serialize_array_group_either_left
    (impl_serialize_array_group_zero_or_more_slice i1 sq)
    (impl_serialize_array_group_zero_or_more_iterator is_empty length share gather truncate i1 sq)

(* impl_serialize_array_group_one_or_more *)

let impl_serialize_array_group_one_or_more_empty
  (#p: cbor_parser) (lmin: cbor_min_length p) (lmax: cbor_max_length p)
  (count: U64.t) (size size_before: SZ.t)
  (l: list Cbor.cbor)
  (#t: array_group None) (#tgt: Type0) (#inj: bool) (ps1: ag_spec t tgt inj)
  (w0 w: Seq.seq U8.t)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\
    Seq.length w == Seq.length w0 /\
    SZ.v size_before <= Seq.length w0 /\
    SZ.v size_before <= Seq.length w /\
    Seq.equal (Seq.slice w0 0 (SZ.v size_before)) (Seq.slice w 0 (SZ.v size_before))
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_one_or_more ps1) [] w0 w false
  ))
= norm_spec [delta_only [`%impl_serialize_array_group_post; `%impl_serialize_array_group_valid; `%impl_serialize_array_group_invalid; `%impl_serialize_array_group_requires; `%ag_spec_one_or_more]; iota; zeta] (impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_one_or_more ps1) ([] #tgt) w0 w false)

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 16"

let impl_serialize_array_group_one_or_more_nonempty
  (#p: cbor_parser) (lmin: cbor_min_length p) (lmax: cbor_max_length p)
  (count: U64.t) (size size_before: SZ.t)
  (l: list Cbor.cbor)
  (#t: array_group None) (#tgt: Type0) (#inj: bool) (ps1: ag_spec t tgt inj)
  (v: list tgt) (w0 w: Seq.seq U8.t) (res: bool)
: Lemma
  (requires (
    Cons? v /\
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_zero_or_more ps1) v w0 w res
  ))
  (ensures (
    impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_one_or_more ps1) v w0 w res
  ))
= norm_spec [delta_only [`%impl_serialize_array_group_post; `%impl_serialize_array_group_valid; `%impl_serialize_array_group_invalid; `%impl_serialize_array_group_requires; `%impl_serialize_array_group_pre; `%ag_spec_one_or_more; `%ag_spec_zero_or_more]; iota; zeta] (impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_zero_or_more ps1) v w0 w res);
  norm_spec [delta_only [`%impl_serialize_array_group_post; `%impl_serialize_array_group_valid; `%impl_serialize_array_group_invalid; `%impl_serialize_array_group_requires; `%impl_serialize_array_group_pre; `%ag_spec_one_or_more; `%ag_spec_zero_or_more]; iota; zeta] (impl_serialize_array_group_post lmin lmax count size size_before l (ag_spec_one_or_more ps1) v w0 w res)

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 8 --split_queries always"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_one_or_more_slice
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
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group lmin lmax #_ #_ #_ (ag_spec_one_or_more ps1) #_ (rel_slice_of_list r1 false)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  unfold (rel_slice_of_list r1 false c v);
  S.pts_to_len c.s;
  SM.seq_list_match_length r1 _ _;
  fold (rel_slice_of_list r1 false c v);
  if (S.len c.s = 0sz) {
    with w_curr . assert (pts_to out w_curr);
    with count_curr . assert (pts_to out_count count_curr);
    with size_curr . assert (pts_to out_size size_curr);
    impl_serialize_array_group_one_or_more_empty lmin lmax count_curr size_curr size_before l ps1 w0 w_curr;
    false
  } else {
    let res = impl_serialize_array_group_zero_or_more_slice i1 sq c out out_count out_size l;
    with w_post . assert (pts_to out w_post);
    with count_post . assert (pts_to out_count count_post);
    with size_post . assert (pts_to out_size size_post);
    impl_serialize_array_group_one_or_more_nonempty lmin lmax count_post size_post size_before l ps1 v w0 w_post res;
    res
  }
}

#pop-options

let impl_serialize_array_group_one_or_more_iterator_t
  (#p: cbor_parser)
  (lmin: cbor_min_length p)
  (lmax: cbor_max_length p)
  (#cbor_array_iterator_t: Type)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
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
=
  impl_serialize_array_group lmin lmax #_ #(list tgt1) #_ (ag_spec_one_or_more ps1) #(array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1)) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1))

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 8 --split_queries always"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_one_or_more_iterator
  (#[@@@erasable]p: Ghost.erased cbor_parser)
  (#[@@@erasable]lmin: Ghost.erased (cbor_min_length p))
  (#[@@@erasable]lmax: Ghost.erased (cbor_max_length p))
  (#cbor_array_iterator_t: Type0)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
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
: impl_serialize_array_group_one_or_more_iterator_t lmin lmax #cbor_array_iterator_t cbor_array_iterator_match #t1 #tgt1 #inj1 #ps1 #impl_tgt1 #r1 i1 sq
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (#w0: _)
    (#size_before: _)
    (l: _)
{
  let v' : Ghost.erased (list (dfst (Iterator.mk_spec r1))) = v;
  Trade.rewrite_with_trade
    (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c v)
    (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c v');
  let em = cddl_array_iterator_is_empty is_empty impl_tgt1 _ c;
  Trade.elim _ _;
  if (em) {
    with w_curr . assert (pts_to out w_curr);
    with count_curr . assert (pts_to out_count count_curr);
    with size_curr . assert (pts_to out_size size_curr);
    impl_serialize_array_group_one_or_more_empty lmin lmax count_curr size_curr size_before l ps1 w0 w_curr;
    false
  } else {
    let res = impl_serialize_array_group_zero_or_more_iterator is_empty length share gather truncate i1 sq c out out_count out_size l;
    with w_post . assert (pts_to out w_post);
    with count_post . assert (pts_to out_count count_post);
    with size_post . assert (pts_to out_size size_post);
    impl_serialize_array_group_one_or_more_nonempty lmin lmax count_post size_post size_before l ps1 v w0 w_post res;
    res
  }
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_one_or_more
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
= impl_serialize_array_group_either_left
    (impl_serialize_array_group_one_or_more_slice i1 sq)
    (impl_serialize_array_group_one_or_more_iterator is_empty length share gather truncate i1 sq)

module CBOR.Pulse.Raw.EverParse.Nondet
#lang-pulse
include CBOR.Spec.Raw.Nondet
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Format
open LowParse.Spec.VCList
open LowParse.Pulse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
let impl_equiv_t
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
=
  (l1: S.slice byte) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (raw_data_item)) ->
  stt (option bool)
    (pts_to_serialized (serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_raw_data_item) l2 #p2 gl2 **
      pure (raw_data_item_size gl1 + raw_data_item_size gl2 <= bound)
    )
    (fun res ->
      pts_to_serialized (serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        raw_data_item_size gl1 + raw_data_item_size gl2 <= bound /\
        res == equiv gl1 gl2
      )
    )

inline_for_extraction
let impl_equiv_hd_t
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
=
  (n1: Ghost.erased nat) ->
  (l1: S.slice byte) ->
  (n2: Ghost.erased nat) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (nlist n1 raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (nlist n2 raw_data_item)) ->
  stt (option bool)
    (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0 /\
        raw_data_item_size (List.Tot.hd gl1) + raw_data_item_size (List.Tot.hd gl2) <= bound
      )
    )
    (fun res ->
pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0 /\
        raw_data_item_size (List.Tot.hd gl1) + raw_data_item_size (List.Tot.hd gl2) <= bound /\
        res == equiv (List.Tot.hd gl1) (List.Tot.hd gl2)
      )
    )

let pts_to_serialized_nlist_raw_data_item_head_header'_post_children
  (n: pos)
  (va: LowParse.Spec.VCList.nlist n raw_data_item)
  (h: header) (v': (header & (leaf_content h & (nlist (remaining_data_items_header h) raw_data_item & nlist (n - 1)  raw_data_item  ))))
: Lemma
  (requires
    pts_to_serialized_nlist_raw_data_item_head_header'_post n va h v'
  )
  (ensures
    (fst (snd (snd v')) <: list raw_data_item) == begin match List.Tot.hd va with
    | Array _ v -> v
    | Map _ v -> CBOR.Spec.Util.list_of_pair_list v
    | Tagged _ v -> [v]
    | _ -> []
    end
  )
= // assert (synth_raw_data_item_from_alt (synth_raw_data_item_from_alt_recip (List.Tot.hd va)) == List.Tot.hd va);
  ()

let check_equiv_head
  (a1 a2: raw_data_item)
: Tot bool
= 
      match a1, a2 with
      | Int64 ty1 v1, Int64 ty2 v2 ->
        ty1 = ty2 &&
        v1.value = v2.value
      | Simple v1, Simple v2 ->
        v1 = v2
      | String ty1 _ s1, String ty2 _ s2 ->
        ty1 = ty2 &&
        s1 = s2
      | Tagged tag1 b1, Tagged tag2 b2 ->
        tag1.value = tag2.value
      | Array len1 ar1, Array len2 ar2 ->
        len1.value = len2.value
      | _ -> false

let check_equiv_head_correct_pre
  (gl1: list raw_data_item)
  (gl2: list raw_data_item)
  (equiv: ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 }) -> option bool))
: Tot prop
=
    List.Tot.length gl1 == List.Tot.length gl2 /\
    Cons? gl1 /\ Cons? gl2 /\ (
    let a1 = List.Tot.hd gl1 in
    let a2 = List.Tot.hd gl2 in
    let gc1 = dsnd (dfst (synth_raw_data_item_from_alt_recip a1)) in
    let gc2 = dsnd (dfst (synth_raw_data_item_from_alt_recip a2)) in
    let h1 = get_raw_data_item_header a1 in
    let h2 = get_raw_data_item_header a2 in
    get_header_major_type h1 == get_header_major_type h2 /\
    equiv a1 a2 = Some false
  )

let check_equiv_head_correct_post
  (gl1: list raw_data_item)
  (gl2: list raw_data_item)
  (equiv: ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 }) -> option bool))
: Tot prop
=
  check_equiv_head_correct_pre gl1 gl2 equiv /\ (
    let a1 :: q1 = gl1 in
    let a2 :: q2 = gl2 in
    let l1' = dsnd (synth_raw_data_item_from_alt_recip a1) `List.Tot.append` q1 in
    let l2' = dsnd (synth_raw_data_item_from_alt_recip a2) `List.Tot.append` q2 in
    (check_equiv_head a1 a2 ==> list_sum raw_data_item_size l1' + list_sum raw_data_item_size l2' <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2) /\
    check_equiv_list gl1 gl2 equiv == (if check_equiv_head a1 a2 then check_equiv_list l1' l2' equiv else Some false)
  )

#push-options "--z3rlimit 32"

let check_equiv_head_correct
  (gl1: list raw_data_item)
  (gl2: list raw_data_item)
  (equiv: ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 }) -> option bool))
  (sq: squash (check_equiv_head_correct_pre gl1 gl2 equiv))
: Lemma
  (ensures (
    check_equiv_head_correct_post gl1 gl2 equiv
  ))
=
  let a1 :: q1 = gl1 in
  let a2 :: q2 = gl2 in
  let l1' = dsnd (synth_raw_data_item_from_alt_recip a1) `List.Tot.append` q1 in
  let l2' = dsnd (synth_raw_data_item_from_alt_recip a2) `List.Tot.append` q2 in
  raw_data_item_size_eq a1;
  raw_data_item_size_eq a2;
  match a1, a2 with
  | Array len1 ar1, Array len2 ar2 ->
        list_sum_append raw_data_item_size ar1 q1;
        list_sum_append raw_data_item_size ar2 q2;
        ()
  | _ ->  ()

module U64 = FStar.UInt64

#pop-options

#push-options "--z3rlimit 64"

let pi
  (h1: header)
  (mt1: major_type_t)
  (len: U64.t)
  (sq: squash (
      mt1 == get_header_major_type h1 /\
      (mt1 == cbor_major_type_byte_string \/ mt1 == cbor_major_type_text_string) /\
      len == argument_as_uint64 (dfst h1) (dsnd h1) 
  ))
= 
  parse_synth  (parse_filter (LowParse.Spec.SeqBytes.parse_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq #h1 ())

let pi_correct
  (h1: header)
  (mt1: major_type_t)
  (len: U64.t)
  (sq: squash (
      mt1 == get_header_major_type h1 /\
      (mt1 == cbor_major_type_byte_string \/ mt1 == cbor_major_type_text_string) /\
      len == argument_as_uint64 (dfst h1) (dsnd h1) 
  ))
: Lemma
  (forall b . parse (parse_leaf_content h1) b == parse (pi h1 mt1 len sq) b)
= ()

let sigma
  (h1: header)
  (mt1: major_type_t)
  (len: U64.t)
  (sq: squash (
      mt1 == get_header_major_type h1 /\
      (mt1 == cbor_major_type_byte_string \/ mt1 == cbor_major_type_text_string) /\
      len == argument_as_uint64 (dfst h1) (dsnd h1) 
  ))
: serializer (pi h1 mt1 len sq)
= 
  serialize_synth  #_ #_ #(c: leaf_content h1 {b2t (LeafContentSeq? #h1 c)}) _ (LeafContentSeq #h1 ()) (serialize_filter (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq?.v #h1) ()

// FIXME: WHY WHY WHY do I need to break abstraction here? I can't unfold sigma in pulse.
let sigma_correct
  (a1: raw_data_item)
  (h1: header)
  (mt1: major_type_t)
  (len: U64.t)
  (c1: leaf_content h1)
  (sq: squash (
      mt1 == get_header_major_type h1 /\
      (mt1 == cbor_major_type_byte_string \/ mt1 == cbor_major_type_text_string) /\
      len == argument_as_uint64 (dfst h1) (dsnd h1) /\
      h1 == get_raw_data_item_header a1 /\
      c1 == dsnd (dfst (synth_raw_data_item_from_alt_recip a1))
  ))
: Lemma
  (serialize (sigma h1 mt1 len ()) c1 == String?.v a1)
= assert (serialize (sigma h1 mt1 len ()) c1 == serialize (serialize_synth #_ #_ #(c: leaf_content h1 {b2t (LeafContentSeq? #h1 c)}) _ (LeafContentSeq #h1 ()) (serialize_filter (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq?.v #h1) ()) c1)
  ;
  serialize_synth_eq
    _ (LeafContentSeq #h1 ()) (serialize_filter (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq?.v #h1) ()
    c1;
  assert ((LeafContentSeq?.v c1 <: bytes ) == (String?.v a1 <: bytes));
  assert (serialize (sigma h1 mt1 len ()) c1 == serialize (serialize_filter (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq?.v #h1 c1));
  assert (serialize (sigma h1 mt1 len ()) c1 == String?.v a1);
  ()

inline_for_extraction
fn impl_check_equiv_head
  (h1: header)
  (c1: S.slice byte)
  (h2: header)
  (c2: S.slice byte)
  (#p1: perm)
  (#gc1: Ghost.erased (leaf_content h1))
  (#p2: perm)
  (#gc2: Ghost.erased (leaf_content h2))
  (a1: Ghost.erased raw_data_item)
  (a2: Ghost.erased raw_data_item)
requires
  pts_to_serialized (serialize_leaf_content h1) c1 #p1 gc1 **
  pts_to_serialized (serialize_leaf_content h2) c2 #p2 gc2 **
  pure (
    h1 == get_raw_data_item_header a1 /\
    Ghost.reveal gc1 == dsnd (dfst (synth_raw_data_item_from_alt_recip a1)) /\
    h2 == get_raw_data_item_header a2 /\
    Ghost.reveal gc2 == dsnd (dfst (synth_raw_data_item_from_alt_recip a2)) /\
    get_header_major_type h1 == get_header_major_type h2
  )
returns res: bool
ensures
  pts_to_serialized (serialize_leaf_content h1) c1 #p1 gc1 **
  pts_to_serialized (serialize_leaf_content h2) c2 #p2 gc2 **
  pure (
    res == check_equiv_head a1 a2
  )
{
  let mt1 = get_header_major_type h1;
  if (mt1 = cbor_major_type_simple_value) {
    (argument_as_simple_value (dfst h1) (dsnd h1) = argument_as_simple_value (dfst h2) (dsnd h2))
  } else {
    let len = argument_as_uint64 (dfst h1) (dsnd h1);
    if (len <> argument_as_uint64 (dfst h2) (dsnd h2)) {
      false
    } else if (mt1 = cbor_major_type_byte_string || mt1 = cbor_major_type_text_string) {
      pi_correct h1 mt1 len ();
      pts_to_serialized_ext_trade
        (serialize_leaf_content h1)
        (sigma h1 mt1 len ())
        c1;
      sigma_correct a1 h1 mt1 len gc1 ();
      pts_to_serialized_elim_trade
        (sigma h1 mt1 len ())
        c1;
      Trade.trans _ _ (pts_to_serialized (serialize_leaf_content h1) c1 #p1 gc1);
      pi_correct h2 mt1 len ();
      pts_to_serialized_ext_trade
        (serialize_leaf_content h2)
        (sigma h2 mt1 len ())
        c2;
      sigma_correct a2 h2 mt1 len gc2 ();
      pts_to_serialized_elim_trade
        (sigma h2 mt1 len ())
        c2;
      Trade.trans _ _ (pts_to_serialized (serialize_leaf_content h2) c2 #p2 gc2);
      CBOR.Spec.Raw.Format.bytes_lex_compare_equal (String?.v a1) (String?.v a2);
      let cmp = CBOR.Pulse.Raw.Compare.Bytes.lex_compare_bytes c1 c2;
      Trade.elim _ (pts_to_serialized (serialize_leaf_content h1) c1 #p1 gc1);
      Trade.elim _ (pts_to_serialized (serialize_leaf_content h2) c2 #p2 gc2);
      (cmp = 0s)
    } else {
       (mt1 <> cbor_major_type_map)
    }
  }
}

inline_for_extraction
fn impl_check_equiv_list
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item))
  (#bound: Ghost.erased nat)
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool))
  (impl_equiv: impl_equiv_hd_t bound equiv)
  (sq: squash (
    list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 <= bound
  ))
requires
  pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v n2) serialize_raw_data_item) l2 #p2 gl2
returns res: option bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v n2) serialize_raw_data_item) l2 #p2 gl2 **
  pure (
    res == check_equiv_list gl1 gl2 equiv
  )
{
  if (n1 <> n2) {
    Some false
  } else {
    let mut pn = n1;
    let mut pl1 = l1;
    let mut pl2 = l2;
    Trade.refl
      (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1);
    pts_to_serialized_ext_trade
      (serialize_nlist (SZ.v n2) serialize_raw_data_item)
      (serialize_nlist (SZ.v n1) serialize_raw_data_item)
      l2;
    let mut pres = Some true;
    while (
      let res = !pres;
      let n = !pn;
      ((res = Some true) && SZ.gt n 0sz)
    )
    invariant b . exists* res n' l1' l2' gl1' gl2' .
      pts_to pres res **
      pts_to pn n' **
      pts_to pl1 l1' **
      pts_to pl2 l2' **
      pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l1' #p1 gl1' **
      Trade.trade
        (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l1' #p1 gl1')
        (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1) **
      pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l2' #p2 gl2' **
      Trade.trade
        (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l2' #p2 gl2')
        (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l2 #p2 gl2) **
      pure (
        b == ((res = Some true) && SZ.v n' > 0) /\
        list_sum raw_data_item_size gl1' + list_sum raw_data_item_size gl2' <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 /\
        check_equiv_list gl1 gl2 equiv == (if res = Some true then check_equiv_list gl1' gl2' equiv else res)
      )
    {
      let l1' = !pl1;
      let l2' = !pl2;
      let r = impl_equiv _ l1' _ l2';
      if (None? r) {
        pres := r
      } else {
        let n = !pn;
        with gl1' . assert (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
        with gl2' . assert (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
        assume (pure (SZ.fits_u64));
        raw_data_item_size_eq (List.Tot.hd gl1');
        raw_data_item_size_eq (List.Tot.hd gl2');
        if (r = Some true) {
          let n' = SZ.sub n 1sz;
          let tl1 = LowParse.Pulse.VCList.nlist_tl
            serialize_raw_data_item
            (jump_raw_data_item ())
            (SZ.v n)
            l1';
          Trade.trans _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1') _;
          pts_to_serialized_nlist_ext
            serialize_raw_data_item
            _
            tl1
            serialize_raw_data_item
            (SZ.v n');
          Trade.trans (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) tl1 #p1 _) _ _;
          let tl2 = LowParse.Pulse.VCList.nlist_tl
            serialize_raw_data_item
            (jump_raw_data_item ())
            (SZ.v n)
            l2';
          Trade.trans _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2') _;
          pts_to_serialized_nlist_ext
            serialize_raw_data_item
            _
            tl2
            serialize_raw_data_item
            (SZ.v n');
          Trade.trans (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) tl2 #p2 _) _ _;
          pn := n';
          pl1 := tl1;
          pl2 := tl2;
        } else {
          let gh1 = pts_to_serialized_nlist_raw_data_item_head_header' l1' (SZ.v n);
          let (hd1, tl1) = split_nondep_then'
            _ (jump_header ())
            _ l1';
          Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
          let h1 = read_header () hd1;
          Trade.elim_hyp_l _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
          rewrite each gh1 as h1;
          let mt1 = get_header_major_type h1;
          let gh2 = pts_to_serialized_nlist_raw_data_item_head_header' l2' (SZ.v n);
          let (hd2, tl2) = split_nondep_then'
            _ (jump_header ())
            _ l2';
          Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
          let h2 = read_header () hd2;
          Trade.elim_hyp_l _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
          rewrite each gh2 as h2;
          let mt2 = get_header_major_type h2;
          if (mt1 <> mt2) {
            Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
            Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
            pres := Some false
          } else {
            let (lc1, tl1') = split_nondep_then'
              _ (jump_leaf_content () h1)
              _ tl1;
            Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
            with w1 . assert (
              pts_to_serialized (serialize_nondep_then (serialize_nlist (remaining_data_items_header h1) serialize_raw_data_item) (serialize_nlist (SZ.v n - 1) serialize_raw_data_item)) tl1' #p1 w1
            );
            list_sum_append raw_data_item_size (fst w1) (snd w1);
            pts_to_serialized_nlist_append serialize_raw_data_item tl1' _ _;
            Trade.trans_hyp_r _ _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
            pts_to_serialized_length _ tl1';
            assert (pure (remaining_data_items_header h1 + (SZ.v n - 1) <= SZ.v (S.len tl1')));
            let n' : SZ.t = SZ.add (impl_remaining_data_items_header (S.len tl1') h1) (SZ.sub n 1sz);
            pts_to_serialized_nlist_ext
              serialize_raw_data_item
              _
              tl1'
              serialize_raw_data_item
              (SZ.v n')
              ;
            Trade.trans_hyp_r _ _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');

            let (lc2, tl2') = split_nondep_then'
              _ (jump_leaf_content () h2)
              _ tl2;
            Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
            pts_to_serialized_nlist_append serialize_raw_data_item tl2' _ _;
            Trade.trans_hyp_r _ _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');

            assert (pure (check_equiv_head_correct_pre gl1' gl2' equiv));
            let sq : squash (check_equiv_head_correct_pre gl1' gl2' equiv) = ();
            check_equiv_head_correct gl1' gl2' equiv sq;
            if (impl_check_equiv_head h1 lc1 h2 lc2 (List.Tot.hd gl1') (List.Tot.hd gl2')) {
                Trade.elim_hyp_l _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
                Trade.trans _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1') _;
                Trade.elim_hyp_l _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
                Trade.trans _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2') _;
                pn := n';
                pl1 := tl1';
                pl2 := tl2';
            } else {
              Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
              Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
              pres := Some false
            }
          }
        }
      }
    };
    Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1);
    Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l2 #p2 gl2);
    !pres
  }
}



inline_for_extraction
fn impl_equiv_hd_weaken
  (#bound1: Ghost.erased nat)
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound1 }) -> option bool))
  (impl_equiv: impl_equiv_hd_t bound1 equiv)
  (bound2: Ghost.erased nat)
  (sq: squash (Ghost.reveal bound2 <= Ghost.reveal bound1))
: impl_equiv_hd_t bound2 equiv
=
  (n1: Ghost.erased nat)
  (l1: S.slice byte)
  (n2: Ghost.erased nat)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist n1 raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist n2 raw_data_item))
{
  impl_equiv n1 l1 n2 l2
}

inline_for_extraction
fn impl_check_equiv_aux
  (#bound: Ghost.erased nat)
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool))
  (impl_equiv: impl_equiv_hd_t bound equiv)
: impl_equiv_t bound (check_equiv_aux bound equiv)
=
  (l1: S.slice byte)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (raw_data_item))
{
  LowParse.Pulse.VCList.pts_to_serialized_nlist_1
    serialize_raw_data_item
    l1;
  LowParse.Pulse.VCList.pts_to_serialized_nlist_1
    serialize_raw_data_item
    l2;
  let sq : squash (list_sum raw_data_item_size [Ghost.reveal gl1] + list_sum raw_data_item_size [Ghost.reveal gl2] <= bound) = ();
  let res = impl_check_equiv_list 1sz l1 1sz l2 impl_equiv sq;
  Trade.elim _ (pts_to_serialized serialize_raw_data_item l1 #p1 gl1);
  Trade.elim _ (pts_to_serialized serialize_raw_data_item l2 #p2 gl2);
  res
}

let serialize_list_of_pair_list
  (n: nat)
  (l: nlist n (raw_data_item & raw_data_item))
: Lemma
  (serialize (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l ==
    serialize (serialize_nlist (n + n) serialize_raw_data_item) (list_of_pair_list _ n l)
  )
= let b = serialize (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l in
  parse_pair_list_as_list
    parse_raw_data_item
    n
    b;
  assert (parse (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item)) b == Some (l, Seq.length b));
  let Some (l', _) = parse (parse_nlist (n + n) parse_raw_data_item) b in
  assert (l == pair_list_of_list _ n l');
  list_of_pair_list_of_list n l';
  parse_injective
    (parse_nlist (n + n) parse_raw_data_item)
    b
    (serialize (serialize_nlist (n + n) serialize_raw_data_item) l');
  ()

inline_for_extraction
fn impl_setoid_assoc_eq_with_overflow
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> option bool))
  (#bound: Ghost.erased nat)
  (impl_equiv: impl_equiv_t bound equiv)
  (nl: SZ.t)
  (ll: S.slice byte)
  (xr_key: S.slice byte)
  (xr_value: S.slice byte)
  (#pl: perm)
  (#gll: Ghost.erased (nlist (SZ.v nl) (raw_data_item & raw_data_item)))
  (#pxr_key: perm)
  (#gxr_key: Ghost.erased raw_data_item)
  (#pxr_value: perm)
  (#gxr_value: Ghost.erased raw_data_item)
requires
  pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll **
  pts_to_serialized serialize_raw_data_item xr_key #pxr_key gxr_key **
  pts_to_serialized serialize_raw_data_item xr_value #pxr_value gxr_value **
  pure (list_sum (pair_sum raw_data_item_size raw_data_item_size) gll + (raw_data_item_size gxr_key + raw_data_item_size gxr_value) <= bound)
returns res: option bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll **
  pts_to_serialized serialize_raw_data_item xr_key #pxr_key gxr_key **
  pts_to_serialized serialize_raw_data_item xr_value #pxr_value gxr_value **
  pure (list_sum (pair_sum raw_data_item_size raw_data_item_size) gll + (raw_data_item_size gxr_key + raw_data_item_size gxr_value) <= bound /\
    res == setoid_assoc_eq_with_overflow equiv equiv gll (Ghost.reveal gxr_key, Ghost.reveal gxr_value)
  )
{
  Trade.refl
    (pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll);
  let mut pll = ll;
  let mut pn = nl;
  let mut pres = Some false;
  let mut pcont = true;
  while (
    let n = !pn;
    let res = !pres;
    let cont = !pcont;
    (SZ.gt n 0sz && (res = Some false) && cont)
  ) invariant b . exists* l n (gl: nlist (SZ.v n) (raw_data_item & raw_data_item)) res cont .
    pts_to pll l **
    pts_to pn n **
    pts_to_serialized
      (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l #pl
      gl **
    Trade.trade
      (pts_to_serialized
        (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl
        gl
      )
      (pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll) **
    pts_to pres res **
    pts_to_serialized serialize_raw_data_item xr_key #pxr_key gxr_key **
    pts_to_serialized serialize_raw_data_item xr_value #pxr_value gxr_value **
    pts_to pcont cont **
    pure (
      b == (SZ.v n > 0 && res = Some false && cont) /\
      list_sum (pair_sum raw_data_item_size raw_data_item_size) gl + (raw_data_item_size gxr_key + raw_data_item_size gxr_value) <= bound /\
      setoid_assoc_eq_with_overflow equiv equiv gll (Ghost.reveal gxr_key, Ghost.reveal gxr_value) == (if res = Some false && cont then setoid_assoc_eq_with_overflow equiv equiv gl (Ghost.reveal gxr_key, Ghost.reveal gxr_value) else res)
    )
  {
    let l = !pll;
    with gn (gl: nlist (SZ.v gn) (raw_data_item & raw_data_item)) . assert (
      pts_to pn gn **
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl
        gl
    );
    let n = !pn;
    let n' = SZ.sub n 1sz;
    nlist_cons_as_nondep_then
      (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      (SZ.v n)
      l;
    pts_to_serialized_nondep_then_assoc_l2r
      serialize_raw_data_item
      serialize_raw_data_item
      (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl
        gl
    );
    let ki : Ghost.erased parser_kind = and_then_kind
      parse_raw_data_item_kind
      (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
    let pi : parser ki (raw_data_item & nlist (SZ.v n') (raw_data_item & raw_data_item)) = nondep_then
        parse_raw_data_item
        (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
    let si : serializer pi = serialize_nondep_then
        serialize_raw_data_item
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
    assume (pure (SZ.fits_u64));
    let (lh, lt) = split_nondep_then'
      serialize_raw_data_item
      (jump_raw_data_item ())
      si
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl
        gl
    );
    let res = impl_equiv xr_key lh;
    if (None? res) {
      Trade.elim _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl
          gl
      );
      pres := res;
    } else {
      Trade.elim_hyp_l _ _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl
          gl
      );
      let kj : Ghost.erased parser_kind = (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
      let pj : parser kj (nlist (SZ.v n') (raw_data_item & raw_data_item)) =
          (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
      let sj : serializer pj =
          (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
      assert (pure (si == serialize_nondep_then serialize_raw_data_item sj));
      let sq : squash (split_nondep_then''_precond pi parse_raw_data_item pj) = ();
      let (lv, lt') = split_nondep_then''
        serialize_raw_data_item
        (jump_raw_data_item ())
        sj
        lt
        sq;
      Trade.trans _ _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl
          gl
      );
      if (Some?.v res) {
        pres := impl_equiv xr_value lv;
        Trade.elim _ (
          pts_to_serialized
            (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
            l #pl
            gl
        );
        pcont := false;
        ()
      } else {
        Trade.elim_hyp_l _ _ (
          pts_to_serialized
            (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
            l #pl
            gl
        );
        Trade.trans _ (
          pts_to_serialized
            (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
            l #pl
            gl
        ) _;
        pts_to_serialized_ext_trade
          sj
          (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          lt';
        Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll);
        pll := lt';
        pn := n';
        ()
      }
    }
  };
  Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll);
  !pres
}

inline_for_extraction
fn impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> option bool))
  (#bound: Ghost.erased nat)
  (impl_equiv: impl_equiv_t bound equiv)
  (nl1: SZ.t)
  (l1: S.slice byte)
  (nl2: SZ.t)
  (l2: S.slice byte)
  (#pl1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v nl1) (raw_data_item & raw_data_item)))
  (#pl2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v nl2) (raw_data_item & raw_data_item)))
requires
  pts_to_serialized (serialize_nlist (SZ.v nl1) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l1 #pl1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2 **
  pure (list_sum (pair_sum raw_data_item_size raw_data_item_size) gl1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) gl2 <= bound)
returns res: option bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v nl1) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l1 #pl1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2 **
  pure (list_sum (pair_sum raw_data_item_size raw_data_item_size) gl1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) gl2 <= bound /\
    res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv gl1) gl2
  )
{
  Trade.refl
    (pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2);
  let mut pl = l2;
  let mut pn = nl2;
  let mut pres = Some true;
  while (
    let n = !pn;
    let res = !pres;
    (SZ.gt n 0sz && (res = Some true))
  ) invariant b . exists* l n (gl: nlist (SZ.v n) (raw_data_item & raw_data_item)) res .
    pts_to pl l **
    pts_to pn n **
    pts_to_serialized
      (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l #pl2
      gl **
    Trade.trade
      (pts_to_serialized
        (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
      )
      (pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2) **
    pts_to pres res **
    pts_to_serialized (serialize_nlist (SZ.v nl1) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l1 #pl1 gl1 **
    pure (
      b == (SZ.v n > 0 && res = Some true) /\
      list_sum (pair_sum raw_data_item_size raw_data_item_size) gl1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) gl <= bound /\
      list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv gl1) gl2 == (if res = Some true then list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv gl1) gl else res)
    )
  {
    let l = !pl;
    with gn (gl: nlist (SZ.v gn) (raw_data_item & raw_data_item)) . assert (
      pts_to pn gn **
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
    );
    let n = !pn;
    let n' = SZ.sub n 1sz;
    nlist_cons_as_nondep_then
      (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      (SZ.v n)
      l;
    pts_to_serialized_nondep_then_assoc_l2r
      serialize_raw_data_item
      serialize_raw_data_item
      (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
    );
    let ki : Ghost.erased parser_kind = and_then_kind
      parse_raw_data_item_kind
      (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
    let pi : parser ki (raw_data_item & nlist (SZ.v n') (raw_data_item & raw_data_item)) = nondep_then
        parse_raw_data_item
        (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
    let si : serializer pi = serialize_nondep_then
        serialize_raw_data_item
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
    assume (pure (SZ.fits_u64));
    let (lh, lt) = split_nondep_then'
      serialize_raw_data_item
      (jump_raw_data_item ())
      si
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
    );
    let kj : Ghost.erased parser_kind = (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
    let pj : parser kj (nlist (SZ.v n') (raw_data_item & raw_data_item)) =
        (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
    let sj : serializer pj =
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
    assert (pure (si == serialize_nondep_then serialize_raw_data_item sj));
    let sq : squash (split_nondep_then''_precond pi parse_raw_data_item pj) = ();
    let (lv, lt') = split_nondep_then''
      serialize_raw_data_item
      (jump_raw_data_item ())
      sj
      lt
      sq;
    let res = impl_setoid_assoc_eq_with_overflow impl_equiv nl1 l1 lh lv;
    Trade.elim_hyp_l (pts_to_serialized serialize_raw_data_item lv #pl2 _) _ _;
    Trade.trans_hyp_r _ _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
    );
    Trade.elim_hyp_l (pts_to_serialized serialize_raw_data_item lh #pl2 _) _ _;
    if (res = Some true) {
      Trade.trans _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl2
          gl
      ) _;
      pts_to_serialized_ext_trade
        sj
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        lt';
      Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2);
      pl := lt';
      pn := n';
    } else {
      Trade.elim _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl2
          gl
      );
      pres := res
    }
  };
  Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2);
  !pres
}

inline_for_extraction
let impl_data_model_hd_t
  (data_model: (x1: raw_data_item) -> (x2: raw_data_item) -> bool)
=
  (n1: Ghost.erased nat) ->
  (l1: S.slice byte) ->
  (n2: Ghost.erased nat) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (nlist n1 raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (nlist n2 raw_data_item)) ->
  stt (bool)
    (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0
      )
    )
    (fun res ->
pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0 /\
        res == data_model (List.Tot.hd gl1) (List.Tot.hd gl2)
      )
    )

let option_sz_v (x: option SZ.t) : GTot (option nat) =
  match x with
  | None -> None
  | Some x' -> Some (SZ.v x')

inline_for_extraction
let impl_check_equiv_map_hd_t
  (check_equiv_map: option nat -> (x1: raw_data_item) -> (x2: raw_data_item) -> option bool)
=
  (map_bound: option SZ.t) ->
  (n1: Ghost.erased nat) ->
  (l1: S.slice byte) ->
  (n2: Ghost.erased nat) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (nlist n1 raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (nlist n2 raw_data_item)) ->
  stt (option bool)
    (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0
      )
    )
    (fun res ->
pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0 /\
        res == check_equiv_map (option_sz_v map_bound) (List.Tot.hd gl1) (List.Tot.hd gl2)
      )
    )

inline_for_extraction
fn impl_check_equiv_hd_of_check_equiv_map
  (check_equiv_map: Ghost.erased (option nat -> (x1: raw_data_item) -> (x2: raw_data_item) -> option bool)) // FIXME: WHY WHY WHY can this argument not be optional?
  (impl: impl_check_equiv_map_hd_t check_equiv_map)
  (bound: Ghost.erased nat)
  (map_bound: option SZ.t)
: impl_equiv_hd_t (Ghost.reveal bound) (Ghost.reveal check_equiv_map (option_sz_v map_bound))
=
  (n1: Ghost.erased nat)
  (l1: S.slice byte)
  (n2: Ghost.erased nat)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist n1 raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist n2 raw_data_item))
{
  impl map_bound n1 l1 n2 l2
}

inline_for_extraction
fn impl_check_equiv_map_hd_body
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_data_model: impl_data_model_hd_t data_model)
  (impl_check_equiv_map_hd: impl_check_equiv_map_hd_t (check_equiv_map data_model))
: impl_check_equiv_map_hd_t (check_equiv_map data_model)
=
  (map_bound: _)
  (n1: Ghost.erased nat)
  (l1: S.slice byte)
  (n2: Ghost.erased nat)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist n1 raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist n2 raw_data_item))
{
  check_equiv_map_eq data_model (option_sz_v map_bound) (List.Tot.hd gl1) (List.Tot.hd gl2);
  if impl_data_model n1 l1 n2 l2 {
    Some true
  } else {
    let _ = pts_to_serialized_nlist_raw_data_item_head_header' l1 n1;
    let ph1 = nondep_then_fst
      serialize_header
      (jump_header ())
      _
      l1;
    Trade.trans _ _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
    let h1 = read_header () ph1;
    Trade.elim _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
    let _ = pts_to_serialized_nlist_raw_data_item_head_header' l2 n2;
    let ph2 = nondep_then_fst
      serialize_header
      (jump_header ())
      _
      l2;
    Trade.trans _ _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
    let h2 = read_header () ph2;
    Trade.elim _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
    let mt1 = get_header_major_type h1;
    let mt2 = get_header_major_type h2;
    if (mt1 = cbor_major_type_map && mt2 = cbor_major_type_map) {
      if (map_bound = Some 0sz) {
        None
      } else {
        let map_bound' : option SZ.t = (match map_bound with None -> None | Some b -> Some (SZ.sub b 1sz));
        let bound : Ghost.erased nat = Ghost.hide (
          let Map _ v1 = List.Tot.hd gl1 in
          let Map _ v2 = List.Tot.hd gl2 in
          list_sum (pair_sum raw_data_item_size raw_data_item_size) v1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) v2
        );
        assume (pure (SZ.fits_u64));
        let nv1 = SZ.uint64_to_sizet (argument_as_uint64 (dfst h1) (dsnd h1));
        let nv2 = SZ.uint64_to_sizet (argument_as_uint64 (dfst h2) (dsnd h2));
        let map1 = nlist_hd' serialize_raw_data_item (jump_raw_data_item ()) n1 l1 ();
        let mut ph = h1;
        let c1 = get_header_and_contents map1 ph;
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
        get_map_payload c1 (List.Tot.hd gl1);
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
        pts_to_serialized_nlist_ext
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
          (U64.v (Map?.len (List.Tot.hd gl1)).value)
          c1
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
          (SZ.v nv1);
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
        let map2 = nlist_hd' serialize_raw_data_item (jump_raw_data_item ()) n2 l2 ();
        let c2 = get_header_and_contents map2 ph;
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
        get_map_payload c2 (List.Tot.hd gl2);
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
        pts_to_serialized_nlist_ext
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
          (U64.v (Map?.len (List.Tot.hd gl2)).value)
          c2
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
          (SZ.v nv2);
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
        let res = impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow
          (impl_check_equiv_aux
            (impl_check_equiv_hd_of_check_equiv_map
              _
              impl_check_equiv_map_hd 
              bound
              map_bound'
            )
          )
          nv2 c2 nv1 c1;
        if (res = Some true) {
          let res = impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow
          (impl_check_equiv_aux
            (impl_check_equiv_hd_of_check_equiv_map
              _
              impl_check_equiv_map_hd 
              bound
              map_bound'
            )
          )
          nv1 c1 nv2 c2;
          Trade.elim _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
          Trade.elim _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
          res
        } else {
          Trade.elim _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
          Trade.elim _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
          res
        }
      }
    } else {
      Some false
    }
  }
}

#pop-options

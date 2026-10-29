module LowParse.Pulse.Iterator
#lang-pulse
include LowParse.PulseParse.Iterator.Type
include LowParse.PulseParse.Iterator
include LowParse.Pulse.VCList
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module LPS = LowParse.Pulse.Base
module LPV = LowParse.Pulse.VCList
module SM = Pulse.Lib.SeqMatch.Util
module IO = LowParse.PulseParse.Iterator.IntOps

open FStar.Real

// Helper to serialize a list without requiring nlist type
let nlist_serialize_bytes
  (#t: Type0) (#k: parser_kind) (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (n: nat) (l: list t)
: GTot (Seq.seq U8.t)
= if List.Tot.length l = n then bare_serialize (serialize_nlist n s) l else Seq.empty

let nlist_serialize_bytes_correct
  (#t: Type0) (#k: parser_kind) (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (n: nat) (l: list t)
: Lemma
  (requires List.Tot.length l == n)
  (ensures nlist_serialize_bytes s n l == bare_serialize (serialize_nlist n s) l)
= ()

let mixed_list_match_for_l2r
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (n: nat)
  (ml: mixed_list i t)
  (l: nlist n u)
: Tot slprop
= mixed_list_match vmatch io p pm ml l

// Helper: write the contents of a base_mixed_list (Serialized case)
// This copies the serialized bytes from the payload slice to the output.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

inline_for_extraction
```pulse
fn l2r_write_base_serialized
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind) (#p: parser k u)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (j: LPS.jumper p)
  (pm: perm)
  (sp: perm)
  (count: i)
  (pl: S.slice U8.t)
  (len: i { io.v len <= io.v count })
  (l: Ghost.erased (nlist (io.v len) u))
  (out: S.slice U8.t)
  (offset: SZ.t)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
  base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Serialized #i #t sp count pl) l **
  S.pts_to out v **
  pure (
    SZ.v offset + Seq.length (bare_serialize (serialize_nlist (io.v len) s) l) <= Seq.length v
  )
returns res: SZ.t
ensures exists* v' .
  base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Serialized #i #t sp count pl) l **
  S.pts_to out v' **
  pure (
    SZ.v res == SZ.v offset + Seq.length (bare_serialize (serialize_nlist (io.v len) s) l) /\
    SZ.v res <= Seq.length v /\
    Seq.length v' == Seq.length v /\
    Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
    Seq.slice v' (SZ.v offset) (SZ.v res) `Seq.equal` bare_serialize (serialize_nlist (io.v len) s) l
  )
{
  // Unfold to get the raw bytes
  unfold (base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Serialized #i #t sp count pl) l);
  with l_all . assert (pts_to_parsed_strong_prefix (parse_nlist (0 + io.v len) p) pl #(pm *. sp) l_all);
  rewrite (pts_to_parsed_strong_prefix (parse_nlist (0 + io.v len) p) pl #(pm *. sp) l_all)
    as (pts_to_parsed_strong_prefix (parse_nlist (io.v len) p) pl #(pm *. sp) l_all);
  // Elim to get raw S.pts_to
  pts_to_parsed_strong_prefix_elim pl;
  with w . assert (S.pts_to pl #(pm *. sp) w);
  // w parses as l_all, and l == l_all (since off=0)
  // Jump to find byte length.  Obtain size_t witness of the element count.
  S.pts_to_len pl;
  FStar.SizeT.fits_lte (io.v len) (io.v count);
  let len_sz : SZ.t = io.to_sizet len;
  intro_pure (LPS.jumper_pre' (parse_nlist (SZ.v len_sz) p) 0sz w) ();
  let byte_len = LPV.jump_nlist j len_sz pl 0sz;
  // validator_success gives us: consumed == SZ.v byte_len
  // and parse (parse_nlist len p) w = Some (l_all, SZ.v byte_len)
  // By serializer_complete: bare_serialize (serialize_nlist len s) l_all == Seq.slice w 0 (SZ.v byte_len)
  serializer_correct_implies_complete (parse_nlist (io.v len) p) (bare_serialize (serialize_nlist (io.v len) s));
  // This establishes byte_len == Seq.length (bare_serialize ... l) since l == l_all
  validator_success_pos_bound (parse_nlist (SZ.v len_sz) p) w byte_len;
  drop_ (pure (LPS.validator_success (parse_nlist (SZ.v len_sz) p) 0sz w byte_len));
  // Now: SZ.v byte_len <= Seq.length w, byte_len == Seq.length (bare_serialize ...)
  // From precondition: offset + byte_len <= Seq.length v
  S.pts_to_len out;
  // Split output and copy
  let out1, out2 = S.split out offset;
  let out21, out22 = S.split out2 byte_len;
  S.pts_to_len out21;
  // Split source to get the relevant prefix
  let pl1, pl2 = S.split pl byte_len;
  S.pts_to_len pl1;
  S.copy out21 pl1;
  S.join pl1 pl2 pl;
  with w' . assert (S.pts_to pl #(pm *. sp) w');
  Seq.lemma_split (Ghost.reveal w) (SZ.v byte_len);
  rewrite (S.pts_to pl #(pm *. sp) w') as (S.pts_to pl #(pm *. sp) w);
  S.join out21 out22 out2;
  S.join out1 out2 out;
  // Elim trade to get back pts_to_parsed_strong_prefix
  elim_trade (S.pts_to pl #(pm *. sp) w) (pts_to_parsed_strong_prefix (parse_nlist (io.v len) p) pl #(pm *. sp) l_all);
  // Refold
  rewrite (pts_to_parsed_strong_prefix (parse_nlist (io.v len) p) pl #(pm *. sp) l_all)
    as (pts_to_parsed_strong_prefix (parse_nlist (0 + io.v len) p) pl #(pm *. sp) l_all);
  fold (base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Serialized #i #t sp count pl) l);
  let res = SZ.add offset byte_len;
  res
}
```

#pop-options

// Helper: write the contents of a base_mixed_list (Slice case)
// Iterates through elements in the slice and calls the element writer.
#push-options "--z3rlimit 800 --fuel 2 --ifuel 2"

inline_for_extraction
```pulse
fn l2r_write_base_slice
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind) (#p: parser k u)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (w: (pm': perm) -> LPS.l2r_writer (vmatch pm') s)
  (pm: perm)
  (sp: perm)
  (sv: perm)
  (ss: S.slice t)
  (count: i)
  (len: i)
  (l: Ghost.erased (nlist (io.v len) u))
  (out: S.slice U8.t)
  (offset: SZ.t)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
  base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Slice #i #t sp sv ss count) l **
  S.pts_to out v **
  pure (
    SZ.v offset + Seq.length (bare_serialize (serialize_nlist (io.v len) s) l) <= Seq.length v
  )
returns res: SZ.t
ensures exists* v' .
  base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Slice #i #t sp sv ss count) l **
  S.pts_to out v' **
  pure (
    SZ.v res == SZ.v offset + Seq.length (bare_serialize (serialize_nlist (io.v len) s) l) /\
    SZ.v res <= Seq.length v /\
    Seq.length v' == Seq.length v /\
    Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
    Seq.slice v' (SZ.v offset) (SZ.v res) `Seq.equal` bare_serialize (serialize_nlist (io.v len) s) l
  )
{
  // Unfold
  unfold (base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Slice #i #t sp sv ss count) l);
  with l' l1 . assert (
    S.pts_to ss #(pm *. sp) l' **
    SM.seq_list_match l1 l (vmatch (pm *. sv))
  );
  // l1 == Seq.slice l' 0 (io.v len), and io.v len <= Seq.length l'
  SM.seq_list_match_length (vmatch (pm *. sv)) l1 l;
  // Obtain a size_t witness of the element count from the Slice invariant.
  S.pts_to_len ss;
  FStar.SizeT.fits_lte (io.v len) (SZ.v (S.len ss));
  let len_sz : SZ.t = io.to_sizet len;
  // Write elements one by one using a loop
  let mut pres = offset;
  let mut pi = 0sz;
  let pl1 : GR.ref (list u) = GR.alloc #(list u) [];
  Trade.refl (SM.seq_list_match l1 (Ghost.reveal l) (vmatch (pm *. sv)));
  while (
    let ix = !pi;
    SZ.lt ix len_sz
  ) invariant exists* res_v i_v l_done (c2: Seq.seq t) (l_rem: list u) (v_cur: Seq.seq U8.t) .
    R.pts_to pres res_v **
    R.pts_to pi i_v **
    GR.pts_to pl1 l_done **
    S.pts_to ss #(pm *. sp) l' **
    SM.seq_list_match c2 l_rem (vmatch (pm *. sv)) **
    S.pts_to out v_cur **
    trade
      (SM.seq_list_match c2 l_rem (vmatch (pm *. sv)))
      (SM.seq_list_match l1 (Ghost.reveal l) (vmatch (pm *. sv))) **
    pure (
      SZ.v i_v <= SZ.v len_sz /\
      Seq.length l' >= SZ.v len_sz /\
      Seq.equal c2 (Seq.slice l' (SZ.v i_v) (SZ.v len_sz)) /\
      SZ.v offset <= SZ.v res_v /\
      SZ.v res_v <= Seq.length v /\
      Seq.length v_cur == Seq.length v /\
      Seq.slice v_cur 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
      List.Tot.length l_done == SZ.v i_v /\
      Seq.slice v_cur (SZ.v offset) (SZ.v res_v) `Seq.equal` bare_serialize (serialize_nlist (SZ.v i_v) s) l_done /\
      List.Tot.append l_done l_rem == Ghost.reveal l /\
      True
    )
  {
    let ix = !pi;
    let off = !pres;
    SM.seq_list_match_length (vmatch (pm *. sv)) _ _;
    with l_done . assert (GR.pts_to pl1 l_done);
    with c2 l_rem . assert (SM.seq_list_match c2 l_rem (vmatch (pm *. sv)));
    serialize_nlist_append s (SZ.v ix) l_done (SZ.v len_sz - SZ.v ix) l_rem;
    SM.seq_list_match_cons_elim_trade c2 l_rem (vmatch (pm *. sv));
    let e = S.op_Array_Access ss ix;
    with ve l_rem'.
      assert (vmatch (pm *. sv) (Seq.head c2) ve ** SM.seq_list_match (Seq.tail c2) l_rem' (vmatch (pm *. sv)));
    List.Tot.append_assoc l_done [ve] l_rem';
    let ix' = SZ.add ix 1sz;
    let ni' : Ghost.erased nat = Ghost.hide (SZ.v len_sz - SZ.v ix');
    serialize_nlist_cons' (ni') s ve l_rem';
    serialize_nlist_singleton s ve;
    serialize_nlist_append s (SZ.v ix) l_done 1 [ve];
    Trade.rewrite_with_trade
      (vmatch (pm *. sv) (Seq.head c2) ve)
      (vmatch (pm *. sv) e ve);
    with v1 . assert (S.pts_to out v1);
    let off' = w (pm *. sv) e out off;
    with v1' . assert (S.pts_to out v1');
    Trade.elim (vmatch (pm *. sv) e ve) (vmatch (pm *. sv) (Seq.head c2) ve);
    pi := ix';
    List.Tot.append_length l_done [ve];
    let l1' : Ghost.erased (list u) = List.Tot.append l_done [ve];
    GR.write pl1 (Ghost.reveal l1');
    pres := off';
    Trade.elim_hyp_l _ _ _;
    Trade.trans _ _ (SM.seq_list_match l1 (Ghost.reveal l) (vmatch (pm *. sv)));
    assert (pure (SZ.v offset <= SZ.v off'));
    assert (pure (SZ.v off' <= Seq.length v));
    assert (pure (Seq.length v1' == Seq.length v));
    Seq.slice_slice v1 0 (SZ.v off) 0 (SZ.v offset);
    Seq.slice_slice v1' 0 (SZ.v off) 0 (SZ.v offset);
    assert (pure (Seq.slice v1' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset)));
    assert (pure (List.Tot.length (Ghost.reveal l1') == SZ.v ix'));
    Seq.slice_slice v1 0 (SZ.v off) (SZ.v offset) (SZ.v off);
    Seq.slice_slice v1' 0 (SZ.v off) (SZ.v offset) (SZ.v off);
    seq_slice_append_ijk v1' (SZ.v offset) (SZ.v off) (SZ.v off');
    assert (pure (Seq.slice v1' (SZ.v offset) (SZ.v off) `Seq.equal` bare_serialize (serialize_nlist (SZ.v ix) s) l_done));
    assert (pure (Seq.slice v1' (SZ.v off) (SZ.v off') `Seq.equal` bare_serialize s ve));
    assert (pure (Seq.slice v1' (SZ.v offset) (SZ.v off') `Seq.equal` Seq.append (Seq.slice v1' (SZ.v offset) (SZ.v off)) (Seq.slice v1' (SZ.v off) (SZ.v off'))));
    assert (pure (Seq.slice v1' (SZ.v offset) (SZ.v off') `Seq.equal` bare_serialize (serialize_nlist (SZ.v ix') s) (Ghost.reveal l1')));
    Seq.lemma_tail_slice l' (SZ.v ix) (SZ.v len_sz);
    assert (pure (Seq.equal (Seq.tail c2) (Seq.slice l' (SZ.v ix') (SZ.v len_sz))));
    assert (pure (ve == List.Tot.hd l_rem));
    assert (pure (l_rem' == List.Tot.tl l_rem));
  };
  with res_v i_v l_done c2_end l_rem_end v_cur .
    assert (R.pts_to pres res_v ** R.pts_to pi i_v ** GR.pts_to pl1 l_done);
  SM.seq_list_match_length (vmatch (pm *. sv)) _ _;
  List.Tot.append_l_nil l_done;
  assert (pure (l_done == Ghost.reveal l));
  GR.free pl1;
  elim_trade
    (SM.seq_list_match _ _ (vmatch (pm *. sv)))
    (SM.seq_list_match l1 (Ghost.reveal l) (vmatch (pm *. sv)));
  fold (base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Slice #i #t sp sv ss count) l);
  !pres
}
```

#pop-options

// Helper: write the contents of a base_mixed_list (Singleton case)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

inline_for_extraction
```pulse
fn l2r_write_base_singleton
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind) (#p: parser k u)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (w: (pm': perm) -> LPS.l2r_writer (vmatch pm') s)
  (pm: perm)
  (sp: perm)
  (sv: perm)
  (sr: ref t)
  (l: Ghost.erased (nlist 1 u))
  (out: S.slice U8.t)
  (offset: SZ.t)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
  base_mixed_list_match_n vmatch io p 0 1 pm (Singleton #i #t sp sv sr) l **
  S.pts_to out v **
  pure (
    SZ.v offset + Seq.length (bare_serialize (serialize_nlist 1 s) l) <= Seq.length v
  )
returns res: SZ.t
ensures exists* v' .
  base_mixed_list_match_n vmatch io p 0 1 pm (Singleton #i #t sp sv sr) l **
  S.pts_to out v' **
  pure (
    SZ.v res == SZ.v offset + Seq.length (bare_serialize (serialize_nlist 1 s) l) /\
    SZ.v res <= Seq.length v /\
    Seq.length v' == Seq.length v /\
    Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
    Seq.slice v' (SZ.v offset) (SZ.v res) `Seq.equal` bare_serialize (serialize_nlist 1 s) l
  )
{
  unfold (base_mixed_list_match_n vmatch io p 0 1 pm (Singleton #i #t sp sv sr) l);
  with x y . assert (R.pts_to sr #(pm *. sp) x ** vmatch (pm *. sv) x y);
  // y is the single element, l == [y]
  serialize_nlist_singleton s y;
  let xv = R.op_Bang sr;
  let off' = w (pm *. sv) xv out offset;
  fold (base_mixed_list_match_n vmatch io p 0 1 pm (Singleton #i #t sp sv sr) l);
  off'
}
```

#pop-options

// Main writer: the full l2r_writer for mixed_list_match
// Uses a loop that repeatedly:
// 1. Extracts the first base chunk (via extract_first_base_loop)
// 2. Writes it (Serialized: copy bytes, Slice: element writer loop, Singleton: element writer)
// 3. Narrows to the remaining portion (via mixed_list_narrow_n)
#push-options "--z3rlimit 32000 --fuel 2 --ifuel 2"

inline_for_extraction
```pulse
fn l2r_write_mixed_list
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (#p: parser k u)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (w: (pm': perm) -> LPS.l2r_writer (vmatch pm') s)
  (j: LPS.jumper p)
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (pm: perm)
  (n: i)
: LPS.l2r_writer #_ #(nlist (io.v n) u) (mixed_list_match_for_l2r vmatch io p pm (io.v n)) (serialize_nlist (io.v n) s)
= (ml: mixed_list i t)
  (#l: Ghost.erased (nlist (io.v n) u))
  (out: S.slice U8.t)
  (offset: SZ.t)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  unfold (mixed_list_match_for_l2r vmatch io p pm (io.v n) ml l);
  if (io.eq n io.zero) {
    // Empty list: nothing to write
    serialize_nlist_nil p s;
    mixed_list_match_length vmatch io p pm ml l;
    fold (mixed_list_match_for_l2r vmatch io p pm (io.v n) ml l);
    offset
  } else {
    // Non-empty: use loop to process base chunks
    let mut p_node = ml;
    let mut p_offset = offset;
    let mut p_remaining = n;
    // Ghost ref for tracking elements written so far
    let pl_done : GR.ref (list u) = GR.alloc #(list u) [];
    // Coerce l to plain list u for use in invariant
    let l_as_list : Ghost.erased (list u) = Ghost.hide (Ghost.reveal l <: list u);
    // Unfold to mixed_list_match_n for the loop
    mixed_list_match_length vmatch io p pm ml l;
    // Create a trade: mixed_list_match -> mixed_list_match_n
    rewrite (mixed_list_match vmatch io p pm ml (Ghost.reveal l))
      as (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
    Trade.rewrite_with_trade
      (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l))
      (mixed_list_match vmatch io p pm ml (Ghost.reveal l));
    serialize_nlist_nil p s;
    while (
      let rem = !p_remaining;
      io.gt rem io.zero
    ) invariant exists* cur_node cur_off cur_rem cur_pm l_done l_rem v_cur . (
      R.pts_to p_node cur_node **
      R.pts_to p_offset cur_off **
      R.pts_to p_remaining cur_rem **
      GR.pts_to pl_done l_done **
      mixed_list_match vmatch io p cur_pm cur_node l_rem **
      trade
        (mixed_list_match vmatch io p cur_pm cur_node l_rem)
        (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l)) **
      S.pts_to out v_cur **
      pure (
        io.v cur_rem <= io.v n /\
        List.Tot.length l_done == io.v n - io.v cur_rem /\
        List.Tot.length l_rem == io.v cur_rem /\
        Ghost.reveal l_as_list == List.Tot.append l_done l_rem /\
        SZ.v offset <= SZ.v cur_off /\
        SZ.v cur_off + Seq.length (bare_serialize (serialize_nlist (io.v cur_rem) s) l_rem) <= Seq.length v_cur /\
        Seq.length v_cur == Seq.length v /\
        Seq.slice v_cur 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
        Seq.slice v_cur (SZ.v offset) (SZ.v cur_off) `Seq.equal` bare_serialize (serialize_nlist (io.v n - io.v cur_rem) s) l_done /\
        io.v (mixed_list_length io cur_node) == io.v cur_rem
      )
    )
    {
      let cur = !p_node;
      let cur_off = !p_offset;
      let cur_rem = !p_remaining;
      with cur_pm l_rem . assert (mixed_list_match vmatch io p cur_pm cur l_rem);
      with l_done . assert (GR.pts_to pl_done l_done);
      // Unfold mixed_list_match to mixed_list_match_n
      rewrite (mixed_list_match vmatch io p cur_pm cur l_rem)
        as (mixed_list_match_n vmatch io p 0 (io.v (mixed_list_length io cur)) cur_pm cur l_rem);
      rewrite (mixed_list_match_n vmatch io p 0 (io.v (mixed_list_length io cur)) cur_pm cur l_rem)
        as (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem);
      // Extract first base
      let res = mixed_list_extract_first_base_loop vmatch io p j 0 (io.v cur_rem) io.zero cur_rem cur_pm cur l_rem;
      let bi = fst res;
      let chunk_len = snd res;
      rewrite (
        (let (bi', len') = res in
         base_mixed_list_match vmatch io p cur_pm bi' (list_narrow l_rem 0 (io.v len')) **
         trade (base_mixed_list_match vmatch io p cur_pm bi' (list_narrow l_rem 0 (io.v len')))
              (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem) **
         pure (io.v len' == io.v (base_mixed_list_length io bi') /\ io.v len' > 0 /\ io.v len' <= io.v cur_rem)))
        as (base_mixed_list_match vmatch io p cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)) **
            trade (base_mixed_list_match vmatch io p cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)))
                 (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem) **
            pure (io.v chunk_len == io.v (base_mixed_list_length io bi) /\ io.v chunk_len > 0 /\ io.v chunk_len <= io.v cur_rem));
      // Write the base chunk
      rewrite (base_mixed_list_match vmatch io p cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)))
        as (base_mixed_list_match_n vmatch io p 0 (io.v (base_mixed_list_length io bi)) cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)));
      rewrite (base_mixed_list_match_n vmatch io p 0 (io.v (base_mixed_list_length io bi)) cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)))
        as (base_mixed_list_match_n vmatch io p 0 (io.v chunk_len) cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)));
      // Dispatch on base type — each branch writes, folds, elim_trades, and does narrow + trade + hints
      match bi {
        Serialized sp_bi count_bi pl_bi -> {
          // Prove the chunk serialization fits in the remaining space
          list_narrow_split l_rem (io.v chunk_len);
          list_narrow_length l_rem 0 (io.v chunk_len);
          list_narrow_length l_rem (io.v chunk_len) (io.v cur_rem - io.v chunk_len);
          serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v cur_rem - io.v chunk_len) (list_narrow l_rem (io.v chunk_len) (io.v cur_rem - io.v chunk_len));
          with v_cur . assert (S.pts_to out v_cur);
          let off' = l2r_write_base_serialized vmatch io s j cur_pm sp_bi count_bi pl_bi chunk_len (list_narrow l_rem 0 (io.v chunk_len)) out cur_off;
          with v' . assert (S.pts_to out v');
          // Derive: slice v' 0 offset == slice v 0 offset
          Seq.slice_slice v_cur 0 (SZ.v cur_off) 0 (SZ.v offset);
          Seq.slice_slice v' 0 (SZ.v cur_off) 0 (SZ.v offset);
          rewrite (base_mixed_list_match_n vmatch io p 0 (io.v chunk_len) cur_pm (Serialized #i #t sp_bi count_bi pl_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            as (base_mixed_list_match vmatch io p cur_pm (Serialized #i #t sp_bi count_bi pl_bi) (list_narrow l_rem 0 (io.v chunk_len)));
          elim_trade
            (base_mixed_list_match vmatch io p cur_pm (Serialized #i #t sp_bi count_bi pl_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem);
          let new_rem = io.sub cur_rem chunk_len;
          let new_node = mixed_list_narrow_n vmatch io p j 0 (io.v cur_rem) cur_pm cur l_rem chunk_len new_rem vmatch_share vmatch_gather;
          rewrite (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem)))
            as (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)));
          rewrite (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem))) (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem))
            as (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem))) (mixed_list_match vmatch io p cur_pm cur l_rem));
          Trade.trans
            (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)))
            (mixed_list_match vmatch io p cur_pm cur l_rem)
            (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
          List.Tot.append_length l_done (list_narrow l_rem 0 (io.v chunk_len));
          list_narrow_length l_rem 0 (io.v chunk_len);
          list_narrow_length l_rem (io.v chunk_len) (io.v new_rem);
          list_narrow_split l_rem (io.v chunk_len);
          List.Tot.append_assoc l_done (list_narrow l_rem 0 (io.v chunk_len)) (list_narrow l_rem (io.v chunk_len) (io.v new_rem));
          serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v new_rem) (list_narrow l_rem (io.v chunk_len) (io.v new_rem));
          // Assert each invariant conjunct individually
          assert (pure (io.v new_rem <= io.v n));
          assert (pure (List.Tot.length (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len))) == io.v n - io.v new_rem));
          assert (pure (List.Tot.length (list_narrow l_rem (io.v chunk_len) (io.v new_rem)) == io.v new_rem));
          assert (pure (Ghost.reveal l_as_list == List.Tot.append (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len))) (list_narrow l_rem (io.v chunk_len) (io.v new_rem))));
          assert (pure (SZ.v offset <= SZ.v off'));
          assert (pure (SZ.v off' + Seq.length (bare_serialize (serialize_nlist (io.v new_rem) s) (list_narrow l_rem (io.v chunk_len) (io.v new_rem))) <= Seq.length v'));
          assert (pure (Seq.length v' == Seq.length v));
          assert (pure (Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset)));
          Seq.slice_slice v_cur 0 (SZ.v cur_off) (SZ.v offset) (SZ.v cur_off);
          Seq.slice_slice v' 0 (SZ.v cur_off) (SZ.v offset) (SZ.v cur_off);
          seq_slice_append_ijk v' (SZ.v offset) (SZ.v cur_off) (SZ.v off');
          serialize_nlist_append s (io.v n - io.v cur_rem) l_done (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len));
          assert (pure (Seq.slice v' (SZ.v offset) (SZ.v off') `Seq.equal` bare_serialize (serialize_nlist (io.v n - io.v new_rem) s) (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len)))));
          GR.op_Colon_Equals pl_done (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len)));
          p_node := new_node;
          p_offset := off';
          p_remaining := new_rem;
        }
        Slice sp_bi sv_bi ss_bi count_bi -> {
          list_narrow_split l_rem (io.v chunk_len);
          list_narrow_length l_rem 0 (io.v chunk_len);
          list_narrow_length l_rem (io.v chunk_len) (io.v cur_rem - io.v chunk_len);
          serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v cur_rem - io.v chunk_len) (list_narrow l_rem (io.v chunk_len) (io.v cur_rem - io.v chunk_len));
          with v_cur . assert (S.pts_to out v_cur);
          let off' = l2r_write_base_slice vmatch io s w cur_pm sp_bi sv_bi ss_bi count_bi chunk_len (list_narrow l_rem 0 (io.v chunk_len)) out cur_off;
          with v' . assert (S.pts_to out v');
          Seq.slice_slice v_cur 0 (SZ.v cur_off) 0 (SZ.v offset);
          Seq.slice_slice v' 0 (SZ.v cur_off) 0 (SZ.v offset);
          rewrite (base_mixed_list_match_n vmatch io p 0 (io.v chunk_len) cur_pm (Slice #i #t sp_bi sv_bi ss_bi count_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            as (base_mixed_list_match vmatch io p cur_pm (Slice #i #t sp_bi sv_bi ss_bi count_bi) (list_narrow l_rem 0 (io.v chunk_len)));
          elim_trade
            (base_mixed_list_match vmatch io p cur_pm (Slice #i #t sp_bi sv_bi ss_bi count_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem);
          let new_rem = io.sub cur_rem chunk_len;
          let new_node = mixed_list_narrow_n vmatch io p j 0 (io.v cur_rem) cur_pm cur l_rem chunk_len new_rem vmatch_share vmatch_gather;
          rewrite (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem)))
            as (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)));
          rewrite (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem))) (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem))
            as (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem))) (mixed_list_match vmatch io p cur_pm cur l_rem));
          Trade.trans
            (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)))
            (mixed_list_match vmatch io p cur_pm cur l_rem)
            (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
          List.Tot.append_length l_done (list_narrow l_rem 0 (io.v chunk_len));
          list_narrow_length l_rem 0 (io.v chunk_len);
          list_narrow_length l_rem (io.v chunk_len) (io.v new_rem);
          list_narrow_split l_rem (io.v chunk_len);
          List.Tot.append_assoc l_done (list_narrow l_rem 0 (io.v chunk_len)) (list_narrow l_rem (io.v chunk_len) (io.v new_rem));
          serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v new_rem) (list_narrow l_rem (io.v chunk_len) (io.v new_rem));
          assert (pure (io.v new_rem <= io.v n));
          assert (pure (List.Tot.length (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len))) == io.v n - io.v new_rem));
          assert (pure (List.Tot.length (list_narrow l_rem (io.v chunk_len) (io.v new_rem)) == io.v new_rem));
          assert (pure (Ghost.reveal l_as_list == List.Tot.append (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len))) (list_narrow l_rem (io.v chunk_len) (io.v new_rem))));
          assert (pure (SZ.v offset <= SZ.v off'));
          assert (pure (SZ.v off' + Seq.length (bare_serialize (serialize_nlist (io.v new_rem) s) (list_narrow l_rem (io.v chunk_len) (io.v new_rem))) <= Seq.length v'));
          assert (pure (Seq.length v' == Seq.length v));
          assert (pure (Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset)));
          Seq.slice_slice v_cur 0 (SZ.v cur_off) (SZ.v offset) (SZ.v cur_off);
          Seq.slice_slice v' 0 (SZ.v cur_off) (SZ.v offset) (SZ.v cur_off);
          seq_slice_append_ijk v' (SZ.v offset) (SZ.v cur_off) (SZ.v off');
          serialize_nlist_append s (io.v n - io.v cur_rem) l_done (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len));
          assert (pure (Seq.slice v' (SZ.v offset) (SZ.v off') `Seq.equal` bare_serialize (serialize_nlist (io.v n - io.v new_rem) s) (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len)))));
          GR.op_Colon_Equals pl_done (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len)));
          p_node := new_node;
          p_offset := off';
          p_remaining := new_rem;
        }
        Singleton sp_bi sv_bi sr_bi -> {
          list_narrow_split l_rem (io.v chunk_len);
          list_narrow_length l_rem 0 (io.v chunk_len);
          list_narrow_length l_rem (io.v chunk_len) (io.v cur_rem - io.v chunk_len);
          serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v cur_rem - io.v chunk_len) (list_narrow l_rem (io.v chunk_len) (io.v cur_rem - io.v chunk_len));
          rewrite (base_mixed_list_match_n vmatch io p 0 (io.v chunk_len) cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            as (base_mixed_list_match_n vmatch io p 0 1 cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)));
          with v_cur . assert (S.pts_to out v_cur);
          let off' = l2r_write_base_singleton vmatch io s w cur_pm sp_bi sv_bi sr_bi (list_narrow l_rem 0 (io.v chunk_len)) out cur_off;
          with v' . assert (S.pts_to out v');
          Seq.slice_slice v_cur 0 (SZ.v cur_off) 0 (SZ.v offset);
          Seq.slice_slice v' 0 (SZ.v cur_off) 0 (SZ.v offset);
          rewrite (base_mixed_list_match_n vmatch io p 0 1 cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            as (base_mixed_list_match vmatch io p cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)));
          elim_trade
            (base_mixed_list_match vmatch io p cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem);
          let new_rem = io.sub cur_rem chunk_len;
          let new_node = mixed_list_narrow_n vmatch io p j 0 (io.v cur_rem) cur_pm cur l_rem chunk_len new_rem vmatch_share vmatch_gather;
          rewrite (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem)))
            as (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)));
          rewrite (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem))) (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem))
            as (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem))) (mixed_list_match vmatch io p cur_pm cur l_rem));
          Trade.trans
            (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)))
            (mixed_list_match vmatch io p cur_pm cur l_rem)
            (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
          List.Tot.append_length l_done (list_narrow l_rem 0 (io.v chunk_len));
          list_narrow_length l_rem 0 (io.v chunk_len);
          list_narrow_length l_rem (io.v chunk_len) (io.v new_rem);
          list_narrow_split l_rem (io.v chunk_len);
          List.Tot.append_assoc l_done (list_narrow l_rem 0 (io.v chunk_len)) (list_narrow l_rem (io.v chunk_len) (io.v new_rem));
          serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v new_rem) (list_narrow l_rem (io.v chunk_len) (io.v new_rem));
          assert (pure (io.v new_rem <= io.v n));
          assert (pure (List.Tot.length (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len))) == io.v n - io.v new_rem));
          assert (pure (List.Tot.length (list_narrow l_rem (io.v chunk_len) (io.v new_rem)) == io.v new_rem));
          assert (pure (Ghost.reveal l_as_list == List.Tot.append (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len))) (list_narrow l_rem (io.v chunk_len) (io.v new_rem))));
          assert (pure (SZ.v offset <= SZ.v off'));
          assert (pure (SZ.v off' + Seq.length (bare_serialize (serialize_nlist (io.v new_rem) s) (list_narrow l_rem (io.v chunk_len) (io.v new_rem))) <= Seq.length v'));
          assert (pure (Seq.length v' == Seq.length v));
          assert (pure (Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset)));
          Seq.slice_slice v_cur 0 (SZ.v cur_off) (SZ.v offset) (SZ.v cur_off);
          Seq.slice_slice v' 0 (SZ.v cur_off) (SZ.v offset) (SZ.v cur_off);
          seq_slice_append_ijk v' (SZ.v offset) (SZ.v cur_off) (SZ.v off');
          serialize_nlist_append s (io.v n - io.v cur_rem) l_done (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len));
          assert (pure (Seq.slice v' (SZ.v offset) (SZ.v off') `Seq.equal` bare_serialize (serialize_nlist (io.v n - io.v new_rem) s) (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len)))));
          GR.op_Colon_Equals pl_done (l_done `List.Tot.append` (list_narrow l_rem 0 (io.v chunk_len)));
          p_node := new_node;
          p_offset := off';
          p_remaining := new_rem;
        }
        Empty -> {
          // Unreachable: chunk_len > 0 from extract_first_base_loop
          unreachable ()
        }
      }
    };
    // Loop done: free ghost ref and elim trade
    with l_done . assert (GR.pts_to pl_done l_done);
    GR.free pl_done;
    with cur_pm l_rem . assert (mixed_list_match vmatch io p cur_pm _ l_rem);
    elim_trade
      (mixed_list_match vmatch io p cur_pm _ l_rem)
      (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
    rewrite (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l))
      as (mixed_list_match vmatch io p pm ml (Ghost.reveal l));
    fold (mixed_list_match_for_l2r vmatch io p pm (io.v n) ml l);
    let res = !p_offset;
    with v_final . assert (S.pts_to out v_final);
    // After loop: cur_rem == 0, so l_done == l and content is fully written
    List.Tot.append_l_nil l_done;
    assert (pure (SZ.v res == SZ.v offset + Seq.length (bare_serialize (serialize_nlist (io.v n) s) (Ghost.reveal l))));
    assert (pure (SZ.v res <= Seq.length v));
    assert (pure (Seq.length v_final == Seq.length v));
    assert (pure (Seq.slice v_final 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset)));
    assert (pure (Seq.slice v_final (SZ.v offset) (SZ.v res) `Seq.equal` bare_serialize (serialize_nlist (io.v n) s) (Ghost.reveal l)));
    res
  }
}
```

#pop-options

// =============================================
// compute_remaining_size for mixed_list_match
// =============================================

// Helper: compute_remaining_size for base_mixed_list (Serialized case)
// Just jumps to find the byte length and subtracts from remaining.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

inline_for_extraction
```pulse
fn compute_remaining_size_base_serialized
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind) (#p: parser k u)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (j: LPS.jumper p)
  (pm: perm)
  (sp: perm)
  (count: i)
  (pl: S.slice U8.t)
  (len: i)
  (l: Ghost.erased (nlist (io.v len) u))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
requires
  base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Serialized #i #t sp count pl) l **
  R.pts_to out v
returns res: bool
ensures exists* v' .
  base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Serialized #i #t sp count pl) l **
  R.pts_to out v' **
  pure (
    let bs = Seq.length (bare_serialize (serialize_nlist (io.v len) s) l) in
    (res == true <==> bs <= SZ.v v) /\
    (res == true ==> bs + SZ.v v' == SZ.v v)
  )
{
  unfold (base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Serialized #i #t sp count pl) l);
  with l_all . assert (pts_to_parsed_strong_prefix (parse_nlist (0 + io.v len) p) pl #(pm *. sp) l_all);
  rewrite (pts_to_parsed_strong_prefix (parse_nlist (0 + io.v len) p) pl #(pm *. sp) l_all)
    as (pts_to_parsed_strong_prefix (parse_nlist (io.v len) p) pl #(pm *. sp) l_all);
  pts_to_parsed_strong_prefix_elim pl;
  with w . assert (S.pts_to pl #(pm *. sp) w);
  S.pts_to_len pl;
  FStar.SizeT.fits_lte (io.v len) (io.v count);
  let len_sz : SZ.t = io.to_sizet len;
  intro_pure (LPS.jumper_pre' (parse_nlist (SZ.v len_sz) p) 0sz w) ();
  let byte_len = LPV.jump_nlist j len_sz pl 0sz;
  serializer_correct_implies_complete (parse_nlist (io.v len) p) (bare_serialize (serialize_nlist (io.v len) s));
  validator_success_pos_bound (parse_nlist (SZ.v len_sz) p) w byte_len;
  drop_ (pure (LPS.validator_success (parse_nlist (SZ.v len_sz) p) 0sz w byte_len));
  elim_trade (S.pts_to pl #(pm *. sp) w) (pts_to_parsed_strong_prefix (parse_nlist (io.v len) p) pl #(pm *. sp) l_all);
  rewrite (pts_to_parsed_strong_prefix (parse_nlist (io.v len) p) pl #(pm *. sp) l_all)
    as (pts_to_parsed_strong_prefix (parse_nlist (0 + io.v len) p) pl #(pm *. sp) l_all);
  fold (base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Serialized #i #t sp count pl) l);
  let remaining = !out;
  if (SZ.lte byte_len remaining) {
    out := SZ.sub remaining byte_len;
    true
  } else {
    false
  }
}
```

#pop-options

// Helper: compute_remaining_size for base_mixed_list (Slice case)
// Iterates through elements calling per-element compute_remaining_size.
#push-options "--z3rlimit 800 --fuel 2 --ifuel 2"

inline_for_extraction
```pulse
fn compute_remaining_size_base_slice
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind) (#p: parser k u)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (cr: (pm': perm) -> LPS.compute_remaining_size (vmatch pm') s)
  (pm: perm)
  (sp: perm)
  (sv: perm)
  (ss: S.slice t)
  (count: i)
  (len: i)
  (l: Ghost.erased (nlist (io.v len) u))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
requires
  base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Slice #i #t sp sv ss count) l **
  R.pts_to out v
returns res: bool
ensures exists* v' .
  base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Slice #i #t sp sv ss count) l **
  R.pts_to out v' **
  pure (
    let bs = Seq.length (bare_serialize (serialize_nlist (io.v len) s) l) in
    (res == true <==> bs <= SZ.v v) /\
    (res == true ==> bs + SZ.v v' == SZ.v v)
  )
{
  unfold (base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Slice #i #t sp sv ss count) l);
  with l' l1 . assert (
    S.pts_to ss #(pm *. sp) l' **
    SM.seq_list_match l1 l (vmatch (pm *. sv))
  );
  SM.seq_list_match_length (vmatch (pm *. sv)) l1 l;
  S.pts_to_len ss;
  FStar.SizeT.fits_lte (io.v len) (SZ.v (S.len ss));
  let len_sz : SZ.t = io.to_sizet len;
  let mut pres = true;
  let mut pi = 0sz;
  Trade.refl (SM.seq_list_match l1 (Ghost.reveal l) (vmatch (pm *. sv)));
  while (
    let res = !pres;
    let ix = !pi;
    (res && (SZ.lt ix len_sz))
  ) invariant exists* res_v i_v (c2: Seq.seq t) (l_rem: list u) v1 . (
    R.pts_to pres res_v **
    R.pts_to pi i_v **
    S.pts_to ss #(pm *. sp) l' **
    SM.seq_list_match c2 l_rem (vmatch (pm *. sv)) **
    R.pts_to out v1 **
    trade
      (SM.seq_list_match c2 l_rem (vmatch (pm *. sv)))
      (SM.seq_list_match l1 (Ghost.reveal l) (vmatch (pm *. sv))) **
    pure (
      SZ.v i_v <= SZ.v len_sz /\
      Seq.length l' >= SZ.v len_sz /\
      Seq.equal c2 (Seq.slice l' (SZ.v i_v) (SZ.v len_sz)) /\
      List.Tot.length l_rem == SZ.v len_sz - SZ.v i_v /\
      (res_v == false ==> SZ.v v < Seq.length (bare_serialize (serialize_nlist (SZ.v len_sz) s) (Ghost.reveal l))) /\
      (res_v == true ==> (
        SZ.v v - Seq.length (bare_serialize (serialize_nlist (SZ.v len_sz) s) (Ghost.reveal l)) == SZ.v v1 - Seq.length (bare_serialize (serialize_nlist (SZ.v len_sz - SZ.v i_v) s) l_rem)
      ))
    )
  ) {
    let ix = !pi;
    SM.seq_list_match_length (vmatch (pm *. sv)) _ _;
    with c2 l_rem . assert (SM.seq_list_match c2 l_rem (vmatch (pm *. sv)));
    SM.seq_list_match_cons_elim_trade c2 l_rem (vmatch (pm *. sv));
    let e = S.op_Array_Access ss ix;
    with ve l_rem'.
      assert (vmatch (pm *. sv) (Seq.head c2) ve ** SM.seq_list_match (Seq.tail c2) l_rem' (vmatch (pm *. sv)));
    let ni' : Ghost.erased nat = Ghost.hide (SZ.v len_sz - SZ.v ix - 1);
    serialize_nlist_cons' (ni') s ve l_rem';
    Trade.rewrite_with_trade
      (vmatch (pm *. sv) (Seq.head c2) ve)
      (vmatch (pm *. sv) e ve);
    let res = cr (pm *. sv) e out;
    Trade.elim (vmatch (pm *. sv) e ve) (vmatch (pm *. sv) (Seq.head c2) ve);
    if (res) {
      let ix' = SZ.add ix 1sz;
      pi := ix';
      Trade.elim_hyp_l _ _ _;
      Trade.trans _ _ (SM.seq_list_match l1 (Ghost.reveal l) (vmatch (pm *. sv)));
      Seq.lemma_tail_slice l' (SZ.v ix) (SZ.v len_sz);
    } else {
      Trade.elim _ (SM.seq_list_match c2 l_rem (vmatch (pm *. sv)));
      pres := false;
    }
  };
  Trade.elim _ _;
  fold (base_mixed_list_match_n vmatch io p 0 (io.v len) pm (Slice #i #t sp sv ss count) l);
  !pres
}
```

#pop-options

// Helper: compute_remaining_size for base_mixed_list (Singleton case)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

inline_for_extraction
```pulse
fn compute_remaining_size_base_singleton
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind) (#p: parser k u)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (cr: (pm': perm) -> LPS.compute_remaining_size (vmatch pm') s)
  (pm: perm)
  (sp: perm)
  (sv: perm)
  (sr: ref t)
  (l: Ghost.erased (nlist 1 u))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
requires
  base_mixed_list_match_n vmatch io p 0 1 pm (Singleton #i #t sp sv sr) l **
  R.pts_to out v
returns res: bool
ensures exists* v' .
  base_mixed_list_match_n vmatch io p 0 1 pm (Singleton #i #t sp sv sr) l **
  R.pts_to out v' **
  pure (
    let bs = Seq.length (bare_serialize (serialize_nlist 1 s) l) in
    (res == true <==> bs <= SZ.v v) /\
    (res == true ==> bs + SZ.v v' == SZ.v v)
  )
{
  unfold (base_mixed_list_match_n vmatch io p 0 1 pm (Singleton #i #t sp sv sr) l);
  with x y . assert (R.pts_to sr #(pm *. sp) x ** vmatch (pm *. sv) x y);
  serialize_nlist_singleton s y;
  let xv = R.op_Bang sr;
  let res = cr (pm *. sv) xv out;
  fold (base_mixed_list_match_n vmatch io p 0 1 pm (Singleton #i #t sp sv sr) l);
  res
}
```

#pop-options

// Main compute_remaining_size for mixed_list_match
#push-options "--z3rlimit 32000 --fuel 2 --ifuel 2"

inline_for_extraction
```pulse
fn compute_remaining_size_mixed_list
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (#p: parser k u)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (cr: (pm': perm) -> LPS.compute_remaining_size (vmatch pm') s)
  (j: LPS.jumper p)
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (pm: perm)
  (n: i)
: LPS.compute_remaining_size #_ #(nlist (io.v n) u) (mixed_list_match_for_l2r vmatch io p pm (io.v n)) (serialize_nlist (io.v n) s)
= (ml: mixed_list i t)
  (#l: Ghost.erased (nlist (io.v n) u))
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
{
  unfold (mixed_list_match_for_l2r vmatch io p pm (io.v n) ml l);
  if (io.eq n io.zero) {
    serialize_nlist_nil p s;
    mixed_list_match_length vmatch io p pm ml l;
    fold (mixed_list_match_for_l2r vmatch io p pm (io.v n) ml l);
    true
  } else {
    let mut p_node = ml;
    let mut p_remaining = n;
    let mut p_result = true;
    mixed_list_match_length vmatch io p pm ml l;
    rewrite (mixed_list_match vmatch io p pm ml (Ghost.reveal l))
      as (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
    Trade.rewrite_with_trade
      (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l))
      (mixed_list_match vmatch io p pm ml (Ghost.reveal l));
    serialize_nlist_nil p s;
    while (
      let res = !p_result;
      let rem = !p_remaining;
      (res && io.gt rem io.zero)
    ) invariant exists* cur_node cur_rem cur_pm l_rem v1 res_v . (
      R.pts_to p_node cur_node **
      R.pts_to p_remaining cur_rem **
      R.pts_to p_result res_v **
      R.pts_to out v1 **
      mixed_list_match vmatch io p cur_pm cur_node l_rem **
      trade
        (mixed_list_match vmatch io p cur_pm cur_node l_rem)
        (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l)) **
      pure (
        io.v cur_rem <= io.v n /\
        List.Tot.length l_rem == io.v cur_rem /\
        io.v (mixed_list_length io cur_node) == io.v cur_rem /\
        (res_v == false ==> SZ.v v < Seq.length (bare_serialize (serialize_nlist (io.v n) s) (Ghost.reveal l))) /\
        (res_v == true ==> (
          SZ.v v - Seq.length (bare_serialize (serialize_nlist (io.v n) s) (Ghost.reveal l)) == SZ.v v1 - Seq.length (bare_serialize (serialize_nlist (io.v cur_rem) s) l_rem)
        ))
      )
    )
    {
      let cur = !p_node;
      let cur_rem = !p_remaining;
      with cur_pm l_rem . assert (mixed_list_match vmatch io p cur_pm cur l_rem);
      rewrite (mixed_list_match vmatch io p cur_pm cur l_rem)
        as (mixed_list_match_n vmatch io p 0 (io.v (mixed_list_length io cur)) cur_pm cur l_rem);
      rewrite (mixed_list_match_n vmatch io p 0 (io.v (mixed_list_length io cur)) cur_pm cur l_rem)
        as (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem);
      let res = mixed_list_extract_first_base_loop vmatch io p j 0 (io.v cur_rem) io.zero cur_rem cur_pm cur l_rem;
      let bi = fst res;
      let chunk_len = snd res;
      rewrite (
        (let (bi', len') = res in
         base_mixed_list_match vmatch io p cur_pm bi' (list_narrow l_rem 0 (io.v len')) **
         trade (base_mixed_list_match vmatch io p cur_pm bi' (list_narrow l_rem 0 (io.v len')))
              (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem) **
         pure (io.v len' == io.v (base_mixed_list_length io bi') /\ io.v len' > 0 /\ io.v len' <= io.v cur_rem)))
        as (base_mixed_list_match vmatch io p cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)) **
            trade (base_mixed_list_match vmatch io p cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)))
                 (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem) **
            pure (io.v chunk_len == io.v (base_mixed_list_length io bi) /\ io.v chunk_len > 0 /\ io.v chunk_len <= io.v cur_rem));
      rewrite (base_mixed_list_match vmatch io p cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)))
        as (base_mixed_list_match_n vmatch io p 0 (io.v (base_mixed_list_length io bi)) cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)));
      rewrite (base_mixed_list_match_n vmatch io p 0 (io.v (base_mixed_list_length io bi)) cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)))
        as (base_mixed_list_match_n vmatch io p 0 (io.v chunk_len) cur_pm bi (list_narrow l_rem 0 (io.v chunk_len)));
      list_narrow_length l_rem 0 (io.v chunk_len);
      list_narrow_length l_rem (io.v chunk_len) (io.v cur_rem - io.v chunk_len);
      list_narrow_split l_rem (io.v chunk_len);
      serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v cur_rem - io.v chunk_len) (list_narrow l_rem (io.v chunk_len) (io.v cur_rem - io.v chunk_len));
      match bi {
        Serialized sp_bi count_bi pl_bi -> {
          let chunk_res = compute_remaining_size_base_serialized vmatch io s j cur_pm sp_bi count_bi pl_bi chunk_len (list_narrow l_rem 0 (io.v chunk_len)) out;
          rewrite (base_mixed_list_match_n vmatch io p 0 (io.v chunk_len) cur_pm (Serialized #i #t sp_bi count_bi pl_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            as (base_mixed_list_match vmatch io p cur_pm (Serialized #i #t sp_bi count_bi pl_bi) (list_narrow l_rem 0 (io.v chunk_len)));
          elim_trade
            (base_mixed_list_match vmatch io p cur_pm (Serialized #i #t sp_bi count_bi pl_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem);
          let new_rem = io.sub cur_rem chunk_len;
          let new_node = mixed_list_narrow_n vmatch io p j 0 (io.v cur_rem) cur_pm cur l_rem chunk_len new_rem vmatch_share vmatch_gather;
          rewrite (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem)))
            as (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)));
          rewrite (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem))) (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem))
            as (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem))) (mixed_list_match vmatch io p cur_pm cur l_rem));
          Trade.trans
            (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)))
            (mixed_list_match vmatch io p cur_pm cur l_rem)
            (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
          if chunk_res {
            list_narrow_length l_rem (io.v chunk_len) (io.v new_rem);
            serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v new_rem) (list_narrow l_rem (io.v chunk_len) (io.v new_rem));
            p_node := new_node;
            p_remaining := new_rem;
          } else {
            p_node := new_node;
            p_remaining := new_rem;
            p_result := false;
          }
        }
        Slice sp_bi sv_bi ss_bi count_bi -> {
          let chunk_res = compute_remaining_size_base_slice vmatch io s cr cur_pm sp_bi sv_bi ss_bi count_bi chunk_len (list_narrow l_rem 0 (io.v chunk_len)) out;
          rewrite (base_mixed_list_match_n vmatch io p 0 (io.v chunk_len) cur_pm (Slice #i #t sp_bi sv_bi ss_bi count_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            as (base_mixed_list_match vmatch io p cur_pm (Slice #i #t sp_bi sv_bi ss_bi count_bi) (list_narrow l_rem 0 (io.v chunk_len)));
          elim_trade
            (base_mixed_list_match vmatch io p cur_pm (Slice #i #t sp_bi sv_bi ss_bi count_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem);
          let new_rem = io.sub cur_rem chunk_len;
          let new_node = mixed_list_narrow_n vmatch io p j 0 (io.v cur_rem) cur_pm cur l_rem chunk_len new_rem vmatch_share vmatch_gather;
          rewrite (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem)))
            as (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)));
          rewrite (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem))) (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem))
            as (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem))) (mixed_list_match vmatch io p cur_pm cur l_rem));
          Trade.trans
            (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)))
            (mixed_list_match vmatch io p cur_pm cur l_rem)
            (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
          if chunk_res {
            list_narrow_length l_rem (io.v chunk_len) (io.v new_rem);
            serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v new_rem) (list_narrow l_rem (io.v chunk_len) (io.v new_rem));
            p_node := new_node;
            p_remaining := new_rem;
          } else {
            p_node := new_node;
            p_remaining := new_rem;
            p_result := false;
          }
        }
        Singleton sp_bi sv_bi sr_bi -> {
          rewrite (base_mixed_list_match_n vmatch io p 0 (io.v chunk_len) cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            as (base_mixed_list_match_n vmatch io p 0 1 cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)));
          let chunk_res = compute_remaining_size_base_singleton vmatch io s cr cur_pm sp_bi sv_bi sr_bi (list_narrow l_rem 0 (io.v chunk_len)) out;
          rewrite (base_mixed_list_match_n vmatch io p 0 1 cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            as (base_mixed_list_match vmatch io p cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)));
          elim_trade
            (base_mixed_list_match vmatch io p cur_pm (Singleton #i #t sp_bi sv_bi sr_bi) (list_narrow l_rem 0 (io.v chunk_len)))
            (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem);
          let new_rem = io.sub cur_rem chunk_len;
          let new_node = mixed_list_narrow_n vmatch io p j 0 (io.v cur_rem) cur_pm cur l_rem chunk_len new_rem vmatch_share vmatch_gather;
          rewrite (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem)))
            as (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)));
          rewrite (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len - 0) (io.v new_rem))) (mixed_list_match_n vmatch io p 0 (io.v cur_rem) cur_pm cur l_rem))
            as (trade (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem))) (mixed_list_match vmatch io p cur_pm cur l_rem));
          Trade.trans
            (mixed_list_match vmatch io p (cur_pm /. 2.0R) new_node (list_narrow l_rem (io.v chunk_len) (io.v new_rem)))
            (mixed_list_match vmatch io p cur_pm cur l_rem)
            (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
          if chunk_res {
            list_narrow_length l_rem (io.v chunk_len) (io.v new_rem);
            serialize_nlist_append s (io.v chunk_len) (list_narrow l_rem 0 (io.v chunk_len)) (io.v new_rem) (list_narrow l_rem (io.v chunk_len) (io.v new_rem));
            p_node := new_node;
            p_remaining := new_rem;
          } else {
            p_node := new_node;
            p_remaining := new_rem;
            p_result := false;
          }
        }
        Empty -> {
          unreachable ()
        }
      }
    };
    with cur_pm l_rem . assert (mixed_list_match vmatch io p cur_pm _ l_rem);
    elim_trade
      (mixed_list_match vmatch io p cur_pm _ l_rem)
      (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l));
    rewrite (mixed_list_match_n vmatch io p 0 (io.v n) pm ml (Ghost.reveal l))
      as (mixed_list_match vmatch io p pm ml (Ghost.reveal l));
    fold (mixed_list_match_for_l2r vmatch io p pm (io.v n) ml l);
    !p_result
  }
}
```

#pop-options

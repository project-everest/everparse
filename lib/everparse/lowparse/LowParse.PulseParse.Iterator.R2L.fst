module LowParse.PulseParse.Iterator.R2L
#lang-pulse
include LowParse.Pulse.R2L
include LowParse.PulseParse.Iterator
open LowParse.PulseParse.Iterator.Type
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module IO = LowParse.PulseParse.Iterator.IntOps
module LPS = LowParse.Pulse.Base
module Trade = Pulse.Lib.Trade.Util

(* Right-to-left serialization of mixed lists.

   Mixed lists can only be traversed front-to-back (with the iterator of
   LowParse.PulseParse.Iterator), whereas an R2L writer must produce the last
   element first. Instead of a backwards traversal, we iterate forwards and
   maintain the invariant that the region written so far, `out[pos..p0)`,
   holds the *byte-reversal* of the encoding of the elements visited so far.
   Each element is R2L-written to the left of that region and then reversed in
   place; since `rev (a ++ b) == rev b ++ rev a`, the invariant is preserved.
   At the end, the whole region is reversed once more. This costs two extra
   passes over the output bytes, but needs no heap allocation, no recursion and
   no additional traversal of the mixed list structure. *)

(* Pure byte reversal *)

let seq_rev (#t: Type) (s: Seq.seq t) : Tot (Seq.seq t) =
  Seq.init (Seq.length s) (fun i -> Seq.index s (Seq.length s - 1 - i))

let seq_rev_append (#t: Type) (a b: Seq.seq t)
: Lemma (seq_rev (Seq.append a b) == Seq.append (seq_rev b) (seq_rev a))
= assert (Seq.equal (seq_rev (Seq.append a b)) (Seq.append (seq_rev b) (seq_rev a)))

let seq_rev_rev (#t: Type) (a: Seq.seq t)
: Lemma (seq_rev (seq_rev a) == a)
= assert (Seq.equal (seq_rev (seq_rev a)) a)

let reverse_range_post (v: bytes) (lo hi: nat) (v': bytes) : prop =
  lo <= hi /\ hi <= Seq.length v /\
  Seq.length v' == Seq.length v /\
  Seq.slice v' 0 lo == Seq.slice v 0 lo /\
  Seq.slice v' hi (Seq.length v) == Seq.slice v hi (Seq.length v) /\
  Seq.slice v' lo hi == seq_rev (Seq.slice v lo hi)

(* In-place reversal of out[lo..hi) *)

let reverse_range_inv (v: bytes) (lo hi: nat) (k: nat) (v': bytes) : prop =
  lo <= hi /\ hi <= Seq.length v /\ 2 * k <= hi - lo /\
  Seq.length v' == Seq.length v /\
  (forall (i: nat) . {:pattern (Seq.index v' i)} i < Seq.length v ==> Seq.index v' i == (
    if lo <= i && i < hi && (i < lo + k || i >= hi - k)
    then Seq.index v (lo + hi - 1 - i)
    else Seq.index v i
  ))

let reverse_range_inv_end (v: bytes) (lo hi: nat) (k: nat) (v': bytes)
: Lemma
  (requires reverse_range_inv v lo hi k v' /\ ~ (2 * (k + 1) <= hi - lo))
  (ensures reverse_range_post v lo hi v')
= assert (Seq.equal (Seq.slice v' 0 lo) (Seq.slice v 0 lo));
  assert (Seq.equal (Seq.slice v' hi (Seq.length v)) (Seq.slice v hi (Seq.length v)));
  assert (Seq.equal (Seq.slice v' lo hi) (seq_rev (Seq.slice v lo hi)))

let reverse_range_inv_step (v: bytes) (lo hi: nat) (k: nat) (v': bytes)
: Lemma
  (requires reverse_range_inv v lo hi k v' /\ 2 * (k + 1) <= hi - lo)
  (ensures (
    let a = Seq.index v' (lo + k) in
    let b = Seq.index v' (hi - 1 - k) in
    reverse_range_inv v lo hi (k + 1) (Seq.upd (Seq.upd v' (lo + k) b) (hi - 1 - k) a)
  ))
= ()

#push-options "--z3rlimit 32"

inline_for_extraction
fn r2l_reverse_range
  (out: S.slice byte)
  (lo hi: SZ.t)
  (#v: Ghost.erased bytes)
requires
  pts_to out v ** pure (SZ.v lo <= SZ.v hi /\ SZ.v hi <= Seq.length v)
ensures exists* v' .
  pts_to out v' ** pure (reverse_range_post v (SZ.v lo) (SZ.v hi) v')
{
  let mut pi = lo;
  let mut pj = hi;
  while (
    let i = !pi;
    let j = !pj;
    SZ.gt (SZ.sub j i) 1sz
  ) invariant exists* i j v' .
    pts_to pi i ** pts_to pj j ** pts_to out v' **
    pure (
      SZ.v lo <= SZ.v i /\ SZ.v j <= SZ.v hi /\
      SZ.v i - SZ.v lo == SZ.v hi - SZ.v j /\
      SZ.v i <= SZ.v j /\
      reverse_range_inv v (SZ.v lo) (SZ.v hi) (SZ.v i - SZ.v lo) v'
    )
  decreases (SZ.v (!pj) - SZ.v (!pi))
  {
    with v' . assert (pts_to out v');
    let i = !pi;
    let j = !pj;
    let j' = SZ.sub j 1sz;
    reverse_range_inv_step v (SZ.v lo) (SZ.v hi) (SZ.v i - SZ.v lo) v';
    let a = S.(out.(i));
    let b = S.(out.(j'));
    S.(out.(i) <- b);
    S.(out.(j') <- a);
    pi := SZ.add i 1sz;
    pj := j';
  };
  with i j v' . assert (pts_to pi i ** pts_to pj j ** pts_to out v');
  assert (pure (SZ.v j - SZ.v i <= 1));
  assert (pure (~ (2 * ((SZ.v i - SZ.v lo) + 1) <= SZ.v hi - SZ.v lo)));
  reverse_range_inv_end v (SZ.v lo) (SZ.v hi) (SZ.v i - SZ.v lo) v';
  assert (pure (reverse_range_post v (SZ.v lo) (SZ.v hi) v'));
}

#pop-options

(* Loop invariant lemmas *)

let rec enc_list_append (#t: Type) (enc: t -> GTot bytes) (l1 l2: list t)
: Lemma
  (ensures enc_list enc (List.Tot.append l1 l2) == Seq.append (enc_list enc l1) (enc_list enc l2))
  (decreases l1)
= match l1 with
  | [] -> assert (Seq.equal (Seq.append Seq.empty (enc_list enc l2)) (enc_list enc l2))
  | a :: q -> enc_list_append enc q l2; Seq.append_assoc (enc a) (enc_list enc q) (enc_list enc l2)

let enc_list_singleton (#t: Type) (enc: t -> GTot bytes) (a: t)
: Lemma (enc_list enc [a] == enc a)
= assert (Seq.equal (Seq.append (enc a) Seq.empty) (enc a))

let r2l_ml_inv
  (#t: Type) (enc: t -> GTot bytes) (l: list t)
  (p0: nat) (v0: bytes)
  (ld: list t) (ok: bool) (pc: nat) (vc: bytes)
: Tot prop
= Seq.length vc == Seq.length v0 /\
  p0 <= Seq.length v0 /\
  Seq.slice vc p0 (Seq.length v0) == Seq.slice v0 p0 (Seq.length v0) /\
  (ok == true ==> (
    pc + Seq.length (enc_list enc ld) == p0 /\
    Seq.slice vc pc p0 == seq_rev (enc_list enc ld)
  )) /\
  (ok == false ==> Seq.length (enc_list enc l) > p0)

let r2l_ml_inv_init (#t: Type) (enc: t -> GTot bytes) (l: list t) (p0: nat) (v0: bytes)
: Lemma
  (requires p0 <= Seq.length v0)
  (ensures r2l_ml_inv enc l p0 v0 [] true p0 v0)
= assert (Seq.equal (Seq.slice v0 p0 p0) (seq_rev (enc_list enc [])))

let r2l_ml_inv_fail
  (#t: Type) (enc: t -> GTot bytes) (l: list t)
  (p0: nat) (v0: bytes)
  (ld: list t) (y: t) (tl: list t) (pc: nat) (vc: bytes)
  (p2: nat) (v2: bytes)
: Lemma
  (requires
    r2l_ml_inv enc l p0 v0 ld true pc vc /\
    l == List.Tot.append ld (y :: tl) /\
    r2l_post (enc y) pc vc false p2 v2)
  (ensures r2l_ml_inv enc l p0 v0 (List.Tot.append ld [y]) false p2 v2)
= enc_list_append enc ld (y :: tl);
  Seq.slice_slice v2 pc (Seq.length v0) (p0 - pc) (Seq.length v0 - pc);
  Seq.slice_slice vc pc (Seq.length v0) (p0 - pc) (Seq.length v0 - pc)

let r2l_ml_inv_step
  (#t: Type) (enc: t -> GTot bytes) (l: list t)
  (p0: nat) (v0: bytes)
  (ld: list t) (y: t) (pc: nat) (vc: bytes)
  (p2: nat) (v2: bytes) (v3: bytes)
: Lemma
  (requires
    r2l_ml_inv enc l p0 v0 ld true pc vc /\
    r2l_post (enc y) pc vc true p2 v2 /\
    reverse_range_post v2 p2 pc v3)
  (ensures r2l_ml_inv enc l p0 v0 (List.Tot.append ld [y]) true p2 v3)
= let n = Seq.length v0 in
  enc_list_append enc ld [y];
  enc_list_singleton enc y;
  seq_rev_append (enc_list enc ld) (enc y);
  Seq.slice_slice v2 pc n (p0 - pc) (n - pc);
  Seq.slice_slice vc pc n (p0 - pc) (n - pc);
  Seq.slice_slice v2 pc n 0 (p0 - pc);
  Seq.slice_slice vc pc n 0 (p0 - pc);
  Seq.slice_slice v3 pc n 0 (n - pc);
  Seq.slice_slice v2 pc n 0 (n - pc);
  assert (Seq.equal (Seq.slice v3 p2 p0) (Seq.append (Seq.slice v3 p2 pc) (Seq.slice v3 pc p0)));
  assert (Seq.equal (Seq.slice v3 p0 n) (Seq.slice (Seq.slice v3 pc n) (p0 - pc) (n - pc)));
  assert (Seq.equal (Seq.slice v2 p0 n) (Seq.slice (Seq.slice v2 pc n) (p0 - pc) (n - pc)));
  assert (Seq.equal (Seq.slice v3 pc p0) (Seq.slice (Seq.slice v3 pc n) 0 (p0 - pc)));
  assert (Seq.equal (Seq.slice v2 pc p0) (Seq.slice (Seq.slice v2 pc n) 0 (p0 - pc)))

let r2l_ml_inv_end
  (#t: Type) (enc: t -> GTot bytes) (l: list t)
  (p0: nat) (v0: bytes)
  (pc: nat) (vc: bytes) (v3: bytes)
: Lemma
  (requires
    r2l_ml_inv enc l p0 v0 l true pc vc /\
    reverse_range_post vc pc p0 v3)
  (ensures r2l_post (enc_list enc l) p0 v0 true pc v3)
= seq_rev_rev (enc_list enc l)

let r2l_ml_inv_end_fail
  (#t: Type) (enc: t -> GTot bytes) (l: list t)
  (p0: nat) (v0: bytes)
  (ld: list t) (pc: nat) (vc: bytes)
: Lemma
  (requires r2l_ml_inv enc l p0 v0 ld false pc vc)
  (ensures r2l_post (enc_list enc l) p0 v0 false pc vc)
= ()

let pts_to_parsed_serialize
  (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p)
  (w: bytes) (y: t)
: Lemma
  (requires k.parser_kind_injective == true /\ pts_to_parsed_prop p w y)
  (ensures bare_serialize s y == w)
= serializer_correct_implies_complete p (bare_serialize s);
  assert (Seq.equal (Seq.slice w 0 (Seq.length w)) w)

(* `enc` agrees with the bytes of every serialized element *)
let enc_consumed (#k: parser_kind) (#u: Type) (p: parser k u) (enc: u -> GTot bytes) =
  (w: bytes) -> (y: u) -> Lemma (requires pts_to_parsed_prop p w y) (ensures enc y == w)

let append_assoc_singleton (#t: Type) (ld: list t) (y: t) (tl: list t)
: Lemma (List.Tot.append ld (y :: tl) == List.Tot.append (List.Tot.append ld [y]) tl)
= List.Tot.append_assoc ld [y] tl

(* Writing one element, either structured or already serialized *)

inline_for_extraction
fn r2l_write_elt_or_serialized_gen
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop) (#i: Type0) (io: IO.int_ops i)
  (#k: Ghost.erased parser_kind) (#p: parser k u) (enc: u -> GTot bytes)
  (enc_ok: enc_consumed p enc)
  (w: (pm: perm) -> r2l_writer_f (vmatch pm) enc)
  (pm: perm)
: r2l_writer_f #(elt_or_serialized t) #u (elt_or_serialized_match vmatch io p pm) enc
= (x': elt_or_serialized t)
  (#x: Ghost.erased u)
  (out: S.slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p0: Ghost.erased SZ.t)
{
  match x' {
    EElement e -> {
      rewrite (elt_or_serialized_match vmatch io p pm x' x) as (vmatch pm e x);
      let res = w pm e out pos;
      rewrite (vmatch pm e x) as (elt_or_serialized_match vmatch io p pm x' x);
      res
    }
    ESerialized pl -> {
      rewrite (elt_or_serialized_match vmatch io p pm x' x) as (pts_to_parsed p pl #pm x);
      unfold (pts_to_parsed p pl #pm x);
      with wb . assert (S.pts_to pl #pm wb);
      enc_ok wb x;
      fold (vmatch_bytes pm pl wb);
      let res = r2l_write_copy pm pl #wb out pos;
      unfold (vmatch_bytes pm pl wb);
      fold (pts_to_parsed p pl #pm x);
      rewrite (pts_to_parsed p pl #pm x) as (elt_or_serialized_match vmatch io p pm x' x);
      res
    }
  }
}

(* The mixed list writer *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"

inline_for_extraction
fn r2l_write_mixed_list_gen
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop) (#i: Type0) (io: IO.int_ops i)
  (#k: Ghost.erased parser_kind) (#p: parser k u) (enc: u -> GTot bytes)
  (enc_ok: enc_consumed p enc)
  (j: LPS.jumper p)
  (w: (pm: perm) -> r2l_writer_f (vmatch pm) enc)
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (pm: perm)
: r2l_writer_f #(mixed_list i t) #(list u) (mixed_list_match vmatch io p pm) (enc_list enc)
= (ml: mixed_list i t)
  (#l: Ghost.erased (list u))
  (out: S.slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased bytes)
  (#p0: Ghost.erased SZ.t)
{
  mixed_list_match_length vmatch io p pm ml l;
  let n0 = mixed_list_length io ml;
  let it0 = iterator_start vmatch io p j pm ml l vmatch_share vmatch_gather;
  with pm0 . assert (iterator_match vmatch io p pm0 it0 l);
  let mut pit = it0;
  let mut pn = n0;
  let mut pok = true;
  r2l_ml_inv_init enc l (SZ.v p0) v;
  let p0r = !pos;
  let mut pld : Ghost.erased (list u) = Ghost.hide [];
  while (
    let ok = !pok;
    let n = !pn;
    (ok && not (io.eq n io.zero))
  ) invariant exists* (it: iterator i t) (pmi: perm) (ld: Ghost.erased (list u)) (lr: list u) (n: i) (ok: bool) (vc: bytes) (pc: SZ.t) .
    R.pts_to pit it ** pts_to pld ld **
    iterator_match vmatch io p pmi it lr **
    trade (iterator_match vmatch io p pmi it lr) (mixed_list_match vmatch io p pm ml l) **
    pts_to pn n ** pts_to pok ok **
    pts_to out vc ** pts_to pos pc **
    pure (
      Ghost.reveal l == List.Tot.append (Ghost.reveal ld) lr /\
      io.v n == List.Tot.length lr /\
      r2l_ml_inv enc l (SZ.v p0) v (Ghost.reveal ld) ok (SZ.v pc) vc
    )
  decreases %[(if !pok then 1 else 0); io.v (!pn)]
  {
    with it pmi lr . assert (R.pts_to pit it ** iterator_match vmatch io p pmi it lr);
    with vc pc . assert (pts_to out vc ** pts_to pos pc);
    let ld = !pld;
    let n = !pn;
    let pcur = !pos;
    let x = iterator_next_eos vmatch io p j pmi pit it lr vmatch_share vmatch_gather;
    unfold (iterator_next_eos_post vmatch io p pmi pit it lr x);
    with pm_v y tl it' pm' . assert (
      elt_or_serialized_match vmatch io p pm_v x y **
      R.pts_to pit it' **
      iterator_match vmatch io p pm' it' tl);
    let res = r2l_write_elt_or_serialized_gen vmatch io enc enc_ok w pm_v x #y out pos;
    Trade.elim_hyp_l (elt_or_serialized_match vmatch io p pm_v x y) (iterator_match vmatch io p pm' it' tl) (iterator_match vmatch io p pmi it lr);
    Trade.trans (iterator_match vmatch io p pm' it' tl) (iterator_match vmatch io p pmi it lr) (mixed_list_match vmatch io p pm ml l);
    append_assoc_singleton #u (Ghost.reveal ld) y tl;
    pn := io.sub n io.one;
    pld := Ghost.hide (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]);
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    if (res) {
      let pnew = !pos;
      r2l_reverse_range out pnew pcur;
      with v3 . assert (pts_to out v3);
      assert (pure (r2l_ml_inv enc l (SZ.v p0) v (Ghost.reveal ld) true (SZ.v pc) vc));
      assert (pure (r2l_post (enc y) (SZ.v pc) vc true (SZ.v p2) v2));
      assert (pure (reverse_range_post v2 (SZ.v p2) (SZ.v pc) v3));
      r2l_ml_inv_step enc l (SZ.v p0) v (Ghost.reveal ld) y (SZ.v pc) vc (SZ.v p2) v2 v3;
      assert (pure (r2l_ml_inv enc l (SZ.v p0) v (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]) true (SZ.v p2) v3));
    } else {
      r2l_ml_inv_fail enc l (SZ.v p0) v (Ghost.reveal ld) y tl (SZ.v pc) vc (SZ.v p2) v2;
      pok := false;
    }
  };
  with it pmi lr . assert (R.pts_to pit it ** iterator_match vmatch io p pmi it lr);
  with vc pc . assert (pts_to out vc ** pts_to pos pc);
  let ld = !pld;
  Trade.elim (iterator_match vmatch io p pmi it lr) (mixed_list_match vmatch io p pm ml l);
  let ok = !pok;
  if (ok) {
    List.Tot.append_l_nil (Ghost.reveal ld);
    let pend = !pos;
    r2l_reverse_range out pend p0r;
    with v3 . assert (pts_to out v3);
    r2l_ml_inv_end enc l (SZ.v p0) v (SZ.v pc) vc v3;
    true
  } else {
    r2l_ml_inv_end_fail enc l (SZ.v p0) v (Ghost.reveal ld) (SZ.v pc) vc;
    false
  }
}

#pop-options

(* The special case of a serializer *)

inline_for_extraction
let r2l_write_mixed_list
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop) (#i: Type0) (io: IO.int_ops i)
  (#k: Ghost.erased parser_kind) (#p: parser k u) (s: serializer p)
  (sq: squash (k.parser_kind_injective == true))
  (j: LPS.jumper p)
  (w: (pm: perm) -> r2l_writer_f (vmatch pm) (bare_serialize s))
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (pm: perm)
: r2l_writer_f #(mixed_list i t) #(list u) (mixed_list_match vmatch io p pm) (enc_list (bare_serialize s))
= r2l_write_mixed_list_gen vmatch io (bare_serialize s) (fun wb y -> pts_to_parsed_serialize s wb y) j w vmatch_share vmatch_gather pm

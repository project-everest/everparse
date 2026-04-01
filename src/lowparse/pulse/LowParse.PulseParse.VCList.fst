module LowParse.PulseParse.VCList
#lang-pulse
include LowParse.Spec.VCList
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice.Util
open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base
open LowParse.Spec.Combinators

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module LPV = LowParse.Pulse.VCList
module U32 = FStar.UInt32

(* pts_to_parsed for nlist 1: convert between pts_to_parsed p and pts_to_parsed (parse_nlist 1 p) *)

ghost
fn pts_to_parsed_nlist_1_intro
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires PPB.pts_to_parsed p input #pm v
  ensures exists* v' .
    PPB.pts_to_parsed (parse_nlist 1 p) input #pm v' **
    trade (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v')
      (PPB.pts_to_parsed p input #pm v) **
    pure ((v' <: list t) == [v])
{
  unfold (PPB.pts_to_parsed p input #pm v);
  with w . assert (pts_to input #pm w);
  parse_nlist_eq 1 p w;
  parse_synth_eq p LPV.synth_nlist_1 w;
  let v' : Ghost.erased (nlist 1 t) = Ghost.hide [v];
  fold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v')
      (PPB.pts_to_parsed p input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v');
      with w' . assert (pts_to input #pm w');
      parse_nlist_eq 1 p w';
      parse_synth_eq p LPV.synth_nlist_1 w';
      fold (PPB.pts_to_parsed p input #pm v)
    };
}

ghost
fn pts_to_parsed_nlist_1_elim
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (#v: nlist 1 t)
  requires PPB.pts_to_parsed (parse_nlist 1 p) input #pm v
  ensures exists* v' .
    PPB.pts_to_parsed p input #pm v' **
    trade (PPB.pts_to_parsed p input #pm v')
      (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v) **
    pure (v == [v'])
{
  unfold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v);
  with w . assert (pts_to input #pm w);
  parse_nlist_eq 1 p w;
  parse_synth_eq p LPV.synth_nlist_1 w;
  let v' = Ghost.hide (List.Tot.hd v);
  fold (PPB.pts_to_parsed p input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed p input #pm v')
      (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed p input #pm v');
      with w' . assert (pts_to input #pm w');
      parse_nlist_eq 1 p w';
      parse_synth_eq p LPV.synth_nlist_1 w';
      fold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v)
    };
}

(* pts_to_parsed ext for nlist: convert between equivalent nlist parsers *)

let pts_to_parsed_nlist_ext_aux
  (#t: Type0)
  (#k1: parser_kind) (#p1: parser k1 t)
  (#k2: parser_kind) (#p2: parser k2 t)
  (n: nat)
  (prf: (b: bytes) -> Lemma (parse p1 b == parse p2 b))
  (b: bytes)
: Lemma (parse (parse_nlist n p1) b == parse (parse_nlist n p2) b)
= parse_nlist_ext n p1 p2 b (fun b' -> prf b')

ghost
fn pts_to_parsed_nlist_ext
  (#t: Type0)
  (#k1: parser_kind) (#p1: parser k1 t)
  (#k2: parser_kind) (#p2: parser k2 t)
  (n: nat)
  (prf: (b: bytes) -> Lemma (parse p1 b == parse p2 b))
  (input: slice byte)
  (#pm: perm)
  (#v: nlist n t)
  requires PPB.pts_to_parsed (parse_nlist n p1) input #pm v
  ensures PPB.pts_to_parsed (parse_nlist n p2) input #pm v
{
  Classical.forall_intro (pts_to_parsed_nlist_ext_aux #t #k1 #p1 #k2 #p2 n prf);
  PPB.pts_to_parsed_ext (parse_nlist n p2) input
}

(* nlist_hd_tl for pts_to_parsed: split a parsed nlist into head and tail sub-slices.
   Requires ParserStrong to split raw bytes at the correct boundary. *)

let nlist_hd_tl_post'
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (n: pos)
  (input: slice byte)
  (pm: perm)
  (v: (nlist n t))
  (hd tl: slice byte)
: slprop
= PPB.pts_to_parsed p hd #(pm /. 2.0R) (List.Tot.hd v) **
  PPB.pts_to_parsed (parse_nlist (n - 1) p) tl #(pm /. 2.0R) (List.Tot.tl v) **
  Trade.trade
    (PPB.pts_to_parsed p hd #(pm /. 2.0R) (List.Tot.hd v) **
      PPB.pts_to_parsed (parse_nlist (n - 1) p) tl #(pm /. 2.0R) (List.Tot.tl v))
    (PPB.pts_to_parsed (parse_nlist n p) input #pm v)

let nlist_hd_tl_post
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (n: pos)
  (input: slice byte)
  (pm: perm)
  (v: (nlist n t))
  (hd_tl: (slice byte & slice byte))
: slprop
= nlist_hd_tl_post' p sq n input pm v (fst hd_tl) (snd hd_tl)

inline_for_extraction
fn nlist_hd_tl
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  PPB.pts_to_parsed (parse_nlist n p) input #pm v
returns res : (slice byte & slice byte)
ensures
  nlist_hd_tl_post p sq n input pm v res
{
  PPB.pts_to_parsed_elim input;
  with w . assert (pts_to input #pm w);
  parse_nlist_eq (Ghost.reveal n) p w;
  parser_kind_prop_equiv k p;
  let off = j input 0sz;
  let input1, input2 = split_trade input off;
  with w1 . assert (pts_to input1 #pm w1);
  with w2 . assert (pts_to input2 #pm w2);
  parse_strong_prefix p w w1;
  let vh = Ghost.hide (List.Tot.hd (Ghost.reveal v));
  let vt : Ghost.erased (nlist (n - 1) t) = Ghost.hide (List.Tot.tl (Ghost.reveal v));
  PPB.pts_to_parsed_intro p input1 vh;
  PPB.pts_to_parsed_intro (parse_nlist (n - 1) p) input2 vt;
  // Trade chain: (parsed hd ** parsed tl) -> (pts_to input1 ** pts_to input2) -> (pts_to input) -> (parsed nlist)
  Trade.prod
    (PPB.pts_to_parsed p input1 #(pm /. 2.0R) vh)
    (pts_to input1 #pm w1)
    (PPB.pts_to_parsed (parse_nlist (n - 1) p) input2 #(pm /. 2.0R) vt)
    (pts_to input2 #pm w2);
  Trade.trans
    (PPB.pts_to_parsed p input1 #(pm /. 2.0R) vh ** PPB.pts_to_parsed (parse_nlist (n - 1) p) input2 #(pm /. 2.0R) vt)
    (pts_to input1 #pm w1 ** pts_to input2 #pm w2)
    (pts_to input #pm w);
  // Use existing trade from pts_to_parsed_elim: (pts_to input #pm w) -> (parsed nlist)
  Trade.trans
    (PPB.pts_to_parsed p input1 #(pm /. 2.0R) vh ** PPB.pts_to_parsed (parse_nlist (n - 1) p) input2 #(pm /. 2.0R) vt)
    (pts_to input #pm w)
    (PPB.pts_to_parsed (parse_nlist n p) input #pm v);
  rewrite each vh as (List.Tot.hd (Ghost.reveal v));
  rewrite each vt as (List.Tot.tl (Ghost.reveal v));
  fold (nlist_hd_tl_post' p sq n input pm v input1 input2);
  fold (nlist_hd_tl_post p sq n input pm v (input1, input2));
  (input1, input2)
}

(* nlist_hd: get head element sub-slice *)

inline_for_extraction
fn nlist_hd
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  PPB.pts_to_parsed (parse_nlist n p) input #pm v
returns input' : slice byte
ensures exists* v' .
  PPB.pts_to_parsed p input' #(pm /. 2.0R) v' **
  trade (PPB.pts_to_parsed p input' #(pm /. 2.0R) v') (PPB.pts_to_parsed (parse_nlist n p) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.hd v
  )
{
  let (hd, tl) = nlist_hd_tl sq j n input;
  unfold (nlist_hd_tl_post p sq n input pm v (hd, tl));
  unfold (nlist_hd_tl_post' p sq n input pm v hd tl);
  Trade.elim_hyp_r _ _ _;
  hd
}

(* nlist_tl: get tail sub-slice *)

inline_for_extraction
fn nlist_tl
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  PPB.pts_to_parsed (parse_nlist n p) input #pm v
returns input' : slice byte
ensures exists* v' .
  PPB.pts_to_parsed (parse_nlist (n - 1) p) input' #(pm /. 2.0R) v' **
  trade (PPB.pts_to_parsed (parse_nlist (n - 1) p) input' #(pm /. 2.0R) v') (PPB.pts_to_parsed (parse_nlist n p) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.tl v
  )
{
  let (hd, tl) = nlist_hd_tl sq j n input;
  unfold (nlist_hd_tl_post p sq n input pm v (hd, tl));
  unfold (nlist_hd_tl_post' p sq n input pm v hd tl);
  Trade.elim_hyp_l _ _ _;
  tl
}

(* Validator combinators *)

let parse_consume (#k: Ghost.erased parser_kind) (#t: Type) (p: parser k t) (b: bytes)
: GTot (option nat)
= match parse p b with
  | Some (_, consumed) -> Some consumed
  | None -> None

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_nlist
  (n: SZ.t)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
: LPS.validator #(nlist (SZ.v n) t) #(parse_nlist_kind (SZ.v n) k) (parse_nlist (SZ.v n) p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  pts_to_len input;
  let mut pcontinue = true;
  let mut pcount = n;
  while (
    let c = !pcontinue;
    let r = !pcount;
    (c && SZ.gt r 0sz)
  ) invariant exists* c r off .
    R.pts_to pcontinue c **
    R.pts_to pcount r **
    R.pts_to poffset off **
    pts_to input #pm v_bytes **
    pure (
      SZ.v off <= Seq.length v_bytes /\
      SZ.v r <= SZ.v n /\ (
      let s0 = Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes) in
      let s = Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes) in
      Some? (parse (parse_nlist (SZ.v n) p) s0) == (c && Some? (parse (parse_nlist (SZ.v r) p) s)) /\
      (Some? (parse (parse_nlist (SZ.v n) p) s0) ==>
        (SZ.v offset + snd (Some?.v (parse (parse_nlist (SZ.v n) p) s0)) ==
         SZ.v off + snd (Some?.v (parse (parse_nlist (SZ.v r) p) s))))
    ))
  {
    let off = !poffset;
    let r = !pcount;
    parse_nlist_eq (SZ.v r) p (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    let is_valid = v input poffset;
    if is_valid {
      pcount := SZ.sub r 1sz
    } else {
      pcontinue := false
    }
  };
  let c = !pcontinue;
  if c {
    let off = !poffset;
    parse_nlist_eq 0 p (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    true
  } else {
    false
  }
}

#pop-options

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_vclist
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (lv: LPS.validator lp)
  (lr: PPB.leaf_reader lp)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (w: LPS.validator p)
  (u: squash (lk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.validator #(vlarray t (U32.v min) (U32.v max)) #(parse_vclist_kind (U32.v min) (U32.v max) lk k) (parse_vclist (U32.v min) (U32.v max) lp p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_vclist_eq (U32.v min) (U32.v max) lp p sinput;
  let offset_val = !poffset;
  let is_valid_len = lv input poffset;
  if is_valid_len {
    let off = !poffset;
    let count = PPB.read_parsed_from_validator_success lr input offset_val off;
    if (U32.lt count min || U32.lt max count) {
      false
    } else {
      SZ.fits_u64_implies_fits_32 ();
      let n = SZ.uint32_to_sizet count;
      let consumed_n = Ghost.hide (SZ.v off - SZ.v offset);
      Seq.lemma_eq_elim
        (Seq.slice sinput consumed_n (Seq.length sinput))
        (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
      validate_nlist n w input poffset
    }
  } else {
    false
  }
}
#pop-options

#push-options "--z3rlimit 32"

inline_for_extraction
fn jump_vclist
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (lj: LPS.jumper lp)
  (lr: PPB.leaf_reader lp)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: LPS.jumper p)
  (u: squash (lk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.jumper #(vlarray t (U32.v min) (U32.v max)) #(parse_vclist_kind (U32.v min) (U32.v max) lk k) (parse_vclist (U32.v min) (U32.v max) lp p)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_vclist_eq (U32.v min) (U32.v max) lp p sinput;
  pts_to_len input;
  let off1 = lj input offset;
  let count = PPB.read_parsed_from_validator_success lr input offset off1;
  SZ.fits_u64_implies_fits_32 ();
  let n = SZ.uint32_to_sizet count;
  Seq.lemma_eq_elim
    (Seq.slice sinput (SZ.v off1 - SZ.v offset) (Seq.length sinput))
    (Seq.slice v_bytes (SZ.v off1) (Seq.length v_bytes));
  LPV.jump_nlist j n input off1
}

#pop-options

(* nlist_nth: access the i-th element of an nlist *)

ghost fn trade_trans_nounify
  (a1 a2 a2' a3: slprop)
requires
  trade a1 a2 ** trade a2' a3 ** pure (a2 == a2')
ensures
  trade a1 a3
{
  rewrite each a2' as a2;
  Trade.trans a1 a2 a3
}

let nlist_nth_inv
  (#t: Type0)
  (n0: Ghost.erased nat)
  (v0: list t)
  (i0: SZ.t)
  (i: SZ.t)
  (n: nat)
  (v: list t)
: Tot prop
= SZ.v i0 < n0 /\
  SZ.v i <= SZ.v i0 /\
  n == n0 - SZ.v i /\
  List.Tot.length v0 == Ghost.reveal n0 /\
  List.Tot.length v == n /\
  List.Tot.index v0 (SZ.v i0) == List.Tot.index v (SZ.v i0 - SZ.v i)

inline_for_extraction
fn nlist_nth
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n0: Ghost.erased nat)
  (input: slice byte)
  (#pm: perm)
  (#v0: Ghost.erased (nlist n0 t))
  (i0: SZ.t { SZ.v i0 < n0 })
requires
  PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0
returns input' : slice byte
ensures exists* v' pm' .
  PPB.pts_to_parsed p input' #pm' v' **
  trade (PPB.pts_to_parsed p input' #pm' v') (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0) **
  pure (v' == List.Tot.index v0 (SZ.v i0))
{
  Trade.refl (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0);
  let mut pi = 0sz;
  let mut pres = input;
  while (
    let i = !pi;
    (SZ.lt i i0)
  ) invariant exists* i res (n: nat) (v: nlist n t) pm' . (
    R.pts_to pi i ** R.pts_to pres res **
    PPB.pts_to_parsed (parse_nlist n p) res #pm' v **
    trade (PPB.pts_to_parsed (parse_nlist n p) res #pm' v) (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0) **
    pure (
      nlist_nth_inv #t n0 v0 i0 i n v
    )
  ) {
    with 'res. assert R.pts_to pres 'res;
    let res = !pres;
    rewrite each 'res as res;
    let i = !pi;
    with v pm' . assert (PPB.pts_to_parsed (parse_nlist (n0 - SZ.v i) p) res #pm' v);
    let res2 = nlist_tl sq j (n0 - SZ.v i) res;
    pi := (SZ.add i 1sz);
    pres := res2;
    with v' pm'' . assert (PPB.pts_to_parsed (parse_nlist (n0 - SZ.v i - 1) p) res2 #pm'' v');
    trade_trans_nounify _ _ _
      (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0);
  };
  with 'res. assert R.pts_to pres 'res;
  let res = !pres;
  rewrite each 'res as res;
  let i = !pi;
  with v pm' . assert (PPB.pts_to_parsed (parse_nlist (n0 - SZ.v i) p) res #pm' v);
  let res2 = nlist_hd sq j (n0 - SZ.v i0) res;
  trade_trans_nounify
    _ _ _ (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0);
  res2
}

(* accessor_nlist_nth: accessor for the i-th element of an nlist *)

include LowParse.CLens

let clens_nlist_nth (#t: Type) (n: nat) (i: nat { i < n })
: Tot (clens (nlist n t) t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (v: nlist n t) -> List.Tot.index v i);
}

inline_for_extraction
fn accessor_nlist_nth
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n0: Ghost.erased nat)
  (i0: SZ.t { SZ.v i0 < n0 })
: PPB.accessor (parse_nlist n0 p) p (clens_nlist_nth n0 (SZ.v i0))
=
  (input: S.slice byte)
  (#pm: perm)
  (#v0: Ghost.erased (nlist n0 t))
{
  let res = nlist_nth sq j n0 input i0;
  with v' pm' . assert (PPB.pts_to_parsed p res #pm' v');
  res
}

(* accessor_vclist_payload: accessor from vclist to nlist *)

module L = FStar.List.Tot
module LPC = LowParse.Pulse.Combinators

let clens_vclist_payload
  (min: nat)
  (max: nat { min <= max })
  (#t: Type)
  (n: Ghost.erased nat)
: Tot (clens (vlarray t min max) (nlist (Ghost.reveal n) t))
= {
  clens_cond = (fun (l: vlarray t min max) -> L.length l == Ghost.reveal n);
  clens_get = (fun (l: vlarray t min max) ->
    (l <: Ghost (nlist (Ghost.reveal n) t) (requires (L.length l == Ghost.reveal n)) (ensures fun _ -> True)));
}

let synth_vclist_dtuple2_injective
  (min: nat)
  (max: nat { min <= max })
  (#t: Type)
: Lemma (synth_injective (parse_vclist_dtuple2_synth min max #t))
= ()

let synth_vclist_dtuple2_recip
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#t: Type)
  (x: vlarray t min max)
: GTot (dtuple2 (bounded_count min max) (fun (n: bounded_count min max) -> nlist (U32.v n) t))
= (| U32.uint_to_t (L.length x), x |)

let synth_vclist_dtuple2_inverse
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#t: Type)
: Lemma (synth_inverse (parse_vclist_dtuple2_synth min max #t) (synth_vclist_dtuple2_recip min max #t))
= ()

inline_for_extraction
let mk_jump_vclist_tag
  (min: Ghost.erased nat)
  (max: Ghost.erased nat { min <= max })
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (lj: LPS.jumper lp)
: LPS.jumper (parse_vclist_dtuple2_tag_parser min max lp)
= LPC.jump_synth (LPC.jump_filter lj (bounded_count_prop min max)) (synth_bounded_count min max)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

inline_for_extraction
fn accessor_vclist_payload
  (min: Ghost.erased nat)
  (max: Ghost.erased nat { min <= max /\ max < 4294967296 })
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (lj: LPS.jumper lp)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (n: Ghost.erased nat)
  (sq: squash (lk.parser_kind_subkind == Some ParserStrong /\
    LPS.pts_to_serialized_ext_trade_gen_precond
      (parse_vclist min max lp p)
      (parse_synth
        (parse_dtuple2
          (parse_vclist_dtuple2_tag_parser min max lp)
          (parse_vclist_dtuple2_payload_parser min max p))
        (parse_vclist_dtuple2_synth min max #t))))
: PPB.accessor
    (parse_vclist min max lp p)
    (parse_nlist (Ghost.reveal n) p)
    (clens_vclist_payload min max n)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (vlarray t min max))
{
  (* Step 1: ghost reinterpret as parse_synth parse_dtuple2 synth *)
  PPB.pts_to_parsed_ext_trade_gen
    (parse_synth
      (parse_dtuple2
        (parse_vclist_dtuple2_tag_parser min max lp)
        (parse_vclist_dtuple2_payload_parser min max p))
      (parse_vclist_dtuple2_synth min max #t))
    input;
  with v1 . assert (PPB.pts_to_parsed
    (parse_synth
      (parse_dtuple2
        (parse_vclist_dtuple2_tag_parser min max lp)
        (parse_vclist_dtuple2_payload_parser min max p))
      (parse_vclist_dtuple2_synth min max #t))
    input #pm v1);

  (* Step 2: ghost unwrap synth *)
  synth_vclist_dtuple2_injective min max #t;
  synth_vclist_dtuple2_inverse min max #t;
  PPC.pts_to_parsed_synth_l2r_trade
    (parse_dtuple2
      (parse_vclist_dtuple2_tag_parser min max lp)
      (parse_vclist_dtuple2_payload_parser min max p))
    (parse_vclist_dtuple2_synth min max #t)
    (synth_vclist_dtuple2_recip min max #t)
    input;
  with v2 . assert (PPB.pts_to_parsed
    (parse_dtuple2
      (parse_vclist_dtuple2_tag_parser min max lp)
      (parse_vclist_dtuple2_payload_parser min max p))
    input #pm v2);
  Trade.trans _ _ (PPB.pts_to_parsed (parse_vclist min max lp p) input #pm v);

  (* Step 3: accessor_dtuple2_snd — jump past the tag *)
  let gbc : Ghost.erased (bounded_count min max) = Ghost.hide (dfst v2);
  let s3 = PPC.accessor_dtuple2_snd
    (mk_jump_vclist_tag min max lj)
    (parse_vclist_dtuple2_payload_parser min max p)
    gbc
    ()
    input;
  Trade.trans _ _ (PPB.pts_to_parsed (parse_vclist min max lp p) input #pm v);

  (* Step 4: ghost reinterpret weakened nlist as parse_nlist *)
  with v3 pm3 . assert (PPB.pts_to_parsed
    (parse_vclist_dtuple2_payload_parser min max p (Ghost.reveal gbc))
    s3 #pm3 v3);
  PPB.pts_to_parsed_ext_trade_gen (parse_nlist n p) s3;
  with v4 . assert (PPB.pts_to_parsed (parse_nlist n p) s3 #pm3 v4);
  Trade.trans
    (PPB.pts_to_parsed (parse_nlist n p) s3 #pm3 v4)
    (PPB.pts_to_parsed (parse_vclist_dtuple2_payload_parser min max p (Ghost.reveal gbc)) s3 #pm3 v3)
    (PPB.pts_to_parsed (parse_vclist min max lp p) input #pm v);
  s3
}

#pop-options

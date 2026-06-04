module LowParse.PulseParse.Base
#lang-pulse
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base
module LPS = LowParse.Pulse.Base

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice

let pts_to_parsed_prop
  (#k: parser_kind) (#t: Type) (p: parser k t)
  (w: Seq.seq byte)
  (v: t)
: Tot prop
= match parse p w with
  | None -> False
  | Some (v', consumed) -> v' == v /\
    consumed == Seq.length w

let pts_to_parsed
  (#k: parser_kind) (#t: Type) (p: parser k t)
  ([@@@mkey]input: slice byte)
  (#[exact (`1.0R)] pm: perm)
  (v: t)
: slprop =
  exists* w . S.pts_to input #pm w **
  pure (pts_to_parsed_prop p w v)

ghost fn pts_to_parsed_intro
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  ([@@@mkey]input: slice byte)
  (#pm: perm)
  (#w: Seq.seq byte)
  (v: t)
requires
  S.pts_to input #pm w **
  pure (pts_to_parsed_prop p w v)
ensures
  pts_to_parsed p input #(pm /. 2.0R) v **
  Trade.trade
    (pts_to_parsed p input #(pm /. 2.0R) v)
    (S.pts_to input #pm w)
{
  S.share input;
  fold (pts_to_parsed p input #(pm /. 2.0R) v);
  intro
    (Trade.trade
      (pts_to_parsed p input #(pm /. 2.0R) v)
      (S.pts_to input #pm w)
    )
    #((S.pts_to input #(pm /. 2.0R) w))
    fn _ {
      unfold (pts_to_parsed p input #(pm /. 2.0R) v);
      S.gather input
    };
}

ghost fn pts_to_parsed_intro_injective
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (#w: Seq.seq byte)
  (v: t)
requires
  S.pts_to input #pm w **
  pure (pts_to_parsed_prop p w v /\
    k.parser_kind_injective == true
  )
ensures
  pts_to_parsed p input #(pm) v **
  Trade.trade
    (pts_to_parsed p input #(pm) v)
    (S.pts_to input #pm w)
{
  fold (pts_to_parsed p input #(pm) v);
  intro
    (Trade.trade
      (pts_to_parsed p input #(pm) v)
      (S.pts_to input #pm w)
    )
    #emp
    fn _ {
      unfold (pts_to_parsed p input #(pm) v);
      with w' . assert (S.pts_to input #pm w');
      parse_injective p w w';
      assert pure (Seq.equal w w')
    };
}

ghost fn pts_to_parsed_elim
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (#pm: perm)
  (#v: t)
  (input: slice byte)
requires
  pts_to_parsed p input #(pm) v
ensures exists* w .
  S.pts_to input #pm w **
  Trade.trade
    (S.pts_to input #pm w)
    (pts_to_parsed p input #(pm) v) **
  pure (pts_to_parsed_prop p w v)
{
  unfold (pts_to_parsed p input #(pm) v);
  with w . assert (S.pts_to input #pm w);
  intro
    (Trade.trade
      (S.pts_to input #pm w)
      (pts_to_parsed p input #(pm) v)
    )
    #emp
    fn _ {
      fold (pts_to_parsed p input #(pm) v);
    };
}

ghost fn pts_to_parsed_ext
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_parsed p1 input #pm v ** pure (
    forall x . parse p1 x == parse p2 x
  )
  ensures pts_to_parsed p2 input #pm v
{
  unfold (pts_to_parsed p1 input #pm v);
  fold (pts_to_parsed p2 input #pm v)
}

ghost fn pts_to_parsed_ext_trade
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_parsed p1 input #pm v ** pure (
    forall x . parse p1 x == parse p2 x
  )
  ensures pts_to_parsed p2 input #pm v **
    Trade.trade
      (pts_to_parsed p2 input #pm v)
      (pts_to_parsed p1 input #pm v)
{
    pts_to_parsed_ext p2 input;
    intro
      (Trade.trade
        (pts_to_parsed p2 input #pm v)
        (pts_to_parsed p1 input #pm v)
      )
      #emp
      fn _ {
        pts_to_parsed_ext p1 input
      }
}

ghost fn pts_to_parsed_ext_gen
  (#t1: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (#t2:Type0)
  (#k2: parser_kind)
  (p2: parser k2 t2)
  (input: slice byte)
  (#pm: perm)
  (#v1: t1)
  requires pts_to_parsed p1 input #pm v1 ** pure (
    LPS.pts_to_serialized_ext_trade_gen_precond p1 p2
  )
  ensures exists* (v2: t2) . pts_to_parsed p2 input #pm v2 ** pure (
    LPS.pts_to_serialized_ext_trade_gen_post t1 t2 v1 v2
  )
{
  unfold (pts_to_parsed p1 input #pm v1);
  fold (pts_to_parsed p2 input #pm v1)
}

ghost fn pts_to_parsed_ext_trade_gen
  (#t1: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (#t2:Type0)
  (#k2: parser_kind)
  (p2: parser k2 t2)
  (input: slice byte)
  (#pm: perm)
  (#v1: t1)
  requires pts_to_parsed p1 input #pm v1 ** pure (
    LPS.pts_to_serialized_ext_trade_gen_precond p1 p2
  )
  ensures exists* (v2: t2) . pts_to_parsed p2 input #pm v2 **
    Trade.trade
      (pts_to_parsed p2 input #pm v2)
      (pts_to_parsed p1 input #pm v1) **
    pure (
      LPS.pts_to_serialized_ext_trade_gen_post t1 t2 v1 v2
    )
{
  pts_to_parsed_ext_gen p2 input;
  with v2 . assert (pts_to_parsed p2 input #pm v2);
  intro
    (Trade.trade
      (pts_to_parsed p2 input #pm v2)
      (pts_to_parsed p1 input #pm v1)
    )
    #emp
    fn _ {
      pts_to_parsed_ext_gen p1 input;
      with v1' . rewrite (pts_to_parsed p1 input #pm v1')
        as (pts_to_parsed p1 input #pm v1)
    }
}

ghost fn pts_to_serialized_parsed
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (#s: serializer p)
  (#v: t)
  (#pm: perm)
  (input: S.slice byte)
requires
  LPS.pts_to_serialized s input #pm v
ensures
  pts_to_parsed p input #pm v **
  Trade.trade
    (pts_to_parsed p input #pm v)
    (LPS.pts_to_serialized s input #pm v)
{
  LPS.pts_to_serialized_elim_trade s input;
  pts_to_parsed_intro_injective p input v;
  Trade.trans (pts_to_parsed p input #pm v) _ _
}

ghost fn pts_to_parsed_serialized
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (s: serializer p)
  (#v: t)
  (#pm: perm)
  (input: S.slice byte)
requires
  pts_to_parsed p input #pm v
ensures
  LPS.pts_to_serialized s input #pm v **
  Trade.trade
    (LPS.pts_to_serialized s input #pm v)
    (pts_to_parsed p input #pm v)
{
  pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_injective p w (serialize s v);
  LPS.pts_to_serialized_intro_trade s input v;
  Trade.trans (LPS.pts_to_serialized s input #pm v) _ _
}

let pts_to_parsed_strong_prefix_prop
  (#k: parser_kind) (#t: Type) (p: parser k t)
  (w: Seq.seq byte)
  (v: t)
: Tot prop
= k.parser_kind_subkind == Some ParserStrong /\
  begin match parse p w with
  | None -> False
  | Some (v', consumed) -> v' == v
  end

let pts_to_parsed_strong_prefix
  (#k: parser_kind) (#t: Type) (p: parser k t)
  ([@@@mkey]input: slice byte)
  (#[exact (`1.0R)] pm: perm)
  (v: t)
: slprop =
  exists* v' .
  S.pts_to input #pm v' **
  pure (
    pts_to_parsed_strong_prefix_prop p v' v
  )

ghost fn pts_to_parsed_strong_prefix_intro
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (v: t)
  (#v': bytes)
requires
  S.pts_to input #pm v' **
  pure (
    pts_to_parsed_strong_prefix_prop p v' v
  )
ensures
  pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v **
  Trade.trade
    (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v)
    (S.pts_to input #pm v')
{
  S.share input;
  fold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
  intro
    (Trade.trade
      (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v)
      (S.pts_to input #pm v')
    )
    #(S.pts_to input #(pm /. 2.0R) v')
    fn _ {
      unfold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
      S.gather input
    };
}

module R = Pulse.Lib.Reference

inline_for_extraction
let leaf_reader
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
= (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  stt t (pts_to_parsed p input #pm v) (fun res ->
    pts_to_parsed p input #pm v **
    pure (res == Ghost.reveal v)
  )

inline_for_extraction
let reader
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
= (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  (t': Type0) ->
  (f: ((x: t { x == Ghost.reveal v }) -> Tot t')) ->
  stt t' (pts_to_parsed p input #pm v) (fun x' -> pts_to_parsed p input #pm v ** pure (x' == f v))

inline_for_extraction
fn leaf_reader_of_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: reader p)
: leaf_reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  r input #pm #v t id
}

inline_for_extraction
fn reader_of_leaf_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: leaf_reader p)
: reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  let x = r input #pm #v;
  f x
}

inline_for_extraction
fn leaf_reader_of_serialized
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: LPS.leaf_reader s)
: leaf_reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  pts_to_parsed_serialized s input;
  let res = r input;
  pts_to_serialized_parsed input;
  Trade.trans (pts_to_parsed p input #pm v) (LPS.pts_to_serialized s input #pm v) (pts_to_parsed p input #pm v);
  Trade.elim (pts_to_parsed p input #pm v) (pts_to_parsed p input #pm v);
  res
}

inline_for_extraction
fn serialized_of_leaf_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (r: leaf_reader p)
: LPS.leaf_reader #t #k #p s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  pts_to_serialized_parsed input;
  let res = r input;
  pts_to_parsed_serialized s input;
  Trade.trans (LPS.pts_to_serialized s input #pm v) (pts_to_parsed p input #pm v) (LPS.pts_to_serialized s input #pm v);
  Trade.elim (LPS.pts_to_serialized s input #pm v) (LPS.pts_to_serialized s input #pm v);
  res
}

inline_for_extraction
fn reader_of_serialized
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: LPS.reader s)
: reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  pts_to_parsed_serialized s input;
  let res = r input #pm #v t' f;
  pts_to_serialized_parsed input;
  Trade.trans (pts_to_parsed p input #pm v) (LPS.pts_to_serialized s input #pm v) (pts_to_parsed p input #pm v);
  Trade.elim (pts_to_parsed p input #pm v) (pts_to_parsed p input #pm v);
  res
}

inline_for_extraction
fn read_parsed_from_validator_success
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t {k.parser_kind_subkind == Some ParserStrong})
  (r: leaf_reader p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (offset: SZ.t)
  (off: SZ.t)
  requires (pts_to input #pm v ** pure (LPS.validator_success #k #t p offset v (off)))
  returns v' : t
  ensures pts_to input #pm v ** pure (
    LPS.validator_success #k #t p offset v off /\
    parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (v', SZ.v off - SZ.v offset)
  )
{
  parser_kind_prop_equiv k p;
  let input1, input23 = split_trade input offset;
  with v23 . assert (pts_to input23 #pm v23);
  Trade.elim_hyp_l (pts_to input1 #pm _) (pts_to input23 #pm v23) _;
  let consumed = SZ.sub off offset;
  let input2, input3 = split_trade input23 consumed;
  with v2 . assert (pts_to input2 #pm v2);
  Trade.elim_hyp_r (pts_to input2 #pm v2) (pts_to input3 #pm _) (pts_to input23 #pm v23);
  Trade.trans (pts_to input2 #pm v2) (pts_to input23 #pm _) (pts_to input #pm _);
  let gv1 = Ghost.hide (fst (Some?.v (parse p v23)));
  parse_strong_prefix p v23 v2;
  pts_to_parsed_intro p input2 gv1;
  let res = r input2;
  Trade.elim (pts_to_parsed p input2 #(pm /. 2.0R) gv1) (pts_to input2 #pm v2);
  Trade.elim (pts_to input2 #pm v2) (pts_to input #pm v);
  res
}

inline_for_extraction
fn ifthenelse_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (cond: bool)
  (iftrue: squash (cond == true) -> reader p)
  (iffalse: squash (cond == false) -> reader p)
: reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  if cond {
    iftrue () input #pm #v t' f
  } else {
    iffalse () input #pm #v t' f
  }
}

inline_for_extraction
fn reader_ext
  (#t: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (r1: reader p1)
  (#k2: Ghost.erased parser_kind)
  (p2: parser k2 t { forall x . parse p1 x == parse p2 x })
: reader #t #k2 p2
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  pts_to_parsed_ext_trade p1 input;
  let res = r1 input #pm #v t' f;
  Trade.elim _ _;
  res
}

inline_for_extraction
fn peek_trade_gen
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t {k.parser_kind_subkind == Some ParserStrong})
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (offset: SZ.t)
  (off: SZ.t)
  requires (pts_to input #pm v ** pure (LPS.validator_success #k #t p offset v off))
  returns input': slice byte
  ensures exists* v' . pts_to_parsed p input' #(pm /. 2.0R) v' ** Trade.trade (pts_to_parsed p input' #(pm /. 2.0R) v') (pts_to input #pm v) ** pure (
    LPS.validator_success #k #t p offset v off /\
    parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (v', SZ.v off - SZ.v offset)
  )
{
  parser_kind_prop_equiv k p;
  let input1, input23 = split_trade input offset;
  with v23 . assert (pts_to input23 #pm v23);
  Trade.elim_hyp_l (pts_to input1 #pm _) (pts_to input23 #pm v23) _;
  let consumed = SZ.sub off offset;
  let input2, input3 = split_trade input23 consumed;
  with v2 . assert (pts_to input2 #pm v2);
  Trade.elim_hyp_r (pts_to input2 #pm v2) (pts_to input3 #pm _) (pts_to input23 #pm v23);
  Trade.trans (pts_to input2 #pm v2) (pts_to input23 #pm _) (pts_to input #pm _);
  let gv1 = Ghost.hide (fst (Some?.v (parse p v23)));
  parse_strong_prefix p v23 v2;
  pts_to_parsed_intro p input2 gv1;
  Trade.trans (pts_to_parsed p input2 #(pm /. 2.0R) gv1) (pts_to input2 #pm v2) (pts_to input #pm v);
  input2
}

(* zero_copy_parse: PulseParse version using pts_to_parsed instead of pts_to_serialized *)

let pts_to_parsed_with_perm
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (input: LPS.with_perm (S.slice byte))
  (v: t)
: Tot slprop
= pts_to_parsed p input.v #input.p v

inline_for_extraction
let zero_copy_parse
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (p: parser k t)
=
  (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  stt t'
    (pts_to_parsed p input #pm v)
    (fun res ->
      vmatch res v **
      Trade.trade
        (vmatch res v)
        (pts_to_parsed p input #pm v)
    )

inline_for_extraction
fn zero_copy_parse_id
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
: zero_copy_parse #_ #_ (pts_to_parsed_with_perm p) #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let res = { LPS.v = input; LPS.p = pm };
  Trade.rewrite_with_trade
    (pts_to_parsed p input #pm v)
    (pts_to_parsed_with_perm p res v);
  res
}

inline_for_extraction
fn zero_copy_parse_lens
  (#t1'  #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: zero_copy_parse vmatch1 p)
  (#t2': Type0)
  (#vmatch2: t2' -> t -> slprop)
  (lens: LPS.vmatch_lens vmatch1 vmatch2)
: zero_copy_parse #_ #_ vmatch2 #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let tmp = r input;
  let res = lens tmp _;
  Trade.trans (vmatch2 res _) _ _;
  res
}

inline_for_extraction
fn zero_copy_parse_read
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: leaf_reader p)
: zero_copy_parse #_ #_ (LPS.eq_as_slprop t) #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let res = r input;
  fold (LPS.eq_as_slprop t res v);
  intro (Trade.trade (LPS.eq_as_slprop t res v) (pts_to_parsed p input #pm v)) #(pts_to_parsed p input #pm v) fn _{
    unfold (LPS.eq_as_slprop t res v)
  };
  res
}

inline_for_extraction
fn zero_copy_parse_ignore
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
: zero_copy_parse #_ #_ (LPS.vmatch_ignore #t) #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  fold (LPS.vmatch_ignore () (Ghost.reveal v));
  intro (Trade.trade (LPS.vmatch_ignore () (Ghost.reveal v)) (pts_to_parsed p input #pm v)) #(pts_to_parsed p input #pm v) fn _{
    unfold (LPS.vmatch_ignore () (Ghost.reveal v))
  };
  ()
}

inline_for_extraction
fn zero_copy_parse_ext
  (#t1'  #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: zero_copy_parse vmatch1 p)
  (#k': Ghost.erased parser_kind)
  (p': parser k' t {
    forall b . parse p b == parse p' b
  })
: zero_copy_parse #_ #_ vmatch1 #_ p'
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  pts_to_parsed_ext_trade p input;
  let res = r input;
  Trade.trans (vmatch1 res v) _ _;
  res
}

inline_for_extraction
fn zero_copy_parse_ifthenelse
  (#t1'  #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (cond: bool)
  (rtrue: squash (cond == true) -> zero_copy_parse vmatch1 p)
  (rfalse: squash (cond == false) -> zero_copy_parse vmatch1 p)
: zero_copy_parse #_ #_ vmatch1 #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  if (cond) {
    rtrue () input
  } else {
    rfalse () input
  }
}

include LowParse.CLens

let accessor_postcond
  (#t1: Type0)
  (#t2: Type0)
  (cl: clens t1 t2)
  (v: t1)
  (v2: t2)
: Tot prop
= cl.clens_cond v /\ v2 == cl.clens_get v

inline_for_extraction
let accessor
  (#k1: parser_kind) (#t1: Type0) (p1: parser k1 t1)
  (#k2: parser_kind) (#t2: Type0) (p2: parser k2 t2)
  (cl: clens t1 t2)
: Tot Type
= (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t1) ->
  stt (slice byte)
    (pts_to_parsed p1 input #pm v ** pure (cl.clens_cond v))
    (fun result -> exists* v2 pm' .
      pts_to_parsed p2 result #pm' v2 **
      pure (accessor_postcond cl v v2) **
      Trade.trade
        (pts_to_parsed p2 result #pm' v2)
        (pts_to_parsed p1 input #pm v))

(* accessor_parser_ext: accessor between two parsers of different kinds
   but same value type and same parse behavior *)

let clens_parser_ext
  (#t1 #t2: Type)
  (sq: squash (t1 == t2))
: Tot (clens t1 t2)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (x: t1) -> (x <: t2));
}

inline_for_extraction
fn accessor_parser_ext
  (#k1: parser_kind) (#t1: Type0) (p1: parser k1 t1)
  (#k2: parser_kind) (#t2: Type0) (p2: parser k2 t2)
  (sq: squash (LPS.pts_to_serialized_ext_trade_gen_precond p1 p2))
: accessor p1 p2 (clens_parser_ext ())
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t1)
{
  pts_to_parsed_ext_trade_gen p2 input;
  with v2 . assert (pts_to_parsed p2 input #pm v2);
  input
}

(* Packed high-level separation logic predicate: the low-level representation
   [x] relates to the high-level value [v] when there EXISTS a refinement-free
   "mid" value [vm] such that [x] relates to [vm] via [vmatch] and [vm] converts
   to [v] via the partial conversion [conv]. All refinements on the high-level
   value type [t] are captured by [conv] (a partial function), so the [vmatch]
   right-hand-side type [tm] is free of refinements. *)
let vmatch_conv
  (#t' #tm #t: Type0)
  (vmatch: t' -> tm -> slprop)
  (conv: tm -> GTot (option t))
  (x: t')
  (v: t)
: slprop
= exists* (vm: tm) . vmatch x vm ** pure (conv vm == Some v)

ghost
fn intro_vmatch_conv
  (#t' #tm #t: Type0)
  (vmatch: t' -> tm -> slprop)
  (conv: tm -> GTot (option t))
  (x: t')
  (vm: tm)
  (v: t)
  requires vmatch x vm ** pure (conv vm == Some v)
  ensures vmatch_conv vmatch conv x v
{
  fold (vmatch_conv vmatch conv x v);
}

ghost
fn elim_vmatch_conv
  (#t' #tm #t: Type0)
  (vmatch: t' -> tm -> slprop)
  (conv: tm -> GTot (option t))
  (x: t')
  (v: t)
  requires vmatch_conv vmatch conv x v
  ensures exists* (vm: tm) . vmatch x vm ** pure (conv vm == Some v)
{
  unfold (vmatch_conv vmatch conv x v);
}

inline_for_extraction
let copyful_parse
  (#t' #tm #t: Type0)
  (vmatch: t' -> tm -> slprop)
  (#k: parser_kind)
  (p: parser k t)
  (conv: tm -> GTot (option t))
=
  (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  stt t'
    (pts_to_parsed p input #pm v)
    (fun res ->
      pts_to_parsed p input #pm v **
      vmatch_conv vmatch conv res v
    )

inline_for_extraction
let free_t
  (#t' #tm: Type0)
  (vmatch: t' -> tm -> slprop)
=
  (x: t') ->
  (#v: Ghost.erased tm) ->
  stt unit
    (vmatch x v)
    (fun _ -> emp)

(* Lift a [free_t] over a mid [vmatch] to a [free_t] over the packed high-level
   predicate [vmatch_conv vmatch conv]: eliminate the existential mid witness,
   then free using the underlying destructor. *)
inline_for_extraction
fn free_vmatch_conv
  (#t' #tm #t: Type0)
  (vmatch: t' -> tm -> slprop)
  (conv: tm -> GTot (option t))
  (free: free_t vmatch)
: free_t #t' #t (vmatch_conv vmatch conv)
=
  (x: t')
  (#v: Ghost.erased t)
{
  elim_vmatch_conv vmatch conv x v;
  with vm . assert (vmatch x vm ** pure (conv vm == Some (Ghost.reveal v)));
  free x #vm;
}

(* A named (non-anonymous) identity conv for leaf types. Using a named top-level
   symbol (rather than an inline lambda) lets SMT congruence equate the conv used
   in a sum's casevmatch with the conv implicit inferred from copyful_parse_leaf,
   which is required to discharge the per-case vmatch-extensionality obligation. *)
let leaf_conv (t: Type) : t -> GTot (option t) = fun x -> Some x

inline_for_extraction
fn copyful_parse_leaf
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: leaf_reader p)
: copyful_parse #_ #_ #_ (LPS.eq_as_slprop t) #_ p (leaf_conv t)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let res = r input;
  fold (LPS.eq_as_slprop t res v);
  intro_vmatch_conv (LPS.eq_as_slprop t) (leaf_conv t) res (Ghost.reveal v) (Ghost.reveal v);
  res
}

inline_for_extraction
fn free_leaf
  (#t: Type0)
: free_t #t #t (LPS.eq_as_slprop t)
=
  (x: t)
  (#v: Ghost.erased _)
{
  unfold (LPS.eq_as_slprop t x v);
}

let vmatch_synth_lhs
  (#t1' #t2' #t: Type0)
  (vmatch: t1' -> t -> slprop)
  (g: t2' -> GTot t1')
  (xl2: t2')
  (xh: t)
: slprop
= vmatch (g xl2) xh

inline_for_extraction
fn copyful_parse_synth_lhs
  (#t1' #tm #t: Type0)
  (#vmatch: t1' -> tm -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#conv: tm -> GTot (option t))
  (r: copyful_parse vmatch p conv)
  (#t2': Type0)
  (f: t1' -> t2')
  (g: t2' -> GTot t1')
  (sq: squash (forall (x: t1') . g (f x) == x))
: copyful_parse #_ #_ #_ (vmatch_synth_lhs vmatch g) #_ p conv
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let res = r input;
  elim_vmatch_conv vmatch conv res (Ghost.reveal v);
  with vm . assert (vmatch res vm ** pure (conv vm == Some (Ghost.reveal v)));
  let res2 = f res;
  rewrite (vmatch res vm) as (vmatch (g res2) vm);
  fold (vmatch_synth_lhs vmatch g res2 vm);
  intro_vmatch_conv (vmatch_synth_lhs vmatch g) conv res2 vm (Ghost.reveal v);
  res2
}

inline_for_extraction
fn free_synth_lhs
  (#t1' #t: Type0)
  (#vmatch: t1' -> t -> slprop)
  (free: free_t vmatch)
  (#t2': Type0)
  (g: t2' -> GTot t1')
  (g': t2' -> t1')
  (sq: squash (forall (x: t2') . g' x == g x))
: free_t #t2' #t (vmatch_synth_lhs vmatch g)
=
  (x: t2')
  (#v: Ghost.erased _)
{
  unfold (vmatch_synth_lhs vmatch g x v);
  rewrite (vmatch (g x) v) as (vmatch (g' x) v);
  free (g' x);
}

inline_for_extraction
fn copyful_parse_ext
  (#t' #tm #t1: Type0)
  (#vmatch1: t' -> tm -> slprop)
  (#conv1: tm -> GTot (option t1))
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (w: copyful_parse vmatch1 p1 conv1)
  (#k2: Ghost.erased parser_kind)
  (p2: parser k2 t1)
  (vmatch2: t' -> tm -> slprop)
  (sq: squash (
    LPS.pts_to_serialized_ext_trade_gen_precond p2 p1 /\
    (forall (x: t') (vm: tm) .
      vmatch2 x vm == vmatch1 x vm)
  ))
: copyful_parse #_ #_ #_ vmatch2 #_ p2 conv1
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t1)
{
  pts_to_parsed_ext_trade_gen p1 input;
  with v1 . assert (pts_to_parsed p1 input #pm v1);
  let res = w input;
  Trade.elim (pts_to_parsed p1 input #pm v1) (pts_to_parsed p2 input #pm v);
  elim_vmatch_conv vmatch1 conv1 res (Ghost.reveal v1);
  with vm . assert (vmatch1 res vm ** pure (conv1 vm == Some (Ghost.reveal v1)));
  rewrite (vmatch1 res vm) as (vmatch2 res vm);
  intro_vmatch_conv vmatch2 conv1 res vm (Ghost.reveal v);
  res
}

inline_for_extraction
fn free_ext
  (#t' #t1: Type0)
  (#vmatch1: t' -> t1 -> slprop)
  (free1: free_t vmatch1)
  (#t2: Type0)
  (vmatch2: t' -> t2 -> slprop)
  (sq: squash (
    t1 == t2 /\
    (forall (x: t') (vb: t2) .
      vmatch2 x vb == vmatch1 x (coerce t1 vb))
  ))
: free_t #t' #t2 vmatch2
=
  (x: t')
  (#v: Ghost.erased t2)
{
  let v1 : Ghost.erased t1 = Ghost.hide (coerce t1 (Ghost.reveal v));
  rewrite (vmatch2 x v) as (vmatch1 x v1);
  free1 x #v1;
}

(* Re-index a [copyful_parse] from a mid type [tm1] (with predicate [vmatch1] and
   conv [conv1]) to a different mid type [tm2] (predicate [vmatch2], conv [conv2]),
   given a ghost map [fg : tm1 -> tm2] that is compatible with both the predicate
   and the conv. Used to bridge the library's dependent-pair sum mid to a generated
   transparent textual mid, while keeping conv tight. *)
inline_for_extraction
fn copyful_parse_coerce_mid
  (#t' #tm1 #t1: Type0)
  (#vmatch1: t' -> tm1 -> slprop)
  (#conv1: tm1 -> GTot (option t1))
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (w: copyful_parse vmatch1 p1 conv1)
  (#tm2: Type0)
  (vmatch2: t' -> tm2 -> slprop)
  (conv2: tm2 -> GTot (option t1))
  (fg: tm1 -> GTot tm2)
  (sq: squash (
    (forall (x: t') (m1: tm1) . vmatch1 x m1 == vmatch2 x (fg m1)) /\
    (forall (m1: tm1) . conv2 (fg m1) == conv1 m1)
  ))
: copyful_parse #_ #_ #_ vmatch2 #_ p1 conv2
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t1)
{
  let res = w input;
  elim_vmatch_conv vmatch1 conv1 res (Ghost.reveal v);
  with m1 . assert (vmatch1 res m1 ** pure (conv1 m1 == Some (Ghost.reveal v)));
  rewrite (vmatch1 res m1) as (vmatch2 res (fg m1));
  intro_vmatch_conv vmatch2 conv2 res (fg m1) (Ghost.reveal v);
  res
}

(* Re-index a [free_t] from a mid type [tm1] to [tm2], given a ghost map
   [gf : tm2 -> tm1] compatible with the predicate. *)
inline_for_extraction
fn free_coerce_mid
  (#t' #tm1: Type0)
  (#vmatch1: t' -> tm1 -> slprop)
  (free1: free_t vmatch1)
  (#tm2: Type0)
  (vmatch2: t' -> tm2 -> slprop)
  (gf: tm2 -> GTot tm1)
  (sq: squash (forall (x: t') (m2: tm2) . vmatch2 x m2 == vmatch1 x (gf m2)))
: free_t #t' #tm2 vmatch2
=
  (x: t')
  (#v: Ghost.erased tm2)
{
  let v1 : Ghost.erased tm1 = Ghost.hide (gf (Ghost.reveal v));
  rewrite (vmatch2 x v) as (vmatch1 x v1);
  free1 x #v1;
}

let l2r_safe_writer_postcond
  (#tm #t: Type0)
  (conv: tm -> GTot (option t))
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (y: tm)
  (v': Seq.seq byte)
  (res: SZ.t)
  (err: bool)
: Tot prop
= begin match conv y with
  | None -> err == true
  | Some y' ->
    let sy = serialize s y' in
    let len = Seq.length sy in
    err == (Seq.length v' < len) /\
    (err == false ==> (SZ.v res == len /\ Seq.slice v' 0 len == sy))
  end

inline_for_extraction
let l2r_safe_writer
  (#t' #tm #t: Type0)
  (vmatch: t' -> tm -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
=
  (x: t') ->
  (#y: Ghost.erased tm) ->
  (out: slice byte) ->
  (#v: Ghost.erased (Seq.seq byte)) ->
  (perr: ref bool) ->
  stt SZ.t
      (exists* err . S.pts_to out v ** vmatch x y ** R.pts_to perr err)
      (fun sz -> exists* v' err . S.pts_to out v' ** vmatch x y ** R.pts_to perr err **
      	   pure (l2r_safe_writer_postcond conv s (Ghost.reveal y) v' sz err)
      )

(* Leaf safe writer: the copyful leaf representation IS the value (eq_as_slprop),
   and [leaf_conv] never fails, so the writer fails (err=true) iff there is not
   enough room. Requires a constant-size leaf so the serialized size [sz] is known
   before writing. *)
inline_for_extraction
fn l2r_safe_writer_leaf
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sz: SZ.t {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == SZ.v sz
  })
  (w: LPS.l2r_leaf_writer s)
: l2r_safe_writer #t #t #t (LPS.eq_as_slprop t) #k #p s (leaf_conv t)
=
  (x: t)
  (#y: Ghost.erased t)
  (out: slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  unfold (LPS.eq_as_slprop t x (Ghost.reveal y));
  S.pts_to_len out;
  serialize_length s x;
  let l = S.len out;
  if (SZ.lt l sz) {
    perr := true;
    fold (LPS.eq_as_slprop t x (Ghost.reveal y));
    sz
  } else {
    let res = w x out 0sz;
    perr := false;
    fold (LPS.eq_as_slprop t x (Ghost.reveal y));
    res
  }
}

(* Re-index an [l2r_safe_writer] across an extensionally-equal parser/serializer
   (mirrors [copyful_parse_ext]). The serialized bytes are unchanged because the
   precondition demands [serialize s2] agrees pointwise with [serialize s1]; the
   predicate is re-indexed via the pointwise [vmatch2 == vmatch1] equality. *)
inline_for_extraction
fn l2r_safe_writer_ext
  (#t' #tm #t1: Type0)
  (#vmatch1: t' -> tm -> slprop)
  (#conv1: tm -> GTot (option t1))
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (w: l2r_safe_writer vmatch1 s1 conv1)
  (#k2: parser_kind)
  (#p2: parser k2 t1)
  (s2: serializer p2)
  (vmatch2: t' -> tm -> slprop)
  (sq: squash (
    (forall (x: t') (vm: tm) . vmatch2 x vm == vmatch1 x vm) /\
    (forall (x: t1) . serialize s2 x == serialize s1 x)
  ))
: l2r_safe_writer #_ #_ #_ vmatch2 #_ #p2 s2 conv1
=
  (x: t')
  (#y: Ghost.erased tm)
  (out: slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  rewrite (vmatch2 x (Ghost.reveal y)) as (vmatch1 x (Ghost.reveal y));
  let res = w x out perr;
  with v' err. assert (S.pts_to out v' ** vmatch1 x (Ghost.reveal y) ** R.pts_to perr err ** pure (l2r_safe_writer_postcond conv1 s1 (Ghost.reveal y) v' res err));
  rewrite (vmatch1 x (Ghost.reveal y)) as (vmatch2 x (Ghost.reveal y));
  res
}
inline_for_extraction
fn l2r_safe_writer_coerce_mid
  (#t' #tm1 #t: Type0)
  (#vmatch1: t' -> tm1 -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (#conv1: tm1 -> GTot (option t))
  (w: l2r_safe_writer vmatch1 s conv1)
  (#tm2: Type0)
  (vmatch2: t' -> tm2 -> slprop)
  (conv2: tm2 -> GTot (option t))
  (gf: tm2 -> GTot tm1)
  (sq: squash (
    (forall (x: t') (m2: tm2) . vmatch2 x m2 == vmatch1 x (gf m2)) /\
    (forall (m2: tm2) . conv2 m2 == conv1 (gf m2))
  ))
: l2r_safe_writer #t' #tm2 #t vmatch2 #k #p s conv2
=
  (x: t')
  (#y: Ghost.erased tm2)
  (out: slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  let y1 : Ghost.erased tm1 = Ghost.hide (gf (Ghost.reveal y));
  rewrite (vmatch2 x (Ghost.reveal y)) as (vmatch1 x (Ghost.reveal y1));
  let res = w x out perr;
  rewrite (vmatch1 x (Ghost.reveal y1)) as (vmatch2 x (Ghost.reveal y));
  res
}

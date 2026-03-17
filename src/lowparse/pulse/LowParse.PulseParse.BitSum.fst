module LowParse.PulseParse.BitSum
#lang-pulse
include LowParse.Spec.BitSum
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module L = FStar.List.Tot

module LPB = LowParse.Pulse.BitSum

inline_for_extraction
let read_synth_cont_ifthenelse
  (#t: Type0)
  (x: Ghost.erased t)
: Tot (if_combinator_weak (PPC.read_synth_cont_t #t x))
= fun cond iftrue iffalse t' g' -> if cond then iftrue () t' g' else iffalse () t' g'

inline_for_extraction
let read_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (d: destr_bitsum'_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: PPB.reader p)
: Tot (PPB.reader (parse_bitsum' b p))
= PPC.read_synth
    (PPC.read_filter
      r
      (filter_bitsum' b)
    )
    (synth_bitsum'_injective b; synth_bitsum' b)
    (synth_bitsum'_recip_inverse b; synth_bitsum'_recip b)
    (
      d
        (PPC.read_synth_cont_t #(bitsum'_type b))
        (read_synth_cont_ifthenelse #(bitsum'_type b))
        (PPC.read_synth_cont_init)
    )

(* Validators *)

#push-options "--z3rlimit 16"

inline_for_extraction
let validate_bitsum'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#k: parser_kind)
  (#p: parser k t)
  (v: LPS.validator p)
  (r: PPB.leaf_reader p)
  (phi: filter_bitsum'_t b)
  (_: squash (k.parser_kind_subkind == Some ParserStrong))
: Tot (LPS.validator (parse_bitsum' b p))
= synth_bitsum'_injective b;
  PPC.validate_synth
    (PPC.validate_filter
      v
      r
      (filter_bitsum' b)
      (fun x -> phi x)
      ()
    )
    (synth_bitsum' b)

inline_for_extraction
noextract
let validate_bitsum_cases_t
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#from: nat)
  (b: bitsum' cl from)
: Tot Type
= (u: (bitsum'_key_type b -> Tot Type0)) ->
  (f: ((x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (u x)))) ->
  (v: ((x: bitsum'_key_type b) -> Tot (LPS.validator #(u x) #(dfst (f x)) (dsnd (f x))))) ->
  (x: parse_filter_refine (filter_bitsum' b)) ->
  Tot (LPS.validator #(u (bitsum'_key_of_t b (synth_bitsum' b x))) #(dfst (f (bitsum'_key_of_t b (synth_bitsum' b x)))) (dsnd (f (bitsum'_key_of_t b (synth_bitsum' b x)))))

inline_for_extraction
let validate_bitsum_cases_bitstop
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
: Tot (validate_bitsum_cases_t #tot #t #cl #0 (BitStop ()))
= fun u f v x -> v ()

inline_for_extraction
let validate_bitsum_cases_bitfield
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
  (phi: validate_bitsum_cases_t rest)
: Tot (validate_bitsum_cases_t (BitField sz rest))
= fun u f v x ->
  phi
    (fun x -> u (coerce (bitsum'_key_type (BitField sz rest)) x))
    (fun x -> f (coerce (bitsum'_key_type (BitField sz rest)) x))
    (fun x -> v (coerce (bitsum'_key_type (BitField sz rest)) x))
    x

inline_for_extraction
let validate_bitsum_cases_bitsum_gen
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (key_of: ((x: enum_repr e) -> Tot (y: enum_key e { y == enum_key_of_repr e x })))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (destr_payload: ((k: enum_key e) -> Tot (validate_bitsum_cases_t (payload k))))
: Tot (validate_bitsum_cases_t (BitSum' key key_size e payload))
= fun u f v x_ ->
      [@inline_let]
      let r = cl.get_bitfield x_ (bitsum'_size - key_size) bitsum'_size in
      [@inline_let]
      let k = key_of r in
      destr_payload 
        k
        (fun x -> u (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        (fun x -> f (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        (fun x -> v (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        x_

inline_for_extraction
noextract
let validate_bitsum_cases_bitsum'_t
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
: Tot Type
= (u: (bitsum'_key_type (BitSum' key key_size e payload) -> Tot Type0)) ->
  (f: ((x: bitsum'_key_type (BitSum' key key_size e payload)) -> Tot (k: parser_kind & parser k (u x)))) ->
  (v: ((x: bitsum'_key_type (BitSum' key key_size e payload)) -> Tot (LPS.validator #(u x) #(dfst (f x)) (dsnd (f x))))) ->
  (x: parse_filter_refine (filter_bitsum' (BitSum' key key_size e payload)) { ~ (list_mem (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) (list_map snd l1)) }) ->
  (xr: t { xr == cl.bitfield_eq_lhs x (bitsum'_size - key_size) bitsum'_size }) ->
  Tot (LPS.validator #(u (bitsum'_key_of_t (BitSum' key key_size e payload) (synth_bitsum' (BitSum' key key_size e payload) x))) #(dfst (f (bitsum'_key_of_t (BitSum' key key_size e payload) (synth_bitsum' (BitSum' key key_size e payload) x)))) (dsnd (f (bitsum'_key_of_t (BitSum' key key_size e payload) (synth_bitsum' (BitSum' key key_size e payload) x)))))

inline_for_extraction
let validate_bitsum_cases_bitsum'_intro
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (phi: validate_bitsum_cases_bitsum'_t cl bitsum'_size key key_size e payload [] e)
: Tot (validate_bitsum_cases_t (BitSum' key key_size e payload))
= fun u f v x ->
    let xr = cl.bitfield_eq_lhs x (bitsum'_size - key_size) bitsum'_size in
    phi u f v x xr

inline_for_extraction
let validate_bitsum_cases_bitsum'_nil
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (h: squash (e == e `L.append` []))
: Tot (validate_bitsum_cases_bitsum'_t cl bitsum'_size key key_size e payload e [])
= fun u f v x xr ->
    L.append_l_nil e;
    false_elim ()

#push-options "--z3rlimit 32"

inline_for_extraction
let validate_bitsum_cases_bitsum'_cons
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (k: key)
  (r: bitfield cl key_size)
  (l2: list (key & bitfield cl key_size) { 
    e == l1 `L.append` ((k, r) :: l2) /\
    list_mem k (list_map fst e) /\
    enum_repr_of_key e k == r /\
    e == (l1 `L.append` [(k, r)]) `L.append` l2
  })
  (destr_payload: validate_bitsum_cases_t (payload k))
  (destr_tail: validate_bitsum_cases_bitsum'_t cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) l2)
: Tot (validate_bitsum_cases_bitsum'_t cl bitsum'_size key key_size e payload l1 ((k, r) :: l2))
= fun u f v x xr ->
    let _ =
      enum_repr_of_key_append_cons e l1 (k, r) l2
    in
    [@inline_let] let yr = cl.bitfield_eq_rhs x (bitsum'_size - key_size) bitsum'_size r in
    [@inline_let] let cond = (xr <: t) = yr in
    [@inline_let] let _ = 
      assert (cond == true <==> (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) == r)
    in
    if cond
    then
      destr_payload 
        (fun x -> u (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        (fun x -> f (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        (fun x -> v (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        x
    else
      [@inline_let] let _ =
        L.append_assoc l1 [(k, r)] l2;
        L.map_append snd l1 [(k, r)];
        L.append_mem (L.map snd l1) (L.map snd [(k, r)]) (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size)
      in
      destr_tail u f v (x <: t) xr

#pop-options

[@filter_bitsum'_t_attr]
noextract
let rec mk_validate_bitsum_cases_bitsum'_t'
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
  (mk_validate_bitsum_cases_t':
    (b: bitsum' cl (bitsum'_size - key_size) { b << BitSum' key key_size e payload }) ->
    Tot (validate_bitsum_cases_t b)
  )
: Tot (validate_bitsum_cases_bitsum'_t cl bitsum'_size key key_size e payload l1 l2)
      (decreases %[BitSum' key key_size e payload; l2])
= bitsum_wellfoundedness (BitSum' key key_size e payload);
  match l2 with
  | [] ->
    [@inline_let] let _ =
      L.append_l_nil l1
    in
    validate_bitsum_cases_bitsum'_nil cl bitsum'_size key key_size e payload ()
  | (k, r) :: q ->
    [@inline_let] let _ =
      enum_repr_of_key_append_cons e l1 (k, r) q;
      L.append_assoc l1 [(k, r)] q
    in  
    validate_bitsum_cases_bitsum'_cons cl bitsum'_size key key_size e payload l1 k r q
      (mk_validate_bitsum_cases_t' (payload k))
      (mk_validate_bitsum_cases_bitsum'_t' cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) q mk_validate_bitsum_cases_t')

[@filter_bitsum'_t_attr]
noextract
let rec mk_validate_bitsum_cases_t'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot (validate_bitsum_cases_t b)
  (decreases b)
= match b with
  | BitStop _ -> validate_bitsum_cases_bitstop cl
  | BitField sz rest -> validate_bitsum_cases_bitfield cl bitsum'_size sz rest (mk_validate_bitsum_cases_t' rest)
  | BitSum' key key_size e payload ->
    validate_bitsum_cases_bitsum'_intro cl bitsum'_size key key_size e payload (mk_validate_bitsum_cases_bitsum'_t' cl bitsum'_size key key_size e payload [] e (mk_validate_bitsum_cases_t' #tot #t #cl #(bitsum'_size - key_size)))

#push-options "--z3rlimit 64"
#restart-solver

inline_for_extraction
fn validate_bitsum
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (v: LPS.validator p)
  (r: PPB.leaf_reader p)
  (phi: filter_bitsum'_t b)
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (vf: (x: bitsum'_key_type b) -> Tot (LPS.validator #(type_of_tag x) #(dfst (f x)) (dsnd (f x))))
  (vs: validate_bitsum_cases_t b)
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
: LPS.validator #data #(parse_bitsum_kind kt b type_of_tag f) (parse_bitsum b tag_of_data type_of_tag synth_case p f)
=
  (input: S.slice byte)
  (poffset: ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_bitsum_eq b tag_of_data type_of_tag synth_case p f sinput;
  let offset_val = !poffset;
  let is_valid_tag = validate_bitsum' b v r phi () input poffset;
  if is_valid_tag {
    let off = !poffset;
    synth_bitsum'_injective b;
    parse_synth_eq (p `parse_filter` filter_bitsum' b) (synth_bitsum' b) sinput;
    parse_filter_eq p (filter_bitsum' b) sinput;
    let x = PPB.read_parsed_from_validator_success r input offset_val off;
    let tg = Ghost.hide (bitsum'_key_of_t b (synth_bitsum' b x));
    parse_synth_eq (dsnd (f tg)) (synth_case.f (synth_bitsum' b x)) (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    Seq.lemma_eq_elim
      (Seq.slice sinput (SZ.v off - SZ.v offset_val) (Seq.length sinput))
      (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    let res = vs type_of_tag f vf x input poffset;
    if res {
      true
    } else {
      poffset := offset_val;
      false
    }
  } else {
    false
  }
}

#pop-options

#pop-options

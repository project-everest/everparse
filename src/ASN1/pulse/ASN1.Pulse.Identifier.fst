module ASN1.Pulse.Identifier
#lang-pulse
open Pulse.Lib.Pervasives
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module Cast = FStar.Int.Cast
module LPS = LowParse.Pulse.Base
module LPI = LowParse.Pulse.Int
module PPB = LowParse.PulseParse.Base
module T = LowParse.Tot.Combinators
module SC = LowParse.Spec.Combinators

(* Validating reader for ASN.1 identifiers (X.690 8.1.2), built by
   following the structure of the spec parser
   `ASN1.Spec.IdentifierU32.parse_asn1_identifier_U32`. *)


inline_for_extraction
let vread_u8 : vreader LowParse.Spec.Int.parse_u8 =
  vread_of_validator LPI.validate_u8 (PPB.leaf_reader_of_serialized (LPI.read_u8' ())) ()

(* parse_cast *)

let parse_cast_eq
  (t : eqtype)
  (p1 : t -> prop)
  (p2 : t -> prop)
  (lem : (x : t -> (Lemma (p1 x ==> p2 x))))
  (#k : parser_kind)
  (p : parser k (x: t {p1 x}))
  (b: bytes)
: Lemma
  (match parse (parse_cast t p1 p2 lem p) b, parse p b with
   | None, None -> True
   | Some (x, l), Some (x', l') -> (x <: t) == (x' <: t) /\ l == l'
   | _ -> False)
  [SMTPat (parse (parse_cast t p1 p2 lem p) b)]
= let id_cast =
    fun (x : t {p1 x}) ->
      let _ = lem x in
      (x <: (x : t {p2 x}))
  in
  T.parse_synth_eq #k #(x : t{p1 x}) #(x : t{p2 x}) p id_cast b

let parse_cast_ext
  (t : eqtype)
  (p1 : t -> prop)
  (p2 : t -> prop)
  (lem1 : (x : t -> (Lemma (p1 x ==> p2 x))))
  (#k : parser_kind)
  (p : parser k (x: t {p1 x}))
: Lemma
  (forall (lem2 : (x : t -> (Lemma (p1 x ==> p2 x)))) (b: bytes) .
    parse (parse_cast t p1 p2 lem1 p) b == parse (parse_cast t p1 p2 lem2 p) b)
= let aux (lem2 : (x : t -> (Lemma (p1 x ==> p2 x)))) (b: bytes)
  : Lemma (parse (parse_cast t p1 p2 lem1 p) b == parse (parse_cast t p1 p2 lem2 p) b)
  = parse_cast_eq t p1 p2 lem1 p b;
    parse_cast_eq t p1 p2 lem2 p b
  in
  Classical.forall_intro_2 aux

inline_for_extraction
fn vread_cast
  (t : eqtype)
  (p1 : Ghost.erased (t -> prop))
  (p2 : Ghost.erased (t -> prop))
  (lem : (x : t -> (Lemma (Ghost.reveal p1 x ==> Ghost.reveal p2 x))))
  (#k : Ghost.erased parser_kind)
  (#p : parser k (x: t {Ghost.reveal p1 x}))
  (r : vreader #(x: t {Ghost.reveal p1 x}) #(Ghost.reveal k) p)
: vreader #(x: t {Ghost.reveal p2 x}) #(Ghost.reveal k) (parse_cast t p1 p2 lem p)
=
  (input: S.slice LowParse.Bytes.byte)
  (poffset: _)
  (#offset: _)
  (#pm: perm)
  (#v: Ghost.erased LowParse.Bytes.bytes)
{
  parse_cast_eq t p1 p2 lem p (Seq.slice v (SZ.v offset) (Seq.length v));
  let res = r input poffset;
  match res {
    None -> { None #(x: t {Ghost.reveal p2 x}) }
    Some x -> {
      lem x;
      Some #(x: t {Ghost.reveal p2 x}) x
    }
  }
}

(* Tail of the loop *)

let tail_t (state: asn1_partial_id_t) =
  (state' : asn1_partial_id_t {partial_state_prefixr state state'})

let pow2_25 : squash (U32.v 33554432ul == UInt.pow2_n #32 (32 - 7)) =
  assert_norm (U32.v 33554432ul == UInt.pow2_n #32 (32 - 7))

inline_for_extraction
let vread_tail
  (state: asn1_partial_id_t {partial_state_bound_f32 state = 3})
  (buf: U8.t)
: vreader (parse_asn1_identifier_tail state buf)
= pow2_25;
  ifthenelse_vreader (parse_asn1_identifier_tail state buf)
    (U8.lt buf 128uy && U32.lt state 33554432ul)
    (fun _ ->
      vread_ext #_ #parse_asn1_identifier_tail_kind
        (vread_weaken parse_asn1_identifier_tail_kind (vread_ret #(tail_t state) (update_state state buf)) ())
        #parse_asn1_identifier_tail_kind (parse_asn1_identifier_tail state buf))
    (fun _ ->
      vread_ext #_ #parse_asn1_identifier_tail_kind
        (vread_fail parse_asn1_identifier_tail_kind (tail_t state))
        #parse_asn1_identifier_tail_kind (parse_asn1_identifier_tail state buf))

(* Loop *)

let spec_of_tot_cont
  (#t1 #t2: Type) (#k: parser_kind)
  (f: t1 -> LowParse.Tot.Base.parser k t2)
  (x: t1)
: LowParse.Spec.Base.parser k t2
= f x

let spec_of_tot_cont_inj
  (#t1 #t2: Type) (#k: parser_kind)
  (f: t1 -> LowParse.Tot.Base.parser k t2)
: Lemma
  (and_then_cases_injective f <==> and_then_cases_injective (spec_of_tot_cont f))
  [SMTPat (and_then_cases_injective (spec_of_tot_cont f))]
= assert (forall x . spec_of_tot_cont f x == f x)

let weaken_eq (k1: parser_kind) (#k2: parser_kind) (#t: Type) (p2: LowParse.Spec.Base.parser k2 t { k1 `is_weaker_than` k2 }) (b: bytes)
: Lemma (parse (LowParse.Spec.Base.weaken k1 p2) b == parse p2 b)
= ()

let loop_continue_eq
  (i : nat {i <= 2})
  (c : parse_loop_continuation_type (i + 1) { parse_loop_continuation_spec (i + 1) c })
  (state' : asn1_partial_id_t {partial_state_bound_f32 state' = i + 1})
  (b: bytes)
: Lemma
  (parse (parse_asn1_identifier_loop_continue i c state') b ==
    parse (SC.and_then LowParse.Spec.Int.parse_u8 (spec_of_tot_cont (c state'))) b)
= T.and_then_eq LowParse.Tot.Int.parse_u8 (c state') b;
  SC.and_then_eq LowParse.Spec.Int.parse_u8 (spec_of_tot_cont (c state')) b

inline_for_extraction
let vread_loop'
  (i : nat {i <= 2})
  (c : parse_loop_continuation_type (i + 1) { parse_loop_continuation_spec (i + 1) c })
  (vc : (state : asn1_partial_id_t {partial_state_bound_f32 state = i + 1}) -> (buf : U8.t) -> vreader #(tail_t state) #(parse_asn1_identifier_loop_kind (i + 1)) (c state buf))
  (state : asn1_partial_id_t {partial_state_bound_f32 state = i })
  (buf : U8.t)
: vreader (parse_asn1_identifier_loop' i c state buf)
= ifthenelse_vreader (parse_asn1_identifier_loop' i c state buf)
    (U8.lt buf 128uy)
    (fun _ ->
      in_bound_32 i state;
      vread_ext #_ #parse_ret_kind
        (vread_ret #(tail_t state) (update_state state buf))
        #(parse_asn1_identifier_loop_kind i) (parse_asn1_identifier_loop' i c state buf))
    (fun _ ->
     vread_let (parse_asn1_identifier_loop' i c state buf) (loop_continue_calc_state' state buf) (fun state' ->
      Classical.forall_intro (loop_continue_eq i c state');
      Classical.forall_intro (weaken_eq (parse_asn1_identifier_loop_kind i) (SC.and_then LowParse.Spec.Int.parse_u8 (spec_of_tot_cont (c state'))));
      vread_ext #_ #(parse_asn1_identifier_loop_kind i)
        (vread_cast asn1_partial_id_t
          (fun state'' -> partial_state_prefixr state' state'')
          (fun state'' -> partial_state_prefixr state state'')
          (Classical.move_requires (partial_state_prefixr_trans state state'))
          (vread_ext #_ #(parse_asn1_identifier_loop_kind i)
            (vread_weaken (parse_asn1_identifier_loop_kind i)
              (vread_and_then #LowParse.Spec.Int.parse_u8_kind vread_u8 #(parse_asn1_identifier_loop_kind (i + 1)) #_ #(spec_of_tot_cont (c state')) (vc state') ())
              ())
            #(parse_asn1_identifier_loop_kind i) (parse_asn1_identifier_loop_continue i c state')))
        #(parse_asn1_identifier_loop_kind i) (parse_asn1_identifier_loop' i c state buf)))

#push-options "--fuel 1"
let loop_eq (i : nat {i <= 2}) (state : asn1_partial_id_t {partial_state_bound_f32 state = i}) (buf: U8.t)
: Lemma (parse_asn1_identifier_loop i state buf == parse_asn1_identifier_loop' i (parse_asn1_identifier_loop (i + 1)) state buf)
= ()

let loop3_eq (state : asn1_partial_id_t {partial_state_bound_f32 state = 3}) (buf: U8.t)
: Lemma (parse_asn1_identifier_loop 3 state buf == parse_asn1_identifier_tail state buf)
= ()
#pop-options

inline_for_extraction
let vread_loop3
  (state : asn1_partial_id_t {partial_state_bound_f32 state = 3})
  (buf : U8.t)
: vreader (parse_asn1_identifier_loop 3 state buf)
= loop3_eq state buf;
  vread_ext #_ #(parse_asn1_identifier_loop_kind 3) (vread_tail state buf)
    #(parse_asn1_identifier_loop_kind 3) (parse_asn1_identifier_loop 3 state buf)

inline_for_extraction
let vread_loop2
  (state : asn1_partial_id_t {partial_state_bound_f32 state = 2})
  (buf : U8.t)
: vreader (parse_asn1_identifier_loop 2 state buf)
= loop_eq 2 state buf;
  vread_ext #_ #(parse_asn1_identifier_loop_kind 2) (vread_loop' 2 (parse_asn1_identifier_loop 3) vread_loop3 state buf)
    #(parse_asn1_identifier_loop_kind 2) (parse_asn1_identifier_loop 2 state buf)

inline_for_extraction
let vread_loop1
  (state : asn1_partial_id_t {partial_state_bound_f32 state = 1})
  (buf : U8.t)
: vreader (parse_asn1_identifier_loop 1 state buf)
= loop_eq 1 state buf;
  vread_ext #_ #(parse_asn1_identifier_loop_kind 1) (vread_loop' 1 (parse_asn1_identifier_loop 2) vread_loop2 state buf)
    #(parse_asn1_identifier_loop_kind 1) (parse_asn1_identifier_loop 1 state buf)

inline_for_extraction
let vread_loop0
  (state : asn1_partial_id_t {partial_state_bound_f32 state = 0})
  (buf : U8.t)
: vreader (parse_asn1_identifier_loop 0 state buf)
= loop_eq 0 state buf;
  vread_ext #_ #(parse_asn1_identifier_loop_kind 0) (vread_loop' 0 (parse_asn1_identifier_loop 1) vread_loop1 state buf)
    #(parse_asn1_identifier_loop_kind 0) (parse_asn1_identifier_loop 0 state buf)

(* Head *)

let tot_and_then_eq
  (#k: parser_kind) (#t: Type) (p: LowParse.Tot.Base.parser k t)
  (#k': parser_kind) (#t': Type) (p': t -> LowParse.Tot.Base.parser k' t')
  (b: bytes)
: Lemma
  (requires ((and_then_kind k k').parser_kind_injective ==> and_then_cases_injective p'))
  (ensures (parse (T.and_then p p') b == parse (SC.and_then #k #t p #k' #t' (spec_of_tot_cont p')) b))
= T.and_then_eq p p' b;
  SC.and_then_eq #k #t p #k' #t' (spec_of_tot_cont p') b

let head_cast_lem (state: asn1_partial_id_t) (x: asn1_partial_id_t)
: Lemma (partial_state_prefixr state x ==> (31 <= U32.v x <: prop))
= if partial_state_bound_f32 x >= 1
  then begin
    lemma_partial_state_lowerbound_mono (partial_state_bound_f32 x) 1;
    assert_norm (partial_state_lowerbound 1 == 128)
  end

#push-options "--ifuel 2"
let head_eq (buf: U8.t) (b: bytes)
: Lemma
  (requires (U8.v buf >= 128 /\ U8.v buf - 128 <> 0))
  (ensures (
    let state = initialize_partial_state (U8.sub buf 128uy) in
    match parse (parse_asn1_identifier_head buf) b, parse (parse_asn1_identifier_head' state) b with
    | None, None -> True
    | Some (x, l), Some (x', l') -> (x <: U32.t) == (x' <: U32.t) /\ l == l'
    | _ -> False
  ))
= assert (parse_asn1_identifier_head buf == parse_cast asn1_partial_id_t (fun x -> partial_state_prefixr (initialize_partial_state (U8.sub buf 128uy)) x) (fun x -> 31 <= U32.v x) (fun _ -> ()) (parse_asn1_identifier_head' (initialize_partial_state (U8.sub buf 128uy))));
  parse_cast_eq asn1_partial_id_t (fun x -> partial_state_prefixr (initialize_partial_state (U8.sub buf 128uy)) x) (fun x -> 31 <= U32.v x) (fun _ -> ()) (parse_asn1_identifier_head' (initialize_partial_state (U8.sub buf 128uy))) b
#pop-options

let head_cast (state: asn1_partial_id_t) (x: asn1_partial_id_t {partial_state_prefixr state x})
: Tot (state : asn1_partial_id_t {31 <= U32.v state})
= head_cast_lem state x; x

let head_eq_all (buf: U8.t)
: Lemma
  (requires (U8.v buf >= 128 /\ U8.v buf - 128 <> 0))
  (ensures (
    let state = initialize_partial_state (U8.sub buf 128uy) in
    vread_map_prop #parse_asn1_identifier_head_kind (parse_asn1_identifier_head' state) (head_cast state) #parse_asn1_identifier_head_kind (parse_asn1_identifier_head buf)
  ))
= Classical.forall_intro (head_eq buf)

let head_t = (state : asn1_partial_id_t {31 <= U32.v state})

let head'_eq
  (state : asn1_partial_id_t {partial_state_bound_f32 state = 0})
  (b: bytes)
: Lemma
  (parse (parse_asn1_identifier_head' state) b == parse (SC.and_then LowParse.Spec.Int.parse_u8 (spec_of_tot_cont (parse_asn1_identifier_loop 0 state))) b)
= tot_and_then_eq LowParse.Tot.Int.parse_u8 (parse_asn1_identifier_loop 0 state) b

inline_for_extraction
let vread_head'
  (state : asn1_partial_id_t {partial_state_bound_f32 state = 0})
: vreader (parse_asn1_identifier_head' state)
= Classical.forall_intro (head'_eq state);
  vread_ext #_ #parse_asn1_identifier_head_kind
    (vread_weaken parse_asn1_identifier_head_kind
      (vread_and_then #LowParse.Spec.Int.parse_u8_kind vread_u8 #(parse_asn1_identifier_loop_kind 0) #_ #(spec_of_tot_cont (parse_asn1_identifier_loop 0 state)) (vread_loop0 state) ())
      ())
    #parse_asn1_identifier_head_kind (parse_asn1_identifier_head' state)

inline_for_extraction
let vread_head
  (buf : U8.t)
: vreader (parse_asn1_identifier_head buf)
= ifthenelse_vreader (parse_asn1_identifier_head buf)
    (U8.lt buf 128uy)
    (fun _ ->
      ifthenelse_vreader (parse_asn1_identifier_head buf)
        (U8.lt buf 31uy)
        (fun _ ->
          vread_ext #_ #parse_asn1_identifier_head_kind
            (vread_fail parse_asn1_identifier_head_kind head_t)
            #parse_asn1_identifier_head_kind (parse_asn1_identifier_head buf))
        (fun _ ->
          vread_ext #_ #parse_asn1_identifier_head_kind
            (vread_weaken parse_asn1_identifier_head_kind (vread_ret #head_t (initialize_partial_state buf)) ())
            #parse_asn1_identifier_head_kind (parse_asn1_identifier_head buf)))
    (fun _ ->
      ifthenelse_vreader (parse_asn1_identifier_head buf)
        (U8.sub buf 128uy = 0uy)
        (fun _ ->
          vread_ext #_ #parse_asn1_identifier_head_kind
            (vread_fail parse_asn1_identifier_head_kind head_t)
            #parse_asn1_identifier_head_kind (parse_asn1_identifier_head buf))
        (fun _ ->
          head_eq_all buf;
          vread_let (parse_asn1_identifier_head buf) (initialize_partial_state (U8.sub buf 128uy)) (fun state ->
          vread_map (vread_head' state) (head_cast state)
            #parse_asn1_identifier_head_kind (parse_asn1_identifier_head buf) ())))


(* First byte *)

let first_cast (x: U32.t {31 <= U32.v x}) : Tot U32.t = x

let first'_eq (buf : U8.t {U8.v buf == 31}) (b: bytes)
: Lemma
  (requires (and_then_cases_injective parse_asn1_identifier_head))
  (ensures (match parse (parse_asn1_identifier_first' buf) b,
         parse (SC.and_then #_ #_ LowParse.Spec.Int.parse_u8 #parse_asn1_identifier_head_kind #_ (spec_of_tot_cont parse_asn1_identifier_head)) b with
    | None, None -> True
    | Some (x, l), Some (x', l') -> (x <: U32.t) == (x' <: U32.t) /\ l == l'
    | _ -> False
  ))
= assert (parse_asn1_identifier_first' buf == parse_cast U32.t (fun x -> 31 <= U32.v x) (fun _ -> True) (fun _ -> ())
    (weaken parse_asn1_identifier_first_kind (T.and_then LowParse.Tot.Int.parse_u8 parse_asn1_identifier_head)));
  parse_cast_eq U32.t (fun x -> 31 <= U32.v x) (fun _ -> True) (fun _ -> ())
    (weaken parse_asn1_identifier_first_kind (T.and_then LowParse.Tot.Int.parse_u8 parse_asn1_identifier_head)) b;
  tot_and_then_eq LowParse.Tot.Int.parse_u8 parse_asn1_identifier_head b

let first'_eq_all (buf : U8.t {U8.v buf == 31})
: Lemma
  (requires (and_then_cases_injective parse_asn1_identifier_head))
  (ensures (vread_map_prop #(and_then_kind LowParse.Spec.Int.parse_u8_kind parse_asn1_identifier_head_kind)
    (SC.and_then #_ #_ LowParse.Spec.Int.parse_u8 #parse_asn1_identifier_head_kind #_ (spec_of_tot_cont parse_asn1_identifier_head))
    first_cast
    #parse_asn1_identifier_first_kind
    (parse_asn1_identifier_first' buf)))
= Classical.forall_intro (Classical.move_requires (first'_eq buf))

inline_for_extraction
let vread_first'
  (buf : U8.t {U8.v buf <= 31})
: vreader (parse_asn1_identifier_first' buf)
= ifthenelse_vreader (parse_asn1_identifier_first' buf)
    (U8.lt buf 31uy)
    (fun _ ->
      vread_ext #_ #parse_asn1_identifier_first_kind
        (vread_weaken parse_asn1_identifier_first_kind (vread_ret (Cast.uint8_to_uint32 buf)) ())
        #parse_asn1_identifier_first_kind (parse_asn1_identifier_first' buf))
    (fun _ ->
      lemma_parse_asn1_identifier_head_inj ();
      first'_eq_all buf;
      vread_map
        (vread_and_then #LowParse.Spec.Int.parse_u8_kind vread_u8 #parse_asn1_identifier_head_kind #_ #(spec_of_tot_cont parse_asn1_identifier_head) vread_head ())
        first_cast
        #parse_asn1_identifier_first_kind (parse_asn1_identifier_first' buf)
        ())

let first_eq_all (buf : U8.t)
: Lemma
  (vread_map_prop #parse_asn1_identifier_first_kind
    (parse_asn1_identifier_first' (U8.rem buf 32uy))
    (MK_ASN1_ID (decode_asn1_identifier_class' buf) (decode_asn1_identifier_flag' buf))
    #parse_asn1_identifier_first_kind
    (parse_asn1_identifier_first buf))
= let f = MK_ASN1_ID (decode_asn1_identifier_class' buf) (decode_asn1_identifier_flag' buf) in
  let p = parse_asn1_identifier_first' (U8.rem buf 32uy) in
  assert (parse_asn1_identifier_first buf == T.parse_synth p f);
  Classical.forall_intro (T.parse_synth_eq p f)

inline_for_extraction
let vread_first
  (buf : U8.t)
: vreader (parse_asn1_identifier_first buf)
= first_eq_all buf;
  vread_map
    (vread_first' (U8.rem buf 32uy))
    (MK_ASN1_ID (decode_asn1_identifier_class' buf) (decode_asn1_identifier_flag' buf))
    #parse_asn1_identifier_first_kind (parse_asn1_identifier_first buf)
    ()

(* Identifier *)

let identifier_eq (b: bytes)
: Lemma
  (requires (and_then_cases_injective parse_asn1_identifier_first))
  (ensures (parse parse_asn1_identifier_U32 b ==
    parse (SC.and_then #_ #_ LowParse.Spec.Int.parse_u8 #parse_asn1_identifier_first_kind #_ (spec_of_tot_cont parse_asn1_identifier_first)) b))
= tot_and_then_eq LowParse.Tot.Int.parse_u8 parse_asn1_identifier_first b

inline_for_extraction noextract
let vread_identifier_spec
: vreader parse_asn1_identifier_U32
= lemma_parse_asn1_identifier_first_inj ();
  Classical.forall_intro (Classical.move_requires identifier_eq);
  vread_ext #_ #asn1_strong_parser_kind
    (vread_weaken asn1_strong_parser_kind
      (vread_and_then #LowParse.Spec.Int.parse_u8_kind vread_u8 #parse_asn1_identifier_first_kind #_ #(spec_of_tot_cont parse_asn1_identifier_first) vread_first ())
      ())
    #asn1_strong_parser_kind parse_asn1_identifier_U32

(* Extracted once as a C function shared by every TLV *)
fn vread_identifier_impl
  (input: S.slice byte)
  (poffset: ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires S.pts_to input #pm v ** pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: option asn1_id_t
  ensures S.pts_to input #pm v ** (exists* off . pts_to poffset off ** pure (vreader_postcond #asn1_strong_parser_kind parse_asn1_identifier_U32 offset v off res))
{
  vread_identifier_spec input poffset
}

inline_for_extraction
let vread_identifier : vreader parse_asn1_identifier_U32 = vread_identifier_impl

inline_for_extraction
let validate_identifier : LPS.validator parse_asn1_identifier_U32 =
  validate_of_vreader vread_identifier

inline_for_extraction
let jump_identifier : LPS.jumper parse_asn1_identifier_U32 =
  jump_of_vreader vread_identifier

inline_for_extraction
let read_identifier : PPB.leaf_reader parse_asn1_identifier_U32 =
  leaf_read_of_vreader vread_identifier

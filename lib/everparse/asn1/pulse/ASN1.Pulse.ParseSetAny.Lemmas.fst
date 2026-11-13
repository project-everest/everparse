module ASN1.Pulse.ParseSetAny.Lemmas

(* Value-level lemmas for the zero-copy parser of SET { ... } with
   components declared in any order (ASN1.Pulse.ParseSetAny.)

   The parser reads the elements of the SET in their encoding order and
   stores the value of each one in the slot of its component (the first
   component whose tags contain the tag of the element, as in
   ASN1.Spec.SetComponents.parse_set_elem); at the end, the remaining empty
   slots are filled with the default values of their components. The loop
   invariant [inv] relates the slots filled so far with the elements of the
   SET that remain to be read. *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.List

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Sequence
open ASN1.Spec.SetComponents
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Interpreter

module Seq = FStar.Seq
module Set = FStar.Set
module LS = LowParse.Spec.List
module C = ASN1.Spec.Conformance
module Sq = ASN1.Pulse.Sequence
module SC = ASN1.Pulse.SetComp
module L = ASN1.Pulse.ParseSequence.Lemmas
module PS = ASN1.Pulse.ParseSequence
module SL = ASN1.Pulse.ParseSet.Lemmas
module P = ASN1.Pulse.Parse
module In = ASN1.Pulse.Interpreter

(* Slots: the presence of a value for each component *)

let cons_l (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2)
: Tot (asn1_gen_items_l ((s, d) :: i2))
= ASN1_GEN_ITEMS_CONS s d dk i2 tl

let opt_tuple (#i: _) (ls: asn1_gen_items_l i) : Tot Type0 = list (option unit)

let sfst (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2) (st: opt_tuple (cons_l dk tl))
: Tot (option unit)
= match st with
  | [] -> None
  | o :: _ -> o

let ssnd (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2) (st: opt_tuple (cons_l dk tl))
: Tot (opt_tuple tl)
= match st with
  | [] -> []
  | _ :: r -> r

let scons (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2) (o: option unit) (r: opt_tuple tl)
: Tot (opt_tuple (cons_l dk tl))
= o :: r

let rec none_tuple (#i: _) (ls: asn1_gen_items_l i) : Tot (opt_tuple ls) (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> []
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> scons dk tl None (none_tuple tl)

let rec is_some (#i: _) (ls: asn1_gen_items_l i) (st: opt_tuple ls) (c: nat) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> false
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    if c = 0 then Some? (sfst dk tl st) else is_some tl (ssnd dk tl st) (c - 1)

let rec is_some_none (#i: _) (ls: asn1_gen_items_l i) (c: nat)
: Lemma (ensures (is_some ls (none_tuple ls) c == false)) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ _ _ tl -> if c = 0 then () else is_some_none tl (c - 1)

(* Components of a value *)

let vhd (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2) (v: asn1_sequence_t_core (cons_l dk tl))
: Tot (asn1_decorated_t_core dk)
= match tl with
  | ASN1_GEN_ITEMS_NIL -> let v' : asn1_decorated_t_core dk = v in v'
  | _ -> let v' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = v in fst v'

let vtl (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2) (v: asn1_sequence_t_core (cons_l dk tl))
: Tot (asn1_sequence_t_core tl)
= match tl with
  | ASN1_GEN_ITEMS_NIL -> ()
  | _ -> let v' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = v in snd v'

(* Precondition of the dispatch of an element with identifier [id] *)

let rec dpre (#i: _) (ls: asn1_gen_items_l i) (id: asn1_id_t) (we: bytes) (st: opt_tuple ls) (v: asn1_sequence_t_core ls) : Tot prop (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> False
  | ASN1_GEN_ITEMS_CONS s _ dk _ tl ->
    if Set.mem id s
    then None? (sfst dk tl st) /\ PS.item_parsed_core dk we (vhd dk tl v)
    else dpre tl id we (ssnd dk tl st) (vtl dk tl v)

(* Precondition of the final filling of the empty slots *)

let rec fin_pre (#i: _) (ls: asn1_gen_items_l i) (st: opt_tuple ls) (v: asn1_sequence_t_core ls) : Tot prop (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> True
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    (None? (sfst dk tl st) ==> PS.absent_core dk (vhd dk tl v)) /\
    fin_pre tl (ssnd dk tl st) (vtl dk tl v)

(* Updating the slots *)

let is_some_fill (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2)
  (st: opt_tuple (cons_l dk tl)) (id: asn1_id_t)
: Lemma
  (requires (Set.mem id s))
  (ensures (forall (c: nat) . is_some (cons_l dk tl) (scons dk tl (Some ()) (ssnd dk tl st)) c ==
    (is_some (cons_l dk tl) st c || SC.comp_of_id (In.twins_of (cons_l dk tl)) id = Some c)))
= PS.twin_d_eq dk

let is_some_pass_at (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2)
  (st: opt_tuple (cons_l dk tl)) (st': opt_tuple tl) (id: asn1_id_t) (c: nat)
: Lemma
  (requires (~ (Set.mem id s) /\
    (c > 0 ==> is_some tl st' (c - 1) == (is_some tl (ssnd dk tl st) (c - 1) || SC.comp_of_id (In.twins_of tl) id = Some (c - 1)))))
  (ensures (is_some (cons_l dk tl) (scons dk tl (sfst dk tl st) st') c ==
    (is_some (cons_l dk tl) st c || SC.comp_of_id (In.twins_of (cons_l dk tl)) id = Some c)))
= PS.twin_d_eq dk

let is_some_pass (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2)
  (st: opt_tuple (cons_l dk tl)) (st': opt_tuple tl) (id: asn1_id_t)
: Lemma
  (requires (~ (Set.mem id s) /\
    (forall (c: nat) . is_some tl st' c == (is_some tl (ssnd dk tl st) c || SC.comp_of_id (In.twins_of tl) id = Some c))))
  (ensures (forall (c: nat) . is_some (cons_l dk tl) (scons dk tl (sfst dk tl st) st') c ==
    (is_some (cons_l dk tl) st c || SC.comp_of_id (In.twins_of (cons_l dk tl)) id = Some c)))
= let prf (c: nat) : Lemma (is_some (cons_l dk tl) (scons dk tl (sfst dk tl st) st') c ==
    (is_some (cons_l dk tl) st c || SC.comp_of_id (In.twins_of (cons_l dk tl)) id = Some c))
  = is_some_pass_at dk tl st st' id c
  in
  Classical.forall_intro prf

(* The list of elements of the whole SET *)

let lfull (its: list gen_decorated_parser_twin) (w: bytes) : GTot (list (set_elem_t its)) =
  match parse (parse_list (parse_set_elem its)) w with
  | Some (l, _) -> l
  | None -> []

[@@"opaque_to_smt"]
let full (#i: _) (ls: asn1_gen_items_l i) (w: bytes) (v: asn1_sequence_t_core ls) : prop =
  let its = In.twins_of ls in
  C.items_tagged its /\
  (match parse (parse_list (parse_set_elem its)) w with
   | None -> False
   | Some (l, n) -> n == Seq.length w /\ comps_ok its l /\ set_to_tuple' its l == coerce_eq (PS.seq_t_eq ls) v)

(* The loop invariant: [wr] are the bytes remaining to be read *)

[@@"opaque_to_smt"]
let inv (#i: _) (ls: asn1_gen_items_l i) (w wr: bytes) (st: opt_tuple ls) : prop =
  let its = In.twins_of ls in
  match parse (parse_list (parse_set_elem its)) wr with
  | None -> False
  | Some (l2, n) ->
    n == Seq.length wr /\
    (forall e . List.Tot.memP e l2 ==> List.Tot.memP e (lfull its w)) /\
    (forall (c: nat) .
      (is_some ls st c ==> SC.count_comp its l2 c == 0) /\
      (is_some ls st c == false ==> SC.count_comp its l2 c == SC.count_comp its (lfull its w) c))

(* Initialization *)

let set_parsed_intro (its: list gen_decorated_parser_twin) (w: bytes) (v: asn1_sequence_t (List.Tot.map Mkgendcparser?.d its))
: Lemma
  (requires (P.parsed #asn1_weak_parser_kind (make_asn1_set_parser its) w v))
  (ensures (SL.set_parsed its w v))
= set_to_tuple_injective its;
  parse_synth_eq (parse_list (parse_set_elem its) `parse_filter` set_ok its) (set_to_tuple its) w;
  parse_filter_eq (parse_list (parse_set_elem its)) (set_ok its) w

let init (#ids: id_decs) (items: asn1_gen_items_l ids) (pf: squash (asn1_set_k_wf ids)) (w: bytes) (v: asn1_content_t (ASN1_SET ids items pf))
: Lemma
  (requires (P.parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf)) w v))
  (ensures (full items w v /\ inv items w w (none_tuple items)))
= reveal_opaque (`%full) (full items w v);
  reveal_opaque (`%inv) (inv items w w (none_tuple items));
  let _ = PS.seq_t_eq items in
  C.items_tagged_intro items;
  set_parsed_intro (In.twins_of items) w (coerce_eq (PS.seq_t_eq items) v);
  Classical.forall_intro (is_some_none items)

(* Splitting the value of a SET of one or more components *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let tuple_cons (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2)
  (lL: list (set_elem_t (In.twins_of (cons_l dk tl)))) (v: asn1_sequence_t_core (cons_l dk tl))
: Lemma
  (requires (comps_ok (In.twins_of (cons_l dk tl)) lL /\
    set_to_tuple' (In.twins_of (cons_l dk tl)) lL == coerce_eq (PS.seq_t_eq (cons_l dk tl)) v))
  (ensures (
    let lL' = SL.as_either (In.twin_of dk) (In.twins_of tl) lL in
    comp_ok (In.twin_of dk) (heads lL') /\
    comps_ok (In.twins_of tl) (tails lL') /\
    coerce_eq (PS.twin_d dk) (vhd dk tl v) == comp_value (In.twin_of dk) (heads lL') /\
    set_to_tuple' (In.twins_of tl) (tails lL') == coerce_eq (PS.seq_t_eq tl) (vtl dk tl v)))
= let _ = PS.seq_t_eq (cons_l dk tl) in
  let _ = PS.seq_t_eq tl in
  let _ = PS.twin_d dk in
  ()
#pop-options

(* The bytes of a present component *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let item_prefix (hd: gen_decorated_parser_twin) (wr: bytes) (id: asn1_id_t) (n1: nat) (v1: asn1_decorated_t (Mkgendcparser?.d hd)) (n2: nat)
: Lemma
  (requires (L.item_shaped hd /\
    (match parse parse_asn1_identifier_U32 wr with
     | Some (id', n1') -> id' == id /\ n1' == n1
     | None -> False) /\
    n1 <= Seq.length wr /\
    (match parse (parse_asn1_sequence_item_twin hd id) (Seq.slice wr n1 (Seq.length wr)) with
     | Some (v1', n2') -> v1' == v1 /\ n2' == n2
     | None -> False)))
  (ensures (L.tlv_size wr == Some (n1 + n2) /\ n1 + n2 <= Seq.length wr /\ L.item_parsed hd (Seq.slice wr 0 (n1 + n2)) v1))
= let b1 = Seq.slice wr n1 (Seq.length wr) in
  let p1 = parse_asn1_sequence_item_twin hd id in
  let Some (_, n2') = parse p1 b1 in
  assert (n2' <= Seq.length b1);
  let Some (_, n1') = parse parse_asn1_identifier_U32 wr in
  assert (n1' <= Seq.length wr);
  assert (L.lc_shaped p1);
  assert (Sq.consumed #asn1_strong_parser_kind p1 b1 == Some n2);
  let w' = Seq.slice wr 0 (n1 + n2) in
  L.slice_prefix_slice wr n1 n2;
  parse_strong_prefix #asn1_strong_parser_kind parse_asn1_identifier_U32 wr w';
  parse_strong_prefix #asn1_strong_parser_kind p1 b1 (Seq.slice b1 0 n2)
#pop-options

(* Dispatching an element *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let rec step_dpre (#i: _) (ls: asn1_gen_items_l i) (lL: list (set_elem_t (In.twins_of ls))) (wr: bytes) (st: opt_tuple ls) (v: asn1_sequence_t_core ls)
: Lemma
  (requires (
    comps_ok (In.twins_of ls) lL /\
    set_to_tuple' (In.twins_of ls) lL == coerce_eq (PS.seq_t_eq ls) v /\
    (match parse (parse_set_elem (In.twins_of ls)) wr with
     | None -> False
     | Some (e, _) -> List.Tot.memP e lL /\ is_some ls st (SC.elem_comp (In.twins_of ls) e) == false)))
  (ensures (match parse parse_asn1_identifier_U32 wr, parse (parse_set_elem (In.twins_of ls)) wr with
    | Some (id, _), Some (_, n) -> L.tlv_size wr == Some n /\ n <= Seq.length wr /\ dpre ls id (Seq.slice wr 0 n) st v
    | _ -> False))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    let Some (e, _) = parse (parse_set_elem (In.twins_of ls)) wr in
    let e' : False = e in
    ()
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    let hd = In.twin_of dk in
    let its' = In.twins_of tl in
    PS.twin_d_eq dk;
    L.dec_shaped dk;
    SL.set_elem_cons hd its' wr;
    tuple_cons dk tl lL v;
    let Some (e, n) = parse (parse_set_elem (In.twins_of ls)) wr in
    let Some (id, n1) = parse parse_asn1_identifier_U32 wr in
    let lL' = SL.as_either hd its' lL in
    let e' : either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t its') = e in
    match e' with
    | Inl v1 ->
      memP_heads lL' v1;
      let Some (_, n2) = parse (parse_asn1_sequence_item_twin hd id) (Seq.slice wr n1 (Seq.length wr)) in
      item_prefix hd wr id n1 v1 n2;
      assert (heads lL' == [v1])
    | Inr e2 ->
      memP_tails lL' e2;
      step_dpre tl (tails lL') wr (ssnd dk tl st) (vtl dk tl v)
#pop-options

(* One step of the loop *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let step_pre (#i: _) (ls: asn1_gen_items_l i) (w wr: bytes) (st: opt_tuple ls) (v: asn1_sequence_t_core ls)
: Lemma
  (requires (full ls w v /\ inv ls w wr st /\ Seq.length wr > 0))
  (ensures (match parse parse_asn1_identifier_U32 wr with
    | None -> False
    | Some (id, _) ->
      match L.tlv_size wr with
      | None -> False
      | Some n -> 0 < n /\ n <= Seq.length wr /\ dpre ls id (Seq.slice wr 0 n) st v))
= reveal_opaque (`%full) (full ls w v);
  reveal_opaque (`%inv) (inv ls w wr st);
  let its = In.twins_of ls in
  LS.tot_parse_list_eq (parse_set_elem its) wr;
  L.identifier_nonempty wr;
  let Some (e, _) = parse (parse_set_elem its) wr in
  let Some (l2, _) = parse (parse_list (parse_set_elem its)) wr in
  assert (List.Tot.memP e l2);
  assert (SC.count_comp its l2 (SC.elem_comp its e) >= 1);
  step_dpre ls (lfull its w) wr st v

let count_step (its: list gen_decorated_parser_twin) (l2 q lL: list (set_elem_t its)) (e: set_elem_t its) (c: nat)
: Lemma
  (requires (l2 == e :: q /\ SC.elem_comp its e == c /\ SC.count_comp its l2 c == SC.count_comp its lL c /\ SC.count_comp its lL c <= 1))
  (ensures (SC.count_comp its q c == 0))
= ()

let step_post (#i: _) (ls: asn1_gen_items_l i) (w wr: bytes) (st st': opt_tuple ls) (v: asn1_sequence_t_core ls)
: Lemma
  (requires (full ls w v /\ inv ls w wr st /\ Seq.length wr > 0 /\
    (match parse parse_asn1_identifier_U32 wr with
     | None -> False
     | Some (id, _) -> forall (c: nat) . is_some ls st' c == (is_some ls st c || SC.comp_of_id (In.twins_of ls) id = Some c))))
  (ensures (match L.tlv_size wr with
    | None -> False
    | Some n -> n <= Seq.length wr /\ inv ls w (Seq.slice wr n (Seq.length wr)) st'))
= reveal_opaque (`%full) (full ls w v);
  reveal_opaque (`%inv) (inv ls w wr st);
  let its = In.twins_of ls in
  let lL = lfull its w in
  LS.tot_parse_list_eq (parse_set_elem its) wr;
  SC.set_elem_eq its wr;
  SC.comps_ok_iff its lL;
  let Some (e, n) = parse (parse_set_elem its) wr in
  let Some (l2, _) = parse (parse_list (parse_set_elem its)) wr in
  let ce = SC.elem_comp its e in
  assert (List.Tot.memP e l2);
  assert (SC.count_comp its l2 ce >= 1);
  step_dpre ls lL wr st v;
  let wr' = Seq.slice wr n (Seq.length wr) in
  reveal_opaque (`%inv) (inv ls w wr' st');
  let Some (q, _) = parse (parse_list (parse_set_elem its)) wr' in
  assert (l2 == e :: q);
  let Some (id, _) = parse parse_asn1_identifier_U32 wr in
  assert (SC.comp_of_id its id == Some ce);
  assert (is_some ls st ce == false);
  assert (SC.count_comp its lL ce <= 1);
  let prf (c: nat) : Lemma
    ((is_some ls st' c ==> SC.count_comp its q c == 0) /\
     (is_some ls st' c == false ==> SC.count_comp its q c == SC.count_comp its lL c))
  = assert (SC.count_comp its l2 c == (if ce = c then 1 else 0) + SC.count_comp its q c);
    assert (is_some ls st' c == (is_some ls st c || ce = c));
    if ce = c then begin
      assert (is_some ls st c == false);
      assert (SC.count_comp its l2 c == SC.count_comp its lL c);
      count_step its l2 q lL e c
    end else begin
      assert ((is_some ls st c ==> SC.count_comp its l2 c == 0) /\
        (is_some ls st c == false ==> SC.count_comp its l2 c == SC.count_comp its lL c))
    end
  in
  Classical.forall_intro prf;
  let prf2 (x: set_elem_t its) : Lemma (List.Tot.memP x q ==> List.Tot.memP x lL)
  = assert (List.Tot.memP x q ==> List.Tot.memP x l2)
  in
  Classical.forall_intro prf2;
  assert (L.tlv_size wr == Some n);
  let Some (_, nq) = parse (parse_list (parse_set_elem its)) wr' in
  assert (nq == Seq.length wr');
  assert (inv ls w wr' st')
#pop-options

(* Filling the empty slots *)

#push-options "--fuel 2 --ifuel 1"
let fin_rec_tail (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2)
  (lL: list (set_elem_t (In.twins_of (cons_l dk tl)))) (st: opt_tuple (cons_l dk tl)) (c: nat)
: Lemma
  (requires (is_some (cons_l dk tl) st (c + 1) == false ==> SC.count_comp (In.twins_of (cons_l dk tl)) lL (c + 1) == 0))
  (ensures (is_some tl (ssnd dk tl st) c == false ==>
    SC.count_comp (In.twins_of tl) (tails (SL.as_either (In.twin_of dk) (In.twins_of tl) lL)) c == 0))
= SC.heads_tails_count (In.twin_of dk) (In.twins_of tl) (SL.as_either (In.twin_of dk) (In.twins_of tl) lL)
#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec fin_rec (#i: _) (ls: asn1_gen_items_l i) (lL: list (set_elem_t (In.twins_of ls))) (st: opt_tuple ls) (v: asn1_sequence_t_core ls)
: Lemma
  (requires (
    comps_ok (In.twins_of ls) lL /\
    set_to_tuple' (In.twins_of ls) lL == coerce_eq (PS.seq_t_eq ls) v /\
    (forall (c: nat) . is_some ls st c == false ==> SC.count_comp (In.twins_of ls) lL c == 0)))
  (ensures (fin_pre ls st v))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    let hd = In.twin_of dk in
    let its' = In.twins_of tl in
    PS.twin_d_eq dk;
    tuple_cons dk tl lL v;
    let lL' = SL.as_either hd its' lL in
    SC.heads_tails_count hd its' lL';
    assert (is_some ls st 0 == false ==> SC.count_comp (In.twins_of ls) lL 0 == 0);
    let prf (c: nat) : Lemma (is_some tl (ssnd dk tl st) c == false ==> SC.count_comp its' (tails lL') c == 0)
    = fin_rec_tail dk tl lL st c
    in
    Classical.forall_intro prf;
    fin_rec tl (tails lL') (ssnd dk tl st) (vtl dk tl v)
#pop-options

#push-options "--fuel 2 --ifuel 2"
let final (#i: _) (ls: asn1_gen_items_l i) (w wr: bytes) (st: opt_tuple ls) (v: asn1_sequence_t_core ls)
: Lemma
  (requires (full ls w v /\ inv ls w wr st /\ Seq.length wr == 0))
  (ensures (fin_pre ls st v))
= reveal_opaque (`%full) (full ls w v);
  reveal_opaque (`%inv) (inv ls w wr st);
  let its = In.twins_of ls in
  LS.tot_parse_list_eq (parse_set_elem its) wr;
  fin_rec ls (lfull its w) st v
#pop-options

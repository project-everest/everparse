(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module EverParse3d.Prelude
friend EverParse3d.Kinds
module BF = LowParse.BitFields
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators
module LPL = LowParse.Low.Base
module LPLC = LowParse.Low.Combinators
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

////////////////////////////////////////////////////////////////////////////////
// Parsers
////////////////////////////////////////////////////////////////////////////////

[@@erasable]
noeq
type full_parser (#nz:bool) (#wk: weak_kind) (k:parser_kind nz wk) (t:Type u#r) : Type u#r = {
  pf_parser: LP.parser k t;
  pf_serializer: LP.serializer pf_parser;
}

[@@erasable]
noeq
type parser (#nz:bool) (#wk: weak_kind) (k:parser_kind nz wk) (t:Type u#r) : Type u#r = {
  p_serializable: (t -> GTot bool);
  p_full_parser: full_parser k (LPC.parse_filter_refine p_serializable);
}

let mk_parser_gen
  (#nz:bool) (#wk: weak_kind) (#k:parser_kind nz wk) (#t1:Type u#r)
  (p1: full_parser k t1)
  (#t2: Type u#r)
  (ser: (t2 -> GTot bool))
  (f12: (t1 -> GTot (LPC.parse_filter_refine ser)) { LPC.synth_injective f12 })
  (f21: (LPC.parse_filter_refine ser -> GTot t1) { LPC.synth_inverse f12 f21 })
: Tot (parser k t2)
= {
  p_serializable = ser;
  p_full_parser = {
    pf_parser = LPC.parse_synth p1.pf_parser f12;
    pf_serializer = LPC.serialize_synth _ _ p1.pf_serializer f21 ();
  }
}

let mk_parser
  (#nz:bool) (#wk: weak_kind) (#k:parser_kind nz wk) (#t:Type u#r)
  (p1: full_parser k t)
: Tot (parser k t)
= mk_parser_gen
    p1
    (fun _ -> true)
    (fun x -> x)
    (fun x -> x)

let is_weaker_than #nz1 #wk1 (k:parser_kind nz1 wk1)
                   #nz2 #wk2 (k':parser_kind nz2 wk2) = k `LP.is_weaker_than` k'

let is_weaker_than_refl #nz #wk (k:parser_kind nz wk)
  : Lemma (ensures (is_weaker_than k k))
          [SMTPat (is_weaker_than k k)]
  = ()

let is_weaker_than_glb #nz1 #wk1 (k1:parser_kind nz1 wk1)
                       #nz2 #wk2 (k2:parser_kind nz2 wk2)
  : Lemma (is_weaker_than (glb k1 k2) k1 /\
           is_weaker_than (glb k1 k2) k2)
          [SMTPatOr
            [[SMTPat (is_weaker_than (glb k1 k2) k1)];
             [SMTPat (is_weaker_than (glb k1 k2) k2)]]]
  = ()

let full_parse_dep_pair_body_parser
  (#t1: Type)
  (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2: (t1 -> Tot Type)) (p2: (x: t1) -> full_parser k2 (t2 x))
  (x: t1)
: LP.parser k2 (t2 x)
= (p2 x).pf_parser

let full_parse_dep_pair_body_serializer
  (#t1: Type)
  (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2: (t1 -> Tot Type)) (p2: (x: t1) -> full_parser k2 (t2 x))
  (x: t1)
: LP.serializer (full_parse_dep_pair_body_parser p2 x)
= (p2 x).pf_serializer

/// Parser: bind
inline_for_extraction noextract
let full_parse_dep_pair (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1: Type) (p1: full_parser k1 t1)
                   (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2: (t1 -> Tot Type)) (p2: (x: t1) -> full_parser k2 (t2 x))
  : Tot (full_parser (and_then_kind k1 k2) (dtuple2 t1 t2) )
  = {
    pf_parser = LPC.parse_dtuple2 p1.pf_parser (full_parse_dep_pair_body_parser p2);
    pf_serializer = LPC.serialize_dtuple2 p1.pf_serializer (full_parse_dep_pair_body_serializer p2);
  }

let parse_dep_pair_body_serializable
  (#t1: Type)
  (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2: (t1 -> Tot Type)) (p2: (x: t1) -> parser k2 (t2 x))
  (x1: t1)
: Tot (t2 x1 -> GTot bool)
= (p2 x1).p_serializable

let parse_dep_pair_body_type
  (#t1: Type)
  (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2: (t1 -> Tot Type)) (p2: (x: t1) -> parser k2 (t2 x))
  (x1: t1)
= LPC.parse_filter_refine (parse_dep_pair_body_serializable p2 x1)

let parse_dep_pair_body_full_parser
  (#t1: Type)
  (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2: (t1 -> Tot Type)) (p2: (x: t1) -> parser k2 (t2 x))
  (x1: t1)
: full_parser k2 (parse_dep_pair_body_type p2 x1)
= (p2 x1).p_full_parser

let parse_dep_pair_serializable
  (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1: Type) (p1: parser k1 t1)
                   (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2: (t1 -> Tot Type)) (p2: (x: t1) -> parser k2 (t2 x))
  (x: dtuple2 t1 t2)
: GTot bool
= p1.p_serializable (dfst x) && (p2 (dfst x)).p_serializable (dsnd x)

inline_for_extraction noextract
let parse_dep_pair #_ #_ #t1 p1 #_ #_ #_ #t2 p2 =
  mk_parser_gen
    (full_parse_dep_pair p1.p_full_parser (parse_dep_pair_body_full_parser p2))
    (parse_dep_pair_serializable p1 p2)
    (fun (| x1, x2 |) -> (| (x1 <: t1) , (x2 <: t2 x1) |))
    (fun (x: LPC.parse_filter_refine (parse_dep_pair_serializable p1 p2)) -> (| dfst x, dsnd x |))

/// Parser: sequencing
inline_for_extraction noextract
let full_parse_pair (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1:_) (p1:full_parser k1 t1)
               (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:_) (p2:full_parser k2 t2)
  : Tot (full_parser (and_then_kind k1 k2) (t1 * t2))
  = {
    pf_parser = LPC.nondep_then p1.pf_parser p2.pf_parser;
    pf_serializer = LPC.serialize_nondep_then p1.pf_serializer p2.pf_serializer;
  }

inline_for_extraction noextract
let parse_pair_serializable (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1:_) (p1:parser k1 t1)
               (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:_) (p2:parser k2 t2)
    (x: (t1 & t2))
  : GTot bool
= p1.p_serializable (fst x) && p2.p_serializable (snd x)

inline_for_extraction noextract
let parse_pair #_ #_ #t1 p1 #_ #_ #_ #t2 p2
  = mk_parser_gen
      (full_parse_pair p1.p_full_parser p2.p_full_parser)
      (parse_pair_serializable p1 p2)
      (fun x -> ((fst x <: t1), (snd x <: t2)))
      (fun (x: LPC.parse_filter_refine (parse_pair_serializable p1 p2)) -> (fst x, snd x))

/// Parser: map
let injective_map a b = (a -> Tot b) //{LPC.synth_injective f}

inline_for_extraction noextract
let full_parse_filter (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:_) (p:full_parser k t) (f:(t -> bool))
  : Tot (full_parser (filter_kind k) (refine t f))
  = {
  pf_parser = LPC.parse_filter p.pf_parser f;
  pf_serializer = LPC.serialize_filter p.pf_serializer f;
}

inline_for_extraction noextract
let parse_filter p f
= mk_parser_gen
    (full_parse_filter p.p_full_parser f)
    p.p_serializable
    (fun x -> x)
    (fun x -> x)

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken #nz #wk (#k:parser_kind nz wk) #t (p:parser k t)
                 #nz' #wk' (k':parser_kind nz' wk' {k' `is_weaker_than` k})
  : Tot (parser k' t)
  = {
  p_serializable = p.p_serializable;
  p_full_parser = {
    pf_parser = LP.weaken k' p.p_full_parser.pf_parser;
    pf_serializer = LPC.serialize_weaken k' p.p_full_parser.pf_serializer;
  }
}

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_left #nz #wk #k p k'
  = parse_weaken p (glb k' k)

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_right #nz #wk #k p k'
  = parse_weaken p (glb k k')

/// Parser: unreachable, for default cases of exhaustive pattern matching
inline_for_extraction noextract
let parse_impos ()
  : parser impos_kind False
= mk_parser
  {
      pf_parser = LPC.fail_parser impos_kind False;
      pf_serializer = LPC.fail_serializer impos_kind False (fun _ -> ());
  }

let parse_ite e p1 p2
  = if e then p1 () else p2 ()

let nlist (n:U32.t) (t:Type) = list t

inline_for_extraction noextract
let parse_nlist1
        (n:U32.t)
        (#wk: _)
        (#k:parser_kind true wk)
        (#t:_)
        (p:LP.parser k t)
  : Tot (LP.parser _ (nlist n t))
  = LowParse.Spec.FLData.parse_fldata (LowParse.Spec.List.parse_list p) (U32.v n)

let parse_nlist_total_fixed_size_aux
  (n:U32.t)
  (#wk: _) (#k:parser_kind true wk) #t (p:LP.parser k t)
  (x: LP.bytes)
: Lemma
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.parser_kind_low == 0 /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    Seq.length x >= U32.v n
  ))
  (ensures (
    Some? (LP.parse (parse_nlist1 n p) x)
  ))
= let x' = Seq.slice x 0 (U32.v n) in
  let cnt = (U32.v n / k.LP.parser_kind_low) in
  FStar.Math.Lemmas.lemma_div_exact (U32.v n) k.LP.parser_kind_low;
  FStar.Math.Lemmas.nat_over_pos_is_nat (U32.v n) k.LP.parser_kind_low;
  LowParse.Spec.List.parse_list_total_constant_size p cnt x';
  LP.parser_kind_prop_equiv LowParse.Spec.List.parse_list_kind (LowParse.Spec.List.parse_list p)

inline_for_extraction noextract
let parse_nlist2
        (n:U32.t)
        (#k:parser_kind true WeakKindStrongPrefix)
        (#t:_)
        (#p:LP.parser k t)
        (s: LP.serializer p)
  = LowParse.Spec.FLData.parse_fldata_strong (LowParse.Spec.List.serialize_list _ s) (U32.v n)

inline_for_extraction noextract
let serialize_nlist2
        (n:U32.t)
        (#k:parser_kind true WeakKindStrongPrefix)
        (#t:_)
        (#p:LP.parser k t)
        (s: LP.serializer p)
: Tot (LP.serializer (parse_nlist2 n s))
= LowParse.Spec.FLData.serialize_fldata_strong (LowParse.Spec.List.serialize_list _ s) (U32.v n)

let parse_nlist_total_fixed_size_kind_correct2
  (n:U32.t) (n_is_const:option nat { memoizes_n_as_const n_is_const n })
        (#k:parser_kind true WeakKindStrongPrefix)
        (#t:_)
        (#p:LP.parser k t)
        (s: LP.serializer p)
: Lemma
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.parser_kind_low == 0 /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
    LP.parser_kind_prop (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist2 n s) /\
    (Some? n_is_const ==> kind_nlist k n_is_const == LP.total_constant_size_parser_kind (U32.v n))
  ))
= LP.parser_kind_prop_equiv (LowParse.Spec.FLData.parse_fldata_kind (U32.v n) LowParse.Spec.List.parse_list_kind) (parse_nlist2 n s);
  LP.parser_kind_prop_equiv (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist2 n s);
  Classical.forall_intro (Classical.move_requires (parse_nlist_total_fixed_size_aux n p))

inline_for_extraction noextract
let parse_nlist3
        (n:U32.t)
        (n_const:option nat { Some? n_const ==> Some?.v n_const == U32.v n })
        (#k:parser_kind true WeakKindStrongPrefix)
        (#t:_)
        (#p:LP.parser k t)
        (s: LP.serializer p)
  : Tot (LP.parser (kind_nlist k n_const) (LowParse.Spec.FLData.parse_fldata_strong_t (LowParse.Spec.List.serialize_list _ s) (U32.v n)))
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    let p' : bare_parser (LowParse.Spec.FLData.parse_fldata_strong_t (LowParse.Spec.List.serialize_list _ s) (U32.v n)) = parse_nlist2 n s in
    LP.parser_kind_prop_equiv (parse_fldata_kind (U32.v n) (parse_list_kind)) p';
    LP.parser_kind_prop_equiv (kind_nlist k n_const) p';
    Classical.move_requires (parse_nlist_total_fixed_size_kind_correct2 n n_const #k #t #p) s;
    p'

inline_for_extraction noextract
let serialize_nlist3
        (n:U32.t)
        (n_const:option nat { Some? n_const ==> Some?.v n_const == U32.v n })
        (#k:parser_kind true WeakKindStrongPrefix)
        (#t:_)
        (#p:LP.parser k t)
        (s: LP.serializer p)
  : Tot (LP.serializer (parse_nlist3 n n_const s))
= LP.serialize_ext _ (serialize_nlist2 n s) (parse_nlist3 n n_const s)

let parse_nlist_total_fixed_size_kind_correct3
  (n:U32.t) (n_is_const:option nat { memoizes_n_as_const n_is_const n })
  (#k:parser_kind true WeakKindStrongPrefix) #t (#p:LP.parser k t) (s: LP.serializer p)
: Lemma
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.parser_kind_low == 0 /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
    LP.parser_kind_prop (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist3 n n_is_const s) /\
    (Some? n_is_const ==> kind_nlist k n_is_const == LP.total_constant_size_parser_kind (U32.v n))
  ))
= parse_nlist_total_fixed_size_kind_correct2 n n_is_const s;
  LP.parser_kind_prop_equiv (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist2 n s);
  LP.parser_kind_prop_equiv (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist3 n n_is_const s);
  ()

let rec list_ghost_for_all
  (#t: Type)
  (f: t -> GTot bool)
  (l: list t)
: GTot bool
= match l with
  | [] -> true
  | a :: q -> if f a then list_ghost_for_all f q else false

let list_ghost_for_all'
  (#t: Type)
  (f: t -> GTot bool)
  (l: list t)
: GTot bool
= match l with
  | [] -> true
  | a :: q -> if f a then list_ghost_for_all f q else false

let list_ghost_for_all_unfold
  (#t: Type)
  (f: t -> GTot bool)
  (l: list t)
: Lemma
  (list_ghost_for_all f l == list_ghost_for_all' f l)
= assert_norm (list_ghost_for_all f l == list_ghost_for_all' f l)

let rec list_ghost_for_all_pull_refine
  (#t: Type)
  (f: t -> GTot bool)
  (l: list (LPC.parse_filter_refine f))
: GTot (LPC.parse_filter_refine (list_ghost_for_all f))
= match l with
  | [] -> list_ghost_for_all_unfold f []; []
  | a :: q ->
    let l' : list t = a :: list_ghost_for_all_pull_refine f q in
    list_ghost_for_all_unfold f l';
    l'

let list_ghost_for_all_pull_refine'
  (#t: Type)
  (f: t -> GTot bool)
  (l: list (LPC.parse_filter_refine f))
: GTot (list t)
= match l with
  | [] -> []
  | a :: q -> a :: list_ghost_for_all_pull_refine f q

let list_ghost_for_all_pull_refine_unfold
  (#t: Type)
  (f: t -> GTot bool)
  (l: list (LPC.parse_filter_refine f))
: Lemma
  (list_ghost_for_all_pull_refine f l == list_ghost_for_all_pull_refine' f l)
= assert_norm (list_ghost_for_all_pull_refine f l == list_ghost_for_all_pull_refine' f l)

let rec list_ghost_for_all_push_refine
  (#t: Type)
  (f: t -> GTot bool)
  (l: LPC.parse_filter_refine (list_ghost_for_all f))
: GTot (list (LPC.parse_filter_refine f))
= list_ghost_for_all_unfold f l;
  match l with
  | [] -> []
  | a :: q ->
    a :: list_ghost_for_all_push_refine f q

let list_ghost_for_all_push_refine'
  (#t: Type)
  (f: t -> GTot bool)
  (l: LPC.parse_filter_refine (list_ghost_for_all f))
: GTot (list (LPC.parse_filter_refine f))
= list_ghost_for_all_unfold f l;
  match l with
  | [] -> []
  | a :: q -> a :: list_ghost_for_all_push_refine f q

let list_ghost_for_all_push_refine_unfold
  (#t: Type)
  (f: t -> GTot bool)
  (l: LPC.parse_filter_refine (list_ghost_for_all f))
: Lemma
  (list_ghost_for_all_push_refine f l == list_ghost_for_all_push_refine' f l)
= assert_norm (list_ghost_for_all_push_refine f l == list_ghost_for_all_push_refine' f l)

let rec synth_inverse_list_ghost_for_all_pull_push_refine'
  (#t: Type)
  (f: t -> GTot bool)
  (l: LPC.parse_filter_refine (list_ghost_for_all f))
: Lemma
  (ensures (list_ghost_for_all_pull_refine f (list_ghost_for_all_push_refine f l) == l))
  (decreases l)
= list_ghost_for_all_pull_refine_unfold f (list_ghost_for_all_push_refine f l);
  list_ghost_for_all_push_refine_unfold f l;
  list_ghost_for_all_unfold f l;
  match l with
  | [] -> ()
  | a :: q -> synth_inverse_list_ghost_for_all_pull_push_refine' f q

let synth_inverse_list_ghost_for_all_pull_push_refine
  (#t: Type)
  (f: t -> GTot bool)
: Lemma
  (ensures (LPC.synth_inverse (list_ghost_for_all_pull_refine f) (list_ghost_for_all_push_refine f)))
  [SMTPat (list_ghost_for_all_pull_refine f)]
= LPC.synth_inverse_intro' (list_ghost_for_all_pull_refine f) (list_ghost_for_all_push_refine f) (synth_inverse_list_ghost_for_all_pull_push_refine' f)

let rec synth_inverse_list_ghost_for_all_push_pull_refine'
  (#t: Type)
  (f: t -> GTot bool)
  (l: list (LPC.parse_filter_refine f))
: Lemma
  (ensures (list_ghost_for_all_push_refine f (list_ghost_for_all_pull_refine f l) == l))
  (decreases l)
= list_ghost_for_all_push_refine_unfold f (list_ghost_for_all_pull_refine f l);
  list_ghost_for_all_pull_refine_unfold f l;
  list_ghost_for_all_unfold f (list_ghost_for_all_pull_refine f l);
  match l with
  | [] -> ()
  | a :: q -> synth_inverse_list_ghost_for_all_push_pull_refine' f q

let synth_inverse_list_ghost_for_all_push_pull_refine
  (#t: Type)
  (f: t -> GTot bool)
: Lemma
  (ensures (LPC.synth_inverse (list_ghost_for_all_push_refine f) (list_ghost_for_all_pull_refine f)))
  [SMTPat (list_ghost_for_all_pull_refine f)]
= LPC.synth_inverse_intro' (list_ghost_for_all_push_refine f) (list_ghost_for_all_pull_refine f) (synth_inverse_list_ghost_for_all_push_pull_refine' f)

let parse_nlist_serializable
    (n:U32.t)
    (#k:parser_kind true WeakKindStrongPrefix)
    (#t:_)
    (#f: (t -> GTot bool))
    (#p:LP.parser k (LPC.parse_filter_refine f))
    (s: LP.serializer p)
    (l: list t)
: GTot bool
= list_ghost_for_all f l &&
  Seq.length (LP.serialize (LowParse.Spec.List.serialize_list _ s) (list_ghost_for_all_push_refine f l)) = U32.v n

let parse_nlist_synth_intro
    (n:U32.t)
    (#k:parser_kind true WeakKindStrongPrefix)
    (#t:_)
    (#f: (t -> GTot bool))
    (#p:LP.parser k (LPC.parse_filter_refine f))
    (s: LP.serializer p)
    (l: LowParse.Spec.FLData.parse_fldata_strong_t (LowParse.Spec.List.serialize_list _ s) (U32.v n))
: GTot (LPC.parse_filter_refine (parse_nlist_serializable n s))
= synth_inverse_list_ghost_for_all_push_pull_refine f;
  list_ghost_for_all_pull_refine f l

let parse_nlist_synth_intro_injective
    (n:U32.t)
    (#k:parser_kind true WeakKindStrongPrefix)
    (#t:_)
    (#f: (t -> GTot bool))
    (#p:LP.parser k (LPC.parse_filter_refine f))
    (s: LP.serializer p)
: Lemma
  (ensures (LPC.synth_injective (parse_nlist_synth_intro n s)))
  [SMTPat (parse_nlist_synth_intro n s)]
= synth_inverse_list_ghost_for_all_pull_push_refine f;
  synth_inverse_list_ghost_for_all_push_pull_refine f

inline_for_extraction noextract
let parse_nlist4
        (n:U32.t)
        (n_const:option nat { Some? n_const ==> Some?.v n_const == U32.v n })
        (#k:parser_kind true WeakKindStrongPrefix)
        (#t:_)
        (#f: (t -> GTot bool))
        (#p:LP.parser k (LPC.parse_filter_refine f))
        (s: LP.serializer p)
  : Tot (LP.parser (kind_nlist k n_const) (LPC.parse_filter_refine (parse_nlist_serializable n s)))
= LPC.parse_synth
    (parse_nlist3 n n_const s)
    (parse_nlist_synth_intro n s)

let parse_nlist_synth_elim
    (n:U32.t)
    (#k:parser_kind true WeakKindStrongPrefix)
    (#t:_)
    (#f: (t -> GTot bool))
    (#p:LP.parser k (LPC.parse_filter_refine f))
    (s: LP.serializer p)
    (l: LPC.parse_filter_refine (parse_nlist_serializable n s))
: GTot (LowParse.Spec.FLData.parse_fldata_strong_t (LowParse.Spec.List.serialize_list _ s) (U32.v n))
= synth_inverse_list_ghost_for_all_push_pull_refine f;
  list_ghost_for_all_push_refine f l

let parse_nlist_synth_intro_inverse
    (n:U32.t)
    (#k:parser_kind true WeakKindStrongPrefix)
    (#t:_)
    (#f: (t -> GTot bool))
    (#p:LP.parser k (LPC.parse_filter_refine f))
    (s: LP.serializer p)
: Lemma
  (ensures (LPC.synth_inverse (parse_nlist_synth_intro n s) (parse_nlist_synth_elim n s)))
  [SMTPat (parse_nlist_synth_intro n s)]
= synth_inverse_list_ghost_for_all_pull_push_refine f;
  synth_inverse_list_ghost_for_all_push_pull_refine f

inline_for_extraction noextract
let serialize_nlist4
        (n:U32.t)
        (n_const:option nat { Some? n_const ==> Some?.v n_const == U32.v n })
        (#k:parser_kind true WeakKindStrongPrefix)
        (#t:_)
        (#f: (t -> GTot bool))
        (#p:LP.parser k (LPC.parse_filter_refine f))
        (s: LP.serializer p)
  : Tot (LP.serializer (parse_nlist4 n n_const s))
= LPC.serialize_synth
    (parse_nlist3 n n_const s)
    (parse_nlist_synth_intro n s)
    (serialize_nlist3 n n_const s)
    (parse_nlist_synth_elim n s)
    ()

inline_for_extraction noextract
let parse_nlist n n_is_const #k #t p
  = {
    p_serializable = parse_nlist_serializable n p.p_full_parser.pf_serializer;
    p_full_parser = {
      pf_parser = parse_nlist4 n n_is_const p.p_full_parser.pf_serializer;
      pf_serializer = serialize_nlist4 n n_is_const p.p_full_parser.pf_serializer;
    }
  }

let parse_nlist_total_fixed_size_kind_correct
  (n:U32.t) (n_is_const:option nat { memoizes_n_as_const n_is_const n })
  (#k:parser_kind true WeakKindStrongPrefix) #t (p:parser k t)
: Lemma
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.parser_kind_low == 0 /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
    LP.parser_kind_prop (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n n_is_const p).p_full_parser.pf_parser /\
    (Some? n_is_const ==> kind_nlist k n_is_const == LP.total_constant_size_parser_kind (U32.v n))
  ))
= let s = p.p_full_parser.pf_serializer in
  parse_nlist_total_fixed_size_kind_correct3 n n_is_const s;
  Classical.forall_intro (LPC.parse_synth_eq2 (parse_nlist3 n n_is_const s) (parse_nlist_synth_intro n s) ());
  LP.parser_kind_prop_equiv (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist3 n n_is_const s);
  let pl : LP.parser (LP.total_constant_size_parser_kind (U32.v n)) (LowParse.Spec.FLData.parse_fldata_strong_t (LowParse.Spec.List.serialize_list _ s) (U32.v n)) = (parse_nlist3 n n_is_const s <: LP.bare_parser _) in
  Classical.forall_intro (LPC.parse_synth_eq2 (parse_nlist3 n n_is_const s) (parse_nlist_synth_intro n s) ());
  Classical.forall_intro (LPC.parse_synth_eq2 pl (parse_nlist_synth_intro n s) ());
  LP.parser_kind_prop_ext (LP.total_constant_size_parser_kind (U32.v n)) (LPC.parse_synth pl (parse_nlist_synth_intro n s)) (parse_nlist n n_is_const p).p_full_parser.pf_parser;
  ()

let all_bytes = Seq.seq LP.byte
let parse_all_bytes' 
  : LP.bare_parser all_bytes 
  = fun input -> Some (input, (Seq.length input <: LP.consumed_length input))
let parse_all_bytes =
  LP.parser_kind_prop_equiv kind_all_bytes parse_all_bytes';
  parse_all_bytes'

////////////////////////////////////////////////////////////////////////////////
module B32 = FStar.Bytes
let t_at_most (n:U32.t) (t:Type) = t & all_bytes
inline_for_extraction noextract
let parse_t_at_most n #nz #wk #k #t p
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false 
            #WeakKindStrongPrefix
            (LowParse.Spec.FLData.parse_fldata 
                (LPC.nondep_then p parse_all_bytes)
                (U32.v n))
            #false
            kind_t_at_most

////////////////////////////////////////////////////////////////////////////////
let t_exact (n:U32.t) (t:Type) = t
inline_for_extraction noextract
let parse_t_exact n #nz #wk #k #t p
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false 
            #WeakKindStrongPrefix
            (LowParse.Spec.FLData.parse_fldata 
                p
                (U32.v n))
            #false
            kind_t_exact

////////////////////////////////////////////////////////////////////////////////
// Readers
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
let reader p = LPLC.leaf_reader p

inline_for_extraction noextract
let read_filter p32 f
    = LPLC.read_filter p32 f

let read_impos : reader (parse_impos()) = 
  fun #rrel #rel sl pos -> 
    let h = FStar.HyperStack.ST.get() in
    assert (LPLC.valid (parse_impos()) h sl pos);
    LowParse.Low.Base.Spec.valid_equiv (parse_impos()) h sl pos;
    false_elim ()
  
// ////////////////////////////////////////////////////////////////////////////////
// // Validators
// ////////////////////////////////////////////////////////////////////////////////
inline_for_extraction noextract
let validator #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator #k #t p

inline_for_extraction noextract
let validator_no_read #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator_no_read #k #t p

inline_for_extraction noextract
let validate_nlist_total_constant_size_mod_ok
    (n:U32.t)
    (n_is_const:option nat { memoizes_n_as_const n_is_const n })
    #wk (#k:parser_kind true wk) (#t: Type) (p:parser k t)
  : Pure (validator_no_read (parse_nlist n n_is_const p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296 /\
    U32.v n % k.LP.parser_kind_low == 0
  ))
  (ensures (fun _ -> True))
= 
      (fun #rrel #rel sl len pos ->
         let h = FStar.HyperStack.ST.get () in
         [@inline_let]
         let _ =
           parse_nlist_total_fixed_size_kind_correct n n_is_const p;
           LPL.valid_facts (parse_nlist n n_is_const p) h sl (LPL.uint64_to_uint32 pos);
           LPL.valid_facts (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n n_is_const p)) h sl (LPL.uint64_to_uint32 pos)
         in
         LPL.validate_total_constant_size_no_read (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n n_is_const p)) (FStar.Int.Cast.uint32_to_uint64 n) () sl len pos
      )

module LUT = LowParse.Spec.ListUpTo

inline_for_extraction
noextract
let cond_string_up_to
  (#t: eqtype)
  (terminator: t)
  (x: t)
: Tot bool
= x = terminator

let cstring
  (t: eqtype)
  (terminator: t)
: Tot Type0
= LUT.parse_list_up_to_t (cond_string_up_to terminator)

let parse_string
  #k #t p terminator
=
  LowParse.Spec.Base.parser_kind_prop_equiv k p;
  LP.weaken parse_string_kind (LUT.parse_list_up_to (cond_string_up_to terminator) p (fun _ _ _ -> ()))

inline_for_extraction noextract
let is_zero (x: FStar.UInt8.t) : Tot bool = x = 0uy

let all_zeros = list (LowParse.Spec.Combinators.parse_filter_refine is_zero)
let parse_all_zeros = LowParse.Spec.List.parse_list (LowParse.Spec.Combinators.parse_filter LowParse.Spec.Int.parse_u8 is_zero)


////////////////////////////////////////////////////////////////////////////////
// Base types
////////////////////////////////////////////////////////////////////////////////

/// UINT8
let parse____UINT8 = LowParse.Spec.Int.parse_u8
let read____UINT8 = LowParse.Low.Int.read_u8

/// UINT8BE
let parse____UINT8BE = LowParse.Spec.Int.parse_u8
let read____UINT8BE = LowParse.Low.Int.read_u8

/// UInt16BE
let parse____UINT16BE = LowParse.Spec.Int.parse_u16
let read____UINT16BE = LowParse.Low.Int.read_u16

/// UInt32BE
let parse____UINT32BE = LowParse.Spec.Int.parse_u32
let read____UINT32BE = LowParse.Low.Int.read_u32

/// UInt64BE
let parse____UINT64BE = LowParse.Spec.Int.parse_u64
let read____UINT64BE = LowParse.Low.Int.read_u64


/// UInt16
let parse____UINT16 = LowParse.Spec.BoundedInt.parse_u16_le
let read____UINT16 = LowParse.Low.BoundedInt.read_u16_le

/// UInt32
let parse____UINT32 = LowParse.Spec.BoundedInt.parse_u32_le
let read____UINT32 = LowParse.Low.BoundedInt.read_u32_le


/// UInt64
let parse____UINT64 = LowParse.Spec.Int.parse_u64_le
let read____UINT64 = LowParse.Low.Int.read_u64_le
  
let parse_unit = LPC.parse_empty

inline_for_extraction noextract
let read_unit
  : LPL.leaf_reader unit
  = LPLC.read_ret ()

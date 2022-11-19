module LowParse.SteelST.Fold.Gen
include LowParse.Spec.Fold

#set-options "--ide_id_info_off"

open Steel.ST.GenElim // for sndp
open LowParse.Spec.List // for parse_list_kind
open LowParse.Spec.VLGen

module AP = LowParse.SteelST.ArrayPtr
module LP = LowParse.Spec.Base
module SZ = LowParse.Steel.StdInt

open LowParse.SteelST.Validate
open LowParse.SteelST.Access

let pkind
  (ne pr: bool)
: Tot parser_kind
= {
  parser_kind_low = if ne then 1 else 0;
  parser_kind_high = None;
  parser_kind_subkind = Some (if pr then ParserConsumesAll else ParserStrong);
  parser_kind_metadata = None;
}

inline_for_extraction
[@@specialize]
noeq
type scalar_ops (t: Type) = {
  scalar_parser: parser (pkind true false) t;
  scalar_validator: validator scalar_parser;
  scalar_jumper: jumper scalar_parser;
  scalar_reader: leaf_reader scalar_parser;
}

inline_for_extraction
noeq
type low_level_state
  (state_i: Type) (state_t: state_i -> Type) (ll_state: Type) (ll_state_ptr: Type)
= {
    ll_state_match: ((#i: state_i) -> (h: state_t i) -> ll_state -> vprop);
    ll_state_failure: ((#i: state_i) -> (h: state_t i) -> vprop);
    state_ge: ((#i1: state_i) -> (s1: state_t i1) -> (#i2: state_i) -> (s2: state_t i2) -> prop);
    state_ge_refl: (
      (#i: state_i) -> (s: state_t i) ->
      Lemma
      (state_ge s s)
    );
    state_ge_trans: (
      (#i1: state_i) -> (s1: state_t i1) ->
      (#i2: state_i) -> (s2: state_t i2) ->
      (#i3: state_i) -> (s3: state_t i3) ->
      Lemma
      (requires (
        state_ge s1 s2 /\
        state_ge s2 s3
      ))
      (ensures (state_ge s1 s3))
    );
    ll_state_failure_inc: (
      (#opened: _) ->
      (#i1: state_i) -> (s1: state_t i1) ->
      (#i2: state_i) -> (s2: state_t i2) ->
      STGhost unit opened
        (ll_state_failure s1)
        (fun _ -> ll_state_failure s2)
        (state_ge s2 s1)
        (fun _ -> True)
    );
    ll_state_shape: (state_i -> ll_state -> prop);
    ll_state_match_shape: (
      (#opened: _) ->
      (#i: state_i) ->
      (h: state_t i) ->
      (l: ll_state) ->
      STGhost unit opened
        (ll_state_match h l)
        (fun _ -> ll_state_match h l)
        True
        (fun _ -> ll_state_shape i l)
    );
    ll_state_pts_to: (ll_state_ptr -> ll_state -> vprop);
  }

inline_for_extraction
let with_ll_state_ptr_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (i: state_i)
: Tot Type
=
  (l: ll_state) ->
  (#kpre: vprop) ->
  (#t: Type) ->
  (#kpost: (t -> vprop)) ->
  (k: (
    (p: ll_state_ptr) ->
    STT t
      (kpre `star` cl.ll_state_pts_to p l)
      (fun r -> kpost r `star` exists_ (cl.ll_state_pts_to p))
  )) ->
  STF t kpre kpost (cl.ll_state_shape i l) (fun _ -> True)

inline_for_extraction
let load_ll_state_ptr_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (i: state_i)
: Tot Type
=
  (#gl: Ghost.erased ll_state) ->
  (p: ll_state_ptr) ->
  (#kpre: vprop) ->
  (#t: Type) ->
  (#kpost: (t -> vprop)) ->
  (k: (
    (l: ll_state) ->
    ST t
       (kpre `star` cl.ll_state_pts_to p l)
       kpost
       (l == Ghost.reveal gl)
       (fun _ -> True)
  )) ->
  STF t
    (kpre `star` cl.ll_state_pts_to p gl)
    kpost
    (cl.ll_state_shape i gl)
    (fun _ -> True)

inline_for_extraction
let store_ll_state_ptr_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (i: state_i)
: Tot Type
= (#gl: Ghost.erased ll_state) ->
  (p: ll_state_ptr) ->
  (l': ll_state) ->
  ST unit
     (cl.ll_state_pts_to p gl)
     (fun _ -> cl.ll_state_pts_to p l')
     (cl.ll_state_shape i gl /\ cl.ll_state_shape i l')
     (fun _ -> True)

inline_for_extraction
[@@noextract_to "krml"]
let stt_impl_t'
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
  (kpre: vprop)
  (kpost: vprop)
: Tot Type
= (bout: ll_state) ->
  (h: Ghost.erased (state_t pre)) ->
  (k_success: (
    (bout': ll_state) ->
    (h': Ghost.erased (state_t post)) ->
    (v: ret_t) ->
    ST unit
      (kpre `star`
        cl.ll_state_match h' bout')
      (fun _ -> kpost)
      (
        p h == (v, Ghost.reveal h')
      )
      (fun _ -> True)
  )) ->
  (k_failure: (
    (h': Ghost.erased (state_t post)) ->
    (v: Ghost.erased ret_t) ->
    ST unit
      (kpre `star` cl.ll_state_failure h')
      (fun _ -> kpost)
      (
        p h == (Ghost.reveal v, Ghost.reveal h')
      )
      (fun _ -> True)
  )) ->
  STT unit
    (kpre `star`
      cl.ll_state_match h bout)
    (fun _ -> kpost)

inline_for_extraction
[@@noextract_to "krml"]
let stt_impl_t
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
: Tot Type
=
  (kpre: vprop) ->
  (kpost: vprop) ->
  stt_impl_t' cl p kpre kpost

inline_for_extraction
let size_of
  (ar: AP.array byte)
: Tot Type
= (s: SZ.size_t { SZ.size_v s == AP.length ar })

inline_for_extraction
[@@noextract_to "krml"]
let fold_impl_t
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ty: Type)
  (#kty: parser_kind)
  (pty: parser kty ty)
  (with_size: bool)
  (p: fold_t state_t ty ret_t pre post)
: Tot Type
=
  (kpre: vprop) ->
  (kpost: vprop) ->
  (#vbin: v kty ty) ->
  (bin: byte_array) ->
  (bin_sz: (if with_size then size_of (array_of' vbin) else unit)) ->
  stt_impl_t' cl (p vbin.contents)
    (kpre `star` aparse pty bin vbin)
    kpost

inline_for_extraction
val impl_action
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: Ghost.erased (stt state_t ret_t pre post))
  (pi: stt_impl_t cl p)
  (#ty: Type)
  (#kty: parser_kind)
  (pty: parser kty ty)
  (with_size: bool)
: Tot (fold_impl_t cl pty with_size (action_fold p))

inline_for_extraction
[@@noextract_to "krml"]
val impl_ret
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (i: state_i)
  (v: ret_t)
: Tot (stt_impl_t cl (ret #state_i #state_t #i v))

inline_for_extraction
val impl_rewrite_parser
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ty: Type)
  (p: Ghost.erased (fold_t state_t ty ret_t pre post))
  (#kty: Ghost.erased parser_kind)
  (#pty: parser kty ty)
  (#with_size: bool)
  (pi: fold_impl_t cl pty with_size p)
  (#kty': Ghost.erased parser_kind)
  (pty': parser kty' ty)
: Pure (fold_impl_t cl pty' with_size p)
    (requires (forall x . parse pty' x == parse pty x))
    (ensures (fun _ -> True))

inline_for_extraction
[@@noextract_to "krml"]
val impl_read
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (i: state_i)
  (#ty: Type)
  (#kty: Ghost.erased parser_kind)
  (#pty: parser kty ty)
  (rty: leaf_reader pty)
  (with_size: bool)
: Tot (fold_impl_t cl pty with_size (fold_read #state_i #state_t #i #ty ()))

let stt_state_inc
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
: Tot Type
= (s: state_t pre) ->
  Lemma
  (snd (p s) `cl.state_ge` s)

let fold_state_inc
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ty: Type)
  (p: fold_t state_t ty ret_t pre post)
: Tot Type
= (i: ty) ->
  stt_state_inc cl (p i)

let get_return_state
  #state_i #state_t
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
  (s: state_t pre)
: Pure (Ghost.erased (state_t post))
    (requires True)
    (ensures (fun y -> Ghost.reveal y == sndp (p s)))
= sndp (p s)

let get_return_value
  #state_i #state_t
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
  (s: state_t pre)
: Pure (Ghost.erased ret_t)
    (requires True)
    (ensures (fun y -> Ghost.reveal y == fstp (p s)))
= fstp (p s)

[@@noextract_to "krml"]
inline_for_extraction
val impl_bind
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ty: Type)
  (#kty: Ghost.erased parser_kind)
  (pty: parser kty ty)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (#ret2: _)
  (#post2: _)
  (f: Ghost.erased (fold_t state_t ty ret1 pre1 post1))
  (with_size: bool)
  (impl_f: fold_impl_t cl pty with_size f)
  (g: Ghost.erased ((x: ret1) -> fold_t state_t ty ret2 post1 post2))
  (impl_g: ((x: ret1) -> fold_impl_t cl pty with_size (Ghost.reveal g x)))
  (g_prf: ((x: ret1) -> fold_state_inc cl (Ghost.reveal g x)))
: Tot (fold_impl_t cl pty with_size (bind_fold f g))

let ifthenelse
  (#t: Type)
  (b: bool)
  (vtrue: (squash (b == true) -> t))
  (vfalse: (squash (b == false) -> t))
: Tot t
= if b then vtrue () else vfalse ()

let ifthenelse_dep
  (b: bool)
  (ttrue: (squash (b == true) -> Type))
  (tfalse: (squash (b == false) -> Type))
  (pi: (Type -> Type))
  (ptrue: (squash (b == true) -> pi (ttrue ())))
  (pfalse: (squash (b == false) -> pi (tfalse ())))
: Tot (pi (ifthenelse b ttrue tfalse))
= if b then ptrue () else pfalse ()

inline_for_extraction
[@@noextract_to "krml"]
val impl_if_gen
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret: Type)
  (#pre: _)
  (#post: _)
  (x: bool)
  (t1: (squash (x == true) -> Type))
  (f1: Ghost.erased (squash (x == true) -> fold_t state_t (t1 ()) ret pre post))
  (#k: Ghost.erased parser_kind)
  (p1: (squash (x == true) -> parser k (t1 ())))
  (with_size: bool)
  (impl_f1: squash (x == true) -> fold_impl_t cl (p1 ()) with_size (Ghost.reveal f1 ()))
  (t2: (squash (x == false) -> Type))
  (f2: Ghost.erased (squash (x == false) -> fold_t state_t (t2 ()) ret pre post))
  (p2: (squash (x == false) -> parser k (t2 ())))
  (impl_f2: squash (x == false) -> fold_impl_t cl (p2 ()) with_size (Ghost.reveal f2 ()))
: Tot (fold_impl_t cl #ret #pre #post #(ifthenelse x t1 t2) #k (ifthenelse_dep x t1 t2 (parser k) p1 p2) with_size (ifthenelse_dep x t1 t2 (fun t -> fold_t state_t t ret pre post) (Ghost.reveal f1) (Ghost.reveal f2)))

inline_for_extraction
[@@noextract_to "krml"]
val impl_if
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#t: Type)
  (#ret: Type)
  (#pre: _)
  (#post: _)
  (x: bool)
  (f1: Ghost.erased (squash (x == true) -> fold_t state_t t ret pre post))
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (with_size: bool)
  (impl_f1: squash (x == true) -> fold_impl_t cl p with_size (Ghost.reveal f1 ()))
  (f2: Ghost.erased (squash (x == false) -> fold_t state_t t ret pre post))
  (impl_f2: squash (x == false) -> fold_impl_t cl p with_size (Ghost.reveal f2 ()))
: Tot (fold_impl_t cl p with_size (if x then Ghost.reveal f1 () else Ghost.reveal f2 ()))

inline_for_extraction
[@@noextract_to "krml"]
val impl_pair
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#t1: Type0)
  (#t2: Type0)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (f1: Ghost.erased (fold_t state_t t1 ret1 pre1 post1))
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1)
  (impl_f1: fold_impl_t cl p1 false f1)
  (j1: jumper p1) // MUST be computed OUTSIDE of impl_pair
  (#ret2: _)
  (#post2: _)
  (f2: Ghost.erased ((x: ret1) -> fold_t state_t t2 ret2 post1 post2))
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t2)
  (with_size: bool)
  (impl_f2: ((x: ret1) -> fold_impl_t cl p2 with_size (Ghost.reveal f2 x)))
  (f2_prf: ((x: ret1) -> fold_state_inc cl (Ghost.reveal f2 x))) 
: Pure (fold_impl_t cl (p1 `nondep_then` p2) with_size (fold_pair f1 f2))
    (requires (k1.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))

let parser_of_choice_payload
  (#kt: Type)
  (#k: parser_kind)
  (t: (kt -> Type))
  (f: (x: kt) -> parser k (t x))
  (x: kt)
: Tot (parser k (t x))
= f x

inline_for_extraction
[@@noextract_to "krml"]
val impl_choice
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#kt: Type0)
  (#t: (kt -> Type0))
  (#ret_t: Type0)
  (#pre: _)
  (#post: _)
  (f: Ghost.erased ((x: kt) -> fold_t state_t (t x) ret_t pre post))
  (#ktk: Ghost.erased parser_kind)
  (#ktp: parser ktk kt)
  (j: jumper ktp)
  (r: leaf_reader ktp)
  (#k: parser_kind)
  (p: (x: kt) -> parser k (t x))
  (with_size: bool)
  (impl_f: (x: kt) -> fold_impl_t cl (p x) with_size (Ghost.reveal f x))
: Pure (fold_impl_t cl (parse_dtuple2 ktp p) with_size (fold_choice f))
    (requires (ktk.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))

(* for loop *)

#set-options "--print_universes"

inline_for_extraction
val impl_for
  (#state_i: Type)
  (#state_t: (_ -> Type0))
  (#ll_state: Type0)
  (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (from: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (prf: (x: nat { SZ.size_v from <= x /\ x < SZ.size_v to }) -> fold_state_inc cl (Ghost.reveal f x))
  (fi: (x: SZ.size_t { SZ.size_v from <= SZ.size_v x /\ SZ.size_v x < SZ.size_v to }) -> fold_impl_t cl p false (Ghost.reveal f (SZ.size_v x)))
  (with_size: bool)
  (wc: with_ll_state_ptr_t u#_ u#_ u#_ u#_ u#0 cl inv) // same
  (wl: (load_ll_state_ptr_t u#_ u#_ u#_ u#_ u#0 cl inv))
  (ws: store_ll_state_ptr_t cl inv)
: Tot (fold_impl_t cl p with_size (fold_for inv (SZ.size_v from) (SZ.size_v to) f))

[@@__reduce__]
let parse_nlist0
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_filter_kind parse_list_kind) (nlist n t))
= parse_list p `parse_filter` (fun l -> List.Tot.length l = n) `parse_synth` (fun x -> (x <: (nlist n t)))

let parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_filter_kind parse_list_kind) (nlist n t))
= parse_nlist0 n p

val intro_nlist
  (#opened: _)
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (#vb: v parse_list_kind (list t))
  (b: byte_array)
: STGhost (v (parse_filter_kind parse_list_kind) (nlist n t)) opened
    (aparse (parse_list p) b vb)
    (fun vb' -> aparse (parse_nlist n p) b vb')
    (List.Tot.length vb.contents == n)
    (fun vb' ->
      array_of' vb' == array_of' vb /\
      (vb'.contents <: list t) == vb.contents
    )

val elim_nlist
  (#opened: _)
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (#vb: v (parse_filter_kind parse_list_kind) (nlist n t))
  (b: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_nlist n p) b vb)
    (fun vb' -> aparse (parse_list p) b vb')
    True
    (fun vb' ->
      array_of' vb' == array_of' vb /\
      (vb.contents <: list t) == vb'.contents
    )

let size_v_injective : squash (synth_injective SZ.size_v) = ()

let parse_size_prefixed
  (#st: Type)
  (#sk: parser_kind)
  (sp: parser sk st)
  (sz: (st -> SZ.size_t) { synth_injective sz })
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (sk `and_then_kind` parse_vlgen_alt_payload_kind) t)
= parse_vlgen_alt
    ((sp `parse_synth` sz) `parse_synth` (SZ.size_v))
    p

inline_for_extraction
val validate_size_prefixed
  (#st: Type)
  (#sk: Ghost.erased parser_kind)
  (#sp: parser sk st)
  (sv: validator sp)
  (sr: leaf_reader sp)
  (sz: (st -> SZ.size_t) { synth_injective sz })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: ((s: SZ.size_t) -> validator (parse_fldata p (SZ.size_v s))))
: Pure (validator (parse_size_prefixed sp sz p)) 
    (requires (sk.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))

inline_for_extraction
val jump_size_prefixed
  (#st: Type)
  (#sk: Ghost.erased parser_kind)
  (#sp: parser sk st)
  (sv: jumper sp)
  (sr: leaf_reader sp)
  (sz: (st -> SZ.size_t) { synth_injective sz })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
: Pure (jumper (parse_size_prefixed sp sz p)) 
    (requires (sk.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))

val intro_parse_size_prefixed
  (#opened: _)
  (#st: Type)
  (#sk: Ghost.erased parser_kind)
  (sp: parser sk st)
  (sz: (st -> SZ.size_t) { synth_injective sz })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
  (#vbs: v _ _)
  (bs: byte_array)
  (#vb: v _ _)
  (b: byte_array)
: STGhost (v _ _) opened
    (aparse (parse_synth sp sz) bs vbs `star`
      aparse p b vb)
    (fun vbs' -> aparse (parse_size_prefixed sp sz p) bs vbs')
    (sk.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of' vbs) (array_of' vb) /\
      SZ.size_v vbs.contents == AP.length (array_of' vb))
    (fun vbs' ->
      AP.merge_into (array_of' vbs) (array_of' vb) (array_of' vbs') /\
      vbs'.contents == vb.contents
    )

val elim_parse_size_prefixed
  (#opened: _)
  (#st: Type)
  (#sk: Ghost.erased parser_kind)
  (sp: parser sk st)
  (sz: (st -> SZ.size_t) { synth_injective sz })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
  (#vb: v _ _)
  (b: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse (parse_size_prefixed sp sz p) b vb)
    (fun bl -> exists_ (fun (vb': v _ _) -> exists_ (fun (vbl: v _ _) ->
      aparse (parse_synth sp sz) b vb' `star`
      aparse p bl vbl `star` pure (
      AP.merge_into (array_of' vb') (array_of' vbl) (array_of' vb) /\
      SZ.size_v vb'.contents == AP.length (array_of' vbl) /\
      vbl.contents == vb.contents
    ))))
    (sk.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)

inline_for_extraction
val impl_size_prefixed
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#st: Type)
  (#sk: Ghost.erased parser_kind)
  (#sp: parser sk st)
  (sj: jumper sp)
  (sr: leaf_reader sp)
  (sz: (st -> SZ.size_t) { synth_injective sz })
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#ret_t: _) (#pre: _) (#post: _)
  (f: Ghost.erased (fold_t state_t t ret_t pre post))
  (body_with_size: bool)
  (fi: fold_impl_t cl p body_with_size f)
  (with_size: bool)
: Pure (fold_impl_t cl (parse_size_prefixed sp sz p) with_size (Ghost.reveal f))
    (requires (sk.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))

inline_for_extraction
val impl_list_index
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (jp: jumper p)
  (n: SZ.size_t)
  (idx: (i: SZ.size_t { SZ.size_v i < SZ.size_v n }))
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (fi: fold_impl_t cl p false f)
  (with_size: bool)
: Pure (fold_impl_t cl (parse_nlist (SZ.size_v n) p) with_size (fold_list_index inv (SZ.size_v n) (SZ.size_v idx) f))
    (requires  k.parser_kind_subkind == Some ParserStrong)
    (ensures (fun _ -> True))

inline_for_extraction
val impl_list_index_of
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (jp: jumper p)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (fi: fold_impl_t cl p false f)
  (with_size: bool)
  (n: SZ.size_t)
  (idx: Ghost.erased ((i: nat { i < SZ.size_v n }) -> Tot (i: nat { i < SZ.size_v n })))
  (idx' : (i: SZ.size_t) -> Pure SZ.size_t (requires SZ.size_v i < SZ.size_v n) (ensures fun j -> SZ.size_v j == Ghost.reveal idx (SZ.size_v i)))
  (j: SZ.size_t {SZ.size_v j < SZ.size_v n})
: Pure (fold_impl_t cl (parse_nlist (SZ.size_v n) p) with_size (fold_list_index_of inv f (SZ.size_v n) idx (SZ.size_v j)))
    (requires  k.parser_kind_subkind == Some ParserStrong)
    (ensures (fun _ -> True))

inline_for_extraction
val impl_for_list
  (#state_i: Type)
  (#state_t: (_ -> Type0))
  (#ll_state: Type0)
  (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type0)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (#k: parser_kind)
  (#p: parser k t)
  (j: jumper p)
  (fi: fold_impl_t cl p false f)
  (prf: fold_state_inc cl f)
  (idx: array_index_fn)
  (wc: with_ll_state_ptr_t u#_ u#_ u#_ u#_ u#0 cl inv) // same
  (wl: (load_ll_state_ptr_t u#_ u#_ u#_ u#_ u#0 cl inv))
  (ws: store_ll_state_ptr_t cl inv)
: Pure (fold_impl_t cl (parse_list p) true (fold_for_list inv f idx.array_index_f_nat))
    (requires (
      k.parser_kind_subkind == Some ParserStrong
    ))
    (ensures (fun _ -> True))

(* list fold *)

val fold_list_append
  (#state_i: _)
  (#state_t: _)
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv (inv))
  (state: state_t inv)
  (l1 l2: list t)
: Lemma
  (ensures (fold_list inv f (l1 `List.Tot.append` l2) state ==
    (let (_, state1) = fold_list inv f l1 state in
    fold_list inv f l2 state1)))
  (decreases l1)

val fold_list_snoc
  (#state_i: _)
  (#state_t: _)
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv (inv))
  (state: state_t inv)
  (l: list t)
  (x: t)
: Lemma
  (ensures (fold_list inv f (List.Tot.snoc (l, x)) state ==
    (let (_, state1) = fold_list inv f l state in
    f x state1)))

inline_for_extraction
val impl_list
  (#state_i: Type)
  (#state_t: (_ -> Type0))
  (#ll_state: Type0)
  (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type0)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (prf: fold_state_inc cl f)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (impl_f: fold_impl_t cl p false f)
  (j: jumper p) // MUST be computed OUTSIDE of impl_list
  (wc: with_ll_state_ptr_t u#_ u#_ u#_ u#_ u#0 cl inv) // same
  (wl: (load_ll_state_ptr_t u#_ u#_ u#_ u#_ u#0 cl inv))
  (ws: store_ll_state_ptr_t cl inv)
: Pure (fold_impl_t cl (parse_list p) true (fold_list inv f))
    (requires (
      k.parser_kind_subkind == Some ParserStrong
    ))
    (ensures (fun _ -> True))

(* Implementing programs *)

[@@specialize]
noeq
type action_impl
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (action_t: (t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
  (action_sem: ((#t: Type) -> (#pre: _) -> (#post: _) -> action_t t pre post -> stt state_t t pre post))
= {
    a_inc: (
      (#t: Type) ->
      (#pre: state_i) ->
      (#post: state_i) ->
      (a: action_t t pre post) ->
      stt_state_inc cl (action_sem a)
    );
    a_impl: (
      (#t: Type) ->
      (#pre: state_i) ->
      (#post: state_i) ->
      (a: action_t t pre post) ->
      stt_impl_t cl (action_sem a)
    );
  }

[@@specialize]
noeq
type ll_state_ptr_ops
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
= {
    with_ll_state_ptr: (
      (inv: state_i) ->
      with_ll_state_ptr_t cl inv
    );
    load_ll_state_ptr: (
      (inv: state_i) ->
      load_ll_state_ptr_t cl inv
    );
    store_ll_state_ptr: (
      (inv: state_i) ->
      store_ll_state_ptr_t cl inv
    );
  }

val fold_list_inc
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (prf: fold_state_inc cl f)
: Tot (fold_state_inc cl (fold_list inv f))

val fold_for_list_inc
  (#state_i: _)
  (#state_t: _)
  (#ll_state: _)
  (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (prf: fold_state_inc cl f)
  (idx: ((n: nat) -> (x: nat {x < n}) -> (y: nat {y < n})))
: Tot (fold_state_inc cl (fold_for_list inv f idx))

val prog_inc
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#action_t: (t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
  (#action_sem: ((#t: Type) -> (#pre: _) -> (#post: _) -> action_t t pre post -> stt state_t t pre post))
  (a_cl: action_impl cl action_t action_sem)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ne #pr: bool)
  (#ty: typ type_of_scalar ne pr)
  (p: prog type_of_scalar state_t action_t ty ret_t pre post)
: Tot (fold_state_inc cl (sem action_sem p))

let rec parser_of_typ
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#ne #pr: bool)
  (t: typ type_of_scalar ne pr)
: Tot (parser (pkind ne pr) (type_of_typ t))
  (decreases t)
= match t returns parser (pkind ne pr) (type_of_typ t) with
  | TScalar s -> (p_of_s s).scalar_parser
  | TPair t1 t2 -> weaken _ (nondep_then (parser_of_typ p_of_s t1) (parser_of_typ p_of_s t2))
  | TIf b ttrue tfalse -> parser_of_typ p_of_s (if b then ttrue () else tfalse ())
  | TList t' -> parse_list (parser_of_typ p_of_s t')
  | TChoice s f -> weaken _ (parse_dtuple2 (p_of_s s).scalar_parser #_ #(type_of_payload' s f) (fun x -> parser_of_typ p_of_s (f x)))
  | TUnit -> weaken _ parse_empty
  | TFalse ne pr -> fail_parser (pkind ne pr) (squash False)
  | TSizePrefixed sc sz t -> weaken _ (parse_size_prefixed (p_of_s sc).scalar_parser sz (parser_of_typ p_of_s t))

inline_for_extraction
val validate_ifthenelse
  (#k: parser_kind)
  (x: bool)
  (ttrue: (squash (x == true) -> Type))
  (tfalse: (squash (x == false) -> Type))
  (ptrue: (squash (x == true) -> parser k (ttrue ())))
  (pfalse: (squash (x == false) -> parser k (tfalse ())))
  (jtrue: (squash (x == true) -> validator (ptrue ())))
  (jfalse: (squash (x == false) -> validator (pfalse ())))
: Tot (validator #k #(ifthenelse x ttrue tfalse) (ifthenelse_dep x ttrue tfalse (parser k) ptrue pfalse))

inline_for_extraction
val validate_TPair
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#ne1 #ne2 #pr2: bool)
  (t1: typ type_of_scalar ne1 false)
  (v1: validator (parser_of_typ p_of_s t1))
  (t2: typ type_of_scalar ne2 pr2)
  (v2: validator (parser_of_typ p_of_s t2))
: Tot (validator (parser_of_typ p_of_s (TPair t1 t2)))

inline_for_extraction
val validate_TChoice
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (s: scalar_t)
  (#ne: bool)
  (#pr: bool)
  (body: (type_of_scalar s -> typ type_of_scalar ne pr))
  (body_v: ((k: type_of_scalar s) -> validator (parser_of_typ p_of_s (body k))))
: Tot (validator (parser_of_typ p_of_s (TChoice s body)))

inline_for_extraction
val validate_TSizePrefixed
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (s: scalar_t)
  (sz: (type_of_scalar s -> SZ.size_t) {synth_injective sz})
  (#ne: bool)
  (#pr: bool)
  (t: typ type_of_scalar ne pr)
  (v: validator (parser_of_typ p_of_s t))
: Tot (validator (parser_of_typ p_of_s (TSizePrefixed s sz t)))

inline_for_extraction
val validate_TIf
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#ne: bool)
  (#pr: bool)
  (b: bool)
  (ttrue: (squash (b == true) -> typ type_of_scalar ne pr))
  (vtrue: ((sq: squash (b == true)) -> validator (parser_of_typ p_of_s (ttrue ()))))
  (tfalse: (squash (b == false) -> typ type_of_scalar ne pr))
  (vfalse: ((sq: squash (b == false)) -> validator (parser_of_typ p_of_s (tfalse ()))))
: Tot (validator (parser_of_typ p_of_s (TIf b ttrue tfalse)))

inline_for_extraction
noextract
val validate_TList
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#t: typ type_of_scalar true false)
  (v: validator (parser_of_typ p_of_s t))
: Tot (validator (parser_of_typ p_of_s (TList t)))

inline_for_extraction
noextract
val validate_TUnit
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
: Tot (validator (parser_of_typ p_of_s TUnit))

inline_for_extraction
noextract
val validate_TFalse
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (ne pr: bool)
: Tot (validator (parser_of_typ p_of_s (TFalse ne pr)))

[@@specialize]
let rec validator_of_typ
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#ne #pr: bool)
  (t: typ type_of_scalar ne pr)
: Tot (validator (parser_of_typ p_of_s t))
  (decreases t)
=
  match t returns validator (parser_of_typ p_of_s t) with
  | TScalar s -> coerce _ ((p_of_s s).scalar_validator)
  | TPair t1 t2 -> coerce _ (validate_TPair p_of_s t1 (validator_of_typ p_of_s t1) t2 (validator_of_typ p_of_s t2))
  | TList t' -> coerce _ (validate_TList p_of_s (validator_of_typ p_of_s t'))
  | TIf b ttrue tfalse ->
    coerce _ (validate_TIf p_of_s b ttrue (fun _ -> validator_of_typ p_of_s (ttrue ())) tfalse (fun _ -> validator_of_typ p_of_s (tfalse ())))
  | TChoice s f ->
    coerce _ (validate_TChoice p_of_s s f (fun x -> (validator_of_typ p_of_s (f x))))
  | TSizePrefixed s sz #_ #pr' t' ->
    coerce _ (validate_TSizePrefixed p_of_s s sz t' (validator_of_typ p_of_s t'))
  | TUnit -> coerce _ (validate_TUnit p_of_s)
  | TFalse _ _ -> validate_TFalse p_of_s _ _

inline_for_extraction
val jump_ifthenelse
  (#k: parser_kind)
  (x: bool)
  (ttrue: (squash (x == true) -> Type))
  (tfalse: (squash (x == false) -> Type))
  (ptrue: (squash (x == true) -> parser k (ttrue ())))
  (pfalse: (squash (x == false) -> parser k (tfalse ())))
  (jtrue: (squash (x == true) -> jumper (ptrue ())))
  (jfalse: (squash (x == false) -> jumper (pfalse ())))
: Tot (jumper #k #(ifthenelse x ttrue tfalse) (ifthenelse_dep x ttrue tfalse (parser k) ptrue pfalse))

open LowParse.SteelST.Combinators

[@@specialize]
let rec jumper_of_typ
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#ne: bool)
  (t: typ type_of_scalar ne false)
: Tot (jumper (parser_of_typ p_of_s t))
  (decreases t)
=
  match t returns jumper (parser_of_typ p_of_s t) with
  | TScalar s -> (p_of_s s).scalar_jumper
  | TPair t1 t2 -> jump_weaken (pkind ne false) (jump_pair (jumper_of_typ p_of_s t1) (jumper_of_typ p_of_s t2)) ()
  | TSizePrefixed s sz t' -> jump_size_prefixed (p_of_s s).scalar_jumper (p_of_s s).scalar_reader sz (parser_of_typ p_of_s t')
  | TIf b ttrue tfalse ->
    jump_ifthenelse
      b
      (fun _ -> type_of_typ (ttrue ()))
      (fun _ -> type_of_typ (tfalse ()))
      (fun _ -> parser_of_typ p_of_s (ttrue ()))
      (fun _ -> parser_of_typ p_of_s (tfalse ()))
      (fun _ -> jumper_of_typ p_of_s (ttrue ()))
      (fun _ -> jumper_of_typ p_of_s (tfalse ()))
  | TChoice s f ->
    coerce _
      (jump_weaken (pkind ne false)
        (jump_dtuple2
          (p_of_s s).scalar_jumper
          (p_of_s s).scalar_reader
          _
          (fun x -> jumper_of_typ p_of_s (f x))
        )
        ()
      )
  | TUnit -> jump_constant_size parse_empty SZ.zero_size
  | TFalse ne pr -> jump_fail _ _ ()

[@@specialize]
let rec impl
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#action_t: (t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
  (#action_sem: ((#t: Type) -> (#pre: _) -> (#post: _) -> action_t t pre post -> stt state_t t pre post))
  (a_cl: action_impl cl action_t action_sem)
  (ptr_cl: ll_state_ptr_ops cl)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ne: bool)
  (#pr: bool)
  (#ty: typ type_of_scalar ne pr)
  (p: prog type_of_scalar state_t action_t ty ret_t pre post)
: Tot (fold_impl_t cl #ret_t #pre #post #(type_of_typ ty) #(pkind ne pr) (parser_of_typ p_of_s ty) pr (sem action_sem p))
  (decreases p)
= match p with
  | PRet #_ #_ #_ #_ #_ #_ #i v ->
      coerce _ (impl_action cl (ret v) (impl_ret cl i v) (parser_of_typ p_of_s ty) pr)
  | PAction a ->
      coerce _ (impl_action cl _ (a_cl.a_impl a) (parser_of_typ p_of_s ty) pr)
  | PBind f g ->
      coerce _ (impl_bind cl (parser_of_typ p_of_s ty) (sem action_sem f) pr (coerce _ (impl p_of_s a_cl ptr_cl f)) (fun x -> sem action_sem (g x)) (fun x -> coerce _ (impl p_of_s a_cl ptr_cl (g x))) (fun x -> prog_inc a_cl (g x)) <: fold_impl_t cl (parser_of_typ p_of_s ty) pr (sem action_sem (PBind f g)))
  | PIfP x ptrue pfalse ->
      coerce _
        (impl_if
          cl x
          (fun _ -> sem action_sem (ptrue ()))
          (parser_of_typ p_of_s ty)
          pr
          (fun _ -> coerce _ (impl p_of_s a_cl ptr_cl (ptrue ()))) (fun _ -> sem action_sem (pfalse ()))
          (fun _ -> coerce _ (impl p_of_s a_cl ptr_cl (pfalse ())))
        )
  | PIfT x #_ #_ #ttrue ptrue #tfalse pfalse ->
      coerce _
        (impl_if_gen
          cl x
          (fun _ -> type_of_typ (ttrue ()))
          (fun _ -> sem action_sem (ptrue ()))
          (fun _ -> parser_of_typ p_of_s (ttrue ()))
          pr
          (fun _ -> impl p_of_s a_cl ptr_cl (ptrue ()))
          (fun _ -> type_of_typ (tfalse ()))
          (fun _ -> sem action_sem (pfalse ()))
          (fun _ -> parser_of_typ p_of_s (tfalse ()))
          (fun _ -> impl p_of_s a_cl ptr_cl (pfalse ()))
        )
  | PScalar i s ->
      coerce _ (impl_read cl i (p_of_s s).scalar_reader pr)
  | PPair #_ #_ #_ #_ #_ #_ #t1 #_ #_ #t2 f1 f2 ->
      assert_norm (sem action_sem (PPair f1 f2) == fold_pair (sem action_sem f1) (fun x -> sem action_sem (f2 x)));
      coerce _
        (impl_rewrite_parser
          cl
          (fold_pair (sem action_sem f1) (fun x -> sem action_sem (f2 x)))
          #_ #_ #pr
          (impl_pair cl
            (sem action_sem f1)
            (impl p_of_s a_cl ptr_cl f1)
            (jumper_of_typ p_of_s t1)
            (fun x -> sem action_sem (f2 x))
            pr
            (fun x -> impl p_of_s a_cl ptr_cl (f2 x))
            (fun x -> prog_inc a_cl (f2 x))
          )
          (parser_of_typ p_of_s (TPair t1 t2))
        )
  | PSizePrefixed #_ #_ #_ #_ #_ #_ #_ #pr' #ty sc sz f ->
      coerce _
        (impl_rewrite_parser
          cl
          (sem action_sem f)
          (impl_size_prefixed
            cl
            (p_of_s sc).scalar_jumper
            (p_of_s sc).scalar_reader
            sz
            (sem action_sem f)
            pr'
            (impl p_of_s a_cl ptr_cl f)
            pr
          )
          (parser_of_typ p_of_s (TSizePrefixed sc sz ty))
        )
  | PList #_ #_ #_ #_ #_ #ty inv f ->
      coerce _
        (impl_rewrite_parser
          cl
          (fold_list inv (sem action_sem f))
          #_ #_ #true
          (impl_list
            cl
            inv
            (sem action_sem f)
            (prog_inc a_cl f)
            (parser_of_typ p_of_s ty)
            (impl p_of_s a_cl ptr_cl f)
            (jumper_of_typ p_of_s ty)
            (ptr_cl.with_ll_state_ptr inv)
            (ptr_cl.load_ll_state_ptr inv)
            (ptr_cl.store_ll_state_ptr inv)
          )
          (parser_of_typ p_of_s (TList ty))
        )
  | PListFor #_ #_ #_ #_ #_ #ty inv idx f ->
      coerce _
        (impl_rewrite_parser
          cl
          (fold_for_list inv (sem action_sem f) idx.array_index_f_nat)
          #_ #_ #true
          (impl_for_list
            cl
            inv
            (sem action_sem f)
            (jumper_of_typ p_of_s ty)
            (impl p_of_s a_cl ptr_cl f)
            (prog_inc a_cl f)
            idx
            (ptr_cl.with_ll_state_ptr inv)
            (ptr_cl.load_ll_state_ptr inv)
            (ptr_cl.store_ll_state_ptr inv)
          )
          (parser_of_typ p_of_s (TList ty))
        )
  | PChoice #_ #_ #_ #_ #_ #s #_ #_ #t f ->
      assert_norm (sem action_sem (PChoice f) == fold_choice #_ #_ #_ #(type_of_scalar s) #(type_of_payload' s t) (fun x -> sem action_sem (f x)));
      assert_norm (parser_of_typ p_of_s (TChoice s t) == weaken (pkind ne pr) (parse_dtuple2 (p_of_s s).scalar_parser #_ #(type_of_payload' s t) (fun x -> parser_of_typ p_of_s (t x))));
      coerce _
        (impl_rewrite_parser
          cl
          (fold_choice #_ #_ #_ #(type_of_scalar s) #(type_of_payload' s t) (fun x -> sem action_sem (f x)))
          #_
          #(parse_dtuple2 (p_of_s s).scalar_parser #_ #(type_of_payload' s t) (fun x -> parser_of_typ p_of_s (t x)))
          #pr
          (impl_choice
            cl
            #(type_of_scalar s)
            #(type_of_payload' s t)
            (fun x -> sem action_sem (f x))
            (p_of_s s).scalar_jumper
            (p_of_s s).scalar_reader
            (fun x -> parser_of_typ p_of_s (t x))
            pr
            (fun x -> impl p_of_s a_cl ptr_cl (f x))
          )
          (parser_of_typ p_of_s (TChoice s t))
        )

inline_for_extraction
let mk_ll_state_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (vpre: vprop)
  (#pre: state_i)
  (h: state_t pre)
: Tot Type
= (#kpre: vprop) ->
  (#tret: Type) ->
  (#kpost: (tret -> vprop)) ->
  (k: (
    (out: ll_state) ->
    STT tret
      (kpre `star` cl.ll_state_match h out)
      kpost
  )) ->
  STF tret (kpre `star` vpre) kpost True (fun _ -> True)

let extract_impl_unit_post
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (pre post: state_i)
  (f: stt state_t unit pre post)
  (h: state_t pre)
  (b: bool)
: Tot vprop
= let h' = get_return_state f h in
  if b
  then exists_ (cl.ll_state_match h')
  else cl.ll_state_failure h'

inline_for_extraction
val extract_impl_stt'_unit
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (f: Ghost.erased (stt state_t unit pre post))
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t u#_ u#_ u#_ u#_ u#0 cl vpre h)
  (kpre0: vprop)
  (fi: (kpre: vprop) -> (kpost: vprop) -> stt_impl_t' cl f (kpre0 `star` kpre) kpost)
: STT bool
    (vpre `star` kpre0)
    (fun res -> extract_impl_unit_post cl pre post f h res `star` kpre0)

inline_for_extraction
val extract_impl_stt_unit
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#f: Ghost.erased (stt state_t unit pre post))
  (fi: stt_impl_t cl f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t u#_ u#_ u#_ u#_ u#0 cl vpre h)
: STT bool
    (vpre)
    (fun res -> extract_impl_unit_post cl pre post f h res)

inline_for_extraction
let extract_impl_fold_unit_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#t: Type)
  (#f: Ghost.erased (fold_t state_t t unit pre post))
  (#k: parser_kind)
  (#p: parser k t)
  (#with_size: bool)
  (fi: fold_impl_t cl p with_size f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t cl vpre h)
: Tot Type
= (vbin: v k t) ->
  (bin: byte_array) ->
  (bin_sz: (if with_size then size_of (array_of' vbin) else unit)) ->
  STT bool
    (vpre `star` aparse p bin vbin)
    (fun res -> extract_impl_unit_post cl pre post (Ghost.reveal f vbin.contents) h res `star` aparse p bin vbin)

inline_for_extraction
val extract_impl_fold_unit
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#t: Type)
  (#f: Ghost.erased (fold_t state_t t unit pre post))
  (#k: parser_kind)
  (#p: parser k t)
  (#with_size: bool)
  (fi: fold_impl_t cl p with_size f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t u#_ u#_ u#_ u#_ u#0 cl vpre h)
: Tot (extract_impl_fold_unit_t fi mk)

module R = Steel.ST.Reference

let extract_impl_post
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (pre post: state_i)
  (#ret_t: Type)
  (r: R.ref ret_t)
  (f: stt state_t ret_t pre post)
  (h: state_t pre)
  (b: bool)
: Tot vprop
= let h' = get_return_state f h in
  let v = get_return_value f h in
  if b
  then exists_ (cl.ll_state_match h') `star` R.pts_to r full_perm v
  else cl.ll_state_failure h' `star` exists_ (R.pts_to r full_perm)

inline_for_extraction
val extract_impl_stt'
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#rett: Type)
  (f: Ghost.erased (stt state_t rett pre post))
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t u#_ u#_ u#_ u#_ u#0 cl vpre h)
  (kpre0: vprop)
  (fi: (kpre: vprop) -> (kpost: vprop) -> stt_impl_t' cl f (kpre0 `star` kpre) kpost)
  (r: R.ref rett)
: STT bool
    (vpre `star` kpre0 `star` exists_ (R.pts_to r full_perm))
    (fun res -> extract_impl_post cl pre post r f h res `star` kpre0)

inline_for_extraction
val extract_impl_stt
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#t: Type)
  (#f: Ghost.erased (stt state_t t pre post))
  (fi: stt_impl_t cl f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t u#_ u#_ u#_ u#_ u#0 cl vpre h)
  (r: R.ref t)
: STT bool
    (vpre `star` exists_ (R.pts_to r full_perm))
    (fun res -> extract_impl_post cl pre post r f h res)

inline_for_extraction
val extract_impl_fold
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#t: Type)
  (#rett: Type)
  (#f: Ghost.erased (fold_t state_t t rett pre post))
  (#k: parser_kind)
  (#p: parser k t)
  (#with_size: bool)
  (fi: fold_impl_t cl p with_size f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t u#_ u#_ u#_ u#_ u#0 cl vpre h)
  (vbin: v k t)
  (bin: byte_array)
  (bin_sz: (if with_size then size_of (array_of' vbin) else unit))
  (r: R.ref rett)
: STT bool
    (vpre `star` aparse p bin vbin `star` exists_ (R.pts_to r full_perm))
    (fun res -> extract_impl_post cl pre post r (Ghost.reveal f vbin.contents) h res `star` aparse p bin vbin)

let no_ll_state_failure_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
: Tot Type
= (#opened: _) ->
  (#i: state_i) ->
  (h: state_t i) ->
  STGhost unit opened
    (cl.ll_state_failure h)
    (fun _ -> emp)
    (True)
    (fun _ -> False)

inline_for_extraction
val extract_impl_stt'_no_failure
  (#state_i: Type) (#state_t: state_i -> Type0) (#ll_state: Type0) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (no_fail: no_ll_state_failure_t cl)
  (#pre #post: state_i)
  (#rett: Type0)
  (f: Ghost.erased (stt state_t rett pre post))
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t u#_ u#_ u#_ u#_ u#0 cl vpre h)
  (kpre0: vprop)
  (fi: (kpre: vprop) -> (kpost: vprop) -> stt_impl_t' cl f (kpre0 `star` kpre) kpost)
  (dummy: rett) // because Steel doesn't have uninitialized references yet
: STT rett
    (vpre `star` kpre0)
    (fun res -> 
      exists_ (fun (h': state_t post) ->
        exists_ (cl.ll_state_match h') `star`
        kpre0 `star`
        pure (Ghost.reveal f (Ghost.reveal h) == (res, h'))
    ))

inline_for_extraction
val extract_impl_stt_no_failure
  (#state_i: Type) (#state_t: state_i -> Type0) (#ll_state: Type0) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (no_fail: no_ll_state_failure_t cl)
  (#pre #post: state_i)
  (#t: Type0)
  (#f: Ghost.erased (stt state_t t pre post))
  (fi: stt_impl_t cl f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t u#_ u#_ u#_ u#_ u#0 cl vpre h)
  (dummy: t) // because Steel doesn't have uninitialized references yet
: STT t
    vpre
    (fun res -> 
      exists_ (fun (h': state_t post) ->
        exists_ (cl.ll_state_match h') `star`
        pure (Ghost.reveal f (Ghost.reveal h) == (res, h'))
    ))

inline_for_extraction
val extract_impl_fold_no_failure
  (#state_i: Type) (#state_t: state_i -> Type0) (#ll_state: Type0) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (no_fail: no_ll_state_failure_t cl)
  (#pre #post: state_i)
  (#t: Type)
  (#rett: Type0)
  (#f: Ghost.erased (fold_t state_t t rett pre post))
  (#k: parser_kind)
  (#p: parser k t)
  (#with_size: bool)
  (fi: fold_impl_t cl p with_size f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t u#_ u#_ u#_ u#_ u#0 cl vpre h)
  (vbin: v k t)
  (bin: byte_array)
  (bin_sz: (if with_size then size_of (array_of' vbin) else unit))
  (dummy: rett)
: STT rett
    (vpre `star` aparse p bin vbin)
    (fun res -> 
      aparse p bin vbin `star`
      exists_ (fun (h': state_t post) ->
        exists_ (cl.ll_state_match h') `star`
        pure (Ghost.reveal f vbin.contents (Ghost.reveal h) == (res, h'))
    ))

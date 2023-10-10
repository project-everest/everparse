module LowParse.SteelST.Write
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference

open Steel.ST.GenElim

include LowParse.SteelST.Parse

// DEPRECATED: use l2r_writer instead
inline_for_extraction
let writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
=
  (#va: _) ->
  (x: t) ->
  (a: byte_array) ->
  ST SZ.t
    (AP.arrayptr a va)
    (fun sz -> exists_ (fun vl -> aparse p a vl `star` exists_ (fun ar -> exists_ (fun vr -> AP.arrayptr ar vr `star` pure (
      AP.merge_into (array_of' vl) (AP.array_of vr) (AP.array_of va) /\
      vl.contents == x /\
      SZ.v sz == AP.length (array_of' vl)
    )))))
    (Seq.length (serialize s x) <= AP.length (AP.array_of va) /\
      AP.array_perm (AP.array_of va) == full_perm)
    (fun _ -> True)

inline_for_extraction
let exact_writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
=
  (#va: _) ->
  (x: t) ->
  (a: byte_array) ->
  ST (v k t)
    (AP.arrayptr a va)
    (fun va' -> aparse p a va')
    (Seq.length (serialize s x) == AP.length (AP.array_of va) /\
      AP.array_perm (AP.array_of va) == full_perm)
    (fun va' ->
      array_of' va' == AP.array_of va /\
      va'.contents == x
    )

inline_for_extraction
let exact_write
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#p: parser k t)
  (#s: serializer p)
  (w: writer s)
: Tot (exact_writer s)
= fun x a ->
  let _ = w x a in
  let _ = gen_elim () in
  let va0 = elim_aparse _ a in
  parse_injective p (AP.contents_of va0) (serialize s x);
  let va1 = AP.join a _ in
  assert (AP.contents_of va1 `Seq.equal` AP.contents_of va0);
  let va' = intro_aparse p a in
  return va'

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
let write_constant_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: exact_writer s)
  (sz: SZ.t)
: Pure (writer s)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low == SZ.v sz
    ))
    (ensures (fun _ -> True))
= fun x a ->
  let _ = AP.gsplit a sz in
  let _ = gen_elim () in
  let _ = w x a in
  return sz

#pop-options

(* Computing the serialization size for a given value. Since the size_t type is overflow-prone, the function needs to take a size bound as argument, and returns the difference between the bound and the serialization size of the value. The function also needs to take a reference to record overflow. *)

noextract
let size_comp_for_post
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
  (sz: SZ.t)
  (res: SZ.t)
  (err: bool)
: Tot prop
= let len = Seq.length (serialize s x) in
  if err then len > SZ.v sz else SZ.v res + len == SZ.v sz

inline_for_extraction
let size_comp_for
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Tot Type
= (sz: SZ.t) ->
  (perr: R.ref bool) ->
  STT SZ.t
    (R.pts_to perr full_perm false)
    (fun res -> exists_ (fun err ->
      R.pts_to perr full_perm err `star`
      pure (size_comp_for_post s x sz res err)
    ))

inline_for_extraction
let size_comp
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
= (x: t) ->
  size_comp_for s x

inline_for_extraction
let size_comp_constant_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: SZ.t)
: Pure (size_comp s)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low == SZ.v sz
    ))
    (ensures (fun _ -> True))
= fun x sz' perr ->
  if sz' `SZ.lt` sz
  then begin
    R.write perr true;
    return sz' // dummy
  end else begin
    [@@inline_let]
    let rem = sz' `SZ.sub` sz in
    noop ();
    return rem
  end

(* Left-to-right writing *)

module LW = LowParse.SteelST.L2ROutput

inline_for_extraction
let l2r_writer_for
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (v: t)
: Tot Type
= (#vout: AP.array byte) ->
  (out: LW.t) ->
  ST byte_array
    (LW.vp out vout)
    (fun res -> exists_ (fun vres -> exists_ (fun vout' ->
      aparse p res vres `star`
      LW.vp out vout' `star`
      pure (
        AP.merge_into (array_of vres) vout' vout /\
        vres.contents == v
    ))))
    (Seq.length (serialize s v) <= AP.length vout)
    (fun _ -> True)

inline_for_extraction
let l2r_writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
= (v: t) ->
  l2r_writer_for s v

inline_for_extraction
let l2r_write_constant_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: exact_writer s)
  (sz: SZ.t)
: Pure (l2r_writer s)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low == SZ.v sz
    ))
    (ensures (fun _ -> True))
= fun v out ->
    let res = LW.split out sz in
    let _ = gen_elim () in
    let _ = w v res in
    return res

inline_for_extraction
let ifthenelse_l2r_writer_for
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: Ghost.erased t)
  (cond: bool)
  (iftrue: (squash (cond == true) -> Tot (l2r_writer_for s v)))
  (iffalse: (squash (cond == false) -> Tot (l2r_writer_for s v)))
: Tot (l2r_writer_for s v)
= fun out ->
    if cond
    then iftrue () out
    else iffalse () out

inline_for_extraction
let ifthenelse_l2r_writer
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (cond: bool)
  (iftrue: (squash (cond == true) -> Tot (l2r_writer s)))
  (iffalse: (squash (cond == false) -> Tot (l2r_writer s)))
: Tot (l2r_writer s)
= fun v -> ifthenelse_l2r_writer_for s v cond (fun _ -> iftrue () v) (fun _ -> iffalse () v)

(* Right-to-left writing *)

module W = LowParse.SteelST.R2LOutput

[@@__reduce__]
let maybe_r2l_write_true
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (out: W.t)
  (vout: AP.array byte)
  (v: t)
: Tot vprop
=   exists_ (fun vl -> exists_ (fun a -> exists_ (fun va ->
      W.vp out vl `star`
      aparse p a va `star`
      pure (
        AP.merge_into vl (array_of' va) vout /\
        AP.array_perm (array_of' va) == full_perm /\
        va.contents == v
    ))))

[@@__reduce__]
let maybe_r2l_write_false
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (out: W.t)
  (vout: AP.array byte)
  (v: t)
: Tot vprop
=   W.vp out vout `star`
    pure ((Seq.length (serialize s v) > AP.length vout) == true)

let maybe_r2l_write
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (out: W.t)
  (vout: AP.array byte)
  (v: t)
  (success: bool)
: Tot vprop
= if success
  then maybe_r2l_write_true p out vout v
  else maybe_r2l_write_false s out vout v

inline_for_extraction
let maybe_r2l_writer_for
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (v: t)
: Tot Type
= (#vout: AP.array byte) ->
  (out: W.t) ->
  STT bool
    (W.vp out vout)
    (fun res -> maybe_r2l_write s out vout v res)

inline_for_extraction
let maybe_r2l_writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (v: t) ->
  maybe_r2l_writer_for s v

let intro_maybe_r2l_write_success
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (out: W.t)
  (vout: AP.array byte)
  (v: t)
  (vl: _)
  (a: _)
  (va: _)
: STGhost unit opened
    (W.vp out vl `star` aparse p a va)
    (fun _ -> maybe_r2l_write s out vout v true)
    (
      AP.merge_into vl (array_of' va) vout /\
      AP.array_perm (array_of' va) == full_perm /\
      va.contents == v
    )
    (fun _ -> True)
= noop ();
  rewrite
    (maybe_r2l_write_true p out vout v)
    (maybe_r2l_write s out vout v true)

let intro_maybe_r2l_write_failure
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (out: W.t)
  (vout: AP.array byte)
  (v: t)
: STGhost unit opened
    (W.vp out vout)
    (fun _ -> maybe_r2l_write s out vout v false)
    (Seq.length (serialize s v) > AP.length vout)
    (fun _ -> True)
= noop ();
  rewrite
    (maybe_r2l_write_false s out vout v)
    (maybe_r2l_write s out vout v false)

inline_for_extraction
let maybe_r2l_write_constant_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: exact_writer s)
  (sz: SZ.t)
: Pure (maybe_r2l_writer s)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low == SZ.v sz
    ))
    (ensures (fun _ -> True))
= fun x #vout out ->
  serialize_length s x;
  let len = W.len out in
  if sz `SZ.lte` len
  then begin
    let a = W.split out sz in
    let _ = gen_elim () in
    let _ = w x a in
    intro_maybe_r2l_write_success s out vout x _ _ _;
    return true
  end else begin
    intro_maybe_r2l_write_failure s out vout x;
    return false
  end

inline_for_extraction
let ifthenelse_maybe_r2l_writer_for
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: Ghost.erased t)
  (cond: bool)
  (iftrue: (squash (cond == true) -> Tot (maybe_r2l_writer_for s v)))
  (iffalse: (squash (cond == false) -> Tot (maybe_r2l_writer_for s v)))
: Tot (maybe_r2l_writer_for s v)
= fun a ->
    if cond
    then iftrue () a
    else iffalse () a

inline_for_extraction
let ifthenelse_maybe_r2l_writer
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (cond: bool)
  (iftrue: (squash (cond == true) -> Tot (maybe_r2l_writer s)))
  (iffalse: (squash (cond == false) -> Tot (maybe_r2l_writer s)))
: Tot (maybe_r2l_writer s)
= fun v -> ifthenelse_maybe_r2l_writer_for s v cond (fun _ -> iftrue () v) (fun _ -> iffalse () v)

inline_for_extraction
let ghost_elim_maybe_r2l_write_success
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (#v: t)
  (#vout: AP.array byte)
  (#success: Ghost.erased bool)
  (out: W.t)
: STGhost (Ghost.erased byte_array) opened
    (maybe_r2l_write s out vout v success)
    (fun a ->
      exists_ (fun vl -> exists_ (fun va ->
        W.vp out vl `star`
        aparse p a va `star`
        pure (
          AP.merge_into vl (array_of' va) vout /\
          AP.array_perm (array_of' va) == full_perm /\
          va.contents == Ghost.reveal v
    ))))
    (Ghost.reveal success == true)
    (fun _ -> True)
= rewrite
    (maybe_r2l_write s out vout v success)
    (maybe_r2l_write_true p out vout v);
  let _ = gen_elim () in
  _

inline_for_extraction
let elim_maybe_r2l_write_success
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (#v: Ghost.erased t)
  (#vout: AP.array byte)
  (#success: Ghost.erased bool)
  (out: W.t)
: ST byte_array
    (maybe_r2l_write s out vout v success)
    (fun a ->
      exists_ (fun vl -> exists_ (fun va ->
        W.vp out vl `star`
        aparse p a va `star`
        pure (
          AP.merge_into vl (array_of' va) vout /\
          AP.array_perm (array_of' va) == full_perm /\
          va.contents == Ghost.reveal v
    ))))
    (Ghost.reveal success == true)
    (fun _ -> True)
= let _ = ghost_elim_maybe_r2l_write_success s out in
  let _ = gen_elim () in
  let _ = elim_aparse p _ in
  let a = W.hop out _ in
  let _ = gen_elim () in
  let _ = intro_aparse p a in
  return a

let elim_maybe_r2l_write_failure
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (#v: t)
  (#vout: AP.array byte)
  (#success: bool)
  (out: W.t)
: STGhost unit opened
    (maybe_r2l_write s out vout v success)
    (fun a -> W.vp out vout)
    (Ghost.reveal success == false)
    (fun _ -> Seq.length (serialize s v) > AP.length vout)
= rewrite
    (maybe_r2l_write s out vout v success)
    (maybe_r2l_write_false s out vout v);
  let _ = gen_elim () in
  noop ()

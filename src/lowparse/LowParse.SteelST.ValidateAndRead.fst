module LowParse.SteelST.ValidateAndRead
include LowParse.SteelST.Validate
include LowParse.SteelST.Access
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module R = Steel.ST.Reference

let validate_and_read_success
  (#k: parser_kind)
  (#t: Type)
  (va: AP.v byte)
  (p: parser k t)
  (res: Ghost.erased byte_array)
  (vp: v k t)
  (vres: AP.v byte)
  (lenl: SZ.t)
  (w: t)
: GTot prop
= ghost_peek_strong_post va p res vp vres /\
  SZ.v lenl == AP.length (array_of vp) /\
  w == vp.contents

inline_for_extraction
let validate_and_read
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= 
  (#b: AP.v byte) ->
  (a: byte_array) ->
  (len: SZ.t) ->
  (pre: vprop) ->
  (t': Type) ->
  (post: (t' -> vprop)) ->
  (fsuccess: (
    (#va: v k t) ->
    (lenl: SZ.t) ->
    (w: t) ->
    (#b': AP.v byte) ->
    (a': Ghost.erased byte_array) ->
    ST t'
      (aparse p a va `star` AP.arrayptr a' b' `star` pre)
      post
      (validate_and_read_success b p a' va b' lenl w)
      (fun _ -> True)
  )) ->
  (ffailure: (
    (e: U32.t) ->
    ST t'
      (AP.arrayptr a b `star` pre)
      post
      (parse p (AP.contents_of b) == None /\ e <> 0ul)
      (fun _ -> True)
  )) ->
  ST t'
    (AP.arrayptr a b `star` pre)
    post
    (SZ.v len == AP.length (AP.array_of b))
    (fun _ -> True)

inline_for_extraction
let validator_of_validate_and_read  
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (vr: validate_and_read p)
: Pure (validator p)
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #b a len err ->
    vr a len
      (R.pts_to err full_perm 0ul)
      SZ.t
      (fun res ->
        AP.arrayptr a b `star` exists_ (fun v_err ->
        R.pts_to err full_perm v_err `star`
        pure (validator_prop p b v_err res)
      ))
      (fun lenl w a' ->
        unpeek_strong a b a';
        return lenl
      )
      (fun e ->
        R.write err e;
        return 0sz
      )

inline_for_extraction
let mk_validate_and_read
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (r: cps_reader p)
: Pure (validate_and_read p)
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun a len pre t' post fsuccess ffailure ->
  R.with_local 0ul (fun perr ->
    let len1 = v a len perr in
//    let _ = gen_elim () in // FIXME: WHY WHY WHY does this fail?
    let _ = elim_exists () in
    elim_pure _;
    let e = R.read perr in
    if e = 0ul
    then begin
      noop ();
      let a' = ghost_peek_strong p a in
//      let _ = gen_elim () in // FIXME: WHY WHY WHY does this fail?
      let _ = elim_exists () in
      let _ = elim_exists () in
      elim_pure _;
      r a (AP.arrayptr a' _ `star` pre) t' post (fun w -> fsuccess len1 w a')
    end else begin
      noop ();
      ffailure e
    end
  )

inline_for_extraction
let read_and_jump
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= 
  (#va: v k t) ->
  (a: byte_array) ->
  (pre: vprop) ->
  (t': Type) ->
  (post: (t' -> vprop)) ->
  (f: (
    (lenl: SZ.t) ->
    (w: t) ->
    ST t'
      (aparse p a va `star` pre)
      post
      (SZ.v lenl == AP.length (array_of va) /\
        w == va.contents
      )
      (fun _ -> True)
  )) ->
  STT t'
    (aparse p a va `star` pre)
    post

inline_for_extraction
let jumper_of_read_and_jump
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (vr: read_and_jump p)
: Pure (jumper p)
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #b a ->
    let a' = ghost_peek_strong p a in
//    let _ = gen_elim () in // FIXME: WHY WHY WHY does this fail?
    let _ = elim_exists () in
    let _ = elim_exists () in
    elim_pure _;
    let va = vpattern_replace (aparse _ _) in
    let b' = vpattern_replace (AP.arrayptr a') in
    let res = vr a
      (AP.arrayptr a' b')
      SZ.t
      (fun res ->
        AP.arrayptr a b `star`
        pure (jumper_post p b res)
      )
      (fun lenl w ->
        unpeek_strong a b a';
        return lenl
      )
    in
    elim_pure _;
    return res

inline_for_extraction
let cps_reader_of_read_and_jump
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (vr: read_and_jump p)
: Pure (cps_reader p)
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #va a pre t' post f ->
    vr a
      pre
      t'
      post
      (fun _ w -> f w)

inline_for_extraction
let mk_read_and_jump
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (r: cps_reader p)
  (j: jumper p)
: Tot (read_and_jump p)
= fun a pre t' post f ->
    let len1 = get_parsed_size j a in
    r a pre t' post (fun w ->
      f len1 w
    )

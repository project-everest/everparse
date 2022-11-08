module LowParse.SteelST.List.Length

open LowParse.SteelST.List.Iter.ConsumesWithArray
open Steel.ST.GenElim

module R = Steel.ST.Reference

unfold
let list_length_state_prop0
  (#t: Type)
  (ar: AP.array byte)
  (l: list t)
  (vl: v parse_list_kind (list t))
  (len: SZ.size_t)
: Tot prop
=
  ar == array_of' vl /\
  l == vl.contents /\
  SZ.size_v len <= AP.length ar /\ // necessary to prevent integer overflow; true since each element consumes at least one byte
  SZ.size_v len == List.Tot.length l

let list_length_state_prop
  (#t: Type)
  (ar: AP.array byte)
  (l: list t)
  (vl: v parse_list_kind (list t))
  (len: SZ.size_t)
: Tot prop
= list_length_state_prop0 ar l vl len

[@@__reduce__]
let list_length_state0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a0: byte_array)
  (blen: R.ref SZ.size_t)
  (ar: AP.array byte)
  ()
  (l: list t)
: Tot vprop
= exists_ (fun (vl: v _ _) -> exists_ (fun len ->
    aparse (parse_list p) a0 vl `star`
    R.pts_to blen full_perm len `star`
    pure (
      list_length_state_prop ar l vl len
    )
  ))

let list_length_state
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a0: byte_array)
  (blen: R.ref SZ.size_t)
  (ar: AP.array byte)
  ()
  (l: list t)
: Tot vprop
= list_length_state0 p a0 blen ar () l

#push-options "--z3rlimit 64"
#restart-solver

inline_for_extraction
let list_length
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#va0: v _ _)
  (a0: byte_array)
  (len: SZ.size_t)
: ST SZ.size_t
    (aparse (parse_list p) a0 va0)
    (fun _ -> aparse (parse_list p) a0 va0)
    (SZ.size_v len == AP.length (array_of' va0) /\
      k.parser_kind_subkind == Some ParserStrong)
    (fun res -> SZ.size_v res == List.Tot.length va0.contents)
= let a1 = list_split_nil_l _ a0 in
  let _ = gen_elim () in
  let vl : v _ _ = vpattern (aparse (parse_list p) a0) in
  let ar = array_of' vl in
  let phi (_: unit) (_: t) : Tot unit = () in
  let res : (res: SZ.size_t { SZ.size_v res == List.Tot.length va0.contents }) = with_local SZ.zero_size (fun blen ->
    noop ();
    rewrite
      (list_length_state0 p a0 blen ar () [])
      (list_length_state p a0 blen ar () []);
    list_iter_consumes_with_array
      j
      phi
      (list_length_state p a0 blen)
      (fun va a al accu l ->
        rewrite
          (list_length_state p a0 blen al _ l)
          (list_length_state0 p a0 blen al () l);
        let _ = gen_elim () in
        let len = R.read blen in
        let _ = intro_singleton _ a in
        let vl' = list_append _ a0 a in
        let al' = array_of' vl' in
        let l' = Ghost.hide (List.Tot.snoc (Ghost.reveal l, va.contents)) in
        List.Tot.append_length l [va.contents];
        let len' = len `SZ.size_add` SZ.one_size in
        R.write blen len';
        list_iter_consumes_with_array_body_post_intro k phi va al accu l al' l' ();
        noop ();
        rewrite
          (list_length_state0 p a0 blen al' () l')
          (list_length_state p a0 blen al' () l');
        return ()
      )
      a0
      len
      ar
      ();
    let _ = gen_elim () in
    rewrite
      (list_length_state p a0 blen _ _ _)
      (list_length_state0 p a0 blen (array_of' va0) () va0.contents);
    let _ = gen_elim () in
    let res = R.read blen in
    let res' : (res: SZ.size_t { SZ.size_v res == List.Tot.length va0.contents }) = res in
    noop ();
    return res'
  )
  in
  return res

#pop-options


module LowParse.SteelST.Access
include LowParse.SteelST.Parse

module AP = LowParse.SteelST.ArrayPtr
module SZ = LowParse.Steel.StdInt

open Steel.ST.Util

#set-options "--ide_id_info_off"

let parsed_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (Type u#1)
=
  (base: Type) ->
  (va: AP.v base byte) ->
  (a: byte_array base) ->
  (sq: squash (Some? (parse p (AP.contents_of va)))) ->
  STT SZ.size_t
    (AP.arrayptr a va)
    (fun res -> AP.arrayptr a va `star` pure (
      match parse p (AP.contents_of' va) with
      | None -> False
      | Some (_, consumed) ->
        SZ.size_v res == consumed
    ))

let parsed_size_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: SZ.size_t)
: Pure (parsed_size p)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      SZ.size_v sz == k.parser_kind_low
    ))
    (ensures (fun _ -> True))
=
  fun base va a sq ->
  parser_kind_prop_equiv k p;
  noop ();
  return sz

let get_parsed_size
  (#base: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#vp: v base k t)
  (j: parsed_size p)
  (a: byte_array base)
: STT SZ.size_t
    (aparse p a vp)
    (fun res -> aparse p a vp `star` pure (SZ.size_v res == AP.length (array_of vp)))
=
  let _ = elim_aparse p a in
  elim_pure _; // FIXME: this can go away if I replace pure with ensures; but not if I also have exists_ in the post-resource of the callee. This is just to illustrate the intended style.
  let res = j base _ a () in
  elim_pure _;
  let _ = intro_aparse p a () in
  elim_pure _;
  return res

let seq_slice
  (#a:Type) (s:Seq.seq a) (i: nat) (j: nat) : Pure (Seq.seq a)
  (requires (i <= j /\ j <= Seq.length s))
  (ensures (fun _ -> True))
= Seq.slice s i j

let parse'
  (#a: Type)
  (#k: parser_kind)
  (p: parser k a)
  (b: bytes)
: GTot (option (a & nat))
= match parse p b with
  | None -> None
  | Some (v, c) -> Some (v, c)

let peek_strong
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#va: AP.v base byte)
  (j: parsed_size p)
  (a: byte_array base)
  (sq: squash (
    k.parser_kind_subkind == Some ParserStrong /\
    Some? (parse p (AP.contents_of' va))
  ))
: STT (byte_array base)
    (AP.arrayptr a va)
    (fun res -> exists_ (fun vp -> aparse p a vp `star` exists_ (fun vres -> AP.arrayptr res vres `star` pure (
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      AP.contents_of' vres == seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed)
    ))))
=
  let n = j base _ a () in
  elim_pure _;
  parse_strong_prefix p (AP.contents_of va) (Seq.slice (AP.contents_of va) 0 (SZ.size_v n));
  let res = AP.split a n () in
  let _ = elim_exists () in
  let _ = elim_exists () in
  elim_pure _;
  let _ = intro_aparse p a () in
  elim_pure _;
  return res

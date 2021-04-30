module LowParse.Steel.Base
include LowParse.Spec.Base

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Memory
open Steel.FractionalPermission

module S = Steel.Memory
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module A = Steel.Array

(* For now, we only support parsers with ParserStrong or ParserConsumesAll subkind. *)

let byte_array = A.array byte

let supported_kind
  (k: parser_kind)
: Tot bool
= match k.parser_kind_subkind with
  | Some ParserStrong
  | Some ParserConsumesAll
    -> true
  | _ -> false

let parsed_value
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: Ghost.erased t)
  (b: bytes)
: Tot prop
= supported_kind k /\
  begin match parse p b with
  | None -> False
  | Some (v', consumed) ->
    v' == Ghost.reveal v /\
    consumed == Seq.length b
  end

let valid'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: byte_array)
  (perm: A.perm)
  (v: Ghost.erased t)
: Tot S.slprop
= S.h_exists (fun (b: A.contents byte) -> A.is_array x perm b `S.star` S.pure (parsed_value p v b))

let valid
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: byte_array)
  (perm: A.perm)
: Tot S.slprop
= S.h_exists (valid' p x perm)

let valid'_intro_exact_pre
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: byte_array)
  (b: Ghost.erased bytes)
: Tot prop
=
  supported_kind k == true /\
    begin match parse p b with
    | None -> False
    | Some (_, consumed) -> consumed == Seq.length b
    end

let valid'_intro_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: byte_array)
  (perm: A.perm)
  (b: Ghost.erased bytes)
: SE.Steel
    (Ghost.erased t)
    (A.is_array x perm b)
    (fun v ->
      valid' p x perm v
    )
    (requires (fun _ ->
      valid'_intro_exact_pre p x b
    ))
    (ensures (fun _ v _ ->
      match parse p b with
      | None -> False
      | Some (v', _) ->
        Ghost.reveal v == v'
    ))
=
  let v : Ghost.erased t = Ghost.hide (fst (Some?.v (parse p (Ghost.reveal b)))) in
  SEA.intro_pure (parsed_value p v b);
  SEA.intro_exists b (fun (b: A.contents byte) -> A.is_array x perm b `S.star` S.pure (parsed_value p v b));
  v

let valid'_intro_consumes_all
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: byte_array)
  (perm: A.perm)
  (b: Ghost.erased bytes)
: SE.Steel
    (Ghost.erased t)
    (A.is_array x perm b)
    (fun v ->
      valid' p x perm v
    )
    (requires (fun _ ->
      k.parser_kind_subkind == Some ParserConsumesAll /\
      Some? (parse p b) == true
    ))
    (ensures (fun _ v _ ->
      match parse p b with
      | None -> False
      | Some (v', _) ->
        Ghost.reveal v == v'
    ))
=
  parser_kind_prop_equiv k p;
  valid'_intro_exact p x perm b

module U32 = FStar.UInt32

(* FIXME: WHY WHY WHY do we need < in Steel.Array.split? *)

(* FIXME: the current version of split cannot be used, due to unification issues:
assume
val array_split (#t:Type) (#p:A.perm) (#r:A.contents t) (a:A.array t) (i:U32.t { U32.v i <= A.length r })
  : SE.Steel (A.array t & A.array t)
          (A.is_array a p r)
          (fun (al, ar) ->
             let prefix, suffix = Seq.split r (U32.v i) in
             A.is_array al p prefix `S.star` A.is_array ar p suffix)
          (fun _ -> True)
          (fun _ (al, ar) _ -> A.adjacent al ar)
*)

noeq
type array_split_res
  (t: Type)
=
  {
    as_al: A.array t;
    as_ar: A.array t;
    as_prefix: A.contents t;
    as_suffix: A.contents t;
  }

assume
val array_split (#t:Type) (#p:A.perm) (#r:A.contents t) (a:A.array t) (i:U32.t { U32.v i <= A.length r })
  : SE.Steel (array_split_res t)
          (A.is_array a p r)
          (fun res ->
             A.is_array res.as_al p res.as_prefix `S.star` A.is_array res.as_ar p res.as_suffix)
          (fun _ -> True)
          (fun _ res _ -> 
            (Ghost.reveal res.as_prefix, Ghost.reveal res.as_suffix) == Seq.split r (U32.v i) /\
            A.adjacent res.as_al res.as_ar
          )

noeq
type valid_intro_strong_res
  (t: Type)
=
  {
    vi_hd: byte_array;
    vi_tl: byte_array;
    vi_value: Ghost.erased t;
    vi_btl: Ghost.erased bytes;
  }

let valid'_intro_strong
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: byte_array)
  (perm: A.perm)
  (sz: U32.t)
  (b: Ghost.erased bytes)
: SE.Steel
    (valid_intro_strong_res t)
    (A.is_array x perm b)
    (fun res ->
      valid' p res.vi_hd perm res.vi_value `S.star` A.is_array res.vi_tl perm res.vi_btl
    )
    (requires (fun _ ->
      k.parser_kind_subkind == Some ParserStrong /\
      begin match parse p b with
      | None -> False
      | Some (_, consumed) -> U32.v sz == consumed
      end
    ))
    (ensures (fun _ res _ ->
      match parse p b with
      | None -> False
      | Some (v', consumed) ->
        res.vi_value == (Ghost.hide v') /\
        Ghost.reveal res.vi_btl == Seq.slice (Ghost.reveal b) consumed (Seq.length b) /\
        A.adjacent res.vi_hd res.vi_tl (* FIXME: and their join is x? *)
    ))
=
  let s = array_split x sz in
  parse_strong_prefix p b s.as_prefix;
  let v = valid'_intro_exact p s.as_al perm s.as_prefix in
  let res = { vi_hd = s.as_al; vi_tl = s.as_ar; vi_value = v; vi_btl = s.as_suffix } in
  SEA.change_slprop (valid' p s.as_al perm v `S.star` A.is_array s.as_ar perm s.as_suffix) (valid' p res.vi_hd perm res.vi_value `S.star` A.is_array res.vi_tl perm res.vi_btl) (fun _ -> ());
  return res

let validator
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type0
=
  (x: byte_array) ->
  (x_sz: U32.t) ->
  (perm: A.perm) ->
  (b: Ghost.erased bytes) ->
  SE.Steel
    (option (valid_intro_strong_res t))
    (A.is_array x perm b)
    (fun res ->
      match res with
      | None -> A.is_array x perm b
      | Some res ->
        valid' p res.vi_hd perm res.vi_value `S.star` A.is_array res.vi_tl perm res.vi_btl
    )
    (requires (fun _ ->
      U32.v x_sz == A.length b
    ))
    (ensures (fun _ res _ ->
      match parse p b with
      | None -> None? res == true
      | Some (v', consumed) ->
        Some? res /\
        begin let Some res = res in
          res.vi_value == (Ghost.hide v') /\
          Ghost.reveal res.vi_btl == Seq.slice (Ghost.reveal b) consumed (Seq.length b) /\
          A.adjacent res.vi_hd res.vi_tl (* FIXME: and their join is x? *)
        end
    ))

#set-options "--ide_id_info_off"

let validate_total_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: U32.t {
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata = Some ParserKindMetadataTotal /\
    U32.v sz == k.parser_kind_low
  })
: Tot (validator p)
=
  fun x x_sz perm b ->
    parser_kind_prop_equiv k p;
    if x_sz `U32.lt` sz
    then begin
      assert (None? (parse p b));
      let _ = SE.noop () in
      None
    end else begin
      let res = valid'_intro_strong p x perm sz b in
      Some res
    end

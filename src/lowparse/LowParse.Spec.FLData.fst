(* Parse data of some explicitly fixed length *)

module LowParse.Spec.FLData
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module Classical = FStar.Classical

inline_for_extraction
val parse_fldata'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
: Tot (bare_parser t)

let parse_fldata' #k #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes) ->
  if Seq.length s < sz
  then None
  else
    match parse p (Seq.slice s 0 sz) with
    | Some (v, consumed) ->
      if (consumed <: nat) = (sz <: nat)
      then Some (v, (sz <: consumed_length s))
      else None
    | _ -> None

let parse_fldata_injective
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
: Lemma
  (ensures (injective (parse_fldata' p sz)))
= parser_kind_prop_equiv k p;
  let f
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond (parse_fldata' p sz) b1 b2))
    (ensures (injective_postcond (parse_fldata' p sz) b1 b2))
  = assert (injective_precond p (Seq.slice b1 0 sz) (Seq.slice b2 0 sz))
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (f b))

// unfold
inline_for_extraction
let parse_fldata_kind
  (sz: nat)
  (k: parser_kind)
: Tot parser_kind
= strong_parser_kind sz sz (
    match k.parser_kind_metadata with
    | Some ParserKindMetadataFail -> Some ParserKindMetadataFail
    | _ -> None
  )

inline_for_extraction
val parse_fldata
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
: Tot (parser (parse_fldata_kind sz k) t)

let parse_fldata #b #t p sz =
  parse_fldata_injective p sz;
  parser_kind_prop_equiv b p;
  parser_kind_prop_equiv (parse_fldata_kind sz b) (parse_fldata' p sz);
  parse_fldata' p sz  

val parse_fldata_consumes_all
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
: Pure (bare_parser t)
  (requires (k.parser_kind_subkind == Some ParserConsumesAll))
  (ensures (fun _ -> True))

let parse_fldata_consumes_all #k #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes) ->
  if Seq.length s < sz
  then None
  else
    match parse p (Seq.slice s 0 sz) with
    | Some (v, _) ->
      Some (v, (sz <: consumed_length s))
    | _ -> None

let parse_fldata_consumes_all_correct
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
  (b: bytes)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserConsumesAll))
  (ensures (parse (parse_fldata p sz) b == parse (parse_fldata_consumes_all p sz) b))
= parser_kind_prop_equiv k p

let parse_fldata_strong_pred
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (x: t)
: GTot Type0
= Seq.length (serialize s x) == sz

let parse_fldata_strong_t
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
: Tot Type
= (x: t { parse_fldata_strong_pred s sz x } )

let parse_fldata_strong_correct
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (xbytes: bytes)
  (consumed: consumed_length xbytes)
  (x: t)
: Lemma
  (requires (parse (parse_fldata p sz) xbytes == Some (x, consumed)))
  (ensures (parse_fldata_strong_pred s sz x))
= serializer_correct_implies_complete p s

inline_for_extraction
let parse_fldata_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
: Tot (parser (parse_fldata_kind sz k) (parse_fldata_strong_t s sz))
= coerce_parser
  (parse_fldata_strong_t s sz)
  (parse_strengthen (parse_fldata p sz) (parse_fldata_strong_pred s sz) (parse_fldata_strong_correct s sz))

#set-options "--z3rlimit 16"

let serialize_fldata_strong'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
: Tot (bare_serializer (parse_fldata_strong_t s sz))
= (fun (x: parse_fldata_strong_t s sz) ->
  s x)

let serialize_fldata_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
: Tot (serializer (parse_fldata_strong s sz))
= serialize_fldata_strong' s sz

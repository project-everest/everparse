module LowParse.Tot.VLGen
include LowParse.Spec.VLGen
include LowParse.Tot.Int
include LowParse.Tot.Combinators

module U32 = FStar.UInt32

let parse_vlgen_weak_bare
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 min max))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (bare_parser t)
= fun input ->
    match pk input with
    | None -> None
    | Some (len, sz) ->
      begin
        if Seq.length input < sz + U32.v len
        then None
        else
        let input' = Seq.slice input sz (sz + U32.v len) in
        match p input' with
        | Some (x, consumed_x) ->
          if consumed_x = U32.v len
          then
            Some (x, sz + U32.v len)
        else None
      | _ -> None
    end

let parse_vlgen_weak
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 min max))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_vlgen_weak_kind sk min max k.parser_kind_injective) t)
= Classical.forall_intro (parse_vlgen_weak_unfold min max #sk pk #k #t p);
  parser_kind_prop_ext (parse_vlgen_weak_kind sk min max k.parser_kind_injective) (parse_vlgen_weak min max #sk pk #k #t p) (parse_vlgen_weak_bare min max pk p);
  parse_vlgen_weak_bare min max pk p

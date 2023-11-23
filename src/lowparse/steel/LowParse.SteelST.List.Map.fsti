module LowParse.SteelST.List.Map
include LowParse.SteelST.List.Base

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

open Steel.ST.Util

inline_for_extraction
val list_map_inplace_le_opt
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p { k.parser_kind_subkind == Some ParserStrong })
  (#k': parser_kind)
  (#t': Type0)
  (p': parser k' t' { k'.parser_kind_subkind == Some ParserStrong })
  (phi: Ghost.erased (t -> t'))
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (vout: AP.v byte { AP.adjacent (AP.array_of vout) (array_of' va) }) -> // TODO: add write permissions
    (out: byte_array) ->
    STT SZ.t
      (aparse p a va `star` AP.arrayptr out vout)
      (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
        aparse p' out vout' `star` AP.arrayptr res' vres' `star` pure (
        SZ.v res == AP.length (array_of vout') /\
        SZ.v res > 0 /\
        AP.merge_into (array_of' vout') (AP.array_of vres') (AP.merge (AP.array_of vout) (array_of' va)) /\
        vout'.contents == Ghost.reveal phi va.contents
      )))))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.t { SZ.v len == length_opt va.array })
  (#vout: _)
  (out: byte_array { adjacent_opt (AP.array_of vout) va.array })  // TODO: add write permissions
: STT SZ.t
    (aparse_list p a va `star` AP.arrayptr out vout)
    (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
      aparse (parse_list p') out vout' `star` AP.arrayptr res' vres' `star` pure (
      SZ.v res == AP.length (array_of' vout') /\
      AP.merge_into (array_of' vout') (AP.array_of vres') (merge_opt (AP.array_of vout) va.array) /\
      vout'.contents == List.Tot.map phi va.contents
    )))))

inline_for_extraction
val list_map_inplace_le
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p { k.parser_kind_subkind == Some ParserStrong })
  (#k': parser_kind)
  (#t': Type0)
  (p': parser k' t' { k'.parser_kind_subkind == Some ParserStrong })
  (phi: Ghost.erased (t -> t'))
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (vout: AP.v byte { AP.adjacent (AP.array_of vout) (array_of' va) }) -> // TODO: add write permissions
    (out: byte_array) ->
    STT SZ.t
      (aparse p a va `star` AP.arrayptr out vout)
      (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
        aparse p' out vout' `star` AP.arrayptr res' vres' `star` pure (
        SZ.v res == AP.length (array_of vout') /\
        SZ.v res > 0 /\
        AP.merge_into (array_of' vout') (AP.array_of vres') (AP.merge (AP.array_of vout) (array_of' va)) /\
        vout'.contents == Ghost.reveal phi va.contents
      )))))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.t { SZ.v len == AP.length (array_of' va) })
  (#vout: _)
  (out: byte_array { AP.adjacent (AP.array_of vout) (array_of' va) })  // TODO: add write permissions
: STT SZ.t
    (aparse (parse_list p) a va `star` AP.arrayptr out vout)
    (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
      aparse (parse_list p') out vout' `star` AP.arrayptr res' vres' `star` pure (
      SZ.v res == AP.length (array_of' vout') /\
      AP.merge_into (array_of' vout') (AP.array_of vres') (AP.merge (AP.array_of vout) (array_of' va)) /\
      vout'.contents == List.Tot.map phi va.contents
    )))))

inline_for_extraction
val list_map_inplace_eq
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p { k.parser_kind_subkind == Some ParserStrong })
  (#k': parser_kind)
  (#t': Type0)
  (p': parser k' t' { k'.parser_kind_subkind == Some ParserStrong })
  (phi: Ghost.erased (t -> t'))
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) -> // TODO: add write permissions
    (a: byte_array) ->
    STT (v k' t')
      (aparse p a va)
      (fun va' -> aparse p' a va' `star` pure (
        array_of' va' == array_of' va /\
        va'.contents == Ghost.reveal phi va.contents
      ))
  ))
  (#va: v _ _)
  (a: byte_array)
  (len: SZ.t)
: ST (v _ _)
    (aparse (parse_list p) a va)
    (fun va' -> aparse (parse_list p') a va')
    (SZ.v len == AP.length (array_of' va))  // TODO: add write permissions
    (fun va' ->
      array_of' va' == array_of' va /\
      va'.contents == List.Tot.map phi va.contents
    )

inline_for_extraction
val list_map_inplace_eq_opt
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p { k.parser_kind_subkind == Some ParserStrong })
  (#k': parser_kind)
  (#t': Type0)
  (p': parser k' t' { k'.parser_kind_subkind == Some ParserStrong })
  (phi: Ghost.erased (t -> t'))
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) -> // TODO: add write permissions
    (a: byte_array) ->
    STT (v k' t')
      (aparse p a va)
      (fun va' -> aparse p' a va' `star` pure (
        array_of' va' == array_of' va /\
        va'.contents == Ghost.reveal phi va.contents
      ))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.t)
: ST _
    (aparse_list p a va)
    (fun va' -> aparse_list p' a va')
    (SZ.v len == length_opt va.array)  // TODO: add write permissions
    (fun va' ->
      va'.array == va.array /\
      va'.contents == List.Tot.map phi va.contents
    )

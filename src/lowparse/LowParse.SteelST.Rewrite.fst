module LowParse.SteelST.Rewrite
include LowParse.Spec.Rewrite
include LowParse.SteelST.Combinators
open Steel.ST.GenElim

let rewrite_1
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#w: v k t)
  (x: byte_array)
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t')
  (f: (t -> GTot (option t')))
  (sq: squash (can_rewrite p p' f))
: STGhost (v k' t') opened
    (aparse p x w)
    (fun w' -> aparse p' x w')
    (Some? (f w.contents))
    (fun w' ->
      f w.contents == Some w'.contents /\
      array_of' w' == array_of' w
    )
= let _ = elim_aparse p x in
  intro_aparse p' x

module AP = LowParse.SteelST.ArrayPtr

let rewrite_2
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#w1: v k1 t1)
  (x: byte_array)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#w2: v k2 t2)
  (x2: byte_array)
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t')
  (f: ((t1 & t2) -> GTot (option t')))
  (sq: squash (can_rewrite (p1 `nondep_then` p2) p' f))
: STGhost (v k' t') opened
    (aparse p1 x w1 `star` aparse p2 x2 w2)
    (fun w' -> aparse p' x w')
    (Some? (f (w1.contents, w2.contents)) /\
      k1.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of' w1) (array_of' w2)
    )
    (fun w' ->
      f (w1.contents, w2.contents) == Some w'.contents /\
      AP.adjacent (array_of' w1) (array_of' w2) /\
      AP.merge (array_of' w1) (array_of' w2) == array_of' w'
    )
= let _ = merge_pair p1 p2 x x2 in
  rewrite_1 x p' f sq

let rewrite_3
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#w1: v k1 t1)
  (x: byte_array)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#w2: v k2 t2)
  (x2: byte_array)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#w3: v k3 t3)
  (x3: byte_array)
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t')
  (f: ((t1 & (t2 & t3)) -> GTot (option t')))
  (sq: squash (can_rewrite (p1 `nondep_then` (p2 `nondep_then` p3)) p' f))
: STGhost (v k' t') opened
    (aparse p1 x w1 `star` aparse p2 x2 w2 `star` aparse p3 x3 w3)
    (fun w' -> aparse p' x w')
    (Some? (f (w1.contents, (w2.contents, w3.contents))) /\
      k1.parser_kind_subkind == Some ParserStrong /\
      k2.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of' w1) (array_of' w2) /\
      AP.adjacent (array_of' w2) (array_of' w3)
    )
    (fun w' ->
      f (w1.contents, (w2.contents, w3.contents)) == Some w'.contents /\
      AP.adjacent (array_of' w1) (array_of' w2) /\
      AP.adjacent (array_of' w2) (array_of' w3) /\
      AP.merge (array_of' w1) (AP.merge (array_of' w2) (array_of' w3)) == array_of' w'
    )
= let _ = merge_pair p2 p3 x2 x3 in
  rewrite_2 x x2 p' f sq

let rewrite_4
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#w1: v k1 t1)
  (x: byte_array)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#w2: v k2 t2)
  (x2: byte_array)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#w3: v k3 t3)
  (x3: byte_array)
  (#k4: parser_kind)
  (#t4: Type)
  (#p4: parser k4 t4)
  (#w4: v k4 t4)
  (x4: byte_array)
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t')
  (f: ((t1 & (t2 & (t3 & t4))) -> GTot (option t')))
  (sq: squash (can_rewrite (p1 `nondep_then` (p2 `nondep_then` (p3 `nondep_then` p4))) p' f))
: STGhost (v k' t') opened
    (aparse p1 x w1 `star` aparse p2 x2 w2 `star` aparse p3 x3 w3 `star` aparse p4 x4 w4)
    (fun w' -> aparse p' x w')
    (Some? (f (w1.contents, (w2.contents, (w3.contents, w4.contents)))) /\
      k1.parser_kind_subkind == Some ParserStrong /\
      k2.parser_kind_subkind == Some ParserStrong /\
      k3.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of' w1) (array_of' w2) /\
      AP.adjacent (array_of' w2) (array_of' w3) /\
      AP.adjacent (array_of' w3) (array_of' w4)
    )
    (fun w' ->
      f (w1.contents, (w2.contents, (w3.contents, w4.contents))) == Some w'.contents /\
      AP.adjacent (array_of' w1) (array_of' w2) /\
      AP.adjacent (array_of' w2) (array_of' w3) /\
      AP.adjacent (array_of' w3) (array_of' w4) /\
      AP.merge (array_of' w1) (AP.merge (array_of' w2) (AP.merge (array_of' w3) (array_of' w4))) == array_of' w'
    )
= let _ = merge_pair p3 p4 x3 x4 in
  rewrite_3 x x2 x3 p' f sq

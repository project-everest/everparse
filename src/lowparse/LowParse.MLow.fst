module LowParse.MLow
include LowParse.MLow.Base
include LowParse.MLow.Combinators
include LowParse.MLow.Int

let inversion_tuple2 (a b: Type) : Lemma (inversion (tuple2 a b)) [SMTPat (tuple2 a b)] = allow_inversion (tuple2 a b)

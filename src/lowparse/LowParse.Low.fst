module LowParse.Low
include LowParse.Low.Base
include LowParse.Low.Combinators
include LowParse.Low.Int
include LowParse.Low.List
include LowParse.Low.FLData
include LowParse.Low.Array
include LowParse.Low.Bytes
include LowParse.Low.VLData
include LowParse.Low.Enum
include LowParse.Low.Option
include LowParse.Low.Sum
include LowParse.Low.Tac.Sum
include LowParse.Low.IfThenElse
include LowParse.Low.VCList
include LowParse.Low.BCVLI
include LowParse.Low.DER
include LowParse.Low.VLGen

let inversion_tuple2 (a b: Type) : Lemma (inversion (tuple2 a b)) [SMTPat (tuple2 a b)] = allow_inversion (tuple2 a b)

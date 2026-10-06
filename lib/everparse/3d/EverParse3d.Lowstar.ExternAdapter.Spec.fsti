module EverParse3d.Lowstar.ExternAdapter.Spec
module P = EverParse3d.Prelude
module U8 = FStar.UInt8

// Public observation of the otherwise abstract P.parser. The implementation
// is exactly LowParse.Spec.Base.parse, not a second parser specification.
noextract
val parse
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (p: P.parser #nz #wk k t) (input: Seq.seq U8.t)
  : GTot (option (t & (n: nat { n <= Seq.length input })))

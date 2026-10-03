module EverParse3d.Lowstar.ExternAdapter.Spec
friend EverParse3d.Kinds
friend EverParse3d.Prelude
module P = EverParse3d.Prelude
module LP = LowParse.Spec.Base
module U8 = FStar.UInt8

noextract
let parse
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (p: P.parser #nz #wk k t) (input: Seq.seq U8.t)
  : GTot (option (t & (n: nat { n <= Seq.length input })))
  = LP.parse p input

let parse_eq
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (p: P.parser #nz #wk k t) (input: Seq.seq U8.t)
  : Lemma (parse p input == LP.parse p input)
  = ()

let parse_bounds
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (p: P.parser #nz #wk k t) (input: Seq.seq U8.t)
  : Lemma (Some? (LP.parse p input) ==>
      snd (Some?.v (LP.parse p input)) <= Seq.length input)
  = match LP.parse p input with
    | None -> ()
    | Some _ -> ()

module CBOR.SteelST.Raw.Base
include CBOR.Spec.Format
open LowParse.SteelST.Combinators
open Steel.ST.GenElim

module I = LowParse.SteelST.Int

let read_u8 = I.read_u8
let read_u16 = I.read_u16
let read_u32 = I.read_u32
let read_u64 = I.read_u64

let elim_synth'
  #opened
  #k1 #t1 (p1: parser k1 t1)
  #t2 (f2: t1 -> GTot t2) (g1: t2 -> GTot t1)
  #va2 (a: byte_array)
  (sq: squash (synth_injective f2 /\
    synth_inverse f2 g1
  ))
: STGhost (v k1 t1) opened
    (aparse (p1 `parse_synth` f2) a va2)
    (fun va -> aparse p1 a va)
    True
    (fun va ->
      array_of va2 == array_of va /\
      va2.contents == f2 (va.contents) /\
      va.contents == g1 va2.contents
    )
= let va = elim_synth p1 f2 a () in
  assert (f2 (g1 va2.contents) == va2.contents);
  noop ();
  va

let ifthenelse_vprop
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
: Tot vprop
= if cond
  then vtrue ()
  else vfalse ()

let intro_ifthenelse_vprop_true
  (#opened: _)
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
  (cond_true: squash (cond == true))
: STGhostT unit opened
    (vtrue ())
    (fun _ -> ifthenelse_vprop cond vtrue vfalse)
= rewrite
    (vtrue ())
    (ifthenelse_vprop cond vtrue vfalse)

let intro_ifthenelse_vprop_false
  (#opened: _)
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
  (cond_false: squash (cond == false))
: STGhostT unit opened
    (vfalse ())
    (fun _ -> ifthenelse_vprop cond vtrue vfalse)
= rewrite
    (vfalse ())
    (ifthenelse_vprop cond vtrue vfalse)

let elim_ifthenelse_vprop_true
  (#opened: _)
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
  (sq: squash (cond == true))
: STGhostT unit opened
    (ifthenelse_vprop cond vtrue vfalse)
    (fun _ -> vtrue ())
= rewrite
    (ifthenelse_vprop cond vtrue vfalse)
    (vtrue ())

let elim_ifthenelse_vprop_false
  (#opened: _)
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
  (sq: squash (cond == false))
: STGhostT unit opened
    (ifthenelse_vprop cond vtrue vfalse)
    (fun _ -> vfalse ())
= rewrite
    (ifthenelse_vprop cond vtrue vfalse)
    (vfalse ())

let write_u8 = I.write_u8
let write_u16 = I.write_u16
let write_u32 = I.write_u32
let write_u64 = I.write_u64


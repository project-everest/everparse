module CBOR.Pulse.Raw.EverParse.UTF8
#lang-pulse
friend CBOR.Spec.API.UTF8
friend CBOR.Spec.Raw.Format.UTF8

open CBOR.Spec.Raw.Format.UTF8

let impl_fetch_utf8_correct_postcond
  (i: SZ.t)
  (v: Seq.seq U8.t)
  (vcont: bool)
  (res: SZ.t)
: Tot prop
= 
  SZ.v i < Seq.length v /\
  begin match fetch (Seq.slice v (SZ.v i) (Seq.length v)) with
  | Success vres -> vcont == true /\ SZ.v res == SZ.v i + vres
  | _ -> vcont == false /\ res == i
  end

inline_for_extraction noextract [@@noextract_to "krml"]
let u8_in_80_BF
  (x: U8.t)
: Tot bool
= U8.lte 0x80uy x && U8.lte x 0xBFuy

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_fetch_utf8_correct
  (s: S.slice U8.t)
  (len: SZ.t { len == S.len s })
  (pi: ref SZ.t)
  (pcont: ref bool)
  (#i: Ghost.erased SZ.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to s #p v ** pts_to pi i ** pts_to pcont true ** pure (SZ.v i < Seq.length v))
ensures
    (exists* vcont res . pts_to s #p v ** pts_to pi res ** pts_to pcont vcont **
      pure (
        impl_fetch_utf8_correct_postcond i v vcont res
      )
    )
{
  S.pts_to_len s;
  let i = !pi;
  let byte1 = S.op_Array_Access s i;
  let i1 : SZ.t = (SZ.add i 1sz);
  if (U8.lte byte1 0x7Fuy) {
    pi := i1;
  } else if (i1 = len) {
    pcont := false;
  } else {
    let byte2 = S.op_Array_Access s i1;
    let i2 : SZ.t = SZ.add i1 1sz;
    if (U8.lte 0xC2uy byte1 && U8.lte byte1 0xDFuy && u8_in_80_BF byte2) {
       pi := i2;
    } else if (i2 = len) {
      pcont := false
    } else {
      let byte3 = S.op_Array_Access s i2;
      let i3 : SZ.t = SZ.add i2 1sz;
      if (not (u8_in_80_BF byte3)) {
         pcont := false
      } else if (byte1 = 0xE0uy) {
        if (U8.lte 0xA0uy byte2 && U8.lte byte2 0xBFuy) {
           pi := i3;
        } else {
          pcont := false
        }
      } else if (byte1 = 0xEDuy) {
        if (U8.lte 0x80uy byte2 && U8.lte byte2 0x9Fuy) {
           pi := i3;
        } else {
          pcont := false
        }
      } else if (U8.lte 0xE1uy byte1 && U8.lte byte1 0xEFuy && u8_in_80_BF byte2) {
        pi := i3;
      } else if (i3 = len) {
        pcont := false
      } else {
        let byte4 = S.op_Array_Access s i3;
        let i4 = SZ.add i3 1sz;
        if (not (u8_in_80_BF byte4)) {
           pcont := false
        } else if (byte1 = 0xF0uy && U8.lte 0x90uy byte2 && U8.lte byte2 0xBFuy) {
          pi := i4;
        } else if (U8.lte 0xF1uy byte1 && U8.lte byte1 0xF3uy && u8_in_80_BF byte2) {
          pi := i4;
        } else if (byte1 = 0xF4uy && U8.lte 0x80uy byte2 && U8.lte byte2 0x8Fuy) {
          pi := i4;
        } else {
          pcont := false
        }
      }
    }
  }
}

#push-options "--z3rlimit 16"

#restart-solver

fn impl_correct
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to s #p v)
returns res: bool
ensures
    (pts_to s #p v ** pure (res == correct v))
{
  S.pts_to_len s;
  let mut pres = true;
  let mut pi = 0sz;
  let len = S.len s;
  Seq.slice_length v;
  while (
    let res = !pres;
    if res {
      let i = !pi;
      SZ.lt i len
    } else {
      false
    }
  ) invariant cont . exists* res i .
    pts_to s #p v **
    pts_to pres res **
    pts_to pi i **
    pure (
      SZ.v i <= Seq.length v /\
      correct v == (res && correct (Seq.slice v (SZ.v i) (Seq.length v))) /\
      cont == (res && SZ.v i < Seq.length v)
    )
  {
    impl_fetch_utf8_correct s len pi pres;
    ()
  };
  !pres
}

#pop-options

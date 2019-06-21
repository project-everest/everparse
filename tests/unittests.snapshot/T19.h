/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -I ../../src/lowparse -skip-compilation -tmpdir ../unittests.snapshot -bundle LowParse.\* -drop FStar.Tactics.\* -drop FStar.Reflection.\* T10.fst T11.fst T11_z.fst T12.fst T12_z.fst T13.fst T13_x.fst T14.fst T14_x.fst T15_body.fst T15.fst T16.fst T16_x.fst T17.fst T17_x_a.fst T17_x_b.fst T18.fst T18_x_a.fst T18_x_b.fst T19.fst T1.fst T20.fst T21.fst T22_body_a.fst T22_body_b.fst T22.fst T23.fst T24.fst T24_y.fst T25_bpayload.fst T25.fst T25_payload.fst T26.fst T27.fst T28.fst T29.fst T2.fst T30.fst T31.fst T32.fst T33.fst T34.fst T35.fst T36.fst T3.fst T4.fst T5.fst T6.fst T6le.fst T7.fst T8.fst T8_z.fst T9_b.fst T9.fst Tag2.fst Tag.fst Tagle.fst -warn-error +9
  F* version: 74c6d2a5
  KreMLin version: 1bd260eb
 */

#include "kremlib.h"
#ifndef __T19_H
#define __T19_H

#include "LowParse.h"
#include "T13.h"
#include "Tag.h"


#define T19_X_a 0
#define T19_X_b 1

typedef uint8_t T19_t19__tags;

typedef struct T19_t19__s
{
  T19_t19__tags tag;
  T13_t13 _0;
}
T19_t19_;

bool T19_uu___is_X_a(T19_t19_ projectee);

bool T19_uu___is_X_b(T19_t19_ projectee);

T13_t13 T19___proj__X_b__item___0(T19_t19_ projectee);

Tag_tag T19_tag_of_t19(T19_t19_ x);

uint32_t T19_t19_validator(Tag_tag k, LowParse_Slice_slice input, uint32_t pos);

uint32_t T19_t19_jumper(Tag_tag k, LowParse_Slice_slice input, uint32_t pos);

#define __T19_H_DEFINED
#endif

/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -I ../../src/lowparse -skip-compilation -tmpdir ../unittests.snapshot -bundle LowParse.\* -drop FStar.Tactics.\* -drop FStar.Reflection.\* T10.fst T11.fst T11_z.fst T12.fst T12_z.fst T13.fst T13_x.fst T14.fst T14_x.fst T15_body.fst T15.fst T16.fst T16_x.fst T17.fst T17_x_a.fst T17_x_b.fst T18.fst T18_x_a.fst T18_x_b.fst T19.fst T1.fst T20.fst T21.fst T22_body_a.fst T22_body_b.fst T22.fst T23.fst T24.fst T24_y.fst T25_bpayload.fst T25.fst T25_payload.fst T26.fst T27.fst T28.fst T29.fst T2.fst T30.fst T31.fst T32.fst T33.fst T34.fst T35.fst T36.fst T3.fst T4.fst T5.fst T6.fst T6le.fst T7.fst T8.fst T8_z.fst T9_b.fst T9.fst Tag2.fst Tag.fst Tagle.fst -warn-error +9
  F* version: 74c6d2a5
  KreMLin version: 1bd260eb
 */

#include "T7.h"

bool T7_uu___is_Body_x(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_x)
    return true;
  else
    return false;
}

FStar_Bytes_bytes T7___proj__Body_x__item___0(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_x)
    return projectee.case_Body_x;
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool T7_uu___is_Body_y(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_y)
    return true;
  else
    return false;
}

Prims_list__FStar_Bytes_bytes *T7___proj__Body_y__item___0(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_y)
    return projectee.case_Body_y;
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool T7_uu___is_Body_w(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_w)
    return true;
  else
    return false;
}

bool T7_uu___is_Body_v(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_v)
    return true;
  else
    return false;
}

Prims_list__FStar_Bytes_bytes *T7___proj__Body_v__item___0(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_v)
    return projectee.case_Body_v;
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool T7_uu___is_Body_t(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_t)
    return true;
  else
    return false;
}

Prims_list__FStar_Bytes_bytes *T7___proj__Body_t__item___0(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_t)
    return projectee.case_Body_t;
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool T7_uu___is_Body_z(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_z)
    return true;
  else
    return false;
}

Prims_list__FStar_Bytes_bytes *T7___proj__Body_z__item___0(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_z)
    return projectee.case_Body_z;
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool T7_uu___is_Body_Unknown_tag2(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_Unknown_tag2)
    return true;
  else
    return false;
}

uint8_t T7___proj__Body_Unknown_tag2__item__v(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_Unknown_tag2)
    return projectee.case_Body_Unknown_tag2.v;
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

Prims_list__FStar_Bytes_bytes *T7___proj__Body_Unknown_tag2__item__x(T7_t7 projectee)
{
  if (projectee.tag == T7_Body_Unknown_tag2)
    return projectee.case_Body_Unknown_tag2.x;
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

Tag2_tag2 T7_tag_of_t7(T7_t7 x)
{
  if (x.tag == T7_Body_x)
    return ((Tag2_tag2){ .tag = Tag2_X });
  else if (x.tag == T7_Body_y)
    return ((Tag2_tag2){ .tag = Tag2_Y });
  else if (x.tag == T7_Body_w)
    return ((Tag2_tag2){ .tag = Tag2_W });
  else if (x.tag == T7_Body_v)
    return ((Tag2_tag2){ .tag = Tag2_V });
  else if (x.tag == T7_Body_t)
    return ((Tag2_tag2){ .tag = Tag2_T });
  else if (x.tag == T7_Body_z)
    return ((Tag2_tag2){ .tag = Tag2_Z });
  else if (x.tag == T7_Body_Unknown_tag2)
  {
    uint8_t v1 = x.case_Body_Unknown_tag2.v;
    return ((Tag2_tag2){ .tag = Tag2_Unknown_tag2, ._0 = v1 });
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint32_t T7_t7_validator(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t pos_after_tag;
  if (input.len - pos < (uint32_t)1U)
    pos_after_tag = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    pos_after_tag = pos + (uint32_t)1U;
  if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < pos_after_tag)
    return pos_after_tag;
  else
  {
    uint8_t tg = LowParse_Low_Int_read_u8(input, pos);
    if (tg == (uint8_t)0U)
      return T3_t3_validator(input, pos_after_tag);
    else if (tg == (uint8_t)1U)
      return T4_t4_validator(input, pos_after_tag);
    else if (tg == (uint8_t)2U)
      return T2_t2_validator(input, pos_after_tag);
    else if (tg == (uint8_t)3U)
      return T2_t2_validator(input, pos_after_tag);
    else if (tg == (uint8_t)4U)
      return T2_t2_validator(input, pos_after_tag);
    else if (tg == (uint8_t)5U)
      if (input.len - pos_after_tag < (uint32_t)0U)
        return LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      else
        return pos_after_tag + (uint32_t)0U;
    else
      return T2_t2_validator(input, pos_after_tag);
  }
}

uint32_t T7_t7_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t pos_after_tag = pos + (uint32_t)1U;
  uint8_t tg = LowParse_Low_Int_read_u8(input, pos);
  if (tg == (uint8_t)0U)
    return T3_t3_jumper(input, pos_after_tag);
  else if (tg == (uint8_t)1U)
    return T4_t4_jumper(input, pos_after_tag);
  else if (tg == (uint8_t)2U)
    return T2_t2_jumper(input, pos_after_tag);
  else if (tg == (uint8_t)3U)
    return T2_t2_jumper(input, pos_after_tag);
  else if (tg == (uint8_t)4U)
    return T2_t2_jumper(input, pos_after_tag);
  else if (tg == (uint8_t)5U)
    return pos_after_tag + (uint32_t)0U;
  else
    return T2_t2_jumper(input, pos_after_tag);
}

uint32_t T7_t7_accessor_x(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)1U;
}

uint32_t T7_t7_accessor_y(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)1U;
}

uint32_t T7_t7_accessor_v(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)1U;
}

uint32_t T7_t7_accessor_t(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)1U;
}

uint32_t T7_t7_accessor_z(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)1U;
}

uint32_t T7_t7_accessor_Unknown(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)1U;
}

void T7_finalize_t7_Unknown_tag2(uint8_t v1, LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t pos1 = LowParse_Low_Int_write_u8(v1, input, pos);
}


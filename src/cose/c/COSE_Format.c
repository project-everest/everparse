

#include "internal/COSE_Format.h"

#include "CBORDetAPI.h"
#include "internal/fstar.h"

#define CDDL_SIMPLE_VALUE_FALSE (20U)

#define CDDL_SIMPLE_VALUE_TRUE (21U)

static bool sizet_lte_u64(size_t b, uint64_t a)
{
  return
    !(b / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U >= (size_t)16U) &&
      b <= a;
}

static bool u64_lte_sizet(uint64_t a, size_t b)
{
  return
    b / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U >= (size_t)16U || a <= b;
}

static bool sizet_fits_u64(size_t b)
{
  return b / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U < (size_t)16U;
}

static bool sizet_eq_u64(size_t b, uint64_t a)
{
  return
    !(b / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U >= (size_t)16U) &&
      b == a;
}

typedef enum { MGOK, MGFail, MGCutFail } impl_map_group_result;

#define SIMPLE_VALUE_TRUE (21U)

#define SIMPLE_VALUE_FALSE (20U)

bool COSE_Format_validate_bool(cbor_det_t c)
{
  bool ite;
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    ite = cbor_det_read_simple_value(c) == CDDL_SIMPLE_VALUE_FALSE;
  else
    ite = false;
  if (ite)
    return true;
  else if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return cbor_det_read_simple_value(c) == CDDL_SIMPLE_VALUE_TRUE;
  else
    return false;
}

bool COSE_Format_evercddl_bool_right(bool x1)
{
  return x1;
}

bool COSE_Format_evercddl_bool_left(bool x4)
{
  return x4;
}

/**
Parser for evercddl_bool
*/
bool COSE_Format_parse_bool(cbor_det_t c)
{
  return cbor_det_read_simple_value(c) == SIMPLE_VALUE_TRUE;
}

size_t Pulse_Lib_Slice_len__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.len;
}

uint8_t *Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.elt;
}

typedef struct option__size_t_s
{
  FStar_Pervasives_Native_option__size_t_tags tag;
  size_t v;
}
option__size_t;

/**
Serializer for evercddl_bool
*/
size_t COSE_Format_serialize_bool(bool c, Pulse_Lib_Slice_slice__uint8_t out)
{
  if (c)
    if
    (
      SIMPLE_VALUE_TRUE <= MAX_SIMPLE_VALUE_ADDITIONAL_INFO ||
        MIN_SIMPLE_VALUE_LONG_ARGUMENT <= SIMPLE_VALUE_TRUE
    )
    {
      cbor_det_t x = cbor_det_mk_simple_value(SIMPLE_VALUE_TRUE);
      size_t len = cbor_det_size(x, Pulse_Lib_Slice_len__uint8_t(out));
      option__size_t scrut;
      if (len > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(x, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
            }
          );
      else
        scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      if (scrut.tag == FStar_Pervasives_Native_None)
        return (size_t)0U;
      else if (scrut.tag == FStar_Pervasives_Native_Some)
        return scrut.v;
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    else
      return (size_t)0U;
  else if
  (
    SIMPLE_VALUE_FALSE <= MAX_SIMPLE_VALUE_ADDITIONAL_INFO ||
      MIN_SIMPLE_VALUE_LONG_ARGUMENT <= SIMPLE_VALUE_FALSE
  )
  {
    cbor_det_t x = cbor_det_mk_simple_value(SIMPLE_VALUE_FALSE);
    size_t len = cbor_det_size(x, Pulse_Lib_Slice_len__uint8_t(out));
    option__size_t scrut;
    if (len > (size_t)0U)
      scrut =
        (
          (option__size_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = cbor_det_serialize(x, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
          }
        );
    else
      scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
    if (scrut.tag == FStar_Pervasives_Native_None)
      return (size_t)0U;
    else if (scrut.tag == FStar_Pervasives_Native_Some)
      return scrut.v;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else
    return (size_t)0U;
}

static FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
split__uint8_t(Pulse_Lib_Slice_slice__uint8_t s, size_t i)
{
  return
    (
      (FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
        ._1 = { .elt = s.elt, .len = i },
        ._2 = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__bool_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_bool(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__bool_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_bool(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__bool_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_bool(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__bool_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_everparsenomatch(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return false;
}

void COSE_Format_everparsenomatch_right(void)
{

}

/**
Parser for everparsenomatch
*/
void COSE_Format_parse_everparsenomatch(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_everparsenomatch_right();
}

/**
Serializer for everparsenomatch
*/
size_t COSE_Format_serialize_everparsenomatch(Pulse_Lib_Slice_slice__uint8_t out)
{
  KRML_MAYBE_UNUSED_VAR(out);
  return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_everparsenomatch(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_everparsenomatch(rl))
    {
      COSE_Format_parse_everparsenomatch(rl);
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = rem
          }
        );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_any(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return true;
}

cbor_det_t COSE_Format_any_right(cbor_det_t x1)
{
  return x1;
}

cbor_det_t COSE_Format_any_left(cbor_det_t x4)
{
  return x4;
}

/**
Parser for any
*/
cbor_det_t COSE_Format_parse_any(cbor_det_t c)
{
  return c;
}

/**
Serializer for any
*/
size_t COSE_Format_serialize_any(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  size_t len = cbor_det_size(c, Pulse_Lib_Slice_len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
        }
      );
  else
    scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (scrut.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (scrut.tag == FStar_Pervasives_Native_Some)
    return scrut.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_any(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_any(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = rl, ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_undefined(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return cbor_det_read_simple_value(c) == 23U;
  else
    return false;
}

void COSE_Format_undefined_right(void)
{

}

/**
Parser for undefined
*/
void COSE_Format_parse_undefined(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_undefined_right();
}

/**
Serializer for undefined
*/
size_t COSE_Format_serialize_undefined(Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t c1 = cbor_det_mk_simple_value(23U);
  size_t len = cbor_det_size(c1, Pulse_Lib_Slice_len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c1, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
        }
      );
  else
    scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (scrut.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (scrut.tag == FStar_Pervasives_Native_Some)
    return scrut.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_undefined(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_undefined(rl))
    {
      COSE_Format_parse_undefined(rl);
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = rem
          }
        );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_nil(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return cbor_det_read_simple_value(c) == 22U;
  else
    return false;
}

void COSE_Format_nil_right(void)
{

}

/**
Parser for nil
*/
void COSE_Format_parse_nil(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_nil_right();
}

/**
Serializer for nil
*/
size_t COSE_Format_serialize_nil(Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t c1 = cbor_det_mk_simple_value(22U);
  size_t len = cbor_det_size(c1, Pulse_Lib_Slice_len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c1, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
        }
      );
  else
    scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (scrut.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (scrut.tag == FStar_Pervasives_Native_Some)
    return scrut.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_nil(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_nil(rl))
    {
      COSE_Format_parse_nil(rl);
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = rem
          }
        );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_null(cbor_det_t c)
{
  return COSE_Format_validate_nil(c);
}

void COSE_Format_evercddl_null_right(void)
{

}

void COSE_Format_evercddl_null_left(void)
{

}

/**
Parser for evercddl_null
*/
void COSE_Format_parse_null(cbor_det_t c)
{
  COSE_Format_parse_nil(c);
  COSE_Format_evercddl_null_right();
}

/**
Serializer for evercddl_null
*/
size_t COSE_Format_serialize_null(Pulse_Lib_Slice_slice__uint8_t out)
{
  return COSE_Format_serialize_nil(out);
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_null(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_null(rl))
    {
      COSE_Format_parse_null(rl);
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = rem
          }
        );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_true(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return cbor_det_read_simple_value(c) == 21U;
  else
    return false;
}

void COSE_Format_evercddl_true_right(void)
{

}

/**
Parser for evercddl_true
*/
void COSE_Format_parse_true(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_evercddl_true_right();
}

/**
Serializer for evercddl_true
*/
size_t COSE_Format_serialize_true(Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t c1 = cbor_det_mk_simple_value(21U);
  size_t len = cbor_det_size(c1, Pulse_Lib_Slice_len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c1, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
        }
      );
  else
    scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (scrut.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (scrut.tag == FStar_Pervasives_Native_Some)
    return scrut.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_true(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_true(rl))
    {
      COSE_Format_parse_true(rl);
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = rem
          }
        );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_false(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return cbor_det_read_simple_value(c) == 20U;
  else
    return false;
}

void COSE_Format_evercddl_false_right(void)
{

}

/**
Parser for evercddl_false
*/
void COSE_Format_parse_false(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_evercddl_false_right();
}

/**
Serializer for evercddl_false
*/
size_t COSE_Format_serialize_false(Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t c1 = cbor_det_mk_simple_value(20U);
  size_t len = cbor_det_size(c1, Pulse_Lib_Slice_len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c1, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
        }
      );
  else
    scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (scrut.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (scrut.tag == FStar_Pervasives_Native_Some)
    return scrut.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_false(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_false(rl))
    {
      COSE_Format_parse_false(rl);
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = rem
          }
        );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2_____Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_tstr(cbor_det_t c)
{
  return cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TEXT_STRING;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_tstr_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_tstr_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

static Pulse_Lib_Slice_slice__uint8_t arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

/**
Parser for tstr
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_tstr(cbor_det_t c)
{
  uint64_t len = cbor_det_get_string_length(c);
  return arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len);
}

/**
Serializer for tstr
*/
size_t
COSE_Format_serialize_tstr(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  if (sizet_lte_u64(Pulse_Lib_Slice_len__uint8_t(c), 18446744073709551615ULL))
  {
    size_t alen = Pulse_Lib_Slice_len__uint8_t(c);
    if
    (
      cbor_det_impl_utf8_correct_from_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c),
        alen)
    )
    {
      uint8_t *a1 = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c);
      cbor_det_t pres = dummy_cbor_det_t();
      bool ite;
      if (CBOR_MAJOR_TYPE_TEXT_STRING == CBOR_MAJOR_TYPE_BYTE_STRING)
        ite =
          cbor_det_mk_byte_string_from_arrayptr(a1,
            (uint64_t)Pulse_Lib_Slice_len__uint8_t(c),
            &pres);
      else
        ite =
          cbor_det_mk_text_string_from_arrayptr(a1,
            (uint64_t)Pulse_Lib_Slice_len__uint8_t(c),
            &pres);
      KRML_MAYBE_UNUSED_VAR(ite);
      cbor_det_t x = pres;
      size_t len1 = cbor_det_size(x, Pulse_Lib_Slice_len__uint8_t(out));
      option__size_t scrut;
      if (len1 > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(x,
                Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
                len1)
            }
          );
      else
        scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      if (scrut.tag == FStar_Pervasives_Native_None)
        return (size_t)0U;
      else if (scrut.tag == FStar_Pervasives_Native_Some)
        return scrut.v;
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    else
      return (size_t)0U;
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_tstr(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_tstr(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_tstr(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_bstr(cbor_det_t c)
{
  return cbor_det_major_type(c) == CBOR_MAJOR_TYPE_BYTE_STRING;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_bstr_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_bstr_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for bstr
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_bstr(cbor_det_t c)
{
  uint64_t len = cbor_det_get_string_length(c);
  return arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len);
}

/**
Serializer for bstr
*/
size_t
COSE_Format_serialize_bstr(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  if (sizet_lte_u64(Pulse_Lib_Slice_len__uint8_t(c), 18446744073709551615ULL))
  {
    uint8_t *a = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c);
    cbor_det_t pres = dummy_cbor_det_t();
    cbor_det_mk_byte_string_from_arrayptr(a, (uint64_t)Pulse_Lib_Slice_len__uint8_t(c), &pres);
    cbor_det_t x = pres;
    size_t len1 = cbor_det_size(x, Pulse_Lib_Slice_len__uint8_t(out));
    option__size_t scrut;
    if (len1 > (size_t)0U)
      scrut =
        (
          (option__size_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = cbor_det_serialize(x, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len1)
          }
        );
    else
      scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
    if (scrut.tag == FStar_Pervasives_Native_None)
      return (size_t)0U;
    else if (scrut.tag == FStar_Pervasives_Native_Some)
      return scrut.v;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_bstr(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_bstr(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_bstr(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_bytes(cbor_det_t c)
{
  return COSE_Format_validate_bstr(c);
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_bytes_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_bytes_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for bytes
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_bytes(cbor_det_t c)
{
  return COSE_Format_parse_bstr(c);
}

/**
Serializer for bytes
*/
size_t
COSE_Format_serialize_bytes(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_bstr(c, out);
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_bytes(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_bytes(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_bytes(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_text(cbor_det_t c)
{
  return COSE_Format_validate_tstr(c);
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_text_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_text_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for text
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_text(cbor_det_t c)
{
  return COSE_Format_parse_tstr(c);
}

/**
Serializer for text
*/
size_t
COSE_Format_serialize_text(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_tstr(c, out);
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_text(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_text(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_text(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_nint(cbor_det_t c)
{
  return cbor_det_major_type(c) == CBOR_MAJOR_TYPE_NEG_INT64;
}

uint64_t COSE_Format_nint_right(uint64_t x1)
{
  return x1;
}

uint64_t COSE_Format_nint_left(uint64_t x4)
{
  return x4;
}

/**
Parser for nint
*/
uint64_t COSE_Format_parse_nint(cbor_det_t c)
{
  return cbor_det_read_uint64(c);
}

/**
Serializer for nint
*/
size_t COSE_Format_serialize_nint(uint64_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t x = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, c);
  size_t len = cbor_det_size(x, Pulse_Lib_Slice_len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(x, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
        }
      );
  else
    scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (scrut.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (scrut.tag == FStar_Pervasives_Native_Some)
    return scrut.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__uint64_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_nint(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__uint64_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_nint(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__uint64_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_nint(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__uint64_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_uint(cbor_det_t c)
{
  return cbor_det_major_type(c) == CBOR_MAJOR_TYPE_UINT64;
}

uint64_t COSE_Format_evercddl_uint_right(uint64_t x1)
{
  return x1;
}

uint64_t COSE_Format_evercddl_uint_left(uint64_t x4)
{
  return x4;
}

/**
Parser for evercddl_uint
*/
uint64_t COSE_Format_parse_uint(cbor_det_t c)
{
  return cbor_det_read_uint64(c);
}

/**
Serializer for evercddl_uint
*/
size_t COSE_Format_serialize_uint(uint64_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t x = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, c);
  size_t len = cbor_det_size(x, Pulse_Lib_Slice_len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(x, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
        }
      );
  else
    scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (scrut.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (scrut.tag == FStar_Pervasives_Native_Some)
    return scrut.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__uint64_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_uint(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__uint64_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_uint(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__uint64_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_uint(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__uint64_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_int(cbor_det_t c)
{
  if (COSE_Format_validate_uint(c))
    return true;
  else
    return COSE_Format_validate_nint(c);
}

COSE_Format_evercddl_int COSE_Format_evercddl_int_right(COSE_Format_evercddl_int_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return
      (
        (COSE_Format_evercddl_int){
          .tag = COSE_Format_Mkevercddl_int0,
          { .case_Mkevercddl_int0 = x2.case_Inl }
        }
      );
  else if (x2.tag == COSE_Format_Inr)
    return
      (
        (COSE_Format_evercddl_int){
          .tag = COSE_Format_Mkevercddl_int1,
          { .case_Mkevercddl_int1 = x2.case_Inr }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

COSE_Format_evercddl_int_ugly COSE_Format_evercddl_int_left(COSE_Format_evercddl_int x8)
{
  if (x8.tag == COSE_Format_Mkevercddl_int0)
    return
      (
        (COSE_Format_evercddl_int_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = x8.case_Mkevercddl_int0 }
        }
      );
  else if (x8.tag == COSE_Format_Mkevercddl_int1)
    return
      (
        (COSE_Format_evercddl_int_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = x8.case_Mkevercddl_int1 }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

/**
Parser for evercddl_int
*/
COSE_Format_evercddl_int COSE_Format_parse_int(cbor_det_t c)
{
  COSE_Format_evercddl_int_ugly ite;
  if (COSE_Format_validate_uint(c))
    ite =
      (
        (COSE_Format_evercddl_int_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_uint(c) }
        }
      );
  else
    ite =
      (
        (COSE_Format_evercddl_int_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_nint(c) }
        }
      );
  return COSE_Format_evercddl_int_right(ite);
}

/**
Serializer for evercddl_int
*/
size_t
COSE_Format_serialize_int(COSE_Format_evercddl_int c, Pulse_Lib_Slice_slice__uint8_t out)
{
  COSE_Format_evercddl_int_ugly scrut = COSE_Format_evercddl_int_left(c);
  if (scrut.tag == COSE_Format_Inl)
    return COSE_Format_serialize_uint(scrut.case_Inl, out);
  else if (scrut.tag == COSE_Format_Inr)
    return COSE_Format_serialize_nint(scrut.case_Inr, out);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_int(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_int(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_int(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_cborany(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (55799ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_any(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

cbor_det_t COSE_Format_cborany_right(cbor_det_t x1)
{
  return x1;
}

cbor_det_t COSE_Format_cborany_left(cbor_det_t x4)
{
  return x4;
}

/**
Parser for cborany
*/
cbor_det_t COSE_Format_parse_cborany(cbor_det_t c)
{
  return cbor_det_get_tagged_payload(c);
}

/**
Serializer for cborany
*/
size_t COSE_Format_serialize_cborany(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(55799ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_any(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cborany(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cborany(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cborany(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_mimemessage(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (36ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_tstr(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_mimemessage_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_mimemessage_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for mimemessage
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_mimemessage(cbor_det_t c)
{
  return COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c));
}

/**
Serializer for mimemessage
*/
size_t
COSE_Format_serialize_mimemessage(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  Pulse_Lib_Slice_slice__uint8_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(36ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_mimemessage(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_mimemessage(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_mimemessage(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_regexp(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (35ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_tstr(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_regexp_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_regexp_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for regexp
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_regexp(cbor_det_t c)
{
  return COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c));
}

/**
Serializer for regexp
*/
size_t
COSE_Format_serialize_regexp(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  Pulse_Lib_Slice_slice__uint8_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(35ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_regexp(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_regexp(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_regexp(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_b64legacy(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (34ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_tstr(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_b64legacy_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_b64legacy_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for b64legacy
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_b64legacy(cbor_det_t c)
{
  return COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c));
}

/**
Serializer for b64legacy
*/
size_t
COSE_Format_serialize_b64legacy(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  Pulse_Lib_Slice_slice__uint8_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(34ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_b64legacy(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_b64legacy(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_b64legacy(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_b64url(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (33ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_tstr(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_b64url_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_b64url_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for b64url
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_b64url(cbor_det_t c)
{
  return COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c));
}

/**
Serializer for b64url
*/
size_t
COSE_Format_serialize_b64url(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  Pulse_Lib_Slice_slice__uint8_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(33ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_b64url(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_b64url(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_b64url(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_uri(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (32ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_tstr(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_uri_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_uri_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for uri
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_uri(cbor_det_t c)
{
  return COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c));
}

/**
Serializer for uri
*/
size_t
COSE_Format_serialize_uri(Pulse_Lib_Slice_slice__uint8_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  Pulse_Lib_Slice_slice__uint8_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(32ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_uri(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_uri(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_uri(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_encodedcbor(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (24ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_bstr(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_encodedcbor_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_encodedcbor_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for encodedcbor
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_encodedcbor(cbor_det_t c)
{
  return COSE_Format_parse_bstr(cbor_det_get_tagged_payload(c));
}

/**
Serializer for encodedcbor
*/
size_t
COSE_Format_serialize_encodedcbor(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  Pulse_Lib_Slice_slice__uint8_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(24ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_bstr(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_encodedcbor(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_encodedcbor(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_encodedcbor(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_eb16(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (23ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_any(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

cbor_det_t COSE_Format_eb16_right(cbor_det_t x1)
{
  return x1;
}

cbor_det_t COSE_Format_eb16_left(cbor_det_t x4)
{
  return x4;
}

/**
Parser for eb16
*/
cbor_det_t COSE_Format_parse_eb16(cbor_det_t c)
{
  return cbor_det_get_tagged_payload(c);
}

/**
Serializer for eb16
*/
size_t COSE_Format_serialize_eb16(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(23ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_any(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_eb16(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_eb16(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_eb16(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_eb64legacy(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (22ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_any(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

cbor_det_t COSE_Format_eb64legacy_right(cbor_det_t x1)
{
  return x1;
}

cbor_det_t COSE_Format_eb64legacy_left(cbor_det_t x4)
{
  return x4;
}

/**
Parser for eb64legacy
*/
cbor_det_t COSE_Format_parse_eb64legacy(cbor_det_t c)
{
  return cbor_det_get_tagged_payload(c);
}

/**
Serializer for eb64legacy
*/
size_t COSE_Format_serialize_eb64legacy(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(22ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_any(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_eb64legacy(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_eb64legacy(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_eb64legacy(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_eb64url(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (21ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_any(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

cbor_det_t COSE_Format_eb64url_right(cbor_det_t x1)
{
  return x1;
}

cbor_det_t COSE_Format_eb64url_left(cbor_det_t x4)
{
  return x4;
}

/**
Parser for eb64url
*/
cbor_det_t COSE_Format_parse_eb64url(cbor_det_t c)
{
  return cbor_det_get_tagged_payload(c);
}

/**
Serializer for eb64url
*/
size_t COSE_Format_serialize_eb64url(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(21ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_any(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_eb64url(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_eb64url(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_eb64url(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_number(cbor_det_t c)
{
  return COSE_Format_validate_int(c);
}

COSE_Format_evercddl_int COSE_Format_number_right(COSE_Format_evercddl_int x1)
{
  return x1;
}

COSE_Format_evercddl_int COSE_Format_number_left(COSE_Format_evercddl_int x4)
{
  return x4;
}

/**
Parser for number
*/
COSE_Format_evercddl_int COSE_Format_parse_number(cbor_det_t c)
{
  return COSE_Format_parse_int(c);
}

/**
Serializer for number
*/
size_t
COSE_Format_serialize_number(COSE_Format_evercddl_int c, Pulse_Lib_Slice_slice__uint8_t out)
{
  return COSE_Format_serialize_int(c, out);
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_number(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_number(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_number(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_tdate(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (0ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_tstr(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_tdate_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t COSE_Format_tdate_left(Pulse_Lib_Slice_slice__uint8_t x4)
{
  return x4;
}

/**
Parser for tdate
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_tdate(cbor_det_t c)
{
  return COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c));
}

/**
Serializer for tdate
*/
size_t
COSE_Format_serialize_tdate(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  Pulse_Lib_Slice_slice__uint8_t cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(0ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_tdate(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_tdate(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_tdate(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_values(cbor_det_t c)
{
  return COSE_Format_validate_any(c);
}

cbor_det_t COSE_Format_values_right(cbor_det_t x1)
{
  return x1;
}

cbor_det_t COSE_Format_values_left(cbor_det_t x4)
{
  return x4;
}

/**
Parser for values
*/
cbor_det_t COSE_Format_parse_values(cbor_det_t c)
{
  return c;
}

/**
Serializer for values
*/
size_t COSE_Format_serialize_values(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  return COSE_Format_serialize_any(c, out);
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_values(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_values(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_values(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_evercddl_label(cbor_det_t c)
{
  if (COSE_Format_validate_int(c))
    return true;
  else
    return COSE_Format_validate_tstr(c);
}

COSE_Format_evercddl_label COSE_Format_evercddl_label_right(COSE_Format_evercddl_label_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return
      (
        (COSE_Format_evercddl_label){
          .tag = COSE_Format_Mkevercddl_label0,
          { .case_Mkevercddl_label0 = x2.case_Inl }
        }
      );
  else if (x2.tag == COSE_Format_Inr)
    return
      (
        (COSE_Format_evercddl_label){
          .tag = COSE_Format_Mkevercddl_label1,
          { .case_Mkevercddl_label1 = x2.case_Inr }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

COSE_Format_evercddl_label_ugly COSE_Format_evercddl_label_left(COSE_Format_evercddl_label x8)
{
  if (x8.tag == COSE_Format_Mkevercddl_label0)
    return
      (
        (COSE_Format_evercddl_label_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = x8.case_Mkevercddl_label0 }
        }
      );
  else if (x8.tag == COSE_Format_Mkevercddl_label1)
    return
      (
        (COSE_Format_evercddl_label_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = x8.case_Mkevercddl_label1 }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

/**
Parser for evercddl_label
*/
COSE_Format_evercddl_label COSE_Format_parse_evercddl_label(cbor_det_t c)
{
  COSE_Format_evercddl_label_ugly ite;
  if (COSE_Format_validate_int(c))
    ite =
      (
        (COSE_Format_evercddl_label_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_int(c) }
        }
      );
  else
    ite =
      (
        (COSE_Format_evercddl_label_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_tstr(c) }
        }
      );
  return COSE_Format_evercddl_label_right(ite);
}

/**
Serializer for evercddl_label
*/
size_t
COSE_Format_serialize_evercddl_label(
  COSE_Format_evercddl_label c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_label_ugly scrut = COSE_Format_evercddl_label_left(c);
  if (scrut.tag == COSE_Format_Inl)
    return COSE_Format_serialize_int(scrut.case_Inl, out);
  else if (scrut.tag == COSE_Format_Inr)
    return COSE_Format_serialize_tstr(scrut.case_Inr, out);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_evercddl_label(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_evercddl_label(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_evercddl_label(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_aux_env29_validate_1(cbor_det_array_iterator_t *pi)
{
  if (cbor_det_array_iterator_is_empty(pi[0U]))
    return false;
  else
  {
    cbor_det_t c = cbor_det_array_iterator_next(pi);
    if (COSE_Format_validate_tstr(c))
      return true;
    else
      return COSE_Format_validate_int(c);
  }
}

COSE_Format_aux_env29_type_1
COSE_Format_aux_env29_type_1_right(COSE_Format_aux_env29_type_1_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return
      (
        (COSE_Format_aux_env29_type_1){
          .tag = COSE_Format_Mkaux_env29_type_10,
          { .case_Mkaux_env29_type_10 = x2.case_Inl }
        }
      );
  else if (x2.tag == COSE_Format_Inr)
    return
      (
        (COSE_Format_aux_env29_type_1){
          .tag = COSE_Format_Mkaux_env29_type_11,
          { .case_Mkaux_env29_type_11 = x2.case_Inr }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

COSE_Format_aux_env29_type_1_ugly
COSE_Format_aux_env29_type_1_left(COSE_Format_aux_env29_type_1 x8)
{
  if (x8.tag == COSE_Format_Mkaux_env29_type_10)
    return
      (
        (COSE_Format_aux_env29_type_1_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = x8.case_Mkaux_env29_type_10 }
        }
      );
  else if (x8.tag == COSE_Format_Mkaux_env29_type_11)
    return
      (
        (COSE_Format_aux_env29_type_1_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = x8.case_Mkaux_env29_type_11 }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

/**
Parser for aux_env29_type_1
*/
COSE_Format_aux_env29_type_1 COSE_Format_aux_env29_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t buf = c;
  cbor_det_t x = cbor_det_array_iterator_next(&buf);
  COSE_Format_aux_env29_type_1_ugly ite;
  if (COSE_Format_validate_tstr(x))
    ite =
      (
        (COSE_Format_aux_env29_type_1_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_tstr(x) }
        }
      );
  else
    ite =
      (
        (COSE_Format_aux_env29_type_1_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_int(x) }
        }
      );
  return COSE_Format_aux_env29_type_1_right(ite);
}

/**
Serializer for aux_env29_type_1
*/
bool
COSE_Format_aux_env29_serialize_1(
  COSE_Format_aux_env29_type_1 c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  uint64_t count = out_count[0U];
  if (count < 18446744073709551615ULL)
  {
    size_t size = out_size[0U];
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size)._2;
    COSE_Format_aux_env29_type_1_ugly scrut = COSE_Format_aux_env29_type_1_left(c);
    size_t size1;
    if (scrut.tag == COSE_Format_Inl)
      size1 = COSE_Format_serialize_tstr(scrut.case_Inl, out1);
    else if (scrut.tag == COSE_Format_Inr)
      size1 = COSE_Format_serialize_int(scrut.case_Inr, out1);
    else
      size1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
    if (size1 == (size_t)0U)
      return false;
    else
    {
      out_count[0U] = count + 1ULL;
      out_size[0U] = size + size1;
      return true;
    }
  }
  else
    return false;
}

bool COSE_Format_aux_env29_map_constraint_2(cbor_det_map_entry_t x)
{
  cbor_det_t k = cbor_det_map_entry_key(x);
  bool ite0;
  if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
    ite0 = cbor_det_read_uint64(k) == 1ULL;
  else
    ite0 = false;
  bool ite1;
  if (ite0)
  {
    cbor_det_map_entry_value(x);
    ite1 = true;
  }
  else
    ite1 = false;
  bool ite2;
  if (ite1)
    ite2 = true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k1) == 2ULL;
    else
      ite = false;
    if (ite)
      ite2 = COSE_Format_validate_bstr(cbor_det_map_entry_value(x));
    else
      ite2 = false;
  }
  bool ite3;
  if (ite2)
    ite3 = true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k1) == 3ULL;
    else
      ite = false;
    if (ite)
    {
      cbor_det_t v = cbor_det_map_entry_value(x);
      if (COSE_Format_validate_tstr(v))
        ite3 = true;
      else
        ite3 = COSE_Format_validate_int(v);
    }
    else
      ite3 = false;
  }
  bool ite4;
  if (ite3)
    ite4 = true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite0;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
      ite0 = cbor_det_read_uint64(k1) == 4ULL;
    else
      ite0 = false;
    if (ite0)
    {
      cbor_det_t v = cbor_det_map_entry_value(x);
      if (cbor_det_major_type(v) == CBOR_MAJOR_TYPE_ARRAY)
      {
        cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(v);
        bool ite0;
        if (cbor_det_array_iterator_is_empty(pi))
          ite0 = false;
        else
        {
          cbor_det_t c = cbor_det_array_iterator_next(&pi);
          if (COSE_Format_validate_tstr(c))
            ite0 = true;
          else
            ite0 = COSE_Format_validate_int(c);
        }
        bool ite1;
        if (ite0)
        {
          bool pcont = true;
          while (pcont)
          {
            cbor_det_array_iterator_t i11 = pi;
            bool ite;
            if (cbor_det_array_iterator_is_empty(pi))
              ite = false;
            else
            {
              cbor_det_t c = cbor_det_array_iterator_next(&pi);
              if (COSE_Format_validate_tstr(c))
                ite = true;
              else
                ite = COSE_Format_validate_int(c);
            }
            if (!ite)
            {
              pi = i11;
              pcont = false;
            }
          }
          ite1 = true;
        }
        else
          ite1 = false;
        if (ite1)
          ite4 = cbor_det_array_iterator_is_empty(pi);
        else
          ite4 = false;
      }
      else
        ite4 = false;
    }
    else
      ite4 = false;
  }
  if (ite4)
    return true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k1) == 5ULL;
    else
      ite = false;
    if (ite)
      return COSE_Format_validate_bstr(cbor_det_map_entry_value(x));
    else
      return false;
  }
}

typedef struct option__CBOR_Pulse_API_Det_Type_cbor_det_t_s
{
  FStar_Pervasives_Native_option__size_t_tags tag;
  cbor_det_t v;
}
option__CBOR_Pulse_API_Det_Type_cbor_det_t;

bool COSE_Format_validate_cose_key_generic(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t remaining = cbor_det_get_map_length(c);
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest = c1;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
    if (cbor_det_map_get(c, c1, &dest))
      scrut0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest
          }
        );
    else
      scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    impl_map_group_result ite0;
    if (scrut0.tag == FStar_Pervasives_Native_None)
      ite0 = MGFail;
    else if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t cv = scrut0.v;
      bool ite;
      if (COSE_Format_validate_tstr(cv))
        ite = true;
      else
        ite = COSE_Format_validate_int(cv);
      if (ite)
      {
        remaining--;
        ite0 = MGOK;
      }
      else
        ite0 = MGFail;
    }
    else
      ite0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    impl_map_group_result sw0;
    switch (ite0)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            if (COSE_Format_validate_bstr(scrut.v))
            {
              remaining--;
              ite = MGOK;
            }
            else
              ite = MGFail;
          else
            ite =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite)
          {
            case MGOK:
              {
                sw0 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                sw0 = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw0 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw0 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw0 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw1;
    switch (sw0)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite0;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite0 = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = scrut.v;
            bool ite;
            if (COSE_Format_validate_tstr(cv))
              ite = true;
            else
              ite = COSE_Format_validate_int(cv);
            if (ite)
            {
              remaining--;
              ite0 = MGOK;
            }
            else
              ite0 = MGFail;
          }
          else
            ite0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite0)
          {
            case MGOK:
              {
                sw1 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                sw1 = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw1 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw1 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw1 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw2;
    switch (sw1)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite0;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite0 = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = scrut.v;
            bool ite1;
            if (cbor_det_major_type(cv) == CBOR_MAJOR_TYPE_ARRAY)
            {
              cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(cv);
              bool ite0;
              if (cbor_det_array_iterator_is_empty(pi))
                ite0 = false;
              else
              {
                cbor_det_t c3 = cbor_det_array_iterator_next(&pi);
                if (COSE_Format_validate_tstr(c3))
                  ite0 = true;
                else
                  ite0 = COSE_Format_validate_int(c3);
              }
              bool ite2;
              if (ite0)
              {
                bool pcont = true;
                while (pcont)
                {
                  cbor_det_array_iterator_t i11 = pi;
                  bool ite;
                  if (cbor_det_array_iterator_is_empty(pi))
                    ite = false;
                  else
                  {
                    cbor_det_t c3 = cbor_det_array_iterator_next(&pi);
                    if (COSE_Format_validate_tstr(c3))
                      ite = true;
                    else
                      ite = COSE_Format_validate_int(c3);
                  }
                  if (!ite)
                  {
                    pi = i11;
                    pcont = false;
                  }
                }
                ite2 = true;
              }
              else
                ite2 = false;
              if (ite2)
                ite1 = cbor_det_array_iterator_is_empty(pi);
              else
                ite1 = false;
            }
            else
              ite1 = false;
            if (ite1)
            {
              remaining--;
              ite0 = MGOK;
            }
            else
              ite0 = MGFail;
          }
          else
            ite0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite0)
          {
            case MGOK:
              {
                sw2 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                sw2 = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw2 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw2 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw2 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw3;
    switch (sw2)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            if (COSE_Format_validate_bstr(scrut.v))
            {
              remaining--;
              ite = MGOK;
            }
            else
              ite = MGFail;
          else
            ite =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite)
          {
            case MGOK:
              {
                sw3 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                sw3 = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw3 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw3 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw3 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw;
    switch (sw3)
    {
      case MGOK:
        {
          cbor_det_map_iterator_t pj = cbor_det_map_iterator_start(c);
          while (!cbor_det_map_iterator_is_empty(pj))
          {
            cbor_det_map_entry_t chd = cbor_det_map_iterator_next(&pj);
            bool ite0;
            if (COSE_Format_validate_evercddl_label(cbor_det_map_entry_key(chd)))
              ite0 = COSE_Format_validate_values(cbor_det_map_entry_value(chd));
            else
              ite0 = false;
            bool ite1;
            if (ite0)
            {
              cbor_det_t k1 = cbor_det_map_entry_key(chd);
              bool ite0;
              if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
                ite0 = cbor_det_read_uint64(k1) == 1ULL;
              else
                ite0 = false;
              bool ite2;
              if (ite0)
              {
                cbor_det_map_entry_value(chd);
                ite2 = true;
              }
              else
                ite2 = false;
              bool ite3;
              if (ite2)
                ite3 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k2) == 2ULL;
                else
                  ite = false;
                if (ite)
                  ite3 = COSE_Format_validate_bstr(cbor_det_map_entry_value(chd));
                else
                  ite3 = false;
              }
              bool ite4;
              if (ite3)
                ite4 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k2) == 3ULL;
                else
                  ite = false;
                if (ite)
                {
                  cbor_det_t v = cbor_det_map_entry_value(chd);
                  if (COSE_Format_validate_tstr(v))
                    ite4 = true;
                  else
                    ite4 = COSE_Format_validate_int(v);
                }
                else
                  ite4 = false;
              }
              bool ite5;
              if (ite4)
                ite5 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite0;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_UINT64)
                  ite0 = cbor_det_read_uint64(k2) == 4ULL;
                else
                  ite0 = false;
                if (ite0)
                {
                  cbor_det_t v = cbor_det_map_entry_value(chd);
                  if (cbor_det_major_type(v) == CBOR_MAJOR_TYPE_ARRAY)
                  {
                    cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(v);
                    bool ite0;
                    if (cbor_det_array_iterator_is_empty(pi))
                      ite0 = false;
                    else
                    {
                      cbor_det_t c2 = cbor_det_array_iterator_next(&pi);
                      if (COSE_Format_validate_tstr(c2))
                        ite0 = true;
                      else
                        ite0 = COSE_Format_validate_int(c2);
                    }
                    bool ite1;
                    if (ite0)
                    {
                      bool pcont = true;
                      while (pcont)
                      {
                        cbor_det_array_iterator_t i11 = pi;
                        bool ite;
                        if (cbor_det_array_iterator_is_empty(pi))
                          ite = false;
                        else
                        {
                          cbor_det_t c2 = cbor_det_array_iterator_next(&pi);
                          if (COSE_Format_validate_tstr(c2))
                            ite = true;
                          else
                            ite = COSE_Format_validate_int(c2);
                        }
                        if (!ite)
                        {
                          pi = i11;
                          pcont = false;
                        }
                      }
                      ite1 = true;
                    }
                    else
                      ite1 = false;
                    if (ite1)
                      ite5 = cbor_det_array_iterator_is_empty(pi);
                    else
                      ite5 = false;
                  }
                  else
                    ite5 = false;
                }
                else
                  ite5 = false;
              }
              bool ite6;
              if (ite5)
                ite6 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k2) == 5ULL;
                else
                  ite = false;
                if (ite)
                  ite6 = COSE_Format_validate_bstr(cbor_det_map_entry_value(chd));
                else
                  ite6 = false;
              }
              ite1 = !ite6;
            }
            else
              ite1 = false;
            if (!!ite1)
              remaining--;
          }
          sw = MGOK;
          break;
        }
      case MGFail:
        {
          sw = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (sw)
    {
      case MGOK:
        {
          return remaining == 0ULL;
        }
      case MGFail:
        {
          return false;
        }
      case MGCutFail:
        {
          return false;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
  else
    return false;
}

COSE_Format_cose_key_generic
COSE_Format_cose_key_generic_right(COSE_Format_cose_key_generic_ugly x6)
{
  return
    (
      (COSE_Format_cose_key_generic){
        .intkey1 = x6._1._1._1._1._1,
        .intkey2 = x6._1._1._1._1._2,
        .intkey3 = x6._1._1._1._2,
        .intkey4 = x6._1._1._2,
        .intkey5 = x6._1._2,
        ._x0 = x6._2
      }
    );
}

COSE_Format_cose_key_generic_ugly
COSE_Format_cose_key_generic_left(COSE_Format_cose_key_generic x14)
{
  return
    (
      (COSE_Format_cose_key_generic_ugly){
        ._1 = {
          ._1 = {
            ._1 = { ._1 = { ._1 = x14.intkey1, ._2 = x14.intkey2 }, ._2 = x14.intkey3 },
            ._2 = x14.intkey4
          },
          ._2 = x14.intkey5
        },
        ._2 = x14._x0
      }
    );
}

/**
Parser for cose_key_generic
*/
COSE_Format_cose_key_generic COSE_Format_parse_cose_key_generic(cbor_det_t c)
{
  cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
  cbor_det_t dest = c1;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
  if (cbor_det_map_get(c, c1, &dest))
    scrut0 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest
        }
      );
  else
    scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  COSE_Format_aux_env29_type_1_ugly w1;
  if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t w = scrut0.v;
    if (COSE_Format_validate_tstr(w))
      w1 =
        (
          (COSE_Format_aux_env29_type_1_ugly){
            .tag = COSE_Format_Inl,
            { .case_Inl = COSE_Format_parse_tstr(w) }
          }
        );
    else
      w1 =
        (
          (COSE_Format_aux_env29_type_1_ugly){
            .tag = COSE_Format_Inr,
            { .case_Inr = COSE_Format_parse_int(w) }
          }
        );
  }
  else
    w1 =
      KRML_EABORT(COSE_Format_aux_env29_type_1_ugly,
        "unreachable (pattern matches are exhaustive in F*)");
  uint64_t buf0 = 0ULL;
  KRML_HOST_IGNORE(&buf0);
  cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
  cbor_det_t dest1 = c2;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
  if (cbor_det_map_get(c, c2, &dest1))
    scrut1 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest1
        }
      );
  else
    scrut1 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite0;
  if (scrut1.tag == FStar_Pervasives_Native_None)
    ite0 = MGFail;
  else if (scrut1.tag == FStar_Pervasives_Native_Some)
    if (COSE_Format_validate_bstr(scrut1.v))
      ite0 = MGOK;
    else
      ite0 = MGFail;
  else
    ite0 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite1;
  if (ite0 == MGOK)
    ite1 = true;
  else
    ite1 = false;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t ite2;
  if (ite1)
  {
    cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
    cbor_det_t dest2 = c3;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c3, &dest2))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest2
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    Pulse_Lib_Slice_slice__uint8_t ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
      ite = COSE_Format_parse_bstr(scrut.v);
    else
      ite =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    ite2 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite2 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_tuple2__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  w11 = { ._1 = w1, ._2 = ite2 };
  uint64_t buf1 = 0ULL;
  KRML_HOST_IGNORE(&buf1);
  cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
  cbor_det_t dest2 = c3;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut2;
  if (cbor_det_map_get(c, c3, &dest2))
    scrut2 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest2
        }
      );
  else
    scrut2 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite3;
  if (scrut2.tag == FStar_Pervasives_Native_None)
    ite3 = MGFail;
  else if (scrut2.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = scrut2.v;
    bool ite;
    if (COSE_Format_validate_tstr(cv))
      ite = true;
    else
      ite = COSE_Format_validate_int(cv);
    if (ite)
      ite3 = MGOK;
    else
      ite3 = MGFail;
  }
  else
    ite3 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite4;
  if (ite3 == MGOK)
    ite4 = true;
  else
    ite4 = false;
  FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly ite5;
  if (ite4)
  {
    cbor_det_t c4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
    cbor_det_t dest3 = c4;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c4, &dest3))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest3
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    COSE_Format_aux_env29_type_1_ugly ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      if (COSE_Format_validate_tstr(w))
        ite =
          (
            (COSE_Format_aux_env29_type_1_ugly){
              .tag = COSE_Format_Inl,
              { .case_Inl = COSE_Format_parse_tstr(w) }
            }
          );
      else
        ite =
          (
            (COSE_Format_aux_env29_type_1_ugly){
              .tag = COSE_Format_Inr,
              { .case_Inr = COSE_Format_parse_int(w) }
            }
          );
    }
    else
      ite =
        KRML_EABORT(COSE_Format_aux_env29_type_1_ugly,
          "unreachable (pattern matches are exhaustive in F*)");
    ite5 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite5 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly
  w12 = { ._1 = w11, ._2 = ite5 };
  uint64_t buf2 = 0ULL;
  KRML_HOST_IGNORE(&buf2);
  cbor_det_t c4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
  cbor_det_t dest3 = c4;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut3;
  if (cbor_det_map_get(c, c4, &dest3))
    scrut3 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest3
        }
      );
  else
    scrut3 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite6;
  if (scrut3.tag == FStar_Pervasives_Native_None)
    ite6 = MGFail;
  else if (scrut3.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = scrut3.v;
    bool ite0;
    if (cbor_det_major_type(cv) == CBOR_MAJOR_TYPE_ARRAY)
    {
      cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(cv);
      bool ite1;
      if (cbor_det_array_iterator_is_empty(pi))
        ite1 = false;
      else
      {
        cbor_det_t c5 = cbor_det_array_iterator_next(&pi);
        if (COSE_Format_validate_tstr(c5))
          ite1 = true;
        else
          ite1 = COSE_Format_validate_int(c5);
      }
      bool ite2;
      if (ite1)
      {
        bool pcont = true;
        while (pcont)
        {
          cbor_det_array_iterator_t i11 = pi;
          bool ite;
          if (cbor_det_array_iterator_is_empty(pi))
            ite = false;
          else
          {
            cbor_det_t c5 = cbor_det_array_iterator_next(&pi);
            if (COSE_Format_validate_tstr(c5))
              ite = true;
            else
              ite = COSE_Format_validate_int(c5);
          }
          if (!ite)
          {
            pi = i11;
            pcont = false;
          }
        }
        ite2 = true;
      }
      else
        ite2 = false;
      if (ite2)
        ite0 = cbor_det_array_iterator_is_empty(pi);
      else
        ite0 = false;
    }
    else
      ite0 = false;
    if (ite0)
      ite6 = MGOK;
    else
      ite6 = MGFail;
  }
  else
    ite6 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite7;
  if (ite6 == MGOK)
    ite7 = true;
  else
    ite7 = false;
  FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
  ite8;
  if (ite7)
  {
    cbor_det_t c5 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
    cbor_det_t dest4 = c5;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c5, &dest4))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest4
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
    ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
      ite =
        (
          (FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1){
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_array_iterator_contents = cbor_det_array_iterator_start(scrut.v),
                .cddl_array_iterator_impl_validate = COSE_Format_aux_env29_validate_1,
                .cddl_array_iterator_impl_parse = COSE_Format_aux_env29_parse_1
              }
            }
          }
        );
    else
      ite =
        KRML_EABORT(FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1,
          "unreachable (pattern matches are exhaustive in F*)");
    ite8 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite8 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
  w13 = { ._1 = w12, ._2 = ite8 };
  uint64_t buf = 0ULL;
  KRML_HOST_IGNORE(&buf);
  cbor_det_t c5 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
  cbor_det_t dest4 = c5;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut4;
  if (cbor_det_map_get(c, c5, &dest4))
    scrut4 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest4
        }
      );
  else
    scrut4 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite9;
  if (scrut4.tag == FStar_Pervasives_Native_None)
    ite9 = MGFail;
  else if (scrut4.tag == FStar_Pervasives_Native_Some)
    if (COSE_Format_validate_bstr(scrut4.v))
      ite9 = MGOK;
    else
      ite9 = MGFail;
  else
    ite9 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite10;
  if (ite9 == MGOK)
    ite10 = true;
  else
    ite10 = false;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t ite11;
  if (ite10)
  {
    cbor_det_t c6 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
    cbor_det_t dest5 = c6;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c6, &dest5))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest5
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    Pulse_Lib_Slice_slice__uint8_t ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
      ite = COSE_Format_parse_bstr(scrut.v);
    else
      ite =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    ite11 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite11 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  w14 = { ._1 = w13, ._2 = ite11 };
  return
    COSE_Format_cose_key_generic_right((
        (COSE_Format_cose_key_generic_ugly){
          ._1 = w14,
          ._2 = {
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_map_iterator_contents = cbor_det_map_iterator_start(c),
                .cddl_map_iterator_impl_validate1 = COSE_Format_validate_evercddl_label,
                .cddl_map_iterator_impl_parse1 = COSE_Format_parse_evercddl_label,
                .cddl_map_iterator_impl_validate_ex = COSE_Format_aux_env29_map_constraint_2,
                .cddl_map_iterator_impl_validate2 = COSE_Format_validate_values,
                .cddl_map_iterator_impl_parse2 = COSE_Format_parse_values
              }
            }
          }
        }
      ));
}

static size_t
len__COSE_Format_aux_env29_type_1(Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1 s)
{
  return s.len;
}

static COSE_Format_aux_env29_type_1
op_Array_Access__COSE_Format_aux_env29_type_1(
  Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1 a,
  size_t i
)
{
  return a.elt[i];
}

static size_t
len__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(
  Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  s
)
{
  return s.len;
}

static FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
op_Array_Access__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(
  Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  a,
  size_t i
)
{
  return a.elt[i];
}

typedef struct
tuple2__Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t_s
{
  Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  _1;
  Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  _2;
}
tuple2__Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t;

static tuple2__Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
split__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(
  Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  s,
  size_t i
)
{
  return
    (
      (tuple2__Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t){
        ._1 = { .elt = s.elt, .len = i },
        ._2 = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

/**
Serializer for cose_key_generic
*/
size_t
COSE_Format_serialize_cose_key_generic(
  COSE_Format_cose_key_generic c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_cose_key_generic_ugly scrut0 = COSE_Format_cose_key_generic_left(c);
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  c1 = scrut0._1;
  FStar_Pervasives_either__Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  c2 = scrut0._2;
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
  c110 = c1._1;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t c210 = c1._2;
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly
  c120 = c110._1;
  FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
  c22 = c110._2;
  FStar_Pervasives_Native_tuple2__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  c130 = c120._1;
  FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly c230 = c120._2;
  COSE_Format_aux_env29_type_1_ugly c140 = c130._1;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t c24 = c130._2;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size0 = psize;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
    cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
    option__size_t scrut;
    if (len > (size_t)0U)
      scrut =
        (
          (option__size_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = cbor_det_serialize(c3, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1), len)
          }
        );
    else
      scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
    size_t res1;
    if (scrut.tag == FStar_Pervasives_Native_None)
      res1 = (size_t)0U;
    else if (scrut.tag == FStar_Pervasives_Native_Some)
      res1 = scrut.v;
    else
      res1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
    if (res1 > (size_t)0U)
    {
      size_t size1 = size0 + res1;
      Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1)._2;
      size_t res2;
      if (c140.tag == COSE_Format_Inl)
        res2 = COSE_Format_serialize_tstr(c140.case_Inl, out2);
      else if (c140.tag == COSE_Format_Inr)
        res2 = COSE_Format_serialize_int(c140.case_Inr, out2);
      else
        res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (res2 > (size_t)0U)
      {
        size_t size2 = size1 + res2;
        Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
        size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
        if
        (
          cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
            aout_len,
            size0,
            size1)
        )
        {
          psize = size2;
          pcount = count0 + 1ULL;
          ite0 = true;
        }
        else
          ite0 = false;
      }
      else
        ite0 = false;
    }
    else
      ite0 = false;
  }
  else
    ite0 = false;
  bool ite1;
  if (ite0)
    if (c24.tag == FStar_Pervasives_Native_Some)
    {
      Pulse_Lib_Slice_slice__uint8_t c15 = c24.v;
      uint64_t count1 = pcount;
      if (count1 < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          size_t res2 = COSE_Format_serialize_bstr(c15, split__uint8_t(out, size1)._2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count1 + 1ULL;
              ite1 = true;
            }
            else
              ite1 = false;
          }
          else
            ite1 = false;
        }
        else
          ite1 = false;
      }
      else
        ite1 = false;
    }
    else if (c24.tag == FStar_Pervasives_Native_None)
      ite1 = true;
    else
      ite1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite1 = false;
  bool ite2;
  if (ite1)
    if (c230.tag == FStar_Pervasives_Native_Some)
    {
      COSE_Format_aux_env29_type_1_ugly c14 = c230.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1)._2;
          size_t res2;
          if (c14.tag == COSE_Format_Inl)
            res2 = COSE_Format_serialize_tstr(c14.case_Inl, out2);
          else if (c14.tag == COSE_Format_Inr)
            res2 = COSE_Format_serialize_int(c14.case_Inr, out2);
          else
            res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count + 1ULL;
              ite2 = true;
            }
            else
              ite2 = false;
          }
          else
            ite2 = false;
        }
        else
          ite2 = false;
      }
      else
        ite2 = false;
    }
    else if (c230.tag == FStar_Pervasives_Native_None)
      ite2 = true;
    else
      ite2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite2 = false;
  bool ite3;
  if (ite2)
    if (c22.tag == FStar_Pervasives_Native_Some)
    {
      FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
      c13 = c22.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1)._2;
          uint64_t pcount1 = 0ULL;
          size_t psize1 = (size_t)0U;
          bool ite;
          if (c13.tag == COSE_Format_Inl)
          {
            Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1 c14 = c13.case_Inl;
            if (len__COSE_Format_aux_env29_type_1(c14) == (size_t)0U)
              ite = false;
            else
            {
              bool pres = true;
              size_t pi = (size_t)0U;
              size_t slen1 = len__COSE_Format_aux_env29_type_1(c14);
              while (pres && pi < slen1)
              {
                size_t i = pi;
                if
                (
                  COSE_Format_aux_env29_serialize_1(op_Array_Access__COSE_Format_aux_env29_type_1(c14,
                      i),
                    out2,
                    &pcount1,
                    &psize1)
                )
                  pi = i + (size_t)1U;
                else
                  pres = false;
              }
              ite = pres;
            }
          }
          else if (c13.tag == COSE_Format_Inr)
          {
            CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
            c23 = c13.case_Inr;
            if (cbor_det_array_iterator_is_empty(c23.cddl_array_iterator_contents))
              ite = false;
            else
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
              pc = c23;
              bool pres = true;
              bool em1 = cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
              bool cond = pres && !em1;
              while (cond)
              {
                CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
                i = pc;
                uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
                cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
                KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
                cbor_det_array_iterator_t ji = pj;
                uint64_t len1 = cbor_det_array_iterator_length(ji);
                pc =
                  (
                    (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1){
                      .cddl_array_iterator_contents = ji,
                      .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
                      .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
                    }
                  );
                if
                (
                  !COSE_Format_aux_env29_serialize_1(i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
                        len0 - len1)),
                    out2,
                    &pcount1,
                    &psize1)
                )
                  pres = false;
                bool em1 = cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
                cond = pres && !em1;
              }
              bool ret = pres;
              ite = ret ? ret : ret;
            }
          }
          else
            ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          size_t res21;
          if (ite)
          {
            size_t size = psize1;
            uint64_t count1 = pcount1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out2);
            res21 =
              cbor_det_serialize_array_to_array(count1,
                Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2),
                aout_len,
                size);
          }
          else
            res21 = (size_t)0U;
          if (res21 > (size_t)0U)
          {
            size_t size2 = size1 + res21;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count + 1ULL;
              ite3 = true;
            }
            else
              ite3 = false;
          }
          else
            ite3 = false;
        }
        else
          ite3 = false;
      }
      else
        ite3 = false;
    }
    else if (c22.tag == FStar_Pervasives_Native_None)
      ite3 = true;
    else
      ite3 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite3 = false;
  bool ite4;
  if (ite3)
    if (c210.tag == FStar_Pervasives_Native_Some)
    {
      Pulse_Lib_Slice_slice__uint8_t c12 = c210.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          size_t res2 = COSE_Format_serialize_bstr(c12, split__uint8_t(out, size1)._2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count + 1ULL;
              ite4 = true;
            }
            else
              ite4 = false;
          }
          else
            ite4 = false;
        }
        else
          ite4 = false;
      }
      else
        ite4 = false;
    }
    else if (c210.tag == FStar_Pervasives_Native_None)
      ite4 = true;
    else
      ite4 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite4 = false;
  bool ite;
  if (ite4)
    if (c2.tag == COSE_Format_Inl)
    {
      Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      c11 = c2.case_Inl;
      Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      buf = c11;
      KRML_HOST_IGNORE(&buf);
      bool pres = true;
      Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      pc = c11;
      bool
      pem =
        len__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(c11)
        == (size_t)0U;
      while (pres && !pem)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          i = pc;
          FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          res =
            op_Array_Access__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(i,
              (size_t)0U);
          pc =
            split__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(i,
              (size_t)1U)._2;
          FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          scrut0 = res;
          COSE_Format_evercddl_label ek = scrut0._1;
          cbor_det_t ev = scrut0._2;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
          size_t size1 = COSE_Format_serialize_evercddl_label(ek, out1);
          if (size1 == (size_t)0U)
            pres = false;
          else
          {
            FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 = split__uint8_t(out1, size1);
            Pulse_Lib_Slice_slice__uint8_t out1_ = scrut0._1;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0._2;
            size_t size2 = COSE_Format_serialize_values(ev, out2);
            if (size2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len = Pulse_Lib_Slice_len__uint8_t(out1_);
              size_t
              len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1_), len);
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut0;
              if (len1 == (size_t)0U)
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut = split__uint8_t(out1_, len1);
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len2),
                        ._2 = rem
                      }
                    }
                  );
              }
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut1;
              if (scrut0.tag == FStar_Pervasives_Native_None)
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                pair = scrut0.v;
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = { ._1 = pair._1, ._2 = pair._2 }
                    }
                  );
              }
              else
                scrut1 =
                  KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                    "unreachable (pattern matches are exhaustive in F*)");
              if (scrut1.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t ck = scrut1.v._1;
                Pulse_Lib_Slice_slice__uint8_t out2_ = split__uint8_t(out2, size2)._1;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(out2_);
                size_t
                len3 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2_),
                    len2);
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut0;
                if (len3 == (size_t)0U)
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut = split__uint8_t(out2_, len3);
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                  size_t len4 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len4),
                          ._2 = rem
                        }
                      }
                    );
                }
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut;
                if (scrut0.tag == FStar_Pervasives_Native_None)
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else if (scrut0.tag == FStar_Pervasives_Native_Some)
                {
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                  pair = scrut0.v;
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = { ._1 = pair._1, ._2 = pair._2 }
                      }
                    );
                }
                else
                  scrut =
                    KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                      "unreachable (pattern matches are exhaustive in F*)");
                if (scrut.tag == FStar_Pervasives_Native_Some)
                  if (COSE_Format_aux_env29_map_constraint_2(cbor_det_mk_map_entry(ck, scrut.v._1)))
                    pres = false;
                  else
                  {
                    size_t size1_ = size0 + size1;
                    size_t size2_ = size1_ + size2;
                    Pulse_Lib_Slice_slice__uint8_t out_ = split__uint8_t(out, size2_)._1;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out_);
                    if
                    (
                      cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out_),
                        aout_len,
                        size0,
                        size1_)
                    )
                    {
                      pem =
                        len__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(pc)
                        == (size_t)0U;
                      psize = size2_;
                      pcount = count_;
                    }
                    else
                      pres = false;
                  }
                else
                {
                  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                    __FILE__,
                    __LINE__,
                    "unreachable (pattern matches are exhaustive in F*)");
                  KRML_HOST_EXIT(255U);
                }
              }
              else
              {
                KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                  __FILE__,
                  __LINE__,
                  "unreachable (pattern matches are exhaustive in F*)");
                KRML_HOST_EXIT(255U);
              }
            }
          }
        }
      }
      ite = pres;
    }
    else if (c2.tag == COSE_Format_Inr)
    {
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      c21 = c2.case_Inr;
      bool pres = true;
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      pc = c21;
      cbor_det_map_iterator_t pj = c21.cddl_map_iterator_contents;
      bool pres1 = true;
      bool test0 = cbor_det_map_iterator_is_empty(pj);
      bool cond = pres1 && !test0;
      while (cond)
      {
        cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
        if (!!c21.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
          if (!c21.cddl_map_iterator_impl_validate_ex(elt))
            pres1 = !c21.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
        bool test = cbor_det_map_iterator_is_empty(pj);
        cond = pres1 && !test;
      }
      bool pem = pres1;
      while (pres && !pem)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          i = pc;
          cbor_det_map_iterator_t pj1 = i.cddl_map_iterator_contents;
          cbor_det_map_entry_t hd0 = cbor_det_map_iterator_next(&pj1);
          cbor_det_map_entry_t phd = hd0;
          bool tk0 = i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd0));
          bool tv0 = i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0));
          bool pcont = !tk0 || !tv0 || i.cddl_map_iterator_impl_validate_ex(hd0);
          while (pcont)
          {
            cbor_det_map_entry_t hd = cbor_det_map_iterator_next(&pj1);
            phd = hd;
            bool tk = i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd));
            bool tv = i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd));
            pcont = !tk || !tv || i.cddl_map_iterator_impl_validate_ex(hd);
          }
          cbor_det_map_entry_t hd = phd;
          COSE_Format_evercddl_label
          hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
          cbor_det_t hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
          pc =
            (
              (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t){
                .cddl_map_iterator_contents = pj1,
                .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
                .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
                .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
                .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
                .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
              }
            );
          COSE_Format_evercddl_label ek = hd_key_res;
          cbor_det_t ev = hd_value_res;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
          size_t size1 = COSE_Format_serialize_evercddl_label(ek, out1);
          if (size1 == (size_t)0U)
            pres = false;
          else
          {
            FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 = split__uint8_t(out1, size1);
            Pulse_Lib_Slice_slice__uint8_t out1_ = scrut0._1;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0._2;
            size_t size2 = COSE_Format_serialize_values(ev, out2);
            if (size2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len = Pulse_Lib_Slice_len__uint8_t(out1_);
              size_t
              len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1_), len);
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut0;
              if (len1 == (size_t)0U)
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut = split__uint8_t(out1_, len1);
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len2),
                        ._2 = rem
                      }
                    }
                  );
              }
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut1;
              if (scrut0.tag == FStar_Pervasives_Native_None)
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                pair = scrut0.v;
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = { ._1 = pair._1, ._2 = pair._2 }
                    }
                  );
              }
              else
                scrut1 =
                  KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                    "unreachable (pattern matches are exhaustive in F*)");
              if (scrut1.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t ck = scrut1.v._1;
                Pulse_Lib_Slice_slice__uint8_t out2_ = split__uint8_t(out2, size2)._1;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(out2_);
                size_t
                len3 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2_),
                    len2);
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut0;
                if (len3 == (size_t)0U)
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut = split__uint8_t(out2_, len3);
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                  size_t len4 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len4),
                          ._2 = rem
                        }
                      }
                    );
                }
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut;
                if (scrut0.tag == FStar_Pervasives_Native_None)
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else if (scrut0.tag == FStar_Pervasives_Native_Some)
                {
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                  pair = scrut0.v;
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = { ._1 = pair._1, ._2 = pair._2 }
                      }
                    );
                }
                else
                  scrut =
                    KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                      "unreachable (pattern matches are exhaustive in F*)");
                if (scrut.tag == FStar_Pervasives_Native_Some)
                  if (COSE_Format_aux_env29_map_constraint_2(cbor_det_mk_map_entry(ck, scrut.v._1)))
                    pres = false;
                  else
                  {
                    size_t size1_ = size0 + size1;
                    size_t size2_ = size1_ + size2;
                    Pulse_Lib_Slice_slice__uint8_t out_ = split__uint8_t(out, size2_)._1;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out_);
                    if
                    (
                      cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out_),
                        aout_len,
                        size0,
                        size1_)
                    )
                    {
                      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
                      __anf0 = pc;
                      cbor_det_map_iterator_t pj2 = __anf0.cddl_map_iterator_contents;
                      bool pres2 = true;
                      bool test = cbor_det_map_iterator_is_empty(pj2);
                      bool cond = pres2 && !test;
                      while (cond)
                      {
                        cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj2);
                        if (!!__anf0.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
                          if (!__anf0.cddl_map_iterator_impl_validate_ex(elt))
                            pres2 =
                              !__anf0.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
                        bool test = cbor_det_map_iterator_is_empty(pj2);
                        cond = pres2 && !test;
                      }
                      pem = pres2;
                      psize = size2_;
                      pcount = count_;
                    }
                    else
                      pres = false;
                  }
                else
                {
                  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                    __FILE__,
                    __LINE__,
                    "unreachable (pattern matches are exhaustive in F*)");
                  KRML_HOST_EXIT(255U);
                }
              }
              else
              {
                KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                  __FILE__,
                  __LINE__,
                  "unreachable (pattern matches are exhaustive in F*)");
                KRML_HOST_EXIT(255U);
              }
            }
          }
        }
      }
      ite = pres;
    }
    else
      ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite = false;
  if (ite)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
    return
      cbor_det_serialize_map_to_array(count,
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_generic_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cose_key_generic(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_generic_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cose_key_generic(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_generic_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cose_key_generic(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_generic_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool
COSE_Format_is_empty_iterate_array_aux_env29_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
  i
)
{
  return cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents);
}

COSE_Format_aux_env29_type_1
COSE_Format_next_iterate_array_aux_env29_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
  *pi
)
{
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1
  i = pi[0U];
  uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
  cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
  KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
  cbor_det_array_iterator_t ji = pj;
  uint64_t len1 = cbor_det_array_iterator_length(ji);
  pi[0U] =
    (
      (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1){
        .cddl_array_iterator_contents = ji,
        .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
        .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
      }
    );
  return
    i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
        len0 - len1));
}

bool
COSE_Format_is_empty_iterate_map_evercddl_label_and_values(
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  i
)
{
  cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
  bool pres = true;
  bool test = cbor_det_map_iterator_is_empty(pj);
  bool cond = pres && !test;
  while (cond)
  {
    cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
    if (!!i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
      if (!i.cddl_map_iterator_impl_validate_ex(elt))
        pres = !i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
    bool test = cbor_det_map_iterator_is_empty(pj);
    cond = pres && !test;
  }
  return pres;
}

FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
COSE_Format_next_iterate_map_evercddl_label_and_values(
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  *pi
)
{
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  i = pi[0U];
  cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
  cbor_det_map_entry_t hd0 = cbor_det_map_iterator_next(&pj);
  cbor_det_map_entry_t phd = hd0;
  bool tk0 = i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd0));
  bool tv0 = i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0));
  bool pcont = !tk0 || !tv0 || i.cddl_map_iterator_impl_validate_ex(hd0);
  while (pcont)
  {
    cbor_det_map_entry_t hd = cbor_det_map_iterator_next(&pj);
    phd = hd;
    bool tk = i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd));
    bool tv = i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd));
    pcont = !tk || !tv || i.cddl_map_iterator_impl_validate_ex(hd);
  }
  cbor_det_map_entry_t hd = phd;
  COSE_Format_evercddl_label
  hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
  cbor_det_t hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
  pi[0U] =
    (
      (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t){
        .cddl_map_iterator_contents = pj,
        .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
        .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
        .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
        .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
        .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
      }
    );
  return
    (
      (FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t){
        ._1 = hd_key_res,
        ._2 = hd_value_res
      }
    );
}

bool COSE_Format_aux_env30_validate_1(cbor_det_array_iterator_t *pi)
{
  if (cbor_det_array_iterator_is_empty(pi[0U]))
    return false;
  else
    return COSE_Format_validate_cose_key_generic(cbor_det_array_iterator_next(pi));
}

COSE_Format_cose_key_generic
COSE_Format_aux_env30_type_1_right(COSE_Format_cose_key_generic x1)
{
  return x1;
}

COSE_Format_cose_key_generic COSE_Format_aux_env30_type_1_left(COSE_Format_cose_key_generic x4)
{
  return x4;
}

/**
Parser for aux_env30_type_1
*/
COSE_Format_cose_key_generic COSE_Format_aux_env30_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t buf = c;
  return COSE_Format_parse_cose_key_generic(cbor_det_array_iterator_next(&buf));
}

/**
Serializer for aux_env30_type_1
*/
bool
COSE_Format_aux_env30_serialize_1(
  COSE_Format_cose_key_generic c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  uint64_t count = out_count[0U];
  if (count < 18446744073709551615ULL)
  {
    size_t size = out_size[0U];
    size_t size1 = COSE_Format_serialize_cose_key_generic(c, split__uint8_t(out, size)._2);
    if (size1 == (size_t)0U)
      return false;
    else
    {
      out_count[0U] = count + 1ULL;
      out_size[0U] = size + size1;
      return true;
    }
  }
  else
    return false;
}

bool COSE_Format_validate_cose_keyset(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(c);
    bool ite0;
    if (cbor_det_array_iterator_is_empty(pi))
      ite0 = false;
    else
      ite0 = COSE_Format_validate_cose_key_generic(cbor_det_array_iterator_next(&pi));
    bool ite1;
    if (ite0)
    {
      bool pcont = true;
      while (pcont)
      {
        cbor_det_array_iterator_t i11 = pi;
        bool ite;
        if (cbor_det_array_iterator_is_empty(pi))
          ite = false;
        else
          ite = COSE_Format_validate_cose_key_generic(cbor_det_array_iterator_next(&pi));
        if (!ite)
        {
          pi = i11;
          pcont = false;
        }
      }
      ite1 = true;
    }
    else
      ite1 = false;
    if (ite1)
      return cbor_det_array_iterator_is_empty(pi);
    else
      return false;
  }
  else
    return false;
}

COSE_Format_cose_keyset COSE_Format_cose_keyset_right(COSE_Format_cose_keyset_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return
      (
        (COSE_Format_cose_keyset){
          .tag = COSE_Format_Mkcose_keyset0,
          { .case_Mkcose_keyset0 = x2.case_Inl }
        }
      );
  else if (x2.tag == COSE_Format_Inr)
    return
      (
        (COSE_Format_cose_keyset){
          .tag = COSE_Format_Mkcose_keyset1,
          { .case_Mkcose_keyset1 = x2.case_Inr }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

COSE_Format_cose_keyset_ugly COSE_Format_cose_keyset_left(COSE_Format_cose_keyset x8)
{
  if (x8.tag == COSE_Format_Mkcose_keyset0)
    return
      (
        (COSE_Format_cose_keyset_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = x8.case_Mkcose_keyset0 }
        }
      );
  else if (x8.tag == COSE_Format_Mkcose_keyset1)
    return
      (
        (COSE_Format_cose_keyset_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = x8.case_Mkcose_keyset1 }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

/**
Parser for cose_keyset
*/
COSE_Format_cose_keyset COSE_Format_parse_cose_keyset(cbor_det_t c)
{
  return
    COSE_Format_cose_keyset_right((
        (COSE_Format_cose_keyset_ugly){
          .tag = COSE_Format_Inr,
          {
            .case_Inr = {
              .cddl_array_iterator_contents = cbor_det_array_iterator_start(c),
              .cddl_array_iterator_impl_validate = COSE_Format_aux_env30_validate_1,
              .cddl_array_iterator_impl_parse = COSE_Format_aux_env30_parse_1
            }
          }
        }
      ));
}

static size_t
len__COSE_Format_cose_key_generic(Pulse_Lib_Slice_slice__COSE_Format_cose_key_generic s)
{
  return s.len;
}

static COSE_Format_cose_key_generic
op_Array_Access__COSE_Format_cose_key_generic(
  Pulse_Lib_Slice_slice__COSE_Format_cose_key_generic a,
  size_t i
)
{
  return a.elt[i];
}

/**
Serializer for cose_keyset
*/
size_t
COSE_Format_serialize_cose_keyset(
  COSE_Format_cose_keyset c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_cose_keyset_ugly scrut = COSE_Format_cose_keyset_left(c);
  bool ite;
  if (scrut.tag == COSE_Format_Inl)
  {
    Pulse_Lib_Slice_slice__COSE_Format_cose_key_generic c1 = scrut.case_Inl;
    if (len__COSE_Format_cose_key_generic(c1) == (size_t)0U)
      ite = false;
    else
    {
      bool pres = true;
      size_t pi = (size_t)0U;
      size_t slen = len__COSE_Format_cose_key_generic(c1);
      while (pres && pi < slen)
      {
        size_t i = pi;
        if
        (
          COSE_Format_aux_env30_serialize_1(op_Array_Access__COSE_Format_cose_key_generic(c1, i),
            out,
            &pcount,
            &psize)
        )
          pi = i + (size_t)1U;
        else
          pres = false;
      }
      ite = pres;
    }
  }
  else if (scrut.tag == COSE_Format_Inr)
  {
    CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_key_generic
    c2 = scrut.case_Inr;
    if (cbor_det_array_iterator_is_empty(c2.cddl_array_iterator_contents))
      ite = false;
    else
    {
      CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_key_generic
      pc = c2;
      bool pres = true;
      bool em1 = cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
      bool cond = pres && !em1;
      while (cond)
      {
        CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_key_generic
        i = pc;
        uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
        cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
        KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
        cbor_det_array_iterator_t ji = pj;
        uint64_t len1 = cbor_det_array_iterator_length(ji);
        pc =
          (
            (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_key_generic){
              .cddl_array_iterator_contents = ji,
              .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
              .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
            }
          );
        if
        (
          !COSE_Format_aux_env30_serialize_1(i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
                len0 - len1)),
            out,
            &pcount,
            &psize)
        )
          pres = false;
        bool em1 = cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
        cond = pres && !em1;
      }
      bool ret = pres;
      ite = ret ? ret : ret;
    }
  }
  else
    ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  if (ite)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
    return
      cbor_det_serialize_array_to_array(count,
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_keyset_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cose_keyset(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_keyset_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cose_keyset(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_keyset_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cose_keyset(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_keyset_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool
COSE_Format_is_empty_iterate_array_aux_env30_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_key_generic
  i
)
{
  return cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents);
}

COSE_Format_cose_key_generic
COSE_Format_next_iterate_array_aux_env30_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_key_generic
  *pi
)
{
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_key_generic
  i = pi[0U];
  uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
  cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
  KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
  cbor_det_array_iterator_t ji = pj;
  uint64_t len1 = cbor_det_array_iterator_length(ji);
  pi[0U] =
    (
      (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_key_generic){
        .cddl_array_iterator_contents = ji,
        .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
        .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
      }
    );
  return
    i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
        len0 - len1));
}

bool COSE_Format_aux_env31_map_constraint_1(cbor_det_map_entry_t x)
{
  cbor_det_t k = cbor_det_map_entry_key(x);
  bool ite0;
  if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
    ite0 = cbor_det_read_uint64(k) == 1ULL;
  else
    ite0 = false;
  bool ite1;
  if (ite0)
  {
    cbor_det_map_entry_value(x);
    ite1 = true;
  }
  else
    ite1 = false;
  bool ite2;
  if (ite1)
    ite2 = true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_NEG_INT64)
      ite = cbor_det_read_uint64(k1) == 0ULL;
    else
      ite = false;
    if (ite)
    {
      cbor_det_map_entry_value(x);
      ite2 = true;
    }
    else
      ite2 = false;
  }
  bool ite3;
  if (ite2)
    ite3 = true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_NEG_INT64)
      ite = cbor_det_read_uint64(k1) == 1ULL;
    else
      ite = false;
    if (ite)
    {
      cbor_det_map_entry_value(x);
      ite3 = true;
    }
    else
      ite3 = false;
  }
  if (ite3)
    return true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_NEG_INT64)
      ite = cbor_det_read_uint64(k1) == 3ULL;
    else
      ite = false;
    if (ite)
    {
      cbor_det_map_entry_value(x);
      return true;
    }
    else
      return false;
  }
}

bool COSE_Format_validate_cose_key_okp(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t remaining = cbor_det_get_map_length(c);
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest = c1;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
    if (cbor_det_map_get(c, c1, &dest))
      scrut0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest
          }
        );
    else
      scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    impl_map_group_result ite0;
    if (scrut0.tag == FStar_Pervasives_Native_None)
      ite0 = MGFail;
    else if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t cv = scrut0.v;
      bool ite;
      if (cbor_det_major_type(cv) == CBOR_MAJOR_TYPE_UINT64)
        ite = cbor_det_read_uint64(cv) == 1ULL;
      else
        ite = false;
      if (ite)
      {
        remaining--;
        ite0 = MGOK;
      }
      else
        ite0 = MGCutFail;
    }
    else
      ite0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    impl_map_group_result sw0;
    switch (ite0)
    {
      case MGOK:
        {
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 0ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          if (scrut.tag == FStar_Pervasives_Native_None)
            sw0 = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = scrut.v;
            bool ite;
            if (COSE_Format_validate_int(cv))
              ite = true;
            else
              ite = COSE_Format_validate_tstr(cv);
            if (ite)
            {
              remaining--;
              sw0 = MGOK;
            }
            else
              sw0 = MGCutFail;
          }
          else
            sw0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          break;
        }
      case MGFail:
        {
          sw0 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw0 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw1;
    switch (sw0)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            if (COSE_Format_validate_bstr(scrut.v))
            {
              remaining--;
              ite = MGOK;
            }
            else
              ite = MGCutFail;
          else
            ite =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite)
          {
            case MGOK:
              {
                sw1 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                sw1 = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw1 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw1 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw1 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw2;
    switch (sw1)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            if (COSE_Format_validate_bstr(scrut.v))
            {
              remaining--;
              ite = MGOK;
            }
            else
              ite = MGCutFail;
          else
            ite =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite)
          {
            case MGOK:
              {
                sw2 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                sw2 = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw2 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw2 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw2 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw;
    switch (sw2)
    {
      case MGOK:
        {
          cbor_det_map_iterator_t pj = cbor_det_map_iterator_start(c);
          while (!cbor_det_map_iterator_is_empty(pj))
          {
            cbor_det_map_entry_t chd = cbor_det_map_iterator_next(&pj);
            bool ite0;
            if (COSE_Format_validate_evercddl_label(cbor_det_map_entry_key(chd)))
              ite0 = COSE_Format_validate_values(cbor_det_map_entry_value(chd));
            else
              ite0 = false;
            bool ite1;
            if (ite0)
            {
              cbor_det_t k1 = cbor_det_map_entry_key(chd);
              bool ite0;
              if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
                ite0 = cbor_det_read_uint64(k1) == 1ULL;
              else
                ite0 = false;
              bool ite2;
              if (ite0)
              {
                cbor_det_map_entry_value(chd);
                ite2 = true;
              }
              else
                ite2 = false;
              bool ite3;
              if (ite2)
                ite3 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_NEG_INT64)
                  ite = cbor_det_read_uint64(k2) == 0ULL;
                else
                  ite = false;
                if (ite)
                {
                  cbor_det_map_entry_value(chd);
                  ite3 = true;
                }
                else
                  ite3 = false;
              }
              bool ite4;
              if (ite3)
                ite4 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_NEG_INT64)
                  ite = cbor_det_read_uint64(k2) == 1ULL;
                else
                  ite = false;
                if (ite)
                {
                  cbor_det_map_entry_value(chd);
                  ite4 = true;
                }
                else
                  ite4 = false;
              }
              bool ite5;
              if (ite4)
                ite5 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_NEG_INT64)
                  ite = cbor_det_read_uint64(k2) == 3ULL;
                else
                  ite = false;
                if (ite)
                {
                  cbor_det_map_entry_value(chd);
                  ite5 = true;
                }
                else
                  ite5 = false;
              }
              ite1 = !ite5;
            }
            else
              ite1 = false;
            if (!!ite1)
              remaining--;
          }
          sw = MGOK;
          break;
        }
      case MGFail:
        {
          sw = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (sw)
    {
      case MGOK:
        {
          return remaining == 0ULL;
        }
      case MGFail:
        {
          return false;
        }
      case MGCutFail:
        {
          return false;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
  else
    return false;
}

COSE_Format_cose_key_okp COSE_Format_cose_key_okp_right(COSE_Format_cose_key_okp_ugly x5)
{
  return
    (
      (COSE_Format_cose_key_okp){
        .intkeyneg1 = x5._1._1._1,
        .intkeyneg2 = x5._1._1._2,
        .intkeyneg4 = x5._1._2,
        ._x0 = x5._2
      }
    );
}

COSE_Format_cose_key_okp_ugly COSE_Format_cose_key_okp_left(COSE_Format_cose_key_okp x12)
{
  return
    (
      (COSE_Format_cose_key_okp_ugly){
        ._1 = { ._1 = { ._1 = x12.intkeyneg1, ._2 = x12.intkeyneg2 }, ._2 = x12.intkeyneg4 },
        ._2 = x12._x0
      }
    );
}

/**
Parser for cose_key_okp
*/
COSE_Format_cose_key_okp COSE_Format_parse_cose_key_okp(cbor_det_t c)
{
  cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
  cbor_det_t buf0 = c1;
  cbor_det_map_get(c, c1, &buf0);
  cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 0ULL);
  cbor_det_t dest1 = c2;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
  if (cbor_det_map_get(c, c2, &dest1))
    scrut0 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest1
        }
      );
  else
    scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  COSE_Format_evercddl_label_ugly w11;
  if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t w = scrut0.v;
    if (COSE_Format_validate_int(w))
      w11 =
        (
          (COSE_Format_evercddl_label_ugly){
            .tag = COSE_Format_Inl,
            { .case_Inl = COSE_Format_parse_int(w) }
          }
        );
    else
      w11 =
        (
          (COSE_Format_evercddl_label_ugly){
            .tag = COSE_Format_Inr,
            { .case_Inr = COSE_Format_parse_tstr(w) }
          }
        );
  }
  else
    w11 =
      KRML_EABORT(COSE_Format_evercddl_label_ugly,
        "unreachable (pattern matches are exhaustive in F*)");
  uint64_t buf1 = 0ULL;
  KRML_HOST_IGNORE(&buf1);
  cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
  cbor_det_t dest2 = c3;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
  if (cbor_det_map_get(c, c3, &dest2))
    scrut1 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest2
        }
      );
  else
    scrut1 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite0;
  if (scrut1.tag == FStar_Pervasives_Native_None)
    ite0 = MGFail;
  else if (scrut1.tag == FStar_Pervasives_Native_Some)
    if (COSE_Format_validate_bstr(scrut1.v))
      ite0 = MGOK;
    else
      ite0 = MGCutFail;
  else
    ite0 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite1;
  if (ite0 == MGOK)
    ite1 = true;
  else
    ite1 = false;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t ite2;
  if (ite1)
  {
    cbor_det_t c4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
    cbor_det_t dest3 = c4;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c4, &dest3))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest3
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    Pulse_Lib_Slice_slice__uint8_t ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
      ite = COSE_Format_parse_bstr(scrut.v);
    else
      ite =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    ite2 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite2 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2_____COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  w12 = { ._1 = w11, ._2 = ite2 };
  uint64_t buf = 0ULL;
  KRML_HOST_IGNORE(&buf);
  cbor_det_t c4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
  cbor_det_t dest3 = c4;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut2;
  if (cbor_det_map_get(c, c4, &dest3))
    scrut2 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest3
        }
      );
  else
    scrut2 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite3;
  if (scrut2.tag == FStar_Pervasives_Native_None)
    ite3 = MGFail;
  else if (scrut2.tag == FStar_Pervasives_Native_Some)
    if (COSE_Format_validate_bstr(scrut2.v))
      ite3 = MGOK;
    else
      ite3 = MGCutFail;
  else
    ite3 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite4;
  if (ite3 == MGOK)
    ite4 = true;
  else
    ite4 = false;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t ite5;
  if (ite4)
  {
    cbor_det_t c5 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
    cbor_det_t dest4 = c5;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c5, &dest4))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest4
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    Pulse_Lib_Slice_slice__uint8_t ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
      ite = COSE_Format_parse_bstr(scrut.v);
    else
      ite =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    ite5 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite5 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2_____COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  w13 = { ._1 = w12, ._2 = ite5 };
  return
    COSE_Format_cose_key_okp_right((
        (COSE_Format_cose_key_okp_ugly){
          ._1 = w13,
          ._2 = {
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_map_iterator_contents = cbor_det_map_iterator_start(c),
                .cddl_map_iterator_impl_validate1 = COSE_Format_validate_evercddl_label,
                .cddl_map_iterator_impl_parse1 = COSE_Format_parse_evercddl_label,
                .cddl_map_iterator_impl_validate_ex = COSE_Format_aux_env31_map_constraint_1,
                .cddl_map_iterator_impl_validate2 = COSE_Format_validate_values,
                .cddl_map_iterator_impl_parse2 = COSE_Format_parse_values
              }
            }
          }
        }
      ));
}

/**
Serializer for cose_key_okp
*/
size_t
COSE_Format_serialize_cose_key_okp(
  COSE_Format_cose_key_okp c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_cose_key_okp_ugly scrut0 = COSE_Format_cose_key_okp_left(c);
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2_____COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  c1 = scrut0._1;
  FStar_Pervasives_either__Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  c2 = scrut0._2;
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2_____COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  c110 = c1._1;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t c210 = c1._2;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t c22 = c110._2;
  COSE_Format_evercddl_label_ugly c23 = c110._1;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size0 = psize;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
    cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
    option__size_t scrut0;
    if (len > (size_t)0U)
      scrut0 =
        (
          (option__size_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = cbor_det_serialize(c3, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1), len)
          }
        );
    else
      scrut0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
    size_t res1;
    if (scrut0.tag == FStar_Pervasives_Native_None)
      res1 = (size_t)0U;
    else if (scrut0.tag == FStar_Pervasives_Native_Some)
      res1 = scrut0.v;
    else
      res1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
    if (res1 > (size_t)0U)
    {
      size_t size1 = size0 + res1;
      Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1)._2;
      cbor_det_t c4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
      size_t len1 = cbor_det_size(c4, Pulse_Lib_Slice_len__uint8_t(out2));
      option__size_t scrut;
      if (len1 > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(c4,
                Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2),
                len1)
            }
          );
      else
        scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      size_t res21;
      if (scrut.tag == FStar_Pervasives_Native_None)
        res21 = (size_t)0U;
      else if (scrut.tag == FStar_Pervasives_Native_Some)
        res21 = scrut.v;
      else
        res21 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (res21 > (size_t)0U)
      {
        size_t size2 = size1 + res21;
        Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
        size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
        if
        (
          cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
            aout_len,
            size0,
            size1)
        )
        {
          psize = size2;
          pcount = count0 + 1ULL;
          ite0 = true;
        }
        else
          ite0 = false;
      }
      else
        ite0 = false;
    }
    else
      ite0 = false;
  }
  else
    ite0 = false;
  bool ite1;
  if (ite0)
  {
    uint64_t count1 = pcount;
    if (count1 < 18446744073709551615ULL)
    {
      size_t size0 = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
      cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 0ULL);
      size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
      option__size_t scrut;
      if (len > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(c3,
                Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                len)
            }
          );
      else
        scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      size_t res11;
      if (scrut.tag == FStar_Pervasives_Native_None)
        res11 = (size_t)0U;
      else if (scrut.tag == FStar_Pervasives_Native_Some)
        res11 = scrut.v;
      else
        res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (res11 > (size_t)0U)
      {
        size_t size1 = size0 + res11;
        Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1)._2;
        size_t res2;
        if (c23.tag == COSE_Format_Inl)
          res2 = COSE_Format_serialize_int(c23.case_Inl, out2);
        else if (c23.tag == COSE_Format_Inr)
          res2 = COSE_Format_serialize_tstr(c23.case_Inr, out2);
        else
          res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res2 > (size_t)0U)
        {
          size_t size2 = size1 + res2;
          Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
          size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
          if
          (
            cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
              aout_len,
              size0,
              size1)
          )
          {
            psize = size2;
            pcount = count1 + 1ULL;
            ite1 = true;
          }
          else
            ite1 = false;
        }
        else
          ite1 = false;
      }
      else
        ite1 = false;
    }
    else
      ite1 = false;
  }
  else
    ite1 = false;
  bool ite2;
  if (ite1)
    if (c22.tag == FStar_Pervasives_Native_Some)
    {
      Pulse_Lib_Slice_slice__uint8_t c13 = c22.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          size_t res2 = COSE_Format_serialize_bstr(c13, split__uint8_t(out, size1)._2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count + 1ULL;
              ite2 = true;
            }
            else
              ite2 = false;
          }
          else
            ite2 = false;
        }
        else
          ite2 = false;
      }
      else
        ite2 = false;
    }
    else if (c22.tag == FStar_Pervasives_Native_None)
      ite2 = true;
    else
      ite2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite2 = false;
  bool ite3;
  if (ite2)
    if (c210.tag == FStar_Pervasives_Native_Some)
    {
      Pulse_Lib_Slice_slice__uint8_t c12 = c210.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          size_t res2 = COSE_Format_serialize_bstr(c12, split__uint8_t(out, size1)._2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count + 1ULL;
              ite3 = true;
            }
            else
              ite3 = false;
          }
          else
            ite3 = false;
        }
        else
          ite3 = false;
      }
      else
        ite3 = false;
    }
    else if (c210.tag == FStar_Pervasives_Native_None)
      ite3 = true;
    else
      ite3 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite3 = false;
  bool ite;
  if (ite3)
    if (c2.tag == COSE_Format_Inl)
    {
      Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      c11 = c2.case_Inl;
      Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      buf = c11;
      KRML_HOST_IGNORE(&buf);
      bool pres = true;
      Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      pc = c11;
      bool
      pem =
        len__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(c11)
        == (size_t)0U;
      while (pres && !pem)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          i = pc;
          FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          res =
            op_Array_Access__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(i,
              (size_t)0U);
          pc =
            split__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(i,
              (size_t)1U)._2;
          FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          scrut0 = res;
          COSE_Format_evercddl_label ek = scrut0._1;
          cbor_det_t ev = scrut0._2;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
          size_t size1 = COSE_Format_serialize_evercddl_label(ek, out1);
          if (size1 == (size_t)0U)
            pres = false;
          else
          {
            FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 = split__uint8_t(out1, size1);
            Pulse_Lib_Slice_slice__uint8_t out1_ = scrut0._1;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0._2;
            size_t size2 = COSE_Format_serialize_values(ev, out2);
            if (size2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len = Pulse_Lib_Slice_len__uint8_t(out1_);
              size_t
              len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1_), len);
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut0;
              if (len1 == (size_t)0U)
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut = split__uint8_t(out1_, len1);
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len2),
                        ._2 = rem
                      }
                    }
                  );
              }
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut1;
              if (scrut0.tag == FStar_Pervasives_Native_None)
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                pair = scrut0.v;
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = { ._1 = pair._1, ._2 = pair._2 }
                    }
                  );
              }
              else
                scrut1 =
                  KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                    "unreachable (pattern matches are exhaustive in F*)");
              if (scrut1.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t ck = scrut1.v._1;
                Pulse_Lib_Slice_slice__uint8_t out2_ = split__uint8_t(out2, size2)._1;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(out2_);
                size_t
                len3 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2_),
                    len2);
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut0;
                if (len3 == (size_t)0U)
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut = split__uint8_t(out2_, len3);
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                  size_t len4 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len4),
                          ._2 = rem
                        }
                      }
                    );
                }
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut;
                if (scrut0.tag == FStar_Pervasives_Native_None)
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else if (scrut0.tag == FStar_Pervasives_Native_Some)
                {
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                  pair = scrut0.v;
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = { ._1 = pair._1, ._2 = pair._2 }
                      }
                    );
                }
                else
                  scrut =
                    KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                      "unreachable (pattern matches are exhaustive in F*)");
                if (scrut.tag == FStar_Pervasives_Native_Some)
                  if (COSE_Format_aux_env31_map_constraint_1(cbor_det_mk_map_entry(ck, scrut.v._1)))
                    pres = false;
                  else
                  {
                    size_t size1_ = size0 + size1;
                    size_t size2_ = size1_ + size2;
                    Pulse_Lib_Slice_slice__uint8_t out_ = split__uint8_t(out, size2_)._1;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out_);
                    if
                    (
                      cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out_),
                        aout_len,
                        size0,
                        size1_)
                    )
                    {
                      pem =
                        len__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(pc)
                        == (size_t)0U;
                      psize = size2_;
                      pcount = count_;
                    }
                    else
                      pres = false;
                  }
                else
                {
                  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                    __FILE__,
                    __LINE__,
                    "unreachable (pattern matches are exhaustive in F*)");
                  KRML_HOST_EXIT(255U);
                }
              }
              else
              {
                KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                  __FILE__,
                  __LINE__,
                  "unreachable (pattern matches are exhaustive in F*)");
                KRML_HOST_EXIT(255U);
              }
            }
          }
        }
      }
      ite = pres;
    }
    else if (c2.tag == COSE_Format_Inr)
    {
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      c21 = c2.case_Inr;
      bool pres = true;
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      pc = c21;
      cbor_det_map_iterator_t pj = c21.cddl_map_iterator_contents;
      bool pres1 = true;
      bool test0 = cbor_det_map_iterator_is_empty(pj);
      bool cond = pres1 && !test0;
      while (cond)
      {
        cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
        if (!!c21.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
          if (!c21.cddl_map_iterator_impl_validate_ex(elt))
            pres1 = !c21.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
        bool test = cbor_det_map_iterator_is_empty(pj);
        cond = pres1 && !test;
      }
      bool pem = pres1;
      while (pres && !pem)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          i = pc;
          cbor_det_map_iterator_t pj1 = i.cddl_map_iterator_contents;
          cbor_det_map_entry_t hd0 = cbor_det_map_iterator_next(&pj1);
          cbor_det_map_entry_t phd = hd0;
          bool tk0 = i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd0));
          bool tv0 = i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0));
          bool pcont = !tk0 || !tv0 || i.cddl_map_iterator_impl_validate_ex(hd0);
          while (pcont)
          {
            cbor_det_map_entry_t hd = cbor_det_map_iterator_next(&pj1);
            phd = hd;
            bool tk = i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd));
            bool tv = i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd));
            pcont = !tk || !tv || i.cddl_map_iterator_impl_validate_ex(hd);
          }
          cbor_det_map_entry_t hd = phd;
          COSE_Format_evercddl_label
          hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
          cbor_det_t hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
          pc =
            (
              (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t){
                .cddl_map_iterator_contents = pj1,
                .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
                .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
                .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
                .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
                .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
              }
            );
          COSE_Format_evercddl_label ek = hd_key_res;
          cbor_det_t ev = hd_value_res;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
          size_t size1 = COSE_Format_serialize_evercddl_label(ek, out1);
          if (size1 == (size_t)0U)
            pres = false;
          else
          {
            FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 = split__uint8_t(out1, size1);
            Pulse_Lib_Slice_slice__uint8_t out1_ = scrut0._1;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0._2;
            size_t size2 = COSE_Format_serialize_values(ev, out2);
            if (size2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len = Pulse_Lib_Slice_len__uint8_t(out1_);
              size_t
              len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1_), len);
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut0;
              if (len1 == (size_t)0U)
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut = split__uint8_t(out1_, len1);
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len2),
                        ._2 = rem
                      }
                    }
                  );
              }
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut1;
              if (scrut0.tag == FStar_Pervasives_Native_None)
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                pair = scrut0.v;
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = { ._1 = pair._1, ._2 = pair._2 }
                    }
                  );
              }
              else
                scrut1 =
                  KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                    "unreachable (pattern matches are exhaustive in F*)");
              if (scrut1.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t ck = scrut1.v._1;
                Pulse_Lib_Slice_slice__uint8_t out2_ = split__uint8_t(out2, size2)._1;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(out2_);
                size_t
                len3 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2_),
                    len2);
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut0;
                if (len3 == (size_t)0U)
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut = split__uint8_t(out2_, len3);
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                  size_t len4 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len4),
                          ._2 = rem
                        }
                      }
                    );
                }
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut;
                if (scrut0.tag == FStar_Pervasives_Native_None)
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else if (scrut0.tag == FStar_Pervasives_Native_Some)
                {
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                  pair = scrut0.v;
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = { ._1 = pair._1, ._2 = pair._2 }
                      }
                    );
                }
                else
                  scrut =
                    KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                      "unreachable (pattern matches are exhaustive in F*)");
                if (scrut.tag == FStar_Pervasives_Native_Some)
                  if (COSE_Format_aux_env31_map_constraint_1(cbor_det_mk_map_entry(ck, scrut.v._1)))
                    pres = false;
                  else
                  {
                    size_t size1_ = size0 + size1;
                    size_t size2_ = size1_ + size2;
                    Pulse_Lib_Slice_slice__uint8_t out_ = split__uint8_t(out, size2_)._1;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out_);
                    if
                    (
                      cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out_),
                        aout_len,
                        size0,
                        size1_)
                    )
                    {
                      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
                      __anf0 = pc;
                      cbor_det_map_iterator_t pj2 = __anf0.cddl_map_iterator_contents;
                      bool pres2 = true;
                      bool test = cbor_det_map_iterator_is_empty(pj2);
                      bool cond = pres2 && !test;
                      while (cond)
                      {
                        cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj2);
                        if (!!__anf0.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
                          if (!__anf0.cddl_map_iterator_impl_validate_ex(elt))
                            pres2 =
                              !__anf0.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
                        bool test = cbor_det_map_iterator_is_empty(pj2);
                        cond = pres2 && !test;
                      }
                      pem = pres2;
                      psize = size2_;
                      pcount = count_;
                    }
                    else
                      pres = false;
                  }
                else
                {
                  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                    __FILE__,
                    __LINE__,
                    "unreachable (pattern matches are exhaustive in F*)");
                  KRML_HOST_EXIT(255U);
                }
              }
              else
              {
                KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                  __FILE__,
                  __LINE__,
                  "unreachable (pattern matches are exhaustive in F*)");
                KRML_HOST_EXIT(255U);
              }
            }
          }
        }
      }
      ite = pres;
    }
    else
      ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite = false;
  if (ite)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
    return
      cbor_det_serialize_map_to_array(count,
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_okp_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cose_key_okp(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_okp_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cose_key_okp(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_okp_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cose_key_okp(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_okp_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_cose_key(cbor_det_t c)
{
  return COSE_Format_validate_cose_key_okp(c);
}

COSE_Format_cose_key_okp COSE_Format_cose_key_right(COSE_Format_cose_key_okp x1)
{
  return x1;
}

COSE_Format_cose_key_okp COSE_Format_cose_key_left(COSE_Format_cose_key_okp x4)
{
  return x4;
}

/**
Parser for cose_key
*/
COSE_Format_cose_key_okp COSE_Format_parse_cose_key(cbor_det_t c)
{
  return COSE_Format_parse_cose_key_okp(c);
}

/**
Serializer for cose_key
*/
size_t
COSE_Format_serialize_cose_key(COSE_Format_cose_key_okp c, Pulse_Lib_Slice_slice__uint8_t out)
{
  return COSE_Format_serialize_cose_key_okp(c, out);
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_okp_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cose_key(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_okp_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cose_key(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_okp_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cose_key(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_key_okp_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_aux_env34_validate_1(cbor_det_array_iterator_t *pi)
{
  if (cbor_det_array_iterator_is_empty(pi[0U]))
    return false;
  else
    return COSE_Format_validate_evercddl_label(cbor_det_array_iterator_next(pi));
}

COSE_Format_evercddl_label COSE_Format_aux_env34_type_1_right(COSE_Format_evercddl_label x1)
{
  return x1;
}

COSE_Format_evercddl_label COSE_Format_aux_env34_type_1_left(COSE_Format_evercddl_label x4)
{
  return x4;
}

/**
Parser for aux_env34_type_1
*/
COSE_Format_evercddl_label COSE_Format_aux_env34_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t buf = c;
  return COSE_Format_parse_evercddl_label(cbor_det_array_iterator_next(&buf));
}

/**
Serializer for aux_env34_type_1
*/
bool
COSE_Format_aux_env34_serialize_1(
  COSE_Format_evercddl_label c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  uint64_t count = out_count[0U];
  if (count < 18446744073709551615ULL)
  {
    size_t size = out_size[0U];
    size_t size1 = COSE_Format_serialize_evercddl_label(c, split__uint8_t(out, size)._2);
    if (size1 == (size_t)0U)
      return false;
    else
    {
      out_count[0U] = count + 1ULL;
      out_size[0U] = size + size1;
      return true;
    }
  }
  else
    return false;
}

bool COSE_Format_aux_env34_map_constraint_2(cbor_det_map_entry_t x)
{
  cbor_det_t k = cbor_det_map_entry_key(x);
  bool ite0;
  if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
    ite0 = cbor_det_read_uint64(k) == 1ULL;
  else
    ite0 = false;
  bool ite1;
  if (ite0)
  {
    cbor_det_t v = cbor_det_map_entry_value(x);
    if (COSE_Format_validate_int(v))
      ite1 = true;
    else
      ite1 = COSE_Format_validate_tstr(v);
  }
  else
    ite1 = false;
  bool ite2;
  if (ite1)
    ite2 = true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite0;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
      ite0 = cbor_det_read_uint64(k1) == 2ULL;
    else
      ite0 = false;
    if (ite0)
    {
      cbor_det_t v = cbor_det_map_entry_value(x);
      if (cbor_det_major_type(v) == CBOR_MAJOR_TYPE_ARRAY)
      {
        cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(v);
        bool ite0;
        if (cbor_det_array_iterator_is_empty(pi))
          ite0 = false;
        else
          ite0 = COSE_Format_validate_evercddl_label(cbor_det_array_iterator_next(&pi));
        bool ite1;
        if (ite0)
        {
          bool pcont = true;
          while (pcont)
          {
            cbor_det_array_iterator_t i11 = pi;
            bool ite;
            if (cbor_det_array_iterator_is_empty(pi))
              ite = false;
            else
              ite = COSE_Format_validate_evercddl_label(cbor_det_array_iterator_next(&pi));
            if (!ite)
            {
              pi = i11;
              pcont = false;
            }
          }
          ite1 = true;
        }
        else
          ite1 = false;
        if (ite1)
          ite2 = cbor_det_array_iterator_is_empty(pi);
        else
          ite2 = false;
      }
      else
        ite2 = false;
    }
    else
      ite2 = false;
  }
  bool ite3;
  if (ite2)
    ite3 = true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k1) == 3ULL;
    else
      ite = false;
    if (ite)
    {
      cbor_det_t v = cbor_det_map_entry_value(x);
      if (COSE_Format_validate_tstr(v))
        ite3 = true;
      else
        ite3 = COSE_Format_validate_int(v);
    }
    else
      ite3 = false;
  }
  bool ite4;
  if (ite3)
    ite4 = true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k1) == 4ULL;
    else
      ite = false;
    if (ite)
      ite4 = COSE_Format_validate_bstr(cbor_det_map_entry_value(x));
    else
      ite4 = false;
  }
  bool ite5;
  if (ite4)
    ite5 = true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k1) == 5ULL;
    else
      ite = false;
    if (ite)
    {
      cbor_det_map_entry_value(x);
      ite5 = true;
    }
    else
      ite5 = false;
  }
  if (ite5)
    return true;
  else
  {
    cbor_det_t k1 = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k1) == 6ULL;
    else
      ite = false;
    if (ite)
    {
      cbor_det_map_entry_value(x);
      return true;
    }
    else
      return false;
  }
}

bool COSE_Format_validate_header_map(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t remaining = cbor_det_get_map_length(c);
    uint64_t i0 = remaining;
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest = c1;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
    if (cbor_det_map_get(c, c1, &dest))
      scrut0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest
          }
        );
    else
      scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    impl_map_group_result ite0;
    if (scrut0.tag == FStar_Pervasives_Native_None)
      ite0 = MGFail;
    else if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t cv = scrut0.v;
      bool ite;
      if (COSE_Format_validate_int(cv))
        ite = true;
      else
        ite = COSE_Format_validate_tstr(cv);
      if (ite)
      {
        remaining--;
        ite0 = MGOK;
      }
      else
        ite0 = MGFail;
    }
    else
      ite0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    impl_map_group_result sw0;
    switch (ite0)
    {
      case MGOK:
        {
          sw0 = MGOK;
          break;
        }
      case MGFail:
        {
          remaining = i0;
          sw0 = MGOK;
          break;
        }
      case MGCutFail:
        {
          sw0 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw1;
    switch (sw0)
    {
      case MGOK:
        {
          uint64_t i01 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite0;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite0 = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = scrut.v;
            bool ite1;
            if (cbor_det_major_type(cv) == CBOR_MAJOR_TYPE_ARRAY)
            {
              cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(cv);
              bool ite0;
              if (cbor_det_array_iterator_is_empty(pi))
                ite0 = false;
              else
                ite0 = COSE_Format_validate_evercddl_label(cbor_det_array_iterator_next(&pi));
              bool ite2;
              if (ite0)
              {
                bool pcont = true;
                while (pcont)
                {
                  cbor_det_array_iterator_t i11 = pi;
                  bool ite;
                  if (cbor_det_array_iterator_is_empty(pi))
                    ite = false;
                  else
                    ite = COSE_Format_validate_evercddl_label(cbor_det_array_iterator_next(&pi));
                  if (!ite)
                  {
                    pi = i11;
                    pcont = false;
                  }
                }
                ite2 = true;
              }
              else
                ite2 = false;
              if (ite2)
                ite1 = cbor_det_array_iterator_is_empty(pi);
              else
                ite1 = false;
            }
            else
              ite1 = false;
            if (ite1)
            {
              remaining--;
              ite0 = MGOK;
            }
            else
              ite0 = MGFail;
          }
          else
            ite0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite0)
          {
            case MGOK:
              {
                sw1 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i01;
                sw1 = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw1 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw1 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw1 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw2;
    switch (sw1)
    {
      case MGOK:
        {
          uint64_t i01 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite0;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite0 = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = scrut.v;
            bool ite;
            if (COSE_Format_validate_tstr(cv))
              ite = true;
            else
              ite = COSE_Format_validate_int(cv);
            if (ite)
            {
              remaining--;
              ite0 = MGOK;
            }
            else
              ite0 = MGFail;
          }
          else
            ite0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite0)
          {
            case MGOK:
              {
                sw2 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i01;
                sw2 = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw2 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw2 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw2 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw3;
    switch (sw2)
    {
      case MGOK:
        {
          uint64_t i01 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            if (COSE_Format_validate_bstr(scrut.v))
            {
              remaining--;
              ite = MGOK;
            }
            else
              ite = MGFail;
          else
            ite =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite)
          {
            case MGOK:
              {
                sw3 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i01;
                sw3 = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw3 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw3 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw3 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw4;
    switch (sw3)
    {
      case MGOK:
        {
          uint64_t i01 = remaining;
          cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
          cbor_det_t dest1 = c2;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
          if (cbor_det_map_get(c, c2, &dest1))
            scrut0 =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest1
                }
              );
          else
            scrut0 =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite0;
          if (scrut0.tag == FStar_Pervasives_Native_None)
            ite0 = MGFail;
          else if (scrut0.tag == FStar_Pervasives_Native_Some)
            if (COSE_Format_validate_bstr(scrut0.v))
            {
              remaining--;
              ite0 = MGOK;
            }
            else
              ite0 = MGFail;
          else
            ite0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          impl_map_group_result sw0;
          switch (ite0)
          {
            case MGOK:
              {
                uint64_t i02 = remaining;
                cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                cbor_det_t dest2 = c3;
                option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
                if (cbor_det_map_get(c, c3, &dest2))
                  scrut =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = dest2
                      }
                    );
                else
                  scrut =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                impl_map_group_result ite;
                if (scrut.tag == FStar_Pervasives_Native_None)
                  ite = MGFail;
                else if (scrut.tag == FStar_Pervasives_Native_Some)
                  if (COSE_Format_validate_everparsenomatch(scrut.v))
                  {
                    remaining--;
                    ite = MGOK;
                  }
                  else
                    ite = MGCutFail;
                else
                  ite =
                    KRML_EABORT(impl_map_group_result,
                      "unreachable (pattern matches are exhaustive in F*)");
                switch (ite)
                {
                  case MGOK:
                    {
                      sw0 = MGOK;
                      break;
                    }
                  case MGFail:
                    {
                      remaining = i02;
                      sw0 = MGOK;
                      break;
                    }
                  case MGCutFail:
                    {
                      sw0 = MGCutFail;
                      break;
                    }
                  default:
                    {
                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                      KRML_HOST_EXIT(253U);
                    }
                }
                break;
              }
            case MGFail:
              {
                sw0 = MGFail;
                break;
              }
            case MGCutFail:
              {
                sw0 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          switch (sw0)
          {
            case MGOK:
              {
                sw4 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i01;
                uint64_t i02 = remaining;
                cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                cbor_det_t dest2 = c3;
                option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
                if (cbor_det_map_get(c, c3, &dest2))
                  scrut0 =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = dest2
                      }
                    );
                else
                  scrut0 =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                impl_map_group_result ite0;
                if (scrut0.tag == FStar_Pervasives_Native_None)
                  ite0 = MGFail;
                else if (scrut0.tag == FStar_Pervasives_Native_Some)
                  if (COSE_Format_validate_bstr(scrut0.v))
                  {
                    remaining--;
                    ite0 = MGOK;
                  }
                  else
                    ite0 = MGFail;
                else
                  ite0 =
                    KRML_EABORT(impl_map_group_result,
                      "unreachable (pattern matches are exhaustive in F*)");
                impl_map_group_result sw0;
                switch (ite0)
                {
                  case MGOK:
                    {
                      uint64_t i03 = remaining;
                      cbor_det_t c4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
                      cbor_det_t dest3 = c4;
                      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
                      if (cbor_det_map_get(c, c4, &dest3))
                        scrut =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_Some,
                              .v = dest3
                            }
                          );
                      else
                        scrut =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_None
                            }
                          );
                      impl_map_group_result ite;
                      if (scrut.tag == FStar_Pervasives_Native_None)
                        ite = MGFail;
                      else if (scrut.tag == FStar_Pervasives_Native_Some)
                        if (COSE_Format_validate_everparsenomatch(scrut.v))
                        {
                          remaining--;
                          ite = MGOK;
                        }
                        else
                          ite = MGCutFail;
                      else
                        ite =
                          KRML_EABORT(impl_map_group_result,
                            "unreachable (pattern matches are exhaustive in F*)");
                      switch (ite)
                      {
                        case MGOK:
                          {
                            sw0 = MGOK;
                            break;
                          }
                        case MGFail:
                          {
                            remaining = i03;
                            sw0 = MGOK;
                            break;
                          }
                        case MGCutFail:
                          {
                            sw0 = MGCutFail;
                            break;
                          }
                        default:
                          {
                            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                              __FILE__,
                              __LINE__);
                            KRML_HOST_EXIT(253U);
                          }
                      }
                      break;
                    }
                  case MGFail:
                    {
                      sw0 = MGFail;
                      break;
                    }
                  case MGCutFail:
                    {
                      sw0 = MGCutFail;
                      break;
                    }
                  default:
                    {
                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                      KRML_HOST_EXIT(253U);
                    }
                }
                switch (sw0)
                {
                  case MGOK:
                    {
                      sw4 = MGOK;
                      break;
                    }
                  case MGFail:
                    {
                      remaining = i02;
                      uint64_t i03 = remaining;
                      cbor_det_t c4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                      cbor_det_t dest3 = c4;
                      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
                      if (cbor_det_map_get(c, c4, &dest3))
                        scrut0 =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_Some,
                              .v = dest3
                            }
                          );
                      else
                        scrut0 =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_None
                            }
                          );
                      impl_map_group_result ite0;
                      if (scrut0.tag == FStar_Pervasives_Native_None)
                        ite0 = MGFail;
                      else if (scrut0.tag == FStar_Pervasives_Native_Some)
                        if (COSE_Format_validate_everparsenomatch(scrut0.v))
                        {
                          remaining--;
                          ite0 = MGOK;
                        }
                        else
                          ite0 = MGCutFail;
                      else
                        ite0 =
                          KRML_EABORT(impl_map_group_result,
                            "unreachable (pattern matches are exhaustive in F*)");
                      impl_map_group_result sw;
                      switch (ite0)
                      {
                        case MGOK:
                          {
                            sw = MGOK;
                            break;
                          }
                        case MGFail:
                          {
                            remaining = i03;
                            sw = MGOK;
                            break;
                          }
                        case MGCutFail:
                          {
                            sw = MGCutFail;
                            break;
                          }
                        default:
                          {
                            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                              __FILE__,
                              __LINE__);
                            KRML_HOST_EXIT(253U);
                          }
                      }
                      switch (sw)
                      {
                        case MGOK:
                          {
                            uint64_t i04 = remaining;
                            cbor_det_t c5 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
                            cbor_det_t dest4 = c5;
                            option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
                            if (cbor_det_map_get(c, c5, &dest4))
                              scrut =
                                (
                                  (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                                    .tag = FStar_Pervasives_Native_Some,
                                    .v = dest4
                                  }
                                );
                            else
                              scrut =
                                (
                                  (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                                    .tag = FStar_Pervasives_Native_None
                                  }
                                );
                            impl_map_group_result ite;
                            if (scrut.tag == FStar_Pervasives_Native_None)
                              ite = MGFail;
                            else if (scrut.tag == FStar_Pervasives_Native_Some)
                              if (COSE_Format_validate_everparsenomatch(scrut.v))
                              {
                                remaining--;
                                ite = MGOK;
                              }
                              else
                                ite = MGCutFail;
                            else
                              ite =
                                KRML_EABORT(impl_map_group_result,
                                  "unreachable (pattern matches are exhaustive in F*)");
                            switch (ite)
                            {
                              case MGOK:
                                {
                                  sw4 = MGOK;
                                  break;
                                }
                              case MGFail:
                                {
                                  remaining = i04;
                                  sw4 = MGOK;
                                  break;
                                }
                              case MGCutFail:
                                {
                                  sw4 = MGCutFail;
                                  break;
                                }
                              default:
                                {
                                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                    __FILE__,
                                    __LINE__);
                                  KRML_HOST_EXIT(253U);
                                }
                            }
                            break;
                          }
                        case MGFail:
                          {
                            sw4 = MGFail;
                            break;
                          }
                        case MGCutFail:
                          {
                            sw4 = MGCutFail;
                            break;
                          }
                        default:
                          {
                            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                              __FILE__,
                              __LINE__);
                            KRML_HOST_EXIT(253U);
                          }
                      }
                      break;
                    }
                  case MGCutFail:
                    {
                      sw4 = MGCutFail;
                      break;
                    }
                  default:
                    {
                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                      KRML_HOST_EXIT(253U);
                    }
                }
                break;
              }
            case MGCutFail:
              {
                sw4 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw4 = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw4 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result sw;
    switch (sw4)
    {
      case MGOK:
        {
          cbor_det_map_iterator_t pj = cbor_det_map_iterator_start(c);
          while (!cbor_det_map_iterator_is_empty(pj))
          {
            cbor_det_map_entry_t chd = cbor_det_map_iterator_next(&pj);
            bool ite0;
            if (COSE_Format_validate_evercddl_label(cbor_det_map_entry_key(chd)))
              ite0 = COSE_Format_validate_values(cbor_det_map_entry_value(chd));
            else
              ite0 = false;
            bool ite1;
            if (ite0)
            {
              cbor_det_t k1 = cbor_det_map_entry_key(chd);
              bool ite0;
              if (cbor_det_major_type(k1) == CBOR_MAJOR_TYPE_UINT64)
                ite0 = cbor_det_read_uint64(k1) == 1ULL;
              else
                ite0 = false;
              bool ite2;
              if (ite0)
              {
                cbor_det_t v = cbor_det_map_entry_value(chd);
                if (COSE_Format_validate_int(v))
                  ite2 = true;
                else
                  ite2 = COSE_Format_validate_tstr(v);
              }
              else
                ite2 = false;
              bool ite3;
              if (ite2)
                ite3 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite0;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_UINT64)
                  ite0 = cbor_det_read_uint64(k2) == 2ULL;
                else
                  ite0 = false;
                if (ite0)
                {
                  cbor_det_t v = cbor_det_map_entry_value(chd);
                  if (cbor_det_major_type(v) == CBOR_MAJOR_TYPE_ARRAY)
                  {
                    cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(v);
                    bool ite0;
                    if (cbor_det_array_iterator_is_empty(pi))
                      ite0 = false;
                    else
                      ite0 = COSE_Format_validate_evercddl_label(cbor_det_array_iterator_next(&pi));
                    bool ite1;
                    if (ite0)
                    {
                      bool pcont = true;
                      while (pcont)
                      {
                        cbor_det_array_iterator_t i11 = pi;
                        bool ite;
                        if (cbor_det_array_iterator_is_empty(pi))
                          ite = false;
                        else
                          ite =
                            COSE_Format_validate_evercddl_label(cbor_det_array_iterator_next(&pi));
                        if (!ite)
                        {
                          pi = i11;
                          pcont = false;
                        }
                      }
                      ite1 = true;
                    }
                    else
                      ite1 = false;
                    if (ite1)
                      ite3 = cbor_det_array_iterator_is_empty(pi);
                    else
                      ite3 = false;
                  }
                  else
                    ite3 = false;
                }
                else
                  ite3 = false;
              }
              bool ite4;
              if (ite3)
                ite4 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k2) == 3ULL;
                else
                  ite = false;
                if (ite)
                {
                  cbor_det_t v = cbor_det_map_entry_value(chd);
                  if (COSE_Format_validate_tstr(v))
                    ite4 = true;
                  else
                    ite4 = COSE_Format_validate_int(v);
                }
                else
                  ite4 = false;
              }
              bool ite5;
              if (ite4)
                ite5 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k2) == 4ULL;
                else
                  ite = false;
                if (ite)
                  ite5 = COSE_Format_validate_bstr(cbor_det_map_entry_value(chd));
                else
                  ite5 = false;
              }
              bool ite6;
              if (ite5)
                ite6 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k2) == 5ULL;
                else
                  ite = false;
                if (ite)
                {
                  cbor_det_map_entry_value(chd);
                  ite6 = true;
                }
                else
                  ite6 = false;
              }
              bool ite7;
              if (ite6)
                ite7 = true;
              else
              {
                cbor_det_t k2 = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k2) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k2) == 6ULL;
                else
                  ite = false;
                if (ite)
                {
                  cbor_det_map_entry_value(chd);
                  ite7 = true;
                }
                else
                  ite7 = false;
              }
              ite1 = !ite7;
            }
            else
              ite1 = false;
            if (!!ite1)
              remaining--;
          }
          sw = MGOK;
          break;
        }
      case MGFail:
        {
          sw = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (sw)
    {
      case MGOK:
        {
          return remaining == 0ULL;
        }
      case MGFail:
        {
          return false;
        }
      case MGCutFail:
        {
          return false;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
  else
    return false;
}

COSE_Format_header_map COSE_Format_header_map_right(COSE_Format_header_map_ugly x6)
{
  return
    (
      (COSE_Format_header_map){
        .intkey1 = x6._1._1._1._1._1,
        .intkey2 = x6._1._1._1._1._2,
        .intkey3 = x6._1._1._1._2,
        .intkey4 = x6._1._1._2,
        ._x0 = x6._1._2,
        ._x1 = x6._2
      }
    );
}

COSE_Format_header_map_ugly COSE_Format_header_map_left(COSE_Format_header_map x14)
{
  return
    (
      (COSE_Format_header_map_ugly){
        ._1 = {
          ._1 = {
            ._1 = { ._1 = { ._1 = x14.intkey1, ._2 = x14.intkey2 }, ._2 = x14.intkey3 },
            ._2 = x14.intkey4
          },
          ._2 = x14._x0
        },
        ._2 = x14._x1
      }
    );
}

/**
Parser for header_map
*/
COSE_Format_header_map COSE_Format_parse_header_map(cbor_det_t c)
{
  uint64_t buf0 = 0ULL;
  KRML_HOST_IGNORE(&buf0);
  cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
  cbor_det_t dest = c1;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
  if (cbor_det_map_get(c, c1, &dest))
    scrut0 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest
        }
      );
  else
    scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite0;
  if (scrut0.tag == FStar_Pervasives_Native_None)
    ite0 = MGFail;
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = scrut0.v;
    bool ite;
    if (COSE_Format_validate_int(cv))
      ite = true;
    else
      ite = COSE_Format_validate_tstr(cv);
    if (ite)
      ite0 = MGOK;
    else
      ite0 = MGFail;
  }
  else
    ite0 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite1;
  if (ite0 == MGOK)
    ite1 = true;
  else
    ite1 = false;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly w1;
  if (ite1)
  {
    cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest1 = c2;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c2, &dest1))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest1
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    COSE_Format_evercddl_label_ugly ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      if (COSE_Format_validate_int(w))
        ite =
          (
            (COSE_Format_evercddl_label_ugly){
              .tag = COSE_Format_Inl,
              { .case_Inl = COSE_Format_parse_int(w) }
            }
          );
      else
        ite =
          (
            (COSE_Format_evercddl_label_ugly){
              .tag = COSE_Format_Inr,
              { .case_Inr = COSE_Format_parse_tstr(w) }
            }
          );
    }
    else
      ite =
        KRML_EABORT(COSE_Format_evercddl_label_ugly,
          "unreachable (pattern matches are exhaustive in F*)");
    w1 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    w1 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly){
          .tag = FStar_Pervasives_Native_None
        }
      );
  uint64_t buf1 = 0ULL;
  KRML_HOST_IGNORE(&buf1);
  cbor_det_t c2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
  cbor_det_t dest1 = c2;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
  if (cbor_det_map_get(c, c2, &dest1))
    scrut1 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest1
        }
      );
  else
    scrut1 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite2;
  if (scrut1.tag == FStar_Pervasives_Native_None)
    ite2 = MGFail;
  else if (scrut1.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = scrut1.v;
    bool ite0;
    if (cbor_det_major_type(cv) == CBOR_MAJOR_TYPE_ARRAY)
    {
      cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(cv);
      bool ite1;
      if (cbor_det_array_iterator_is_empty(pi))
        ite1 = false;
      else
        ite1 = COSE_Format_validate_evercddl_label(cbor_det_array_iterator_next(&pi));
      bool ite2;
      if (ite1)
      {
        bool pcont = true;
        while (pcont)
        {
          cbor_det_array_iterator_t i11 = pi;
          bool ite;
          if (cbor_det_array_iterator_is_empty(pi))
            ite = false;
          else
            ite = COSE_Format_validate_evercddl_label(cbor_det_array_iterator_next(&pi));
          if (!ite)
          {
            pi = i11;
            pcont = false;
          }
        }
        ite2 = true;
      }
      else
        ite2 = false;
      if (ite2)
        ite0 = cbor_det_array_iterator_is_empty(pi);
      else
        ite0 = false;
    }
    else
      ite0 = false;
    if (ite0)
      ite2 = MGOK;
    else
      ite2 = MGFail;
  }
  else
    ite2 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite3;
  if (ite2 == MGOK)
    ite3 = true;
  else
    ite3 = false;
  FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
  ite4;
  if (ite3)
  {
    cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
    cbor_det_t dest2 = c3;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c3, &dest2))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest2
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
    ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
      ite =
        (
          (FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label){
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_array_iterator_contents = cbor_det_array_iterator_start(scrut.v),
                .cddl_array_iterator_impl_validate = COSE_Format_aux_env34_validate_1,
                .cddl_array_iterator_impl_parse = COSE_Format_aux_env34_parse_1
              }
            }
          }
        );
    else
      ite =
        KRML_EABORT(FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label,
          "unreachable (pattern matches are exhaustive in F*)");
    ite4 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite4 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
  w11 = { ._1 = w1, ._2 = ite4 };
  uint64_t buf2 = 0ULL;
  KRML_HOST_IGNORE(&buf2);
  cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
  cbor_det_t dest2 = c3;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut2;
  if (cbor_det_map_get(c, c3, &dest2))
    scrut2 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest2
        }
      );
  else
    scrut2 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite5;
  if (scrut2.tag == FStar_Pervasives_Native_None)
    ite5 = MGFail;
  else if (scrut2.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = scrut2.v;
    bool ite;
    if (COSE_Format_validate_tstr(cv))
      ite = true;
    else
      ite = COSE_Format_validate_int(cv);
    if (ite)
      ite5 = MGOK;
    else
      ite5 = MGFail;
  }
  else
    ite5 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite6;
  if (ite5 == MGOK)
    ite6 = true;
  else
    ite6 = false;
  FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly ite7;
  if (ite6)
  {
    cbor_det_t c4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
    cbor_det_t dest3 = c4;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c4, &dest3))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest3
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    COSE_Format_aux_env29_type_1_ugly ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      if (COSE_Format_validate_tstr(w))
        ite =
          (
            (COSE_Format_aux_env29_type_1_ugly){
              .tag = COSE_Format_Inl,
              { .case_Inl = COSE_Format_parse_tstr(w) }
            }
          );
      else
        ite =
          (
            (COSE_Format_aux_env29_type_1_ugly){
              .tag = COSE_Format_Inr,
              { .case_Inr = COSE_Format_parse_int(w) }
            }
          );
    }
    else
      ite =
        KRML_EABORT(COSE_Format_aux_env29_type_1_ugly,
          "unreachable (pattern matches are exhaustive in F*)");
    ite7 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite7 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly
  w12 = { ._1 = w11, ._2 = ite7 };
  uint64_t buf3 = 0ULL;
  KRML_HOST_IGNORE(&buf3);
  cbor_det_t c4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
  cbor_det_t dest3 = c4;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut3;
  if (cbor_det_map_get(c, c4, &dest3))
    scrut3 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest3
        }
      );
  else
    scrut3 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite8;
  if (scrut3.tag == FStar_Pervasives_Native_None)
    ite8 = MGFail;
  else if (scrut3.tag == FStar_Pervasives_Native_Some)
    if (COSE_Format_validate_bstr(scrut3.v))
      ite8 = MGOK;
    else
      ite8 = MGFail;
  else
    ite8 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  bool ite9;
  if (ite8 == MGOK)
    ite9 = true;
  else
    ite9 = false;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t ite10;
  if (ite9)
  {
    cbor_det_t c5 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
    cbor_det_t dest4 = c5;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c5, &dest4))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest4
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    Pulse_Lib_Slice_slice__uint8_t ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
      ite = COSE_Format_parse_bstr(scrut.v);
    else
      ite =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    ite10 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite10 =
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  w13 = { ._1 = w12, ._2 = ite10 };
  uint64_t dummy = 0ULL;
  cbor_det_t c5 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
  cbor_det_t dest4 = c5;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut4;
  if (cbor_det_map_get(c, c5, &dest4))
    scrut4 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest4
        }
      );
  else
    scrut4 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite11;
  if (scrut4.tag == FStar_Pervasives_Native_None)
    ite11 = MGFail;
  else if (scrut4.tag == FStar_Pervasives_Native_Some)
    if (COSE_Format_validate_bstr(scrut4.v))
      ite11 = MGOK;
    else
      ite11 = MGFail;
  else
    ite11 =
      KRML_EABORT(impl_map_group_result,
        "unreachable (pattern matches are exhaustive in F*)");
  impl_map_group_result sw0;
  switch (ite11)
  {
    case MGOK:
      {
        uint64_t i0 = dummy;
        cbor_det_t c6 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
        cbor_det_t dest5 = c6;
        option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
        if (cbor_det_map_get(c, c6, &dest5))
          scrut =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = dest5
              }
            );
        else
          scrut =
            ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        impl_map_group_result ite;
        if (scrut.tag == FStar_Pervasives_Native_None)
          ite = MGFail;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          if (COSE_Format_validate_everparsenomatch(scrut.v))
            ite = MGOK;
          else
            ite = MGCutFail;
        else
          ite =
            KRML_EABORT(impl_map_group_result,
              "unreachable (pattern matches are exhaustive in F*)");
        switch (ite)
        {
          case MGOK:
            {
              sw0 = MGOK;
              break;
            }
          case MGFail:
            {
              dummy = i0;
              sw0 = MGOK;
              break;
            }
          case MGCutFail:
            {
              sw0 = MGCutFail;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        break;
      }
    case MGFail:
      {
        sw0 = MGFail;
        break;
      }
    case MGCutFail:
      {
        sw0 = MGCutFail;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  bool ite12;
  if (sw0 == MGOK)
    ite12 = true;
  else
    ite12 = false;
  FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____
  ite13;
  if (ite12)
  {
    cbor_det_t c6 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
    cbor_det_t dest5 = c6;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
    if (cbor_det_map_get(c, c6, &dest5))
      scrut0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest5
          }
        );
    else
      scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    Pulse_Lib_Slice_slice__uint8_t w14;
    if (scrut0.tag == FStar_Pervasives_Native_Some)
      w14 = COSE_Format_parse_bstr(scrut0.v);
    else
      w14 =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    uint64_t buf = 0ULL;
    KRML_HOST_IGNORE(&buf);
    cbor_det_t c7 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
    cbor_det_t dest6 = c7;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
    if (cbor_det_map_get(c, c7, &dest6))
      scrut1 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest6
          }
        );
    else
      scrut1 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    impl_map_group_result ite0;
    if (scrut1.tag == FStar_Pervasives_Native_None)
      ite0 = MGFail;
    else if (scrut1.tag == FStar_Pervasives_Native_Some)
      if (COSE_Format_validate_everparsenomatch(scrut1.v))
        ite0 = MGOK;
      else
        ite0 = MGCutFail;
    else
      ite0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    bool ite1;
    if (ite0 == MGOK)
      ite1 = true;
    else
      ite1 = false;
    FStar_Pervasives_Native_option__size_t_tags ite;
    if (ite1)
    {
      cbor_det_t c8 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
      cbor_det_t dest7 = c8;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
      if (cbor_det_map_get(c, c8, &dest7))
        scrut =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest7
            }
          );
      else
        scrut =
          ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      if (scrut.tag == FStar_Pervasives_Native_Some)
        COSE_Format_parse_everparsenomatch(scrut.v);
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
      ite = FStar_Pervasives_Native_Some;
    }
    else
      ite = FStar_Pervasives_Native_None;
    ite13 =
      (
        (FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____){
          .tag = COSE_Format_Inl,
          { .case_Inl = { ._1 = w14, ._2 = ite } }
        }
      );
  }
  else
  {
    uint64_t dummy1 = 0ULL;
    cbor_det_t c6 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
    cbor_det_t dest5 = c6;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
    if (cbor_det_map_get(c, c6, &dest5))
      scrut0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest5
          }
        );
    else
      scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    impl_map_group_result ite0;
    if (scrut0.tag == FStar_Pervasives_Native_None)
      ite0 = MGFail;
    else if (scrut0.tag == FStar_Pervasives_Native_Some)
      if (COSE_Format_validate_bstr(scrut0.v))
        ite0 = MGOK;
      else
        ite0 = MGFail;
    else
      ite0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    impl_map_group_result sw;
    switch (ite0)
    {
      case MGOK:
        {
          uint64_t i0 = dummy1;
          cbor_det_t c7 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
          cbor_det_t dest6 = c7;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c7, &dest6))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest6
                }
              );
          else
            scrut =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result ite;
          if (scrut.tag == FStar_Pervasives_Native_None)
            ite = MGFail;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            if (COSE_Format_validate_everparsenomatch(scrut.v))
              ite = MGOK;
            else
              ite = MGCutFail;
          else
            ite =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          switch (ite)
          {
            case MGOK:
              {
                sw = MGOK;
                break;
              }
            case MGFail:
              {
                dummy1 = i0;
                sw = MGOK;
                break;
              }
            case MGCutFail:
              {
                sw = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          break;
        }
      case MGFail:
        {
          sw = MGFail;
          break;
        }
      case MGCutFail:
        {
          sw = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    bool ite1;
    if (sw == MGOK)
      ite1 = true;
    else
      ite1 = false;
    FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____
    ite2;
    if (ite1)
    {
      cbor_det_t c7 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
      cbor_det_t dest6 = c7;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
      if (cbor_det_map_get(c, c7, &dest6))
        scrut0 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest6
            }
          );
      else
        scrut0 =
          ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      Pulse_Lib_Slice_slice__uint8_t w14;
      if (scrut0.tag == FStar_Pervasives_Native_Some)
        w14 = COSE_Format_parse_bstr(scrut0.v);
      else
        w14 =
          KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
            "unreachable (pattern matches are exhaustive in F*)");
      uint64_t buf = 0ULL;
      KRML_HOST_IGNORE(&buf);
      cbor_det_t c8 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
      cbor_det_t dest7 = c8;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
      if (cbor_det_map_get(c, c8, &dest7))
        scrut1 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest7
            }
          );
      else
        scrut1 =
          ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      impl_map_group_result ite0;
      if (scrut1.tag == FStar_Pervasives_Native_None)
        ite0 = MGFail;
      else if (scrut1.tag == FStar_Pervasives_Native_Some)
        if (COSE_Format_validate_everparsenomatch(scrut1.v))
          ite0 = MGOK;
        else
          ite0 = MGCutFail;
      else
        ite0 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      bool ite1;
      if (ite0 == MGOK)
        ite1 = true;
      else
        ite1 = false;
      FStar_Pervasives_Native_option__size_t_tags ite;
      if (ite1)
      {
        cbor_det_t c9 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        cbor_det_t dest8 = c9;
        option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
        if (cbor_det_map_get(c, c9, &dest8))
          scrut =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = dest8
              }
            );
        else
          scrut =
            ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        if (scrut.tag == FStar_Pervasives_Native_Some)
          COSE_Format_parse_everparsenomatch(scrut.v);
        else
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
        ite = FStar_Pervasives_Native_Some;
      }
      else
        ite = FStar_Pervasives_Native_None;
      ite2 =
        (
          (FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____){
            .tag = COSE_Format_Inl,
            { .case_Inl = { ._1 = w14, ._2 = ite } }
          }
        );
    }
    else
    {
      uint64_t buf0 = 0ULL;
      KRML_HOST_IGNORE(&buf0);
      cbor_det_t c7 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
      cbor_det_t dest6 = c7;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
      if (cbor_det_map_get(c, c7, &dest6))
        scrut0 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest6
            }
          );
      else
        scrut0 =
          ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      impl_map_group_result ite0;
      if (scrut0.tag == FStar_Pervasives_Native_None)
        ite0 = MGFail;
      else if (scrut0.tag == FStar_Pervasives_Native_Some)
        if (COSE_Format_validate_everparsenomatch(scrut0.v))
          ite0 = MGOK;
        else
          ite0 = MGCutFail;
      else
        ite0 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      bool ite1;
      if (ite0 == MGOK)
        ite1 = true;
      else
        ite1 = false;
      FStar_Pervasives_Native_option__size_t_tags w14;
      if (ite1)
      {
        cbor_det_t c8 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
        cbor_det_t dest7 = c8;
        option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
        if (cbor_det_map_get(c, c8, &dest7))
          scrut =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = dest7
              }
            );
        else
          scrut =
            ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        if (scrut.tag == FStar_Pervasives_Native_Some)
          COSE_Format_parse_everparsenomatch(scrut.v);
        else
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
        w14 = FStar_Pervasives_Native_Some;
      }
      else
        w14 = FStar_Pervasives_Native_None;
      uint64_t buf = 0ULL;
      KRML_HOST_IGNORE(&buf);
      cbor_det_t c8 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
      cbor_det_t dest7 = c8;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
      if (cbor_det_map_get(c, c8, &dest7))
        scrut1 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest7
            }
          );
      else
        scrut1 =
          ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      impl_map_group_result ite3;
      if (scrut1.tag == FStar_Pervasives_Native_None)
        ite3 = MGFail;
      else if (scrut1.tag == FStar_Pervasives_Native_Some)
        if (COSE_Format_validate_everparsenomatch(scrut1.v))
          ite3 = MGOK;
        else
          ite3 = MGCutFail;
      else
        ite3 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      bool ite4;
      if (ite3 == MGOK)
        ite4 = true;
      else
        ite4 = false;
      FStar_Pervasives_Native_option__size_t_tags ite;
      if (ite4)
      {
        cbor_det_t c9 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        cbor_det_t dest8 = c9;
        option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
        if (cbor_det_map_get(c, c9, &dest8))
          scrut =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = dest8
              }
            );
        else
          scrut =
            ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        if (scrut.tag == FStar_Pervasives_Native_Some)
          COSE_Format_parse_everparsenomatch(scrut.v);
        else
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
        ite = FStar_Pervasives_Native_Some;
      }
      else
        ite = FStar_Pervasives_Native_None;
      ite2 =
        (
          (FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____){
            .tag = COSE_Format_Inr,
            { .case_Inr = { ._1 = w14, ._2 = ite } }
          }
        );
    }
    ite13 =
      (
        (FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____){
          .tag = COSE_Format_Inr,
          { .case_Inr = ite2 }
        }
      );
  }
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____
  w14 = { ._1 = w13, ._2 = ite13 };
  return
    COSE_Format_header_map_right((
        (COSE_Format_header_map_ugly){
          ._1 = w14,
          ._2 = {
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_map_iterator_contents = cbor_det_map_iterator_start(c),
                .cddl_map_iterator_impl_validate1 = COSE_Format_validate_evercddl_label,
                .cddl_map_iterator_impl_parse1 = COSE_Format_parse_evercddl_label,
                .cddl_map_iterator_impl_validate_ex = COSE_Format_aux_env34_map_constraint_2,
                .cddl_map_iterator_impl_validate2 = COSE_Format_validate_values,
                .cddl_map_iterator_impl_parse2 = COSE_Format_parse_values
              }
            }
          }
        }
      ));
}

static size_t
len__COSE_Format_evercddl_label(Pulse_Lib_Slice_slice__COSE_Format_evercddl_label s)
{
  return s.len;
}

static COSE_Format_evercddl_label
op_Array_Access__COSE_Format_evercddl_label(
  Pulse_Lib_Slice_slice__COSE_Format_evercddl_label a,
  size_t i
)
{
  return a.elt[i];
}

/**
Serializer for header_map
*/
size_t
COSE_Format_serialize_header_map(COSE_Format_header_map c, Pulse_Lib_Slice_slice__uint8_t out)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_header_map_ugly scrut0 = COSE_Format_header_map_left(c);
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____
  c1 = scrut0._1;
  FStar_Pervasives_either__Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  c2 = scrut0._2;
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly_FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
  c110 = c1._1;
  FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____
  c210 = c1._2;
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly
  c120 = c110._1;
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t c220 = c110._2;
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly_FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
  c130 = c120._1;
  FStar_Pervasives_Native_option__COSE_Format_aux_env29_type_1_ugly c230 = c120._2;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_label_ugly c140 = c130._1;
  FStar_Pervasives_Native_option__FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
  c240 = c130._2;
  bool ite0;
  if (c140.tag == FStar_Pervasives_Native_Some)
  {
    COSE_Format_evercddl_label_ugly c15 = c140.v;
    uint64_t count = pcount;
    if (count < 18446744073709551615ULL)
    {
      size_t size0 = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
      cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
      size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
      option__size_t scrut;
      if (len > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(c3,
                Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                len)
            }
          );
      else
        scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      size_t res1;
      if (scrut.tag == FStar_Pervasives_Native_None)
        res1 = (size_t)0U;
      else if (scrut.tag == FStar_Pervasives_Native_Some)
        res1 = scrut.v;
      else
        res1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (res1 > (size_t)0U)
      {
        size_t size1 = size0 + res1;
        Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1)._2;
        size_t res2;
        if (c15.tag == COSE_Format_Inl)
          res2 = COSE_Format_serialize_int(c15.case_Inl, out2);
        else if (c15.tag == COSE_Format_Inr)
          res2 = COSE_Format_serialize_tstr(c15.case_Inr, out2);
        else
          res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res2 > (size_t)0U)
        {
          size_t size2 = size1 + res2;
          Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
          size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
          if
          (
            cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
              aout_len,
              size0,
              size1)
          )
          {
            psize = size2;
            pcount = count + 1ULL;
            ite0 = true;
          }
          else
            ite0 = false;
        }
        else
          ite0 = false;
      }
      else
        ite0 = false;
    }
    else
      ite0 = false;
  }
  else if (c140.tag == FStar_Pervasives_Native_None)
    ite0 = true;
  else
    ite0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  bool ite1;
  if (ite0)
    if (c240.tag == FStar_Pervasives_Native_Some)
    {
      FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
      c15 = c240.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1)._2;
          uint64_t pcount1 = 0ULL;
          size_t psize1 = (size_t)0U;
          bool ite;
          if (c15.tag == COSE_Format_Inl)
          {
            Pulse_Lib_Slice_slice__COSE_Format_evercddl_label c16 = c15.case_Inl;
            if (len__COSE_Format_evercddl_label(c16) == (size_t)0U)
              ite = false;
            else
            {
              bool pres = true;
              size_t pi = (size_t)0U;
              size_t slen1 = len__COSE_Format_evercddl_label(c16);
              while (pres && pi < slen1)
              {
                size_t i = pi;
                if
                (
                  COSE_Format_aux_env34_serialize_1(op_Array_Access__COSE_Format_evercddl_label(c16,
                      i),
                    out2,
                    &pcount1,
                    &psize1)
                )
                  pi = i + (size_t)1U;
                else
                  pres = false;
              }
              ite = pres;
            }
          }
          else if (c15.tag == COSE_Format_Inr)
          {
            CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
            c25 = c15.case_Inr;
            if (cbor_det_array_iterator_is_empty(c25.cddl_array_iterator_contents))
              ite = false;
            else
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
              pc = c25;
              bool pres = true;
              bool em1 = cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
              bool cond = pres && !em1;
              while (cond)
              {
                CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
                i = pc;
                uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
                cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
                KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
                cbor_det_array_iterator_t ji = pj;
                uint64_t len1 = cbor_det_array_iterator_length(ji);
                pc =
                  (
                    (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label){
                      .cddl_array_iterator_contents = ji,
                      .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
                      .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
                    }
                  );
                if
                (
                  !COSE_Format_aux_env34_serialize_1(i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
                        len0 - len1)),
                    out2,
                    &pcount1,
                    &psize1)
                )
                  pres = false;
                bool em1 = cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
                cond = pres && !em1;
              }
              bool ret = pres;
              ite = ret ? ret : ret;
            }
          }
          else
            ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          size_t res21;
          if (ite)
          {
            size_t size = psize1;
            uint64_t count1 = pcount1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out2);
            res21 =
              cbor_det_serialize_array_to_array(count1,
                Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2),
                aout_len,
                size);
          }
          else
            res21 = (size_t)0U;
          if (res21 > (size_t)0U)
          {
            size_t size2 = size1 + res21;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count + 1ULL;
              ite1 = true;
            }
            else
              ite1 = false;
          }
          else
            ite1 = false;
        }
        else
          ite1 = false;
      }
      else
        ite1 = false;
    }
    else if (c240.tag == FStar_Pervasives_Native_None)
      ite1 = true;
    else
      ite1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite1 = false;
  bool ite2;
  if (ite1)
    if (c230.tag == FStar_Pervasives_Native_Some)
    {
      COSE_Format_aux_env29_type_1_ugly c14 = c230.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1)._2;
          size_t res2;
          if (c14.tag == COSE_Format_Inl)
            res2 = COSE_Format_serialize_tstr(c14.case_Inl, out2);
          else if (c14.tag == COSE_Format_Inr)
            res2 = COSE_Format_serialize_int(c14.case_Inr, out2);
          else
            res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count + 1ULL;
              ite2 = true;
            }
            else
              ite2 = false;
          }
          else
            ite2 = false;
        }
        else
          ite2 = false;
      }
      else
        ite2 = false;
    }
    else if (c230.tag == FStar_Pervasives_Native_None)
      ite2 = true;
    else
      ite2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite2 = false;
  bool ite3;
  if (ite2)
    if (c220.tag == FStar_Pervasives_Native_Some)
    {
      Pulse_Lib_Slice_slice__uint8_t c13 = c220.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          size_t res2 = COSE_Format_serialize_bstr(c13, split__uint8_t(out, size1)._2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count + 1ULL;
              ite3 = true;
            }
            else
              ite3 = false;
          }
          else
            ite3 = false;
        }
        else
          ite3 = false;
      }
      else
        ite3 = false;
    }
    else if (c220.tag == FStar_Pervasives_Native_None)
      ite3 = true;
    else
      ite3 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite3 = false;
  bool ite4;
  if (ite3)
    if (c210.tag == COSE_Format_Inl)
    {
      FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option____
      c12 = c210.case_Inl;
      Pulse_Lib_Slice_slice__uint8_t c13 = c12._1;
      FStar_Pervasives_Native_option__size_t_tags c22 = c12._2;
      uint64_t count = pcount;
      bool ite;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3,
                  Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                  len)
              }
            );
        else
          scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res11;
        if (scrut.tag == FStar_Pervasives_Native_None)
          res11 = (size_t)0U;
        else if (scrut.tag == FStar_Pervasives_Native_Some)
          res11 = scrut.v;
        else
          res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          size_t res2 = COSE_Format_serialize_bstr(c13, split__uint8_t(out, size1)._2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                aout_len,
                size0,
                size1)
            )
            {
              psize = size2;
              pcount = count + 1ULL;
              ite = true;
            }
            else
              ite = false;
          }
          else
            ite = false;
        }
        else
          ite = false;
      }
      else
        ite = false;
      if (ite)
        switch (c22)
        {
          case FStar_Pervasives_Native_Some:
            {
              uint64_t count1 = pcount;
              if (count1 < 18446744073709551615ULL)
              {
                size_t size0 = psize;
                Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
                cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
                option__size_t scrut;
                if (len > (size_t)0U)
                  scrut =
                    (
                      (option__size_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = cbor_det_serialize(c3,
                          Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                          len)
                      }
                    );
                else
                  scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
                size_t res12;
                if (scrut.tag == FStar_Pervasives_Native_None)
                  res12 = (size_t)0U;
                else if (scrut.tag == FStar_Pervasives_Native_Some)
                  res12 = scrut.v;
                else
                  res12 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
                if (res12 > (size_t)0U)
                {
                  size_t size1 = size0 + res12;
                  size_t
                  res2 = COSE_Format_serialize_everparsenomatch(split__uint8_t(out, size1)._2);
                  if (res2 > (size_t)0U)
                  {
                    size_t size2 = size1 + res2;
                    Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
                    if
                    (
                      cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                        aout_len,
                        size0,
                        size1)
                    )
                    {
                      psize = size2;
                      pcount = count1 + 1ULL;
                      ite4 = true;
                    }
                    else
                      ite4 = false;
                  }
                  else
                    ite4 = false;
                }
                else
                  ite4 = false;
              }
              else
                ite4 = false;
              break;
            }
          case FStar_Pervasives_Native_None:
            {
              ite4 = true;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
      else
        ite4 = false;
    }
    else if (c210.tag == COSE_Format_Inr)
    {
      FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option_____FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____
      c22 = c210.case_Inr;
      if (c22.tag == COSE_Format_Inl)
      {
        FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_option____
        c12 = c22.case_Inl;
        Pulse_Lib_Slice_slice__uint8_t c13 = c12._1;
        FStar_Pervasives_Native_option__size_t_tags c23 = c12._2;
        uint64_t count = pcount;
        bool ite;
        if (count < 18446744073709551615ULL)
        {
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
          cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
          size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
          option__size_t scrut;
          if (len > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(c3,
                    Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                    len)
                }
              );
          else
            scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
          size_t res11;
          if (scrut.tag == FStar_Pervasives_Native_None)
            res11 = (size_t)0U;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            res11 = scrut.v;
          else
            res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          if (res11 > (size_t)0U)
          {
            size_t size1 = size0 + res11;
            size_t res2 = COSE_Format_serialize_bstr(c13, split__uint8_t(out, size1)._2);
            if (res2 > (size_t)0U)
            {
              size_t size2 = size1 + res2;
              Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
              size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
              if
              (
                cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                  aout_len,
                  size0,
                  size1)
              )
              {
                psize = size2;
                pcount = count + 1ULL;
                ite = true;
              }
              else
                ite = false;
            }
            else
              ite = false;
          }
          else
            ite = false;
        }
        else
          ite = false;
        if (ite)
          switch (c23)
          {
            case FStar_Pervasives_Native_Some:
              {
                uint64_t count1 = pcount;
                if (count1 < 18446744073709551615ULL)
                {
                  size_t size0 = psize;
                  Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
                  cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
                  size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
                  option__size_t scrut;
                  if (len > (size_t)0U)
                    scrut =
                      (
                        (option__size_t){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = cbor_det_serialize(c3,
                            Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                            len)
                        }
                      );
                  else
                    scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
                  size_t res12;
                  if (scrut.tag == FStar_Pervasives_Native_None)
                    res12 = (size_t)0U;
                  else if (scrut.tag == FStar_Pervasives_Native_Some)
                    res12 = scrut.v;
                  else
                    res12 =
                      KRML_EABORT(size_t,
                        "unreachable (pattern matches are exhaustive in F*)");
                  if (res12 > (size_t)0U)
                  {
                    size_t size1 = size0 + res12;
                    size_t
                    res2 = COSE_Format_serialize_everparsenomatch(split__uint8_t(out, size1)._2);
                    if (res2 > (size_t)0U)
                    {
                      size_t size2 = size1 + res2;
                      Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
                      size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
                      if
                      (
                        cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                          aout_len,
                          size0,
                          size1)
                      )
                      {
                        psize = size2;
                        pcount = count1 + 1ULL;
                        ite4 = true;
                      }
                      else
                        ite4 = false;
                    }
                    else
                      ite4 = false;
                  }
                  else
                    ite4 = false;
                }
                else
                  ite4 = false;
                break;
              }
            case FStar_Pervasives_Native_None:
              {
                ite4 = true;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
        else
          ite4 = false;
      }
      else if (c22.tag == COSE_Format_Inr)
      {
        FStar_Pervasives_Native_tuple2__FStar_Pervasives_Native_option_____FStar_Pervasives_Native_option____
        c23 = c22.case_Inr;
        FStar_Pervasives_Native_option__size_t_tags c24 = c23._2;
        bool sw;
        switch (c23._1)
        {
          case FStar_Pervasives_Native_Some:
            {
              uint64_t count = pcount;
              if (count < 18446744073709551615ULL)
              {
                size_t size0 = psize;
                Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
                cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
                option__size_t scrut;
                if (len > (size_t)0U)
                  scrut =
                    (
                      (option__size_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = cbor_det_serialize(c3,
                          Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                          len)
                      }
                    );
                else
                  scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
                size_t res11;
                if (scrut.tag == FStar_Pervasives_Native_None)
                  res11 = (size_t)0U;
                else if (scrut.tag == FStar_Pervasives_Native_Some)
                  res11 = scrut.v;
                else
                  res11 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
                if (res11 > (size_t)0U)
                {
                  size_t size1 = size0 + res11;
                  size_t
                  res2 = COSE_Format_serialize_everparsenomatch(split__uint8_t(out, size1)._2);
                  if (res2 > (size_t)0U)
                  {
                    size_t size2 = size1 + res2;
                    Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
                    if
                    (
                      cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                        aout_len,
                        size0,
                        size1)
                    )
                    {
                      psize = size2;
                      pcount = count + 1ULL;
                      sw = true;
                    }
                    else
                      sw = false;
                  }
                  else
                    sw = false;
                }
                else
                  sw = false;
              }
              else
                sw = false;
              break;
            }
          case FStar_Pervasives_Native_None:
            {
              sw = true;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        if (sw)
          switch (c24)
          {
            case FStar_Pervasives_Native_Some:
              {
                uint64_t count = pcount;
                if (count < 18446744073709551615ULL)
                {
                  size_t size0 = psize;
                  Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
                  cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
                  size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
                  option__size_t scrut;
                  if (len > (size_t)0U)
                    scrut =
                      (
                        (option__size_t){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = cbor_det_serialize(c3,
                            Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                            len)
                        }
                      );
                  else
                    scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
                  size_t res12;
                  if (scrut.tag == FStar_Pervasives_Native_None)
                    res12 = (size_t)0U;
                  else if (scrut.tag == FStar_Pervasives_Native_Some)
                    res12 = scrut.v;
                  else
                    res12 =
                      KRML_EABORT(size_t,
                        "unreachable (pattern matches are exhaustive in F*)");
                  if (res12 > (size_t)0U)
                  {
                    size_t size1 = size0 + res12;
                    size_t
                    res2 = COSE_Format_serialize_everparsenomatch(split__uint8_t(out, size1)._2);
                    if (res2 > (size_t)0U)
                    {
                      size_t size2 = size1 + res2;
                      Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2)._1;
                      size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out012);
                      if
                      (
                        cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out012),
                          aout_len,
                          size0,
                          size1)
                      )
                      {
                        psize = size2;
                        pcount = count + 1ULL;
                        ite4 = true;
                      }
                      else
                        ite4 = false;
                    }
                    else
                      ite4 = false;
                  }
                  else
                    ite4 = false;
                }
                else
                  ite4 = false;
                break;
              }
            case FStar_Pervasives_Native_None:
              {
                ite4 = true;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
        else
          ite4 = false;
      }
      else
        ite4 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
    }
    else
      ite4 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite4 = false;
  bool ite;
  if (ite4)
    if (c2.tag == COSE_Format_Inl)
    {
      Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      c11 = c2.case_Inl;
      Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      buf = c11;
      KRML_HOST_IGNORE(&buf);
      bool pres = true;
      Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      pc = c11;
      bool
      pem =
        len__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(c11)
        == (size_t)0U;
      while (pres && !pem)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          i = pc;
          FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          res =
            op_Array_Access__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(i,
              (size_t)0U);
          pc =
            split__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(i,
              (size_t)1U)._2;
          FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          scrut0 = res;
          COSE_Format_evercddl_label ek = scrut0._1;
          cbor_det_t ev = scrut0._2;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
          size_t size1 = COSE_Format_serialize_evercddl_label(ek, out1);
          if (size1 == (size_t)0U)
            pres = false;
          else
          {
            FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 = split__uint8_t(out1, size1);
            Pulse_Lib_Slice_slice__uint8_t out1_ = scrut0._1;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0._2;
            size_t size2 = COSE_Format_serialize_values(ev, out2);
            if (size2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len = Pulse_Lib_Slice_len__uint8_t(out1_);
              size_t
              len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1_), len);
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut0;
              if (len1 == (size_t)0U)
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut = split__uint8_t(out1_, len1);
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len2),
                        ._2 = rem
                      }
                    }
                  );
              }
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut1;
              if (scrut0.tag == FStar_Pervasives_Native_None)
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                pair = scrut0.v;
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = { ._1 = pair._1, ._2 = pair._2 }
                    }
                  );
              }
              else
                scrut1 =
                  KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                    "unreachable (pattern matches are exhaustive in F*)");
              if (scrut1.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t ck = scrut1.v._1;
                Pulse_Lib_Slice_slice__uint8_t out2_ = split__uint8_t(out2, size2)._1;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(out2_);
                size_t
                len3 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2_),
                    len2);
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut0;
                if (len3 == (size_t)0U)
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut = split__uint8_t(out2_, len3);
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                  size_t len4 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len4),
                          ._2 = rem
                        }
                      }
                    );
                }
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut;
                if (scrut0.tag == FStar_Pervasives_Native_None)
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else if (scrut0.tag == FStar_Pervasives_Native_Some)
                {
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                  pair = scrut0.v;
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = { ._1 = pair._1, ._2 = pair._2 }
                      }
                    );
                }
                else
                  scrut =
                    KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                      "unreachable (pattern matches are exhaustive in F*)");
                if (scrut.tag == FStar_Pervasives_Native_Some)
                  if (COSE_Format_aux_env34_map_constraint_2(cbor_det_mk_map_entry(ck, scrut.v._1)))
                    pres = false;
                  else
                  {
                    size_t size1_ = size0 + size1;
                    size_t size2_ = size1_ + size2;
                    Pulse_Lib_Slice_slice__uint8_t out_ = split__uint8_t(out, size2_)._1;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out_);
                    if
                    (
                      cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out_),
                        aout_len,
                        size0,
                        size1_)
                    )
                    {
                      pem =
                        len__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(pc)
                        == (size_t)0U;
                      psize = size2_;
                      pcount = count_;
                    }
                    else
                      pres = false;
                  }
                else
                {
                  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                    __FILE__,
                    __LINE__,
                    "unreachable (pattern matches are exhaustive in F*)");
                  KRML_HOST_EXIT(255U);
                }
              }
              else
              {
                KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                  __FILE__,
                  __LINE__,
                  "unreachable (pattern matches are exhaustive in F*)");
                KRML_HOST_EXIT(255U);
              }
            }
          }
        }
      }
      ite = pres;
    }
    else if (c2.tag == COSE_Format_Inr)
    {
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      c21 = c2.case_Inr;
      bool pres = true;
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
      pc = c21;
      cbor_det_map_iterator_t pj = c21.cddl_map_iterator_contents;
      bool pres1 = true;
      bool test0 = cbor_det_map_iterator_is_empty(pj);
      bool cond = pres1 && !test0;
      while (cond)
      {
        cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
        if (!!c21.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
          if (!c21.cddl_map_iterator_impl_validate_ex(elt))
            pres1 = !c21.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
        bool test = cbor_det_map_iterator_is_empty(pj);
        cond = pres1 && !test;
      }
      bool pem = pres1;
      while (pres && !pem)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
          i = pc;
          cbor_det_map_iterator_t pj1 = i.cddl_map_iterator_contents;
          cbor_det_map_entry_t hd0 = cbor_det_map_iterator_next(&pj1);
          cbor_det_map_entry_t phd = hd0;
          bool tk0 = i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd0));
          bool tv0 = i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0));
          bool pcont = !tk0 || !tv0 || i.cddl_map_iterator_impl_validate_ex(hd0);
          while (pcont)
          {
            cbor_det_map_entry_t hd = cbor_det_map_iterator_next(&pj1);
            phd = hd;
            bool tk = i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd));
            bool tv = i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd));
            pcont = !tk || !tv || i.cddl_map_iterator_impl_validate_ex(hd);
          }
          cbor_det_map_entry_t hd = phd;
          COSE_Format_evercddl_label
          hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
          cbor_det_t hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
          pc =
            (
              (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t){
                .cddl_map_iterator_contents = pj1,
                .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
                .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
                .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
                .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
                .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
              }
            );
          COSE_Format_evercddl_label ek = hd_key_res;
          cbor_det_t ev = hd_value_res;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0)._2;
          size_t size1 = COSE_Format_serialize_evercddl_label(ek, out1);
          if (size1 == (size_t)0U)
            pres = false;
          else
          {
            FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 = split__uint8_t(out1, size1);
            Pulse_Lib_Slice_slice__uint8_t out1_ = scrut0._1;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0._2;
            size_t size2 = COSE_Format_serialize_values(ev, out2);
            if (size2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len = Pulse_Lib_Slice_len__uint8_t(out1_);
              size_t
              len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1_), len);
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut0;
              if (len1 == (size_t)0U)
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut = split__uint8_t(out1_, len1);
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len2),
                        ._2 = rem
                      }
                    }
                  );
              }
              FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
              scrut1;
              if (scrut0.tag == FStar_Pervasives_Native_None)
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                pair = scrut0.v;
                scrut1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = { ._1 = pair._1, ._2 = pair._2 }
                    }
                  );
              }
              else
                scrut1 =
                  KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                    "unreachable (pattern matches are exhaustive in F*)");
              if (scrut1.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t ck = scrut1.v._1;
                Pulse_Lib_Slice_slice__uint8_t out2_ = split__uint8_t(out2, size2)._1;
                size_t len2 = Pulse_Lib_Slice_len__uint8_t(out2_);
                size_t
                len3 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2_),
                    len2);
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut0;
                if (len3 == (size_t)0U)
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut = split__uint8_t(out2_, len3);
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
                  size_t len4 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len4),
                          ._2 = rem
                        }
                      }
                    );
                }
                FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                scrut;
                if (scrut0.tag == FStar_Pervasives_Native_None)
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else if (scrut0.tag == FStar_Pervasives_Native_Some)
                {
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
                  pair = scrut0.v;
                  scrut =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = { ._1 = pair._1, ._2 = pair._2 }
                      }
                    );
                }
                else
                  scrut =
                    KRML_EABORT(FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t,
                      "unreachable (pattern matches are exhaustive in F*)");
                if (scrut.tag == FStar_Pervasives_Native_Some)
                  if (COSE_Format_aux_env34_map_constraint_2(cbor_det_mk_map_entry(ck, scrut.v._1)))
                    pres = false;
                  else
                  {
                    size_t size1_ = size0 + size1;
                    size_t size2_ = size1_ + size2;
                    Pulse_Lib_Slice_slice__uint8_t out_ = split__uint8_t(out, size2_)._1;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out_);
                    if
                    (
                      cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out_),
                        aout_len,
                        size0,
                        size1_)
                    )
                    {
                      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
                      __anf0 = pc;
                      cbor_det_map_iterator_t pj2 = __anf0.cddl_map_iterator_contents;
                      bool pres2 = true;
                      bool test = cbor_det_map_iterator_is_empty(pj2);
                      bool cond = pres2 && !test;
                      while (cond)
                      {
                        cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj2);
                        if (!!__anf0.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
                          if (!__anf0.cddl_map_iterator_impl_validate_ex(elt))
                            pres2 =
                              !__anf0.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
                        bool test = cbor_det_map_iterator_is_empty(pj2);
                        cond = pres2 && !test;
                      }
                      pem = pres2;
                      psize = size2_;
                      pcount = count_;
                    }
                    else
                      pres = false;
                  }
                else
                {
                  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                    __FILE__,
                    __LINE__,
                    "unreachable (pattern matches are exhaustive in F*)");
                  KRML_HOST_EXIT(255U);
                }
              }
              else
              {
                KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                  __FILE__,
                  __LINE__,
                  "unreachable (pattern matches are exhaustive in F*)");
                KRML_HOST_EXIT(255U);
              }
            }
          }
        }
      }
      ite = pres;
    }
    else
      ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite = false;
  if (ite)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
    return
      cbor_det_serialize_map_to_array(count,
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_header_map_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_header_map(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_header_map_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_header_map(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_header_map_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_header_map(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_header_map_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool
COSE_Format_is_empty_iterate_array_aux_env34_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
  i
)
{
  return cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents);
}

COSE_Format_evercddl_label
COSE_Format_next_iterate_array_aux_env34_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
  *pi
)
{
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label
  i = pi[0U];
  uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
  cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
  KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
  cbor_det_array_iterator_t ji = pj;
  uint64_t len1 = cbor_det_array_iterator_length(ji);
  pi[0U] =
    (
      (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label){
        .cddl_array_iterator_contents = ji,
        .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
        .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
      }
    );
  return
    i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
        len0 - len1));
}

bool COSE_Format_validate_empty_or_serialized_map(cbor_det_t c)
{
  bool ite;
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_BYTE_STRING)
  {
    uint64_t len = cbor_det_get_string_length(c);
    Pulse_Lib_Slice_slice__uint8_t
    pl = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len);
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(pl);
    size_t len2 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(pl), len1);
    FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0;
    if (len2 == (size_t)0U)
      scrut0 =
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut = split__uint8_t(pl, len2);
      Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
      Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
      size_t len3 = Pulse_Lib_Slice_len__uint8_t(input2);
      scrut0 =
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = {
              ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len3),
              ._2 = rem
            }
          }
        );
    }
    if (scrut0.tag == FStar_Pervasives_Native_None)
      ite = false;
    else if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
      r = scrut0.v;
      cbor_det_t res = r._1;
      if (Pulse_Lib_Slice_len__uint8_t(r._2) == (size_t)0U)
        ite = COSE_Format_validate_header_map(res);
      else
        ite = false;
    }
    else
      ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  }
  else
    ite = false;
  if (ite)
    return true;
  else if (cbor_det_major_type(c) == 2U)
  {
    uint64_t len = cbor_det_get_string_length(c);
    size_t
    len1 =
      Pulse_Lib_Slice_len__uint8_t(arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c),
          (size_t)len));
    bool lo_ok = u64_lte_sizet(0ULL, len1);
    return lo_ok && sizet_lte_u64(len1, 0ULL);
  }
  else
    return false;
}

COSE_Format_empty_or_serialized_map
COSE_Format_empty_or_serialized_map_right(COSE_Format_empty_or_serialized_map_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return
      (
        (COSE_Format_empty_or_serialized_map){
          .tag = COSE_Format_Mkempty_or_serialized_map0,
          { .case_Mkempty_or_serialized_map0 = x2.case_Inl }
        }
      );
  else if (x2.tag == COSE_Format_Inr)
    return
      (
        (COSE_Format_empty_or_serialized_map){
          .tag = COSE_Format_Mkempty_or_serialized_map1,
          { .case_Mkempty_or_serialized_map1 = x2.case_Inr }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

COSE_Format_empty_or_serialized_map_ugly
COSE_Format_empty_or_serialized_map_left(COSE_Format_empty_or_serialized_map x8)
{
  if (x8.tag == COSE_Format_Mkempty_or_serialized_map0)
    return
      (
        (COSE_Format_empty_or_serialized_map_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = x8.case_Mkempty_or_serialized_map0 }
        }
      );
  else if (x8.tag == COSE_Format_Mkempty_or_serialized_map1)
    return
      (
        (COSE_Format_empty_or_serialized_map_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = x8.case_Mkempty_or_serialized_map1 }
        }
      );
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_det_t
fst__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t(
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  x
)
{
  return x._1;
}

/**
Parser for empty_or_serialized_map
*/
COSE_Format_empty_or_serialized_map COSE_Format_parse_empty_or_serialized_map(cbor_det_t c)
{
  bool ite0;
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_BYTE_STRING)
  {
    uint64_t len = cbor_det_get_string_length(c);
    Pulse_Lib_Slice_slice__uint8_t
    pl = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len);
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(pl);
    size_t len2 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(pl), len1);
    FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0;
    if (len2 == (size_t)0U)
      scrut0 =
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut = split__uint8_t(pl, len2);
      Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
      Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
      size_t len3 = Pulse_Lib_Slice_len__uint8_t(input2);
      scrut0 =
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = {
              ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len3),
              ._2 = rem
            }
          }
        );
    }
    if (scrut0.tag == FStar_Pervasives_Native_None)
      ite0 = false;
    else if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
      r = scrut0.v;
      cbor_det_t res = r._1;
      if (Pulse_Lib_Slice_len__uint8_t(r._2) == (size_t)0U)
        ite0 = COSE_Format_validate_header_map(res);
      else
        ite0 = false;
    }
    else
      ite0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  }
  else
    ite0 = false;
  COSE_Format_empty_or_serialized_map_ugly ite1;
  if (ite0)
  {
    uint64_t len = cbor_det_get_string_length(c);
    Pulse_Lib_Slice_slice__uint8_t
    cs = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len);
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(cs);
    size_t len2 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(cs), len1);
    FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0;
    if (len2 == (size_t)0U)
      scrut0 =
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut = split__uint8_t(cs, len2);
      Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
      Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
      size_t len3 = Pulse_Lib_Slice_len__uint8_t(input2);
      scrut0 =
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = {
              ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len3),
              ._2 = rem
            }
          }
        );
    }
    COSE_Format_header_map ite;
    if (scrut0.tag == FStar_Pervasives_Native_Some)
      ite =
        COSE_Format_parse_header_map(fst__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t(scrut0.v));
    else
      ite =
        KRML_EABORT(COSE_Format_header_map,
          "unreachable (pattern matches are exhaustive in F*)");
    ite1 =
      ((COSE_Format_empty_or_serialized_map_ugly){ .tag = COSE_Format_Inl, { .case_Inl = ite } });
  }
  else
  {
    uint64_t len = cbor_det_get_string_length(c);
    ite1 =
      (
        (COSE_Format_empty_or_serialized_map_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len) }
        }
      );
  }
  return COSE_Format_empty_or_serialized_map_right(ite1);
}

/**
Serializer for empty_or_serialized_map
*/
size_t
COSE_Format_serialize_empty_or_serialized_map(
  COSE_Format_empty_or_serialized_map c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_empty_or_serialized_map_ugly scrut0 = COSE_Format_empty_or_serialized_map_left(c);
  if (scrut0.tag == COSE_Format_Inl)
  {
    size_t sz = COSE_Format_serialize_header_map(scrut0.case_Inl, out);
    if (sz == (size_t)0U || !sizet_fits_u64(sz))
      return (size_t)0U;
    else
    {
      size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
      return
        cbor_det_serialize_string_to_array(CBOR_MAJOR_TYPE_BYTE_STRING,
          (uint64_t)sz,
          Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
          aout_len);
    }
  }
  else if (scrut0.tag == COSE_Format_Inr)
  {
    Pulse_Lib_Slice_slice__uint8_t c2 = scrut0.case_Inr;
    size_t len = Pulse_Lib_Slice_len__uint8_t(c2);
    bool lo_ok = u64_lte_sizet(0ULL, len);
    if (lo_ok && sizet_lte_u64(len, 0ULL))
      if (2U == CBOR_MAJOR_TYPE_BYTE_STRING)
        if (sizet_lte_u64(Pulse_Lib_Slice_len__uint8_t(c2), 18446744073709551615ULL))
        {
          uint8_t *a = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c2);
          cbor_det_t pres = dummy_cbor_det_t();
          cbor_det_mk_byte_string_from_arrayptr(a,
            (uint64_t)Pulse_Lib_Slice_len__uint8_t(c2),
            &pres);
          cbor_det_t x = pres;
          size_t len2 = cbor_det_size(x, Pulse_Lib_Slice_len__uint8_t(out));
          option__size_t scrut;
          if (len2 > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(x,
                    Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
                    len2)
                }
              );
          else
            scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
          if (scrut.tag == FStar_Pervasives_Native_None)
            return (size_t)0U;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            return scrut.v;
          else
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        else
          return (size_t)0U;
      else if (sizet_lte_u64(Pulse_Lib_Slice_len__uint8_t(c2), 18446744073709551615ULL))
      {
        size_t alen = Pulse_Lib_Slice_len__uint8_t(c2);
        if
        (
          cbor_det_impl_utf8_correct_from_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c2),
            alen)
        )
        {
          uint8_t *a1 = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c2);
          cbor_det_t pres = dummy_cbor_det_t();
          bool ite;
          if (CBOR_MAJOR_TYPE_TEXT_STRING == CBOR_MAJOR_TYPE_BYTE_STRING)
            ite =
              cbor_det_mk_byte_string_from_arrayptr(a1,
                (uint64_t)Pulse_Lib_Slice_len__uint8_t(c2),
                &pres);
          else
            ite =
              cbor_det_mk_text_string_from_arrayptr(a1,
                (uint64_t)Pulse_Lib_Slice_len__uint8_t(c2),
                &pres);
          KRML_MAYBE_UNUSED_VAR(ite);
          cbor_det_t x = pres;
          size_t len2 = cbor_det_size(x, Pulse_Lib_Slice_len__uint8_t(out));
          option__size_t scrut;
          if (len2 > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(x,
                    Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
                    len2)
                }
              );
          else
            scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
          if (scrut.tag == FStar_Pervasives_Native_None)
            return (size_t)0U;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            return scrut.v;
          else
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        else
          return (size_t)0U;
      }
      else
        return (size_t)0U;
    else
      return (size_t)0U;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_empty_or_serialized_map(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_empty_or_serialized_map(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_empty_or_serialized_map(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static uint8_t op_Array_Access__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i)
{
  return a.elt[i];
}

bool COSE_Format_validate_sig_structure(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(c);
    bool ite0;
    if (cbor_det_array_iterator_is_empty(pi))
      ite0 = false;
    else
    {
      cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
      bool ite;
      if (cbor_det_major_type(c1) == CBOR_MAJOR_TYPE_TEXT_STRING)
      {
        uint64_t len = cbor_det_get_string_length(c1);
        Pulse_Lib_Slice_slice__uint8_t
        s = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c1), (size_t)len);
        if (!sizet_eq_u64(Pulse_Lib_Slice_len__uint8_t(s), 9ULL))
          ite = false;
        else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
          if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
            if (op_Array_Access__uint8_t(s, (size_t)2U) == 103U)
              if (op_Array_Access__uint8_t(s, (size_t)3U) == 110U)
              {
                size_t i_4 = (size_t)5U;
                if (op_Array_Access__uint8_t(s, (size_t)4U) == 97U)
                {
                  size_t i_5 = i_4 + (size_t)1U;
                  if (op_Array_Access__uint8_t(s, i_4) == 116U)
                  {
                    size_t i_6 = i_5 + (size_t)1U;
                    if (op_Array_Access__uint8_t(s, i_5) == 117U)
                    {
                      size_t i_7 = i_6 + (size_t)1U;
                      if (op_Array_Access__uint8_t(s, i_6) == 114U)
                        if (op_Array_Access__uint8_t(s, i_7) == 101U)
                          ite = true;
                        else
                          ite = false;
                      else
                        ite = false;
                    }
                    else
                      ite = false;
                  }
                  else
                    ite = false;
                }
                else
                  ite = false;
              }
              else
                ite = false;
            else
              ite = false;
          else
            ite = false;
        else
          ite = false;
      }
      else
        ite = false;
      if (ite)
        ite0 = true;
      else if (cbor_det_major_type(c1) == CBOR_MAJOR_TYPE_TEXT_STRING)
      {
        uint64_t len = cbor_det_get_string_length(c1);
        Pulse_Lib_Slice_slice__uint8_t
        s = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c1), (size_t)len);
        if (!sizet_eq_u64(Pulse_Lib_Slice_len__uint8_t(s), 10ULL))
          ite0 = false;
        else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
          if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
            if (op_Array_Access__uint8_t(s, (size_t)2U) == 103U)
              if (op_Array_Access__uint8_t(s, (size_t)3U) == 110U)
              {
                size_t i_4 = (size_t)5U;
                if (op_Array_Access__uint8_t(s, (size_t)4U) == 97U)
                {
                  size_t i_5 = i_4 + (size_t)1U;
                  if (op_Array_Access__uint8_t(s, i_4) == 116U)
                  {
                    size_t i_6 = i_5 + (size_t)1U;
                    if (op_Array_Access__uint8_t(s, i_5) == 117U)
                    {
                      size_t i_7 = i_6 + (size_t)1U;
                      if (op_Array_Access__uint8_t(s, i_6) == 114U)
                      {
                        size_t i_8 = i_7 + (size_t)1U;
                        if (op_Array_Access__uint8_t(s, i_7) == 101U)
                          if (op_Array_Access__uint8_t(s, i_8) == 49U)
                            ite0 = true;
                          else
                            ite0 = false;
                        else
                          ite0 = false;
                      }
                      else
                        ite0 = false;
                    }
                    else
                      ite0 = false;
                  }
                  else
                    ite0 = false;
                }
                else
                  ite0 = false;
              }
              else
                ite0 = false;
            else
              ite0 = false;
          else
            ite0 = false;
        else
          ite0 = false;
      }
      else
        ite0 = false;
    }
    bool ite1;
    if (ite0)
    {
      bool ite0;
      if (cbor_det_array_iterator_is_empty(pi))
        ite0 = false;
      else
        ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pi));
      if (ite0)
      {
        cbor_det_array_iterator_t i3 = pi;
        bool ite0;
        if (cbor_det_array_iterator_is_empty(pi))
          ite0 = false;
        else
          ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pi));
        bool ite2;
        if (ite0)
        {
          bool ite;
          if (cbor_det_array_iterator_is_empty(pi))
            ite = false;
          else
            ite = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pi));
          if (ite)
            if (cbor_det_array_iterator_is_empty(pi))
              ite2 = false;
            else
              ite2 = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pi));
          else
            ite2 = false;
        }
        else
          ite2 = false;
        if (ite2)
          ite1 = true;
        else
        {
          pi = i3;
          bool ite;
          if (cbor_det_array_iterator_is_empty(pi))
            ite = false;
          else
            ite = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pi));
          if (ite)
            if (cbor_det_array_iterator_is_empty(pi))
              ite1 = false;
            else
              ite1 = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pi));
          else
            ite1 = false;
        }
      }
      else
        ite1 = false;
    }
    else
      ite1 = false;
    if (ite1)
      return cbor_det_array_iterator_is_empty(pi);
    else
      return false;
  }
  else
    return false;
}

COSE_Format_sig_structure COSE_Format_sig_structure_right(COSE_Format_sig_structure_ugly x3)
{
  return
    ((COSE_Format_sig_structure){ .context = x3._1, .body_protected = x3._2._1, ._x0 = x3._2._2 });
}

COSE_Format_sig_structure_ugly COSE_Format_sig_structure_left(COSE_Format_sig_structure x8)
{
  return
    (
      (COSE_Format_sig_structure_ugly){
        ._1 = x8.context,
        ._2 = { ._1 = x8.body_protected, ._2 = x8._x0 }
      }
    );
}

/**
Parser for sig_structure
*/
COSE_Format_sig_structure COSE_Format_parse_sig_structure(cbor_det_t c)
{
  cbor_det_array_iterator_t ar = cbor_det_array_iterator_start(c);
  uint64_t rlen0 = cbor_det_array_iterator_length(ar);
  cbor_det_array_iterator_t pc = ar;
  bool ite0;
  if (cbor_det_array_iterator_is_empty(pc))
    ite0 = false;
  else
  {
    cbor_det_t c1 = cbor_det_array_iterator_next(&pc);
    bool ite;
    if (cbor_det_major_type(c1) == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      uint64_t len = cbor_det_get_string_length(c1);
      Pulse_Lib_Slice_slice__uint8_t
      s = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c1), (size_t)len);
      if (!sizet_eq_u64(Pulse_Lib_Slice_len__uint8_t(s), 9ULL))
        ite = false;
      else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
        if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
          if (op_Array_Access__uint8_t(s, (size_t)2U) == 103U)
            if (op_Array_Access__uint8_t(s, (size_t)3U) == 110U)
            {
              size_t i_4 = (size_t)5U;
              if (op_Array_Access__uint8_t(s, (size_t)4U) == 97U)
              {
                size_t i_5 = i_4 + (size_t)1U;
                if (op_Array_Access__uint8_t(s, i_4) == 116U)
                {
                  size_t i_6 = i_5 + (size_t)1U;
                  if (op_Array_Access__uint8_t(s, i_5) == 117U)
                  {
                    size_t i_7 = i_6 + (size_t)1U;
                    if (op_Array_Access__uint8_t(s, i_6) == 114U)
                      if (op_Array_Access__uint8_t(s, i_7) == 101U)
                        ite = true;
                      else
                        ite = false;
                    else
                      ite = false;
                  }
                  else
                    ite = false;
                }
                else
                  ite = false;
              }
              else
                ite = false;
            }
            else
              ite = false;
          else
            ite = false;
        else
          ite = false;
      else
        ite = false;
    }
    else
      ite = false;
    if (ite)
      ite0 = true;
    else if (cbor_det_major_type(c1) == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      uint64_t len = cbor_det_get_string_length(c1);
      Pulse_Lib_Slice_slice__uint8_t
      s = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c1), (size_t)len);
      if (!sizet_eq_u64(Pulse_Lib_Slice_len__uint8_t(s), 10ULL))
        ite0 = false;
      else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
        if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
          if (op_Array_Access__uint8_t(s, (size_t)2U) == 103U)
            if (op_Array_Access__uint8_t(s, (size_t)3U) == 110U)
            {
              size_t i_4 = (size_t)5U;
              if (op_Array_Access__uint8_t(s, (size_t)4U) == 97U)
              {
                size_t i_5 = i_4 + (size_t)1U;
                if (op_Array_Access__uint8_t(s, i_4) == 116U)
                {
                  size_t i_6 = i_5 + (size_t)1U;
                  if (op_Array_Access__uint8_t(s, i_5) == 117U)
                  {
                    size_t i_7 = i_6 + (size_t)1U;
                    if (op_Array_Access__uint8_t(s, i_6) == 114U)
                    {
                      size_t i_8 = i_7 + (size_t)1U;
                      if (op_Array_Access__uint8_t(s, i_7) == 101U)
                        if (op_Array_Access__uint8_t(s, i_8) == 49U)
                          ite0 = true;
                        else
                          ite0 = false;
                      else
                        ite0 = false;
                    }
                    else
                      ite0 = false;
                  }
                  else
                    ite0 = false;
                }
                else
                  ite0 = false;
              }
              else
                ite0 = false;
            }
            else
              ite0 = false;
          else
            ite0 = false;
        else
          ite0 = false;
      else
        ite0 = false;
    }
    else
      ite0 = false;
  }
  KRML_MAYBE_UNUSED_VAR(ite0);
  cbor_det_array_iterator_t c1 = pc;
  cbor_det_array_iterator_t
  buf0 = cbor_det_array_iterator_truncate(ar, rlen0 - cbor_det_array_iterator_length(c1));
  cbor_det_t x = cbor_det_array_iterator_next(&buf0);
  bool ite1;
  if (cbor_det_major_type(x) == CBOR_MAJOR_TYPE_TEXT_STRING)
  {
    uint64_t len = cbor_det_get_string_length(x);
    Pulse_Lib_Slice_slice__uint8_t
    s = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(x), (size_t)len);
    if (!sizet_eq_u64(Pulse_Lib_Slice_len__uint8_t(s), 9ULL))
      ite1 = false;
    else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
      if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
        if (op_Array_Access__uint8_t(s, (size_t)2U) == 103U)
          if (op_Array_Access__uint8_t(s, (size_t)3U) == 110U)
          {
            size_t i_4 = (size_t)5U;
            if (op_Array_Access__uint8_t(s, (size_t)4U) == 97U)
            {
              size_t i_5 = i_4 + (size_t)1U;
              if (op_Array_Access__uint8_t(s, i_4) == 116U)
              {
                size_t i_6 = i_5 + (size_t)1U;
                if (op_Array_Access__uint8_t(s, i_5) == 117U)
                {
                  size_t i_7 = i_6 + (size_t)1U;
                  if (op_Array_Access__uint8_t(s, i_6) == 114U)
                    if (op_Array_Access__uint8_t(s, i_7) == 101U)
                      ite1 = true;
                    else
                      ite1 = false;
                  else
                    ite1 = false;
                }
                else
                  ite1 = false;
              }
              else
                ite1 = false;
            }
            else
              ite1 = false;
          }
          else
            ite1 = false;
        else
          ite1 = false;
      else
        ite1 = false;
    else
      ite1 = false;
  }
  else
    ite1 = false;
  COSE_Format_evercddl_int_ugly_tags w1;
  if (ite1)
    w1 = COSE_Format_Inl;
  else
    w1 = COSE_Format_Inr;
  uint64_t rlen01 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t pc2 = c1;
  bool ite2;
  if (cbor_det_array_iterator_is_empty(pc2))
    ite2 = false;
  else
    ite2 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc2));
  KRML_MAYBE_UNUSED_VAR(ite2);
  cbor_det_array_iterator_t c11 = pc2;
  cbor_det_array_iterator_t
  buf1 = cbor_det_array_iterator_truncate(c1, rlen01 - cbor_det_array_iterator_length(c11));
  COSE_Format_empty_or_serialized_map
  w11 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf1));
  cbor_det_array_iterator_t pc4 = c11;
  bool ite3;
  if (cbor_det_array_iterator_is_empty(pc4))
    ite3 = false;
  else
    ite3 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc4));
  bool ite4;
  if (ite3)
  {
    bool ite;
    if (cbor_det_array_iterator_is_empty(pc4))
      ite = false;
    else
      ite = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pc4));
    if (ite)
      if (cbor_det_array_iterator_is_empty(pc4))
        ite4 = false;
      else
        ite4 = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pc4));
    else
      ite4 = false;
  }
  else
    ite4 = false;
  FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  ite5;
  if (ite4)
  {
    uint64_t rlen02 = cbor_det_array_iterator_length(c11);
    cbor_det_array_iterator_t pc5 = c11;
    bool ite0;
    if (cbor_det_array_iterator_is_empty(pc5))
      ite0 = false;
    else
      ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc5));
    KRML_MAYBE_UNUSED_VAR(ite0);
    cbor_det_array_iterator_t c12 = pc5;
    cbor_det_array_iterator_t
    buf0 = cbor_det_array_iterator_truncate(c11, rlen02 - cbor_det_array_iterator_length(c12));
    COSE_Format_empty_or_serialized_map
    w12 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
    uint64_t rlen03 = cbor_det_array_iterator_length(c12);
    cbor_det_array_iterator_t pc7 = c12;
    bool ite;
    if (cbor_det_array_iterator_is_empty(pc7))
      ite = false;
    else
      ite = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pc7));
    KRML_MAYBE_UNUSED_VAR(ite);
    cbor_det_array_iterator_t c13 = pc7;
    cbor_det_array_iterator_t
    buf1 = cbor_det_array_iterator_truncate(c12, rlen03 - cbor_det_array_iterator_length(c13));
    Pulse_Lib_Slice_slice__uint8_t
    w13 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf1));
    cbor_det_array_iterator_t buf = c13;
    ite5 =
      (
        (FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = COSE_Format_Inl,
          {
            .case_Inl = {
              ._1 = w12,
              ._2 = { ._1 = w13, ._2 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf)) }
            }
          }
        }
      );
  }
  else
  {
    uint64_t rlen02 = cbor_det_array_iterator_length(c11);
    cbor_det_array_iterator_t pc5 = c11;
    bool ite;
    if (cbor_det_array_iterator_is_empty(pc5))
      ite = false;
    else
      ite = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pc5));
    KRML_MAYBE_UNUSED_VAR(ite);
    cbor_det_array_iterator_t c12 = pc5;
    cbor_det_array_iterator_t
    buf0 = cbor_det_array_iterator_truncate(c11, rlen02 - cbor_det_array_iterator_length(c12));
    Pulse_Lib_Slice_slice__uint8_t
    w12 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf0));
    cbor_det_array_iterator_t buf = c12;
    ite5 =
      (
        (FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = COSE_Format_Inr,
          {
            .case_Inr = {
              ._1 = w12,
              ._2 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf))
            }
          }
        }
      );
  }
  return
    COSE_Format_sig_structure_right((
        (COSE_Format_sig_structure_ugly){ ._1 = w1, ._2 = { ._1 = w11, ._2 = ite5 } }
      ));
}

Pulse_Lib_Slice_slice__uint8_t Pulse_Lib_Slice_from_array__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

static void op_Array_Assignment__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i, uint8_t v)
{
  a.elt[i] = v;
}

/**
Serializer for sig_structure
*/
size_t
COSE_Format_serialize_sig_structure(
  COSE_Format_sig_structure c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_sig_structure_ugly scrut0 = COSE_Format_sig_structure_left(c);
  COSE_Format_evercddl_int_ugly_tags c1 = scrut0._1;
  FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  c2 = scrut0._2;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size)._2;
    size_t size1;
    switch (c1)
    {
      case COSE_Format_Inl:
        {
          uint8_t buf[(size_t)9ULL];
          memset(buf, 0U, (size_t)9ULL * sizeof (uint8_t));
          Pulse_Lib_Slice_slice__uint8_t s = Pulse_Lib_Slice_from_array__uint8_t(buf, (size_t)9ULL);
          op_Array_Assignment__uint8_t(s, (size_t)0U, 83U);
          op_Array_Assignment__uint8_t(s, (size_t)1U, 105U);
          op_Array_Assignment__uint8_t(s, (size_t)2U, 103U);
          op_Array_Assignment__uint8_t(s, (size_t)3U, 110U);
          op_Array_Assignment__uint8_t(s, (size_t)4U, 97U);
          size_t i_4 = (size_t)5U;
          op_Array_Assignment__uint8_t(s, i_4, 116U);
          size_t i_5 = i_4 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_5, 117U);
          size_t i_6 = i_5 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_6, 114U);
          op_Array_Assignment__uint8_t(s, i_6 + (size_t)1U, 101U);
          uint8_t *a1 = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s);
          cbor_det_t pres = dummy_cbor_det_t();
          bool ite;
          if (CBOR_MAJOR_TYPE_TEXT_STRING == CBOR_MAJOR_TYPE_BYTE_STRING)
            ite =
              cbor_det_mk_byte_string_from_arrayptr(a1,
                (uint64_t)Pulse_Lib_Slice_len__uint8_t(s),
                &pres);
          else
            ite =
              cbor_det_mk_text_string_from_arrayptr(a1,
                (uint64_t)Pulse_Lib_Slice_len__uint8_t(s),
                &pres);
          KRML_MAYBE_UNUSED_VAR(ite);
          cbor_det_t c3 = pres;
          size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
          option__size_t scrut;
          if (len > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(c3,
                    Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                    len)
                }
              );
          else
            scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
          if (scrut.tag == FStar_Pervasives_Native_None)
            size1 = (size_t)0U;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            size1 = scrut.v;
          else
            size1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          break;
        }
      case COSE_Format_Inr:
        {
          uint8_t buf[(size_t)10ULL];
          memset(buf, 0U, (size_t)10ULL * sizeof (uint8_t));
          Pulse_Lib_Slice_slice__uint8_t
          s = Pulse_Lib_Slice_from_array__uint8_t(buf, (size_t)10ULL);
          op_Array_Assignment__uint8_t(s, (size_t)0U, 83U);
          op_Array_Assignment__uint8_t(s, (size_t)1U, 105U);
          op_Array_Assignment__uint8_t(s, (size_t)2U, 103U);
          op_Array_Assignment__uint8_t(s, (size_t)3U, 110U);
          op_Array_Assignment__uint8_t(s, (size_t)4U, 97U);
          size_t i_4 = (size_t)5U;
          op_Array_Assignment__uint8_t(s, i_4, 116U);
          size_t i_5 = i_4 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_5, 117U);
          size_t i_6 = i_5 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_6, 114U);
          size_t i_7 = i_6 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_7, 101U);
          op_Array_Assignment__uint8_t(s, i_7 + (size_t)1U, 49U);
          uint8_t *a1 = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s);
          cbor_det_t pres = dummy_cbor_det_t();
          bool ite;
          if (CBOR_MAJOR_TYPE_TEXT_STRING == CBOR_MAJOR_TYPE_BYTE_STRING)
            ite =
              cbor_det_mk_byte_string_from_arrayptr(a1,
                (uint64_t)Pulse_Lib_Slice_len__uint8_t(s),
                &pres);
          else
            ite =
              cbor_det_mk_text_string_from_arrayptr(a1,
                (uint64_t)Pulse_Lib_Slice_len__uint8_t(s),
                &pres);
          KRML_MAYBE_UNUSED_VAR(ite);
          cbor_det_t c3 = pres;
          size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out1));
          option__size_t scrut;
          if (len > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(c3,
                    Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
                    len)
                }
              );
          else
            scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
          if (scrut.tag == FStar_Pervasives_Native_None)
            size1 = (size_t)0U;
          else if (scrut.tag == FStar_Pervasives_Native_Some)
            size1 = scrut.v;
          else
            size1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    if (size1 == (size_t)0U)
      ite0 = false;
    else
    {
      pcount = count0 + 1ULL;
      psize = size + size1;
      ite0 = true;
    }
  }
  else
    ite0 = false;
  bool ite1;
  if (ite0)
  {
    COSE_Format_empty_or_serialized_map c11 = c2._1;
    FStar_Pervasives_either__FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    c21 = c2._2;
    uint64_t count1 = pcount;
    bool ite0;
    if (count1 < 18446744073709551615ULL)
    {
      size_t size = psize;
      size_t
      size1 = COSE_Format_serialize_empty_or_serialized_map(c11, split__uint8_t(out, size)._2);
      if (size1 == (size_t)0U)
        ite0 = false;
      else
      {
        pcount = count1 + 1ULL;
        psize = size + size1;
        ite0 = true;
      }
    }
    else
      ite0 = false;
    if (ite0)
      if (c21.tag == COSE_Format_Inl)
      {
        FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        c12 = c21.case_Inl;
        COSE_Format_empty_or_serialized_map c13 = c12._1;
        FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        c22 = c12._2;
        uint64_t count2 = pcount;
        bool ite0;
        if (count2 < 18446744073709551615ULL)
        {
          size_t size = psize;
          size_t
          size1 = COSE_Format_serialize_empty_or_serialized_map(c13, split__uint8_t(out, size)._2);
          if (size1 == (size_t)0U)
            ite0 = false;
          else
          {
            pcount = count2 + 1ULL;
            psize = size + size1;
            ite0 = true;
          }
        }
        else
          ite0 = false;
        if (ite0)
        {
          Pulse_Lib_Slice_slice__uint8_t c14 = c22._1;
          Pulse_Lib_Slice_slice__uint8_t c23 = c22._2;
          uint64_t count3 = pcount;
          bool ite;
          if (count3 < 18446744073709551615ULL)
          {
            size_t size = psize;
            size_t size1 = COSE_Format_serialize_bstr(c14, split__uint8_t(out, size)._2);
            if (size1 == (size_t)0U)
              ite = false;
            else
            {
              pcount = count3 + 1ULL;
              psize = size + size1;
              ite = true;
            }
          }
          else
            ite = false;
          if (ite)
          {
            uint64_t count4 = pcount;
            if (count4 < 18446744073709551615ULL)
            {
              size_t size = psize;
              size_t size1 = COSE_Format_serialize_bstr(c23, split__uint8_t(out, size)._2);
              if (size1 == (size_t)0U)
                ite1 = false;
              else
              {
                pcount = count4 + 1ULL;
                psize = size + size1;
                ite1 = true;
              }
            }
            else
              ite1 = false;
          }
          else
            ite1 = false;
        }
        else
          ite1 = false;
      }
      else if (c21.tag == COSE_Format_Inr)
      {
        FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        c22 = c21.case_Inr;
        Pulse_Lib_Slice_slice__uint8_t c12 = c22._1;
        Pulse_Lib_Slice_slice__uint8_t c23 = c22._2;
        uint64_t count2 = pcount;
        bool ite;
        if (count2 < 18446744073709551615ULL)
        {
          size_t size = psize;
          size_t size1 = COSE_Format_serialize_bstr(c12, split__uint8_t(out, size)._2);
          if (size1 == (size_t)0U)
            ite = false;
          else
          {
            pcount = count2 + 1ULL;
            psize = size + size1;
            ite = true;
          }
        }
        else
          ite = false;
        if (ite)
        {
          uint64_t count3 = pcount;
          if (count3 < 18446744073709551615ULL)
          {
            size_t size = psize;
            size_t size1 = COSE_Format_serialize_bstr(c23, split__uint8_t(out, size)._2);
            if (size1 == (size_t)0U)
              ite1 = false;
            else
            {
              pcount = count3 + 1ULL;
              psize = size + size1;
              ite1 = true;
            }
          }
          else
            ite1 = false;
        }
        else
          ite1 = false;
      }
      else
        ite1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
    else
      ite1 = false;
  }
  else
    ite1 = false;
  if (ite1)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
    return
      cbor_det_serialize_array_to_array(count,
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_sig_structure_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_sig_structure(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_sig_structure_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_sig_structure(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_sig_structure_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_sig_structure(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_sig_structure_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_cose_sign1(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(c);
    bool ite0;
    if (cbor_det_array_iterator_is_empty(pi))
      ite0 = false;
    else
      ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pi));
    bool ite1;
    if (ite0)
      if (cbor_det_array_iterator_is_empty(pi))
        ite1 = false;
      else
        ite1 = COSE_Format_validate_header_map(cbor_det_array_iterator_next(&pi));
    else
      ite1 = false;
    bool ite2;
    if (ite1)
    {
      bool ite;
      if (cbor_det_array_iterator_is_empty(pi))
        ite = false;
      else
      {
        cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
        if (COSE_Format_validate_bstr(c1))
          ite = true;
        else
          ite = COSE_Format_validate_nil(c1);
      }
      if (ite)
        if (cbor_det_array_iterator_is_empty(pi))
          ite2 = false;
        else
          ite2 = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pi));
      else
        ite2 = false;
    }
    else
      ite2 = false;
    if (ite2)
      return cbor_det_array_iterator_is_empty(pi);
    else
      return false;
  }
  else
    return false;
}

COSE_Format_cose_sign1 COSE_Format_cose_sign1_right(COSE_Format_cose_sign1_ugly x4)
{
  return
    (
      (COSE_Format_cose_sign1){
        .protected0 = x4._1._1,
        .unprotected = x4._1._2,
        .payload = x4._2._1,
        .signature = x4._2._2
      }
    );
}

COSE_Format_cose_sign1_ugly COSE_Format_cose_sign1_left(COSE_Format_cose_sign1 x10)
{
  return
    (
      (COSE_Format_cose_sign1_ugly){
        ._1 = { ._1 = x10.protected0, ._2 = x10.unprotected },
        ._2 = { ._1 = x10.payload, ._2 = x10.signature }
      }
    );
}

/**
Parser for cose_sign1
*/
COSE_Format_cose_sign1 COSE_Format_parse_cose_sign1(cbor_det_t c)
{
  cbor_det_array_iterator_t ar = cbor_det_array_iterator_start(c);
  uint64_t rlen0 = cbor_det_array_iterator_length(ar);
  cbor_det_array_iterator_t pc = ar;
  bool ite0;
  if (cbor_det_array_iterator_is_empty(pc))
    ite0 = false;
  else
    ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc));
  bool ite1;
  if (ite0)
    if (cbor_det_array_iterator_is_empty(pc))
      ite1 = false;
    else
      ite1 = COSE_Format_validate_header_map(cbor_det_array_iterator_next(&pc));
  else
    ite1 = false;
  KRML_MAYBE_UNUSED_VAR(ite1);
  cbor_det_array_iterator_t c1 = pc;
  cbor_det_array_iterator_t
  c0_ = cbor_det_array_iterator_truncate(ar, rlen0 - cbor_det_array_iterator_length(c1));
  uint64_t rlen01 = cbor_det_array_iterator_length(c0_);
  cbor_det_array_iterator_t pc1 = c0_;
  bool ite2;
  if (cbor_det_array_iterator_is_empty(pc1))
    ite2 = false;
  else
    ite2 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc1));
  KRML_MAYBE_UNUSED_VAR(ite2);
  cbor_det_array_iterator_t c11 = pc1;
  cbor_det_array_iterator_t
  buf0 = cbor_det_array_iterator_truncate(c0_, rlen01 - cbor_det_array_iterator_length(c11));
  COSE_Format_empty_or_serialized_map
  w1 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
  cbor_det_array_iterator_t buf1 = c11;
  FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_COSE_Format_header_map
  w11 = { ._1 = w1, ._2 = COSE_Format_parse_header_map(cbor_det_array_iterator_next(&buf1)) };
  uint64_t rlen02 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t pc4 = c1;
  bool ite;
  if (cbor_det_array_iterator_is_empty(pc4))
    ite = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc4);
    if (COSE_Format_validate_bstr(c2))
      ite = true;
    else
      ite = COSE_Format_validate_nil(c2);
  }
  KRML_MAYBE_UNUSED_VAR(ite);
  cbor_det_array_iterator_t c12 = pc4;
  cbor_det_array_iterator_t
  buf2 = cbor_det_array_iterator_truncate(c1, rlen02 - cbor_det_array_iterator_length(c12));
  cbor_det_t x2 = cbor_det_array_iterator_next(&buf2);
  FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t___ w12;
  if (COSE_Format_validate_bstr(x2))
    w12 =
      (
        (FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t___){
          .tag = COSE_Format_Inl,
          .v = COSE_Format_parse_bstr(x2)
        }
      );
  else
  {
    COSE_Format_parse_nil(x2);
    w12 = ((FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t___){ .tag = COSE_Format_Inr });
  }
  cbor_det_array_iterator_t buf = c12;
  return
    COSE_Format_cose_sign1_right((
        (COSE_Format_cose_sign1_ugly){
          ._1 = w11,
          ._2 = { ._1 = w12, ._2 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf)) }
        }
      ));
}

/**
Serializer for cose_sign1
*/
size_t
COSE_Format_serialize_cose_sign1(COSE_Format_cose_sign1 c, Pulse_Lib_Slice_slice__uint8_t out)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_cose_sign1_ugly scrut = COSE_Format_cose_sign1_left(c);
  FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_COSE_Format_header_map
  c1 = scrut._1;
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t____Pulse_Lib_Slice_slice__uint8_t
  c2 = scrut._2;
  COSE_Format_empty_or_serialized_map c110 = c1._1;
  COSE_Format_header_map c210 = c1._2;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    size_t
    size1 = COSE_Format_serialize_empty_or_serialized_map(c110, split__uint8_t(out, size)._2);
    if (size1 == (size_t)0U)
      ite0 = false;
    else
    {
      pcount = count0 + 1ULL;
      psize = size + size1;
      ite0 = true;
    }
  }
  else
    ite0 = false;
  bool ite1;
  if (ite0)
  {
    uint64_t count1 = pcount;
    if (count1 < 18446744073709551615ULL)
    {
      size_t size = psize;
      size_t size1 = COSE_Format_serialize_header_map(c210, split__uint8_t(out, size)._2);
      if (size1 == (size_t)0U)
        ite1 = false;
      else
      {
        pcount = count1 + 1ULL;
        psize = size + size1;
        ite1 = true;
      }
    }
    else
      ite1 = false;
  }
  else
    ite1 = false;
  bool ite2;
  if (ite1)
  {
    FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t___ c11 = c2._1;
    Pulse_Lib_Slice_slice__uint8_t c21 = c2._2;
    uint64_t count = pcount;
    bool ite;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size)._2;
      size_t size1;
      if (c11.tag == COSE_Format_Inl)
        size1 = COSE_Format_serialize_bstr(c11.v, out1);
      else if (c11.tag == COSE_Format_Inr)
        size1 = COSE_Format_serialize_nil(out1);
      else
        size1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (size1 == (size_t)0U)
        ite = false;
      else
      {
        pcount = count + 1ULL;
        psize = size + size1;
        ite = true;
      }
    }
    else
      ite = false;
    if (ite)
    {
      uint64_t count1 = pcount;
      if (count1 < 18446744073709551615ULL)
      {
        size_t size = psize;
        size_t size1 = COSE_Format_serialize_bstr(c21, split__uint8_t(out, size)._2);
        if (size1 == (size_t)0U)
          ite2 = false;
        else
        {
          pcount = count1 + 1ULL;
          psize = size + size1;
          ite2 = true;
        }
      }
      else
        ite2 = false;
    }
    else
      ite2 = false;
  }
  else
    ite2 = false;
  if (ite2)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
    return
      cbor_det_serialize_array_to_array(count,
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cose_sign1(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cose_sign1(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cose_sign1(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_cose_sign1_tagged(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (18ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_cose_sign1(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

COSE_Format_cose_sign1 COSE_Format_cose_sign1_tagged_right(COSE_Format_cose_sign1 x1)
{
  return x1;
}

COSE_Format_cose_sign1 COSE_Format_cose_sign1_tagged_left(COSE_Format_cose_sign1 x4)
{
  return x4;
}

/**
Parser for cose_sign1_tagged
*/
COSE_Format_cose_sign1 COSE_Format_parse_cose_sign1_tagged(cbor_det_t c)
{
  return COSE_Format_parse_cose_sign1(cbor_det_get_tagged_payload(c));
}

/**
Serializer for cose_sign1_tagged
*/
size_t
COSE_Format_serialize_cose_sign1_tagged(
  COSE_Format_cose_sign1 c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_cose_sign1 cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(18ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_cose_sign1(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cose_sign1_tagged(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cose_sign1_tagged(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cose_sign1_tagged(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_validate_cose_signature(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(c);
    bool ite0;
    if (cbor_det_array_iterator_is_empty(pi))
      ite0 = false;
    else
      ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pi));
    bool ite1;
    if (ite0)
      if (cbor_det_array_iterator_is_empty(pi))
        ite1 = false;
      else
        ite1 = COSE_Format_validate_header_map(cbor_det_array_iterator_next(&pi));
    else
      ite1 = false;
    bool ite;
    if (ite1)
      if (cbor_det_array_iterator_is_empty(pi))
        ite = false;
      else
        ite = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pi));
    else
      ite = false;
    if (ite)
      return cbor_det_array_iterator_is_empty(pi);
    else
      return false;
  }
  else
    return false;
}

COSE_Format_cose_signature COSE_Format_cose_signature_right(COSE_Format_cose_signature_ugly x3)
{
  return
    (
      (COSE_Format_cose_signature){
        .protected0 = x3._1._1,
        .unprotected = x3._1._2,
        .signature = x3._2
      }
    );
}

COSE_Format_cose_signature_ugly COSE_Format_cose_signature_left(COSE_Format_cose_signature x8)
{
  return
    (
      (COSE_Format_cose_signature_ugly){
        ._1 = { ._1 = x8.protected0, ._2 = x8.unprotected },
        ._2 = x8.signature
      }
    );
}

/**
Parser for cose_signature
*/
COSE_Format_cose_signature COSE_Format_parse_cose_signature(cbor_det_t c)
{
  cbor_det_array_iterator_t ar = cbor_det_array_iterator_start(c);
  uint64_t rlen0 = cbor_det_array_iterator_length(ar);
  cbor_det_array_iterator_t pc = ar;
  bool ite0;
  if (cbor_det_array_iterator_is_empty(pc))
    ite0 = false;
  else
    ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc));
  bool ite1;
  if (ite0)
    if (cbor_det_array_iterator_is_empty(pc))
      ite1 = false;
    else
      ite1 = COSE_Format_validate_header_map(cbor_det_array_iterator_next(&pc));
  else
    ite1 = false;
  KRML_MAYBE_UNUSED_VAR(ite1);
  cbor_det_array_iterator_t c1 = pc;
  cbor_det_array_iterator_t
  c0_ = cbor_det_array_iterator_truncate(ar, rlen0 - cbor_det_array_iterator_length(c1));
  uint64_t rlen01 = cbor_det_array_iterator_length(c0_);
  cbor_det_array_iterator_t pc1 = c0_;
  bool ite;
  if (cbor_det_array_iterator_is_empty(pc1))
    ite = false;
  else
    ite = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc1));
  KRML_MAYBE_UNUSED_VAR(ite);
  cbor_det_array_iterator_t c11 = pc1;
  cbor_det_array_iterator_t
  buf0 = cbor_det_array_iterator_truncate(c0_, rlen01 - cbor_det_array_iterator_length(c11));
  COSE_Format_empty_or_serialized_map
  w1 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
  cbor_det_array_iterator_t buf1 = c11;
  FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_COSE_Format_header_map
  w11 = { ._1 = w1, ._2 = COSE_Format_parse_header_map(cbor_det_array_iterator_next(&buf1)) };
  cbor_det_array_iterator_t buf = c1;
  return
    COSE_Format_cose_signature_right((
        (COSE_Format_cose_signature_ugly){
          ._1 = w11,
          ._2 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf))
        }
      ));
}

/**
Serializer for cose_signature
*/
size_t
COSE_Format_serialize_cose_signature(
  COSE_Format_cose_signature c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_cose_signature_ugly scrut = COSE_Format_cose_signature_left(c);
  FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_COSE_Format_header_map
  c1 = scrut._1;
  Pulse_Lib_Slice_slice__uint8_t c2 = scrut._2;
  COSE_Format_empty_or_serialized_map c11 = c1._1;
  COSE_Format_header_map c21 = c1._2;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    size_t
    size1 = COSE_Format_serialize_empty_or_serialized_map(c11, split__uint8_t(out, size)._2);
    if (size1 == (size_t)0U)
      ite0 = false;
    else
    {
      pcount = count0 + 1ULL;
      psize = size + size1;
      ite0 = true;
    }
  }
  else
    ite0 = false;
  bool ite1;
  if (ite0)
  {
    uint64_t count1 = pcount;
    if (count1 < 18446744073709551615ULL)
    {
      size_t size = psize;
      size_t size1 = COSE_Format_serialize_header_map(c21, split__uint8_t(out, size)._2);
      if (size1 == (size_t)0U)
        ite1 = false;
      else
      {
        pcount = count1 + 1ULL;
        psize = size + size1;
        ite1 = true;
      }
    }
    else
      ite1 = false;
  }
  else
    ite1 = false;
  bool ite;
  if (ite1)
  {
    uint64_t count = pcount;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      size_t size1 = COSE_Format_serialize_bstr(c2, split__uint8_t(out, size)._2);
      if (size1 == (size_t)0U)
        ite = false;
      else
      {
        pcount = count + 1ULL;
        psize = size + size1;
        ite = true;
      }
    }
    else
      ite = false;
  }
  else
    ite = false;
  if (ite)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
    return
      cbor_det_serialize_array_to_array(count,
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_signature_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cose_signature(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_signature_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cose_signature(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_signature_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cose_signature(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_signature_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool COSE_Format_aux_env41_validate_1(cbor_det_array_iterator_t *pi)
{
  if (cbor_det_array_iterator_is_empty(pi[0U]))
    return false;
  else
    return COSE_Format_validate_cose_signature(cbor_det_array_iterator_next(pi));
}

COSE_Format_cose_signature COSE_Format_aux_env41_type_1_right(COSE_Format_cose_signature x1)
{
  return x1;
}

COSE_Format_cose_signature COSE_Format_aux_env41_type_1_left(COSE_Format_cose_signature x4)
{
  return x4;
}

/**
Parser for aux_env41_type_1
*/
COSE_Format_cose_signature COSE_Format_aux_env41_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t buf = c;
  return COSE_Format_parse_cose_signature(cbor_det_array_iterator_next(&buf));
}

/**
Serializer for aux_env41_type_1
*/
bool
COSE_Format_aux_env41_serialize_1(
  COSE_Format_cose_signature c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  uint64_t count = out_count[0U];
  if (count < 18446744073709551615ULL)
  {
    size_t size = out_size[0U];
    size_t size1 = COSE_Format_serialize_cose_signature(c, split__uint8_t(out, size)._2);
    if (size1 == (size_t)0U)
      return false;
    else
    {
      out_count[0U] = count + 1ULL;
      out_size[0U] = size + size1;
      return true;
    }
  }
  else
    return false;
}

bool COSE_Format_validate_cose_sign(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(c);
    bool ite0;
    if (cbor_det_array_iterator_is_empty(pi))
      ite0 = false;
    else
      ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pi));
    bool ite1;
    if (ite0)
      if (cbor_det_array_iterator_is_empty(pi))
        ite1 = false;
      else
        ite1 = COSE_Format_validate_header_map(cbor_det_array_iterator_next(&pi));
    else
      ite1 = false;
    bool ite2;
    if (ite1)
    {
      bool ite0;
      if (cbor_det_array_iterator_is_empty(pi))
        ite0 = false;
      else
      {
        cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
        if (COSE_Format_validate_bstr(c1))
          ite0 = true;
        else
          ite0 = COSE_Format_validate_nil(c1);
      }
      if (ite0)
        if (cbor_det_array_iterator_is_empty(pi))
          ite2 = false;
        else
        {
          cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
          if (cbor_det_major_type(c1) == CBOR_MAJOR_TYPE_ARRAY)
          {
            cbor_det_array_iterator_t pi1 = cbor_det_array_iterator_start(c1);
            bool ite0;
            if (cbor_det_array_iterator_is_empty(pi1))
              ite0 = false;
            else
              ite0 = COSE_Format_validate_cose_signature(cbor_det_array_iterator_next(&pi1));
            bool ite1;
            if (ite0)
            {
              bool pcont = true;
              while (pcont)
              {
                cbor_det_array_iterator_t i11 = pi1;
                bool ite;
                if (cbor_det_array_iterator_is_empty(pi1))
                  ite = false;
                else
                  ite = COSE_Format_validate_cose_signature(cbor_det_array_iterator_next(&pi1));
                if (!ite)
                {
                  pi1 = i11;
                  pcont = false;
                }
              }
              ite1 = true;
            }
            else
              ite1 = false;
            if (ite1)
              ite2 = cbor_det_array_iterator_is_empty(pi1);
            else
              ite2 = false;
          }
          else
            ite2 = false;
        }
      else
        ite2 = false;
    }
    else
      ite2 = false;
    if (ite2)
      return cbor_det_array_iterator_is_empty(pi);
    else
      return false;
  }
  else
    return false;
}

COSE_Format_cose_sign COSE_Format_cose_sign_right(COSE_Format_cose_sign_ugly x4)
{
  return
    (
      (COSE_Format_cose_sign){
        .protected0 = x4._1._1,
        .unprotected = x4._1._2,
        .payload = x4._2._1,
        .signatures = x4._2._2
      }
    );
}

COSE_Format_cose_sign_ugly COSE_Format_cose_sign_left(COSE_Format_cose_sign x10)
{
  return
    (
      (COSE_Format_cose_sign_ugly){
        ._1 = { ._1 = x10.protected0, ._2 = x10.unprotected },
        ._2 = { ._1 = x10.payload, ._2 = x10.signatures }
      }
    );
}

/**
Parser for cose_sign
*/
COSE_Format_cose_sign COSE_Format_parse_cose_sign(cbor_det_t c)
{
  cbor_det_array_iterator_t ar = cbor_det_array_iterator_start(c);
  uint64_t rlen0 = cbor_det_array_iterator_length(ar);
  cbor_det_array_iterator_t pc = ar;
  bool ite0;
  if (cbor_det_array_iterator_is_empty(pc))
    ite0 = false;
  else
    ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc));
  bool ite1;
  if (ite0)
    if (cbor_det_array_iterator_is_empty(pc))
      ite1 = false;
    else
      ite1 = COSE_Format_validate_header_map(cbor_det_array_iterator_next(&pc));
  else
    ite1 = false;
  KRML_MAYBE_UNUSED_VAR(ite1);
  cbor_det_array_iterator_t c1 = pc;
  cbor_det_array_iterator_t
  c0_ = cbor_det_array_iterator_truncate(ar, rlen0 - cbor_det_array_iterator_length(c1));
  uint64_t rlen01 = cbor_det_array_iterator_length(c0_);
  cbor_det_array_iterator_t pc1 = c0_;
  bool ite2;
  if (cbor_det_array_iterator_is_empty(pc1))
    ite2 = false;
  else
    ite2 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc1));
  KRML_MAYBE_UNUSED_VAR(ite2);
  cbor_det_array_iterator_t c11 = pc1;
  cbor_det_array_iterator_t
  buf0 = cbor_det_array_iterator_truncate(c0_, rlen01 - cbor_det_array_iterator_length(c11));
  COSE_Format_empty_or_serialized_map
  w1 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
  cbor_det_array_iterator_t buf1 = c11;
  FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_COSE_Format_header_map
  w11 = { ._1 = w1, ._2 = COSE_Format_parse_header_map(cbor_det_array_iterator_next(&buf1)) };
  uint64_t rlen02 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t pc4 = c1;
  bool ite;
  if (cbor_det_array_iterator_is_empty(pc4))
    ite = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc4);
    if (COSE_Format_validate_bstr(c2))
      ite = true;
    else
      ite = COSE_Format_validate_nil(c2);
  }
  KRML_MAYBE_UNUSED_VAR(ite);
  cbor_det_array_iterator_t c12 = pc4;
  cbor_det_array_iterator_t
  buf2 = cbor_det_array_iterator_truncate(c1, rlen02 - cbor_det_array_iterator_length(c12));
  cbor_det_t x2 = cbor_det_array_iterator_next(&buf2);
  FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t___ w12;
  if (COSE_Format_validate_bstr(x2))
    w12 =
      (
        (FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t___){
          .tag = COSE_Format_Inl,
          .v = COSE_Format_parse_bstr(x2)
        }
      );
  else
  {
    COSE_Format_parse_nil(x2);
    w12 = ((FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t___){ .tag = COSE_Format_Inr });
  }
  cbor_det_array_iterator_t buf = c12;
  return
    COSE_Format_cose_sign_right((
        (COSE_Format_cose_sign_ugly){
          ._1 = w11,
          ._2 = {
            ._1 = w12,
            ._2 = {
              .tag = COSE_Format_Inr,
              {
                .case_Inr = {
                  .cddl_array_iterator_contents = cbor_det_array_iterator_start(cbor_det_array_iterator_next(&buf)),
                  .cddl_array_iterator_impl_validate = COSE_Format_aux_env41_validate_1,
                  .cddl_array_iterator_impl_parse = COSE_Format_aux_env41_parse_1
                }
              }
            }
          }
        }
      ));
}

static size_t
len__COSE_Format_cose_signature(Pulse_Lib_Slice_slice__COSE_Format_cose_signature s)
{
  return s.len;
}

static COSE_Format_cose_signature
op_Array_Access__COSE_Format_cose_signature(
  Pulse_Lib_Slice_slice__COSE_Format_cose_signature a,
  size_t i
)
{
  return a.elt[i];
}

/**
Serializer for cose_sign
*/
size_t
COSE_Format_serialize_cose_sign(COSE_Format_cose_sign c, Pulse_Lib_Slice_slice__uint8_t out)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_cose_sign_ugly scrut = COSE_Format_cose_sign_left(c);
  FStar_Pervasives_Native_tuple2__COSE_Format_empty_or_serialized_map_COSE_Format_header_map
  c1 = scrut._1;
  FStar_Pervasives_Native_tuple2__FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t____FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature
  c2 = scrut._2;
  COSE_Format_empty_or_serialized_map c110 = c1._1;
  COSE_Format_header_map c210 = c1._2;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    size_t
    size1 = COSE_Format_serialize_empty_or_serialized_map(c110, split__uint8_t(out, size)._2);
    if (size1 == (size_t)0U)
      ite0 = false;
    else
    {
      pcount = count0 + 1ULL;
      psize = size + size1;
      ite0 = true;
    }
  }
  else
    ite0 = false;
  bool ite1;
  if (ite0)
  {
    uint64_t count1 = pcount;
    if (count1 < 18446744073709551615ULL)
    {
      size_t size = psize;
      size_t size1 = COSE_Format_serialize_header_map(c210, split__uint8_t(out, size)._2);
      if (size1 == (size_t)0U)
        ite1 = false;
      else
      {
        pcount = count1 + 1ULL;
        psize = size + size1;
        ite1 = true;
      }
    }
    else
      ite1 = false;
  }
  else
    ite1 = false;
  bool ite2;
  if (ite1)
  {
    FStar_Pervasives_either__Pulse_Lib_Slice_slice__uint8_t___ c11 = c2._1;
    FStar_Pervasives_either__Pulse_Lib_Slice_slice__COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature
    c21 = c2._2;
    uint64_t count = pcount;
    bool ite0;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size)._2;
      size_t size1;
      if (c11.tag == COSE_Format_Inl)
        size1 = COSE_Format_serialize_bstr(c11.v, out1);
      else if (c11.tag == COSE_Format_Inr)
        size1 = COSE_Format_serialize_nil(out1);
      else
        size1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (size1 == (size_t)0U)
        ite0 = false;
      else
      {
        pcount = count + 1ULL;
        psize = size + size1;
        ite0 = true;
      }
    }
    else
      ite0 = false;
    if (ite0)
    {
      uint64_t count1 = pcount;
      if (count1 < 18446744073709551615ULL)
      {
        size_t size = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size)._2;
        uint64_t pcount1 = 0ULL;
        size_t psize1 = (size_t)0U;
        bool ite;
        if (c21.tag == COSE_Format_Inl)
        {
          Pulse_Lib_Slice_slice__COSE_Format_cose_signature c12 = c21.case_Inl;
          if (len__COSE_Format_cose_signature(c12) == (size_t)0U)
            ite = false;
          else
          {
            bool pres = true;
            size_t pi = (size_t)0U;
            size_t slen = len__COSE_Format_cose_signature(c12);
            while (pres && pi < slen)
            {
              size_t i = pi;
              if
              (
                COSE_Format_aux_env41_serialize_1(op_Array_Access__COSE_Format_cose_signature(c12,
                    i),
                  out1,
                  &pcount1,
                  &psize1)
              )
                pi = i + (size_t)1U;
              else
                pres = false;
            }
            ite = pres;
          }
        }
        else if (c21.tag == COSE_Format_Inr)
        {
          CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature
          c22 = c21.case_Inr;
          if (cbor_det_array_iterator_is_empty(c22.cddl_array_iterator_contents))
            ite = false;
          else
          {
            CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature
            pc = c22;
            bool pres = true;
            bool em1 = cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
            bool cond = pres && !em1;
            while (cond)
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature
              i = pc;
              uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
              cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
              KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
              cbor_det_array_iterator_t ji = pj;
              uint64_t len1 = cbor_det_array_iterator_length(ji);
              pc =
                (
                  (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature){
                    .cddl_array_iterator_contents = ji,
                    .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
                    .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
                  }
                );
              if
              (
                !COSE_Format_aux_env41_serialize_1(i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
                      len0 - len1)),
                  out1,
                  &pcount1,
                  &psize1)
              )
                pres = false;
              bool em1 = cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
              cond = pres && !em1;
            }
            bool ret = pres;
            ite = ret ? ret : ret;
          }
        }
        else
          ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
        size_t size10;
        if (ite)
        {
          size_t size1 = psize1;
          uint64_t count2 = pcount1;
          size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out1);
          size10 =
            cbor_det_serialize_array_to_array(count2,
              Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
              aout_len,
              size1);
        }
        else
          size10 = (size_t)0U;
        if (size10 == (size_t)0U)
          ite2 = false;
        else
        {
          pcount = count1 + 1ULL;
          psize = size + size10;
          ite2 = true;
        }
      }
      else
        ite2 = false;
    }
    else
      ite2 = false;
  }
  else
    ite2 = false;
  if (ite2)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
    return
      cbor_det_serialize_array_to_array(count,
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cose_sign(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cose_sign(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cose_sign(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool
COSE_Format_is_empty_iterate_array_aux_env41_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature
  i
)
{
  return cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents);
}

COSE_Format_cose_signature
COSE_Format_next_iterate_array_aux_env41_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature
  *pi
)
{
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature
  i = pi[0U];
  uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
  cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
  KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
  cbor_det_array_iterator_t ji = pj;
  uint64_t len1 = cbor_det_array_iterator_length(ji);
  pi[0U] =
    (
      (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_cose_signature){
        .cddl_array_iterator_contents = ji,
        .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
        .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
      }
    );
  return
    i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
        len0 - len1));
}

bool COSE_Format_validate_cose_sign_tagged(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (98ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_cose_sign(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

COSE_Format_cose_sign COSE_Format_cose_sign_tagged_right(COSE_Format_cose_sign x1)
{
  return x1;
}

COSE_Format_cose_sign COSE_Format_cose_sign_tagged_left(COSE_Format_cose_sign x4)
{
  return x4;
}

/**
Parser for cose_sign_tagged
*/
COSE_Format_cose_sign COSE_Format_parse_cose_sign_tagged(cbor_det_t c)
{
  return COSE_Format_parse_cose_sign(cbor_det_get_tagged_payload(c));
}

/**
Serializer for cose_sign_tagged
*/
size_t
COSE_Format_serialize_cose_sign_tagged(
  COSE_Format_cose_sign c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_cose_sign cpayload = c;
  size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out);
  size_t
  tsz =
    cbor_det_serialize_tag_to_array(98ULL,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out),
      aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    size_t psz = COSE_Format_serialize_cose_sign(cpayload, split__uint8_t(out, tsz)._2);
    return psz == (size_t)0U ? (size_t)0U : tsz + psz;
  }
}

FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign_Pulse_Lib_Slice_slice__uint8_t
COSE_Format_validate_and_parse_cose_sign_tagged(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len1 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0;
  if (len1 == (size_t)0U)
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(s, len1);
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut._1;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut._2;
    size_t len2 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            ._1 = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len2),
            ._2 = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign_Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice__uint8_t
    rlrem = scrut0.v;
    cbor_det_t rl = rlrem._1;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem._2;
    if (COSE_Format_validate_cose_sign_tagged(rl))
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { ._1 = COSE_Format_parse_cose_sign_tagged(rl), ._2 = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign_Pulse_Lib_Slice_slice__uint8_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}


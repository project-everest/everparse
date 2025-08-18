

#include "internal/COSE_Format.h"

#include "CBORDetAPI.h"

#define SIMPLE_VALUE_FALSE (20U)

#define SIMPLE_VALUE_TRUE (21U)

typedef enum { MGOK, MGFail, MGCutFail } impl_map_group_result;

static bool uu___is_MGOK(impl_map_group_result projectee)
{
  switch (projectee)
  {
    case MGOK:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

#define CDDL_SIMPLE_VALUE_FALSE (20U)

#define CDDL_SIMPLE_VALUE_TRUE (21U)

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

bool COSE_Format_uu___is_Mkevercddl_bool0(bool projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static bool evercddl_bool_right(bool x1)
{
  return x1;
}

static bool evercddl_bool_left(bool x3)
{
  return x3;
}

/**
Parser for evercddl_bool
*/
bool COSE_Format_parse_bool(cbor_det_t c)
{
  return evercddl_bool_right(cbor_det_read_simple_value(c) == SIMPLE_VALUE_TRUE);
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
  if (evercddl_bool_left(c))
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

typedef struct __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t_s
{
  Pulse_Lib_Slice_slice__uint8_t fst;
  Pulse_Lib_Slice_slice__uint8_t snd;
}
__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t;

static __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
split__uint8_t(Pulse_Lib_Slice_slice__uint8_t s, size_t i)
{
  return
    (
      (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

typedef struct __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t_s
{
  cbor_det_t fst;
  Pulse_Lib_Slice_slice__uint8_t snd;
}
__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t;

typedef struct option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t__s
{
  FStar_Pervasives_Native_option__size_t_tags tag;
  __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t v;
}
option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_;

FStar_Pervasives_Native_option___COSE_Format_evercddl_bool___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_bool(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_bool___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_bool(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bool___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_bool(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bool___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkeverparsenomatch0(COSE_Format_everparsenomatch projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_everparsenomatch everparsenomatch_right(void)
{
  return COSE_Format_Mkeverparsenomatch0;
}

/**
Parser for everparsenomatch
*/
COSE_Format_everparsenomatch COSE_Format_parse_everparsenomatch(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return everparsenomatch_right();
}

/**
Serializer for everparsenomatch
*/
size_t
COSE_Format_serialize_everparsenomatch(
  COSE_Format_everparsenomatch c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  KRML_MAYBE_UNUSED_VAR(out);
  return (size_t)0U;
}

FStar_Pervasives_Native_option___COSE_Format_everparsenomatch___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_everparsenomatch(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_everparsenomatch___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_everparsenomatch(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_everparsenomatch___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_everparsenomatch(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_everparsenomatch___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkany0(cbor_det_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static cbor_det_t any_right(cbor_det_t x1)
{
  return x1;
}

static cbor_det_t any_left(cbor_det_t x3)
{
  return x3;
}

/**
Parser for any
*/
cbor_det_t COSE_Format_parse_any(cbor_det_t c)
{
  return any_right(c);
}

/**
Serializer for any
*/
size_t COSE_Format_serialize_any(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t c_ = any_left(c);
  size_t len = cbor_det_size(c_, Pulse_Lib_Slice_len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c_, Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out), len)
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

FStar_Pervasives_Native_option___COSE_Format_any___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_any(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_any___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_any(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_any___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_any(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_any___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkundefined0(COSE_Format_undefined projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_undefined undefined_right(void)
{
  return COSE_Format_Mkundefined0;
}

/**
Parser for undefined
*/
COSE_Format_undefined COSE_Format_parse_undefined(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return undefined_right();
}

/**
Serializer for undefined
*/
size_t
COSE_Format_serialize_undefined(COSE_Format_undefined c, Pulse_Lib_Slice_slice__uint8_t out)
{
  KRML_MAYBE_UNUSED_VAR(c);
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

FStar_Pervasives_Native_option___COSE_Format_undefined___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_undefined(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_undefined___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_undefined(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_undefined___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_undefined(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_undefined___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mknil0(COSE_Format_nil projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_nil nil_right(void)
{
  return COSE_Format_Mknil0;
}

/**
Parser for nil
*/
COSE_Format_nil COSE_Format_parse_nil(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return nil_right();
}

/**
Serializer for nil
*/
size_t COSE_Format_serialize_nil(COSE_Format_nil c, Pulse_Lib_Slice_slice__uint8_t out)
{
  KRML_MAYBE_UNUSED_VAR(c);
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

FStar_Pervasives_Native_option___COSE_Format_nil___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_nil(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_nil___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_nil(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_nil___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_nil(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_nil___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkevercddl_null0(COSE_Format_nil projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_nil evercddl_null_right(COSE_Format_nil x1)
{
  return x1;
}

static COSE_Format_nil evercddl_null_left(COSE_Format_nil x3)
{
  return x3;
}

/**
Parser for evercddl_null
*/
COSE_Format_nil COSE_Format_parse_null(cbor_det_t c)
{
  return evercddl_null_right(COSE_Format_parse_nil(c));
}

/**
Serializer for evercddl_null
*/
size_t COSE_Format_serialize_null(COSE_Format_nil c, Pulse_Lib_Slice_slice__uint8_t out)
{
  return COSE_Format_serialize_nil(evercddl_null_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_null___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_null(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_null___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_null(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_null___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_null(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_null___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkevercddl_true0(COSE_Format_evercddl_true projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_evercddl_true evercddl_true_right(void)
{
  return COSE_Format_Mkevercddl_true0;
}

/**
Parser for evercddl_true
*/
COSE_Format_evercddl_true COSE_Format_parse_true(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return evercddl_true_right();
}

/**
Serializer for evercddl_true
*/
size_t
COSE_Format_serialize_true(COSE_Format_evercddl_true c, Pulse_Lib_Slice_slice__uint8_t out)
{
  KRML_MAYBE_UNUSED_VAR(c);
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_true___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_true(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_true___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_true(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_true___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_true(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_true___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkevercddl_false0(COSE_Format_evercddl_false projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_evercddl_false evercddl_false_right(void)
{
  return COSE_Format_Mkevercddl_false0;
}

/**
Parser for evercddl_false
*/
COSE_Format_evercddl_false COSE_Format_parse_false(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return evercddl_false_right();
}

/**
Serializer for evercddl_false
*/
size_t
COSE_Format_serialize_false(COSE_Format_evercddl_false c, Pulse_Lib_Slice_slice__uint8_t out)
{
  KRML_MAYBE_UNUSED_VAR(c);
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_false___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_false(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_false___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_false(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_false___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_false(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_false___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mktstr0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t tstr_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t tstr_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
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
  return tstr_right(arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len));
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
  Pulse_Lib_Slice_slice__uint8_t c_ = tstr_left(c);
  if (Pulse_Lib_Slice_len__uint8_t(c_) <= (size_t)18446744073709551615ULL)
  {
    size_t alen = Pulse_Lib_Slice_len__uint8_t(c_);
    if
    (
      cbor_det_impl_utf8_correct_from_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c_),
        alen)
    )
    {
      uint8_t *a = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c_);
      cbor_det_t
      x =
        cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
          a,
          (uint64_t)Pulse_Lib_Slice_len__uint8_t(c_));
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

FStar_Pervasives_Native_option___COSE_Format_tstr___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_tstr(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_tstr___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_tstr(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_tstr___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_tstr(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_tstr___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkbstr0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t bstr_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t bstr_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for bstr
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_bstr(cbor_det_t c)
{
  uint64_t len = cbor_det_get_string_length(c);
  return bstr_right(arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len));
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
  Pulse_Lib_Slice_slice__uint8_t c_ = bstr_left(c);
  if (Pulse_Lib_Slice_len__uint8_t(c_) <= (size_t)18446744073709551615ULL)
  {
    uint8_t *a = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c_);
    cbor_det_t
    x =
      cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_BYTE_STRING,
        a,
        (uint64_t)Pulse_Lib_Slice_len__uint8_t(c_));
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

FStar_Pervasives_Native_option___COSE_Format_bstr___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_bstr(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_bstr___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_bstr(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_bstr___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_bstr(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_bstr___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkbytes0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t bytes_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t bytes_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for bytes
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_bytes(cbor_det_t c)
{
  return bytes_right(COSE_Format_parse_bstr(c));
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
  return COSE_Format_serialize_bstr(bytes_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_bytes___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_bytes(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_bytes___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_bytes(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_bytes___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_bytes(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_bytes___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mktext0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t text_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t text_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for text
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_text(cbor_det_t c)
{
  return text_right(COSE_Format_parse_tstr(c));
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
  return COSE_Format_serialize_tstr(text_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_text___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_text(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_text___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_text(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_text___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_text(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_text___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mknint0(uint64_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static uint64_t nint_right(uint64_t x1)
{
  return x1;
}

static uint64_t nint_left(uint64_t x3)
{
  return x3;
}

/**
Parser for nint
*/
uint64_t COSE_Format_parse_nint(cbor_det_t c)
{
  return nint_right(cbor_det_read_uint64(c));
}

/**
Serializer for nint
*/
size_t COSE_Format_serialize_nint(uint64_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t x = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, nint_left(c));
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

FStar_Pervasives_Native_option___COSE_Format_nint___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_nint(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_nint___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_nint(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_nint___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_nint(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_nint___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkevercddl_uint0(uint64_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static uint64_t evercddl_uint_right(uint64_t x1)
{
  return x1;
}

static uint64_t evercddl_uint_left(uint64_t x3)
{
  return x3;
}

/**
Parser for evercddl_uint
*/
uint64_t COSE_Format_parse_uint(cbor_det_t c)
{
  return evercddl_uint_right(cbor_det_read_uint64(c));
}

/**
Serializer for evercddl_uint
*/
size_t COSE_Format_serialize_uint(uint64_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t x = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, evercddl_uint_left(c));
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_uint___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_uint(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_uint___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_uint(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_uint___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_uint(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_uint___Pulse_Lib_Slice_slice_uint8_t_){
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

typedef struct evercddl_int_ugly_s
{
  COSE_Format_evercddl_int_ugly_tags tag;
  union {
    uint64_t case_Inl;
    uint64_t case_Inr;
  }
  ;
}
evercddl_int_ugly;

bool COSE_Format_uu___is_Mkevercddl_int0(COSE_Format_evercddl_int projectee)
{
  if (projectee.tag == COSE_Format_Mkevercddl_int0)
    return true;
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_int1(COSE_Format_evercddl_int projectee)
{
  if (projectee.tag == COSE_Format_Mkevercddl_int1)
    return true;
  else
    return false;
}

static COSE_Format_evercddl_int evercddl_int_right(evercddl_int_ugly x2)
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

static evercddl_int_ugly evercddl_int_left(COSE_Format_evercddl_int x7)
{
  if (x7.tag == COSE_Format_Mkevercddl_int0)
    return
      ((evercddl_int_ugly){ .tag = COSE_Format_Inl, { .case_Inl = x7.case_Mkevercddl_int0 } });
  else if (x7.tag == COSE_Format_Mkevercddl_int1)
    return
      ((evercddl_int_ugly){ .tag = COSE_Format_Inr, { .case_Inr = x7.case_Mkevercddl_int1 } });
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
  evercddl_int_ugly ite;
  if (COSE_Format_validate_uint(c))
    ite =
      ((evercddl_int_ugly){ .tag = COSE_Format_Inl, { .case_Inl = COSE_Format_parse_uint(c) } });
  else
    ite =
      ((evercddl_int_ugly){ .tag = COSE_Format_Inr, { .case_Inr = COSE_Format_parse_nint(c) } });
  return evercddl_int_right(ite);
}

/**
Serializer for evercddl_int
*/
size_t
COSE_Format_serialize_int(COSE_Format_evercddl_int c, Pulse_Lib_Slice_slice__uint8_t out)
{
  evercddl_int_ugly scrut = evercddl_int_left(c);
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_int___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_int(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_int___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_int(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_int___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_int(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_int___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkcborany0(cbor_det_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static cbor_det_t cborany_right(cbor_det_t x1)
{
  return x1;
}

static cbor_det_t cborany_left(cbor_det_t x3)
{
  return x3;
}

/**
Parser for cborany
*/
cbor_det_t COSE_Format_parse_cborany(cbor_det_t c)
{
  return cborany_right(COSE_Format_parse_any(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for cborany
*/
size_t COSE_Format_serialize_cborany(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t cpayload = cborany_left(c);
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
    size_t psz = COSE_Format_serialize_any(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_cborany___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cborany(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cborany___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cborany(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cborany___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cborany(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cborany___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkmimemessage0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t mimemessage_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t mimemessage_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for mimemessage
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_mimemessage(cbor_det_t c)
{
  return mimemessage_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
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
  Pulse_Lib_Slice_slice__uint8_t cpayload = mimemessage_left(c);
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
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_mimemessage___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_mimemessage(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_mimemessage___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_mimemessage(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_mimemessage___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_mimemessage(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_mimemessage___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkregexp0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t regexp_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t regexp_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for regexp
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_regexp(cbor_det_t c)
{
  return regexp_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
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
  Pulse_Lib_Slice_slice__uint8_t cpayload = regexp_left(c);
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
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_regexp___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_regexp(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_regexp___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_regexp(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_regexp___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_regexp(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_regexp___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkb64legacy0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t b64legacy_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t b64legacy_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for b64legacy
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_b64legacy(cbor_det_t c)
{
  return b64legacy_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
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
  Pulse_Lib_Slice_slice__uint8_t cpayload = b64legacy_left(c);
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
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_b64legacy___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_b64legacy(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_b64legacy___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_b64legacy(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_b64legacy___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_b64legacy(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_b64legacy___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkb64url0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t b64url_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t b64url_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for b64url
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_b64url(cbor_det_t c)
{
  return b64url_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
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
  Pulse_Lib_Slice_slice__uint8_t cpayload = b64url_left(c);
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
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_b64url___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_b64url(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_b64url___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_b64url(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_b64url___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_b64url(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_b64url___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkuri0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t uri_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t uri_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for uri
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_uri(cbor_det_t c)
{
  return uri_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for uri
*/
size_t
COSE_Format_serialize_uri(Pulse_Lib_Slice_slice__uint8_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  Pulse_Lib_Slice_slice__uint8_t cpayload = uri_left(c);
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
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_uri___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_uri(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_uri___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_uri(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_uri___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_uri(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_uri___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkencodedcbor0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t encodedcbor_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t encodedcbor_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for encodedcbor
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_encodedcbor(cbor_det_t c)
{
  return encodedcbor_right(COSE_Format_parse_bstr(cbor_det_get_tagged_payload(c)));
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
  Pulse_Lib_Slice_slice__uint8_t cpayload = encodedcbor_left(c);
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
    size_t psz = COSE_Format_serialize_bstr(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_encodedcbor___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_encodedcbor(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_encodedcbor___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_encodedcbor(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_encodedcbor___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_encodedcbor(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_encodedcbor___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkeb160(cbor_det_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static cbor_det_t eb16_right(cbor_det_t x1)
{
  return x1;
}

static cbor_det_t eb16_left(cbor_det_t x3)
{
  return x3;
}

/**
Parser for eb16
*/
cbor_det_t COSE_Format_parse_eb16(cbor_det_t c)
{
  return eb16_right(COSE_Format_parse_any(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for eb16
*/
size_t COSE_Format_serialize_eb16(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t cpayload = eb16_left(c);
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
    size_t psz = COSE_Format_serialize_any(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_eb16___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_eb16(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_eb16___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_eb16(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_eb16___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_eb16(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_eb16___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkeb64legacy0(cbor_det_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static cbor_det_t eb64legacy_right(cbor_det_t x1)
{
  return x1;
}

static cbor_det_t eb64legacy_left(cbor_det_t x3)
{
  return x3;
}

/**
Parser for eb64legacy
*/
cbor_det_t COSE_Format_parse_eb64legacy(cbor_det_t c)
{
  return eb64legacy_right(COSE_Format_parse_any(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for eb64legacy
*/
size_t COSE_Format_serialize_eb64legacy(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t cpayload = eb64legacy_left(c);
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
    size_t psz = COSE_Format_serialize_any(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_eb64legacy___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_eb64legacy(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_eb64legacy___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_eb64legacy(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_eb64legacy___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_eb64legacy(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_eb64legacy___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkeb64url0(cbor_det_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static cbor_det_t eb64url_right(cbor_det_t x1)
{
  return x1;
}

static cbor_det_t eb64url_left(cbor_det_t x3)
{
  return x3;
}

/**
Parser for eb64url
*/
cbor_det_t COSE_Format_parse_eb64url(cbor_det_t c)
{
  return eb64url_right(COSE_Format_parse_any(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for eb64url
*/
size_t COSE_Format_serialize_eb64url(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t cpayload = eb64url_left(c);
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
    size_t psz = COSE_Format_serialize_any(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_eb64url___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_eb64url(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_eb64url___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_eb64url(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_eb64url___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_eb64url(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_eb64url___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mknumber0(COSE_Format_evercddl_int projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_evercddl_int number_right(COSE_Format_evercddl_int x1)
{
  return x1;
}

static COSE_Format_evercddl_int number_left(COSE_Format_evercddl_int x3)
{
  return x3;
}

/**
Parser for number
*/
COSE_Format_evercddl_int COSE_Format_parse_number(cbor_det_t c)
{
  return number_right(COSE_Format_parse_int(c));
}

/**
Serializer for number
*/
size_t
COSE_Format_serialize_number(COSE_Format_evercddl_int c, Pulse_Lib_Slice_slice__uint8_t out)
{
  return COSE_Format_serialize_int(number_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_number___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_number(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_number___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_number(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_number___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_number(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_number___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mktdate0(Pulse_Lib_Slice_slice__uint8_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static Pulse_Lib_Slice_slice__uint8_t tdate_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t tdate_left(Pulse_Lib_Slice_slice__uint8_t x3)
{
  return x3;
}

/**
Parser for tdate
*/
Pulse_Lib_Slice_slice__uint8_t COSE_Format_parse_tdate(cbor_det_t c)
{
  return tdate_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
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
  Pulse_Lib_Slice_slice__uint8_t cpayload = tdate_left(c);
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
    size_t psz = COSE_Format_serialize_tstr(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_tdate___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_tdate(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_tdate___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_tdate(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_tdate___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_tdate(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_tdate___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkvalues0(cbor_det_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static cbor_det_t values_right(cbor_det_t x1)
{
  return x1;
}

static cbor_det_t values_left(cbor_det_t x3)
{
  return x3;
}

/**
Parser for values
*/
cbor_det_t COSE_Format_parse_values(cbor_det_t c)
{
  return values_right(COSE_Format_parse_any(c));
}

/**
Serializer for values
*/
size_t COSE_Format_serialize_values(cbor_det_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  return COSE_Format_serialize_any(values_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_values___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_values(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_values___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_values(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_values___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_values(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_values___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_label(cbor_det_t c)
{
  if (COSE_Format_validate_int(c))
    return true;
  else
    return COSE_Format_validate_tstr(c);
}

bool COSE_Format_uu___is_Mklabel0(COSE_Format_label projectee)
{
  if (projectee.tag == COSE_Format_Mklabel0)
    return true;
  else
    return false;
}

bool COSE_Format_uu___is_Mklabel1(COSE_Format_label projectee)
{
  if (projectee.tag == COSE_Format_Mklabel1)
    return true;
  else
    return false;
}

static COSE_Format_label label_right(COSE_Format_label_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return ((COSE_Format_label){ .tag = COSE_Format_Mklabel0, { .case_Mklabel0 = x2.case_Inl } });
  else if (x2.tag == COSE_Format_Inr)
    return ((COSE_Format_label){ .tag = COSE_Format_Mklabel1, { .case_Mklabel1 = x2.case_Inr } });
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static COSE_Format_label_ugly label_left(COSE_Format_label x7)
{
  if (x7.tag == COSE_Format_Mklabel0)
    return ((COSE_Format_label_ugly){ .tag = COSE_Format_Inl, { .case_Inl = x7.case_Mklabel0 } });
  else if (x7.tag == COSE_Format_Mklabel1)
    return ((COSE_Format_label_ugly){ .tag = COSE_Format_Inr, { .case_Inr = x7.case_Mklabel1 } });
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
Parser for label
*/
COSE_Format_label COSE_Format_parse_label(cbor_det_t c)
{
  COSE_Format_label_ugly ite;
  if (COSE_Format_validate_int(c))
    ite =
      ((COSE_Format_label_ugly){ .tag = COSE_Format_Inl, { .case_Inl = COSE_Format_parse_int(c) } });
  else
    ite =
      (
        (COSE_Format_label_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_tstr(c) }
        }
      );
  return label_right(ite);
}

/**
Serializer for label
*/
size_t COSE_Format_serialize_label(COSE_Format_label c, Pulse_Lib_Slice_slice__uint8_t out)
{
  COSE_Format_label_ugly scrut = label_left(c);
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

FStar_Pervasives_Native_option___COSE_Format_label___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_label(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_label___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_label(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_label___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_label(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_label___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_aux_env29_map_constraint_1(cbor_det_map_entry_t x)
{
  cbor_det_t k0 = cbor_det_map_entry_key(x);
  bool ite0;
  if (cbor_det_major_type(k0) == CBOR_MAJOR_TYPE_UINT64)
    ite0 = cbor_det_read_uint64(k0) == 1ULL;
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
    cbor_det_t k = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_NEG_INT64)
      ite = cbor_det_read_uint64(k) == 0ULL;
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
    cbor_det_t k = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_NEG_INT64)
      ite = cbor_det_read_uint64(k) == 1ULL;
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
    cbor_det_t k = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_NEG_INT64)
      ite = cbor_det_read_uint64(k) == 3ULL;
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

typedef struct option__CBOR_Pulse_API_Det_Type_cbor_det_t_s
{
  FStar_Pervasives_Native_option__size_t_tags tag;
  cbor_det_t v;
}
option__CBOR_Pulse_API_Det_Type_cbor_det_t;

bool COSE_Format_validate_cose_key_okp(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t remaining = cbor_det_get_map_length(c);
    cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest0 = c10;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
    if (cbor_det_map_get(c, c10, &dest0))
      scrut0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest0
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
        remaining = remaining - 1ULL;
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
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 0ULL);
          cbor_det_t dest = c1;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c1, &dest))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest
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
              remaining = remaining - 1ULL;
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
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
          cbor_det_t dest = c1;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c1, &dest))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest
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
              remaining = remaining - 1ULL;
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
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
          cbor_det_t dest = c1;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c1, &dest))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest
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
              remaining = remaining - 1ULL;
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
            if (COSE_Format_validate_label(cbor_det_map_entry_key(chd)))
              ite0 = COSE_Format_validate_values(cbor_det_map_entry_value(chd));
            else
              ite0 = false;
            bool ite1;
            if (ite0)
            {
              cbor_det_t k0 = cbor_det_map_entry_key(chd);
              bool ite0;
              if (cbor_det_major_type(k0) == CBOR_MAJOR_TYPE_UINT64)
                ite0 = cbor_det_read_uint64(k0) == 1ULL;
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
                cbor_det_t k = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_NEG_INT64)
                  ite = cbor_det_read_uint64(k) == 0ULL;
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
                cbor_det_t k = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_NEG_INT64)
                  ite = cbor_det_read_uint64(k) == 1ULL;
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
                cbor_det_t k = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_NEG_INT64)
                  ite = cbor_det_read_uint64(k) == 3ULL;
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
              remaining = remaining - 1ULL;
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

typedef struct
________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr__FStar_Pervasives_Native_option_COSE_Format_bstr_s
{
  COSE_Format_label_ugly fst;
  FStar_Pervasives_Native_option__COSE_Format_bstr snd;
}
________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr__FStar_Pervasives_Native_option_COSE_Format_bstr;

typedef struct
_________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_Native_option_COSE_Format_bstr_s
{
  ________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr__FStar_Pervasives_Native_option_COSE_Format_bstr
  fst;
  FStar_Pervasives_Native_option__COSE_Format_bstr snd;
}
_________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_Native_option_COSE_Format_bstr;

typedef struct cose_key_okp_ugly_s
{
  _________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_Native_option_COSE_Format_bstr
  fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_label___COSE_Format_values__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
  snd;
}
cose_key_okp_ugly;

bool COSE_Format_uu___is_Mkcose_key_okp0(COSE_Format_cose_key_okp projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_cose_key_okp cose_key_okp_right(cose_key_okp_ugly x5)
{
  return
    (
      (COSE_Format_cose_key_okp){
        .intkeyneg1 = x5.fst.fst.fst,
        .intkeyneg2 = x5.fst.fst.snd,
        .intkeyneg4 = x5.fst.snd,
        ._x0 = x5.snd
      }
    );
}

static cose_key_okp_ugly cose_key_okp_left(COSE_Format_cose_key_okp x11)
{
  return
    (
      (cose_key_okp_ugly){
        .fst = { .fst = { .fst = x11.intkeyneg1, .snd = x11.intkeyneg2 }, .snd = x11.intkeyneg4 },
        .snd = x11._x0
      }
    );
}

/**
Parser for cose_key_okp
*/
COSE_Format_cose_key_okp COSE_Format_parse_cose_key_okp(cbor_det_t c)
{
  cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
  cbor_det_t dest0 = c10;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t ite0;
  if (cbor_det_map_get(c, c10, &dest0))
    ite0 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest0
        }
      );
  else
    ite0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  if (!(ite0.tag == FStar_Pervasives_Native_Some))
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 0ULL);
  cbor_det_t dest1 = c11;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
  if (cbor_det_map_get(c, c11, &dest1))
    scrut0 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest1
        }
      );
  else
    scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  COSE_Format_label_ugly w1;
  if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t w = scrut0.v;
    if (COSE_Format_validate_int(w))
      w1 =
        (
          (COSE_Format_label_ugly){
            .tag = COSE_Format_Inl,
            { .case_Inl = COSE_Format_parse_int(w) }
          }
        );
    else
      w1 =
        (
          (COSE_Format_label_ugly){
            .tag = COSE_Format_Inr,
            { .case_Inr = COSE_Format_parse_tstr(w) }
          }
        );
  }
  else
    w1 = KRML_EABORT(COSE_Format_label_ugly, "unreachable (pattern matches are exhaustive in F*)");
  uint64_t buf0 = 0ULL;
  KRML_HOST_IGNORE(&buf0);
  cbor_det_t c12 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
  cbor_det_t dest2 = c12;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
  if (cbor_det_map_get(c, c12, &dest2))
    scrut1 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest2
        }
      );
  else
    scrut1 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite1;
  if (scrut1.tag == FStar_Pervasives_Native_None)
    ite1 = MGFail;
  else if (scrut1.tag == FStar_Pervasives_Native_Some)
    if (COSE_Format_validate_bstr(scrut1.v))
      ite1 = MGOK;
    else
      ite1 = MGCutFail;
  else
    ite1 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__COSE_Format_bstr ite2;
  if (uu___is_MGOK(ite1))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
    cbor_det_t dest = c1;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c1, &dest))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest
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
        (FStar_Pervasives_Native_option__COSE_Format_bstr){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite2 =
      ((FStar_Pervasives_Native_option__COSE_Format_bstr){ .tag = FStar_Pervasives_Native_None });
  ________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr__FStar_Pervasives_Native_option_COSE_Format_bstr
  w10 = { .fst = w1, .snd = ite2 };
  uint64_t buf = 0ULL;
  KRML_HOST_IGNORE(&buf);
  cbor_det_t c13 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
  cbor_det_t dest3 = c13;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut2;
  if (cbor_det_map_get(c, c13, &dest3))
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
  FStar_Pervasives_Native_option__COSE_Format_bstr ite4;
  if (uu___is_MGOK(ite3))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
    cbor_det_t dest = c1;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c1, &dest))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest
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
    ite4 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_bstr){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite4 =
      ((FStar_Pervasives_Native_option__COSE_Format_bstr){ .tag = FStar_Pervasives_Native_None });
  _________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_Native_option_COSE_Format_bstr
  w11 = { .fst = w10, .snd = ite4 };
  return
    cose_key_okp_right((
        (cose_key_okp_ugly){
          .fst = w11,
          .snd = {
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_map_iterator_contents = cbor_det_map_iterator_start(c),
                .cddl_map_iterator_impl_validate1 = COSE_Format_validate_label,
                .cddl_map_iterator_impl_parse1 = COSE_Format_parse_label,
                .cddl_map_iterator_impl_validate_ex = COSE_Format_aux_env29_map_constraint_1,
                .cddl_map_iterator_impl_validate2 = COSE_Format_validate_values,
                .cddl_map_iterator_impl_parse2 = COSE_Format_parse_values
              }
            }
          }
        }
      ));
}

static size_t
len___COSE_Format_label___COSE_Format_values_(
  Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ s
)
{
  return s.len;
}

static K___COSE_Format_label_COSE_Format_values
op_Array_Access___COSE_Format_label___COSE_Format_values_(
  Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ a,
  size_t i
)
{
  return a.elt[i];
}

typedef struct
__Pulse_Lib_Slice_slice__COSE_Format_label___COSE_Format_values__Pulse_Lib_Slice_slice__COSE_Format_label___COSE_Format_values__s
{
  Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ fst;
  Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ snd;
}
__Pulse_Lib_Slice_slice__COSE_Format_label___COSE_Format_values__Pulse_Lib_Slice_slice__COSE_Format_label___COSE_Format_values_;

static __Pulse_Lib_Slice_slice__COSE_Format_label___COSE_Format_values__Pulse_Lib_Slice_slice__COSE_Format_label___COSE_Format_values_
split___COSE_Format_label___COSE_Format_values_(
  Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ s,
  size_t i
)
{
  return
    (
      (__Pulse_Lib_Slice_slice__COSE_Format_label___COSE_Format_values__Pulse_Lib_Slice_slice__COSE_Format_label___COSE_Format_values_){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
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
  cose_key_okp_ugly scrut0 = cose_key_okp_left(c);
  _________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_Native_option_COSE_Format_bstr
  c1 = scrut0.fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_label___COSE_Format_values__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
  c2 = scrut0.snd;
  ________FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr__FStar_Pervasives_Native_option_COSE_Format_bstr
  c11 = c1.fst;
  FStar_Pervasives_Native_option__COSE_Format_bstr c21 = c1.snd;
  FStar_Pervasives_Native_option__COSE_Format_bstr c22 = c11.snd;
  COSE_Format_label_ugly c23 = c11.fst;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size0 = psize;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
    cbor_det_t c30 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    size_t len0 = cbor_det_size(c30, Pulse_Lib_Slice_len__uint8_t(out1));
    option__size_t scrut0;
    if (len0 > (size_t)0U)
      scrut0 =
        (
          (option__size_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = cbor_det_serialize(c30,
              Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out1),
              len0)
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
      Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1).snd;
      cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
      size_t len = cbor_det_size(c3, Pulse_Lib_Slice_len__uint8_t(out2));
      option__size_t scrut;
      if (len > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(c3,
                Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2),
                len)
            }
          );
      else
        scrut = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      size_t res2;
      if (scrut.tag == FStar_Pervasives_Native_None)
        res2 = (size_t)0U;
      else if (scrut.tag == FStar_Pervasives_Native_Some)
        res2 = scrut.v;
      else
        res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (res2 > (size_t)0U)
      {
        size_t size2 = size1 + res2;
        Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
    uint64_t count = pcount;
    if (count < 18446744073709551615ULL)
    {
      size_t size0 = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
        Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1).snd;
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
          Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
          size_t res2 = COSE_Format_serialize_bstr(c13, split__uint8_t(out, size1).snd);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
    if (c21.tag == FStar_Pervasives_Native_Some)
    {
      Pulse_Lib_Slice_slice__uint8_t c12 = c21.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
          size_t res2 = COSE_Format_serialize_bstr(c12, split__uint8_t(out, size1).snd);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
    else if (c21.tag == FStar_Pervasives_Native_None)
      ite3 = true;
    else
      ite3 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite3 = false;
  bool ite4;
  if (ite3)
    if (c2.tag == COSE_Format_Inl)
    {
      Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ i = c2.case_Inl;
      Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ buf = i;
      KRML_HOST_IGNORE(&buf);
      Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ pc = i;
      bool pres = true;
      bool cond;
      if (pres)
        cond = !(len___COSE_Format_label___COSE_Format_values_(pc) == (size_t)0U);
      else
        cond = false;
      while (cond)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ i1 = pc;
          K___COSE_Format_label_COSE_Format_values
          res = op_Array_Access___COSE_Format_label___COSE_Format_values_(i1, (size_t)0U);
          pc = split___COSE_Format_label___COSE_Format_values_(i1, (size_t)1U).snd;
          K___COSE_Format_label_COSE_Format_values scrut0 = res;
          COSE_Format_label ck = scrut0.fst;
          cbor_det_t cv = scrut0.snd;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
          size_t sz1 = COSE_Format_serialize_label(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            scrut0 = split__uint8_t(out1, sz1);
            Pulse_Lib_Slice_slice__uint8_t outl2 = scrut0.fst;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0.snd;
            size_t sz2 = COSE_Format_serialize_values(cv, out2);
            if (sz2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len0 = Pulse_Lib_Slice_len__uint8_t(outl2);
              size_t
              len2 =
                cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(outl2),
                  len0);
              option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
              if (len2 == (size_t)0U)
                scrut0 =
                  (
                    (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                scrut = split__uint8_t(outl2, len2);
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
                size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len1),
                        .snd = rem
                      }
                    }
                  );
              }
              if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t o1 = scrut0.v.fst;
                size_t len = Pulse_Lib_Slice_len__uint8_t(out2);
                size_t
                len0 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2),
                    len);
                option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
                if (len0 == (size_t)0U)
                  scrut0 =
                    (
                      (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut = split__uint8_t(out2, len0);
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
                  size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len1),
                          .snd = rem
                        }
                      }
                    );
                }
                if (scrut0.tag == FStar_Pervasives_Native_Some)
                  if
                  (COSE_Format_aux_env29_map_constraint_1(cbor_det_mk_map_entry(o1, scrut0.v.fst)))
                    pres = false;
                  else
                  {
                    size_t size1 = size0 + sz1;
                    size_t size2 = size1 + sz2;
                    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                    scrut = split__uint8_t(out, size2);
                    Pulse_Lib_Slice_slice__uint8_t
                    outl =
                      (
                        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                          .fst = scrut.fst,
                          .snd = scrut.snd
                        }
                      ).fst;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(outl);
                    if
                    (
                      !cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(outl),
                        aout_len,
                        size0,
                        size1)
                    )
                      pres = false;
                    else
                    {
                      pcount = count_;
                      psize = size2;
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
        bool ite;
        if (pres)
          ite = !(len___COSE_Format_label___COSE_Format_values_(pc) == (size_t)0U);
        else
          ite = false;
        cond = ite;
      }
      ite4 = pres;
    }
    else if (c2.tag == COSE_Format_Inr)
    {
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
      pc = c2.case_Inr;
      bool pres = true;
      bool cond0;
      if (pres)
      {
        CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
        c3 = pc;
        cbor_det_map_iterator_t pj = c3.cddl_map_iterator_contents;
        bool pres1 = true;
        bool cond;
        if (pres1)
          cond = !cbor_det_map_iterator_is_empty(pj);
        else
          cond = false;
        while (cond)
        {
          cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
          if (!!c3.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
            if (!c3.cddl_map_iterator_impl_validate_ex(elt))
              pres1 = !c3.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
          bool ite;
          if (pres1)
            ite = !cbor_det_map_iterator_is_empty(pj);
          else
            ite = false;
          cond = ite;
        }
        cond0 = !pres1;
      }
      else
        cond0 = false;
      while (cond0)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
          i = pc;
          cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
          cbor_det_map_entry_t phd = cbor_det_map_iterator_next(&pj);
          cbor_det_map_entry_t hd0 = phd;
          bool cond;
          if (!i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd0)))
            cond = true;
          else if (!i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0)))
            cond = true;
          else
            cond = i.cddl_map_iterator_impl_validate_ex(hd0);
          while (cond)
          {
            phd = cbor_det_map_iterator_next(&pj);
            cbor_det_map_entry_t hd = phd;
            bool ite;
            if (!i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd)))
              ite = true;
            else if (!i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd)))
              ite = true;
            else
              ite = i.cddl_map_iterator_impl_validate_ex(hd);
            cond = ite;
          }
          cbor_det_map_entry_t hd = phd;
          COSE_Format_label
          hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
          cbor_det_t hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
          pc =
            (
              (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values){
                .cddl_map_iterator_contents = pj,
                .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
                .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
                .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
                .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
                .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
              }
            );
          COSE_Format_label ck = hd_key_res;
          cbor_det_t cv = hd_value_res;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
          size_t sz1 = COSE_Format_serialize_label(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            scrut0 = split__uint8_t(out1, sz1);
            Pulse_Lib_Slice_slice__uint8_t outl2 = scrut0.fst;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0.snd;
            size_t sz2 = COSE_Format_serialize_values(cv, out2);
            if (sz2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len0 = Pulse_Lib_Slice_len__uint8_t(outl2);
              size_t
              len2 =
                cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(outl2),
                  len0);
              option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
              if (len2 == (size_t)0U)
                scrut0 =
                  (
                    (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                scrut = split__uint8_t(outl2, len2);
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
                size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len1),
                        .snd = rem
                      }
                    }
                  );
              }
              if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t o1 = scrut0.v.fst;
                size_t len = Pulse_Lib_Slice_len__uint8_t(out2);
                size_t
                len0 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2),
                    len);
                option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
                if (len0 == (size_t)0U)
                  scrut0 =
                    (
                      (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut = split__uint8_t(out2, len0);
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
                  size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len1),
                          .snd = rem
                        }
                      }
                    );
                }
                if (scrut0.tag == FStar_Pervasives_Native_Some)
                  if
                  (COSE_Format_aux_env29_map_constraint_1(cbor_det_mk_map_entry(o1, scrut0.v.fst)))
                    pres = false;
                  else
                  {
                    size_t size1 = size0 + sz1;
                    size_t size2 = size1 + sz2;
                    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                    scrut = split__uint8_t(out, size2);
                    Pulse_Lib_Slice_slice__uint8_t
                    outl =
                      (
                        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                          .fst = scrut.fst,
                          .snd = scrut.snd
                        }
                      ).fst;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(outl);
                    if
                    (
                      !cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(outl),
                        aout_len,
                        size0,
                        size1)
                    )
                      pres = false;
                    else
                    {
                      pcount = count_;
                      psize = size2;
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
        bool ite;
        if (pres)
        {
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
          c3 = pc;
          cbor_det_map_iterator_t pj = c3.cddl_map_iterator_contents;
          bool pres1 = true;
          bool cond;
          if (pres1)
            cond = !cbor_det_map_iterator_is_empty(pj);
          else
            cond = false;
          while (cond)
          {
            cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
            if (!!c3.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
              if (!c3.cddl_map_iterator_impl_validate_ex(elt))
                pres1 = !c3.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
            bool ite;
            if (pres1)
              ite = !cbor_det_map_iterator_is_empty(pj);
            else
              ite = false;
            cond = ite;
          }
          ite = !pres1;
        }
        else
          ite = false;
        cond0 = ite;
      }
      ite4 = pres;
    }
    else
      ite4 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite4 = false;
  if (ite4)
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

FStar_Pervasives_Native_option___COSE_Format_cose_key_okp___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_key_okp(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_key_okp___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_key_okp(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_key_okp___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_key_okp(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_key_okp___Pulse_Lib_Slice_slice_uint8_t_){
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
COSE_Format_is_empty_iterate_map_label_and_values(
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
  i
)
{
  cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
  bool pres = true;
  bool cond;
  if (pres)
    cond = !cbor_det_map_iterator_is_empty(pj);
  else
    cond = false;
  while (cond)
  {
    cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
    if (!!i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
      if (!i.cddl_map_iterator_impl_validate_ex(elt))
        pres = !i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
    bool ite;
    if (pres)
      ite = !cbor_det_map_iterator_is_empty(pj);
    else
      ite = false;
    cond = ite;
  }
  return pres;
}

K___COSE_Format_label_COSE_Format_values
COSE_Format_next_iterate_map_label_and_values(
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
  *pi
)
{
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
  i = *pi;
  cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
  cbor_det_map_entry_t phd = cbor_det_map_iterator_next(&pj);
  cbor_det_map_entry_t hd0 = phd;
  bool cond;
  if (!i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd0)))
    cond = true;
  else if (!i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0)))
    cond = true;
  else
    cond = i.cddl_map_iterator_impl_validate_ex(hd0);
  while (cond)
  {
    phd = cbor_det_map_iterator_next(&pj);
    cbor_det_map_entry_t hd = phd;
    bool ite;
    if (!i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd)))
      ite = true;
    else if (!i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd)))
      ite = true;
    else
      ite = i.cddl_map_iterator_impl_validate_ex(hd);
    cond = ite;
  }
  cbor_det_map_entry_t hd = phd;
  COSE_Format_label hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
  cbor_det_t hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
  *pi =
    (
      (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values){
        .cddl_map_iterator_contents = pj,
        .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
        .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
        .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
        .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
        .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
      }
    );
  return ((K___COSE_Format_label_COSE_Format_values){ .fst = hd_key_res, .snd = hd_value_res });
}

bool COSE_Format_validate_cose_key(cbor_det_t c)
{
  return COSE_Format_validate_cose_key_okp(c);
}

bool COSE_Format_uu___is_Mkcose_key0(COSE_Format_cose_key_okp projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_cose_key_okp cose_key_right(COSE_Format_cose_key_okp x1)
{
  return x1;
}

static COSE_Format_cose_key_okp cose_key_left(COSE_Format_cose_key_okp x3)
{
  return x3;
}

/**
Parser for cose_key
*/
COSE_Format_cose_key_okp COSE_Format_parse_cose_key(cbor_det_t c)
{
  return cose_key_right(COSE_Format_parse_cose_key_okp(c));
}

/**
Serializer for cose_key
*/
size_t
COSE_Format_serialize_cose_key(COSE_Format_cose_key_okp c, Pulse_Lib_Slice_slice__uint8_t out)
{
  return COSE_Format_serialize_cose_key_okp(cose_key_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_cose_key___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_key(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_key___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_key(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_key___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_key(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_key___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_aux_env32_validate_1(cbor_det_array_iterator_t *pi)
{
  if (cbor_det_array_iterator_is_empty(*pi))
    return false;
  else
    return COSE_Format_validate_label(cbor_det_array_iterator_next(pi));
}

bool COSE_Format_uu___is_Mkaux_env32_type_10(COSE_Format_label projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_label aux_env32_type_1_right(COSE_Format_label x1)
{
  return x1;
}

static COSE_Format_label aux_env32_type_1_left(COSE_Format_label x3)
{
  return x3;
}

/**
Parser for aux_env32_type_1
*/
COSE_Format_label COSE_Format_aux_env32_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t buf = c;
  return aux_env32_type_1_right(COSE_Format_parse_label(cbor_det_array_iterator_next(&buf)));
}

/**
Serializer for aux_env32_type_1
*/
bool
COSE_Format_aux_env32_serialize_1(
  COSE_Format_label c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  COSE_Format_label c_ = aux_env32_type_1_left(c);
  uint64_t count = *out_count;
  if (count < 18446744073709551615ULL)
  {
    size_t size = *out_size;
    size_t size1 = COSE_Format_serialize_label(c_, split__uint8_t(out, size).snd);
    if (size1 == (size_t)0U)
      return false;
    else
    {
      *out_count = count + 1ULL;
      *out_size = size + size1;
      return true;
    }
  }
  else
    return false;
}

bool COSE_Format_aux_env32_map_constraint_2(cbor_det_map_entry_t x)
{
  cbor_det_t k0 = cbor_det_map_entry_key(x);
  bool ite0;
  if (cbor_det_major_type(k0) == CBOR_MAJOR_TYPE_UINT64)
    ite0 = cbor_det_read_uint64(k0) == 1ULL;
  else
    ite0 = false;
  bool ite1;
  if (ite0)
  {
    cbor_det_t v1 = cbor_det_map_entry_value(x);
    if (COSE_Format_validate_int(v1))
      ite1 = true;
    else
      ite1 = COSE_Format_validate_tstr(v1);
  }
  else
    ite1 = false;
  bool ite2;
  if (ite1)
    ite2 = true;
  else
  {
    cbor_det_t k = cbor_det_map_entry_key(x);
    bool ite0;
    if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
      ite0 = cbor_det_read_uint64(k) == 2ULL;
    else
      ite0 = false;
    if (ite0)
    {
      cbor_det_t v1 = cbor_det_map_entry_value(x);
      if (cbor_det_major_type(v1) == CBOR_MAJOR_TYPE_ARRAY)
      {
        cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(v1);
        bool ite0;
        if (cbor_det_array_iterator_is_empty(pi))
          ite0 = false;
        else
          ite0 = COSE_Format_validate_label(cbor_det_array_iterator_next(&pi));
        bool ite1;
        if (ite0)
        {
          bool pcont = true;
          while (pcont)
          {
            cbor_det_array_iterator_t i1 = pi;
            bool ite;
            if (cbor_det_array_iterator_is_empty(pi))
              ite = false;
            else
              ite = COSE_Format_validate_label(cbor_det_array_iterator_next(&pi));
            if (!ite)
            {
              pi = i1;
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
    cbor_det_t k = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k) == 3ULL;
    else
      ite = false;
    if (ite)
    {
      cbor_det_t v1 = cbor_det_map_entry_value(x);
      if (COSE_Format_validate_tstr(v1))
        ite3 = true;
      else
        ite3 = COSE_Format_validate_int(v1);
    }
    else
      ite3 = false;
  }
  bool ite4;
  if (ite3)
    ite4 = true;
  else
  {
    cbor_det_t k = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k) == 4ULL;
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
    cbor_det_t k = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k) == 5ULL;
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
    cbor_det_t k = cbor_det_map_entry_key(x);
    bool ite;
    if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
      ite = cbor_det_read_uint64(k) == 6ULL;
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
    uint64_t i00 = remaining;
    cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest0 = c10;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
    if (cbor_det_map_get(c, c10, &dest0))
      scrut0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest0
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
        remaining = remaining - 1ULL;
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
          remaining = i00;
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
          uint64_t i0 = remaining;
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
          cbor_det_t dest = c1;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c1, &dest))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest
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
                ite0 = COSE_Format_validate_label(cbor_det_array_iterator_next(&pi));
              bool ite2;
              if (ite0)
              {
                bool pcont = true;
                while (pcont)
                {
                  cbor_det_array_iterator_t i1 = pi;
                  bool ite;
                  if (cbor_det_array_iterator_is_empty(pi))
                    ite = false;
                  else
                    ite = COSE_Format_validate_label(cbor_det_array_iterator_next(&pi));
                  if (!ite)
                  {
                    pi = i1;
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
              remaining = remaining - 1ULL;
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
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
          cbor_det_t dest = c1;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c1, &dest))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest
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
              remaining = remaining - 1ULL;
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
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
          cbor_det_t dest = c1;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c1, &dest))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest
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
              remaining = remaining - 1ULL;
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
    impl_map_group_result sw4;
    switch (sw3)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
          cbor_det_t dest0 = c10;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
          if (cbor_det_map_get(c, c10, &dest0))
            scrut0 =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest0
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
              remaining = remaining - 1ULL;
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
                uint64_t i01 = remaining;
                cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                cbor_det_t dest = c1;
                option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
                if (cbor_det_map_get(c, c1, &dest))
                  scrut =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = dest
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
                    remaining = remaining - 1ULL;
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
                      remaining = i01;
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
                remaining = i0;
                uint64_t i01 = remaining;
                cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                cbor_det_t dest0 = c10;
                option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
                if (cbor_det_map_get(c, c10, &dest0))
                  scrut0 =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = dest0
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
                    remaining = remaining - 1ULL;
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
                      cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
                      cbor_det_t dest = c1;
                      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
                      if (cbor_det_map_get(c, c1, &dest))
                        scrut =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_Some,
                              .v = dest
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
                          remaining = remaining - 1ULL;
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
                      remaining = i01;
                      uint64_t i02 = remaining;
                      cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                      cbor_det_t dest0 = c10;
                      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
                      if (cbor_det_map_get(c, c10, &dest0))
                        scrut0 =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_Some,
                              .v = dest0
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
                          remaining = remaining - 1ULL;
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
                            remaining = i02;
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
                            uint64_t i02 = remaining;
                            cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
                            cbor_det_t dest = c1;
                            option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
                            if (cbor_det_map_get(c, c1, &dest))
                              scrut =
                                (
                                  (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                                    .tag = FStar_Pervasives_Native_Some,
                                    .v = dest
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
                                remaining = remaining - 1ULL;
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
                                  remaining = i02;
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
            if (COSE_Format_validate_label(cbor_det_map_entry_key(chd)))
              ite0 = COSE_Format_validate_values(cbor_det_map_entry_value(chd));
            else
              ite0 = false;
            bool ite1;
            if (ite0)
            {
              cbor_det_t k0 = cbor_det_map_entry_key(chd);
              bool ite0;
              if (cbor_det_major_type(k0) == CBOR_MAJOR_TYPE_UINT64)
                ite0 = cbor_det_read_uint64(k0) == 1ULL;
              else
                ite0 = false;
              bool ite2;
              if (ite0)
              {
                cbor_det_t v1 = cbor_det_map_entry_value(chd);
                if (COSE_Format_validate_int(v1))
                  ite2 = true;
                else
                  ite2 = COSE_Format_validate_tstr(v1);
              }
              else
                ite2 = false;
              bool ite3;
              if (ite2)
                ite3 = true;
              else
              {
                cbor_det_t k = cbor_det_map_entry_key(chd);
                bool ite0;
                if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                  ite0 = cbor_det_read_uint64(k) == 2ULL;
                else
                  ite0 = false;
                if (ite0)
                {
                  cbor_det_t v1 = cbor_det_map_entry_value(chd);
                  if (cbor_det_major_type(v1) == CBOR_MAJOR_TYPE_ARRAY)
                  {
                    cbor_det_array_iterator_t pi = cbor_det_array_iterator_start(v1);
                    bool ite0;
                    if (cbor_det_array_iterator_is_empty(pi))
                      ite0 = false;
                    else
                      ite0 = COSE_Format_validate_label(cbor_det_array_iterator_next(&pi));
                    bool ite1;
                    if (ite0)
                    {
                      bool pcont = true;
                      while (pcont)
                      {
                        cbor_det_array_iterator_t i1 = pi;
                        bool ite;
                        if (cbor_det_array_iterator_is_empty(pi))
                          ite = false;
                        else
                          ite = COSE_Format_validate_label(cbor_det_array_iterator_next(&pi));
                        if (!ite)
                        {
                          pi = i1;
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
                cbor_det_t k = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k) == 3ULL;
                else
                  ite = false;
                if (ite)
                {
                  cbor_det_t v1 = cbor_det_map_entry_value(chd);
                  if (COSE_Format_validate_tstr(v1))
                    ite4 = true;
                  else
                    ite4 = COSE_Format_validate_int(v1);
                }
                else
                  ite4 = false;
              }
              bool ite5;
              if (ite4)
                ite5 = true;
              else
              {
                cbor_det_t k = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k) == 4ULL;
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
                cbor_det_t k = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k) == 5ULL;
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
                cbor_det_t k = cbor_det_map_entry_key(chd);
                bool ite;
                if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                  ite = cbor_det_read_uint64(k) == 6ULL;
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
              remaining = remaining - 1ULL;
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

typedef struct
__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1_s
{
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr
  fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
  snd;
}
__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1;

typedef struct
___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int_s
{
  __FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
  fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int
  snd;
}
___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int;

typedef struct
____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int__FStar_Pervasives_Native_option_COSE_Format_bstr_s
{
  ___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int
  fst;
  FStar_Pervasives_Native_option__COSE_Format_bstr snd;
}
____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int__FStar_Pervasives_Native_option_COSE_Format_bstr;

typedef struct
_____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__s
{
  ____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int__FStar_Pervasives_Native_option_COSE_Format_bstr
  fst;
  FStar_Pervasives_either___COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_
  snd;
}
_____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_;

typedef struct header_map_ugly_s
{
  _____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_
  fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_label___COSE_Format_values__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
  snd;
}
header_map_ugly;

bool COSE_Format_uu___is_Mkheader_map0(COSE_Format_header_map projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_header_map header_map_right(header_map_ugly x6)
{
  return
    (
      (COSE_Format_header_map){
        .intkey1 = x6.fst.fst.fst.fst.fst,
        .intkey2 = x6.fst.fst.fst.fst.snd,
        .intkey3 = x6.fst.fst.fst.snd,
        .intkey4 = x6.fst.fst.snd,
        ._x0 = x6.fst.snd,
        ._x1 = x6.snd
      }
    );
}

static header_map_ugly header_map_left(COSE_Format_header_map x13)
{
  return
    (
      (header_map_ugly){
        .fst = {
          .fst = {
            .fst = { .fst = { .fst = x13.intkey1, .snd = x13.intkey2 }, .snd = x13.intkey3 },
            .snd = x13.intkey4
          },
          .snd = x13._x0
        },
        .snd = x13._x1
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
  cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
  cbor_det_t dest0 = c10;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
  if (cbor_det_map_get(c, c10, &dest0))
    scrut0 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest0
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
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr
  w1;
  if (uu___is_MGOK(ite0))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest = c1;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c1, &dest))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    COSE_Format_label_ugly ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      if (COSE_Format_validate_int(w))
        ite =
          (
            (COSE_Format_label_ugly){
              .tag = COSE_Format_Inl,
              { .case_Inl = COSE_Format_parse_int(w) }
            }
          );
      else
        ite =
          (
            (COSE_Format_label_ugly){
              .tag = COSE_Format_Inr,
              { .case_Inr = COSE_Format_parse_tstr(w) }
            }
          );
    }
    else
      ite =
        KRML_EABORT(COSE_Format_label_ugly,
          "unreachable (pattern matches are exhaustive in F*)");
    w1 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    w1 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr){
          .tag = FStar_Pervasives_Native_None
        }
      );
  uint64_t buf1 = 0ULL;
  KRML_HOST_IGNORE(&buf1);
  cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
  cbor_det_t dest1 = c11;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
  if (cbor_det_map_get(c, c11, &dest1))
    scrut1 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest1
        }
      );
  else
    scrut1 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite1;
  if (scrut1.tag == FStar_Pervasives_Native_None)
    ite1 = MGFail;
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
        ite1 = COSE_Format_validate_label(cbor_det_array_iterator_next(&pi));
      bool ite2;
      if (ite1)
      {
        bool pcont = true;
        while (pcont)
        {
          cbor_det_array_iterator_t i1 = pi;
          bool ite;
          if (cbor_det_array_iterator_is_empty(pi))
            ite = false;
          else
            ite = COSE_Format_validate_label(cbor_det_array_iterator_next(&pi));
          if (!ite)
          {
            pi = i1;
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
      ite1 = MGOK;
    else
      ite1 = MGFail;
  }
  else
    ite1 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
  ite2;
  if (uu___is_MGOK(ite1))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
    cbor_det_t dest = c1;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c1, &dest))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
    ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
      ite =
        (
          (FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1){
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_array_iterator_contents = cbor_det_array_iterator_start(scrut.v),
                .cddl_array_iterator_impl_validate = COSE_Format_aux_env32_validate_1,
                .cddl_array_iterator_impl_parse = COSE_Format_aux_env32_parse_1
              }
            }
          }
        );
    else
      ite =
        KRML_EABORT(FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1,
          "unreachable (pattern matches are exhaustive in F*)");
    ite2 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite2 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1){
          .tag = FStar_Pervasives_Native_None
        }
      );
  __FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
  w10 = { .fst = w1, .snd = ite2 };
  uint64_t buf2 = 0ULL;
  KRML_HOST_IGNORE(&buf2);
  cbor_det_t c12 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
  cbor_det_t dest2 = c12;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut2;
  if (cbor_det_map_get(c, c12, &dest2))
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
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int
  ite4;
  if (uu___is_MGOK(ite3))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
    cbor_det_t dest = c1;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c1, &dest))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest
          }
        );
    else
      scrut = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    FStar_Pervasives_either__COSE_Format_tstr_COSE_Format_evercddl_int ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      if (COSE_Format_validate_tstr(w))
        ite =
          (
            (FStar_Pervasives_either__COSE_Format_tstr_COSE_Format_evercddl_int){
              .tag = COSE_Format_Inl,
              { .case_Inl = COSE_Format_parse_tstr(w) }
            }
          );
      else
        ite =
          (
            (FStar_Pervasives_either__COSE_Format_tstr_COSE_Format_evercddl_int){
              .tag = COSE_Format_Inr,
              { .case_Inr = COSE_Format_parse_int(w) }
            }
          );
    }
    else
      ite =
        KRML_EABORT(FStar_Pervasives_either__COSE_Format_tstr_COSE_Format_evercddl_int,
          "unreachable (pattern matches are exhaustive in F*)");
    ite4 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite4 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int){
          .tag = FStar_Pervasives_Native_None
        }
      );
  ___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int
  w12 = { .fst = w10, .snd = ite4 };
  uint64_t buf3 = 0ULL;
  KRML_HOST_IGNORE(&buf3);
  cbor_det_t c13 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
  cbor_det_t dest3 = c13;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut3;
  if (cbor_det_map_get(c, c13, &dest3))
    scrut3 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest3
        }
      );
  else
    scrut3 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite5;
  if (scrut3.tag == FStar_Pervasives_Native_None)
    ite5 = MGFail;
  else if (scrut3.tag == FStar_Pervasives_Native_Some)
    if (COSE_Format_validate_bstr(scrut3.v))
      ite5 = MGOK;
    else
      ite5 = MGFail;
  else
    ite5 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__COSE_Format_bstr ite6;
  if (uu___is_MGOK(ite5))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
    cbor_det_t dest = c1;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
    if (cbor_det_map_get(c, c1, &dest))
      scrut =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest
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
    ite6 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_bstr){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite6 =
      ((FStar_Pervasives_Native_option__COSE_Format_bstr){ .tag = FStar_Pervasives_Native_None });
  ____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int__FStar_Pervasives_Native_option_COSE_Format_bstr
  w13 = { .fst = w12, .snd = ite6 };
  uint64_t dummy = 0ULL;
  cbor_det_t c14 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
  cbor_det_t dest4 = c14;
  option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut4;
  if (cbor_det_map_get(c, c14, &dest4))
    scrut4 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest4
        }
      );
  else
    scrut4 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result ite7;
  if (scrut4.tag == FStar_Pervasives_Native_None)
    ite7 = MGFail;
  else if (scrut4.tag == FStar_Pervasives_Native_Some)
    if (COSE_Format_validate_bstr(scrut4.v))
      ite7 = MGOK;
    else
      ite7 = MGFail;
  else
    ite7 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  impl_map_group_result sw0;
  switch (ite7)
  {
    case MGOK:
      {
        uint64_t i0 = dummy;
        cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
        cbor_det_t dest = c1;
        option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
        if (cbor_det_map_get(c, c1, &dest))
          scrut =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = dest
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
  FStar_Pervasives_either___COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_
  ite8;
  if (uu___is_MGOK(sw0))
  {
    cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
    cbor_det_t dest0 = c10;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
    if (cbor_det_map_get(c, c10, &dest0))
      scrut0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest0
          }
        );
    else
      scrut0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    Pulse_Lib_Slice_slice__uint8_t w11;
    if (scrut0.tag == FStar_Pervasives_Native_Some)
      w11 = COSE_Format_parse_bstr(scrut0.v);
    else
      w11 =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    uint64_t buf = 0ULL;
    KRML_HOST_IGNORE(&buf);
    cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
    cbor_det_t dest1 = c11;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
    if (cbor_det_map_get(c, c11, &dest1))
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
      if (COSE_Format_validate_everparsenomatch(scrut1.v))
        ite0 = MGOK;
      else
        ite0 = MGCutFail;
    else
      ite0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    FStar_Pervasives_Native_option__COSE_Format_everparsenomatch ite1;
    if (uu___is_MGOK(ite0))
    {
      cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
      cbor_det_t dest = c1;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
      if (cbor_det_map_get(c, c1, &dest))
        scrut =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest
            }
          );
      else
        scrut =
          ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      COSE_Format_everparsenomatch ite;
      if (scrut.tag == FStar_Pervasives_Native_Some)
        ite = COSE_Format_parse_everparsenomatch(scrut.v);
      else
        ite =
          KRML_EABORT(COSE_Format_everparsenomatch,
            "unreachable (pattern matches are exhaustive in F*)");
      ite1 =
        (
          (FStar_Pervasives_Native_option__COSE_Format_everparsenomatch){
            .tag = FStar_Pervasives_Native_Some,
            .v = ite
          }
        );
    }
    else
      ite1 =
        (
          (FStar_Pervasives_Native_option__COSE_Format_everparsenomatch){
            .tag = FStar_Pervasives_Native_None
          }
        );
    ite8 =
      (
        (FStar_Pervasives_either___COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_){
          .tag = COSE_Format_Inl,
          { .case_Inl = { .fst = w11, .snd = ite1 } }
        }
      );
  }
  else
  {
    uint64_t dummy1 = 0ULL;
    cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
    cbor_det_t dest0 = c10;
    option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
    if (cbor_det_map_get(c, c10, &dest0))
      scrut0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = dest0
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
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
          cbor_det_t dest = c1;
          option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
          if (cbor_det_map_get(c, c1, &dest))
            scrut =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = dest
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
    FStar_Pervasives_either___COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_
    ite1;
    if (uu___is_MGOK(sw))
    {
      cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
      cbor_det_t dest0 = c10;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
      if (cbor_det_map_get(c, c10, &dest0))
        scrut0 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest0
            }
          );
      else
        scrut0 =
          ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      Pulse_Lib_Slice_slice__uint8_t w11;
      if (scrut0.tag == FStar_Pervasives_Native_Some)
        w11 = COSE_Format_parse_bstr(scrut0.v);
      else
        w11 =
          KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
            "unreachable (pattern matches are exhaustive in F*)");
      uint64_t buf = 0ULL;
      KRML_HOST_IGNORE(&buf);
      cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
      cbor_det_t dest1 = c11;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
      if (cbor_det_map_get(c, c11, &dest1))
        scrut1 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest1
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
      FStar_Pervasives_Native_option__COSE_Format_everparsenomatch ite2;
      if (uu___is_MGOK(ite0))
      {
        cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        cbor_det_t dest = c1;
        option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
        if (cbor_det_map_get(c, c1, &dest))
          scrut =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = dest
              }
            );
        else
          scrut =
            ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        COSE_Format_everparsenomatch ite;
        if (scrut.tag == FStar_Pervasives_Native_Some)
          ite = COSE_Format_parse_everparsenomatch(scrut.v);
        else
          ite =
            KRML_EABORT(COSE_Format_everparsenomatch,
              "unreachable (pattern matches are exhaustive in F*)");
        ite2 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_everparsenomatch){
              .tag = FStar_Pervasives_Native_Some,
              .v = ite
            }
          );
      }
      else
        ite2 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_everparsenomatch){
              .tag = FStar_Pervasives_Native_None
            }
          );
      ite1 =
        (
          (FStar_Pervasives_either___COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_){
            .tag = COSE_Format_Inl,
            { .case_Inl = { .fst = w11, .snd = ite2 } }
          }
        );
    }
    else
    {
      uint64_t buf0 = 0ULL;
      KRML_HOST_IGNORE(&buf0);
      cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
      cbor_det_t dest0 = c10;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut0;
      if (cbor_det_map_get(c, c10, &dest0))
        scrut0 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest0
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
      FStar_Pervasives_Native_option__COSE_Format_everparsenomatch w11;
      if (uu___is_MGOK(ite0))
      {
        cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
        cbor_det_t dest = c1;
        option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
        if (cbor_det_map_get(c, c1, &dest))
          scrut =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = dest
              }
            );
        else
          scrut =
            ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        COSE_Format_everparsenomatch ite;
        if (scrut.tag == FStar_Pervasives_Native_Some)
          ite = COSE_Format_parse_everparsenomatch(scrut.v);
        else
          ite =
            KRML_EABORT(COSE_Format_everparsenomatch,
              "unreachable (pattern matches are exhaustive in F*)");
        w11 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_everparsenomatch){
              .tag = FStar_Pervasives_Native_Some,
              .v = ite
            }
          );
      }
      else
        w11 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_everparsenomatch){
              .tag = FStar_Pervasives_Native_None
            }
          );
      uint64_t buf = 0ULL;
      KRML_HOST_IGNORE(&buf);
      cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
      cbor_det_t dest1 = c11;
      option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut1;
      if (cbor_det_map_get(c, c11, &dest1))
        scrut1 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = dest1
            }
          );
      else
        scrut1 =
          ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      impl_map_group_result ite2;
      if (scrut1.tag == FStar_Pervasives_Native_None)
        ite2 = MGFail;
      else if (scrut1.tag == FStar_Pervasives_Native_Some)
        if (COSE_Format_validate_everparsenomatch(scrut1.v))
          ite2 = MGOK;
        else
          ite2 = MGCutFail;
      else
        ite2 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      FStar_Pervasives_Native_option__COSE_Format_everparsenomatch ite3;
      if (uu___is_MGOK(ite2))
      {
        cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        cbor_det_t dest = c1;
        option__CBOR_Pulse_API_Det_Type_cbor_det_t scrut;
        if (cbor_det_map_get(c, c1, &dest))
          scrut =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = dest
              }
            );
        else
          scrut =
            ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        COSE_Format_everparsenomatch ite;
        if (scrut.tag == FStar_Pervasives_Native_Some)
          ite = COSE_Format_parse_everparsenomatch(scrut.v);
        else
          ite =
            KRML_EABORT(COSE_Format_everparsenomatch,
              "unreachable (pattern matches are exhaustive in F*)");
        ite3 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_everparsenomatch){
              .tag = FStar_Pervasives_Native_Some,
              .v = ite
            }
          );
      }
      else
        ite3 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_everparsenomatch){
              .tag = FStar_Pervasives_Native_None
            }
          );
      ite1 =
        (
          (FStar_Pervasives_either___COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_){
            .tag = COSE_Format_Inr,
            { .case_Inr = { .fst = w11, .snd = ite3 } }
          }
        );
    }
    ite8 =
      (
        (FStar_Pervasives_either___COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_){
          .tag = COSE_Format_Inr,
          { .case_Inr = ite1 }
        }
      );
  }
  _____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_
  w11 = { .fst = w13, .snd = ite8 };
  return
    header_map_right((
        (header_map_ugly){
          .fst = w11,
          .snd = {
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_map_iterator_contents = cbor_det_map_iterator_start(c),
                .cddl_map_iterator_impl_validate1 = COSE_Format_validate_label,
                .cddl_map_iterator_impl_parse1 = COSE_Format_parse_label,
                .cddl_map_iterator_impl_validate_ex = COSE_Format_aux_env32_map_constraint_2,
                .cddl_map_iterator_impl_validate2 = COSE_Format_validate_values,
                .cddl_map_iterator_impl_parse2 = COSE_Format_parse_values
              }
            }
          }
        }
      ));
}

static size_t
len__COSE_Format_aux_env32_type_1(Pulse_Lib_Slice_slice__COSE_Format_aux_env32_type_1 s)
{
  return s.len;
}

static COSE_Format_label
op_Array_Access__COSE_Format_aux_env32_type_1(
  Pulse_Lib_Slice_slice__COSE_Format_aux_env32_type_1 a,
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
  header_map_ugly scrut0 = header_map_left(c);
  _____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int____FStar_Pervasives_Native_option_COSE_Format_bstr__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_
  c1 = scrut0.fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_label___COSE_Format_values__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
  c2 = scrut0.snd;
  ____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int__FStar_Pervasives_Native_option_COSE_Format_bstr
  c11 = c1.fst;
  FStar_Pervasives_either___COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch__FStar_Pervasives_either__COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_
  c21 = c1.snd;
  ___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int
  c120 = c11.fst;
  FStar_Pervasives_Native_option__COSE_Format_bstr c220 = c11.snd;
  __FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
  c130 = c120.fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_tstr_COSE_Format_evercddl_int
  c230 = c120.snd;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr
  c140 = c130.fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
  c240 = c130.snd;
  bool ite0;
  if (c140.tag == FStar_Pervasives_Native_Some)
  {
    COSE_Format_label_ugly c15 = c140.v;
    uint64_t count = pcount;
    if (count < 18446744073709551615ULL)
    {
      size_t size0 = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
        Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1).snd;
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
          Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
      FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
      c15 = c240.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
          Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1).snd;
          uint64_t pcount1 = 0ULL;
          size_t psize1 = (size_t)0U;
          bool ite;
          if (c15.tag == COSE_Format_Inl)
          {
            Pulse_Lib_Slice_slice__COSE_Format_aux_env32_type_1 c16 = c15.case_Inl;
            if (len__COSE_Format_aux_env32_type_1(c16) == (size_t)0U)
              ite = false;
            else
            {
              bool pres = true;
              size_t pi = (size_t)0U;
              size_t slen = len__COSE_Format_aux_env32_type_1(c16);
              bool cond;
              if (pres)
                cond = pi < slen;
              else
                cond = false;
              while (cond)
              {
                size_t i = pi;
                if
                (
                  COSE_Format_aux_env32_serialize_1(op_Array_Access__COSE_Format_aux_env32_type_1(c16,
                      i),
                    out2,
                    &pcount1,
                    &psize1)
                )
                  pi = i + (size_t)1U;
                else
                  pres = false;
                bool ite;
                if (pres)
                  ite = pi < slen;
                else
                  ite = false;
                cond = ite;
              }
              ite = pres;
            }
          }
          else if (c15.tag == COSE_Format_Inr)
          {
            CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
            c25 = c15.case_Inr;
            if (cbor_det_array_iterator_is_empty(c25.cddl_array_iterator_contents))
              ite = false;
            else
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
              pc = c25;
              bool pres = true;
              bool cond;
              if (pres)
                cond = !cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
              else
                cond = false;
              while (cond)
              {
                CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
                i = pc;
                uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
                cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
                KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
                cbor_det_array_iterator_t ji = pj;
                uint64_t len1 = cbor_det_array_iterator_length(ji);
                pc =
                  (
                    (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1){
                      .cddl_array_iterator_contents = ji,
                      .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
                      .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
                    }
                  );
                if
                (
                  !COSE_Format_aux_env32_serialize_1(i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
                        len0 - len1)),
                    out2,
                    &pcount1,
                    &psize1)
                )
                  pres = false;
                bool ite;
                if (pres)
                  ite = !cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
                else
                  ite = false;
                cond = ite;
              }
              ite = pres;
            }
          }
          else
            ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          size_t res2;
          if (ite)
          {
            size_t size = psize1;
            uint64_t count1 = pcount1;
            size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out2);
            res2 =
              cbor_det_serialize_array_to_array(count1,
                Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2),
                aout_len,
                size);
          }
          else
            res2 = (size_t)0U;
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
      FStar_Pervasives_either__COSE_Format_tstr_COSE_Format_evercddl_int c14 = c230.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
          Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1).snd;
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
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
          size_t res2 = COSE_Format_serialize_bstr(c13, split__uint8_t(out, size1).snd);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
    if (c21.tag == COSE_Format_Inl)
    {
      K___COSE_Format_bstr_FStar_Pervasives_Native_option_COSE_Format_everparsenomatch
      c12 = c21.case_Inl;
      Pulse_Lib_Slice_slice__uint8_t c13 = c12.fst;
      FStar_Pervasives_Native_option__COSE_Format_everparsenomatch c22 = c12.snd;
      uint64_t count0 = pcount;
      bool ite;
      if (count0 < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
          size_t res2 = COSE_Format_serialize_bstr(c13, split__uint8_t(out, size1).snd);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
        if (c22.tag == FStar_Pervasives_Native_Some)
        {
          COSE_Format_everparsenomatch c14 = c22.v;
          uint64_t count = pcount;
          if (count < 18446744073709551615ULL)
          {
            size_t size0 = psize;
            Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
              res2 = COSE_Format_serialize_everparsenomatch(c14, split__uint8_t(out, size1).snd);
              if (res2 > (size_t)0U)
              {
                size_t size2 = size1 + res2;
                Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
        else if (c22.tag == FStar_Pervasives_Native_None)
          ite4 = true;
        else
          ite4 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
      else
        ite4 = false;
    }
    else if (c21.tag == COSE_Format_Inr)
    {
      FStar_Pervasives_either___COSE_Format_bstr___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_
      c22 = c21.case_Inr;
      if (c22.tag == COSE_Format_Inl)
      {
        K___COSE_Format_bstr_FStar_Pervasives_Native_option_COSE_Format_everparsenomatch
        c12 = c22.case_Inl;
        Pulse_Lib_Slice_slice__uint8_t c13 = c12.fst;
        FStar_Pervasives_Native_option__COSE_Format_everparsenomatch c23 = c12.snd;
        uint64_t count0 = pcount;
        bool ite;
        if (count0 < 18446744073709551615ULL)
        {
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
            size_t res2 = COSE_Format_serialize_bstr(c13, split__uint8_t(out, size1).snd);
            if (res2 > (size_t)0U)
            {
              size_t size2 = size1 + res2;
              Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
          if (c23.tag == FStar_Pervasives_Native_Some)
          {
            COSE_Format_everparsenomatch c14 = c23.v;
            uint64_t count = pcount;
            if (count < 18446744073709551615ULL)
            {
              size_t size0 = psize;
              Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
                res12 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
              if (res12 > (size_t)0U)
              {
                size_t size1 = size0 + res12;
                size_t
                res2 = COSE_Format_serialize_everparsenomatch(c14, split__uint8_t(out, size1).snd);
                if (res2 > (size_t)0U)
                {
                  size_t size2 = size1 + res2;
                  Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
          else if (c23.tag == FStar_Pervasives_Native_None)
            ite4 = true;
          else
            ite4 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
        else
          ite4 = false;
      }
      else if (c22.tag == COSE_Format_Inr)
      {
        K___FStar_Pervasives_Native_option_COSE_Format_everparsenomatch_FStar_Pervasives_Native_option_COSE_Format_everparsenomatch
        c23 = c22.case_Inr;
        FStar_Pervasives_Native_option__COSE_Format_everparsenomatch c12 = c23.fst;
        FStar_Pervasives_Native_option__COSE_Format_everparsenomatch c24 = c23.snd;
        bool ite;
        if (c12.tag == FStar_Pervasives_Native_Some)
        {
          COSE_Format_everparsenomatch c13 = c12.v;
          uint64_t count = pcount;
          if (count < 18446744073709551615ULL)
          {
            size_t size0 = psize;
            Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
              res2 = COSE_Format_serialize_everparsenomatch(c13, split__uint8_t(out, size1).snd);
              if (res2 > (size_t)0U)
              {
                size_t size2 = size1 + res2;
                Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
        }
        else if (c12.tag == FStar_Pervasives_Native_None)
          ite = true;
        else
          ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
        if (ite)
          if (c24.tag == FStar_Pervasives_Native_Some)
          {
            COSE_Format_everparsenomatch c13 = c24.v;
            uint64_t count = pcount;
            if (count < 18446744073709551615ULL)
            {
              size_t size0 = psize;
              Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
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
                res12 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
              if (res12 > (size_t)0U)
              {
                size_t size1 = size0 + res12;
                size_t
                res2 = COSE_Format_serialize_everparsenomatch(c13, split__uint8_t(out, size1).snd);
                if (res2 > (size_t)0U)
                {
                  size_t size2 = size1 + res2;
                  Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
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
          else if (c24.tag == FStar_Pervasives_Native_None)
            ite4 = true;
          else
            ite4 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
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
  bool ite5;
  if (ite4)
    if (c2.tag == COSE_Format_Inl)
    {
      Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ i = c2.case_Inl;
      Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ buf = i;
      KRML_HOST_IGNORE(&buf);
      Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ pc = i;
      bool pres = true;
      bool cond;
      if (pres)
        cond = !(len___COSE_Format_label___COSE_Format_values_(pc) == (size_t)0U);
      else
        cond = false;
      while (cond)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          Pulse_Lib_Slice_slice___COSE_Format_label___COSE_Format_values_ i1 = pc;
          K___COSE_Format_label_COSE_Format_values
          res = op_Array_Access___COSE_Format_label___COSE_Format_values_(i1, (size_t)0U);
          pc = split___COSE_Format_label___COSE_Format_values_(i1, (size_t)1U).snd;
          K___COSE_Format_label_COSE_Format_values scrut0 = res;
          COSE_Format_label ck = scrut0.fst;
          cbor_det_t cv = scrut0.snd;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
          size_t sz1 = COSE_Format_serialize_label(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            scrut0 = split__uint8_t(out1, sz1);
            Pulse_Lib_Slice_slice__uint8_t outl2 = scrut0.fst;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0.snd;
            size_t sz2 = COSE_Format_serialize_values(cv, out2);
            if (sz2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len0 = Pulse_Lib_Slice_len__uint8_t(outl2);
              size_t
              len2 =
                cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(outl2),
                  len0);
              option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
              if (len2 == (size_t)0U)
                scrut0 =
                  (
                    (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                scrut = split__uint8_t(outl2, len2);
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
                size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len1),
                        .snd = rem
                      }
                    }
                  );
              }
              if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t o1 = scrut0.v.fst;
                size_t len = Pulse_Lib_Slice_len__uint8_t(out2);
                size_t
                len0 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2),
                    len);
                option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
                if (len0 == (size_t)0U)
                  scrut0 =
                    (
                      (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut = split__uint8_t(out2, len0);
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
                  size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len1),
                          .snd = rem
                        }
                      }
                    );
                }
                if (scrut0.tag == FStar_Pervasives_Native_Some)
                  if
                  (COSE_Format_aux_env32_map_constraint_2(cbor_det_mk_map_entry(o1, scrut0.v.fst)))
                    pres = false;
                  else
                  {
                    size_t size1 = size0 + sz1;
                    size_t size2 = size1 + sz2;
                    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                    scrut = split__uint8_t(out, size2);
                    Pulse_Lib_Slice_slice__uint8_t
                    outl =
                      (
                        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                          .fst = scrut.fst,
                          .snd = scrut.snd
                        }
                      ).fst;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(outl);
                    if
                    (
                      !cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(outl),
                        aout_len,
                        size0,
                        size1)
                    )
                      pres = false;
                    else
                    {
                      pcount = count_;
                      psize = size2;
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
        bool ite;
        if (pres)
          ite = !(len___COSE_Format_label___COSE_Format_values_(pc) == (size_t)0U);
        else
          ite = false;
        cond = ite;
      }
      ite5 = pres;
    }
    else if (c2.tag == COSE_Format_Inr)
    {
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
      pc = c2.case_Inr;
      bool pres = true;
      bool cond0;
      if (pres)
      {
        CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
        c3 = pc;
        cbor_det_map_iterator_t pj = c3.cddl_map_iterator_contents;
        bool pres1 = true;
        bool cond;
        if (pres1)
          cond = !cbor_det_map_iterator_is_empty(pj);
        else
          cond = false;
        while (cond)
        {
          cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
          if (!!c3.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
            if (!c3.cddl_map_iterator_impl_validate_ex(elt))
              pres1 = !c3.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
          bool ite;
          if (pres1)
            ite = !cbor_det_map_iterator_is_empty(pj);
          else
            ite = false;
          cond = ite;
        }
        cond0 = !pres1;
      }
      else
        cond0 = false;
      while (cond0)
      {
        uint64_t count = pcount;
        if (count == 18446744073709551615ULL)
          pres = false;
        else
        {
          uint64_t count_ = count + 1ULL;
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
          i = pc;
          cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
          cbor_det_map_entry_t phd = cbor_det_map_iterator_next(&pj);
          cbor_det_map_entry_t hd0 = phd;
          bool cond;
          if (!i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd0)))
            cond = true;
          else if (!i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0)))
            cond = true;
          else
            cond = i.cddl_map_iterator_impl_validate_ex(hd0);
          while (cond)
          {
            phd = cbor_det_map_iterator_next(&pj);
            cbor_det_map_entry_t hd = phd;
            bool ite;
            if (!i.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(hd)))
              ite = true;
            else if (!i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd)))
              ite = true;
            else
              ite = i.cddl_map_iterator_impl_validate_ex(hd);
            cond = ite;
          }
          cbor_det_map_entry_t hd = phd;
          COSE_Format_label
          hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
          cbor_det_t hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
          pc =
            (
              (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values){
                .cddl_map_iterator_contents = pj,
                .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
                .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
                .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
                .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
                .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
              }
            );
          COSE_Format_label ck = hd_key_res;
          cbor_det_t cv = hd_value_res;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
          size_t sz1 = COSE_Format_serialize_label(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            scrut0 = split__uint8_t(out1, sz1);
            Pulse_Lib_Slice_slice__uint8_t outl2 = scrut0.fst;
            Pulse_Lib_Slice_slice__uint8_t out2 = scrut0.snd;
            size_t sz2 = COSE_Format_serialize_values(cv, out2);
            if (sz2 == (size_t)0U)
              pres = false;
            else
            {
              size_t len0 = Pulse_Lib_Slice_len__uint8_t(outl2);
              size_t
              len2 =
                cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(outl2),
                  len0);
              option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
              if (len2 == (size_t)0U)
                scrut0 =
                  (
                    (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                      .tag = FStar_Pervasives_Native_None
                    }
                  );
              else
              {
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                scrut = split__uint8_t(outl2, len2);
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
                Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
                Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
                size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
                scrut0 =
                  (
                    (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = {
                        .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                          len1),
                        .snd = rem
                      }
                    }
                  );
              }
              if (scrut0.tag == FStar_Pervasives_Native_Some)
              {
                cbor_det_t o1 = scrut0.v.fst;
                size_t len = Pulse_Lib_Slice_len__uint8_t(out2);
                size_t
                len0 =
                  cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(out2),
                    len);
                option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
                if (len0 == (size_t)0U)
                  scrut0 =
                    (
                      (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else
                {
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut = split__uint8_t(out2, len0);
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
                  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
                  Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
                  size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
                  scrut0 =
                    (
                      (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = {
                          .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2),
                            len1),
                          .snd = rem
                        }
                      }
                    );
                }
                if (scrut0.tag == FStar_Pervasives_Native_Some)
                  if
                  (COSE_Format_aux_env32_map_constraint_2(cbor_det_mk_map_entry(o1, scrut0.v.fst)))
                    pres = false;
                  else
                  {
                    size_t size1 = size0 + sz1;
                    size_t size2 = size1 + sz2;
                    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                    scrut = split__uint8_t(out, size2);
                    Pulse_Lib_Slice_slice__uint8_t
                    outl =
                      (
                        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                          .fst = scrut.fst,
                          .snd = scrut.snd
                        }
                      ).fst;
                    size_t aout_len = Pulse_Lib_Slice_len__uint8_t(outl);
                    if
                    (
                      !cbor_det_serialize_map_insert_to_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(outl),
                        aout_len,
                        size0,
                        size1)
                    )
                      pres = false;
                    else
                    {
                      pcount = count_;
                      psize = size2;
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
        bool ite;
        if (pres)
        {
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_label_COSE_Format_values
          c3 = pc;
          cbor_det_map_iterator_t pj = c3.cddl_map_iterator_contents;
          bool pres1 = true;
          bool cond;
          if (pres1)
            cond = !cbor_det_map_iterator_is_empty(pj);
          else
            cond = false;
          while (cond)
          {
            cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
            if (!!c3.cddl_map_iterator_impl_validate1(cbor_det_map_entry_key(elt)))
              if (!c3.cddl_map_iterator_impl_validate_ex(elt))
                pres1 = !c3.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(elt));
            bool ite;
            if (pres1)
              ite = !cbor_det_map_iterator_is_empty(pj);
            else
              ite = false;
            cond = ite;
          }
          ite = !pres1;
        }
        else
          ite = false;
        cond0 = ite;
      }
      ite5 = pres;
    }
    else
      ite5 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  else
    ite5 = false;
  if (ite5)
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

FStar_Pervasives_Native_option___COSE_Format_header_map___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_header_map(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_header_map___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_header_map(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_header_map___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_header_map(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_header_map___Pulse_Lib_Slice_slice_uint8_t_){
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
COSE_Format_is_empty_iterate_array_aux_env32_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
  i
)
{
  return cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents);
}

COSE_Format_label
COSE_Format_next_iterate_array_aux_env32_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
  *pi
)
{
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1
  i = *pi;
  uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
  cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
  KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
  cbor_det_array_iterator_t ji = pj;
  uint64_t len1 = cbor_det_array_iterator_length(ji);
  *pi =
    (
      (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env32_type_1){
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
    uint64_t len0 = cbor_det_get_string_length(c);
    Pulse_Lib_Slice_slice__uint8_t
    pl = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len0);
    size_t len = Pulse_Lib_Slice_len__uint8_t(pl);
    size_t len2 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(pl), len);
    option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
    if (len2 == (size_t)0U)
      scrut0 =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut = split__uint8_t(pl, len2);
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
      Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
      size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
      scrut0 =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = {
              .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
              .snd = rem
            }
          }
        );
    }
    if (scrut0.tag == FStar_Pervasives_Native_None)
      ite = false;
    else if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t r = scrut0.v;
      cbor_det_t res = r.fst;
      if (Pulse_Lib_Slice_len__uint8_t(r.snd) == (size_t)0U)
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
    len0 =
      Pulse_Lib_Slice_len__uint8_t(arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c),
          (size_t)len));
    return (size_t)0U <= len0 && len0 <= (size_t)0U;
  }
  else
    return false;
}

typedef struct empty_or_serialized_map_ugly_s
{
  COSE_Format_evercddl_int_ugly_tags tag;
  union {
    COSE_Format_header_map case_Inl;
    Pulse_Lib_Slice_slice__uint8_t case_Inr;
  }
  ;
}
empty_or_serialized_map_ugly;

bool
COSE_Format_uu___is_Mkempty_or_serialized_map0(COSE_Format_empty_or_serialized_map projectee)
{
  if (projectee.tag == COSE_Format_Mkempty_or_serialized_map0)
    return true;
  else
    return false;
}

bool
COSE_Format_uu___is_Mkempty_or_serialized_map1(COSE_Format_empty_or_serialized_map projectee)
{
  if (projectee.tag == COSE_Format_Mkempty_or_serialized_map1)
    return true;
  else
    return false;
}

static COSE_Format_empty_or_serialized_map
empty_or_serialized_map_right(empty_or_serialized_map_ugly x2)
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

static empty_or_serialized_map_ugly
empty_or_serialized_map_left(COSE_Format_empty_or_serialized_map x7)
{
  if (x7.tag == COSE_Format_Mkempty_or_serialized_map0)
    return
      (
        (empty_or_serialized_map_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = x7.case_Mkempty_or_serialized_map0 }
        }
      );
  else if (x7.tag == COSE_Format_Mkempty_or_serialized_map1)
    return
      (
        (empty_or_serialized_map_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = x7.case_Mkempty_or_serialized_map1 }
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
  __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t x
)
{
  return x.fst;
}

/**
Parser for empty_or_serialized_map
*/
COSE_Format_empty_or_serialized_map COSE_Format_parse_empty_or_serialized_map(cbor_det_t c)
{
  bool ite0;
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_BYTE_STRING)
  {
    uint64_t len0 = cbor_det_get_string_length(c);
    Pulse_Lib_Slice_slice__uint8_t
    pl = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len0);
    size_t len = Pulse_Lib_Slice_len__uint8_t(pl);
    size_t len2 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(pl), len);
    option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
    if (len2 == (size_t)0U)
      scrut0 =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut = split__uint8_t(pl, len2);
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
      Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
      size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
      scrut0 =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = {
              .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
              .snd = rem
            }
          }
        );
    }
    if (scrut0.tag == FStar_Pervasives_Native_None)
      ite0 = false;
    else if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t r = scrut0.v;
      cbor_det_t res = r.fst;
      if (Pulse_Lib_Slice_len__uint8_t(r.snd) == (size_t)0U)
        ite0 = COSE_Format_validate_header_map(res);
      else
        ite0 = false;
    }
    else
      ite0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  }
  else
    ite0 = false;
  empty_or_serialized_map_ugly ite1;
  if (ite0)
  {
    uint64_t len0 = cbor_det_get_string_length(c);
    Pulse_Lib_Slice_slice__uint8_t
    cs = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len0);
    size_t len = Pulse_Lib_Slice_len__uint8_t(cs);
    size_t len2 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(cs), len);
    option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
    if (len2 == (size_t)0U)
      scrut0 =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut = split__uint8_t(cs, len2);
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
      Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
      size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
      scrut0 =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = {
              .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
              .snd = rem
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
    ite1 = ((empty_or_serialized_map_ugly){ .tag = COSE_Format_Inl, { .case_Inl = ite } });
  }
  else
  {
    uint64_t len = cbor_det_get_string_length(c);
    ite1 =
      (
        (empty_or_serialized_map_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len) }
        }
      );
  }
  return empty_or_serialized_map_right(ite1);
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
  empty_or_serialized_map_ugly scrut0 = empty_or_serialized_map_left(c);
  if (scrut0.tag == COSE_Format_Inl)
  {
    size_t sz = COSE_Format_serialize_header_map(scrut0.case_Inl, out);
    if (sz == (size_t)0U || sz > (size_t)18446744073709551615ULL)
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
    if ((size_t)0ULL <= len && len <= (size_t)0ULL)
      if (2U == CBOR_MAJOR_TYPE_BYTE_STRING)
        if (Pulse_Lib_Slice_len__uint8_t(c2) <= (size_t)18446744073709551615ULL)
        {
          uint8_t *a = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c2);
          cbor_det_t
          x =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_BYTE_STRING,
              a,
              (uint64_t)Pulse_Lib_Slice_len__uint8_t(c2));
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
      else if (Pulse_Lib_Slice_len__uint8_t(c2) <= (size_t)18446744073709551615ULL)
      {
        size_t alen = Pulse_Lib_Slice_len__uint8_t(c2);
        if
        (
          cbor_det_impl_utf8_correct_from_array(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c2),
            alen)
        )
        {
          uint8_t *a = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(c2);
          cbor_det_t
          x =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
              a,
              (uint64_t)Pulse_Lib_Slice_len__uint8_t(c2));
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

FStar_Pervasives_Native_option___COSE_Format_empty_or_serialized_map___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_empty_or_serialized_map(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_empty_or_serialized_map___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_empty_or_serialized_map(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_empty_or_serialized_map___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_empty_or_serialized_map(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_empty_or_serialized_map___Pulse_Lib_Slice_slice_uint8_t_){
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
        if (Pulse_Lib_Slice_len__uint8_t(s) != (size_t)9ULL)
          ite = false;
        else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
          if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
            if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U) == 103U)
              if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U) == 110U)
              {
                size_t i_4 = (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U;
                if
                (
                  op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U) ==
                    97U
                )
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
        if (Pulse_Lib_Slice_len__uint8_t(s) != (size_t)10ULL)
          ite0 = false;
        else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
          if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
            if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U) == 103U)
              if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U) == 110U)
              {
                size_t i_4 = (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U;
                if
                (
                  op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U) ==
                    97U
                )
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
        cbor_det_array_iterator_t i1 = pi;
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
          pi = i1;
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

typedef struct
__COSE_Format_empty_or_serialized_map_FStar_Pervasives_either__COSE_Format_empty_or_serialized_map____COSE_Format_bstr___COSE_Format_bstr____COSE_Format_bstr___COSE_Format_bstr__s
{
  COSE_Format_empty_or_serialized_map fst;
  FStar_Pervasives_either___COSE_Format_empty_or_serialized_map____COSE_Format_bstr___COSE_Format_bstr____COSE_Format_bstr___COSE_Format_bstr_
  snd;
}
__COSE_Format_empty_or_serialized_map_FStar_Pervasives_either__COSE_Format_empty_or_serialized_map____COSE_Format_bstr___COSE_Format_bstr____COSE_Format_bstr___COSE_Format_bstr_;

typedef struct sig_structure_ugly_s
{
  COSE_Format_evercddl_int_ugly_tags fst;
  __COSE_Format_empty_or_serialized_map_FStar_Pervasives_either__COSE_Format_empty_or_serialized_map____COSE_Format_bstr___COSE_Format_bstr____COSE_Format_bstr___COSE_Format_bstr_
  snd;
}
sig_structure_ugly;

bool COSE_Format_uu___is_Mksig_structure0(COSE_Format_sig_structure projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_sig_structure sig_structure_right(sig_structure_ugly x3)
{
  return
    (
      (COSE_Format_sig_structure){
        .context = x3.fst,
        .body_protected = x3.snd.fst,
        ._x0 = x3.snd.snd
      }
    );
}

static sig_structure_ugly sig_structure_left(COSE_Format_sig_structure x7)
{
  return
    ((sig_structure_ugly){ .fst = x7.context, .snd = { .fst = x7.body_protected, .snd = x7._x0 } });
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
      if (Pulse_Lib_Slice_len__uint8_t(s) != (size_t)9ULL)
        ite = false;
      else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
        if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
          if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U) == 103U)
            if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U) == 110U)
            {
              size_t i_4 = (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U;
              if
              (
                op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U) ==
                  97U
              )
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
      if (Pulse_Lib_Slice_len__uint8_t(s) != (size_t)10ULL)
        ite0 = false;
      else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
        if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
          if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U) == 103U)
            if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U) == 110U)
            {
              size_t i_4 = (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U;
              if
              (
                op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U) ==
                  97U
              )
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
    if (Pulse_Lib_Slice_len__uint8_t(s) != (size_t)9ULL)
      ite1 = false;
    else if (op_Array_Access__uint8_t(s, (size_t)0U) == 83U)
      if (op_Array_Access__uint8_t(s, (size_t)1U) == 105U)
        if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U) == 103U)
          if (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U) == 110U)
          {
            size_t i_4 = (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U;
            if
            (op_Array_Access__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U) == 97U)
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
  cbor_det_array_iterator_t pc1 = c1;
  bool ite2;
  if (cbor_det_array_iterator_is_empty(pc1))
    ite2 = false;
  else
    ite2 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc1));
  KRML_MAYBE_UNUSED_VAR(ite2);
  cbor_det_array_iterator_t c11 = pc1;
  cbor_det_array_iterator_t
  buf1 = cbor_det_array_iterator_truncate(c1, rlen01 - cbor_det_array_iterator_length(c11));
  COSE_Format_empty_or_serialized_map
  w11 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf1));
  cbor_det_array_iterator_t pc2 = c11;
  bool ite3;
  if (cbor_det_array_iterator_is_empty(pc2))
    ite3 = false;
  else
    ite3 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc2));
  bool ite4;
  if (ite3)
  {
    bool ite;
    if (cbor_det_array_iterator_is_empty(pc2))
      ite = false;
    else
      ite = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pc2));
    if (ite)
      if (cbor_det_array_iterator_is_empty(pc2))
        ite4 = false;
      else
        ite4 = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pc2));
    else
      ite4 = false;
  }
  else
    ite4 = false;
  FStar_Pervasives_either___COSE_Format_empty_or_serialized_map____COSE_Format_bstr___COSE_Format_bstr____COSE_Format_bstr___COSE_Format_bstr_
  ite5;
  if (ite4)
  {
    uint64_t rlen02 = cbor_det_array_iterator_length(c11);
    cbor_det_array_iterator_t pc3 = c11;
    bool ite0;
    if (cbor_det_array_iterator_is_empty(pc3))
      ite0 = false;
    else
      ite0 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc3));
    KRML_MAYBE_UNUSED_VAR(ite0);
    cbor_det_array_iterator_t c12 = pc3;
    cbor_det_array_iterator_t
    buf0 = cbor_det_array_iterator_truncate(c11, rlen02 - cbor_det_array_iterator_length(c12));
    COSE_Format_empty_or_serialized_map
    w12 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
    uint64_t rlen03 = cbor_det_array_iterator_length(c12);
    cbor_det_array_iterator_t pc4 = c12;
    bool ite;
    if (cbor_det_array_iterator_is_empty(pc4))
      ite = false;
    else
      ite = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pc4));
    KRML_MAYBE_UNUSED_VAR(ite);
    cbor_det_array_iterator_t c13 = pc4;
    cbor_det_array_iterator_t
    buf1 = cbor_det_array_iterator_truncate(c12, rlen03 - cbor_det_array_iterator_length(c13));
    Pulse_Lib_Slice_slice__uint8_t
    w13 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf1));
    cbor_det_array_iterator_t buf = c13;
    ite5 =
      (
        (FStar_Pervasives_either___COSE_Format_empty_or_serialized_map____COSE_Format_bstr___COSE_Format_bstr____COSE_Format_bstr___COSE_Format_bstr_){
          .tag = COSE_Format_Inl,
          {
            .case_Inl = {
              .fst = w12,
              .snd = {
                .fst = w13,
                .snd = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf))
              }
            }
          }
        }
      );
  }
  else
  {
    uint64_t rlen02 = cbor_det_array_iterator_length(c11);
    cbor_det_array_iterator_t pc3 = c11;
    bool ite;
    if (cbor_det_array_iterator_is_empty(pc3))
      ite = false;
    else
      ite = COSE_Format_validate_bstr(cbor_det_array_iterator_next(&pc3));
    KRML_MAYBE_UNUSED_VAR(ite);
    cbor_det_array_iterator_t c12 = pc3;
    cbor_det_array_iterator_t
    buf0 = cbor_det_array_iterator_truncate(c11, rlen02 - cbor_det_array_iterator_length(c12));
    Pulse_Lib_Slice_slice__uint8_t
    w12 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf0));
    cbor_det_array_iterator_t buf = c12;
    ite5 =
      (
        (FStar_Pervasives_either___COSE_Format_empty_or_serialized_map____COSE_Format_bstr___COSE_Format_bstr____COSE_Format_bstr___COSE_Format_bstr_){
          .tag = COSE_Format_Inr,
          {
            .case_Inr = {
              .fst = w12,
              .snd = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf))
            }
          }
        }
      );
  }
  return
    sig_structure_right(((sig_structure_ugly){ .fst = w1, .snd = { .fst = w11, .snd = ite5 } }));
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
  sig_structure_ugly scrut0 = sig_structure_left(c);
  COSE_Format_evercddl_int_ugly_tags c1 = scrut0.fst;
  __COSE_Format_empty_or_serialized_map_FStar_Pervasives_either__COSE_Format_empty_or_serialized_map____COSE_Format_bstr___COSE_Format_bstr____COSE_Format_bstr___COSE_Format_bstr_
  c2 = scrut0.snd;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
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
          op_Array_Assignment__uint8_t(s, (size_t)1U + (size_t)1U, 103U);
          op_Array_Assignment__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U, 110U);
          op_Array_Assignment__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U, 97U);
          size_t i_4 = (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_4, 116U);
          size_t i_5 = i_4 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_5, 117U);
          size_t i_6 = i_5 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_6, 114U);
          op_Array_Assignment__uint8_t(s, i_6 + (size_t)1U, 101U);
          uint8_t *a1 = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s);
          cbor_det_t
          c3 =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
              a1,
              (uint64_t)Pulse_Lib_Slice_len__uint8_t(s));
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
          op_Array_Assignment__uint8_t(s, (size_t)1U + (size_t)1U, 103U);
          op_Array_Assignment__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U, 110U);
          op_Array_Assignment__uint8_t(s, (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U, 97U);
          size_t i_4 = (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_4, 116U);
          size_t i_5 = i_4 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_5, 117U);
          size_t i_6 = i_5 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_6, 114U);
          size_t i_7 = i_6 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_7, 101U);
          op_Array_Assignment__uint8_t(s, i_7 + (size_t)1U, 49U);
          uint8_t *a1 = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s);
          cbor_det_t
          c3 =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
              a1,
              (uint64_t)Pulse_Lib_Slice_len__uint8_t(s));
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
    COSE_Format_empty_or_serialized_map c11 = c2.fst;
    FStar_Pervasives_either___COSE_Format_empty_or_serialized_map____COSE_Format_bstr___COSE_Format_bstr____COSE_Format_bstr___COSE_Format_bstr_
    c21 = c2.snd;
    uint64_t count0 = pcount;
    bool ite0;
    if (count0 < 18446744073709551615ULL)
    {
      size_t size = psize;
      size_t
      size1 = COSE_Format_serialize_empty_or_serialized_map(c11, split__uint8_t(out, size).snd);
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
    if (ite0)
      if (c21.tag == COSE_Format_Inl)
      {
        K___COSE_Format_empty_or_serialized_map__COSE_Format_bstr___COSE_Format_bstr_
        c12 = c21.case_Inl;
        COSE_Format_empty_or_serialized_map c13 = c12.fst;
        K___COSE_Format_bstr_COSE_Format_bstr c22 = c12.snd;
        uint64_t count0 = pcount;
        bool ite0;
        if (count0 < 18446744073709551615ULL)
        {
          size_t size = psize;
          size_t
          size1 = COSE_Format_serialize_empty_or_serialized_map(c13, split__uint8_t(out, size).snd);
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
        if (ite0)
        {
          Pulse_Lib_Slice_slice__uint8_t c14 = c22.fst;
          Pulse_Lib_Slice_slice__uint8_t c23 = c22.snd;
          uint64_t count = pcount;
          bool ite;
          if (count < 18446744073709551615ULL)
          {
            size_t size = psize;
            size_t size1 = COSE_Format_serialize_bstr(c14, split__uint8_t(out, size).snd);
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
            uint64_t count = pcount;
            if (count < 18446744073709551615ULL)
            {
              size_t size = psize;
              size_t size1 = COSE_Format_serialize_bstr(c23, split__uint8_t(out, size).snd);
              if (size1 == (size_t)0U)
                ite1 = false;
              else
              {
                pcount = count + 1ULL;
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
        K___COSE_Format_bstr_COSE_Format_bstr c22 = c21.case_Inr;
        Pulse_Lib_Slice_slice__uint8_t c12 = c22.fst;
        Pulse_Lib_Slice_slice__uint8_t c23 = c22.snd;
        uint64_t count = pcount;
        bool ite;
        if (count < 18446744073709551615ULL)
        {
          size_t size = psize;
          size_t size1 = COSE_Format_serialize_bstr(c12, split__uint8_t(out, size).snd);
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
          uint64_t count = pcount;
          if (count < 18446744073709551615ULL)
          {
            size_t size = psize;
            size_t size1 = COSE_Format_serialize_bstr(c23, split__uint8_t(out, size).snd);
            if (size1 == (size_t)0U)
              ite1 = false;
            else
            {
              pcount = count + 1ULL;
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

FStar_Pervasives_Native_option___COSE_Format_sig_structure___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_sig_structure(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_sig_structure___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_sig_structure(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_sig_structure___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_sig_structure(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_sig_structure___Pulse_Lib_Slice_slice_uint8_t_){
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

typedef struct __COSE_Format_empty_or_serialized_map_COSE_Format_header_map_s
{
  COSE_Format_empty_or_serialized_map fst;
  COSE_Format_header_map snd;
}
__COSE_Format_empty_or_serialized_map_COSE_Format_header_map;

typedef struct __FStar_Pervasives_either_COSE_Format_bstr_COSE_Format_nil_COSE_Format_bstr_s
{
  FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil fst;
  Pulse_Lib_Slice_slice__uint8_t snd;
}
__FStar_Pervasives_either_COSE_Format_bstr_COSE_Format_nil_COSE_Format_bstr;

typedef struct cose_sign1_ugly_s
{
  __COSE_Format_empty_or_serialized_map_COSE_Format_header_map fst;
  __FStar_Pervasives_either_COSE_Format_bstr_COSE_Format_nil_COSE_Format_bstr snd;
}
cose_sign1_ugly;

bool COSE_Format_uu___is_Mkcose_sign10(COSE_Format_cose_sign1 projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_cose_sign1 cose_sign1_right(cose_sign1_ugly x4)
{
  return
    (
      (COSE_Format_cose_sign1){
        .protected = x4.fst.fst,
        .unprotected = x4.fst.snd,
        .payload = x4.snd.fst,
        .signature = x4.snd.snd
      }
    );
}

static cose_sign1_ugly cose_sign1_left(COSE_Format_cose_sign1 x9)
{
  return
    (
      (cose_sign1_ugly){
        .fst = { .fst = x9.protected, .snd = x9.unprotected },
        .snd = { .fst = x9.payload, .snd = x9.signature }
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
  uint64_t rlen010 = cbor_det_array_iterator_length(c0_);
  cbor_det_array_iterator_t pc10 = c0_;
  bool ite2;
  if (cbor_det_array_iterator_is_empty(pc10))
    ite2 = false;
  else
    ite2 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc10));
  KRML_MAYBE_UNUSED_VAR(ite2);
  cbor_det_array_iterator_t c11 = pc10;
  cbor_det_array_iterator_t
  buf0 = cbor_det_array_iterator_truncate(c0_, rlen010 - cbor_det_array_iterator_length(c11));
  COSE_Format_empty_or_serialized_map
  w1 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
  cbor_det_array_iterator_t buf1 = c11;
  __COSE_Format_empty_or_serialized_map_COSE_Format_header_map
  w10 = { .fst = w1, .snd = COSE_Format_parse_header_map(cbor_det_array_iterator_next(&buf1)) };
  uint64_t rlen01 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t pc1 = c1;
  bool ite;
  if (cbor_det_array_iterator_is_empty(pc1))
    ite = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc1);
    if (COSE_Format_validate_bstr(c2))
      ite = true;
    else
      ite = COSE_Format_validate_nil(c2);
  }
  KRML_MAYBE_UNUSED_VAR(ite);
  cbor_det_array_iterator_t c110 = pc1;
  cbor_det_array_iterator_t
  buf2 = cbor_det_array_iterator_truncate(c1, rlen01 - cbor_det_array_iterator_length(c110));
  cbor_det_t x = cbor_det_array_iterator_next(&buf2);
  FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil w11;
  if (COSE_Format_validate_bstr(x))
    w11 =
      (
        (FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_bstr(x) }
        }
      );
  else
    w11 =
      (
        (FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_nil(x) }
        }
      );
  cbor_det_array_iterator_t buf = c110;
  return
    cose_sign1_right((
        (cose_sign1_ugly){
          .fst = w10,
          .snd = { .fst = w11, .snd = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf)) }
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
  cose_sign1_ugly scrut = cose_sign1_left(c);
  __COSE_Format_empty_or_serialized_map_COSE_Format_header_map c1 = scrut.fst;
  __FStar_Pervasives_either_COSE_Format_bstr_COSE_Format_nil_COSE_Format_bstr c2 = scrut.snd;
  COSE_Format_empty_or_serialized_map c110 = c1.fst;
  COSE_Format_header_map c210 = c1.snd;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    size_t
    size1 = COSE_Format_serialize_empty_or_serialized_map(c110, split__uint8_t(out, size).snd);
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
    uint64_t count = pcount;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      size_t size1 = COSE_Format_serialize_header_map(c210, split__uint8_t(out, size).snd);
      if (size1 == (size_t)0U)
        ite1 = false;
      else
      {
        pcount = count + 1ULL;
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
    FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil c11 = c2.fst;
    Pulse_Lib_Slice_slice__uint8_t c21 = c2.snd;
    uint64_t count = pcount;
    bool ite;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
      size_t size1;
      if (c11.tag == COSE_Format_Inl)
        size1 = COSE_Format_serialize_bstr(c11.case_Inl, out1);
      else if (c11.tag == COSE_Format_Inr)
        size1 = COSE_Format_serialize_nil(c11.case_Inr, out1);
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
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size = psize;
        size_t size1 = COSE_Format_serialize_bstr(c21, split__uint8_t(out, size).snd);
        if (size1 == (size_t)0U)
          ite2 = false;
        else
        {
          pcount = count + 1ULL;
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

FStar_Pervasives_Native_option___COSE_Format_cose_sign1___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_sign1(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_sign1___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_sign1(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_sign1___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_sign1(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_sign1___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_uu___is_Mkcose_sign1_tagged0(COSE_Format_cose_sign1 projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_cose_sign1 cose_sign1_tagged_right(COSE_Format_cose_sign1 x1)
{
  return x1;
}

static COSE_Format_cose_sign1 cose_sign1_tagged_left(COSE_Format_cose_sign1 x3)
{
  return x3;
}

/**
Parser for cose_sign1_tagged
*/
COSE_Format_cose_sign1 COSE_Format_parse_cose_sign1_tagged(cbor_det_t c)
{
  return cose_sign1_tagged_right(COSE_Format_parse_cose_sign1(cbor_det_get_tagged_payload(c)));
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
  COSE_Format_cose_sign1 cpayload = cose_sign1_tagged_left(c);
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
    size_t psz = COSE_Format_serialize_cose_sign1(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_cose_sign1_tagged___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_sign1_tagged(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_sign1_tagged___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_sign1_tagged(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_sign1_tagged___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_sign1_tagged(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_sign1_tagged___Pulse_Lib_Slice_slice_uint8_t_){
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

typedef struct cose_signature_ugly_s
{
  __COSE_Format_empty_or_serialized_map_COSE_Format_header_map fst;
  Pulse_Lib_Slice_slice__uint8_t snd;
}
cose_signature_ugly;

bool COSE_Format_uu___is_Mkcose_signature0(COSE_Format_cose_signature projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_cose_signature cose_signature_right(cose_signature_ugly x3)
{
  return
    (
      (COSE_Format_cose_signature){
        .protected = x3.fst.fst,
        .unprotected = x3.fst.snd,
        .signature = x3.snd
      }
    );
}

static cose_signature_ugly cose_signature_left(COSE_Format_cose_signature x7)
{
  return
    (
      (cose_signature_ugly){
        .fst = { .fst = x7.protected, .snd = x7.unprotected },
        .snd = x7.signature
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
  __COSE_Format_empty_or_serialized_map_COSE_Format_header_map
  w10 = { .fst = w1, .snd = COSE_Format_parse_header_map(cbor_det_array_iterator_next(&buf1)) };
  cbor_det_array_iterator_t buf = c1;
  return
    cose_signature_right((
        (cose_signature_ugly){
          .fst = w10,
          .snd = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf))
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
  cose_signature_ugly scrut = cose_signature_left(c);
  __COSE_Format_empty_or_serialized_map_COSE_Format_header_map c1 = scrut.fst;
  Pulse_Lib_Slice_slice__uint8_t c2 = scrut.snd;
  COSE_Format_empty_or_serialized_map c11 = c1.fst;
  COSE_Format_header_map c21 = c1.snd;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    size_t
    size1 = COSE_Format_serialize_empty_or_serialized_map(c11, split__uint8_t(out, size).snd);
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
    uint64_t count = pcount;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      size_t size1 = COSE_Format_serialize_header_map(c21, split__uint8_t(out, size).snd);
      if (size1 == (size_t)0U)
        ite1 = false;
      else
      {
        pcount = count + 1ULL;
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
      size_t size1 = COSE_Format_serialize_bstr(c2, split__uint8_t(out, size).snd);
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

FStar_Pervasives_Native_option___COSE_Format_cose_signature___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_signature(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_signature___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_signature(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_signature___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_signature(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_signature___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_aux_env39_validate_1(cbor_det_array_iterator_t *pi)
{
  if (cbor_det_array_iterator_is_empty(*pi))
    return false;
  else
    return COSE_Format_validate_cose_signature(cbor_det_array_iterator_next(pi));
}

bool COSE_Format_uu___is_Mkaux_env39_type_10(COSE_Format_cose_signature projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_cose_signature aux_env39_type_1_right(COSE_Format_cose_signature x1)
{
  return x1;
}

static COSE_Format_cose_signature aux_env39_type_1_left(COSE_Format_cose_signature x3)
{
  return x3;
}

/**
Parser for aux_env39_type_1
*/
COSE_Format_cose_signature COSE_Format_aux_env39_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t buf = c;
  return
    aux_env39_type_1_right(COSE_Format_parse_cose_signature(cbor_det_array_iterator_next(&buf)));
}

/**
Serializer for aux_env39_type_1
*/
bool
COSE_Format_aux_env39_serialize_1(
  COSE_Format_cose_signature c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  COSE_Format_cose_signature c_ = aux_env39_type_1_left(c);
  uint64_t count = *out_count;
  if (count < 18446744073709551615ULL)
  {
    size_t size = *out_size;
    size_t size1 = COSE_Format_serialize_cose_signature(c_, split__uint8_t(out, size).snd);
    if (size1 == (size_t)0U)
      return false;
    else
    {
      *out_count = count + 1ULL;
      *out_size = size + size1;
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

typedef struct
__FStar_Pervasives_either_COSE_Format_bstr_COSE_Format_nil_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1_s
{
  FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
  snd;
}
__FStar_Pervasives_either_COSE_Format_bstr_COSE_Format_nil_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1;

typedef struct cose_sign_ugly_s
{
  __COSE_Format_empty_or_serialized_map_COSE_Format_header_map fst;
  __FStar_Pervasives_either_COSE_Format_bstr_COSE_Format_nil_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
  snd;
}
cose_sign_ugly;

bool COSE_Format_uu___is_Mkcose_sign0(COSE_Format_cose_sign projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_cose_sign cose_sign_right(cose_sign_ugly x4)
{
  return
    (
      (COSE_Format_cose_sign){
        .protected = x4.fst.fst,
        .unprotected = x4.fst.snd,
        .payload = x4.snd.fst,
        .signatures = x4.snd.snd
      }
    );
}

static cose_sign_ugly cose_sign_left(COSE_Format_cose_sign x9)
{
  return
    (
      (cose_sign_ugly){
        .fst = { .fst = x9.protected, .snd = x9.unprotected },
        .snd = { .fst = x9.payload, .snd = x9.signatures }
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
  uint64_t rlen010 = cbor_det_array_iterator_length(c0_);
  cbor_det_array_iterator_t pc10 = c0_;
  bool ite2;
  if (cbor_det_array_iterator_is_empty(pc10))
    ite2 = false;
  else
    ite2 = COSE_Format_validate_empty_or_serialized_map(cbor_det_array_iterator_next(&pc10));
  KRML_MAYBE_UNUSED_VAR(ite2);
  cbor_det_array_iterator_t c11 = pc10;
  cbor_det_array_iterator_t
  buf0 = cbor_det_array_iterator_truncate(c0_, rlen010 - cbor_det_array_iterator_length(c11));
  COSE_Format_empty_or_serialized_map
  w1 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
  cbor_det_array_iterator_t buf1 = c11;
  __COSE_Format_empty_or_serialized_map_COSE_Format_header_map
  w10 = { .fst = w1, .snd = COSE_Format_parse_header_map(cbor_det_array_iterator_next(&buf1)) };
  uint64_t rlen01 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t pc1 = c1;
  bool ite;
  if (cbor_det_array_iterator_is_empty(pc1))
    ite = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc1);
    if (COSE_Format_validate_bstr(c2))
      ite = true;
    else
      ite = COSE_Format_validate_nil(c2);
  }
  KRML_MAYBE_UNUSED_VAR(ite);
  cbor_det_array_iterator_t c110 = pc1;
  cbor_det_array_iterator_t
  buf2 = cbor_det_array_iterator_truncate(c1, rlen01 - cbor_det_array_iterator_length(c110));
  cbor_det_t x = cbor_det_array_iterator_next(&buf2);
  FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil w11;
  if (COSE_Format_validate_bstr(x))
    w11 =
      (
        (FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_bstr(x) }
        }
      );
  else
    w11 =
      (
        (FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_nil(x) }
        }
      );
  cbor_det_array_iterator_t buf = c110;
  return
    cose_sign_right((
        (cose_sign_ugly){
          .fst = w10,
          .snd = {
            .fst = w11,
            .snd = {
              .tag = COSE_Format_Inr,
              {
                .case_Inr = {
                  .cddl_array_iterator_contents = cbor_det_array_iterator_start(cbor_det_array_iterator_next(&buf)),
                  .cddl_array_iterator_impl_validate = COSE_Format_aux_env39_validate_1,
                  .cddl_array_iterator_impl_parse = COSE_Format_aux_env39_parse_1
                }
              }
            }
          }
        }
      ));
}

static size_t
len__COSE_Format_aux_env39_type_1(Pulse_Lib_Slice_slice__COSE_Format_aux_env39_type_1 s)
{
  return s.len;
}

static COSE_Format_cose_signature
op_Array_Access__COSE_Format_aux_env39_type_1(
  Pulse_Lib_Slice_slice__COSE_Format_aux_env39_type_1 a,
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
  cose_sign_ugly scrut = cose_sign_left(c);
  __COSE_Format_empty_or_serialized_map_COSE_Format_header_map c1 = scrut.fst;
  __FStar_Pervasives_either_COSE_Format_bstr_COSE_Format_nil_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
  c2 = scrut.snd;
  COSE_Format_empty_or_serialized_map c110 = c1.fst;
  COSE_Format_header_map c210 = c1.snd;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    size_t
    size1 = COSE_Format_serialize_empty_or_serialized_map(c110, split__uint8_t(out, size).snd);
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
    uint64_t count = pcount;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      size_t size1 = COSE_Format_serialize_header_map(c210, split__uint8_t(out, size).snd);
      if (size1 == (size_t)0U)
        ite1 = false;
      else
      {
        pcount = count + 1ULL;
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
    FStar_Pervasives_either__COSE_Format_bstr_COSE_Format_nil c11 = c2.fst;
    FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
    c21 = c2.snd;
    uint64_t count = pcount;
    bool ite0;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
      size_t size1;
      if (c11.tag == COSE_Format_Inl)
        size1 = COSE_Format_serialize_bstr(c11.case_Inl, out1);
      else if (c11.tag == COSE_Format_Inr)
        size1 = COSE_Format_serialize_nil(c11.case_Inr, out1);
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
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
        uint64_t pcount1 = 0ULL;
        size_t psize1 = (size_t)0U;
        bool ite;
        if (c21.tag == COSE_Format_Inl)
        {
          Pulse_Lib_Slice_slice__COSE_Format_aux_env39_type_1 c12 = c21.case_Inl;
          if (len__COSE_Format_aux_env39_type_1(c12) == (size_t)0U)
            ite = false;
          else
          {
            bool pres = true;
            size_t pi = (size_t)0U;
            size_t slen = len__COSE_Format_aux_env39_type_1(c12);
            bool cond;
            if (pres)
              cond = pi < slen;
            else
              cond = false;
            while (cond)
            {
              size_t i = pi;
              if
              (
                COSE_Format_aux_env39_serialize_1(op_Array_Access__COSE_Format_aux_env39_type_1(c12,
                    i),
                  out1,
                  &pcount1,
                  &psize1)
              )
                pi = i + (size_t)1U;
              else
                pres = false;
              bool ite;
              if (pres)
                ite = pi < slen;
              else
                ite = false;
              cond = ite;
            }
            ite = pres;
          }
        }
        else if (c21.tag == COSE_Format_Inr)
        {
          CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
          c22 = c21.case_Inr;
          if (cbor_det_array_iterator_is_empty(c22.cddl_array_iterator_contents))
            ite = false;
          else
          {
            CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
            pc = c22;
            bool pres = true;
            bool cond;
            if (pres)
              cond = !cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
            else
              cond = false;
            while (cond)
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
              i = pc;
              uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
              cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
              KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
              cbor_det_array_iterator_t ji = pj;
              uint64_t len1 = cbor_det_array_iterator_length(ji);
              pc =
                (
                  (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1){
                    .cddl_array_iterator_contents = ji,
                    .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
                    .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
                  }
                );
              if
              (
                !COSE_Format_aux_env39_serialize_1(i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
                      len0 - len1)),
                  out1,
                  &pcount1,
                  &psize1)
              )
                pres = false;
              bool ite;
              if (pres)
                ite = !cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
              else
                ite = false;
              cond = ite;
            }
            ite = pres;
          }
        }
        else
          ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
        size_t size10;
        if (ite)
        {
          size_t size1 = psize1;
          uint64_t count1 = pcount1;
          size_t aout_len = Pulse_Lib_Slice_len__uint8_t(out1);
          size10 =
            cbor_det_serialize_array_to_array(count1,
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
          pcount = count + 1ULL;
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

FStar_Pervasives_Native_option___COSE_Format_cose_sign___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_sign(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_sign___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_sign(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_sign___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_sign(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_sign___Pulse_Lib_Slice_slice_uint8_t_){
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
COSE_Format_is_empty_iterate_array_aux_env39_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
  i
)
{
  return cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents);
}

COSE_Format_cose_signature
COSE_Format_next_iterate_array_aux_env39_type_1(
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
  *pi
)
{
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1
  i = *pi;
  uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
  cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
  KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
  cbor_det_array_iterator_t ji = pj;
  uint64_t len1 = cbor_det_array_iterator_length(ji);
  *pi =
    (
      (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env39_type_1){
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

bool COSE_Format_uu___is_Mkcose_sign_tagged0(COSE_Format_cose_sign projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_cose_sign cose_sign_tagged_right(COSE_Format_cose_sign x1)
{
  return x1;
}

static COSE_Format_cose_sign cose_sign_tagged_left(COSE_Format_cose_sign x3)
{
  return x3;
}

/**
Parser for cose_sign_tagged
*/
COSE_Format_cose_sign COSE_Format_parse_cose_sign_tagged(cbor_det_t c)
{
  return cose_sign_tagged_right(COSE_Format_parse_cose_sign(cbor_det_get_tagged_payload(c)));
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
  COSE_Format_cose_sign cpayload = cose_sign_tagged_left(c);
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
    size_t psz = COSE_Format_serialize_cose_sign(cpayload, split__uint8_t(out, tsz).snd);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_cose_sign_tagged___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_sign_tagged(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_sign_tagged___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_sign_tagged(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_sign_tagged___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_sign_tagged(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_sign_tagged___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_cose_tagged_message(cbor_det_t c)
{
  if (COSE_Format_validate_cose_sign_tagged(c))
    return true;
  else
    return COSE_Format_validate_cose_sign1_tagged(c);
}

typedef struct cose_tagged_message_ugly_s
{
  COSE_Format_evercddl_int_ugly_tags tag;
  union {
    COSE_Format_cose_sign case_Inl;
    COSE_Format_cose_sign1 case_Inr;
  }
  ;
}
cose_tagged_message_ugly;

bool COSE_Format_uu___is_Mkcose_tagged_message0(COSE_Format_cose_tagged_message projectee)
{
  if (projectee.tag == COSE_Format_Mkcose_tagged_message0)
    return true;
  else
    return false;
}

bool COSE_Format_uu___is_Mkcose_tagged_message1(COSE_Format_cose_tagged_message projectee)
{
  if (projectee.tag == COSE_Format_Mkcose_tagged_message1)
    return true;
  else
    return false;
}

static COSE_Format_cose_tagged_message cose_tagged_message_right(cose_tagged_message_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return
      (
        (COSE_Format_cose_tagged_message){
          .tag = COSE_Format_Mkcose_tagged_message0,
          { .case_Mkcose_tagged_message0 = x2.case_Inl }
        }
      );
  else if (x2.tag == COSE_Format_Inr)
    return
      (
        (COSE_Format_cose_tagged_message){
          .tag = COSE_Format_Mkcose_tagged_message1,
          { .case_Mkcose_tagged_message1 = x2.case_Inr }
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

static cose_tagged_message_ugly cose_tagged_message_left(COSE_Format_cose_tagged_message x7)
{
  if (x7.tag == COSE_Format_Mkcose_tagged_message0)
    return
      (
        (cose_tagged_message_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = x7.case_Mkcose_tagged_message0 }
        }
      );
  else if (x7.tag == COSE_Format_Mkcose_tagged_message1)
    return
      (
        (cose_tagged_message_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = x7.case_Mkcose_tagged_message1 }
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
Parser for cose_tagged_message
*/
COSE_Format_cose_tagged_message COSE_Format_parse_cose_tagged_message(cbor_det_t c)
{
  cose_tagged_message_ugly ite;
  if (COSE_Format_validate_cose_sign_tagged(c))
    ite =
      (
        (cose_tagged_message_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_cose_sign_tagged(c) }
        }
      );
  else
    ite =
      (
        (cose_tagged_message_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_cose_sign1_tagged(c) }
        }
      );
  return cose_tagged_message_right(ite);
}

/**
Serializer for cose_tagged_message
*/
size_t
COSE_Format_serialize_cose_tagged_message(
  COSE_Format_cose_tagged_message c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  cose_tagged_message_ugly scrut = cose_tagged_message_left(c);
  if (scrut.tag == COSE_Format_Inl)
    return COSE_Format_serialize_cose_sign_tagged(scrut.case_Inl, out);
  else if (scrut.tag == COSE_Format_Inr)
    return COSE_Format_serialize_cose_sign1_tagged(scrut.case_Inr, out);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option___COSE_Format_cose_tagged_message___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_tagged_message(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_tagged_message___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_tagged_message(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_tagged_message___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_tagged_message(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_tagged_message___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_cose_untagged_message(cbor_det_t c)
{
  if (COSE_Format_validate_cose_sign(c))
    return true;
  else
    return COSE_Format_validate_cose_sign1(c);
}

typedef struct cose_untagged_message_ugly_s
{
  COSE_Format_evercddl_int_ugly_tags tag;
  union {
    COSE_Format_cose_sign case_Inl;
    COSE_Format_cose_sign1 case_Inr;
  }
  ;
}
cose_untagged_message_ugly;

bool COSE_Format_uu___is_Mkcose_untagged_message0(COSE_Format_cose_untagged_message projectee)
{
  if (projectee.tag == COSE_Format_Mkcose_untagged_message0)
    return true;
  else
    return false;
}

bool COSE_Format_uu___is_Mkcose_untagged_message1(COSE_Format_cose_untagged_message projectee)
{
  if (projectee.tag == COSE_Format_Mkcose_untagged_message1)
    return true;
  else
    return false;
}

static COSE_Format_cose_untagged_message
cose_untagged_message_right(cose_untagged_message_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return
      (
        (COSE_Format_cose_untagged_message){
          .tag = COSE_Format_Mkcose_untagged_message0,
          { .case_Mkcose_untagged_message0 = x2.case_Inl }
        }
      );
  else if (x2.tag == COSE_Format_Inr)
    return
      (
        (COSE_Format_cose_untagged_message){
          .tag = COSE_Format_Mkcose_untagged_message1,
          { .case_Mkcose_untagged_message1 = x2.case_Inr }
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

static cose_untagged_message_ugly
cose_untagged_message_left(COSE_Format_cose_untagged_message x7)
{
  if (x7.tag == COSE_Format_Mkcose_untagged_message0)
    return
      (
        (cose_untagged_message_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = x7.case_Mkcose_untagged_message0 }
        }
      );
  else if (x7.tag == COSE_Format_Mkcose_untagged_message1)
    return
      (
        (cose_untagged_message_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = x7.case_Mkcose_untagged_message1 }
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
Parser for cose_untagged_message
*/
COSE_Format_cose_untagged_message COSE_Format_parse_cose_untagged_message(cbor_det_t c)
{
  cose_untagged_message_ugly ite;
  if (COSE_Format_validate_cose_sign(c))
    ite =
      (
        (cose_untagged_message_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_cose_sign(c) }
        }
      );
  else
    ite =
      (
        (cose_untagged_message_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_cose_sign1(c) }
        }
      );
  return cose_untagged_message_right(ite);
}

/**
Serializer for cose_untagged_message
*/
size_t
COSE_Format_serialize_cose_untagged_message(
  COSE_Format_cose_untagged_message c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  cose_untagged_message_ugly scrut = cose_untagged_message_left(c);
  if (scrut.tag == COSE_Format_Inl)
    return COSE_Format_serialize_cose_sign(scrut.case_Inl, out);
  else if (scrut.tag == COSE_Format_Inr)
    return COSE_Format_serialize_cose_sign1(scrut.case_Inr, out);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option___COSE_Format_cose_untagged_message___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_untagged_message(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_untagged_message___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_untagged_message(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_untagged_message___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_untagged_message(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_untagged_message___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_cose_messages(cbor_det_t c)
{
  if (COSE_Format_validate_cose_untagged_message(c))
    return true;
  else
    return COSE_Format_validate_cose_tagged_message(c);
}

typedef struct cose_messages_ugly_s
{
  COSE_Format_evercddl_int_ugly_tags tag;
  union {
    COSE_Format_cose_untagged_message case_Inl;
    COSE_Format_cose_tagged_message case_Inr;
  }
  ;
}
cose_messages_ugly;

bool COSE_Format_uu___is_Mkcose_messages0(COSE_Format_cose_messages projectee)
{
  if (projectee.tag == COSE_Format_Mkcose_messages0)
    return true;
  else
    return false;
}

bool COSE_Format_uu___is_Mkcose_messages1(COSE_Format_cose_messages projectee)
{
  if (projectee.tag == COSE_Format_Mkcose_messages1)
    return true;
  else
    return false;
}

static COSE_Format_cose_messages cose_messages_right(cose_messages_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return
      (
        (COSE_Format_cose_messages){
          .tag = COSE_Format_Mkcose_messages0,
          { .case_Mkcose_messages0 = x2.case_Inl }
        }
      );
  else if (x2.tag == COSE_Format_Inr)
    return
      (
        (COSE_Format_cose_messages){
          .tag = COSE_Format_Mkcose_messages1,
          { .case_Mkcose_messages1 = x2.case_Inr }
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

static cose_messages_ugly cose_messages_left(COSE_Format_cose_messages x7)
{
  if (x7.tag == COSE_Format_Mkcose_messages0)
    return
      ((cose_messages_ugly){ .tag = COSE_Format_Inl, { .case_Inl = x7.case_Mkcose_messages0 } });
  else if (x7.tag == COSE_Format_Mkcose_messages1)
    return
      ((cose_messages_ugly){ .tag = COSE_Format_Inr, { .case_Inr = x7.case_Mkcose_messages1 } });
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
Parser for cose_messages
*/
COSE_Format_cose_messages COSE_Format_parse_cose_messages(cbor_det_t c)
{
  cose_messages_ugly ite;
  if (COSE_Format_validate_cose_untagged_message(c))
    ite =
      (
        (cose_messages_ugly){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_cose_untagged_message(c) }
        }
      );
  else
    ite =
      (
        (cose_messages_ugly){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_cose_tagged_message(c) }
        }
      );
  return cose_messages_right(ite);
}

/**
Serializer for cose_messages
*/
size_t
COSE_Format_serialize_cose_messages(
  COSE_Format_cose_messages c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  cose_messages_ugly scrut = cose_messages_left(c);
  if (scrut.tag == COSE_Format_Inl)
    return COSE_Format_serialize_cose_untagged_message(scrut.case_Inl, out);
  else if (scrut.tag == COSE_Format_Inr)
    return COSE_Format_serialize_cose_tagged_message(scrut.case_Inr, out);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option___COSE_Format_cose_messages___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cose_messages(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_cose_messages___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_cose_messages(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_messages___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cose_messages(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_cose_messages___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_internal_types(cbor_det_t c)
{
  return COSE_Format_validate_sig_structure(c);
}

bool COSE_Format_uu___is_Mkinternal_types0(COSE_Format_sig_structure projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

static COSE_Format_sig_structure internal_types_right(COSE_Format_sig_structure x1)
{
  return x1;
}

static COSE_Format_sig_structure internal_types_left(COSE_Format_sig_structure x3)
{
  return x3;
}

/**
Parser for internal_types
*/
COSE_Format_sig_structure COSE_Format_parse_internal_types(cbor_det_t c)
{
  return internal_types_right(COSE_Format_parse_sig_structure(c));
}

/**
Serializer for internal_types
*/
size_t
COSE_Format_serialize_internal_types(
  COSE_Format_sig_structure c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_sig_structure(internal_types_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_internal_types___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_internal_types(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_internal_types___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_internal_types(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_internal_types___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_internal_types(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_internal_types___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_start(cbor_det_t c)
{
  if (COSE_Format_validate_cose_messages(c))
    return true;
  else
    return COSE_Format_validate_internal_types(c);
}

typedef struct start_ugly_s
{
  COSE_Format_evercddl_int_ugly_tags tag;
  union {
    COSE_Format_cose_messages case_Inl;
    COSE_Format_sig_structure case_Inr;
  }
  ;
}
start_ugly;

bool COSE_Format_uu___is_Mkstart0(COSE_Format_start projectee)
{
  if (projectee.tag == COSE_Format_Mkstart0)
    return true;
  else
    return false;
}

bool COSE_Format_uu___is_Mkstart1(COSE_Format_start projectee)
{
  if (projectee.tag == COSE_Format_Mkstart1)
    return true;
  else
    return false;
}

static COSE_Format_start start_right(start_ugly x2)
{
  if (x2.tag == COSE_Format_Inl)
    return ((COSE_Format_start){ .tag = COSE_Format_Mkstart0, { .case_Mkstart0 = x2.case_Inl } });
  else if (x2.tag == COSE_Format_Inr)
    return ((COSE_Format_start){ .tag = COSE_Format_Mkstart1, { .case_Mkstart1 = x2.case_Inr } });
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static start_ugly start_left(COSE_Format_start x7)
{
  if (x7.tag == COSE_Format_Mkstart0)
    return ((start_ugly){ .tag = COSE_Format_Inl, { .case_Inl = x7.case_Mkstart0 } });
  else if (x7.tag == COSE_Format_Mkstart1)
    return ((start_ugly){ .tag = COSE_Format_Inr, { .case_Inr = x7.case_Mkstart1 } });
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
Parser for start
*/
COSE_Format_start COSE_Format_parse_start(cbor_det_t c)
{
  start_ugly ite;
  if (COSE_Format_validate_cose_messages(c))
    ite =
      ((start_ugly){ .tag = COSE_Format_Inl, { .case_Inl = COSE_Format_parse_cose_messages(c) } });
  else
    ite =
      ((start_ugly){ .tag = COSE_Format_Inr, { .case_Inr = COSE_Format_parse_internal_types(c) } });
  return start_right(ite);
}

/**
Serializer for start
*/
size_t COSE_Format_serialize_start(COSE_Format_start c, Pulse_Lib_Slice_slice__uint8_t out)
{
  start_ugly scrut = start_left(c);
  if (scrut.tag == COSE_Format_Inl)
    return COSE_Format_serialize_cose_messages(scrut.case_Inl, out);
  else if (scrut.tag == COSE_Format_Inr)
    return COSE_Format_serialize_internal_types(scrut.case_Inr, out);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option___COSE_Format_start___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_start(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  size_t len0 = cbor_det_validate(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(s), len);
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ scrut0;
  if (len0 == (size_t)0U)
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t scrut = split__uint8_t(s, len0);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = Pulse_Lib_Slice_len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .fst = cbor_det_parse(Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(input2), len1),
            .snd = rem
          }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_start___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_start(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_start___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_start(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_start___Pulse_Lib_Slice_slice_uint8_t_){
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


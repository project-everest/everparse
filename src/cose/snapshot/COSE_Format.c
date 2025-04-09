

#include "COSE_Format.h"

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

static bool evercddl_bool_pretty_right(bool x1)
{
  return x1;
}

static bool evercddl_bool_pretty_left(bool x3)
{
  return x3;
}

/**
Parser for evercddl_bool
*/
bool COSE_Format_parse_bool(cbor_det_t c)
{
  return evercddl_bool_pretty_right(cbor_det_read_simple_value(c) == SIMPLE_VALUE_TRUE);
}

static size_t len__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.len;
}

static uint8_t *slice_to_arrayptr_intro__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
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
  if (evercddl_bool_pretty_left(c))
    if
    (
      SIMPLE_VALUE_TRUE <= MAX_SIMPLE_VALUE_ADDITIONAL_INFO ||
        MIN_SIMPLE_VALUE_LONG_ARGUMENT <= SIMPLE_VALUE_TRUE
    )
    {
      cbor_det_t x = cbor_det_mk_simple_value(SIMPLE_VALUE_TRUE);
      size_t len = cbor_det_size(x, len__uint8_t(out));
      option__size_t scrut;
      if (len > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(x, slice_to_arrayptr_intro__uint8_t(out), len)
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
    size_t len = cbor_det_size(x, len__uint8_t(out));
    option__size_t scrut;
    if (len > (size_t)0U)
      scrut =
        (
          (option__size_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = cbor_det_serialize(x, slice_to_arrayptr_intro__uint8_t(out), len)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_bool_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_bool(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_bool_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bool_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_bool(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bool_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_everparsenomatch_pretty
evercddl_everparsenomatch_pretty_right(void)
{
  return COSE_Format_Mkevercddl_everparsenomatch_pretty0;
}

/**
Parser for evercddl_everparsenomatch
*/
COSE_Format_evercddl_everparsenomatch_pretty COSE_Format_parse_everparsenomatch(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return evercddl_everparsenomatch_pretty_right();
}

/**
Serializer for evercddl_everparsenomatch
*/
size_t
COSE_Format_serialize_everparsenomatch(
  COSE_Format_evercddl_everparsenomatch_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  KRML_MAYBE_UNUSED_VAR(out);
  return (size_t)0U;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_everparsenomatch_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_everparsenomatch(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_everparsenomatch_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_everparsenomatch_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_everparsenomatch(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_everparsenomatch_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static uint64_t evercddl_uint_pretty_right(uint64_t x1)
{
  return x1;
}

static uint64_t evercddl_uint_pretty_left(uint64_t x3)
{
  return x3;
}

/**
Parser for evercddl_uint
*/
uint64_t COSE_Format_parse_uint(cbor_det_t c)
{
  return evercddl_uint_pretty_right(cbor_det_read_uint64(c));
}

/**
Serializer for evercddl_uint
*/
size_t COSE_Format_serialize_uint(uint64_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t x = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, evercddl_uint_pretty_left(c));
  size_t len = cbor_det_size(x, len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(x, slice_to_arrayptr_intro__uint8_t(out), len)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_uint_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_uint(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_uint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_uint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_uint(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_uint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static uint64_t evercddl_nint_pretty_right(uint64_t x1)
{
  return x1;
}

static uint64_t evercddl_nint_pretty_left(uint64_t x3)
{
  return x3;
}

/**
Parser for evercddl_nint
*/
uint64_t COSE_Format_parse_nint(cbor_det_t c)
{
  return evercddl_nint_pretty_right(cbor_det_read_uint64(c));
}

/**
Serializer for evercddl_nint
*/
size_t COSE_Format_serialize_nint(uint64_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t x = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, evercddl_nint_pretty_left(c));
  size_t len = cbor_det_size(x, len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(x, slice_to_arrayptr_intro__uint8_t(out), len)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_nint_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_nint(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_nint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_nint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_nint(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_nint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

typedef struct evercddl_int_s
{
  COSE_Format_evercddl_int_tags tag;
  union {
    uint64_t case_Inl;
    uint64_t case_Inr;
  }
  ;
}
evercddl_int;

static COSE_Format_evercddl_int_pretty evercddl_int_pretty_right(evercddl_int x2)
{
  if (x2.tag == COSE_Format_Inl)
  {
    uint64_t x3 = x2.case_Inl;
    return
      (
        (COSE_Format_evercddl_int_pretty){
          .tag = COSE_Format_Mkevercddl_int_pretty0,
          { .case_Mkevercddl_int_pretty0 = x3 }
        }
      );
  }
  else if (x2.tag == COSE_Format_Inr)
  {
    uint64_t x4 = x2.case_Inr;
    return
      (
        (COSE_Format_evercddl_int_pretty){
          .tag = COSE_Format_Mkevercddl_int_pretty1,
          { .case_Mkevercddl_int_pretty1 = x4 }
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

static evercddl_int evercddl_int_pretty_left(COSE_Format_evercddl_int_pretty x7)
{
  if (x7.tag == COSE_Format_Mkevercddl_int_pretty0)
  {
    uint64_t x10 = x7.case_Mkevercddl_int_pretty0;
    return ((evercddl_int){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_int_pretty1)
  {
    uint64_t x12 = x7.case_Mkevercddl_int_pretty1;
    return ((evercddl_int){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

/**
Parser for evercddl_int
*/
COSE_Format_evercddl_int_pretty COSE_Format_parse_int(cbor_det_t c)
{
  evercddl_int ite;
  if (COSE_Format_validate_uint(c))
    ite = ((evercddl_int){ .tag = COSE_Format_Inl, { .case_Inl = COSE_Format_parse_uint(c) } });
  else
    ite = ((evercddl_int){ .tag = COSE_Format_Inr, { .case_Inr = COSE_Format_parse_nint(c) } });
  return evercddl_int_pretty_right(ite);
}

/**
Serializer for evercddl_int
*/
size_t
COSE_Format_serialize_int(
  COSE_Format_evercddl_int_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  evercddl_int scrut = evercddl_int_pretty_left(c);
  if (scrut.tag == COSE_Format_Inl)
  {
    uint64_t c1 = scrut.case_Inl;
    return COSE_Format_serialize_uint(c1, out);
  }
  else if (scrut.tag == COSE_Format_Inr)
  {
    uint64_t c2 = scrut.case_Inr;
    return COSE_Format_serialize_nint(c2, out);
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_int_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_int(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_int_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_int_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_int(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_int_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_bstr evercddl_bstr_pretty_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t evercddl_bstr_pretty_left(COSE_Format_evercddl_bstr x3)
{
  return x3;
}

static Pulse_Lib_Slice_slice__uint8_t arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

/**
Parser for evercddl_bstr
*/
COSE_Format_evercddl_bstr COSE_Format_parse_bstr(cbor_det_t c)
{
  uint64_t len = cbor_det_get_string_length(c);
  return
    evercddl_bstr_pretty_right(arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c),
        (size_t)len));
}

/**
Serializer for evercddl_bstr
*/
size_t
COSE_Format_serialize_bstr(COSE_Format_evercddl_bstr c, Pulse_Lib_Slice_slice__uint8_t out)
{
  Pulse_Lib_Slice_slice__uint8_t c_ = evercddl_bstr_pretty_left(c);
  if (len__uint8_t(c_) <= (size_t)18446744073709551615ULL)
  {
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(c_);
    cbor_det_t
    x =
      cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_BYTE_STRING,
        a,
        (uint64_t)len__uint8_t(c_));
    size_t len1 = cbor_det_size(x, len__uint8_t(out));
    option__size_t scrut;
    if (len1 > (size_t)0U)
      scrut =
        (
          (option__size_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = cbor_det_serialize(x, slice_to_arrayptr_intro__uint8_t(out), len1)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_bstr_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_bstr(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_bstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_bstr(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_bstr_pretty
evercddl_encodedcbor_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

static COSE_Format_evercddl_bstr
evercddl_encodedcbor_pretty_left(COSE_Format_evercddl_bstr_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_encodedcbor
*/
COSE_Format_evercddl_bstr_pretty COSE_Format_parse_encodedcbor(cbor_det_t c)
{
  return
    evercddl_encodedcbor_pretty_right(COSE_Format_parse_bstr(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_encodedcbor
*/
size_t
COSE_Format_serialize_encodedcbor(
  COSE_Format_evercddl_bstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 24ULL;
  COSE_Format_evercddl_bstr cpayload = evercddl_encodedcbor_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_bstr(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_encodedcbor_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_encodedcbor(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_encodedcbor_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_encodedcbor_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_encodedcbor(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_encodedcbor_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_bstr_pretty
evercddl_bytes_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

static COSE_Format_evercddl_bstr
evercddl_bytes_pretty_left(COSE_Format_evercddl_bstr_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_bytes
*/
COSE_Format_evercddl_bstr_pretty COSE_Format_parse_bytes(cbor_det_t c)
{
  return evercddl_bytes_pretty_right(COSE_Format_parse_bstr(c));
}

/**
Serializer for evercddl_bytes
*/
size_t
COSE_Format_serialize_bytes(
  COSE_Format_evercddl_bstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_bstr(evercddl_bytes_pretty_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_bytes_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_bytes(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_bytes_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bytes_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_bytes(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bytes_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_bstr evercddl_tstr_pretty_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

static Pulse_Lib_Slice_slice__uint8_t evercddl_tstr_pretty_left(COSE_Format_evercddl_bstr x3)
{
  return x3;
}

/**
Parser for evercddl_tstr
*/
COSE_Format_evercddl_bstr COSE_Format_parse_tstr(cbor_det_t c)
{
  uint64_t len = cbor_det_get_string_length(c);
  return
    evercddl_tstr_pretty_right(arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c),
        (size_t)len));
}

/**
Serializer for evercddl_tstr
*/
size_t
COSE_Format_serialize_tstr(COSE_Format_evercddl_bstr c, Pulse_Lib_Slice_slice__uint8_t out)
{
  Pulse_Lib_Slice_slice__uint8_t c_ = evercddl_tstr_pretty_left(c);
  if (len__uint8_t(c_) <= (size_t)18446744073709551615ULL)
  {
    size_t alen = len__uint8_t(c_);
    if (cbor_det_impl_utf8_correct_from_array(slice_to_arrayptr_intro__uint8_t(c_), alen))
    {
      uint8_t *a = slice_to_arrayptr_intro__uint8_t(c_);
      cbor_det_t
      x =
        cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
          a,
          (uint64_t)len__uint8_t(c_));
      size_t len1 = cbor_det_size(x, len__uint8_t(out));
      option__size_t scrut;
      if (len1 > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(x, slice_to_arrayptr_intro__uint8_t(out), len1)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_tstr_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_tstr(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_tstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_tstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_tstr(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_tstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_label_pretty
evercddl_label_pretty_right(COSE_Format_evercddl_label x2)
{
  if (x2.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_int_pretty x3 = x2.case_Inl;
    return
      (
        (COSE_Format_evercddl_label_pretty){
          .tag = COSE_Format_Mkevercddl_label_pretty0,
          { .case_Mkevercddl_label_pretty0 = x3 }
        }
      );
  }
  else if (x2.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_bstr x4 = x2.case_Inr;
    return
      (
        (COSE_Format_evercddl_label_pretty){
          .tag = COSE_Format_Mkevercddl_label_pretty1,
          { .case_Mkevercddl_label_pretty1 = x4 }
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

static COSE_Format_evercddl_label
evercddl_label_pretty_left(COSE_Format_evercddl_label_pretty x7)
{
  if (x7.tag == COSE_Format_Mkevercddl_label_pretty0)
  {
    COSE_Format_evercddl_int_pretty x10 = x7.case_Mkevercddl_label_pretty0;
    return ((COSE_Format_evercddl_label){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_label_pretty1)
  {
    COSE_Format_evercddl_bstr x12 = x7.case_Mkevercddl_label_pretty1;
    return ((COSE_Format_evercddl_label){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

/**
Parser for evercddl_label
*/
COSE_Format_evercddl_label_pretty COSE_Format_parse_label(cbor_det_t c)
{
  COSE_Format_evercddl_label ite;
  if (COSE_Format_validate_int(c))
    ite =
      (
        (COSE_Format_evercddl_label){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_int(c) }
        }
      );
  else
    ite =
      (
        (COSE_Format_evercddl_label){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_tstr(c) }
        }
      );
  return evercddl_label_pretty_right(ite);
}

/**
Serializer for evercddl_label
*/
size_t
COSE_Format_serialize_label(
  COSE_Format_evercddl_label_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_label scrut = evercddl_label_pretty_left(c);
  if (scrut.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_int_pretty c1 = scrut.case_Inl;
    return COSE_Format_serialize_int(c1, out);
  }
  else if (scrut.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_bstr c2 = scrut.case_Inr;
    return COSE_Format_serialize_tstr(c2, out);
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_label_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_label(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_label_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_label_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_label(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_label_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_tstr_pretty
evercddl_tdate_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

static COSE_Format_evercddl_bstr
evercddl_tdate_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_tdate
*/
COSE_Format_evercddl_tstr_pretty COSE_Format_parse_tdate(cbor_det_t c)
{
  return evercddl_tdate_pretty_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_tdate
*/
size_t
COSE_Format_serialize_tdate(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 0ULL;
  COSE_Format_evercddl_bstr cpayload = evercddl_tdate_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_tdate_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_tdate(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_tdate_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_tdate_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_tdate(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_tdate_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_tstr_pretty evercddl_uri_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

static COSE_Format_evercddl_bstr evercddl_uri_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_uri
*/
COSE_Format_evercddl_tstr_pretty COSE_Format_parse_uri(cbor_det_t c)
{
  return evercddl_uri_pretty_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_uri
*/
size_t
COSE_Format_serialize_uri(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 32ULL;
  COSE_Format_evercddl_bstr cpayload = evercddl_uri_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_uri_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_uri(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_uri_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_uri_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_uri(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_uri_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_tstr_pretty
evercddl_b64url_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

static COSE_Format_evercddl_bstr
evercddl_b64url_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_b64url
*/
COSE_Format_evercddl_tstr_pretty COSE_Format_parse_b64url(cbor_det_t c)
{
  return evercddl_b64url_pretty_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_b64url
*/
size_t
COSE_Format_serialize_b64url(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 33ULL;
  COSE_Format_evercddl_bstr cpayload = evercddl_b64url_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_b64url_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_b64url(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_b64url(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_tstr_pretty
evercddl_b64legacy_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

static COSE_Format_evercddl_bstr
evercddl_b64legacy_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_b64legacy
*/
COSE_Format_evercddl_tstr_pretty COSE_Format_parse_b64legacy(cbor_det_t c)
{
  return evercddl_b64legacy_pretty_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_b64legacy
*/
size_t
COSE_Format_serialize_b64legacy(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 34ULL;
  COSE_Format_evercddl_bstr cpayload = evercddl_b64legacy_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_b64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_b64legacy(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_b64legacy(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_tstr_pretty
evercddl_regexp_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

static COSE_Format_evercddl_bstr
evercddl_regexp_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_regexp
*/
COSE_Format_evercddl_tstr_pretty COSE_Format_parse_regexp(cbor_det_t c)
{
  return evercddl_regexp_pretty_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_regexp
*/
size_t
COSE_Format_serialize_regexp(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 35ULL;
  COSE_Format_evercddl_bstr cpayload = evercddl_regexp_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_regexp_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_regexp(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_regexp_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_regexp_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_regexp(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_regexp_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_tstr_pretty
evercddl_mimemessage_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

static COSE_Format_evercddl_bstr
evercddl_mimemessage_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_mimemessage
*/
COSE_Format_evercddl_tstr_pretty COSE_Format_parse_mimemessage(cbor_det_t c)
{
  return
    evercddl_mimemessage_pretty_right(COSE_Format_parse_tstr(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_mimemessage
*/
size_t
COSE_Format_serialize_mimemessage(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 36ULL;
  COSE_Format_evercddl_bstr cpayload = evercddl_mimemessage_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_mimemessage_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_mimemessage(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_mimemessage_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_mimemessage_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_mimemessage(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_mimemessage_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_tstr_pretty
evercddl_text_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

static COSE_Format_evercddl_bstr evercddl_text_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_text
*/
COSE_Format_evercddl_tstr_pretty COSE_Format_parse_text(cbor_det_t c)
{
  return evercddl_text_pretty_right(COSE_Format_parse_tstr(c));
}

/**
Serializer for evercddl_text
*/
size_t
COSE_Format_serialize_text(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_tstr(evercddl_text_pretty_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_text_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_text(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_text_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_text_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_text(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_text_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_false_pretty evercddl_false_pretty_right(void)
{
  return COSE_Format_Mkevercddl_false_pretty0;
}

/**
Parser for evercddl_false
*/
COSE_Format_evercddl_false_pretty COSE_Format_parse_false(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return evercddl_false_pretty_right();
}

/**
Serializer for evercddl_false
*/
size_t
COSE_Format_serialize_false(
  COSE_Format_evercddl_false_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  cbor_det_t c1 = cbor_det_mk_simple_value(20U);
  size_t len = cbor_det_size(c1, len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c1, slice_to_arrayptr_intro__uint8_t(out), len)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_false_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_false(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_false_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_false_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_false(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_false_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_true_pretty evercddl_true_pretty_right(void)
{
  return COSE_Format_Mkevercddl_true_pretty0;
}

/**
Parser for evercddl_true
*/
COSE_Format_evercddl_true_pretty COSE_Format_parse_true(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return evercddl_true_pretty_right();
}

/**
Serializer for evercddl_true
*/
size_t
COSE_Format_serialize_true(
  COSE_Format_evercddl_true_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  cbor_det_t c1 = cbor_det_mk_simple_value(21U);
  size_t len = cbor_det_size(c1, len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c1, slice_to_arrayptr_intro__uint8_t(out), len)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_true_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_true(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_true_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_true_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_true(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_true_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_nil_pretty evercddl_nil_pretty_right(void)
{
  return COSE_Format_Mkevercddl_nil_pretty0;
}

/**
Parser for evercddl_nil
*/
COSE_Format_evercddl_nil_pretty COSE_Format_parse_nil(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return evercddl_nil_pretty_right();
}

/**
Serializer for evercddl_nil
*/
size_t
COSE_Format_serialize_nil(
  COSE_Format_evercddl_nil_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  cbor_det_t c1 = cbor_det_mk_simple_value(22U);
  size_t len = cbor_det_size(c1, len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c1, slice_to_arrayptr_intro__uint8_t(out), len)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_nil_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_nil(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_nil_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_nil_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_nil(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_nil_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_nil_pretty
evercddl_null_pretty_right(COSE_Format_evercddl_nil_pretty x1)
{
  return x1;
}

static COSE_Format_evercddl_nil_pretty
evercddl_null_pretty_left(COSE_Format_evercddl_nil_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_null
*/
COSE_Format_evercddl_nil_pretty COSE_Format_parse_null(cbor_det_t c)
{
  return evercddl_null_pretty_right(COSE_Format_parse_nil(c));
}

/**
Serializer for evercddl_null
*/
size_t
COSE_Format_serialize_null(
  COSE_Format_evercddl_nil_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_nil(evercddl_null_pretty_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_null_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_null(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_null_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_null_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_null(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_null_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_undefined_pretty evercddl_undefined_pretty_right(void)
{
  return COSE_Format_Mkevercddl_undefined_pretty0;
}

/**
Parser for evercddl_undefined
*/
COSE_Format_evercddl_undefined_pretty COSE_Format_parse_undefined(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  return evercddl_undefined_pretty_right();
}

/**
Serializer for evercddl_undefined
*/
size_t
COSE_Format_serialize_undefined(
  COSE_Format_evercddl_undefined_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  cbor_det_t c1 = cbor_det_mk_simple_value(23U);
  size_t len = cbor_det_size(c1, len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c1, slice_to_arrayptr_intro__uint8_t(out), len)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_undefined_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_undefined(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_undefined_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_undefined_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_undefined(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_undefined_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_any evercddl_any_pretty_right(cbor_det_t x1)
{
  return x1;
}

static cbor_det_t evercddl_any_pretty_left(COSE_Format_evercddl_any x3)
{
  return x3;
}

/**
Parser for evercddl_any
*/
COSE_Format_evercddl_any COSE_Format_parse_any(cbor_det_t c)
{
  return evercddl_any_pretty_right(c);
}

/**
Serializer for evercddl_any
*/
size_t
COSE_Format_serialize_any(COSE_Format_evercddl_any c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t c_ = evercddl_any_pretty_left(c);
  size_t len = cbor_det_size(c_, len__uint8_t(out));
  option__size_t scrut;
  if (len > (size_t)0U)
    scrut =
      (
        (option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = cbor_det_serialize(c_, slice_to_arrayptr_intro__uint8_t(out), len)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_any_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_any(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_any_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_any_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_any(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_any_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_any_pretty
evercddl_values_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

static COSE_Format_evercddl_any evercddl_values_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_values
*/
COSE_Format_evercddl_any_pretty COSE_Format_parse_values(cbor_det_t c)
{
  return evercddl_values_pretty_right(COSE_Format_parse_any(c));
}

/**
Serializer for evercddl_values
*/
size_t
COSE_Format_serialize_values(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_any(evercddl_values_pretty_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_values_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_values(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_values_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_values_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_values(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_values_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_aux_env25_validate_1(cbor_det_array_iterator_t *pi)
{
  if (cbor_det_array_iterator_is_empty(*pi))
    return false;
  else
    return COSE_Format_validate_label(cbor_det_array_iterator_next(pi));
}

static COSE_Format_evercddl_label_pretty
aux_env25_type_1_pretty_right(COSE_Format_evercddl_label_pretty x1)
{
  return x1;
}

static COSE_Format_evercddl_label_pretty
aux_env25_type_1_pretty_left(COSE_Format_evercddl_label_pretty x3)
{
  return x3;
}

/**
Parser for aux_env25_type_1
*/
COSE_Format_evercddl_label_pretty COSE_Format_aux_env25_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t buf = c;
  return
    aux_env25_type_1_pretty_right(COSE_Format_parse_label(cbor_det_array_iterator_next(&buf)));
}

/**
Serializer for aux_env25_type_1
*/
bool
COSE_Format_aux_env25_serialize_1(
  COSE_Format_evercddl_label_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  COSE_Format_evercddl_label_pretty c_ = aux_env25_type_1_pretty_left(c);
  uint64_t count = *out_count;
  if (count < 18446744073709551615ULL)
  {
    size_t size = *out_size;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
    size_t size1 = COSE_Format_serialize_label(c_, out1);
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

bool (*COSE_Format_aux_env25_validate_2)(cbor_det_t x0) = COSE_Format_validate_label;

static COSE_Format_evercddl_label_pretty
aux_env25_type_2_pretty_right(COSE_Format_evercddl_label_pretty x1)
{
  return x1;
}

static COSE_Format_evercddl_label_pretty
aux_env25_type_2_pretty_left(COSE_Format_evercddl_label_pretty x3)
{
  return x3;
}

/**
Parser for aux_env25_type_2
*/
COSE_Format_evercddl_label_pretty COSE_Format_aux_env25_parse_2(cbor_det_t c)
{
  return aux_env25_type_2_pretty_right(COSE_Format_parse_label(c));
}

/**
Serializer for aux_env25_type_2
*/
size_t
COSE_Format_aux_env25_serialize_2(
  COSE_Format_evercddl_label_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_label(aux_env25_type_2_pretty_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_aux_env25_type_2_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_aux_env25_parse_2(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_aux_env25_type_2_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_aux_env25_validate_2(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_aux_env25_type_2_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_aux_env25_parse_2(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_aux_env25_type_2_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_aux_env25_validate_3(cbor_det_t c)
{
  bool ite0;
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_UINT64)
    ite0 = cbor_det_read_uint64(c) == 1ULL;
  else
    ite0 = false;
  bool ite1;
  if (ite0)
    ite1 = true;
  else if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_UINT64)
    ite1 = cbor_det_read_uint64(c) == 2ULL;
  else
    ite1 = false;
  bool ite2;
  if (ite1)
    ite2 = true;
  else if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_UINT64)
    ite2 = cbor_det_read_uint64(c) == 3ULL;
  else
    ite2 = false;
  bool ite3;
  if (ite2)
    ite3 = true;
  else if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_UINT64)
    ite3 = cbor_det_read_uint64(c) == 4ULL;
  else
    ite3 = false;
  bool ite;
  if (ite3)
    ite = true;
  else if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_UINT64)
    ite = cbor_det_read_uint64(c) == 5ULL;
  else
    ite = false;
  if (ite)
    return true;
  else if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_UINT64)
    return cbor_det_read_uint64(c) == 6ULL;
  else
    return false;
}

bool (*COSE_Format_aux_env25_validate_4)(cbor_det_t x0) = COSE_Format_validate_values;

static COSE_Format_evercddl_values_pretty
aux_env25_type_4_pretty_right(COSE_Format_evercddl_any_pretty x1)
{
  return x1;
}

static COSE_Format_evercddl_any_pretty
aux_env25_type_4_pretty_left(COSE_Format_evercddl_values_pretty x3)
{
  return x3;
}

/**
Parser for aux_env25_type_4
*/
COSE_Format_evercddl_values_pretty COSE_Format_aux_env25_parse_4(cbor_det_t c)
{
  return aux_env25_type_4_pretty_right(COSE_Format_parse_values(c));
}

/**
Serializer for aux_env25_type_4
*/
size_t
COSE_Format_aux_env25_serialize_4(
  COSE_Format_evercddl_values_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_values(aux_env25_type_4_pretty_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_aux_env25_type_4_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_aux_env25_parse_4(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_aux_env25_type_4_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_aux_env25_validate_4(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_aux_env25_type_4_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_aux_env25_parse_4(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_aux_env25_type_4_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

typedef struct option__CBOR_Pulse_API_Det_Type_cbor_det_t_s
{
  FStar_Pervasives_Native_option__size_t_tags tag;
  cbor_det_t v;
}
option__CBOR_Pulse_API_Det_Type_cbor_det_t;

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
              ite0 = MGCutFail;
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
              ite0 = MGCutFail;
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
          {
            cbor_det_t cv = scrut.v;
            if (COSE_Format_validate_bstr(cv))
            {
              remaining = remaining - 1ULL;
              ite = MGOK;
            }
            else
              ite = MGCutFail;
          }
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
          {
            cbor_det_t cv = scrut0.v;
            if (COSE_Format_validate_bstr(cv))
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
                {
                  cbor_det_t cv = scrut.v;
                  if (COSE_Format_validate_everparsenomatch(cv))
                  {
                    remaining = remaining - 1ULL;
                    ite = MGOK;
                  }
                  else
                    ite = MGCutFail;
                }
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
                {
                  cbor_det_t cv = scrut0.v;
                  if (COSE_Format_validate_bstr(cv))
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
                      {
                        cbor_det_t cv = scrut.v;
                        if (COSE_Format_validate_everparsenomatch(cv))
                        {
                          remaining = remaining - 1ULL;
                          ite = MGOK;
                        }
                        else
                          ite = MGCutFail;
                      }
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
                      {
                        cbor_det_t cv = scrut0.v;
                        if (COSE_Format_validate_everparsenomatch(cv))
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
                            {
                              cbor_det_t cv = scrut.v;
                              if (COSE_Format_validate_everparsenomatch(cv))
                              {
                                remaining = remaining - 1ULL;
                                ite = MGOK;
                              }
                              else
                                ite = MGCutFail;
                            }
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
            cbor_det_t k = cbor_det_map_entry_key(chd);
            bool ite0;
            if (COSE_Format_validate_label(k))
            {
              bool ite1;
              if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                ite1 = cbor_det_read_uint64(k) == 1ULL;
              else
                ite1 = false;
              bool ite2;
              if (ite1)
                ite2 = true;
              else if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                ite2 = cbor_det_read_uint64(k) == 2ULL;
              else
                ite2 = false;
              bool ite3;
              if (ite2)
                ite3 = true;
              else if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                ite3 = cbor_det_read_uint64(k) == 3ULL;
              else
                ite3 = false;
              bool ite4;
              if (ite3)
                ite4 = true;
              else if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                ite4 = cbor_det_read_uint64(k) == 4ULL;
              else
                ite4 = false;
              bool ite5;
              if (ite4)
                ite5 = true;
              else if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                ite5 = cbor_det_read_uint64(k) == 5ULL;
              else
                ite5 = false;
              bool ite;
              if (ite5)
                ite = true;
              else if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                ite = cbor_det_read_uint64(k) == 6ULL;
              else
                ite = false;
              ite0 = !ite;
            }
            else
              ite0 = false;
            bool ite;
            if (ite0)
              ite = COSE_Format_validate_values(cbor_det_map_entry_value(chd));
            else
              ite = false;
            if (!!ite)
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
__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty_s
{
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
  fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
  snd;
}
__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty;

typedef struct
___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty_s
{
  __FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
  fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  snd;
}
___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty;

typedef struct
____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty_s
{
  ___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  fst;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty snd;
}
____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty;

typedef struct
_____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__s
{
  ____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  fst;
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  snd;
}
_____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_;

typedef struct evercddl_header_map_s
{
  _____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  snd;
}
evercddl_header_map;

static COSE_Format_evercddl_header_map_pretty
evercddl_header_map_pretty_right(evercddl_header_map x6)
{
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  x12 = x6.snd;
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  x11 = x6.fst.snd;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x10 = x6.fst.fst.snd;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  x9 = x6.fst.fst.fst.snd;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
  x8 = x6.fst.fst.fst.fst.snd;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
  x7 = x6.fst.fst.fst.fst.fst;
  return
    (
      (COSE_Format_evercddl_header_map_pretty){
        ._x0 = x7,
        ._x1 = x8,
        ._x2 = x9,
        ._x3 = x10,
        ._x4 = x11,
        ._x5 = x12
      }
    );
}

static evercddl_header_map
evercddl_header_map_pretty_left(COSE_Format_evercddl_header_map_pretty x13)
{
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
  x21 = x13._x0;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
  x22 = x13._x1;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  x23 = x13._x2;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x24 = x13._x3;
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  x25 = x13._x4;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  x26 = x13._x5;
  return
    (
      (evercddl_header_map){
        .fst = {
          .fst = { .fst = { .fst = { .fst = x21, .snd = x22 }, .snd = x23 }, .snd = x24 },
          .snd = x25
        },
        .snd = x26
      }
    );
}

/**
Parser for evercddl_header_map
*/
COSE_Format_evercddl_header_map_pretty COSE_Format_parse_header_map(cbor_det_t c)
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
      ite0 = MGCutFail;
  }
  else
    ite0 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
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
    COSE_Format_evercddl_label ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      if (COSE_Format_validate_int(w))
        ite =
          (
            (COSE_Format_evercddl_label){
              .tag = COSE_Format_Inl,
              { .case_Inl = COSE_Format_parse_int(w) }
            }
          );
      else
        ite =
          (
            (COSE_Format_evercddl_label){
              .tag = COSE_Format_Inr,
              { .case_Inr = COSE_Format_parse_tstr(w) }
            }
          );
    }
    else
      ite =
        KRML_EABORT(COSE_Format_evercddl_label,
          "unreachable (pattern matches are exhaustive in F*)");
    w1 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    w1 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty){
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
      ite1 = MGCutFail;
  }
  else
    ite1 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
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
    FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
    ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      ite =
        (
          (FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty){
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_array_iterator_contents = cbor_det_array_iterator_start(w),
                .cddl_array_iterator_impl_validate = COSE_Format_aux_env25_validate_1,
                .cddl_array_iterator_impl_parse = COSE_Format_aux_env25_parse_1
              }
            }
          }
        );
    }
    else
      ite =
        KRML_EABORT(FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty,
          "unreachable (pattern matches are exhaustive in F*)");
    ite2 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite2 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  __FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
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
      ite3 = MGCutFail;
  }
  else
    ite3 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
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
    FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      if (COSE_Format_validate_tstr(w))
        ite =
          (
            (FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty){
              .tag = COSE_Format_Inl,
              { .case_Inl = COSE_Format_parse_tstr(w) }
            }
          );
      else
        ite =
          (
            (FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty){
              .tag = COSE_Format_Inr,
              { .case_Inr = COSE_Format_parse_int(w) }
            }
          );
    }
    else
      ite =
        KRML_EABORT(FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty,
          "unreachable (pattern matches are exhaustive in F*)");
    ite4 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite4 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  ___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
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
  {
    cbor_det_t cv = scrut3.v;
    if (COSE_Format_validate_bstr(cv))
      ite5 = MGOK;
    else
      ite5 = MGCutFail;
  }
  else
    ite5 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty ite6;
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
    COSE_Format_evercddl_bstr ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      ite = COSE_Format_parse_bstr(w);
    }
    else
      ite =
        KRML_EABORT(COSE_Format_evercddl_bstr,
          "unreachable (pattern matches are exhaustive in F*)");
    ite6 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite6 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  ____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
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
  {
    cbor_det_t cv = scrut4.v;
    if (COSE_Format_validate_bstr(cv))
      ite7 = MGOK;
    else
      ite7 = MGFail;
  }
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
        {
          cbor_det_t cv = scrut.v;
          if (COSE_Format_validate_everparsenomatch(cv))
            ite = MGOK;
          else
            ite = MGCutFail;
        }
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
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
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
    COSE_Format_evercddl_bstr w11;
    if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut0.v;
      w11 = COSE_Format_parse_bstr(w);
    }
    else
      w11 =
        KRML_EABORT(COSE_Format_evercddl_bstr,
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
    {
      cbor_det_t cv = scrut1.v;
      if (COSE_Format_validate_everparsenomatch(cv))
        ite0 = MGOK;
      else
        ite0 = MGCutFail;
    }
    else
      ite0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty ite1;
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
      COSE_Format_evercddl_everparsenomatch_pretty ite;
      if (scrut.tag == FStar_Pervasives_Native_Some)
      {
        cbor_det_t w = scrut.v;
        ite = COSE_Format_parse_everparsenomatch(w);
      }
      else
        ite =
          KRML_EABORT(COSE_Format_evercddl_everparsenomatch_pretty,
            "unreachable (pattern matches are exhaustive in F*)");
      ite1 =
        (
          (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
            .tag = FStar_Pervasives_Native_Some,
            .v = ite
          }
        );
    }
    else
      ite1 =
        (
          (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
            .tag = FStar_Pervasives_Native_None
          }
        );
    ite8 =
      (
        (FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_){
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
    {
      cbor_det_t cv = scrut0.v;
      if (COSE_Format_validate_bstr(cv))
        ite0 = MGOK;
      else
        ite0 = MGFail;
    }
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
          {
            cbor_det_t cv = scrut.v;
            if (COSE_Format_validate_everparsenomatch(cv))
              ite = MGOK;
            else
              ite = MGCutFail;
          }
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
    FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
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
      COSE_Format_evercddl_bstr w11;
      if (scrut0.tag == FStar_Pervasives_Native_Some)
      {
        cbor_det_t w = scrut0.v;
        w11 = COSE_Format_parse_bstr(w);
      }
      else
        w11 =
          KRML_EABORT(COSE_Format_evercddl_bstr,
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
      {
        cbor_det_t cv = scrut1.v;
        if (COSE_Format_validate_everparsenomatch(cv))
          ite0 = MGOK;
        else
          ite0 = MGCutFail;
      }
      else
        ite0 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty ite2;
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
        COSE_Format_evercddl_everparsenomatch_pretty ite;
        if (scrut.tag == FStar_Pervasives_Native_Some)
        {
          cbor_det_t w = scrut.v;
          ite = COSE_Format_parse_everparsenomatch(w);
        }
        else
          ite =
            KRML_EABORT(COSE_Format_evercddl_everparsenomatch_pretty,
              "unreachable (pattern matches are exhaustive in F*)");
        ite2 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_Some,
              .v = ite
            }
          );
      }
      else
        ite2 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_None
            }
          );
      ite1 =
        (
          (FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_){
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
      {
        cbor_det_t cv = scrut0.v;
        if (COSE_Format_validate_everparsenomatch(cv))
          ite0 = MGOK;
        else
          ite0 = MGCutFail;
      }
      else
        ite0 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty w11;
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
        COSE_Format_evercddl_everparsenomatch_pretty ite;
        if (scrut.tag == FStar_Pervasives_Native_Some)
        {
          cbor_det_t w = scrut.v;
          ite = COSE_Format_parse_everparsenomatch(w);
        }
        else
          ite =
            KRML_EABORT(COSE_Format_evercddl_everparsenomatch_pretty,
              "unreachable (pattern matches are exhaustive in F*)");
        w11 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_Some,
              .v = ite
            }
          );
      }
      else
        w11 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
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
      {
        cbor_det_t cv = scrut1.v;
        if (COSE_Format_validate_everparsenomatch(cv))
          ite2 = MGOK;
        else
          ite2 = MGCutFail;
      }
      else
        ite2 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty ite3;
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
        COSE_Format_evercddl_everparsenomatch_pretty ite;
        if (scrut.tag == FStar_Pervasives_Native_Some)
        {
          cbor_det_t w = scrut.v;
          ite = COSE_Format_parse_everparsenomatch(w);
        }
        else
          ite =
            KRML_EABORT(COSE_Format_evercddl_everparsenomatch_pretty,
              "unreachable (pattern matches are exhaustive in F*)");
        ite3 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_Some,
              .v = ite
            }
          );
      }
      else
        ite3 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_None
            }
          );
      ite1 =
        (
          (FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_){
            .tag = COSE_Format_Inr,
            { .case_Inr = { .fst = w11, .snd = ite3 } }
          }
        );
    }
    ite8 =
      (
        (FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_){
          .tag = COSE_Format_Inr,
          { .case_Inr = ite1 }
        }
      );
  }
  _____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  w11 = { .fst = w13, .snd = ite8 };
  return
    evercddl_header_map_pretty_right((
        (evercddl_header_map){
          .fst = w11,
          .snd = {
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_map_iterator_contents = cbor_det_map_iterator_start(c),
                .cddl_map_iterator_impl_validate1 = COSE_Format_aux_env25_validate_2,
                .cddl_map_iterator_impl_parse1 = COSE_Format_aux_env25_parse_2,
                .cddl_map_iterator_impl_validate_ex = COSE_Format_aux_env25_validate_3,
                .cddl_map_iterator_impl_validate2 = COSE_Format_aux_env25_validate_4,
                .cddl_map_iterator_impl_parse2 = COSE_Format_aux_env25_parse_4
              }
            }
          }
        }
      ));
}

static size_t
len__COSE_Format_aux_env25_type_1_pretty(
  Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_1_pretty s
)
{
  return s.len;
}

static COSE_Format_evercddl_label_pretty
op_Array_Access__COSE_Format_aux_env25_type_1_pretty(
  Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_1_pretty a,
  size_t i
)
{
  return a.elt[i];
}

static size_t
len___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(
  Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
  s
)
{
  return s.len;
}

static K___COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
op_Array_Access___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(
  Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
  a,
  size_t i
)
{
  return a.elt[i];
}

typedef struct
__Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__s
{
  Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
  fst;
  Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
  snd;
}
__Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_;

static __Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
split___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(
  Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
  s,
  size_t i
)
{
  return
    (
      (__Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

/**
Serializer for evercddl_header_map
*/
size_t
COSE_Format_serialize_header_map(
  COSE_Format_evercddl_header_map_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  evercddl_header_map scrut0 = evercddl_header_map_pretty_left(c);
  _____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  c1 = scrut0.fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  c2 = scrut0.snd;
  ____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  c110 = c1.fst;
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  c210 = c1.snd;
  ___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  c120 = c110.fst;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty c220 = c110.snd;
  __FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
  c130 = c120.fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  c230 = c120.snd;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
  c140 = c130.fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
  c240 = c130.snd;
  bool ite0;
  if (c140.tag == FStar_Pervasives_Native_Some)
  {
    COSE_Format_evercddl_label c15 = c140.v;
    uint64_t count = pcount;
    if (count < 18446744073709551615ULL)
    {
      size_t size0 = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
      cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
      size_t len = cbor_det_size(c3, len__uint8_t(out1));
      option__size_t scrut;
      if (len > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
        {
          COSE_Format_evercddl_int_pretty c16 = c15.case_Inl;
          res2 = COSE_Format_serialize_int(c16, out2);
        }
        else if (c15.tag == COSE_Format_Inr)
        {
          COSE_Format_evercddl_bstr c25 = c15.case_Inr;
          res2 = COSE_Format_serialize_tstr(c25, out2);
        }
        else
          res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res2 > (size_t)0U)
        {
          size_t size2 = size1 + res2;
          Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
          size_t aout_len = len__uint8_t(out012);
          if
          (
            cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
      FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
      c15 = c240.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
        size_t len = cbor_det_size(c3, len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
            Pulse_Lib_Slice_slice__COSE_Format_aux_env25_type_1_pretty c16 = c15.case_Inl;
            if (len__COSE_Format_aux_env25_type_1_pretty(c16) == (size_t)0U)
              ite = false;
            else
            {
              bool pres = true;
              size_t pi = (size_t)0U;
              size_t slen = len__COSE_Format_aux_env25_type_1_pretty(c16);
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
                  COSE_Format_aux_env25_serialize_1(op_Array_Access__COSE_Format_aux_env25_type_1_pretty(c16,
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
            CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
            c25 = c15.case_Inr;
            if (cbor_det_array_iterator_is_empty(c25.cddl_array_iterator_contents))
              ite = false;
            else
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
              pc = c25;
              bool pres = true;
              bool cond;
              if (pres)
                cond = !cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
              else
                cond = false;
              while (cond)
              {
                CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty
                i = pc;
                uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
                cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
                KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
                cbor_det_array_iterator_t ji = pj;
                uint64_t len1 = cbor_det_array_iterator_length(ji);
                pc =
                  (
                    (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env25_type_1_pretty){
                      .cddl_array_iterator_contents = ji,
                      .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
                      .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
                    }
                  );
                if
                (
                  !COSE_Format_aux_env25_serialize_1(i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
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
            size_t aout_len = len__uint8_t(out2);
            res2 =
              cbor_det_serialize_array_to_array(count1,
                slice_to_arrayptr_intro__uint8_t(out2),
                aout_len,
                size);
          }
          else
            res2 = (size_t)0U;
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
            size_t aout_len = len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
      FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
      c14 = c230.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
        size_t len = cbor_det_size(c3, len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
          {
            COSE_Format_evercddl_bstr c15 = c14.case_Inl;
            res2 = COSE_Format_serialize_tstr(c15, out2);
          }
          else if (c14.tag == COSE_Format_Inr)
          {
            COSE_Format_evercddl_int_pretty c24 = c14.case_Inr;
            res2 = COSE_Format_serialize_int(c24, out2);
          }
          else
            res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
            size_t aout_len = len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
      COSE_Format_evercddl_bstr c13 = c220.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
        size_t len = cbor_det_size(c3, len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
          size_t res2 = COSE_Format_serialize_bstr(c13, out2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
            size_t aout_len = len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
      K___COSE_Format_evercddl_bstr_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
      c12 = c210.case_Inl;
      COSE_Format_evercddl_bstr c13 = c12.fst;
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty c22 = c12.snd;
      uint64_t count0 = pcount;
      bool ite;
      if (count0 < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        size_t len = cbor_det_size(c3, len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
          size_t res2 = COSE_Format_serialize_bstr(c13, out2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
            size_t aout_len = len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
          COSE_Format_evercddl_everparsenomatch_pretty c14 = c22.v;
          uint64_t count = pcount;
          if (count < 18446744073709551615ULL)
          {
            size_t size0 = psize;
            Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
            cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
            size_t len = cbor_det_size(c3, len__uint8_t(out1));
            option__size_t scrut;
            if (len > (size_t)0U)
              scrut =
                (
                  (option__size_t){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
              Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1).snd;
              size_t res2 = COSE_Format_serialize_everparsenomatch(c14, out2);
              if (res2 > (size_t)0U)
              {
                size_t size2 = size1 + res2;
                Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
                size_t aout_len = len__uint8_t(out012);
                if
                (
                  cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
    else if (c210.tag == COSE_Format_Inr)
    {
      FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
      c22 = c210.case_Inr;
      if (c22.tag == COSE_Format_Inl)
      {
        K___COSE_Format_evercddl_bstr_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
        c12 = c22.case_Inl;
        COSE_Format_evercddl_bstr c13 = c12.fst;
        FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty c23 = c12.snd;
        uint64_t count0 = pcount;
        bool ite;
        if (count0 < 18446744073709551615ULL)
        {
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
          cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
          size_t len = cbor_det_size(c3, len__uint8_t(out1));
          option__size_t scrut;
          if (len > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
            size_t res2 = COSE_Format_serialize_bstr(c13, out2);
            if (res2 > (size_t)0U)
            {
              size_t size2 = size1 + res2;
              Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
              size_t aout_len = len__uint8_t(out012);
              if
              (
                cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
            COSE_Format_evercddl_everparsenomatch_pretty c14 = c23.v;
            uint64_t count = pcount;
            if (count < 18446744073709551615ULL)
            {
              size_t size0 = psize;
              Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
              cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
              size_t len = cbor_det_size(c3, len__uint8_t(out1));
              option__size_t scrut;
              if (len > (size_t)0U)
                scrut =
                  (
                    (option__size_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
                Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1).snd;
                size_t res2 = COSE_Format_serialize_everparsenomatch(c14, out2);
                if (res2 > (size_t)0U)
                {
                  size_t size2 = size1 + res2;
                  Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
                  size_t aout_len = len__uint8_t(out012);
                  if
                  (
                    cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
        K___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
        c23 = c22.case_Inr;
        FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty c12 = c23.fst;
        FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty c24 = c23.snd;
        bool ite;
        if (c12.tag == FStar_Pervasives_Native_Some)
        {
          COSE_Format_evercddl_everparsenomatch_pretty c13 = c12.v;
          uint64_t count = pcount;
          if (count < 18446744073709551615ULL)
          {
            size_t size0 = psize;
            Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
            cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
            size_t len = cbor_det_size(c3, len__uint8_t(out1));
            option__size_t scrut;
            if (len > (size_t)0U)
              scrut =
                (
                  (option__size_t){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
              size_t res2 = COSE_Format_serialize_everparsenomatch(c13, out2);
              if (res2 > (size_t)0U)
              {
                size_t size2 = size1 + res2;
                Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
                size_t aout_len = len__uint8_t(out012);
                if
                (
                  cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
            COSE_Format_evercddl_everparsenomatch_pretty c13 = c24.v;
            uint64_t count = pcount;
            if (count < 18446744073709551615ULL)
            {
              size_t size0 = psize;
              Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
              cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
              size_t len = cbor_det_size(c3, len__uint8_t(out1));
              option__size_t scrut;
              if (len > (size_t)0U)
                scrut =
                  (
                    (option__size_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
                Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, size1).snd;
                size_t res2 = COSE_Format_serialize_everparsenomatch(c13, out2);
                if (res2 > (size_t)0U)
                {
                  size_t size2 = size1 + res2;
                  Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
                  size_t aout_len = len__uint8_t(out012);
                  if
                  (
                    cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
      Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
      c11 = c2.case_Inl;
      Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
      i = c11;
      Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
      buf = i;
      KRML_HOST_IGNORE(&buf);
      Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
      pc = i;
      bool pres = true;
      bool cond;
      if (pres)
        cond =
          !(len___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(pc) ==
            (size_t)0U);
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
          Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
          i1 = pc;
          K___COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
          res =
            op_Array_Access___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(i1,
              (size_t)0U);
          Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
          ir =
            split___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(i1,
              (size_t)1U).snd;
          pc = ir;
          K___COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty scrut0 = res;
          COSE_Format_evercddl_label_pretty ck = scrut0.fst;
          COSE_Format_evercddl_values_pretty cv = scrut0.snd;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
          size_t sz1 = COSE_Format_aux_env25_serialize_2(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            size_t len = len__uint8_t(out1);
            size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(out1), len);
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
              scrut = split__uint8_t(out1, len0);
              Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
              Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              scrut1 = { .fst = s1, .snd = s2 };
              Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
              Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
              size_t len1 = len__uint8_t(input2);
              scrut0 =
                (
                  (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = {
                      .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1),
                      .snd = rem
                    }
                  }
                );
            }
            if (scrut0.tag == FStar_Pervasives_Native_Some)
            {
              __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t oo = scrut0.v;
              cbor_det_t o = oo.fst;
              if (COSE_Format_aux_env25_validate_3(o))
                pres = false;
              else
              {
                Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out1, sz1).snd;
                size_t sz2 = COSE_Format_aux_env25_serialize_4(cv, out2);
                if (sz2 == (size_t)0U)
                  pres = false;
                else
                {
                  size_t size1 = size0 + sz1;
                  size_t size2 = size1 + sz2;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut = split__uint8_t(out, size2);
                  Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
                  Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
                  Pulse_Lib_Slice_slice__uint8_t
                  outl =
                    (
                      (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                        .fst = s1,
                        .snd = s2
                      }
                    ).fst;
                  size_t aout_len = len__uint8_t(outl);
                  if
                  (
                    !cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(outl),
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
        bool ite;
        if (pres)
          ite =
            !(len___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(pc)
            == (size_t)0U);
        else
          ite = false;
        cond = ite;
      }
      ite5 = pres;
    }
    else if (c2.tag == COSE_Format_Inr)
    {
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
      c21 = c2.case_Inr;
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
      pc = c21;
      bool pres = true;
      bool cond0;
      if (pres)
      {
        CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
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
          cbor_det_t elt_key = cbor_det_map_entry_key(elt);
          if (!!c3.cddl_map_iterator_impl_validate1(elt_key))
            if (!c3.cddl_map_iterator_impl_validate_ex(elt_key))
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
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
          i = pc;
          cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
          cbor_det_map_entry_t phd = cbor_det_map_iterator_next(&pj);
          cbor_det_map_entry_t hd0 = phd;
          cbor_det_t hd_key0 = cbor_det_map_entry_key(hd0);
          bool cond;
          if (!i.cddl_map_iterator_impl_validate1(hd_key0))
            cond = true;
          else if (i.cddl_map_iterator_impl_validate_ex(hd_key0))
            cond = true;
          else
            cond = !i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0));
          while (cond)
          {
            phd = cbor_det_map_iterator_next(&pj);
            cbor_det_map_entry_t hd = phd;
            cbor_det_t hd_key = cbor_det_map_entry_key(hd);
            bool ite;
            if (!i.cddl_map_iterator_impl_validate1(hd_key))
              ite = true;
            else if (i.cddl_map_iterator_impl_validate_ex(hd_key))
              ite = true;
            else
              ite = !i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd));
            cond = ite;
          }
          cbor_det_map_entry_t hd = phd;
          COSE_Format_evercddl_label_pretty
          hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
          COSE_Format_evercddl_values_pretty
          hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
          pc =
            (
              (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty){
                .cddl_map_iterator_contents = pj,
                .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
                .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
                .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
                .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
                .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
              }
            );
          COSE_Format_evercddl_label_pretty ck = hd_key_res;
          COSE_Format_evercddl_values_pretty cv = hd_value_res;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
          size_t sz1 = COSE_Format_aux_env25_serialize_2(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            size_t len = len__uint8_t(out1);
            size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(out1), len);
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
              scrut = split__uint8_t(out1, len0);
              Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
              Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              scrut1 = { .fst = s1, .snd = s2 };
              Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
              Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
              size_t len1 = len__uint8_t(input2);
              scrut0 =
                (
                  (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = {
                      .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1),
                      .snd = rem
                    }
                  }
                );
            }
            if (scrut0.tag == FStar_Pervasives_Native_Some)
            {
              __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t oo = scrut0.v;
              cbor_det_t o = oo.fst;
              if (COSE_Format_aux_env25_validate_3(o))
                pres = false;
              else
              {
                Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out1, sz1).snd;
                size_t sz2 = COSE_Format_aux_env25_serialize_4(cv, out2);
                if (sz2 == (size_t)0U)
                  pres = false;
                else
                {
                  size_t size1 = size0 + sz1;
                  size_t size2 = size1 + sz2;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut = split__uint8_t(out, size2);
                  Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
                  Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
                  Pulse_Lib_Slice_slice__uint8_t
                  outl =
                    (
                      (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                        .fst = s1,
                        .snd = s2
                      }
                    ).fst;
                  size_t aout_len = len__uint8_t(outl);
                  if
                  (
                    !cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(outl),
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
        bool ite;
        if (pres)
        {
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
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
            cbor_det_t elt_key = cbor_det_map_entry_key(elt);
            if (!!c3.cddl_map_iterator_impl_validate1(elt_key))
              if (!c3.cddl_map_iterator_impl_validate_ex(elt_key))
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
    size_t aout_len = len__uint8_t(out);
    return
      cbor_det_serialize_map_to_array(count,
        slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_header_map_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_header_map(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_header_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_header_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_header_map(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_header_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
COSE_Format_is_empty_iterate_map_aux_env25_type_2_and_aux_env25_type_4(
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
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
    cbor_det_t elt_key = cbor_det_map_entry_key(elt);
    if (!!i.cddl_map_iterator_impl_validate1(elt_key))
      if (!i.cddl_map_iterator_impl_validate_ex(elt_key))
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

K___COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
COSE_Format_next_iterate_map_aux_env25_type_2_and_aux_env25_type_4(
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  *pi
)
{
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  i = *pi;
  cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
  cbor_det_map_entry_t phd = cbor_det_map_iterator_next(&pj);
  cbor_det_map_entry_t hd0 = phd;
  cbor_det_t hd_key0 = cbor_det_map_entry_key(hd0);
  bool cond;
  if (!i.cddl_map_iterator_impl_validate1(hd_key0))
    cond = true;
  else if (i.cddl_map_iterator_impl_validate_ex(hd_key0))
    cond = true;
  else
    cond = !i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0));
  while (cond)
  {
    phd = cbor_det_map_iterator_next(&pj);
    cbor_det_map_entry_t hd = phd;
    cbor_det_t hd_key = cbor_det_map_entry_key(hd);
    bool ite;
    if (!i.cddl_map_iterator_impl_validate1(hd_key))
      ite = true;
    else if (i.cddl_map_iterator_impl_validate_ex(hd_key))
      ite = true;
    else
      ite = !i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd));
    cond = ite;
  }
  cbor_det_map_entry_t hd = phd;
  COSE_Format_evercddl_label_pretty
  hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
  COSE_Format_evercddl_values_pretty
  hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
  *pi =
    (
      (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty){
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
      (K___COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty){
        .fst = hd_key_res,
        .snd = hd_value_res
      }
    );
}

bool COSE_Format_validate_empty_or_serialized_map(cbor_det_t c)
{
  bool ite;
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_BYTE_STRING)
  {
    uint64_t len0 = cbor_det_get_string_length(c);
    Pulse_Lib_Slice_slice__uint8_t
    pl = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len0);
    size_t len = len__uint8_t(pl);
    size_t len2 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(pl), len);
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
      Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
      Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut1 = { .fst = s1, .snd = s2 };
      Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
      size_t len1 = len__uint8_t(input2);
      scrut0 =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = {
              .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1),
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
      Pulse_Lib_Slice_slice__uint8_t rem = r.snd;
      if (len__uint8_t(rem) == (size_t)0U)
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
    len0 = len__uint8_t(arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len));
    return (size_t)0U <= len0 && len0 <= (size_t)0U;
  }
  else
    return false;
}

typedef struct evercddl_empty_or_serialized_map_s
{
  COSE_Format_evercddl_int_tags tag;
  union {
    COSE_Format_evercddl_header_map_pretty case_Inl;
    Pulse_Lib_Slice_slice__uint8_t case_Inr;
  }
  ;
}
evercddl_empty_or_serialized_map;

static COSE_Format_evercddl_empty_or_serialized_map_pretty
evercddl_empty_or_serialized_map_pretty_right(evercddl_empty_or_serialized_map x2)
{
  if (x2.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_header_map_pretty x3 = x2.case_Inl;
    return
      (
        (COSE_Format_evercddl_empty_or_serialized_map_pretty){
          .tag = COSE_Format_Mkevercddl_empty_or_serialized_map_pretty0,
          { .case_Mkevercddl_empty_or_serialized_map_pretty0 = x3 }
        }
      );
  }
  else if (x2.tag == COSE_Format_Inr)
  {
    Pulse_Lib_Slice_slice__uint8_t x4 = x2.case_Inr;
    return
      (
        (COSE_Format_evercddl_empty_or_serialized_map_pretty){
          .tag = COSE_Format_Mkevercddl_empty_or_serialized_map_pretty1,
          { .case_Mkevercddl_empty_or_serialized_map_pretty1 = x4 }
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

static evercddl_empty_or_serialized_map
evercddl_empty_or_serialized_map_pretty_left(
  COSE_Format_evercddl_empty_or_serialized_map_pretty x7
)
{
  if (x7.tag == COSE_Format_Mkevercddl_empty_or_serialized_map_pretty0)
  {
    COSE_Format_evercddl_header_map_pretty
    x10 = x7.case_Mkevercddl_empty_or_serialized_map_pretty0;
    return ((evercddl_empty_or_serialized_map){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_empty_or_serialized_map_pretty1)
  {
    Pulse_Lib_Slice_slice__uint8_t x12 = x7.case_Mkevercddl_empty_or_serialized_map_pretty1;
    return ((evercddl_empty_or_serialized_map){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

static cbor_det_t
fst__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t(
  __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t x
)
{
  return x.fst;
}

/**
Parser for evercddl_empty_or_serialized_map
*/
COSE_Format_evercddl_empty_or_serialized_map_pretty
COSE_Format_parse_empty_or_serialized_map(cbor_det_t c)
{
  bool ite0;
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_BYTE_STRING)
  {
    uint64_t len0 = cbor_det_get_string_length(c);
    Pulse_Lib_Slice_slice__uint8_t
    pl = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len0);
    size_t len = len__uint8_t(pl);
    size_t len2 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(pl), len);
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
      Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
      Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut1 = { .fst = s1, .snd = s2 };
      Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
      size_t len1 = len__uint8_t(input2);
      scrut0 =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = {
              .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1),
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
      Pulse_Lib_Slice_slice__uint8_t rem = r.snd;
      if (len__uint8_t(rem) == (size_t)0U)
        ite0 = COSE_Format_validate_header_map(res);
      else
        ite0 = false;
    }
    else
      ite0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  }
  else
    ite0 = false;
  evercddl_empty_or_serialized_map ite1;
  if (ite0)
  {
    uint64_t len0 = cbor_det_get_string_length(c);
    Pulse_Lib_Slice_slice__uint8_t
    cs = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len0);
    size_t len = len__uint8_t(cs);
    size_t len2 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(cs), len);
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
      Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
      Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut1 = { .fst = s1, .snd = s2 };
      Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
      size_t len1 = len__uint8_t(input2);
      scrut0 =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = {
              .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1),
              .snd = rem
            }
          }
        );
    }
    COSE_Format_evercddl_header_map_pretty ite;
    if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t cp_ = scrut0.v;
      ite =
        COSE_Format_parse_header_map(fst__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t(cp_));
    }
    else
      ite =
        KRML_EABORT(COSE_Format_evercddl_header_map_pretty,
          "unreachable (pattern matches are exhaustive in F*)");
    ite1 = ((evercddl_empty_or_serialized_map){ .tag = COSE_Format_Inl, { .case_Inl = ite } });
  }
  else
  {
    uint64_t len = cbor_det_get_string_length(c);
    ite1 =
      (
        (evercddl_empty_or_serialized_map){
          .tag = COSE_Format_Inr,
          { .case_Inr = arrayptr_to_slice_intro__uint8_t(cbor_det_get_string(c), (size_t)len) }
        }
      );
  }
  return evercddl_empty_or_serialized_map_pretty_right(ite1);
}

/**
Serializer for evercddl_empty_or_serialized_map
*/
size_t
COSE_Format_serialize_empty_or_serialized_map(
  COSE_Format_evercddl_empty_or_serialized_map_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  evercddl_empty_or_serialized_map scrut0 = evercddl_empty_or_serialized_map_pretty_left(c);
  if (scrut0.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_header_map_pretty c1 = scrut0.case_Inl;
    size_t sz = COSE_Format_serialize_header_map(c1, out);
    if (sz == (size_t)0U || sz > (size_t)18446744073709551615ULL)
      return (size_t)0U;
    else
    {
      size_t aout_len = len__uint8_t(out);
      return
        cbor_det_serialize_string_to_array(CBOR_MAJOR_TYPE_BYTE_STRING,
          (uint64_t)sz,
          slice_to_arrayptr_intro__uint8_t(out),
          aout_len);
    }
  }
  else if (scrut0.tag == COSE_Format_Inr)
  {
    Pulse_Lib_Slice_slice__uint8_t c2 = scrut0.case_Inr;
    size_t len = len__uint8_t(c2);
    if ((size_t)0ULL <= len && len <= (size_t)0ULL)
      if (2U == CBOR_MAJOR_TYPE_BYTE_STRING)
        if (len__uint8_t(c2) <= (size_t)18446744073709551615ULL)
        {
          uint8_t *a = slice_to_arrayptr_intro__uint8_t(c2);
          cbor_det_t
          x =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_BYTE_STRING,
              a,
              (uint64_t)len__uint8_t(c2));
          size_t len2 = cbor_det_size(x, len__uint8_t(out));
          option__size_t scrut;
          if (len2 > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(x, slice_to_arrayptr_intro__uint8_t(out), len2)
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
      else if (len__uint8_t(c2) <= (size_t)18446744073709551615ULL)
      {
        size_t alen = len__uint8_t(c2);
        if (cbor_det_impl_utf8_correct_from_array(slice_to_arrayptr_intro__uint8_t(c2), alen))
        {
          uint8_t *a = slice_to_arrayptr_intro__uint8_t(c2);
          cbor_det_t
          x =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
              a,
              (uint64_t)len__uint8_t(c2));
          size_t len2 = cbor_det_size(x, len__uint8_t(out));
          option__size_t scrut;
          if (len2 > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(x, slice_to_arrayptr_intro__uint8_t(out), len2)
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_empty_or_serialized_map_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_empty_or_serialized_map(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_empty_or_serialized_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_empty_or_serialized_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_empty_or_serialized_map(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_empty_or_serialized_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_COSE_Signature(cbor_det_t c)
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

typedef struct
__COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty_s
{
  COSE_Format_evercddl_empty_or_serialized_map_pretty fst;
  COSE_Format_evercddl_header_map_pretty snd;
}
__COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty;

typedef struct evercddl_COSE_Signature_s
{
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  fst;
  COSE_Format_evercddl_bstr snd;
}
evercddl_COSE_Signature;

static COSE_Format_evercddl_COSE_Signature_pretty
evercddl_COSE_Signature_pretty_right(evercddl_COSE_Signature x3)
{
  COSE_Format_evercddl_bstr x6 = x3.snd;
  COSE_Format_evercddl_header_map_pretty x5 = x3.fst.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x4 = x3.fst.fst;
  return ((COSE_Format_evercddl_COSE_Signature_pretty){ ._x0 = x4, ._x1 = x5, ._x2 = x6 });
}

static evercddl_COSE_Signature
evercddl_COSE_Signature_pretty_left(COSE_Format_evercddl_COSE_Signature_pretty x7)
{
  COSE_Format_evercddl_empty_or_serialized_map_pretty x12 = x7._x0;
  COSE_Format_evercddl_header_map_pretty x13 = x7._x1;
  COSE_Format_evercddl_bstr x14 = x7._x2;
  return ((evercddl_COSE_Signature){ .fst = { .fst = x12, .snd = x13 }, .snd = x14 });
}

/**
Parser for evercddl_COSE_Signature
*/
COSE_Format_evercddl_COSE_Signature_pretty COSE_Format_parse_COSE_Signature(cbor_det_t c)
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
  COSE_Format_evercddl_empty_or_serialized_map_pretty
  w1 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
  cbor_det_array_iterator_t buf1 = c11;
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  w10 = { .fst = w1, .snd = COSE_Format_parse_header_map(cbor_det_array_iterator_next(&buf1)) };
  cbor_det_array_iterator_t buf = c1;
  return
    evercddl_COSE_Signature_pretty_right((
        (evercddl_COSE_Signature){
          .fst = w10,
          .snd = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf))
        }
      ));
}

/**
Serializer for evercddl_COSE_Signature
*/
size_t
COSE_Format_serialize_COSE_Signature(
  COSE_Format_evercddl_COSE_Signature_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  evercddl_COSE_Signature scrut = evercddl_COSE_Signature_pretty_left(c);
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  c1 = scrut.fst;
  COSE_Format_evercddl_bstr c2 = scrut.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty c11 = c1.fst;
  COSE_Format_evercddl_header_map_pretty c21 = c1.snd;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
    size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c11, out1);
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
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
      size_t size1 = COSE_Format_serialize_header_map(c21, out1);
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
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
      size_t size1 = COSE_Format_serialize_bstr(c2, out1);
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
    size_t aout_len = len__uint8_t(out);
    return
      cbor_det_serialize_array_to_array(count,
        slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Signature_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Signature(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Signature_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Signature(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Signature_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Signature(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Signature_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
  if (cbor_det_array_iterator_is_empty(*pi))
    return false;
  else
    return COSE_Format_validate_COSE_Signature(cbor_det_array_iterator_next(pi));
}

static COSE_Format_evercddl_COSE_Signature_pretty
aux_env29_type_1_pretty_right(COSE_Format_evercddl_COSE_Signature_pretty x1)
{
  return x1;
}

static COSE_Format_evercddl_COSE_Signature_pretty
aux_env29_type_1_pretty_left(COSE_Format_evercddl_COSE_Signature_pretty x3)
{
  return x3;
}

/**
Parser for aux_env29_type_1
*/
COSE_Format_evercddl_COSE_Signature_pretty
COSE_Format_aux_env29_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t buf = c;
  return
    aux_env29_type_1_pretty_right(COSE_Format_parse_COSE_Signature(cbor_det_array_iterator_next(&buf)));
}

/**
Serializer for aux_env29_type_1
*/
bool
COSE_Format_aux_env29_serialize_1(
  COSE_Format_evercddl_COSE_Signature_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  COSE_Format_evercddl_COSE_Signature_pretty c_ = aux_env29_type_1_pretty_left(c);
  uint64_t count = *out_count;
  if (count < 18446744073709551615ULL)
  {
    size_t size = *out_size;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
    size_t size1 = COSE_Format_serialize_COSE_Signature(c_, out1);
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

bool COSE_Format_validate_COSE_Sign(cbor_det_t c)
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
              ite0 = COSE_Format_validate_COSE_Signature(cbor_det_array_iterator_next(&pi1));
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
                  ite = COSE_Format_validate_COSE_Signature(cbor_det_array_iterator_next(&pi1));
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
__FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty_s
{
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty
  snd;
}
__FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty;

typedef struct evercddl_COSE_Sign_s
{
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  fst;
  __FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty
  snd;
}
evercddl_COSE_Sign;

static COSE_Format_evercddl_COSE_Sign_pretty
evercddl_COSE_Sign_pretty_right(evercddl_COSE_Sign x4)
{
  FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty
  x8 = x4.snd.snd;
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  x7 = x4.snd.fst;
  COSE_Format_evercddl_header_map_pretty x6 = x4.fst.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x5 = x4.fst.fst;
  return ((COSE_Format_evercddl_COSE_Sign_pretty){ ._x0 = x5, ._x1 = x6, ._x2 = x7, ._x3 = x8 });
}

static evercddl_COSE_Sign
evercddl_COSE_Sign_pretty_left(COSE_Format_evercddl_COSE_Sign_pretty x9)
{
  COSE_Format_evercddl_empty_or_serialized_map_pretty x15 = x9._x0;
  COSE_Format_evercddl_header_map_pretty x16 = x9._x1;
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  x17 = x9._x2;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty
  x18 = x9._x3;
  return
    ((evercddl_COSE_Sign){ .fst = { .fst = x15, .snd = x16 }, .snd = { .fst = x17, .snd = x18 } });
}

/**
Parser for evercddl_COSE_Sign
*/
COSE_Format_evercddl_COSE_Sign_pretty COSE_Format_parse_COSE_Sign(cbor_det_t c)
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
  COSE_Format_evercddl_empty_or_serialized_map_pretty
  w1 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
  cbor_det_array_iterator_t buf1 = c11;
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
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
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty w11;
  if (COSE_Format_validate_bstr(x))
    w11 =
      (
        (FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_bstr(x) }
        }
      );
  else
    w11 =
      (
        (FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_nil(x) }
        }
      );
  cbor_det_array_iterator_t buf = c110;
  return
    evercddl_COSE_Sign_pretty_right((
        (evercddl_COSE_Sign){
          .fst = w10,
          .snd = {
            .fst = w11,
            .snd = {
              .tag = COSE_Format_Inr,
              {
                .case_Inr = {
                  .cddl_array_iterator_contents = cbor_det_array_iterator_start(cbor_det_array_iterator_next(&buf)),
                  .cddl_array_iterator_impl_validate = COSE_Format_aux_env29_validate_1,
                  .cddl_array_iterator_impl_parse = COSE_Format_aux_env29_parse_1
                }
              }
            }
          }
        }
      ));
}

static size_t
len__COSE_Format_aux_env29_type_1_pretty(
  Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_pretty s
)
{
  return s.len;
}

static COSE_Format_evercddl_COSE_Signature_pretty
op_Array_Access__COSE_Format_aux_env29_type_1_pretty(
  Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_pretty a,
  size_t i
)
{
  return a.elt[i];
}

/**
Serializer for evercddl_COSE_Sign
*/
size_t
COSE_Format_serialize_COSE_Sign(
  COSE_Format_evercddl_COSE_Sign_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  evercddl_COSE_Sign scrut = evercddl_COSE_Sign_pretty_left(c);
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  c1 = scrut.fst;
  __FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty
  c2 = scrut.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty c110 = c1.fst;
  COSE_Format_evercddl_header_map_pretty c210 = c1.snd;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
    size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c110, out1);
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
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
      size_t size1 = COSE_Format_serialize_header_map(c210, out1);
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
    FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
    c11 = c2.fst;
    FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty
    c21 = c2.snd;
    uint64_t count = pcount;
    bool ite0;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
      size_t size1;
      if (c11.tag == COSE_Format_Inl)
      {
        COSE_Format_evercddl_bstr c12 = c11.case_Inl;
        size1 = COSE_Format_serialize_bstr(c12, out1);
      }
      else if (c11.tag == COSE_Format_Inr)
      {
        COSE_Format_evercddl_nil_pretty c22 = c11.case_Inr;
        size1 = COSE_Format_serialize_nil(c22, out1);
      }
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
          Pulse_Lib_Slice_slice__COSE_Format_aux_env29_type_1_pretty c12 = c21.case_Inl;
          if (len__COSE_Format_aux_env29_type_1_pretty(c12) == (size_t)0U)
            ite = false;
          else
          {
            bool pres = true;
            size_t pi = (size_t)0U;
            size_t slen = len__COSE_Format_aux_env29_type_1_pretty(c12);
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
                COSE_Format_aux_env29_serialize_1(op_Array_Access__COSE_Format_aux_env29_type_1_pretty(c12,
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
          CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty
          c22 = c21.case_Inr;
          if (cbor_det_array_iterator_is_empty(c22.cddl_array_iterator_contents))
            ite = false;
          else
          {
            CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty
            pc = c22;
            bool pres = true;
            bool cond;
            if (pres)
              cond = !cbor_det_array_iterator_is_empty(pc.cddl_array_iterator_contents);
            else
              cond = false;
            while (cond)
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty
              i = pc;
              uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
              cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
              KRML_HOST_IGNORE(i.cddl_array_iterator_impl_validate(&pj));
              cbor_det_array_iterator_t ji = pj;
              uint64_t len1 = cbor_det_array_iterator_length(ji);
              pc =
                (
                  (CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_aux_env29_type_1_pretty){
                    .cddl_array_iterator_contents = ji,
                    .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
                    .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
                  }
                );
              if
              (
                !COSE_Format_aux_env29_serialize_1(i.cddl_array_iterator_impl_parse(cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents,
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
          size_t aout_len = len__uint8_t(out1);
          size10 =
            cbor_det_serialize_array_to_array(count1,
              slice_to_arrayptr_intro__uint8_t(out1),
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
    size_t aout_len = len__uint8_t(out);
    return
      cbor_det_serialize_array_to_array(count,
        slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Sign(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Sign(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Sign(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_COSE_Sign_Tagged(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (98ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_COSE_Sign(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

static COSE_Format_evercddl_COSE_Sign_pretty
evercddl_COSE_Sign_Tagged_pretty_right(COSE_Format_evercddl_COSE_Sign_pretty x1)
{
  return x1;
}

static COSE_Format_evercddl_COSE_Sign_pretty
evercddl_COSE_Sign_Tagged_pretty_left(COSE_Format_evercddl_COSE_Sign_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_COSE_Sign_Tagged
*/
COSE_Format_evercddl_COSE_Sign_pretty COSE_Format_parse_COSE_Sign_Tagged(cbor_det_t c)
{
  return
    evercddl_COSE_Sign_Tagged_pretty_right(COSE_Format_parse_COSE_Sign(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_COSE_Sign_Tagged
*/
size_t
COSE_Format_serialize_COSE_Sign_Tagged(
  COSE_Format_evercddl_COSE_Sign_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 98ULL;
  COSE_Format_evercddl_COSE_Sign_pretty cpayload = evercddl_COSE_Sign_Tagged_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_COSE_Sign(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Sign_Tagged(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Sign_Tagged(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Sign_Tagged(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_COSE_Sign1(cbor_det_t c)
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

typedef struct
__FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_COSE_Format_evercddl_bstr_pretty_s
{
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty fst;
  COSE_Format_evercddl_bstr snd;
}
__FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_COSE_Format_evercddl_bstr_pretty;

typedef struct evercddl_COSE_Sign1_s
{
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  fst;
  __FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_COSE_Format_evercddl_bstr_pretty
  snd;
}
evercddl_COSE_Sign1;

static COSE_Format_evercddl_COSE_Sign1_pretty
evercddl_COSE_Sign1_pretty_right(evercddl_COSE_Sign1 x4)
{
  COSE_Format_evercddl_bstr x8 = x4.snd.snd;
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  x7 = x4.snd.fst;
  COSE_Format_evercddl_header_map_pretty x6 = x4.fst.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x5 = x4.fst.fst;
  return
    ((COSE_Format_evercddl_COSE_Sign1_pretty){ ._x0 = x5, ._x1 = x6, ._x2 = x7, ._x3 = x8 });
}

static evercddl_COSE_Sign1
evercddl_COSE_Sign1_pretty_left(COSE_Format_evercddl_COSE_Sign1_pretty x9)
{
  COSE_Format_evercddl_empty_or_serialized_map_pretty x15 = x9._x0;
  COSE_Format_evercddl_header_map_pretty x16 = x9._x1;
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  x17 = x9._x2;
  COSE_Format_evercddl_bstr x18 = x9._x3;
  return
    ((evercddl_COSE_Sign1){ .fst = { .fst = x15, .snd = x16 }, .snd = { .fst = x17, .snd = x18 } });
}

/**
Parser for evercddl_COSE_Sign1
*/
COSE_Format_evercddl_COSE_Sign1_pretty COSE_Format_parse_COSE_Sign1(cbor_det_t c)
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
  COSE_Format_evercddl_empty_or_serialized_map_pretty
  w1 = COSE_Format_parse_empty_or_serialized_map(cbor_det_array_iterator_next(&buf0));
  cbor_det_array_iterator_t buf1 = c11;
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
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
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty w11;
  if (COSE_Format_validate_bstr(x))
    w11 =
      (
        (FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_bstr(x) }
        }
      );
  else
    w11 =
      (
        (FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_nil(x) }
        }
      );
  cbor_det_array_iterator_t buf = c110;
  return
    evercddl_COSE_Sign1_pretty_right((
        (evercddl_COSE_Sign1){
          .fst = w10,
          .snd = { .fst = w11, .snd = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf)) }
        }
      ));
}

/**
Serializer for evercddl_COSE_Sign1
*/
size_t
COSE_Format_serialize_COSE_Sign1(
  COSE_Format_evercddl_COSE_Sign1_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  evercddl_COSE_Sign1 scrut = evercddl_COSE_Sign1_pretty_left(c);
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  c1 = scrut.fst;
  __FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_COSE_Format_evercddl_bstr_pretty
  c2 = scrut.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty c110 = c1.fst;
  COSE_Format_evercddl_header_map_pretty c210 = c1.snd;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
    size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c110, out1);
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
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
      size_t size1 = COSE_Format_serialize_header_map(c210, out1);
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
    FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
    c11 = c2.fst;
    COSE_Format_evercddl_bstr c21 = c2.snd;
    uint64_t count = pcount;
    bool ite;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
      size_t size1;
      if (c11.tag == COSE_Format_Inl)
      {
        COSE_Format_evercddl_bstr c12 = c11.case_Inl;
        size1 = COSE_Format_serialize_bstr(c12, out1);
      }
      else if (c11.tag == COSE_Format_Inr)
      {
        COSE_Format_evercddl_nil_pretty c22 = c11.case_Inr;
        size1 = COSE_Format_serialize_nil(c22, out1);
      }
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
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
        size_t size1 = COSE_Format_serialize_bstr(c21, out1);
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
    size_t aout_len = len__uint8_t(out);
    return
      cbor_det_serialize_array_to_array(count,
        slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Sign1(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Sign1(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Sign1(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_COSE_Untagged_Message(cbor_det_t c)
{
  if (COSE_Format_validate_COSE_Sign(c))
    return true;
  else
    return COSE_Format_validate_COSE_Sign1(c);
}

typedef struct evercddl_COSE_Untagged_Message_s
{
  COSE_Format_evercddl_int_tags tag;
  union {
    COSE_Format_evercddl_COSE_Sign_pretty case_Inl;
    COSE_Format_evercddl_COSE_Sign1_pretty case_Inr;
  }
  ;
}
evercddl_COSE_Untagged_Message;

static COSE_Format_evercddl_COSE_Untagged_Message_pretty
evercddl_COSE_Untagged_Message_pretty_right(evercddl_COSE_Untagged_Message x2)
{
  if (x2.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Sign_pretty x3 = x2.case_Inl;
    return
      (
        (COSE_Format_evercddl_COSE_Untagged_Message_pretty){
          .tag = COSE_Format_Mkevercddl_COSE_Untagged_Message_pretty0,
          { .case_Mkevercddl_COSE_Untagged_Message_pretty0 = x3 }
        }
      );
  }
  else if (x2.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty x4 = x2.case_Inr;
    return
      (
        (COSE_Format_evercddl_COSE_Untagged_Message_pretty){
          .tag = COSE_Format_Mkevercddl_COSE_Untagged_Message_pretty1,
          { .case_Mkevercddl_COSE_Untagged_Message_pretty1 = x4 }
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

static evercddl_COSE_Untagged_Message
evercddl_COSE_Untagged_Message_pretty_left(
  COSE_Format_evercddl_COSE_Untagged_Message_pretty x7
)
{
  if (x7.tag == COSE_Format_Mkevercddl_COSE_Untagged_Message_pretty0)
  {
    COSE_Format_evercddl_COSE_Sign_pretty x10 = x7.case_Mkevercddl_COSE_Untagged_Message_pretty0;
    return ((evercddl_COSE_Untagged_Message){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_COSE_Untagged_Message_pretty1)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty x12 = x7.case_Mkevercddl_COSE_Untagged_Message_pretty1;
    return ((evercddl_COSE_Untagged_Message){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

/**
Parser for evercddl_COSE_Untagged_Message
*/
COSE_Format_evercddl_COSE_Untagged_Message_pretty
COSE_Format_parse_COSE_Untagged_Message(cbor_det_t c)
{
  evercddl_COSE_Untagged_Message ite;
  if (COSE_Format_validate_COSE_Sign(c))
    ite =
      (
        (evercddl_COSE_Untagged_Message){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_COSE_Sign(c) }
        }
      );
  else
    ite =
      (
        (evercddl_COSE_Untagged_Message){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_COSE_Sign1(c) }
        }
      );
  return evercddl_COSE_Untagged_Message_pretty_right(ite);
}

/**
Serializer for evercddl_COSE_Untagged_Message
*/
size_t
COSE_Format_serialize_COSE_Untagged_Message(
  COSE_Format_evercddl_COSE_Untagged_Message_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  evercddl_COSE_Untagged_Message scrut = evercddl_COSE_Untagged_Message_pretty_left(c);
  if (scrut.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Sign_pretty c1 = scrut.case_Inl;
    return COSE_Format_serialize_COSE_Sign(c1, out);
  }
  else if (scrut.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty c2 = scrut.case_Inr;
    return COSE_Format_serialize_COSE_Sign1(c2, out);
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Untagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Untagged_Message(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Untagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Untagged_Message(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Untagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Untagged_Message(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Untagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_COSE_Sign1_Tagged(cbor_det_t c)
{
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_TAGGED)
    if (18ULL == cbor_det_get_tagged_tag(c))
      return COSE_Format_validate_COSE_Sign1(cbor_det_get_tagged_payload(c));
    else
      return false;
  else
    return false;
}

static COSE_Format_evercddl_COSE_Sign1_pretty
evercddl_COSE_Sign1_Tagged_pretty_right(COSE_Format_evercddl_COSE_Sign1_pretty x1)
{
  return x1;
}

static COSE_Format_evercddl_COSE_Sign1_pretty
evercddl_COSE_Sign1_Tagged_pretty_left(COSE_Format_evercddl_COSE_Sign1_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_COSE_Sign1_Tagged
*/
COSE_Format_evercddl_COSE_Sign1_pretty COSE_Format_parse_COSE_Sign1_Tagged(cbor_det_t c)
{
  return
    evercddl_COSE_Sign1_Tagged_pretty_right(COSE_Format_parse_COSE_Sign1(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_COSE_Sign1_Tagged
*/
size_t
COSE_Format_serialize_COSE_Sign1_Tagged(
  COSE_Format_evercddl_COSE_Sign1_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 18ULL;
  COSE_Format_evercddl_COSE_Sign1_pretty cpayload = evercddl_COSE_Sign1_Tagged_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_COSE_Sign1(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Sign1_Tagged(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Sign1_Tagged(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Sign1_Tagged(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_COSE_Tagged_Message(cbor_det_t c)
{
  if (COSE_Format_validate_COSE_Sign_Tagged(c))
    return true;
  else
    return COSE_Format_validate_COSE_Sign1_Tagged(c);
}

typedef struct evercddl_COSE_Tagged_Message_s
{
  COSE_Format_evercddl_int_tags tag;
  union {
    COSE_Format_evercddl_COSE_Sign_pretty case_Inl;
    COSE_Format_evercddl_COSE_Sign1_pretty case_Inr;
  }
  ;
}
evercddl_COSE_Tagged_Message;

static COSE_Format_evercddl_COSE_Tagged_Message_pretty
evercddl_COSE_Tagged_Message_pretty_right(evercddl_COSE_Tagged_Message x2)
{
  if (x2.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Sign_pretty x3 = x2.case_Inl;
    return
      (
        (COSE_Format_evercddl_COSE_Tagged_Message_pretty){
          .tag = COSE_Format_Mkevercddl_COSE_Tagged_Message_pretty0,
          { .case_Mkevercddl_COSE_Tagged_Message_pretty0 = x3 }
        }
      );
  }
  else if (x2.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty x4 = x2.case_Inr;
    return
      (
        (COSE_Format_evercddl_COSE_Tagged_Message_pretty){
          .tag = COSE_Format_Mkevercddl_COSE_Tagged_Message_pretty1,
          { .case_Mkevercddl_COSE_Tagged_Message_pretty1 = x4 }
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

static evercddl_COSE_Tagged_Message
evercddl_COSE_Tagged_Message_pretty_left(COSE_Format_evercddl_COSE_Tagged_Message_pretty x7)
{
  if (x7.tag == COSE_Format_Mkevercddl_COSE_Tagged_Message_pretty0)
  {
    COSE_Format_evercddl_COSE_Sign_pretty x10 = x7.case_Mkevercddl_COSE_Tagged_Message_pretty0;
    return ((evercddl_COSE_Tagged_Message){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_COSE_Tagged_Message_pretty1)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty x12 = x7.case_Mkevercddl_COSE_Tagged_Message_pretty1;
    return ((evercddl_COSE_Tagged_Message){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

/**
Parser for evercddl_COSE_Tagged_Message
*/
COSE_Format_evercddl_COSE_Tagged_Message_pretty
COSE_Format_parse_COSE_Tagged_Message(cbor_det_t c)
{
  evercddl_COSE_Tagged_Message ite;
  if (COSE_Format_validate_COSE_Sign_Tagged(c))
    ite =
      (
        (evercddl_COSE_Tagged_Message){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_COSE_Sign_Tagged(c) }
        }
      );
  else
    ite =
      (
        (evercddl_COSE_Tagged_Message){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_COSE_Sign1_Tagged(c) }
        }
      );
  return evercddl_COSE_Tagged_Message_pretty_right(ite);
}

/**
Serializer for evercddl_COSE_Tagged_Message
*/
size_t
COSE_Format_serialize_COSE_Tagged_Message(
  COSE_Format_evercddl_COSE_Tagged_Message_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  evercddl_COSE_Tagged_Message scrut = evercddl_COSE_Tagged_Message_pretty_left(c);
  if (scrut.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Sign_pretty c1 = scrut.case_Inl;
    return COSE_Format_serialize_COSE_Sign_Tagged(c1, out);
  }
  else if (scrut.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty c2 = scrut.case_Inr;
    return COSE_Format_serialize_COSE_Sign1_Tagged(c2, out);
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Tagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Tagged_Message(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Tagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Tagged_Message(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Tagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Tagged_Message(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Tagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_COSE_Messages(cbor_det_t c)
{
  if (COSE_Format_validate_COSE_Untagged_Message(c))
    return true;
  else
    return COSE_Format_validate_COSE_Tagged_Message(c);
}

typedef struct evercddl_COSE_Messages_s
{
  COSE_Format_evercddl_int_tags tag;
  union {
    COSE_Format_evercddl_COSE_Untagged_Message_pretty case_Inl;
    COSE_Format_evercddl_COSE_Tagged_Message_pretty case_Inr;
  }
  ;
}
evercddl_COSE_Messages;

static COSE_Format_evercddl_COSE_Messages_pretty
evercddl_COSE_Messages_pretty_right(evercddl_COSE_Messages x2)
{
  if (x2.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Untagged_Message_pretty x3 = x2.case_Inl;
    return
      (
        (COSE_Format_evercddl_COSE_Messages_pretty){
          .tag = COSE_Format_Mkevercddl_COSE_Messages_pretty0,
          { .case_Mkevercddl_COSE_Messages_pretty0 = x3 }
        }
      );
  }
  else if (x2.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_COSE_Tagged_Message_pretty x4 = x2.case_Inr;
    return
      (
        (COSE_Format_evercddl_COSE_Messages_pretty){
          .tag = COSE_Format_Mkevercddl_COSE_Messages_pretty1,
          { .case_Mkevercddl_COSE_Messages_pretty1 = x4 }
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

static evercddl_COSE_Messages
evercddl_COSE_Messages_pretty_left(COSE_Format_evercddl_COSE_Messages_pretty x7)
{
  if (x7.tag == COSE_Format_Mkevercddl_COSE_Messages_pretty0)
  {
    COSE_Format_evercddl_COSE_Untagged_Message_pretty
    x10 = x7.case_Mkevercddl_COSE_Messages_pretty0;
    return ((evercddl_COSE_Messages){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_COSE_Messages_pretty1)
  {
    COSE_Format_evercddl_COSE_Tagged_Message_pretty x12 = x7.case_Mkevercddl_COSE_Messages_pretty1;
    return ((evercddl_COSE_Messages){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

/**
Parser for evercddl_COSE_Messages
*/
COSE_Format_evercddl_COSE_Messages_pretty COSE_Format_parse_COSE_Messages(cbor_det_t c)
{
  evercddl_COSE_Messages ite;
  if (COSE_Format_validate_COSE_Untagged_Message(c))
    ite =
      (
        (evercddl_COSE_Messages){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_COSE_Untagged_Message(c) }
        }
      );
  else
    ite =
      (
        (evercddl_COSE_Messages){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_COSE_Tagged_Message(c) }
        }
      );
  return evercddl_COSE_Messages_pretty_right(ite);
}

/**
Serializer for evercddl_COSE_Messages
*/
size_t
COSE_Format_serialize_COSE_Messages(
  COSE_Format_evercddl_COSE_Messages_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  evercddl_COSE_Messages scrut = evercddl_COSE_Messages_pretty_left(c);
  if (scrut.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Untagged_Message_pretty c1 = scrut.case_Inl;
    return COSE_Format_serialize_COSE_Untagged_Message(c1, out);
  }
  else if (scrut.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_COSE_Tagged_Message_pretty c2 = scrut.case_Inr;
    return COSE_Format_serialize_COSE_Tagged_Message(c2, out);
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Messages_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Messages(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Messages_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Messages(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Messages_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Messages(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Messages_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_Sig_structure(cbor_det_t c)
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
        if (len__uint8_t(s) != (size_t)9ULL)
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
        if (len__uint8_t(s) != (size_t)10ULL)
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
__COSE_Format_evercddl_empty_or_serialized_map_pretty_FStar_Pervasives_either__COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty__s
{
  COSE_Format_evercddl_empty_or_serialized_map_pretty fst;
  FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  snd;
}
__COSE_Format_evercddl_empty_or_serialized_map_pretty_FStar_Pervasives_either__COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_;

typedef struct evercddl_Sig_structure_s
{
  COSE_Format_evercddl_int_tags fst;
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_FStar_Pervasives_either__COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  snd;
}
evercddl_Sig_structure;

static COSE_Format_evercddl_Sig_structure_pretty
evercddl_Sig_structure_pretty_right(evercddl_Sig_structure x3)
{
  FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  x6 = x3.snd.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x5 = x3.snd.fst;
  COSE_Format_evercddl_int_tags x4 = x3.fst;
  return ((COSE_Format_evercddl_Sig_structure_pretty){ ._x0 = x4, ._x1 = x5, ._x2 = x6 });
}

static evercddl_Sig_structure
evercddl_Sig_structure_pretty_left(COSE_Format_evercddl_Sig_structure_pretty x7)
{
  COSE_Format_evercddl_int_tags x12 = x7._x0;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x13 = x7._x1;
  FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  x14 = x7._x2;
  return ((evercddl_Sig_structure){ .fst = x12, .snd = { .fst = x13, .snd = x14 } });
}

/**
Parser for evercddl_Sig_structure
*/
COSE_Format_evercddl_Sig_structure_pretty COSE_Format_parse_Sig_structure(cbor_det_t c)
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
      if (len__uint8_t(s) != (size_t)9ULL)
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
      if (len__uint8_t(s) != (size_t)10ULL)
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
    if (len__uint8_t(s) != (size_t)9ULL)
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
  COSE_Format_evercddl_int_tags w1;
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
  COSE_Format_evercddl_empty_or_serialized_map_pretty
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
  FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
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
    COSE_Format_evercddl_empty_or_serialized_map_pretty
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
    COSE_Format_evercddl_bstr w13 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf1));
    cbor_det_array_iterator_t buf = c13;
    ite5 =
      (
        (FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_){
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
    COSE_Format_evercddl_bstr w12 = COSE_Format_parse_bstr(cbor_det_array_iterator_next(&buf0));
    cbor_det_array_iterator_t buf = c12;
    ite5 =
      (
        (FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_){
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
    evercddl_Sig_structure_pretty_right((
        (evercddl_Sig_structure){ .fst = w1, .snd = { .fst = w11, .snd = ite5 } }
      ));
}

static Pulse_Lib_Slice_slice__uint8_t from_array__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

static void op_Array_Assignment__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i, uint8_t v)
{
  a.elt[i] = v;
}

/**
Serializer for evercddl_Sig_structure
*/
size_t
COSE_Format_serialize_Sig_structure(
  COSE_Format_evercddl_Sig_structure_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  evercddl_Sig_structure scrut0 = evercddl_Sig_structure_pretty_left(c);
  COSE_Format_evercddl_int_tags c1 = scrut0.fst;
  __COSE_Format_evercddl_empty_or_serialized_map_pretty_FStar_Pervasives_either__COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
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
          Pulse_Lib_Slice_slice__uint8_t s = from_array__uint8_t(buf, (size_t)9ULL);
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
          uint8_t *a1 = slice_to_arrayptr_intro__uint8_t(s);
          cbor_det_t
          c3 =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
              a1,
              (uint64_t)len__uint8_t(s));
          size_t len = cbor_det_size(c3, len__uint8_t(out1));
          option__size_t scrut;
          if (len > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
          Pulse_Lib_Slice_slice__uint8_t s = from_array__uint8_t(buf, (size_t)10ULL);
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
          uint8_t *a1 = slice_to_arrayptr_intro__uint8_t(s);
          cbor_det_t
          c3 =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
              a1,
              (uint64_t)len__uint8_t(s));
          size_t len = cbor_det_size(c3, len__uint8_t(out1));
          option__size_t scrut;
          if (len > (size_t)0U)
            scrut =
              (
                (option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
    COSE_Format_evercddl_empty_or_serialized_map_pretty c11 = c2.fst;
    FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
    c21 = c2.snd;
    uint64_t count0 = pcount;
    bool ite0;
    if (count0 < 18446744073709551615ULL)
    {
      size_t size = psize;
      Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
      size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c11, out1);
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
        K___COSE_Format_evercddl_empty_or_serialized_map_pretty__COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
        c12 = c21.case_Inl;
        COSE_Format_evercddl_empty_or_serialized_map_pretty c13 = c12.fst;
        K___COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_bstr_pretty c22 = c12.snd;
        uint64_t count0 = pcount;
        bool ite0;
        if (count0 < 18446744073709551615ULL)
        {
          size_t size = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
          size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c13, out1);
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
          COSE_Format_evercddl_bstr c14 = c22.fst;
          COSE_Format_evercddl_bstr c23 = c22.snd;
          uint64_t count = pcount;
          bool ite;
          if (count < 18446744073709551615ULL)
          {
            size_t size = psize;
            Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
            size_t size1 = COSE_Format_serialize_bstr(c14, out1);
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
              Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
              size_t size1 = COSE_Format_serialize_bstr(c23, out1);
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
        K___COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_bstr_pretty c22 = c21.case_Inr;
        COSE_Format_evercddl_bstr c12 = c22.fst;
        COSE_Format_evercddl_bstr c23 = c22.snd;
        uint64_t count = pcount;
        bool ite;
        if (count < 18446744073709551615ULL)
        {
          size_t size = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
          size_t size1 = COSE_Format_serialize_bstr(c12, out1);
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
            Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size).snd;
            size_t size1 = COSE_Format_serialize_bstr(c23, out1);
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
    size_t aout_len = len__uint8_t(out);
    return
      cbor_det_serialize_array_to_array(count,
        slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_Sig_structure_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_Sig_structure(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_Sig_structure_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_Sig_structure(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_Sig_structure_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_Sig_structure(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_Sig_structure_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_Internal_Types(cbor_det_t c)
{
  return COSE_Format_validate_Sig_structure(c);
}

static COSE_Format_evercddl_Sig_structure_pretty
evercddl_Internal_Types_pretty_right(COSE_Format_evercddl_Sig_structure_pretty x1)
{
  return x1;
}

static COSE_Format_evercddl_Sig_structure_pretty
evercddl_Internal_Types_pretty_left(COSE_Format_evercddl_Sig_structure_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_Internal_Types
*/
COSE_Format_evercddl_Sig_structure_pretty COSE_Format_parse_Internal_Types(cbor_det_t c)
{
  return evercddl_Internal_Types_pretty_right(COSE_Format_parse_Sig_structure(c));
}

/**
Serializer for evercddl_Internal_Types
*/
size_t
COSE_Format_serialize_Internal_Types(
  COSE_Format_evercddl_Sig_structure_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_Sig_structure(evercddl_Internal_Types_pretty_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_Internal_Types_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_Internal_Types(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_Internal_Types_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_Internal_Types(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_Internal_Types_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_Internal_Types(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_Internal_Types_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
  if (COSE_Format_validate_COSE_Messages(c))
    return true;
  else
    return COSE_Format_validate_Internal_Types(c);
}

typedef struct evercddl_start_s
{
  COSE_Format_evercddl_int_tags tag;
  union {
    COSE_Format_evercddl_COSE_Messages_pretty case_Inl;
    COSE_Format_evercddl_Sig_structure_pretty case_Inr;
  }
  ;
}
evercddl_start;

static COSE_Format_evercddl_start_pretty evercddl_start_pretty_right(evercddl_start x2)
{
  if (x2.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Messages_pretty x3 = x2.case_Inl;
    return
      (
        (COSE_Format_evercddl_start_pretty){
          .tag = COSE_Format_Mkevercddl_start_pretty0,
          { .case_Mkevercddl_start_pretty0 = x3 }
        }
      );
  }
  else if (x2.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_Sig_structure_pretty x4 = x2.case_Inr;
    return
      (
        (COSE_Format_evercddl_start_pretty){
          .tag = COSE_Format_Mkevercddl_start_pretty1,
          { .case_Mkevercddl_start_pretty1 = x4 }
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

static evercddl_start evercddl_start_pretty_left(COSE_Format_evercddl_start_pretty x7)
{
  if (x7.tag == COSE_Format_Mkevercddl_start_pretty0)
  {
    COSE_Format_evercddl_COSE_Messages_pretty x10 = x7.case_Mkevercddl_start_pretty0;
    return ((evercddl_start){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_start_pretty1)
  {
    COSE_Format_evercddl_Sig_structure_pretty x12 = x7.case_Mkevercddl_start_pretty1;
    return ((evercddl_start){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

/**
Parser for evercddl_start
*/
COSE_Format_evercddl_start_pretty COSE_Format_parse_start(cbor_det_t c)
{
  evercddl_start ite;
  if (COSE_Format_validate_COSE_Messages(c))
    ite =
      (
        (evercddl_start){
          .tag = COSE_Format_Inl,
          { .case_Inl = COSE_Format_parse_COSE_Messages(c) }
        }
      );
  else
    ite =
      (
        (evercddl_start){
          .tag = COSE_Format_Inr,
          { .case_Inr = COSE_Format_parse_Internal_Types(c) }
        }
      );
  return evercddl_start_pretty_right(ite);
}

/**
Serializer for evercddl_start
*/
size_t
COSE_Format_serialize_start(
  COSE_Format_evercddl_start_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  evercddl_start scrut = evercddl_start_pretty_left(c);
  if (scrut.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Messages_pretty c1 = scrut.case_Inl;
    return COSE_Format_serialize_COSE_Messages(c1, out);
  }
  else if (scrut.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_Sig_structure_pretty c2 = scrut.case_Inr;
    return COSE_Format_serialize_Internal_Types(c2, out);
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

FStar_Pervasives_Native_option___COSE_Format_evercddl_start_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_start(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_start_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_start_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_start(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_start_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_aux_env39_validate_1(cbor_det_t c)
{
  bool ite0;
  if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_UINT64)
    ite0 = cbor_det_read_uint64(c) == 1ULL;
  else
    ite0 = false;
  bool ite1;
  if (ite0)
    ite1 = true;
  else if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_NEG_INT64)
    ite1 = cbor_det_read_uint64(c) == 0ULL;
  else
    ite1 = false;
  bool ite;
  if (ite1)
    ite = true;
  else if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_NEG_INT64)
    ite = cbor_det_read_uint64(c) == 1ULL;
  else
    ite = false;
  if (ite)
    return true;
  else if (cbor_det_major_type(c) == CBOR_MAJOR_TYPE_NEG_INT64)
    return cbor_det_read_uint64(c) == 3ULL;
  else
    return false;
}

bool COSE_Format_validate_COSE_Key_OKP(cbor_det_t c)
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
          {
            cbor_det_t cv = scrut.v;
            if (COSE_Format_validate_bstr(cv))
            {
              remaining = remaining - 1ULL;
              ite = MGOK;
            }
            else
              ite = MGCutFail;
          }
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
          {
            cbor_det_t cv = scrut.v;
            if (COSE_Format_validate_bstr(cv))
            {
              remaining = remaining - 1ULL;
              ite = MGOK;
            }
            else
              ite = MGCutFail;
          }
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
            cbor_det_t k = cbor_det_map_entry_key(chd);
            bool ite0;
            if (COSE_Format_validate_label(k))
            {
              bool ite1;
              if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_UINT64)
                ite1 = cbor_det_read_uint64(k) == 1ULL;
              else
                ite1 = false;
              bool ite2;
              if (ite1)
                ite2 = true;
              else if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_NEG_INT64)
                ite2 = cbor_det_read_uint64(k) == 0ULL;
              else
                ite2 = false;
              bool ite3;
              if (ite2)
                ite3 = true;
              else if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_NEG_INT64)
                ite3 = cbor_det_read_uint64(k) == 1ULL;
              else
                ite3 = false;
              bool ite;
              if (ite3)
                ite = true;
              else if (cbor_det_major_type(k) == CBOR_MAJOR_TYPE_NEG_INT64)
                ite = cbor_det_read_uint64(k) == 3ULL;
              else
                ite = false;
              ite0 = !ite;
            }
            else
              ite0 = false;
            bool ite;
            if (ite0)
              ite = COSE_Format_validate_values(cbor_det_map_entry_value(chd));
            else
              ite = false;
            if (!!ite)
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
________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty_s
{
  COSE_Format_evercddl_label fst;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty snd;
}
________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty;

typedef struct
_________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty_s
{
  ________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  fst;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty snd;
}
_________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty;

typedef struct evercddl_COSE_Key_OKP_s
{
  _________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  snd;
}
evercddl_COSE_Key_OKP;

static COSE_Format_evercddl_COSE_Key_OKP_pretty
evercddl_COSE_Key_OKP_pretty_right(evercddl_COSE_Key_OKP x5)
{
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  x10 = x5.snd;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x9 = x5.fst.snd;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x8 = x5.fst.fst.snd;
  COSE_Format_evercddl_label x7 = x5.fst.fst.fst;
  return
    ((COSE_Format_evercddl_COSE_Key_OKP_pretty){ ._x1 = x7, ._x2 = x8, ._x3 = x9, ._x4 = x10 });
}

static evercddl_COSE_Key_OKP
evercddl_COSE_Key_OKP_pretty_left(COSE_Format_evercddl_COSE_Key_OKP_pretty x11)
{
  COSE_Format_evercddl_label x19 = x11._x1;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x20 = x11._x2;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x21 = x11._x3;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  x22 = x11._x4;
  return
    (
      (evercddl_COSE_Key_OKP){
        .fst = { .fst = { .fst = x19, .snd = x20 }, .snd = x21 },
        .snd = x22
      }
    );
}

/**
Parser for evercddl_COSE_Key_OKP
*/
COSE_Format_evercddl_COSE_Key_OKP_pretty COSE_Format_parse_COSE_Key_OKP(cbor_det_t c)
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
  COSE_Format_evercddl_label w1;
  if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t w = scrut0.v;
    if (COSE_Format_validate_int(w))
      w1 =
        (
          (COSE_Format_evercddl_label){
            .tag = COSE_Format_Inl,
            { .case_Inl = COSE_Format_parse_int(w) }
          }
        );
    else
      w1 =
        (
          (COSE_Format_evercddl_label){
            .tag = COSE_Format_Inr,
            { .case_Inr = COSE_Format_parse_tstr(w) }
          }
        );
  }
  else
    w1 =
      KRML_EABORT(COSE_Format_evercddl_label,
        "unreachable (pattern matches are exhaustive in F*)");
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
  {
    cbor_det_t cv = scrut1.v;
    if (COSE_Format_validate_bstr(cv))
      ite1 = MGOK;
    else
      ite1 = MGCutFail;
  }
  else
    ite1 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty ite2;
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
    COSE_Format_evercddl_bstr ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      ite = COSE_Format_parse_bstr(w);
    }
    else
      ite =
        KRML_EABORT(COSE_Format_evercddl_bstr,
          "unreachable (pattern matches are exhaustive in F*)");
    ite2 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite2 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  ________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
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
  {
    cbor_det_t cv = scrut2.v;
    if (COSE_Format_validate_bstr(cv))
      ite3 = MGOK;
    else
      ite3 = MGCutFail;
  }
  else
    ite3 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty ite4;
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
    COSE_Format_evercddl_bstr ite;
    if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = scrut.v;
      ite = COSE_Format_parse_bstr(w);
    }
    else
      ite =
        KRML_EABORT(COSE_Format_evercddl_bstr,
          "unreachable (pattern matches are exhaustive in F*)");
    ite4 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = ite
        }
      );
  }
  else
    ite4 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  _________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  w11 = { .fst = w10, .snd = ite4 };
  return
    evercddl_COSE_Key_OKP_pretty_right((
        (evercddl_COSE_Key_OKP){
          .fst = w11,
          .snd = {
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .cddl_map_iterator_contents = cbor_det_map_iterator_start(c),
                .cddl_map_iterator_impl_validate1 = COSE_Format_aux_env25_validate_2,
                .cddl_map_iterator_impl_parse1 = COSE_Format_aux_env25_parse_2,
                .cddl_map_iterator_impl_validate_ex = COSE_Format_aux_env39_validate_1,
                .cddl_map_iterator_impl_validate2 = COSE_Format_aux_env25_validate_4,
                .cddl_map_iterator_impl_parse2 = COSE_Format_aux_env25_parse_4
              }
            }
          }
        }
      ));
}

/**
Serializer for evercddl_COSE_Key_OKP
*/
size_t
COSE_Format_serialize_COSE_Key_OKP(
  COSE_Format_evercddl_COSE_Key_OKP_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  evercddl_COSE_Key_OKP scrut0 = evercddl_COSE_Key_OKP_pretty_left(c);
  _________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  c1 = scrut0.fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
  c2 = scrut0.snd;
  ________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  c110 = c1.fst;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty c210 = c1.snd;
  COSE_Format_evercddl_label c120 = c110.fst;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty c22 = c110.snd;
  COSE_Format_evercddl_label c23 = c120;
  uint64_t count0 = pcount;
  bool ite0;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size0 = psize;
    Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
    cbor_det_t c30 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    size_t len0 = cbor_det_size(c30, len__uint8_t(out1));
    option__size_t scrut0;
    if (len0 > (size_t)0U)
      scrut0 =
        (
          (option__size_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = cbor_det_serialize(c30, slice_to_arrayptr_intro__uint8_t(out1), len0)
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
      size_t len = cbor_det_size(c3, len__uint8_t(out2));
      option__size_t scrut;
      if (len > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out2), len)
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
        size_t aout_len = len__uint8_t(out012);
        if
        (
          cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
      size_t len = cbor_det_size(c3, len__uint8_t(out1));
      option__size_t scrut;
      if (len > (size_t)0U)
        scrut =
          (
            (option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
        {
          COSE_Format_evercddl_int_pretty c14 = c23.case_Inl;
          res2 = COSE_Format_serialize_int(c14, out2);
        }
        else if (c23.tag == COSE_Format_Inr)
        {
          COSE_Format_evercddl_bstr c24 = c23.case_Inr;
          res2 = COSE_Format_serialize_tstr(c24, out2);
        }
        else
          res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res2 > (size_t)0U)
        {
          size_t size2 = size1 + res2;
          Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
          size_t aout_len = len__uint8_t(out012);
          if
          (
            cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
      COSE_Format_evercddl_bstr c13 = c22.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
        size_t len = cbor_det_size(c3, len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
          size_t res2 = COSE_Format_serialize_bstr(c13, out2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
            size_t aout_len = len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
      COSE_Format_evercddl_bstr c12 = c210.v;
      uint64_t count = pcount;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
        size_t len = cbor_det_size(c3, len__uint8_t(out1));
        option__size_t scrut;
        if (len > (size_t)0U)
          scrut =
            (
              (option__size_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = cbor_det_serialize(c3, slice_to_arrayptr_intro__uint8_t(out1), len)
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
          size_t res2 = COSE_Format_serialize_bstr(c12, out2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            Pulse_Lib_Slice_slice__uint8_t out012 = split__uint8_t(out, size2).fst;
            size_t aout_len = len__uint8_t(out012);
            if
            (
              cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(out012),
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
  bool ite4;
  if (ite3)
    if (c2.tag == COSE_Format_Inl)
    {
      Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
      c11 = c2.case_Inl;
      Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
      i = c11;
      Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
      buf = i;
      KRML_HOST_IGNORE(&buf);
      Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
      pc = i;
      bool pres = true;
      bool cond;
      if (pres)
        cond =
          !(len___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(pc) ==
            (size_t)0U);
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
          Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
          i1 = pc;
          K___COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
          res =
            op_Array_Access___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(i1,
              (size_t)0U);
          Pulse_Lib_Slice_slice___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_
          ir =
            split___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(i1,
              (size_t)1U).snd;
          pc = ir;
          K___COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty scrut0 = res;
          COSE_Format_evercddl_label_pretty ck = scrut0.fst;
          COSE_Format_evercddl_values_pretty cv = scrut0.snd;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
          size_t sz1 = COSE_Format_aux_env25_serialize_2(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            size_t len = len__uint8_t(out1);
            size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(out1), len);
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
              scrut = split__uint8_t(out1, len0);
              Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
              Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              scrut1 = { .fst = s1, .snd = s2 };
              Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
              Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
              size_t len1 = len__uint8_t(input2);
              scrut0 =
                (
                  (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = {
                      .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1),
                      .snd = rem
                    }
                  }
                );
            }
            if (scrut0.tag == FStar_Pervasives_Native_Some)
            {
              __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t oo = scrut0.v;
              cbor_det_t o = oo.fst;
              if (COSE_Format_aux_env39_validate_1(o))
                pres = false;
              else
              {
                Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out1, sz1).snd;
                size_t sz2 = COSE_Format_aux_env25_serialize_4(cv, out2);
                if (sz2 == (size_t)0U)
                  pres = false;
                else
                {
                  size_t size1 = size0 + sz1;
                  size_t size2 = size1 + sz2;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut = split__uint8_t(out, size2);
                  Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
                  Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
                  Pulse_Lib_Slice_slice__uint8_t
                  outl =
                    (
                      (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                        .fst = s1,
                        .snd = s2
                      }
                    ).fst;
                  size_t aout_len = len__uint8_t(outl);
                  if
                  (
                    !cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(outl),
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
        bool ite;
        if (pres)
          ite =
            !(len___COSE_Format_aux_env25_type_2_pretty___COSE_Format_aux_env25_type_4_pretty_(pc)
            == (size_t)0U);
        else
          ite = false;
        cond = ite;
      }
      ite4 = pres;
    }
    else if (c2.tag == COSE_Format_Inr)
    {
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
      c21 = c2.case_Inr;
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
      pc = c21;
      bool pres = true;
      bool cond0;
      if (pres)
      {
        CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
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
          cbor_det_t elt_key = cbor_det_map_entry_key(elt);
          if (!!c3.cddl_map_iterator_impl_validate1(elt_key))
            if (!c3.cddl_map_iterator_impl_validate_ex(elt_key))
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
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
          i = pc;
          cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
          cbor_det_map_entry_t phd = cbor_det_map_iterator_next(&pj);
          cbor_det_map_entry_t hd0 = phd;
          cbor_det_t hd_key0 = cbor_det_map_entry_key(hd0);
          bool cond;
          if (!i.cddl_map_iterator_impl_validate1(hd_key0))
            cond = true;
          else if (i.cddl_map_iterator_impl_validate_ex(hd_key0))
            cond = true;
          else
            cond = !i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd0));
          while (cond)
          {
            phd = cbor_det_map_iterator_next(&pj);
            cbor_det_map_entry_t hd = phd;
            cbor_det_t hd_key = cbor_det_map_entry_key(hd);
            bool ite;
            if (!i.cddl_map_iterator_impl_validate1(hd_key))
              ite = true;
            else if (i.cddl_map_iterator_impl_validate_ex(hd_key))
              ite = true;
            else
              ite = !i.cddl_map_iterator_impl_validate2(cbor_det_map_entry_value(hd));
            cond = ite;
          }
          cbor_det_map_entry_t hd = phd;
          COSE_Format_evercddl_label_pretty
          hd_key_res = i.cddl_map_iterator_impl_parse1(cbor_det_map_entry_key(hd));
          COSE_Format_evercddl_values_pretty
          hd_value_res = i.cddl_map_iterator_impl_parse2(cbor_det_map_entry_value(hd));
          pc =
            (
              (CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty){
                .cddl_map_iterator_contents = pj,
                .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
                .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
                .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
                .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
                .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
              }
            );
          COSE_Format_evercddl_label_pretty ck = hd_key_res;
          COSE_Format_evercddl_values_pretty cv = hd_value_res;
          size_t size0 = psize;
          Pulse_Lib_Slice_slice__uint8_t out1 = split__uint8_t(out, size0).snd;
          size_t sz1 = COSE_Format_aux_env25_serialize_2(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            size_t len = len__uint8_t(out1);
            size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(out1), len);
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
              scrut = split__uint8_t(out1, len0);
              Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
              Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              scrut1 = { .fst = s1, .snd = s2 };
              Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
              Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
              size_t len1 = len__uint8_t(input2);
              scrut0 =
                (
                  (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = {
                      .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1),
                      .snd = rem
                    }
                  }
                );
            }
            if (scrut0.tag == FStar_Pervasives_Native_Some)
            {
              __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t oo = scrut0.v;
              cbor_det_t o = oo.fst;
              if (COSE_Format_aux_env39_validate_1(o))
                pres = false;
              else
              {
                Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out1, sz1).snd;
                size_t sz2 = COSE_Format_aux_env25_serialize_4(cv, out2);
                if (sz2 == (size_t)0U)
                  pres = false;
                else
                {
                  size_t size1 = size0 + sz1;
                  size_t size2 = size1 + sz2;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  scrut = split__uint8_t(out, size2);
                  Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
                  Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
                  Pulse_Lib_Slice_slice__uint8_t
                  outl =
                    (
                      (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                        .fst = s1,
                        .snd = s2
                      }
                    ).fst;
                  size_t aout_len = len__uint8_t(outl);
                  if
                  (
                    !cbor_det_serialize_map_insert_to_array(slice_to_arrayptr_intro__uint8_t(outl),
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
        bool ite;
        if (pres)
        {
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
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
            cbor_det_t elt_key = cbor_det_map_entry_key(elt);
            if (!!c3.cddl_map_iterator_impl_validate1(elt_key))
              if (!c3.cddl_map_iterator_impl_validate_ex(elt_key))
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
    size_t aout_len = len__uint8_t(out);
    return
      cbor_det_serialize_map_to_array(count,
        slice_to_arrayptr_intro__uint8_t(out),
        aout_len,
        size);
  }
  else
    return (size_t)0U;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_OKP_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Key_OKP(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_OKP_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Key_OKP(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_OKP_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Key_OKP(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_OKP_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_COSE_Key(cbor_det_t c)
{
  return COSE_Format_validate_COSE_Key_OKP(c);
}

static COSE_Format_evercddl_COSE_Key_OKP_pretty
evercddl_COSE_Key_pretty_right(COSE_Format_evercddl_COSE_Key_OKP_pretty x1)
{
  return x1;
}

static COSE_Format_evercddl_COSE_Key_OKP_pretty
evercddl_COSE_Key_pretty_left(COSE_Format_evercddl_COSE_Key_OKP_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_COSE_Key
*/
COSE_Format_evercddl_COSE_Key_OKP_pretty COSE_Format_parse_COSE_Key(cbor_det_t c)
{
  return evercddl_COSE_Key_pretty_right(COSE_Format_parse_COSE_Key_OKP(c));
}

/**
Serializer for evercddl_COSE_Key
*/
size_t
COSE_Format_serialize_COSE_Key(
  COSE_Format_evercddl_COSE_Key_OKP_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  return COSE_Format_serialize_COSE_Key_OKP(evercddl_COSE_Key_pretty_left(c), out);
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Key(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = scrut0.v;
    cbor_det_t rl = rlrem.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = rlrem.snd;
    if (COSE_Format_validate_COSE_Key(rl))
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_COSE_Key(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_any_pretty
evercddl_eb64url_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

static COSE_Format_evercddl_any
evercddl_eb64url_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_eb64url
*/
COSE_Format_evercddl_any_pretty COSE_Format_parse_eb64url(cbor_det_t c)
{
  return evercddl_eb64url_pretty_right(COSE_Format_parse_any(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_eb64url
*/
size_t
COSE_Format_serialize_eb64url(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 21ULL;
  COSE_Format_evercddl_any cpayload = evercddl_eb64url_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_any(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64url_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_eb64url(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_eb64url(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_any_pretty
evercddl_eb64legacy_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

static COSE_Format_evercddl_any
evercddl_eb64legacy_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_eb64legacy
*/
COSE_Format_evercddl_any_pretty COSE_Format_parse_eb64legacy(cbor_det_t c)
{
  return evercddl_eb64legacy_pretty_right(COSE_Format_parse_any(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_eb64legacy
*/
size_t
COSE_Format_serialize_eb64legacy(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 22ULL;
  COSE_Format_evercddl_any cpayload = evercddl_eb64legacy_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_any(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_eb64legacy(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_eb64legacy(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_any_pretty evercddl_eb16_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

static COSE_Format_evercddl_any evercddl_eb16_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_eb16
*/
COSE_Format_evercddl_any_pretty COSE_Format_parse_eb16(cbor_det_t c)
{
  return evercddl_eb16_pretty_right(COSE_Format_parse_any(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_eb16
*/
size_t
COSE_Format_serialize_eb16(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 23ULL;
  COSE_Format_evercddl_any cpayload = evercddl_eb16_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_any(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_eb16_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_eb16(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb16_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb16_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_eb16(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb16_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

static COSE_Format_evercddl_any_pretty
evercddl_cborany_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

static COSE_Format_evercddl_any
evercddl_cborany_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

/**
Parser for evercddl_cborany
*/
COSE_Format_evercddl_any_pretty COSE_Format_parse_cborany(cbor_det_t c)
{
  return evercddl_cborany_pretty_right(COSE_Format_parse_any(cbor_det_get_tagged_payload(c)));
}

/**
Serializer for evercddl_cborany
*/
size_t
COSE_Format_serialize_cborany(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  uint64_t ctag = 55799ULL;
  COSE_Format_evercddl_any cpayload = evercddl_cborany_pretty_left(c);
  size_t aout_len = len__uint8_t(out);
  size_t
  tsz = cbor_det_serialize_tag_to_array(ctag, slice_to_arrayptr_intro__uint8_t(out), aout_len);
  if (tsz == (size_t)0U)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t out2 = split__uint8_t(out, tsz).snd;
    size_t psz = COSE_Format_serialize_any(cpayload, out2);
    if (psz == (size_t)0U)
      return (size_t)0U;
    else
      return tsz + psz;
  }
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_cborany_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cborany(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  size_t len0 = cbor_det_validate(slice_to_arrayptr_intro__uint8_t(s), len);
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
    Pulse_Lib_Slice_slice__uint8_t s1 = scrut.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = scrut.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = scrut1.snd;
    size_t len1 = len__uint8_t(input2);
    scrut0 =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = cbor_det_parse(slice_to_arrayptr_intro__uint8_t(input2), len1), .snd = rem }
        }
      );
  }
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_cborany_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_cborany_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = COSE_Format_parse_cborany(rl), .snd = rem }
          }
        );
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_cborany_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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


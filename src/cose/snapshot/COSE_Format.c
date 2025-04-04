

#include "COSE_Format.h"

#include "CBORDetAPI.h"

#define SIMPLE_VALUE_FALSE (20U)

#define SIMPLE_VALUE_TRUE (21U)

#define MGOK 0
#define MGFail 1
#define MGCutFail 2

typedef uint8_t impl_map_group_result;

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
  uint8_t mt = cbor_det_major_type(c);
  bool test0 = mt == CBOR_MAJOR_TYPE_SIMPLE_VALUE;
  bool test;
  if (test0)
  {
    uint8_t v1 = cbor_det_read_simple_value(c);
    test = v1 == CDDL_SIMPLE_VALUE_FALSE;
  }
  else
    test = false;
  if (test)
    return true;
  else
  {
    uint8_t mt = cbor_det_major_type(c);
    bool test1 = mt == CBOR_MAJOR_TYPE_SIMPLE_VALUE;
    if (test1)
    {
      uint8_t v1 = cbor_det_read_simple_value(c);
      return v1 == CDDL_SIMPLE_VALUE_TRUE;
    }
    else
      return false;
  }
}

bool COSE_Format_uu___is_Mkevercddl_bool_pretty0(bool projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

bool COSE_Format_evercddl_bool_pretty_right(bool x1)
{
  return x1;
}

bool COSE_Format_evercddl_bool_pretty_left(bool x3)
{
  return x3;
}

bool COSE_Format_parse_bool(cbor_det_t c)
{
  uint8_t w = cbor_det_read_simple_value(c);
  bool res = w == SIMPLE_VALUE_TRUE;
  bool res1 = res;
  bool res2 = COSE_Format_evercddl_bool_pretty_right(res1);
  return res2;
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

size_t COSE_Format_serialize_bool(bool c, Pulse_Lib_Slice_slice__uint8_t out)
{
  bool c_ = COSE_Format_evercddl_bool_pretty_left(c);
  bool c_1 = c_;
  if (c_1)
    if
    (
      SIMPLE_VALUE_TRUE <= MAX_SIMPLE_VALUE_ADDITIONAL_INFO ||
        MIN_SIMPLE_VALUE_LONG_ARGUMENT <= SIMPLE_VALUE_TRUE
    )
    {
      cbor_det_t x = cbor_det_mk_simple_value(SIMPLE_VALUE_TRUE);
      size_t slen = len__uint8_t(out);
      size_t len = cbor_det_size(x, slen);
      option__size_t ser;
      if (len > (size_t)0U)
      {
        uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
        size_t len_ = cbor_det_serialize(x, out1, len);
        ser = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
      }
      else
        ser = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      if (ser.tag == FStar_Pervasives_Native_None)
        return (size_t)0U;
      else if (ser.tag == FStar_Pervasives_Native_Some)
        return ser.v;
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
    size_t slen = len__uint8_t(out);
    size_t len = cbor_det_size(x, slen);
    option__size_t ser;
    if (len > (size_t)0U)
    {
      uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
      size_t len_ = cbor_det_serialize(x, out1, len);
      ser = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
    }
    else
      ser = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
    if (ser.tag == FStar_Pervasives_Native_None)
      return (size_t)0U;
    else if (ser.tag == FStar_Pervasives_Native_Some)
      return ser.v;
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
  uint8_t *elt_ = s.elt + i;
  Pulse_Lib_Slice_slice__uint8_t s1 = { .elt = s.elt, .len = i };
  Pulse_Lib_Slice_slice__uint8_t s2 = { .elt = elt_, .len = s.len - i };
  return
    ((__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){ .fst = s1, .snd = s2 });
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_bool_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_bool(rl);
    if (test)
    {
      bool x = COSE_Format_parse_bool(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bool_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool
COSE_Format_uu___is_Mkevercddl_everparsenomatch_pretty0(
  COSE_Format_evercddl_everparsenomatch_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_everparsenomatch_pretty
COSE_Format_evercddl_everparsenomatch_pretty_right(void)
{
  return COSE_Format_Mkevercddl_everparsenomatch_pretty0;
}

COSE_Format_evercddl_everparsenomatch_pretty COSE_Format_parse_everparsenomatch(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_evercddl_everparsenomatch_pretty
  res2 = COSE_Format_evercddl_everparsenomatch_pretty_right();
  return res2;
}

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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_everparsenomatch_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_everparsenomatch(rl);
    if (test)
    {
      COSE_Format_evercddl_everparsenomatch_pretty x = COSE_Format_parse_everparsenomatch(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_everparsenomatch_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t mt = cbor_det_major_type(c);
  return mt == CBOR_MAJOR_TYPE_UINT64;
}

bool COSE_Format_uu___is_Mkevercddl_uint_pretty0(uint64_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

uint64_t COSE_Format_evercddl_uint_pretty_right(uint64_t x1)
{
  return x1;
}

uint64_t COSE_Format_evercddl_uint_pretty_left(uint64_t x3)
{
  return x3;
}

uint64_t COSE_Format_parse_uint(cbor_det_t c)
{
  uint64_t res = cbor_det_read_uint64(c);
  uint64_t res0 = res;
  uint64_t res1 = res0;
  uint64_t res2 = COSE_Format_evercddl_uint_pretty_right(res1);
  return res2;
}

size_t COSE_Format_serialize_uint(uint64_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  uint64_t c_ = COSE_Format_evercddl_uint_pretty_left(c);
  cbor_det_t x = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, c_);
  size_t slen = len__uint8_t(out);
  size_t len = cbor_det_size(x, slen);
  option__size_t ser;
  if (len > (size_t)0U)
  {
    uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
    size_t len_ = cbor_det_serialize(x, out1, len);
    ser = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
  }
  else
    ser = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (ser.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (ser.tag == FStar_Pervasives_Native_Some)
    return ser.v;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_uint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_uint(rl);
    if (test)
    {
      uint64_t x = COSE_Format_parse_uint(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_uint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t mt = cbor_det_major_type(c);
  return mt == CBOR_MAJOR_TYPE_NEG_INT64;
}

bool COSE_Format_uu___is_Mkevercddl_nint_pretty0(uint64_t projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

uint64_t COSE_Format_evercddl_nint_pretty_right(uint64_t x1)
{
  return x1;
}

uint64_t COSE_Format_evercddl_nint_pretty_left(uint64_t x3)
{
  return x3;
}

uint64_t COSE_Format_parse_nint(cbor_det_t c)
{
  uint64_t res = cbor_det_read_uint64(c);
  uint64_t res0 = res;
  uint64_t res1 = res0;
  uint64_t res2 = COSE_Format_evercddl_nint_pretty_right(res1);
  return res2;
}

size_t COSE_Format_serialize_nint(uint64_t c, Pulse_Lib_Slice_slice__uint8_t out)
{
  uint64_t c_ = COSE_Format_evercddl_nint_pretty_left(c);
  cbor_det_t x = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, c_);
  size_t slen = len__uint8_t(out);
  size_t len = cbor_det_size(x, slen);
  option__size_t ser;
  if (len > (size_t)0U)
  {
    uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
    size_t len_ = cbor_det_serialize(x, out1, len);
    ser = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
  }
  else
    ser = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (ser.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (ser.tag == FStar_Pervasives_Native_Some)
    return ser.v;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_nint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_nint(rl);
    if (test)
    {
      uint64_t x = COSE_Format_parse_nint(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_nint_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  bool test = COSE_Format_validate_uint(c);
  if (test)
    return true;
  else
    return COSE_Format_validate_nint(c);
}

bool COSE_Format_uu___is_Mkevercddl_int_pretty0(COSE_Format_evercddl_int_pretty projectee)
{
  if (projectee.tag == COSE_Format_Mkevercddl_int_pretty0)
    return true;
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_int_pretty1(COSE_Format_evercddl_int_pretty projectee)
{
  if (projectee.tag == COSE_Format_Mkevercddl_int_pretty1)
    return true;
  else
    return false;
}

COSE_Format_evercddl_int_pretty
COSE_Format_evercddl_int_pretty_right(COSE_Format_evercddl_int x2)
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

COSE_Format_evercddl_int
COSE_Format_evercddl_int_pretty_left(COSE_Format_evercddl_int_pretty x7)
{
  if (x7.tag == COSE_Format_Mkevercddl_int_pretty0)
  {
    uint64_t x10 = x7.case_Mkevercddl_int_pretty0;
    return ((COSE_Format_evercddl_int){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_int_pretty1)
  {
    uint64_t x12 = x7.case_Mkevercddl_int_pretty1;
    return ((COSE_Format_evercddl_int){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

COSE_Format_evercddl_int_pretty COSE_Format_parse_int(cbor_det_t c)
{
  bool test = COSE_Format_validate_uint(c);
  COSE_Format_evercddl_int res1;
  if (test)
  {
    uint64_t res = COSE_Format_parse_uint(c);
    res1 = ((COSE_Format_evercddl_int){ .tag = COSE_Format_Inl, { .case_Inl = res } });
  }
  else
  {
    uint64_t res = COSE_Format_parse_nint(c);
    res1 = ((COSE_Format_evercddl_int){ .tag = COSE_Format_Inr, { .case_Inr = res } });
  }
  COSE_Format_evercddl_int_pretty res2 = COSE_Format_evercddl_int_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_int(
  COSE_Format_evercddl_int_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_int c_ = COSE_Format_evercddl_int_pretty_left(c);
  if (c_.tag == COSE_Format_Inl)
  {
    uint64_t c1 = c_.case_Inl;
    size_t res = COSE_Format_serialize_uint(c1, out);
    return res;
  }
  else if (c_.tag == COSE_Format_Inr)
  {
    uint64_t c2 = c_.case_Inr;
    size_t res = COSE_Format_serialize_nint(c2, out);
    return res;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_int_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_int(rl);
    if (test)
    {
      COSE_Format_evercddl_int_pretty x = COSE_Format_parse_int(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_int_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t mt = cbor_det_major_type(c);
  return mt == CBOR_MAJOR_TYPE_BYTE_STRING;
}

bool COSE_Format_uu___is_Mkevercddl_bstr_pretty0(COSE_Format_evercddl_bstr projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_bstr_pretty_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t
COSE_Format_evercddl_bstr_pretty_left(COSE_Format_evercddl_bstr x3)
{
  return x3;
}

static Pulse_Lib_Slice_slice__uint8_t arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

COSE_Format_evercddl_bstr COSE_Format_parse_bstr(cbor_det_t c)
{
  uint64_t len = cbor_det_get_string_length(c);
  uint8_t *a = cbor_det_get_string(c);
  Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
  Pulse_Lib_Slice_slice__uint8_t sl = s;
  Pulse_Lib_Slice_slice__uint8_t s0 = sl;
  Pulse_Lib_Slice_slice__uint8_t res1 = s0;
  COSE_Format_evercddl_bstr res2 = COSE_Format_evercddl_bstr_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_bstr(COSE_Format_evercddl_bstr c, Pulse_Lib_Slice_slice__uint8_t out)
{
  Pulse_Lib_Slice_slice__uint8_t c_ = COSE_Format_evercddl_bstr_pretty_left(c);
  size_t len = len__uint8_t(c_);
  if (len <= (size_t)18446744073709551615ULL)
  {
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(c_);
    uint8_t *a0 = a;
    cbor_det_t
    res =
      cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_BYTE_STRING,
        a0,
        (uint64_t)len__uint8_t(c_));
    cbor_det_t x = res;
    size_t slen = len__uint8_t(out);
    size_t len1 = cbor_det_size(x, slen);
    option__size_t ser;
    if (len1 > (size_t)0U)
    {
      uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
      size_t len_ = cbor_det_serialize(x, out1, len1);
      ser = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
    }
    else
      ser = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
    if (ser.tag == FStar_Pervasives_Native_None)
      return (size_t)0U;
    else if (ser.tag == FStar_Pervasives_Native_Some)
      return ser.v;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_bstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_bstr(rl);
    if (test)
    {
      COSE_Format_evercddl_bstr x = COSE_Format_parse_bstr(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (24ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_bstr(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_encodedcbor_pretty0(COSE_Format_evercddl_bstr_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_bstr_pretty
COSE_Format_evercddl_encodedcbor_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_encodedcbor_pretty_left(COSE_Format_evercddl_bstr_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_bstr_pretty COSE_Format_parse_encodedcbor(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_bstr res = COSE_Format_parse_bstr(cpl);
  COSE_Format_evercddl_bstr res1 = res;
  COSE_Format_evercddl_bstr_pretty res2 = COSE_Format_evercddl_encodedcbor_pretty_right(res1);
  return res2;
}

typedef struct __uint64_t_COSE_Format_evercddl_bstr_pretty_s
{
  uint64_t fst;
  COSE_Format_evercddl_bstr snd;
}
__uint64_t_COSE_Format_evercddl_bstr_pretty;

size_t
COSE_Format_serialize_encodedcbor(
  COSE_Format_evercddl_bstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_bstr c_ = COSE_Format_evercddl_encodedcbor_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_bstr_pretty c_1 = { .fst = 24ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_bstr_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_bstr cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_bstr(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_encodedcbor_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_encodedcbor(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_encodedcbor_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_encodedcbor(rl);
    if (test)
    {
      COSE_Format_evercddl_bstr_pretty x = COSE_Format_parse_encodedcbor(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_encodedcbor_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_uu___is_Mkevercddl_bytes_pretty0(COSE_Format_evercddl_bstr_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_bstr_pretty
COSE_Format_evercddl_bytes_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_bytes_pretty_left(COSE_Format_evercddl_bstr_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_bstr_pretty COSE_Format_parse_bytes(cbor_det_t c)
{
  COSE_Format_evercddl_bstr res1 = COSE_Format_parse_bstr(c);
  COSE_Format_evercddl_bstr_pretty res2 = COSE_Format_evercddl_bytes_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_bytes(
  COSE_Format_evercddl_bstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_bstr c_ = COSE_Format_evercddl_bytes_pretty_left(c);
  size_t res = COSE_Format_serialize_bstr(c_, out);
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_bytes_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_bytes(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_bytes_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_bytes(rl);
    if (test)
    {
      COSE_Format_evercddl_bstr_pretty x = COSE_Format_parse_bytes(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_bytes_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t mt = cbor_det_major_type(c);
  return mt == CBOR_MAJOR_TYPE_TEXT_STRING;
}

bool COSE_Format_uu___is_Mkevercddl_tstr_pretty0(COSE_Format_evercddl_bstr projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_tstr_pretty_right(Pulse_Lib_Slice_slice__uint8_t x1)
{
  return x1;
}

Pulse_Lib_Slice_slice__uint8_t
COSE_Format_evercddl_tstr_pretty_left(COSE_Format_evercddl_bstr x3)
{
  return x3;
}

COSE_Format_evercddl_bstr COSE_Format_parse_tstr(cbor_det_t c)
{
  uint64_t len = cbor_det_get_string_length(c);
  uint8_t *a = cbor_det_get_string(c);
  Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
  Pulse_Lib_Slice_slice__uint8_t sl = s;
  Pulse_Lib_Slice_slice__uint8_t s0 = sl;
  Pulse_Lib_Slice_slice__uint8_t res1 = s0;
  COSE_Format_evercddl_bstr res2 = COSE_Format_evercddl_tstr_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_tstr(COSE_Format_evercddl_bstr c, Pulse_Lib_Slice_slice__uint8_t out)
{
  Pulse_Lib_Slice_slice__uint8_t c_ = COSE_Format_evercddl_tstr_pretty_left(c);
  size_t len = len__uint8_t(c_);
  if (len <= (size_t)18446744073709551615ULL)
  {
    size_t alen = len__uint8_t(c_);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(c_);
    bool res = cbor_det_impl_utf8_correct_from_array(a, alen);
    bool correct = res;
    if (correct)
    {
      uint8_t *a = slice_to_arrayptr_intro__uint8_t(c_);
      uint8_t *a0 = a;
      cbor_det_t
      res =
        cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
          a0,
          (uint64_t)len__uint8_t(c_));
      cbor_det_t x = res;
      size_t slen = len__uint8_t(out);
      size_t len1 = cbor_det_size(x, slen);
      option__size_t ser;
      if (len1 > (size_t)0U)
      {
        uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
        size_t len_ = cbor_det_serialize(x, out1, len1);
        ser = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
      }
      else
        ser = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      if (ser.tag == FStar_Pervasives_Native_None)
        return (size_t)0U;
      else if (ser.tag == FStar_Pervasives_Native_Some)
        return ser.v;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_tstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_tstr(rl);
    if (test)
    {
      COSE_Format_evercddl_bstr x = COSE_Format_parse_tstr(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_tstr_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  bool test = COSE_Format_validate_int(c);
  if (test)
    return true;
  else
    return COSE_Format_validate_tstr(c);
}

bool COSE_Format_uu___is_Mkevercddl_label_pretty0(COSE_Format_evercddl_label_pretty projectee)
{
  if (projectee.tag == COSE_Format_Mkevercddl_label_pretty0)
    return true;
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_label_pretty1(COSE_Format_evercddl_label_pretty projectee)
{
  if (projectee.tag == COSE_Format_Mkevercddl_label_pretty1)
    return true;
  else
    return false;
}

COSE_Format_evercddl_label_pretty
COSE_Format_evercddl_label_pretty_right(COSE_Format_evercddl_label x2)
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

COSE_Format_evercddl_label
COSE_Format_evercddl_label_pretty_left(COSE_Format_evercddl_label_pretty x7)
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

COSE_Format_evercddl_label_pretty COSE_Format_parse_label(cbor_det_t c)
{
  bool test = COSE_Format_validate_int(c);
  COSE_Format_evercddl_label res1;
  if (test)
  {
    COSE_Format_evercddl_int_pretty res = COSE_Format_parse_int(c);
    res1 = ((COSE_Format_evercddl_label){ .tag = COSE_Format_Inl, { .case_Inl = res } });
  }
  else
  {
    COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(c);
    res1 = ((COSE_Format_evercddl_label){ .tag = COSE_Format_Inr, { .case_Inr = res } });
  }
  COSE_Format_evercddl_label_pretty res2 = COSE_Format_evercddl_label_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_label(
  COSE_Format_evercddl_label_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_label c_ = COSE_Format_evercddl_label_pretty_left(c);
  if (c_.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_int_pretty c1 = c_.case_Inl;
    size_t res = COSE_Format_serialize_int(c1, out);
    return res;
  }
  else if (c_.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_bstr c2 = c_.case_Inr;
    size_t res = COSE_Format_serialize_tstr(c2, out);
    return res;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_label_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_label(rl);
    if (test)
    {
      COSE_Format_evercddl_label_pretty x = COSE_Format_parse_label(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_label_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

typedef struct option__CBOR_Pulse_API_Det_Type_cbor_det_t_s
{
  FStar_Pervasives_Native_option__size_t_tags tag;
  cbor_det_t v;
}
option__CBOR_Pulse_API_Det_Type_cbor_det_t;

bool COSE_Format_validate_COSE_Key_OKP(cbor_det_t c)
{
  uint8_t ty = cbor_det_major_type(c);
  if (ty == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t rem0 = cbor_det_get_map_length(c);
    uint64_t remaining = rem0;
    cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest0 = c10;
    bool bres0 = cbor_det_map_get(c, c10, &dest0);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t mg0;
    if (bres0)
    {
      cbor_det_t res = dest0;
      mg0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      mg0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    impl_map_group_result res0;
    if (mg0.tag == FStar_Pervasives_Native_None)
      res0 = MGFail;
    else if (mg0.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t cv = mg0.v;
      uint8_t mt = cbor_det_major_type(cv);
      bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
      bool check_value;
      if (is_uint)
      {
        uint64_t i = cbor_det_read_uint64(cv);
        check_value = i == 1ULL;
      }
      else
        check_value = false;
      if (check_value)
      {
        uint64_t i1 = remaining;
        uint64_t i2 = i1 - 1ULL;
        remaining = i2;
        res0 = MGOK;
      }
      else
        res0 = MGFail;
    }
    else
      res0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    impl_map_group_result res2 = res0;
    impl_map_group_result res10 = res2;
    impl_map_group_result res11;
    switch (res10)
    {
      case MGOK:
        {
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 0ULL);
          cbor_det_t dest = c1;
          bool bres = cbor_det_map_get(c, c1, &dest);
          option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
          if (bres)
          {
            cbor_det_t res = dest;
            mg =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = res
                }
              );
          }
          else
            mg =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result res;
          if (mg.tag == FStar_Pervasives_Native_None)
            res = MGFail;
          else if (mg.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = mg.v;
            bool test = COSE_Format_validate_int(cv);
            bool check_value;
            if (test)
              check_value = true;
            else
              check_value = COSE_Format_validate_tstr(cv);
            if (check_value)
            {
              uint64_t i1 = remaining;
              uint64_t i2 = i1 - 1ULL;
              remaining = i2;
              res = MGOK;
            }
            else
              res = MGFail;
          }
          else
            res =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          impl_map_group_result res0 = res;
          impl_map_group_result res1 = res0;
          res11 = res1;
          break;
        }
      case MGFail:
        {
          res11 = MGFail;
          break;
        }
      case MGCutFail:
        {
          res11 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result res1;
    switch (res11)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
          cbor_det_t dest = c1;
          bool bres = cbor_det_map_get(c, c1, &dest);
          option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
          if (bres)
          {
            cbor_det_t res = dest;
            mg =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = res
                }
              );
          }
          else
            mg =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result res0;
          if (mg.tag == FStar_Pervasives_Native_None)
            res0 = MGFail;
          else if (mg.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = mg.v;
            bool check_value = COSE_Format_validate_bstr(cv);
            if (check_value)
            {
              uint64_t i1 = remaining;
              uint64_t i2 = i1 - 1ULL;
              remaining = i2;
              res0 = MGOK;
            }
            else
              res0 = MGFail;
          }
          else
            res0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          impl_map_group_result res2 = res0;
          impl_map_group_result res11 = res2;
          impl_map_group_result res;
          switch (res11)
          {
            case MGOK:
              {
                res = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                res = MGOK;
                break;
              }
            case MGCutFail:
              {
                res = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          res1 = res;
          break;
        }
      case MGFail:
        {
          res1 = MGFail;
          break;
        }
      case MGCutFail:
        {
          res1 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result res3;
    switch (res1)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
          cbor_det_t dest = c1;
          bool bres = cbor_det_map_get(c, c1, &dest);
          option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
          if (bres)
          {
            cbor_det_t res = dest;
            mg =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = res
                }
              );
          }
          else
            mg =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result res0;
          if (mg.tag == FStar_Pervasives_Native_None)
            res0 = MGFail;
          else if (mg.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = mg.v;
            bool check_value = COSE_Format_validate_bstr(cv);
            if (check_value)
            {
              uint64_t i1 = remaining;
              uint64_t i2 = i1 - 1ULL;
              remaining = i2;
              res0 = MGOK;
            }
            else
              res0 = MGFail;
          }
          else
            res0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          impl_map_group_result res1 = res0;
          impl_map_group_result res11 = res1;
          impl_map_group_result res;
          switch (res11)
          {
            case MGOK:
              {
                res = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                res = MGOK;
                break;
              }
            case MGCutFail:
              {
                res = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          res3 = res;
          break;
        }
      case MGFail:
        {
          res3 = MGFail;
          break;
        }
      case MGCutFail:
        {
          res3 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (res3)
    {
      case MGOK:
        {
          uint64_t rem = remaining;
          return rem == 0ULL;
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

bool
COSE_Format_uu___is_Mkevercddl_COSE_Key_OKP_pretty0(
  COSE_Format_evercddl_COSE_Key_OKP_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_COSE_Key_OKP_pretty
COSE_Format_evercddl_COSE_Key_OKP_pretty_right(COSE_Format_evercddl_COSE_Key_OKP x4)
{
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x8 = x4.snd;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x7 = x4.fst.snd;
  COSE_Format_evercddl_label x6 = x4.fst.fst;
  return ((COSE_Format_evercddl_COSE_Key_OKP_pretty){ .x1 = x6, .x2 = x7, .x3 = x8 });
}

COSE_Format_evercddl_COSE_Key_OKP
COSE_Format_evercddl_COSE_Key_OKP_pretty_left(COSE_Format_evercddl_COSE_Key_OKP_pretty x9)
{
  COSE_Format_evercddl_label x16 = x9.x1;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x17 = x9.x2;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x18 = x9.x3;
  return ((COSE_Format_evercddl_COSE_Key_OKP){ .fst = { .fst = x16, .snd = x17 }, .snd = x18 });
}

COSE_Format_evercddl_COSE_Key_OKP_pretty COSE_Format_parse_COSE_Key_OKP(cbor_det_t c)
{
  cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
  cbor_det_t dest0 = c10;
  bool bres0 = cbor_det_map_get(c, c10, &dest0);
  option__CBOR_Pulse_API_Det_Type_cbor_det_t ow0;
  if (bres0)
  {
    cbor_det_t res = dest0;
    ow0 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = res
        }
      );
  }
  else
    ow0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow0;
  if (!(_letpattern.tag == FStar_Pervasives_Native_Some))
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 0ULL);
  cbor_det_t dest1 = c11;
  bool bres1 = cbor_det_map_get(c, c11, &dest1);
  option__CBOR_Pulse_API_Det_Type_cbor_det_t ow1;
  if (bres1)
  {
    cbor_det_t res = dest1;
    ow1 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = res
        }
      );
  }
  else
    ow1 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern0 = ow1;
  COSE_Format_evercddl_label res0;
  if (_letpattern0.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t w = _letpattern0.v;
    bool test = COSE_Format_validate_int(w);
    COSE_Format_evercddl_label res1;
    if (test)
    {
      COSE_Format_evercddl_int_pretty res = COSE_Format_parse_int(w);
      res1 = ((COSE_Format_evercddl_label){ .tag = COSE_Format_Inl, { .case_Inl = res } });
    }
    else
    {
      COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(w);
      res1 = ((COSE_Format_evercddl_label){ .tag = COSE_Format_Inr, { .case_Inr = res } });
    }
    res0 = res1;
  }
  else
    res0 =
      KRML_EABORT(COSE_Format_evercddl_label,
        "unreachable (pattern matches are exhaustive in F*)");
  COSE_Format_evercddl_label w2 = res0;
  COSE_Format_evercddl_label w1 = w2;
  uint64_t dummy0 = 0ULL;
  KRML_HOST_IGNORE(&dummy0);
  cbor_det_t c12 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
  cbor_det_t dest2 = c12;
  bool bres2 = cbor_det_map_get(c, c12, &dest2);
  option__CBOR_Pulse_API_Det_Type_cbor_det_t mg0;
  if (bres2)
  {
    cbor_det_t res = dest2;
    mg0 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = res
        }
      );
  }
  else
    mg0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result res1;
  if (mg0.tag == FStar_Pervasives_Native_None)
    res1 = MGFail;
  else if (mg0.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = mg0.v;
    bool check_value = COSE_Format_validate_bstr(cv);
    if (check_value)
      res1 = MGOK;
    else
      res1 = MGFail;
  }
  else
    res1 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  impl_map_group_result res2 = res1;
  impl_map_group_result test1 = res2;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty _bind_c0;
  if (uu___is_MGOK(test1))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
    cbor_det_t dest = c1;
    bool bres = cbor_det_map_get(c, c1, &dest);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
    if (bres)
    {
      cbor_det_t res = dest;
      ow =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
    COSE_Format_evercddl_bstr res;
    if (_letpattern.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = _letpattern.v;
      COSE_Format_evercddl_bstr res0 = COSE_Format_parse_bstr(w);
      res = res0;
    }
    else
      res =
        KRML_EABORT(COSE_Format_evercddl_bstr,
          "unreachable (pattern matches are exhaustive in F*)");
    COSE_Format_evercddl_bstr w11 = res;
    _bind_c0 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = w11
        }
      );
  }
  else
    _bind_c0 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty w20 = _bind_c0;
  K_________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  w10 = { .fst = w1, .snd = w20 };
  uint64_t dummy = 0ULL;
  KRML_HOST_IGNORE(&dummy);
  cbor_det_t c13 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
  cbor_det_t dest3 = c13;
  bool bres3 = cbor_det_map_get(c, c13, &dest3);
  option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
  if (bres3)
  {
    cbor_det_t res = dest3;
    mg =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = res
        }
      );
  }
  else
    mg = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result res3;
  if (mg.tag == FStar_Pervasives_Native_None)
    res3 = MGFail;
  else if (mg.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = mg.v;
    bool check_value = COSE_Format_validate_bstr(cv);
    if (check_value)
      res3 = MGOK;
    else
      res3 = MGFail;
  }
  else
    res3 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  impl_map_group_result res4 = res3;
  impl_map_group_result test10 = res4;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty _bind_c;
  if (uu___is_MGOK(test10))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
    cbor_det_t dest = c1;
    bool bres = cbor_det_map_get(c, c1, &dest);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
    if (bres)
    {
      cbor_det_t res = dest;
      ow =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
    COSE_Format_evercddl_bstr res;
    if (_letpattern.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = _letpattern.v;
      COSE_Format_evercddl_bstr res0 = COSE_Format_parse_bstr(w);
      res = res0;
    }
    else
      res =
        KRML_EABORT(COSE_Format_evercddl_bstr,
          "unreachable (pattern matches are exhaustive in F*)");
    COSE_Format_evercddl_bstr w11 = res;
    _bind_c =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = w11
        }
      );
  }
  else
    _bind_c =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty w21 = _bind_c;
  COSE_Format_evercddl_COSE_Key_OKP res10 = { .fst = w10, .snd = w21 };
  COSE_Format_evercddl_COSE_Key_OKP_pretty
  res20 = COSE_Format_evercddl_COSE_Key_OKP_pretty_right(res10);
  return res20;
}

size_t
COSE_Format_serialize_COSE_Key_OKP(
  COSE_Format_evercddl_COSE_Key_OKP_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Key_OKP c_ = COSE_Format_evercddl_COSE_Key_OKP_pretty_left(c);
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_evercddl_COSE_Key_OKP _letpattern = c_;
  K_________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  c1 = _letpattern.fst;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty c2 = _letpattern.snd;
  K_________FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  _letpattern10 = c1;
  COSE_Format_evercddl_label c110 = _letpattern10.fst;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty c21 = _letpattern10.snd;
  COSE_Format_evercddl_label _letpattern20 = c110;
  COSE_Format_evercddl_label c22 = _letpattern20;
  uint64_t count0 = pcount;
  bool res10;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size0 = psize;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern3 = split__uint8_t(out, size0);
    Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
    cbor_det_t c30 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    size_t slen0 = len__uint8_t(out1);
    size_t len = cbor_det_size(c30, slen0);
    option__size_t res0;
    if (len > (size_t)0U)
    {
      uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
      size_t len_ = cbor_det_serialize(c30, out2, len);
      res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
    }
    else
      res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
    size_t res1;
    if (res0.tag == FStar_Pervasives_Native_None)
      res1 = (size_t)0U;
    else if (res0.tag == FStar_Pervasives_Native_Some)
      res1 = res0.v;
    else
      res1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
    size_t res11 = res1;
    if (res11 > (size_t)0U)
    {
      size_t size1 = size0 + res11;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern4 = split__uint8_t(out, size1);
      Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern4.snd;
      cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
      size_t slen = len__uint8_t(out2);
      size_t len = cbor_det_size(c3, slen);
      option__size_t res0;
      if (len > (size_t)0U)
      {
        uint8_t *out3 = slice_to_arrayptr_intro__uint8_t(out2);
        size_t len_ = cbor_det_serialize(c3, out3, len);
        res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
      }
      else
        res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      size_t res;
      if (res0.tag == FStar_Pervasives_Native_None)
        res = (size_t)0U;
      else if (res0.tag == FStar_Pervasives_Native_Some)
        res = res0.v;
      else
        res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      size_t res2 = res;
      if (res2 > (size_t)0U)
      {
        size_t size2 = size1 + res2;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern5 = split__uint8_t(out, size2);
        Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern5.fst;
        size_t aout_len = len__uint8_t(out012);
        uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
        bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
        bool res0 = res;
        if (res0)
        {
          psize = size2;
          pcount = count0 + 1ULL;
          res10 = true;
        }
        else
          res10 = false;
      }
      else
        res10 = false;
    }
    else
      res10 = false;
  }
  else
    res10 = false;
  bool res11;
  if (res10)
  {
    uint64_t count = pcount;
    bool res20;
    if (count < 18446744073709551615ULL)
    {
      size_t size0 = psize;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern3 = split__uint8_t(out, size0);
      Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
      cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 0ULL);
      size_t slen = len__uint8_t(out1);
      size_t len = cbor_det_size(c3, slen);
      option__size_t res0;
      if (len > (size_t)0U)
      {
        uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
        size_t len_ = cbor_det_serialize(c3, out2, len);
        res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
      }
      else
        res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      size_t res;
      if (res0.tag == FStar_Pervasives_Native_None)
        res = (size_t)0U;
      else if (res0.tag == FStar_Pervasives_Native_Some)
        res = res0.v;
      else
        res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      size_t res11 = res;
      if (res11 > (size_t)0U)
      {
        size_t size1 = size0 + res11;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern4 = split__uint8_t(out, size1);
        Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern4.snd;
        size_t res2;
        if (c22.tag == COSE_Format_Inl)
        {
          COSE_Format_evercddl_int_pretty c13 = c22.case_Inl;
          size_t res = COSE_Format_serialize_int(c13, out2);
          res2 = res;
        }
        else if (c22.tag == COSE_Format_Inr)
        {
          COSE_Format_evercddl_bstr c23 = c22.case_Inr;
          size_t res = COSE_Format_serialize_tstr(c23, out2);
          res2 = res;
        }
        else
          res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res2 > (size_t)0U)
        {
          size_t size2 = size1 + res2;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern5 = split__uint8_t(out, size2);
          Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern5.fst;
          size_t aout_len = len__uint8_t(out012);
          uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
          bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
          bool res0 = res;
          if (res0)
          {
            psize = size2;
            pcount = count + 1ULL;
            res20 = true;
          }
          else
            res20 = false;
        }
        else
          res20 = false;
      }
      else
        res20 = false;
    }
    else
      res20 = false;
    res11 = res20;
  }
  else
    res11 = false;
  bool res1;
  if (res11)
  {
    bool res2;
    if (c21.tag == FStar_Pervasives_Native_Some)
    {
      COSE_Format_evercddl_bstr c12 = c21.v;
      uint64_t count = pcount;
      bool res0;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern2 = split__uint8_t(out, size0);
        Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 1ULL);
        size_t slen = len__uint8_t(out1);
        size_t len = cbor_det_size(c3, slen);
        option__size_t res1;
        if (len > (size_t)0U)
        {
          uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
          size_t len_ = cbor_det_serialize(c3, out2, len);
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
        }
        else
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res;
        if (res1.tag == FStar_Pervasives_Native_None)
          res = (size_t)0U;
        else if (res1.tag == FStar_Pervasives_Native_Some)
          res = res1.v;
        else
          res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        size_t res11 = res;
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern3 = split__uint8_t(out, size1);
          Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern3.snd;
          size_t res2 = COSE_Format_serialize_bstr(c12, out2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern4 = split__uint8_t(out, size2);
            Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern4.fst;
            size_t aout_len = len__uint8_t(out012);
            uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
            bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
            bool res1 = res;
            if (res1)
            {
              psize = size2;
              pcount = count + 1ULL;
              res0 = true;
            }
            else
              res0 = false;
          }
          else
            res0 = false;
        }
        else
          res0 = false;
      }
      else
        res0 = false;
      res2 = res0;
    }
    else if (c21.tag == FStar_Pervasives_Native_None)
      res2 = true;
    else
      res2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
    res1 = res2;
  }
  else
    res1 = false;
  bool res0;
  if (res1)
  {
    bool res2;
    if (c2.tag == FStar_Pervasives_Native_Some)
    {
      COSE_Format_evercddl_bstr c11 = c2.v;
      uint64_t count = pcount;
      bool res0;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern1 = split__uint8_t(out, size0);
        Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern1.snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, 3ULL);
        size_t slen = len__uint8_t(out1);
        size_t len = cbor_det_size(c3, slen);
        option__size_t res1;
        if (len > (size_t)0U)
        {
          uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
          size_t len_ = cbor_det_serialize(c3, out2, len);
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
        }
        else
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res;
        if (res1.tag == FStar_Pervasives_Native_None)
          res = (size_t)0U;
        else if (res1.tag == FStar_Pervasives_Native_Some)
          res = res1.v;
        else
          res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        size_t res11 = res;
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern2 = split__uint8_t(out, size1);
          Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern2.snd;
          size_t res2 = COSE_Format_serialize_bstr(c11, out2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern3 = split__uint8_t(out, size2);
            Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern3.fst;
            size_t aout_len = len__uint8_t(out012);
            uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
            bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
            bool res1 = res;
            if (res1)
            {
              psize = size2;
              pcount = count + 1ULL;
              res0 = true;
            }
            else
              res0 = false;
          }
          else
            res0 = false;
        }
        else
          res0 = false;
      }
      else
        res0 = false;
      res2 = res0;
    }
    else if (c2.tag == FStar_Pervasives_Native_None)
      res2 = true;
    else
      res2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
    res0 = res2;
  }
  else
    res0 = false;
  size_t _bind_c;
  if (res0)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = len__uint8_t(out);
    uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
    size_t res1 = cbor_det_serialize_map_to_array(count, aout, aout_len, size);
    _bind_c = res1;
  }
  else
    _bind_c = (size_t)0U;
  size_t res = _bind_c;
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_OKP_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Key_OKP(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_OKP_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Key_OKP(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Key_OKP_pretty x = COSE_Format_parse_COSE_Key_OKP(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_OKP_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool
COSE_Format_uu___is_Mkevercddl_COSE_Key_pretty0(
  COSE_Format_evercddl_COSE_Key_OKP_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_COSE_Key_OKP_pretty
COSE_Format_evercddl_COSE_Key_pretty_right(COSE_Format_evercddl_COSE_Key_OKP_pretty x1)
{
  return x1;
}

COSE_Format_evercddl_COSE_Key_OKP_pretty
COSE_Format_evercddl_COSE_Key_pretty_left(COSE_Format_evercddl_COSE_Key_OKP_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_COSE_Key_OKP_pretty COSE_Format_parse_COSE_Key(cbor_det_t c)
{
  COSE_Format_evercddl_COSE_Key_OKP_pretty res1 = COSE_Format_parse_COSE_Key_OKP(c);
  COSE_Format_evercddl_COSE_Key_OKP_pretty
  res2 = COSE_Format_evercddl_COSE_Key_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_COSE_Key(
  COSE_Format_evercddl_COSE_Key_OKP_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Key_OKP_pretty c_ = COSE_Format_evercddl_COSE_Key_pretty_left(c);
  size_t res = COSE_Format_serialize_COSE_Key_OKP(c_, out);
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Key(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Key(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Key_OKP_pretty x = COSE_Format_parse_COSE_Key(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_validate_tdate(cbor_det_t c)
{
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (0ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_tstr(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_tdate_pretty0(COSE_Format_evercddl_tstr_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_tstr_pretty
COSE_Format_evercddl_tdate_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_tdate_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_tstr_pretty COSE_Format_parse_tdate(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(cpl);
  COSE_Format_evercddl_bstr res1 = res;
  COSE_Format_evercddl_tstr_pretty res2 = COSE_Format_evercddl_tdate_pretty_right(res1);
  return res2;
}

typedef struct __uint64_t_COSE_Format_evercddl_tstr_pretty_s
{
  uint64_t fst;
  COSE_Format_evercddl_bstr snd;
}
__uint64_t_COSE_Format_evercddl_tstr_pretty;

size_t
COSE_Format_serialize_tdate(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_bstr c_ = COSE_Format_evercddl_tdate_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_tstr_pretty c_1 = { .fst = 0ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_tstr_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_bstr cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_tdate_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_tdate(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_tdate_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_tdate(rl);
    if (test)
    {
      COSE_Format_evercddl_tstr_pretty x = COSE_Format_parse_tdate(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_tdate_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (32ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_tstr(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_uri_pretty0(COSE_Format_evercddl_tstr_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_tstr_pretty
COSE_Format_evercddl_uri_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_uri_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_tstr_pretty COSE_Format_parse_uri(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(cpl);
  COSE_Format_evercddl_bstr res1 = res;
  COSE_Format_evercddl_tstr_pretty res2 = COSE_Format_evercddl_uri_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_uri(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_bstr c_ = COSE_Format_evercddl_uri_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_tstr_pretty c_1 = { .fst = 32ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_tstr_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_bstr cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_uri_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_uri(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_uri_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_uri(rl);
    if (test)
    {
      COSE_Format_evercddl_tstr_pretty x = COSE_Format_parse_uri(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_uri_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (33ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_tstr(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_b64url_pretty0(COSE_Format_evercddl_tstr_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_tstr_pretty
COSE_Format_evercddl_b64url_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_b64url_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_tstr_pretty COSE_Format_parse_b64url(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(cpl);
  COSE_Format_evercddl_bstr res1 = res;
  COSE_Format_evercddl_tstr_pretty res2 = COSE_Format_evercddl_b64url_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_b64url(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_bstr c_ = COSE_Format_evercddl_b64url_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_tstr_pretty c_1 = { .fst = 33ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_tstr_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_bstr cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_b64url_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_b64url(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_b64url(rl);
    if (test)
    {
      COSE_Format_evercddl_tstr_pretty x = COSE_Format_parse_b64url(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (34ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_tstr(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_b64legacy_pretty0(COSE_Format_evercddl_tstr_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_tstr_pretty
COSE_Format_evercddl_b64legacy_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_b64legacy_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_tstr_pretty COSE_Format_parse_b64legacy(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(cpl);
  COSE_Format_evercddl_bstr res1 = res;
  COSE_Format_evercddl_tstr_pretty res2 = COSE_Format_evercddl_b64legacy_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_b64legacy(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_bstr c_ = COSE_Format_evercddl_b64legacy_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_tstr_pretty c_1 = { .fst = 34ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_tstr_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_bstr cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_b64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_b64legacy(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_b64legacy(rl);
    if (test)
    {
      COSE_Format_evercddl_tstr_pretty x = COSE_Format_parse_b64legacy(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_b64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (35ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_tstr(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_regexp_pretty0(COSE_Format_evercddl_tstr_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_tstr_pretty
COSE_Format_evercddl_regexp_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_regexp_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_tstr_pretty COSE_Format_parse_regexp(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(cpl);
  COSE_Format_evercddl_bstr res1 = res;
  COSE_Format_evercddl_tstr_pretty res2 = COSE_Format_evercddl_regexp_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_regexp(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_bstr c_ = COSE_Format_evercddl_regexp_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_tstr_pretty c_1 = { .fst = 35ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_tstr_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_bstr cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_regexp_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_regexp(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_regexp_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_regexp(rl);
    if (test)
    {
      COSE_Format_evercddl_tstr_pretty x = COSE_Format_parse_regexp(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_regexp_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (36ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_tstr(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_mimemessage_pretty0(COSE_Format_evercddl_tstr_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_tstr_pretty
COSE_Format_evercddl_mimemessage_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_mimemessage_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_tstr_pretty COSE_Format_parse_mimemessage(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(cpl);
  COSE_Format_evercddl_bstr res1 = res;
  COSE_Format_evercddl_tstr_pretty res2 = COSE_Format_evercddl_mimemessage_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_mimemessage(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_bstr c_ = COSE_Format_evercddl_mimemessage_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_tstr_pretty c_1 = { .fst = 36ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_tstr_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_bstr cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_tstr(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_mimemessage_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_mimemessage(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_mimemessage_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_mimemessage(rl);
    if (test)
    {
      COSE_Format_evercddl_tstr_pretty x = COSE_Format_parse_mimemessage(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_mimemessage_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_uu___is_Mkevercddl_text_pretty0(COSE_Format_evercddl_tstr_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_tstr_pretty
COSE_Format_evercddl_text_pretty_right(COSE_Format_evercddl_bstr x1)
{
  return x1;
}

COSE_Format_evercddl_bstr
COSE_Format_evercddl_text_pretty_left(COSE_Format_evercddl_tstr_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_tstr_pretty COSE_Format_parse_text(cbor_det_t c)
{
  COSE_Format_evercddl_bstr res1 = COSE_Format_parse_tstr(c);
  COSE_Format_evercddl_tstr_pretty res2 = COSE_Format_evercddl_text_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_text(
  COSE_Format_evercddl_tstr_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_bstr c_ = COSE_Format_evercddl_text_pretty_left(c);
  size_t res = COSE_Format_serialize_tstr(c_, out);
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_text_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_text(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_text_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_text(rl);
    if (test)
    {
      COSE_Format_evercddl_tstr_pretty x = COSE_Format_parse_text(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_text_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t mt = cbor_det_major_type(c);
  bool test = mt == CBOR_MAJOR_TYPE_SIMPLE_VALUE;
  if (test)
  {
    uint8_t v1 = cbor_det_read_simple_value(c);
    return v1 == 20U;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_false_pretty0(COSE_Format_evercddl_false_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_false_pretty COSE_Format_evercddl_false_pretty_right(void)
{
  return COSE_Format_Mkevercddl_false_pretty0;
}

COSE_Format_evercddl_false_pretty COSE_Format_parse_false(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_evercddl_false_pretty res2 = COSE_Format_evercddl_false_pretty_right();
  return res2;
}

size_t
COSE_Format_serialize_false(
  COSE_Format_evercddl_false_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  cbor_det_t c1 = cbor_det_mk_simple_value(20U);
  size_t slen = len__uint8_t(out);
  size_t len = cbor_det_size(c1, slen);
  option__size_t res0;
  if (len > (size_t)0U)
  {
    uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
    size_t len_ = cbor_det_serialize(c1, out1, len);
    res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
  }
  else
    res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  size_t res;
  if (res0.tag == FStar_Pervasives_Native_None)
    res = (size_t)0U;
  else if (res0.tag == FStar_Pervasives_Native_Some)
    res = res0.v;
  else
    res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_false_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_false(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_false_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_false(rl);
    if (test)
    {
      COSE_Format_evercddl_false_pretty x = COSE_Format_parse_false(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_false_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t mt = cbor_det_major_type(c);
  bool test = mt == CBOR_MAJOR_TYPE_SIMPLE_VALUE;
  if (test)
  {
    uint8_t v1 = cbor_det_read_simple_value(c);
    return v1 == 21U;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_true_pretty0(COSE_Format_evercddl_true_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_true_pretty COSE_Format_evercddl_true_pretty_right(void)
{
  return COSE_Format_Mkevercddl_true_pretty0;
}

COSE_Format_evercddl_true_pretty COSE_Format_parse_true(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_evercddl_true_pretty res2 = COSE_Format_evercddl_true_pretty_right();
  return res2;
}

size_t
COSE_Format_serialize_true(
  COSE_Format_evercddl_true_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  cbor_det_t c1 = cbor_det_mk_simple_value(21U);
  size_t slen = len__uint8_t(out);
  size_t len = cbor_det_size(c1, slen);
  option__size_t res0;
  if (len > (size_t)0U)
  {
    uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
    size_t len_ = cbor_det_serialize(c1, out1, len);
    res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
  }
  else
    res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  size_t res;
  if (res0.tag == FStar_Pervasives_Native_None)
    res = (size_t)0U;
  else if (res0.tag == FStar_Pervasives_Native_Some)
    res = res0.v;
  else
    res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_true_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_true(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_true_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_true(rl);
    if (test)
    {
      COSE_Format_evercddl_true_pretty x = COSE_Format_parse_true(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_true_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t mt = cbor_det_major_type(c);
  bool test = mt == CBOR_MAJOR_TYPE_SIMPLE_VALUE;
  if (test)
  {
    uint8_t v1 = cbor_det_read_simple_value(c);
    return v1 == 22U;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_nil_pretty0(COSE_Format_evercddl_nil_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_nil_pretty COSE_Format_evercddl_nil_pretty_right(void)
{
  return COSE_Format_Mkevercddl_nil_pretty0;
}

COSE_Format_evercddl_nil_pretty COSE_Format_parse_nil(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_evercddl_nil_pretty res2 = COSE_Format_evercddl_nil_pretty_right();
  return res2;
}

size_t
COSE_Format_serialize_nil(
  COSE_Format_evercddl_nil_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  cbor_det_t c1 = cbor_det_mk_simple_value(22U);
  size_t slen = len__uint8_t(out);
  size_t len = cbor_det_size(c1, slen);
  option__size_t res0;
  if (len > (size_t)0U)
  {
    uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
    size_t len_ = cbor_det_serialize(c1, out1, len);
    res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
  }
  else
    res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  size_t res;
  if (res0.tag == FStar_Pervasives_Native_None)
    res = (size_t)0U;
  else if (res0.tag == FStar_Pervasives_Native_Some)
    res = res0.v;
  else
    res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_nil_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_nil(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_nil_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_nil(rl);
    if (test)
    {
      COSE_Format_evercddl_nil_pretty x = COSE_Format_parse_nil(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_nil_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_uu___is_Mkevercddl_null_pretty0(COSE_Format_evercddl_nil_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_nil_pretty
COSE_Format_evercddl_null_pretty_right(COSE_Format_evercddl_nil_pretty x1)
{
  return x1;
}

COSE_Format_evercddl_nil_pretty
COSE_Format_evercddl_null_pretty_left(COSE_Format_evercddl_nil_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_nil_pretty COSE_Format_parse_null(cbor_det_t c)
{
  COSE_Format_evercddl_nil_pretty res1 = COSE_Format_parse_nil(c);
  COSE_Format_evercddl_nil_pretty res2 = COSE_Format_evercddl_null_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_null(
  COSE_Format_evercddl_nil_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_nil_pretty c_ = COSE_Format_evercddl_null_pretty_left(c);
  size_t res = COSE_Format_serialize_nil(c_, out);
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_null_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_null(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_null_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_null(rl);
    if (test)
    {
      COSE_Format_evercddl_nil_pretty x = COSE_Format_parse_null(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_null_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t mt = cbor_det_major_type(c);
  bool test = mt == CBOR_MAJOR_TYPE_SIMPLE_VALUE;
  if (test)
  {
    uint8_t v1 = cbor_det_read_simple_value(c);
    return v1 == 23U;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_undefined_pretty0(
  COSE_Format_evercddl_undefined_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_undefined_pretty COSE_Format_evercddl_undefined_pretty_right(void)
{
  return COSE_Format_Mkevercddl_undefined_pretty0;
}

COSE_Format_evercddl_undefined_pretty COSE_Format_parse_undefined(cbor_det_t c)
{
  KRML_MAYBE_UNUSED_VAR(c);
  COSE_Format_evercddl_undefined_pretty res2 = COSE_Format_evercddl_undefined_pretty_right();
  return res2;
}

size_t
COSE_Format_serialize_undefined(
  COSE_Format_evercddl_undefined_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  KRML_MAYBE_UNUSED_VAR(c);
  cbor_det_t c1 = cbor_det_mk_simple_value(23U);
  size_t slen = len__uint8_t(out);
  size_t len = cbor_det_size(c1, slen);
  option__size_t res0;
  if (len > (size_t)0U)
  {
    uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
    size_t len_ = cbor_det_serialize(c1, out1, len);
    res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
  }
  else
    res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  size_t res;
  if (res0.tag == FStar_Pervasives_Native_None)
    res = (size_t)0U;
  else if (res0.tag == FStar_Pervasives_Native_Some)
    res = res0.v;
  else
    res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_undefined_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_undefined(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_undefined_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_undefined(rl);
    if (test)
    {
      COSE_Format_evercddl_undefined_pretty x = COSE_Format_parse_undefined(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_undefined_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_uu___is_Mkevercddl_any_pretty0(COSE_Format_evercddl_any projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_any COSE_Format_evercddl_any_pretty_right(cbor_det_t x1)
{
  return x1;
}

cbor_det_t COSE_Format_evercddl_any_pretty_left(COSE_Format_evercddl_any x3)
{
  return x3;
}

COSE_Format_evercddl_any COSE_Format_parse_any(cbor_det_t c)
{
  cbor_det_t res1 = c;
  COSE_Format_evercddl_any res2 = COSE_Format_evercddl_any_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_any(COSE_Format_evercddl_any c, Pulse_Lib_Slice_slice__uint8_t out)
{
  cbor_det_t c_ = COSE_Format_evercddl_any_pretty_left(c);
  size_t slen = len__uint8_t(out);
  size_t len = cbor_det_size(c_, slen);
  option__size_t ser;
  if (len > (size_t)0U)
  {
    uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
    size_t len_ = cbor_det_serialize(c_, out1, len);
    ser = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
  }
  else
    ser = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
  if (ser.tag == FStar_Pervasives_Native_None)
    return (size_t)0U;
  else if (ser.tag == FStar_Pervasives_Native_Some)
    return ser.v;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_any_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_any(rl);
    if (test)
    {
      COSE_Format_evercddl_any x = COSE_Format_parse_any(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_any_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_uu___is_Mkevercddl_values_pretty0(COSE_Format_evercddl_any_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_any_pretty
COSE_Format_evercddl_values_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

COSE_Format_evercddl_any
COSE_Format_evercddl_values_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_any_pretty COSE_Format_parse_values(cbor_det_t c)
{
  COSE_Format_evercddl_any res1 = COSE_Format_parse_any(c);
  COSE_Format_evercddl_any_pretty res2 = COSE_Format_evercddl_values_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_values(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_any c_ = COSE_Format_evercddl_values_pretty_left(c);
  size_t res = COSE_Format_serialize_any(c_, out);
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_values_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_values(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_values_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_values(rl);
    if (test)
    {
      COSE_Format_evercddl_any_pretty x = COSE_Format_parse_values(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_values_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_aux_env27_validate_1(cbor_det_array_iterator_t *pi)
{
  cbor_det_array_iterator_t i = *pi;
  bool is_done = cbor_det_array_iterator_is_empty(i);
  if (is_done)
    return false;
  else
  {
    cbor_det_t c = cbor_det_array_iterator_next(pi);
    bool test = COSE_Format_validate_label(c);
    return test;
  }
}

bool
COSE_Format_uu___is_Mkaux_env27_type_1_pretty0(COSE_Format_evercddl_label_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_label_pretty
COSE_Format_aux_env27_type_1_pretty_right(COSE_Format_evercddl_label_pretty x1)
{
  return x1;
}

COSE_Format_evercddl_label_pretty
COSE_Format_aux_env27_type_1_pretty_left(COSE_Format_evercddl_label_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_label_pretty COSE_Format_aux_env27_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t pc = c;
  cbor_det_t x = cbor_det_array_iterator_next(&pc);
  COSE_Format_evercddl_label_pretty res = COSE_Format_parse_label(x);
  return res;
}

bool
COSE_Format_aux_env27_serialize_1(
  COSE_Format_evercddl_label_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  uint64_t count = *out_count;
  if (count < 18446744073709551615ULL)
  {
    size_t size = *out_size;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = split__uint8_t(out, size);
    Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern.snd;
    size_t size1 = COSE_Format_serialize_label(c, out1);
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

bool (*COSE_Format_aux_env27_validate_2)(cbor_det_t x0) = COSE_Format_validate_label;

bool
COSE_Format_uu___is_Mkaux_env27_type_2_pretty0(COSE_Format_evercddl_label_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_label_pretty
COSE_Format_aux_env27_type_2_pretty_right(COSE_Format_evercddl_label_pretty x1)
{
  return x1;
}

COSE_Format_evercddl_label_pretty
COSE_Format_aux_env27_type_2_pretty_left(COSE_Format_evercddl_label_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_label_pretty COSE_Format_aux_env27_parse_2(cbor_det_t c)
{
  COSE_Format_evercddl_label_pretty res1 = COSE_Format_parse_label(c);
  COSE_Format_evercddl_label_pretty res2 = COSE_Format_aux_env27_type_2_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_aux_env27_serialize_2(
  COSE_Format_evercddl_label_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_label_pretty c_ = COSE_Format_aux_env27_type_2_pretty_left(c);
  size_t res = COSE_Format_serialize_label(c_, out);
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_aux_env27_type_2_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_aux_env27_parse_2(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_aux_env27_type_2_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_aux_env27_validate_2(rl);
    if (test)
    {
      COSE_Format_evercddl_label_pretty x = COSE_Format_aux_env27_parse_2(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_aux_env27_type_2_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_aux_env27_type_2_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_aux_env27_validate_3(cbor_det_t c)
{
  uint8_t mt0 = cbor_det_major_type(c);
  bool is_uint = mt0 == CBOR_MAJOR_TYPE_UINT64;
  bool test0;
  if (is_uint)
  {
    uint64_t i = cbor_det_read_uint64(c);
    test0 = i == 1ULL;
  }
  else
    test0 = false;
  bool test1;
  if (test0)
    test1 = true;
  else
  {
    uint8_t mt = cbor_det_major_type(c);
    bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
    if (is_uint)
    {
      uint64_t i = cbor_det_read_uint64(c);
      test1 = i == 2ULL;
    }
    else
      test1 = false;
  }
  bool test2;
  if (test1)
    test2 = true;
  else
  {
    uint8_t mt = cbor_det_major_type(c);
    bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
    if (is_uint)
    {
      uint64_t i = cbor_det_read_uint64(c);
      test2 = i == 3ULL;
    }
    else
      test2 = false;
  }
  bool test3;
  if (test2)
    test3 = true;
  else
  {
    uint8_t mt = cbor_det_major_type(c);
    bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
    if (is_uint)
    {
      uint64_t i = cbor_det_read_uint64(c);
      test3 = i == 4ULL;
    }
    else
      test3 = false;
  }
  bool test;
  if (test3)
    test = true;
  else
  {
    uint8_t mt = cbor_det_major_type(c);
    bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
    if (is_uint)
    {
      uint64_t i = cbor_det_read_uint64(c);
      test = i == 5ULL;
    }
    else
      test = false;
  }
  if (test)
    return true;
  else
  {
    uint8_t mt = cbor_det_major_type(c);
    bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
    if (is_uint)
    {
      uint64_t i = cbor_det_read_uint64(c);
      return i == 6ULL;
    }
    else
      return false;
  }
}

bool (*COSE_Format_aux_env27_validate_4)(cbor_det_t x0) = COSE_Format_validate_values;

bool
COSE_Format_uu___is_Mkaux_env27_type_4_pretty0(COSE_Format_evercddl_values_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_values_pretty
COSE_Format_aux_env27_type_4_pretty_right(COSE_Format_evercddl_any_pretty x1)
{
  return x1;
}

COSE_Format_evercddl_any_pretty
COSE_Format_aux_env27_type_4_pretty_left(COSE_Format_evercddl_values_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_values_pretty COSE_Format_aux_env27_parse_4(cbor_det_t c)
{
  COSE_Format_evercddl_any_pretty res1 = COSE_Format_parse_values(c);
  COSE_Format_evercddl_values_pretty res2 = COSE_Format_aux_env27_type_4_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_aux_env27_serialize_4(
  COSE_Format_evercddl_values_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_any_pretty c_ = COSE_Format_aux_env27_type_4_pretty_left(c);
  size_t res = COSE_Format_serialize_values(c_, out);
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_aux_env27_type_4_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_aux_env27_parse_4(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_aux_env27_type_4_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_aux_env27_validate_4(rl);
    if (test)
    {
      COSE_Format_evercddl_values_pretty x = COSE_Format_aux_env27_parse_4(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_aux_env27_type_4_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_aux_env27_type_4_pretty___Pulse_Lib_Slice_slice_uint8_t_){
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

bool COSE_Format_validate_header_map(cbor_det_t c)
{
  uint8_t ty = cbor_det_major_type(c);
  if (ty == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t rem0 = cbor_det_get_map_length(c);
    uint64_t remaining = rem0;
    uint64_t i00 = remaining;
    cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest0 = c10;
    bool bres0 = cbor_det_map_get(c, c10, &dest0);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t mg0;
    if (bres0)
    {
      cbor_det_t res = dest0;
      mg0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      mg0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    impl_map_group_result res0;
    if (mg0.tag == FStar_Pervasives_Native_None)
      res0 = MGFail;
    else if (mg0.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t cv = mg0.v;
      bool test = COSE_Format_validate_int(cv);
      bool check_value;
      if (test)
        check_value = true;
      else
        check_value = COSE_Format_validate_tstr(cv);
      if (check_value)
      {
        uint64_t i1 = remaining;
        uint64_t i2 = i1 - 1ULL;
        remaining = i2;
        res0 = MGOK;
      }
      else
        res0 = MGCutFail;
    }
    else
      res0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    impl_map_group_result res2 = res0;
    impl_map_group_result res10 = res2;
    impl_map_group_result res14;
    switch (res10)
    {
      case MGOK:
        {
          res14 = MGOK;
          break;
        }
      case MGFail:
        {
          remaining = i00;
          res14 = MGOK;
          break;
        }
      case MGCutFail:
        {
          res14 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result res15;
    switch (res14)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
          cbor_det_t dest = c1;
          bool bres = cbor_det_map_get(c, c1, &dest);
          option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
          if (bres)
          {
            cbor_det_t res = dest;
            mg =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = res
                }
              );
          }
          else
            mg =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result res0;
          if (mg.tag == FStar_Pervasives_Native_None)
            res0 = MGFail;
          else if (mg.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = mg.v;
            uint8_t ty1 = cbor_det_major_type(cv);
            bool check_value;
            if (ty1 == CBOR_MAJOR_TYPE_ARRAY)
            {
              cbor_det_array_iterator_t i = cbor_det_array_iterator_start(cv);
              cbor_det_array_iterator_t pi = i;
              cbor_det_array_iterator_t i10 = pi;
              bool is_done = cbor_det_array_iterator_is_empty(i10);
              bool test1;
              if (is_done)
                test1 = false;
              else
              {
                cbor_det_t c2 = cbor_det_array_iterator_next(&pi);
                bool test = COSE_Format_validate_label(c2);
                test1 = test;
              }
              bool b_success;
              if (test1)
              {
                bool pcont = true;
                while (pcont)
                {
                  cbor_det_array_iterator_t i1 = pi;
                  cbor_det_array_iterator_t i2 = pi;
                  bool is_done = cbor_det_array_iterator_is_empty(i2);
                  bool cont;
                  if (is_done)
                    cont = false;
                  else
                  {
                    cbor_det_t c2 = cbor_det_array_iterator_next(&pi);
                    bool test = COSE_Format_validate_label(c2);
                    cont = test;
                  }
                  if (!cont)
                  {
                    pi = i1;
                    pcont = false;
                  }
                }
                bool test2 = true;
                b_success = test2;
              }
              else
                b_success = false;
              bool _bind_c;
              if (b_success)
              {
                cbor_det_array_iterator_t i_ = pi;
                bool b_end = cbor_det_array_iterator_is_empty(i_);
                _bind_c = b_end;
              }
              else
                _bind_c = false;
              check_value = _bind_c;
            }
            else
              check_value = false;
            if (check_value)
            {
              uint64_t i1 = remaining;
              uint64_t i2 = i1 - 1ULL;
              remaining = i2;
              res0 = MGOK;
            }
            else
              res0 = MGCutFail;
          }
          else
            res0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          impl_map_group_result res1 = res0;
          impl_map_group_result res11 = res1;
          impl_map_group_result res;
          switch (res11)
          {
            case MGOK:
              {
                res = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                res = MGOK;
                break;
              }
            case MGCutFail:
              {
                res = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          res15 = res;
          break;
        }
      case MGFail:
        {
          res15 = MGFail;
          break;
        }
      case MGCutFail:
        {
          res15 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result res16;
    switch (res15)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
          cbor_det_t dest = c1;
          bool bres = cbor_det_map_get(c, c1, &dest);
          option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
          if (bres)
          {
            cbor_det_t res = dest;
            mg =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = res
                }
              );
          }
          else
            mg =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result res0;
          if (mg.tag == FStar_Pervasives_Native_None)
            res0 = MGFail;
          else if (mg.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = mg.v;
            bool test = COSE_Format_validate_tstr(cv);
            bool check_value;
            if (test)
              check_value = true;
            else
              check_value = COSE_Format_validate_int(cv);
            if (check_value)
            {
              uint64_t i1 = remaining;
              uint64_t i2 = i1 - 1ULL;
              remaining = i2;
              res0 = MGOK;
            }
            else
              res0 = MGCutFail;
          }
          else
            res0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          impl_map_group_result res1 = res0;
          impl_map_group_result res11 = res1;
          impl_map_group_result res;
          switch (res11)
          {
            case MGOK:
              {
                res = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                res = MGOK;
                break;
              }
            case MGCutFail:
              {
                res = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          res16 = res;
          break;
        }
      case MGFail:
        {
          res16 = MGFail;
          break;
        }
      case MGCutFail:
        {
          res16 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result res17;
    switch (res16)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
          cbor_det_t dest = c1;
          bool bres = cbor_det_map_get(c, c1, &dest);
          option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
          if (bres)
          {
            cbor_det_t res = dest;
            mg =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = res
                }
              );
          }
          else
            mg =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result res0;
          if (mg.tag == FStar_Pervasives_Native_None)
            res0 = MGFail;
          else if (mg.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = mg.v;
            bool check_value = COSE_Format_validate_bstr(cv);
            if (check_value)
            {
              uint64_t i1 = remaining;
              uint64_t i2 = i1 - 1ULL;
              remaining = i2;
              res0 = MGOK;
            }
            else
              res0 = MGCutFail;
          }
          else
            res0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          impl_map_group_result res1 = res0;
          impl_map_group_result res11 = res1;
          impl_map_group_result res;
          switch (res11)
          {
            case MGOK:
              {
                res = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                res = MGOK;
                break;
              }
            case MGCutFail:
              {
                res = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          res17 = res;
          break;
        }
      case MGFail:
        {
          res17 = MGFail;
          break;
        }
      case MGCutFail:
        {
          res17 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result res1;
    switch (res17)
    {
      case MGOK:
        {
          uint64_t i0 = remaining;
          cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
          cbor_det_t dest0 = c10;
          bool bres0 = cbor_det_map_get(c, c10, &dest0);
          option__CBOR_Pulse_API_Det_Type_cbor_det_t mg0;
          if (bres0)
          {
            cbor_det_t res = dest0;
            mg0 =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = res
                }
              );
          }
          else
            mg0 =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result res0;
          if (mg0.tag == FStar_Pervasives_Native_None)
            res0 = MGFail;
          else if (mg0.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = mg0.v;
            bool check_value = COSE_Format_validate_bstr(cv);
            if (check_value)
            {
              uint64_t i1 = remaining;
              uint64_t i2 = i1 - 1ULL;
              remaining = i2;
              res0 = MGOK;
            }
            else
              res0 = MGFail;
          }
          else
            res0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          impl_map_group_result res2 = res0;
          impl_map_group_result res110 = res2;
          impl_map_group_result res11;
          switch (res110)
          {
            case MGOK:
              {
                uint64_t i01 = remaining;
                cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                cbor_det_t dest = c1;
                bool bres = cbor_det_map_get(c, c1, &dest);
                option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
                if (bres)
                {
                  cbor_det_t res = dest;
                  mg =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = res
                      }
                    );
                }
                else
                  mg =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                impl_map_group_result res0;
                if (mg.tag == FStar_Pervasives_Native_None)
                  res0 = MGFail;
                else if (mg.tag == FStar_Pervasives_Native_Some)
                {
                  cbor_det_t cv = mg.v;
                  bool check_value = COSE_Format_validate_everparsenomatch(cv);
                  if (check_value)
                  {
                    uint64_t i1 = remaining;
                    uint64_t i2 = i1 - 1ULL;
                    remaining = i2;
                    res0 = MGOK;
                  }
                  else
                    res0 = MGCutFail;
                }
                else
                  res0 =
                    KRML_EABORT(impl_map_group_result,
                      "unreachable (pattern matches are exhaustive in F*)");
                impl_map_group_result res1 = res0;
                impl_map_group_result res12 = res1;
                impl_map_group_result res;
                switch (res12)
                {
                  case MGOK:
                    {
                      res = MGOK;
                      break;
                    }
                  case MGFail:
                    {
                      remaining = i01;
                      res = MGOK;
                      break;
                    }
                  case MGCutFail:
                    {
                      res = MGCutFail;
                      break;
                    }
                  default:
                    {
                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                      KRML_HOST_EXIT(253U);
                    }
                }
                res11 = res;
                break;
              }
            case MGFail:
              {
                res11 = MGFail;
                break;
              }
            case MGCutFail:
              {
                res11 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          impl_map_group_result res3;
          switch (res11)
          {
            case MGOK:
              {
                res3 = MGOK;
                break;
              }
            case MGFail:
              {
                remaining = i0;
                uint64_t i01 = remaining;
                cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                cbor_det_t dest0 = c10;
                bool bres0 = cbor_det_map_get(c, c10, &dest0);
                option__CBOR_Pulse_API_Det_Type_cbor_det_t mg0;
                if (bres0)
                {
                  cbor_det_t res = dest0;
                  mg0 =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = res
                      }
                    );
                }
                else
                  mg0 =
                    (
                      (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                impl_map_group_result res0;
                if (mg0.tag == FStar_Pervasives_Native_None)
                  res0 = MGFail;
                else if (mg0.tag == FStar_Pervasives_Native_Some)
                {
                  cbor_det_t cv = mg0.v;
                  bool check_value = COSE_Format_validate_bstr(cv);
                  if (check_value)
                  {
                    uint64_t i1 = remaining;
                    uint64_t i2 = i1 - 1ULL;
                    remaining = i2;
                    res0 = MGOK;
                  }
                  else
                    res0 = MGFail;
                }
                else
                  res0 =
                    KRML_EABORT(impl_map_group_result,
                      "unreachable (pattern matches are exhaustive in F*)");
                impl_map_group_result res1 = res0;
                impl_map_group_result res120 = res1;
                impl_map_group_result res12;
                switch (res120)
                {
                  case MGOK:
                    {
                      uint64_t i02 = remaining;
                      cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
                      cbor_det_t dest = c1;
                      bool bres = cbor_det_map_get(c, c1, &dest);
                      option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
                      if (bres)
                      {
                        cbor_det_t res = dest;
                        mg =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_Some,
                              .v = res
                            }
                          );
                      }
                      else
                        mg =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_None
                            }
                          );
                      impl_map_group_result res0;
                      if (mg.tag == FStar_Pervasives_Native_None)
                        res0 = MGFail;
                      else if (mg.tag == FStar_Pervasives_Native_Some)
                      {
                        cbor_det_t cv = mg.v;
                        bool check_value = COSE_Format_validate_everparsenomatch(cv);
                        if (check_value)
                        {
                          uint64_t i1 = remaining;
                          uint64_t i2 = i1 - 1ULL;
                          remaining = i2;
                          res0 = MGOK;
                        }
                        else
                          res0 = MGCutFail;
                      }
                      else
                        res0 =
                          KRML_EABORT(impl_map_group_result,
                            "unreachable (pattern matches are exhaustive in F*)");
                      impl_map_group_result res1 = res0;
                      impl_map_group_result res13 = res1;
                      impl_map_group_result res;
                      switch (res13)
                      {
                        case MGOK:
                          {
                            res = MGOK;
                            break;
                          }
                        case MGFail:
                          {
                            remaining = i02;
                            res = MGOK;
                            break;
                          }
                        case MGCutFail:
                          {
                            res = MGCutFail;
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
                      res12 = res;
                      break;
                    }
                  case MGFail:
                    {
                      res12 = MGFail;
                      break;
                    }
                  case MGCutFail:
                    {
                      res12 = MGCutFail;
                      break;
                    }
                  default:
                    {
                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                      KRML_HOST_EXIT(253U);
                    }
                }
                impl_map_group_result res2;
                switch (res12)
                {
                  case MGOK:
                    {
                      res2 = MGOK;
                      break;
                    }
                  case MGFail:
                    {
                      remaining = i01;
                      uint64_t i020 = remaining;
                      cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
                      cbor_det_t dest0 = c10;
                      bool bres0 = cbor_det_map_get(c, c10, &dest0);
                      option__CBOR_Pulse_API_Det_Type_cbor_det_t mg0;
                      if (bres0)
                      {
                        cbor_det_t res = dest0;
                        mg0 =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_Some,
                              .v = res
                            }
                          );
                      }
                      else
                        mg0 =
                          (
                            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                              .tag = FStar_Pervasives_Native_None
                            }
                          );
                      impl_map_group_result res0;
                      if (mg0.tag == FStar_Pervasives_Native_None)
                        res0 = MGFail;
                      else if (mg0.tag == FStar_Pervasives_Native_Some)
                      {
                        cbor_det_t cv = mg0.v;
                        bool check_value = COSE_Format_validate_everparsenomatch(cv);
                        if (check_value)
                        {
                          uint64_t i1 = remaining;
                          uint64_t i2 = i1 - 1ULL;
                          remaining = i2;
                          res0 = MGOK;
                        }
                        else
                          res0 = MGCutFail;
                      }
                      else
                        res0 =
                          KRML_EABORT(impl_map_group_result,
                            "unreachable (pattern matches are exhaustive in F*)");
                      impl_map_group_result res1 = res0;
                      impl_map_group_result res130 = res1;
                      impl_map_group_result res13;
                      switch (res130)
                      {
                        case MGOK:
                          {
                            res13 = MGOK;
                            break;
                          }
                        case MGFail:
                          {
                            remaining = i020;
                            res13 = MGOK;
                            break;
                          }
                        case MGCutFail:
                          {
                            res13 = MGCutFail;
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
                      impl_map_group_result res3;
                      switch (res13)
                      {
                        case MGOK:
                          {
                            uint64_t i02 = remaining;
                            cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
                            cbor_det_t dest = c1;
                            bool bres = cbor_det_map_get(c, c1, &dest);
                            option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
                            if (bres)
                            {
                              cbor_det_t res = dest;
                              mg =
                                (
                                  (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                                    .tag = FStar_Pervasives_Native_Some,
                                    .v = res
                                  }
                                );
                            }
                            else
                              mg =
                                (
                                  (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                                    .tag = FStar_Pervasives_Native_None
                                  }
                                );
                            impl_map_group_result res0;
                            if (mg.tag == FStar_Pervasives_Native_None)
                              res0 = MGFail;
                            else if (mg.tag == FStar_Pervasives_Native_Some)
                            {
                              cbor_det_t cv = mg.v;
                              bool check_value = COSE_Format_validate_everparsenomatch(cv);
                              if (check_value)
                              {
                                uint64_t i1 = remaining;
                                uint64_t i2 = i1 - 1ULL;
                                remaining = i2;
                                res0 = MGOK;
                              }
                              else
                                res0 = MGCutFail;
                            }
                            else
                              res0 =
                                KRML_EABORT(impl_map_group_result,
                                  "unreachable (pattern matches are exhaustive in F*)");
                            impl_map_group_result res1 = res0;
                            impl_map_group_result res14 = res1;
                            impl_map_group_result res;
                            switch (res14)
                            {
                              case MGOK:
                                {
                                  res = MGOK;
                                  break;
                                }
                              case MGFail:
                                {
                                  remaining = i02;
                                  res = MGOK;
                                  break;
                                }
                              case MGCutFail:
                                {
                                  res = MGCutFail;
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
                            res3 = res;
                            break;
                          }
                        case MGFail:
                          {
                            res3 = MGFail;
                            break;
                          }
                        case MGCutFail:
                          {
                            res3 = MGCutFail;
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
                      res2 = res3;
                      break;
                    }
                  case MGCutFail:
                    {
                      res2 = MGCutFail;
                      break;
                    }
                  default:
                    {
                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                      KRML_HOST_EXIT(253U);
                    }
                }
                res3 = res2;
                break;
              }
            case MGCutFail:
              {
                res3 = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          res1 = res3;
          break;
        }
      case MGFail:
        {
          res1 = MGFail;
          break;
        }
      case MGCutFail:
        {
          res1 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    impl_map_group_result res;
    switch (res1)
    {
      case MGOK:
        {
          cbor_det_map_iterator_t j0 = cbor_det_map_iterator_start(c);
          cbor_det_map_iterator_t pj = j0;
          cbor_det_map_iterator_t j = pj;
          bool is_empty = cbor_det_map_iterator_is_empty(j);
          bool cond = !is_empty;
          while (cond)
          {
            cbor_det_map_entry_t chd = cbor_det_map_iterator_next(&pj);
            cbor_det_t k = cbor_det_map_entry_key(chd);
            bool test1 = COSE_Format_validate_label(k);
            bool testk;
            if (test1)
            {
              uint8_t mt0 = cbor_det_major_type(k);
              bool is_uint = mt0 == CBOR_MAJOR_TYPE_UINT64;
              bool test0;
              if (is_uint)
              {
                uint64_t i = cbor_det_read_uint64(k);
                test0 = i == 1ULL;
              }
              else
                test0 = false;
              bool test1;
              if (test0)
                test1 = true;
              else
              {
                uint8_t mt = cbor_det_major_type(k);
                bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
                if (is_uint)
                {
                  uint64_t i = cbor_det_read_uint64(k);
                  test1 = i == 2ULL;
                }
                else
                  test1 = false;
              }
              bool test2;
              if (test1)
                test2 = true;
              else
              {
                uint8_t mt = cbor_det_major_type(k);
                bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
                if (is_uint)
                {
                  uint64_t i = cbor_det_read_uint64(k);
                  test2 = i == 3ULL;
                }
                else
                  test2 = false;
              }
              bool test3;
              if (test2)
                test3 = true;
              else
              {
                uint8_t mt = cbor_det_major_type(k);
                bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
                if (is_uint)
                {
                  uint64_t i = cbor_det_read_uint64(k);
                  test3 = i == 4ULL;
                }
                else
                  test3 = false;
              }
              bool test4;
              if (test3)
                test4 = true;
              else
              {
                uint8_t mt = cbor_det_major_type(k);
                bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
                if (is_uint)
                {
                  uint64_t i = cbor_det_read_uint64(k);
                  test4 = i == 5ULL;
                }
                else
                  test4 = false;
              }
              bool test;
              if (test4)
                test = true;
              else
              {
                uint8_t mt = cbor_det_major_type(k);
                bool is_uint = mt == CBOR_MAJOR_TYPE_UINT64;
                if (is_uint)
                {
                  uint64_t i = cbor_det_read_uint64(k);
                  test = i == 6ULL;
                }
                else
                  test = false;
              }
              testk = !test;
            }
            else
              testk = false;
            bool test;
            if (testk)
            {
              cbor_det_t v1 = cbor_det_map_entry_value(chd);
              bool testv = COSE_Format_validate_values(v1);
              test = testv;
            }
            else
              test = false;
            bool test0 = !test;
            if (!test0)
            {
              uint64_t i = remaining;
              uint64_t i_ = i - 1ULL;
              remaining = i_;
            }
            cbor_det_map_iterator_t j = pj;
            bool is_empty = cbor_det_map_iterator_is_empty(j);
            cond = !is_empty;
          }
          impl_map_group_result res0 = MGOK;
          res = res0;
          break;
        }
      case MGFail:
        {
          res = MGFail;
          break;
        }
      case MGCutFail:
        {
          res = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (res)
    {
      case MGOK:
        {
          uint64_t rem = remaining;
          return rem == 0ULL;
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

bool
COSE_Format_uu___is_Mkevercddl_header_map_pretty0(
  COSE_Format_evercddl_header_map_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_header_map_pretty
COSE_Format_evercddl_header_map_pretty_right(COSE_Format_evercddl_header_map x6)
{
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
  x12 = x6.snd;
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  x11 = x6.fst.snd;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x10 = x6.fst.fst.snd;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  x9 = x6.fst.fst.fst.snd;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
  x8 = x6.fst.fst.fst.fst.snd;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
  x7 = x6.fst.fst.fst.fst.fst;
  return
    (
      (COSE_Format_evercddl_header_map_pretty){
        .x0 = x7,
        .x1 = x8,
        .x2 = x9,
        .x3 = x10,
        .x4 = x11,
        .x5 = x12
      }
    );
}

COSE_Format_evercddl_header_map
COSE_Format_evercddl_header_map_pretty_left(COSE_Format_evercddl_header_map_pretty x13)
{
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
  x21 = x13.x0;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
  x22 = x13.x1;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  x23 = x13.x2;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty x24 = x13.x3;
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  x25 = x13.x4;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
  x26 = x13.x5;
  return
    (
      (COSE_Format_evercddl_header_map){
        .fst = {
          .fst = { .fst = { .fst = { .fst = x21, .snd = x22 }, .snd = x23 }, .snd = x24 },
          .snd = x25
        },
        .snd = x26
      }
    );
}

COSE_Format_evercddl_header_map_pretty COSE_Format_parse_header_map(cbor_det_t c)
{
  uint64_t dummy0 = 0ULL;
  KRML_HOST_IGNORE(&dummy0);
  cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
  cbor_det_t dest0 = c10;
  bool bres0 = cbor_det_map_get(c, c10, &dest0);
  option__CBOR_Pulse_API_Det_Type_cbor_det_t mg0;
  if (bres0)
  {
    cbor_det_t res = dest0;
    mg0 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = res
        }
      );
  }
  else
    mg0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result res0;
  if (mg0.tag == FStar_Pervasives_Native_None)
    res0 = MGFail;
  else if (mg0.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = mg0.v;
    bool test = COSE_Format_validate_int(cv);
    bool check_value;
    if (test)
      check_value = true;
    else
      check_value = COSE_Format_validate_tstr(cv);
    if (check_value)
      res0 = MGOK;
    else
      res0 = MGCutFail;
  }
  else
    res0 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  impl_map_group_result res1 = res0;
  impl_map_group_result test10 = res1;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
  _bind_c0;
  if (uu___is_MGOK(test10))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
    cbor_det_t dest = c1;
    bool bres = cbor_det_map_get(c, c1, &dest);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
    if (bres)
    {
      cbor_det_t res = dest;
      ow =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
    COSE_Format_evercddl_label res0;
    if (_letpattern.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = _letpattern.v;
      bool test = COSE_Format_validate_int(w);
      COSE_Format_evercddl_label res1;
      if (test)
      {
        COSE_Format_evercddl_int_pretty res = COSE_Format_parse_int(w);
        res1 = ((COSE_Format_evercddl_label){ .tag = COSE_Format_Inl, { .case_Inl = res } });
      }
      else
      {
        COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(w);
        res1 = ((COSE_Format_evercddl_label){ .tag = COSE_Format_Inr, { .case_Inr = res } });
      }
      res0 = res1;
    }
    else
      res0 =
        KRML_EABORT(COSE_Format_evercddl_label,
          "unreachable (pattern matches are exhaustive in F*)");
    COSE_Format_evercddl_label w1 = res0;
    _bind_c0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = w1
        }
      );
  }
  else
    _bind_c0 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
  w1 = _bind_c0;
  uint64_t dummy3 = 0ULL;
  KRML_HOST_IGNORE(&dummy3);
  cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
  cbor_det_t dest1 = c11;
  bool bres1 = cbor_det_map_get(c, c11, &dest1);
  option__CBOR_Pulse_API_Det_Type_cbor_det_t mg1;
  if (bres1)
  {
    cbor_det_t res = dest1;
    mg1 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = res
        }
      );
  }
  else
    mg1 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result res2;
  if (mg1.tag == FStar_Pervasives_Native_None)
    res2 = MGFail;
  else if (mg1.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = mg1.v;
    uint8_t ty = cbor_det_major_type(cv);
    bool check_value;
    if (ty == CBOR_MAJOR_TYPE_ARRAY)
    {
      cbor_det_array_iterator_t i = cbor_det_array_iterator_start(cv);
      cbor_det_array_iterator_t pi = i;
      cbor_det_array_iterator_t i10 = pi;
      bool is_done = cbor_det_array_iterator_is_empty(i10);
      bool test1;
      if (is_done)
        test1 = false;
      else
      {
        cbor_det_t c2 = cbor_det_array_iterator_next(&pi);
        bool test = COSE_Format_validate_label(c2);
        test1 = test;
      }
      bool b_success;
      if (test1)
      {
        bool pcont = true;
        while (pcont)
        {
          cbor_det_array_iterator_t i1 = pi;
          cbor_det_array_iterator_t i2 = pi;
          bool is_done = cbor_det_array_iterator_is_empty(i2);
          bool cont;
          if (is_done)
            cont = false;
          else
          {
            cbor_det_t c2 = cbor_det_array_iterator_next(&pi);
            bool test = COSE_Format_validate_label(c2);
            cont = test;
          }
          if (!cont)
          {
            pi = i1;
            pcont = false;
          }
        }
        bool test2 = true;
        b_success = test2;
      }
      else
        b_success = false;
      bool _bind_c;
      if (b_success)
      {
        cbor_det_array_iterator_t i_ = pi;
        bool b_end = cbor_det_array_iterator_is_empty(i_);
        _bind_c = b_end;
      }
      else
        _bind_c = false;
      check_value = _bind_c;
    }
    else
      check_value = false;
    if (check_value)
      res2 = MGOK;
    else
      res2 = MGCutFail;
  }
  else
    res2 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  impl_map_group_result res3 = res2;
  impl_map_group_result test12 = res3;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
  _bind_c1;
  if (uu___is_MGOK(test12))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
    cbor_det_t dest = c1;
    bool bres = cbor_det_map_get(c, c1, &dest);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
    if (bres)
    {
      cbor_det_t res = dest;
      ow =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
    FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
    res;
    if (_letpattern.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = _letpattern.v;
      cbor_det_array_iterator_t ar = cbor_det_array_iterator_start(w);
      CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
      i =
        {
          .cddl_array_iterator_contents = ar,
          .cddl_array_iterator_impl_validate = COSE_Format_aux_env27_validate_1,
          .cddl_array_iterator_impl_parse = COSE_Format_aux_env27_parse_1
        };
      FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
      res0 = { .tag = COSE_Format_Inr, { .case_Inr = i } };
      res = res0;
    }
    else
      res =
        KRML_EABORT(FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty,
          "unreachable (pattern matches are exhaustive in F*)");
    FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
    w11 = res;
    _bind_c1 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = w11
        }
      );
  }
  else
    _bind_c1 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
  w2 = _bind_c1;
  K___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
  w10 = { .fst = w1, .snd = w2 };
  uint64_t dummy4 = 0ULL;
  KRML_HOST_IGNORE(&dummy4);
  cbor_det_t c12 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
  cbor_det_t dest2 = c12;
  bool bres2 = cbor_det_map_get(c, c12, &dest2);
  option__CBOR_Pulse_API_Det_Type_cbor_det_t mg2;
  if (bres2)
  {
    cbor_det_t res = dest2;
    mg2 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = res
        }
      );
  }
  else
    mg2 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result res4;
  if (mg2.tag == FStar_Pervasives_Native_None)
    res4 = MGFail;
  else if (mg2.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = mg2.v;
    bool test = COSE_Format_validate_tstr(cv);
    bool check_value;
    if (test)
      check_value = true;
    else
      check_value = COSE_Format_validate_int(cv);
    if (check_value)
      res4 = MGOK;
    else
      res4 = MGCutFail;
  }
  else
    res4 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  impl_map_group_result res5 = res4;
  impl_map_group_result test13 = res5;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  _bind_c2;
  if (uu___is_MGOK(test13))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
    cbor_det_t dest = c1;
    bool bres = cbor_det_map_get(c, c1, &dest);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
    if (bres)
    {
      cbor_det_t res = dest;
      ow =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
    FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty res0;
    if (_letpattern.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = _letpattern.v;
      bool test = COSE_Format_validate_tstr(w);
      FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
      res1;
      if (test)
      {
        COSE_Format_evercddl_bstr res = COSE_Format_parse_tstr(w);
        res1 =
          (
            (FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty){
              .tag = COSE_Format_Inl,
              { .case_Inl = res }
            }
          );
      }
      else
      {
        COSE_Format_evercddl_int_pretty res = COSE_Format_parse_int(w);
        res1 =
          (
            (FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty){
              .tag = COSE_Format_Inr,
              { .case_Inr = res }
            }
          );
      }
      res0 = res1;
    }
    else
      res0 =
        KRML_EABORT(FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty,
          "unreachable (pattern matches are exhaustive in F*)");
    FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
    w11 = res0;
    _bind_c2 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = w11
        }
      );
  }
  else
    _bind_c2 =
      (
        (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  w20 = _bind_c2;
  K____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  w11 = { .fst = w10, .snd = w20 };
  uint64_t dummy5 = 0ULL;
  KRML_HOST_IGNORE(&dummy5);
  cbor_det_t c13 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
  cbor_det_t dest3 = c13;
  bool bres3 = cbor_det_map_get(c, c13, &dest3);
  option__CBOR_Pulse_API_Det_Type_cbor_det_t mg3;
  if (bres3)
  {
    cbor_det_t res = dest3;
    mg3 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = res
        }
      );
  }
  else
    mg3 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result res6;
  if (mg3.tag == FStar_Pervasives_Native_None)
    res6 = MGFail;
  else if (mg3.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = mg3.v;
    bool check_value = COSE_Format_validate_bstr(cv);
    if (check_value)
      res6 = MGOK;
    else
      res6 = MGCutFail;
  }
  else
    res6 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  impl_map_group_result res7 = res6;
  impl_map_group_result test14 = res7;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty _bind_c3;
  if (uu___is_MGOK(test14))
  {
    cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
    cbor_det_t dest = c1;
    bool bres = cbor_det_map_get(c, c1, &dest);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
    if (bres)
    {
      cbor_det_t res = dest;
      ow =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
    COSE_Format_evercddl_bstr res;
    if (_letpattern.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = _letpattern.v;
      COSE_Format_evercddl_bstr res0 = COSE_Format_parse_bstr(w);
      res = res0;
    }
    else
      res =
        KRML_EABORT(COSE_Format_evercddl_bstr,
          "unreachable (pattern matches are exhaustive in F*)");
    COSE_Format_evercddl_bstr w11 = res;
    _bind_c3 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_Some,
          .v = w11
        }
      );
  }
  else
    _bind_c3 =
      (
        (FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty){
          .tag = FStar_Pervasives_Native_None
        }
      );
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty w21 = _bind_c3;
  K_____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  w12 = { .fst = w11, .snd = w21 };
  uint64_t dummy = 0ULL;
  cbor_det_t c14 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
  cbor_det_t dest4 = c14;
  bool bres4 = cbor_det_map_get(c, c14, &dest4);
  option__CBOR_Pulse_API_Det_Type_cbor_det_t mg4;
  if (bres4)
  {
    cbor_det_t res = dest4;
    mg4 =
      (
        (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = res
        }
      );
  }
  else
    mg4 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
  impl_map_group_result res8;
  if (mg4.tag == FStar_Pervasives_Native_None)
    res8 = MGFail;
  else if (mg4.tag == FStar_Pervasives_Native_Some)
  {
    cbor_det_t cv = mg4.v;
    bool check_value = COSE_Format_validate_bstr(cv);
    if (check_value)
      res8 = MGOK;
    else
      res8 = MGFail;
  }
  else
    res8 = KRML_EABORT(impl_map_group_result, "unreachable (pattern matches are exhaustive in F*)");
  impl_map_group_result res9 = res8;
  impl_map_group_result res10 = res9;
  impl_map_group_result test1;
  switch (res10)
  {
    case MGOK:
      {
        uint64_t i0 = dummy;
        cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
        cbor_det_t dest = c1;
        bool bres = cbor_det_map_get(c, c1, &dest);
        option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
        if (bres)
        {
          cbor_det_t res = dest;
          mg =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = res
              }
            );
        }
        else
          mg = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        impl_map_group_result res0;
        if (mg.tag == FStar_Pervasives_Native_None)
          res0 = MGFail;
        else if (mg.tag == FStar_Pervasives_Native_Some)
        {
          cbor_det_t cv = mg.v;
          bool check_value = COSE_Format_validate_everparsenomatch(cv);
          if (check_value)
            res0 = MGOK;
          else
            res0 = MGCutFail;
        }
        else
          res0 =
            KRML_EABORT(impl_map_group_result,
              "unreachable (pattern matches are exhaustive in F*)");
        impl_map_group_result res1 = res0;
        impl_map_group_result res11 = res1;
        impl_map_group_result res;
        switch (res11)
        {
          case MGOK:
            {
              res = MGOK;
              break;
            }
          case MGFail:
            {
              dummy = i0;
              res = MGOK;
              break;
            }
          case MGCutFail:
            {
              res = MGCutFail;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        test1 = res;
        break;
      }
    case MGFail:
      {
        test1 = MGFail;
        break;
      }
    case MGCutFail:
      {
        test1 = MGCutFail;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  _bind_c4;
  if (uu___is_MGOK(test1))
  {
    cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
    cbor_det_t dest0 = c10;
    bool bres0 = cbor_det_map_get(c, c10, &dest0);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t ow0;
    if (bres0)
    {
      cbor_det_t res = dest0;
      ow0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      ow0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow0;
    COSE_Format_evercddl_bstr res0;
    if (_letpattern.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t w = _letpattern.v;
      COSE_Format_evercddl_bstr res = COSE_Format_parse_bstr(w);
      res0 = res;
    }
    else
      res0 =
        KRML_EABORT(COSE_Format_evercddl_bstr,
          "unreachable (pattern matches are exhaustive in F*)");
    COSE_Format_evercddl_bstr w11 = res0;
    uint64_t dummy1 = 0ULL;
    KRML_HOST_IGNORE(&dummy1);
    cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
    cbor_det_t dest1 = c11;
    bool bres1 = cbor_det_map_get(c, c11, &dest1);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
    if (bres1)
    {
      cbor_det_t res = dest1;
      mg =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      mg = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    impl_map_group_result res1;
    if (mg.tag == FStar_Pervasives_Native_None)
      res1 = MGFail;
    else if (mg.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t cv = mg.v;
      bool check_value = COSE_Format_validate_everparsenomatch(cv);
      if (check_value)
        res1 = MGOK;
      else
        res1 = MGCutFail;
    }
    else
      res1 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    impl_map_group_result res2 = res1;
    impl_map_group_result test11 = res2;
    FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty _bind_c;
    if (uu___is_MGOK(test11))
    {
      cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
      cbor_det_t dest = c1;
      bool bres = cbor_det_map_get(c, c1, &dest);
      option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
      if (bres)
      {
        cbor_det_t res = dest;
        ow =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = res
            }
          );
      }
      else
        ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
      COSE_Format_evercddl_everparsenomatch_pretty res;
      if (_letpattern.tag == FStar_Pervasives_Native_Some)
      {
        cbor_det_t w = _letpattern.v;
        COSE_Format_evercddl_everparsenomatch_pretty res0 = COSE_Format_parse_everparsenomatch(w);
        res = res0;
      }
      else
        res =
          KRML_EABORT(COSE_Format_evercddl_everparsenomatch_pretty,
            "unreachable (pattern matches are exhaustive in F*)");
      COSE_Format_evercddl_everparsenomatch_pretty w12 = res;
      _bind_c =
        (
          (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
            .tag = FStar_Pervasives_Native_Some,
            .v = w12
          }
        );
    }
    else
      _bind_c =
        (
          (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
            .tag = FStar_Pervasives_Native_None
          }
        );
    FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty w2 = _bind_c;
    K___COSE_Format_evercddl_bstr_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
    w110 = { .fst = w11, .snd = w2 };
    _bind_c4 =
      (
        (FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_){
          .tag = COSE_Format_Inl,
          { .case_Inl = w110 }
        }
      );
  }
  else
  {
    uint64_t dummy1 = 0ULL;
    cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
    cbor_det_t dest0 = c10;
    bool bres0 = cbor_det_map_get(c, c10, &dest0);
    option__CBOR_Pulse_API_Det_Type_cbor_det_t mg0;
    if (bres0)
    {
      cbor_det_t res = dest0;
      mg0 =
        (
          (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = res
          }
        );
    }
    else
      mg0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
    impl_map_group_result res0;
    if (mg0.tag == FStar_Pervasives_Native_None)
      res0 = MGFail;
    else if (mg0.tag == FStar_Pervasives_Native_Some)
    {
      cbor_det_t cv = mg0.v;
      bool check_value = COSE_Format_validate_bstr(cv);
      if (check_value)
        res0 = MGOK;
      else
        res0 = MGFail;
    }
    else
      res0 =
        KRML_EABORT(impl_map_group_result,
          "unreachable (pattern matches are exhaustive in F*)");
    impl_map_group_result res1 = res0;
    impl_map_group_result res10 = res1;
    impl_map_group_result test11;
    switch (res10)
    {
      case MGOK:
        {
          uint64_t i0 = dummy1;
          cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
          cbor_det_t dest = c1;
          bool bres = cbor_det_map_get(c, c1, &dest);
          option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
          if (bres)
          {
            cbor_det_t res = dest;
            mg =
              (
                (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = res
                }
              );
          }
          else
            mg =
              ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
          impl_map_group_result res0;
          if (mg.tag == FStar_Pervasives_Native_None)
            res0 = MGFail;
          else if (mg.tag == FStar_Pervasives_Native_Some)
          {
            cbor_det_t cv = mg.v;
            bool check_value = COSE_Format_validate_everparsenomatch(cv);
            if (check_value)
              res0 = MGOK;
            else
              res0 = MGCutFail;
          }
          else
            res0 =
              KRML_EABORT(impl_map_group_result,
                "unreachable (pattern matches are exhaustive in F*)");
          impl_map_group_result res1 = res0;
          impl_map_group_result res11 = res1;
          impl_map_group_result res;
          switch (res11)
          {
            case MGOK:
              {
                res = MGOK;
                break;
              }
            case MGFail:
              {
                dummy1 = i0;
                res = MGOK;
                break;
              }
            case MGCutFail:
              {
                res = MGCutFail;
                break;
              }
            default:
              {
                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          test11 = res;
          break;
        }
      case MGFail:
        {
          test11 = MGFail;
          break;
        }
      case MGCutFail:
        {
          test11 = MGCutFail;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
    _bind_c0;
    if (uu___is_MGOK(test11))
    {
      cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
      cbor_det_t dest0 = c10;
      bool bres0 = cbor_det_map_get(c, c10, &dest0);
      option__CBOR_Pulse_API_Det_Type_cbor_det_t ow0;
      if (bres0)
      {
        cbor_det_t res = dest0;
        ow0 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = res
            }
          );
      }
      else
        ow0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow0;
      COSE_Format_evercddl_bstr res0;
      if (_letpattern.tag == FStar_Pervasives_Native_Some)
      {
        cbor_det_t w = _letpattern.v;
        COSE_Format_evercddl_bstr res = COSE_Format_parse_bstr(w);
        res0 = res;
      }
      else
        res0 =
          KRML_EABORT(COSE_Format_evercddl_bstr,
            "unreachable (pattern matches are exhaustive in F*)");
      COSE_Format_evercddl_bstr w11 = res0;
      uint64_t dummy2 = 0ULL;
      KRML_HOST_IGNORE(&dummy2);
      cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
      cbor_det_t dest1 = c11;
      bool bres1 = cbor_det_map_get(c, c11, &dest1);
      option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
      if (bres1)
      {
        cbor_det_t res = dest1;
        mg =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = res
            }
          );
      }
      else
        mg = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      impl_map_group_result res1;
      if (mg.tag == FStar_Pervasives_Native_None)
        res1 = MGFail;
      else if (mg.tag == FStar_Pervasives_Native_Some)
      {
        cbor_det_t cv = mg.v;
        bool check_value = COSE_Format_validate_everparsenomatch(cv);
        if (check_value)
          res1 = MGOK;
        else
          res1 = MGCutFail;
      }
      else
        res1 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      impl_map_group_result res2 = res1;
      impl_map_group_result test12 = res2;
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty _bind_c;
      if (uu___is_MGOK(test12))
      {
        cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        cbor_det_t dest = c1;
        bool bres = cbor_det_map_get(c, c1, &dest);
        option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
        if (bres)
        {
          cbor_det_t res = dest;
          ow =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = res
              }
            );
        }
        else
          ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
        COSE_Format_evercddl_everparsenomatch_pretty res;
        if (_letpattern.tag == FStar_Pervasives_Native_Some)
        {
          cbor_det_t w = _letpattern.v;
          COSE_Format_evercddl_everparsenomatch_pretty res0 = COSE_Format_parse_everparsenomatch(w);
          res = res0;
        }
        else
          res =
            KRML_EABORT(COSE_Format_evercddl_everparsenomatch_pretty,
              "unreachable (pattern matches are exhaustive in F*)");
        COSE_Format_evercddl_everparsenomatch_pretty w12 = res;
        _bind_c =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_Some,
              .v = w12
            }
          );
      }
      else
        _bind_c =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_None
            }
          );
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty w2 = _bind_c;
      K___COSE_Format_evercddl_bstr_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
      w110 = { .fst = w11, .snd = w2 };
      _bind_c0 =
        (
          (FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_){
            .tag = COSE_Format_Inl,
            { .case_Inl = w110 }
          }
        );
    }
    else
    {
      uint64_t dummy20 = 0ULL;
      KRML_HOST_IGNORE(&dummy20);
      cbor_det_t c10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
      cbor_det_t dest0 = c10;
      bool bres0 = cbor_det_map_get(c, c10, &dest0);
      option__CBOR_Pulse_API_Det_Type_cbor_det_t mg0;
      if (bres0)
      {
        cbor_det_t res = dest0;
        mg0 =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = res
            }
          );
      }
      else
        mg0 = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      impl_map_group_result res0;
      if (mg0.tag == FStar_Pervasives_Native_None)
        res0 = MGFail;
      else if (mg0.tag == FStar_Pervasives_Native_Some)
      {
        cbor_det_t cv = mg0.v;
        bool check_value = COSE_Format_validate_everparsenomatch(cv);
        if (check_value)
          res0 = MGOK;
        else
          res0 = MGCutFail;
      }
      else
        res0 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      impl_map_group_result res1 = res0;
      impl_map_group_result test12 = res1;
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty _bind_c1;
      if (uu___is_MGOK(test12))
      {
        cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
        cbor_det_t dest = c1;
        bool bres = cbor_det_map_get(c, c1, &dest);
        option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
        if (bres)
        {
          cbor_det_t res = dest;
          ow =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = res
              }
            );
        }
        else
          ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
        COSE_Format_evercddl_everparsenomatch_pretty res;
        if (_letpattern.tag == FStar_Pervasives_Native_Some)
        {
          cbor_det_t w = _letpattern.v;
          COSE_Format_evercddl_everparsenomatch_pretty res0 = COSE_Format_parse_everparsenomatch(w);
          res = res0;
        }
        else
          res =
            KRML_EABORT(COSE_Format_evercddl_everparsenomatch_pretty,
              "unreachable (pattern matches are exhaustive in F*)");
        COSE_Format_evercddl_everparsenomatch_pretty w11 = res;
        _bind_c1 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_Some,
              .v = w11
            }
          );
      }
      else
        _bind_c1 =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_None
            }
          );
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty w11 = _bind_c1;
      uint64_t dummy2 = 0ULL;
      KRML_HOST_IGNORE(&dummy2);
      cbor_det_t c11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
      cbor_det_t dest1 = c11;
      bool bres1 = cbor_det_map_get(c, c11, &dest1);
      option__CBOR_Pulse_API_Det_Type_cbor_det_t mg;
      if (bres1)
      {
        cbor_det_t res = dest1;
        mg =
          (
            (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = res
            }
          );
      }
      else
        mg = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
      impl_map_group_result res2;
      if (mg.tag == FStar_Pervasives_Native_None)
        res2 = MGFail;
      else if (mg.tag == FStar_Pervasives_Native_Some)
      {
        cbor_det_t cv = mg.v;
        bool check_value = COSE_Format_validate_everparsenomatch(cv);
        if (check_value)
          res2 = MGOK;
        else
          res2 = MGCutFail;
      }
      else
        res2 =
          KRML_EABORT(impl_map_group_result,
            "unreachable (pattern matches are exhaustive in F*)");
      impl_map_group_result res3 = res2;
      impl_map_group_result test120 = res3;
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty _bind_c;
      if (uu___is_MGOK(test120))
      {
        cbor_det_t c1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        cbor_det_t dest = c1;
        bool bres = cbor_det_map_get(c, c1, &dest);
        option__CBOR_Pulse_API_Det_Type_cbor_det_t ow;
        if (bres)
        {
          cbor_det_t res = dest;
          ow =
            (
              (option__CBOR_Pulse_API_Det_Type_cbor_det_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = res
              }
            );
        }
        else
          ow = ((option__CBOR_Pulse_API_Det_Type_cbor_det_t){ .tag = FStar_Pervasives_Native_None });
        option__CBOR_Pulse_API_Det_Type_cbor_det_t _letpattern = ow;
        COSE_Format_evercddl_everparsenomatch_pretty res;
        if (_letpattern.tag == FStar_Pervasives_Native_Some)
        {
          cbor_det_t w = _letpattern.v;
          COSE_Format_evercddl_everparsenomatch_pretty res0 = COSE_Format_parse_everparsenomatch(w);
          res = res0;
        }
        else
          res =
            KRML_EABORT(COSE_Format_evercddl_everparsenomatch_pretty,
              "unreachable (pattern matches are exhaustive in F*)");
        COSE_Format_evercddl_everparsenomatch_pretty w12 = res;
        _bind_c =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_Some,
              .v = w12
            }
          );
      }
      else
        _bind_c =
          (
            (FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty){
              .tag = FStar_Pervasives_Native_None
            }
          );
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty w2 = _bind_c;
      K___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
      w20 = { .fst = w11, .snd = w2 };
      _bind_c0 =
        (
          (FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_){
            .tag = COSE_Format_Inr,
            { .case_Inr = w20 }
          }
        );
    }
    FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
    w2 = _bind_c0;
    _bind_c4 =
      (
        (FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_){
          .tag = COSE_Format_Inr,
          { .case_Inr = w2 }
        }
      );
  }
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  w22 = _bind_c4;
  K______FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  w13 = { .fst = w12, .snd = w22 };
  cbor_det_map_iterator_t i = cbor_det_map_iterator_start(c);
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
  rres =
    {
      .cddl_map_iterator_contents = i,
      .cddl_map_iterator_impl_validate1 = COSE_Format_aux_env27_validate_2,
      .cddl_map_iterator_impl_parse1 = COSE_Format_aux_env27_parse_2,
      .cddl_map_iterator_impl_validate_ex = COSE_Format_aux_env27_validate_3,
      .cddl_map_iterator_impl_validate2 = COSE_Format_aux_env27_validate_4,
      .cddl_map_iterator_impl_parse2 = COSE_Format_aux_env27_parse_4
    };
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
  w23 = { .tag = COSE_Format_Inr, { .case_Inr = rres } };
  COSE_Format_evercddl_header_map res11 = { .fst = w13, .snd = w23 };
  COSE_Format_evercddl_header_map_pretty
  res20 = COSE_Format_evercddl_header_map_pretty_right(res11);
  return res20;
}

static size_t
len__COSE_Format_evercddl_label_pretty(
  Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_pretty s
)
{
  return s.len;
}

static COSE_Format_evercddl_label_pretty
op_Array_Access__COSE_Format_evercddl_label_pretty(
  Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_pretty a,
  size_t i
)
{
  return a.elt[i];
}

static size_t
len___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_(
  Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
  s
)
{
  return s.len;
}

static K___COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
op_Array_Access___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_(
  Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
  a,
  size_t i
)
{
  return a.elt[i];
}

typedef struct
__Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__s
{
  Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
  fst;
  Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
  snd;
}
__Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_;

static __Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
split___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_(
  Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
  s,
  size_t i
)
{
  K___COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty *elt_ = s.elt + i;
  Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
  s1 = { .elt = s.elt, .len = i };
  Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
  s2 = { .elt = elt_, .len = s.len - i };
  return
    (
      (__Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_){
        .fst = s1,
        .snd = s2
      }
    );
}

size_t
COSE_Format_serialize_header_map(
  COSE_Format_evercddl_header_map_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_header_map c_ = COSE_Format_evercddl_header_map_pretty_left(c);
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_evercddl_header_map _letpattern = c_;
  K______FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  c1 = _letpattern.fst;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__CDDL_Pulse_Parse_MapGroup_map_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
  c2 = _letpattern.snd;
  K______FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty____FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  _letpattern10 = c1;
  K_____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  c110 = _letpattern10.fst;
  FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty__FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
  c210 = _letpattern10.snd;
  K_____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty__FStar_Pervasives_Native_option_COSE_Format_evercddl_bstr_pretty
  _letpattern20 = c110;
  K____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  c120 = _letpattern20.fst;
  FStar_Pervasives_Native_option__COSE_Format_evercddl_bstr_pretty c220 = _letpattern20.snd;
  K____FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty___FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty__FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  _letpattern30 = c120;
  K___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
  c130 = _letpattern30.fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
  c230 = _letpattern30.snd;
  K___FStar_Pervasives_Native_option_FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty_FStar_Pervasives_Native_option_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
  _letpattern40 = c130;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty
  c140 = _letpattern40.fst;
  FStar_Pervasives_Native_option__FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
  c240 = _letpattern40.snd;
  bool res10;
  if (c140.tag == FStar_Pervasives_Native_Some)
  {
    COSE_Format_evercddl_label c15 = c140.v;
    uint64_t count = pcount;
    bool res0;
    if (count < 18446744073709551615ULL)
    {
      size_t size0 = psize;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern5 = split__uint8_t(out, size0);
      Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern5.snd;
      cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 1ULL);
      size_t slen = len__uint8_t(out1);
      size_t len = cbor_det_size(c3, slen);
      option__size_t res1;
      if (len > (size_t)0U)
      {
        uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
        size_t len_ = cbor_det_serialize(c3, out2, len);
        res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
      }
      else
        res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
      size_t res;
      if (res1.tag == FStar_Pervasives_Native_None)
        res = (size_t)0U;
      else if (res1.tag == FStar_Pervasives_Native_Some)
        res = res1.v;
      else
        res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      size_t res10 = res;
      if (res10 > (size_t)0U)
      {
        size_t size1 = size0 + res10;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern6 = split__uint8_t(out, size1);
        Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern6.snd;
        size_t res2;
        if (c15.tag == COSE_Format_Inl)
        {
          COSE_Format_evercddl_int_pretty c16 = c15.case_Inl;
          size_t res = COSE_Format_serialize_int(c16, out2);
          res2 = res;
        }
        else if (c15.tag == COSE_Format_Inr)
        {
          COSE_Format_evercddl_bstr c25 = c15.case_Inr;
          size_t res = COSE_Format_serialize_tstr(c25, out2);
          res2 = res;
        }
        else
          res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        if (res2 > (size_t)0U)
        {
          size_t size2 = size1 + res2;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern7 = split__uint8_t(out, size2);
          Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern7.fst;
          size_t aout_len = len__uint8_t(out012);
          uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
          bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
          bool res1 = res;
          if (res1)
          {
            psize = size2;
            pcount = count + 1ULL;
            res0 = true;
          }
          else
            res0 = false;
        }
        else
          res0 = false;
      }
      else
        res0 = false;
    }
    else
      res0 = false;
    res10 = res0;
  }
  else if (c140.tag == FStar_Pervasives_Native_None)
    res10 = true;
  else
    res10 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  bool res12;
  if (res10)
  {
    bool res2;
    if (c240.tag == FStar_Pervasives_Native_Some)
    {
      FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_label_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
      c15 = c240.v;
      uint64_t count = pcount;
      bool res0;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern5 = split__uint8_t(out, size0);
        Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern5.snd;
        cbor_det_t c30 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 2ULL);
        size_t slen0 = len__uint8_t(out1);
        size_t len = cbor_det_size(c30, slen0);
        option__size_t res1;
        if (len > (size_t)0U)
        {
          uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
          size_t len_ = cbor_det_serialize(c30, out2, len);
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
        }
        else
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res2;
        if (res1.tag == FStar_Pervasives_Native_None)
          res2 = (size_t)0U;
        else if (res1.tag == FStar_Pervasives_Native_Some)
          res2 = res1.v;
        else
          res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        size_t res11 = res2;
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern6 = split__uint8_t(out, size1);
          Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern6.snd;
          uint64_t pcount1 = 0ULL;
          size_t psize1 = (size_t)0U;
          bool res1;
          if (c15.tag == COSE_Format_Inl)
          {
            Pulse_Lib_Slice_slice__COSE_Format_evercddl_label_pretty c16 = c15.case_Inl;
            bool res0;
            if (len__COSE_Format_evercddl_label_pretty(c16) == (size_t)0U)
              res0 = false;
            else
            {
              bool pres = true;
              size_t pi = (size_t)0U;
              size_t slen = len__COSE_Format_evercddl_label_pretty(c16);
              bool res = pres;
              bool cond;
              if (res)
              {
                size_t i = pi;
                cond = i < slen;
              }
              else
                cond = false;
              while (cond)
              {
                size_t i0 = pi;
                COSE_Format_evercddl_label_pretty
                x = op_Array_Access__COSE_Format_evercddl_label_pretty(c16, i0);
                bool res = COSE_Format_aux_env27_serialize_1(x, out2, &pcount1, &psize1);
                if (res)
                {
                  size_t i_ = i0 + (size_t)1U;
                  pi = i_;
                }
                else
                  pres = false;
                bool res0 = pres;
                bool ite;
                if (res0)
                {
                  size_t i = pi;
                  ite = i < slen;
                }
                else
                  ite = false;
                cond = ite;
              }
              res0 = pres;
            }
            res1 = res0;
          }
          else if (c15.tag == COSE_Format_Inr)
          {
            CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
            c25 = c15.case_Inr;
            bool res0 = cbor_det_array_iterator_is_empty(c25.cddl_array_iterator_contents);
            bool em = res0;
            bool res2;
            if (em)
              res2 = false;
            else
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
              pc = c25;
              bool pres = true;
              bool res = pres;
              bool cond;
              if (res)
              {
                CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
                c3 = pc;
                bool res2 = cbor_det_array_iterator_is_empty(c3.cddl_array_iterator_contents);
                bool em1 = res2;
                cond = !em1;
              }
              else
                cond = false;
              while (cond)
              {
                CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
                i = pc;
                uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
                cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
                bool _test = i.cddl_array_iterator_impl_validate(&pj);
                KRML_MAYBE_UNUSED_VAR(_test);
                cbor_det_array_iterator_t ji = pj;
                uint64_t len1 = cbor_det_array_iterator_length(ji);
                CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
                j =
                  {
                    .cddl_array_iterator_contents = ji,
                    .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
                    .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
                  };
                pc = j;
                cbor_det_array_iterator_t
                tri = cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents, len0 - len1);
                COSE_Format_evercddl_label_pretty res = i.cddl_array_iterator_impl_parse(tri);
                COSE_Format_evercddl_label_pretty x = res;
                bool res0 = COSE_Format_aux_env27_serialize_1(x, out2, &pcount1, &psize1);
                if (!res0)
                  pres = false;
                bool res1 = pres;
                bool ite;
                if (res1)
                {
                  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_label_pretty
                  c3 = pc;
                  bool res2 = cbor_det_array_iterator_is_empty(c3.cddl_array_iterator_contents);
                  bool em1 = res2;
                  ite = !em1;
                }
                else
                  ite = false;
                cond = ite;
              }
              res2 = pres;
            }
            res1 = res2;
          }
          else
            res1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          size_t _bind_c;
          if (res1)
          {
            size_t size = psize1;
            uint64_t count1 = pcount1;
            size_t aout_len = len__uint8_t(out2);
            uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out2);
            size_t res2 = cbor_det_serialize_array_to_array(count1, aout, aout_len, size);
            _bind_c = res2;
          }
          else
            _bind_c = (size_t)0U;
          size_t res2 = _bind_c;
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern7 = split__uint8_t(out, size2);
            Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern7.fst;
            size_t aout_len = len__uint8_t(out012);
            uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
            bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
            bool res1 = res;
            if (res1)
            {
              psize = size2;
              pcount = count + 1ULL;
              res0 = true;
            }
            else
              res0 = false;
          }
          else
            res0 = false;
        }
        else
          res0 = false;
      }
      else
        res0 = false;
      res2 = res0;
    }
    else if (c240.tag == FStar_Pervasives_Native_None)
      res2 = true;
    else
      res2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
    res12 = res2;
  }
  else
    res12 = false;
  bool res13;
  if (res12)
  {
    bool res20;
    if (c230.tag == FStar_Pervasives_Native_Some)
    {
      FStar_Pervasives_either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
      c14 = c230.v;
      uint64_t count = pcount;
      bool res0;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern4 = split__uint8_t(out, size0);
        Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern4.snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 3ULL);
        size_t slen = len__uint8_t(out1);
        size_t len = cbor_det_size(c3, slen);
        option__size_t res1;
        if (len > (size_t)0U)
        {
          uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
          size_t len_ = cbor_det_serialize(c3, out2, len);
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
        }
        else
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res;
        if (res1.tag == FStar_Pervasives_Native_None)
          res = (size_t)0U;
        else if (res1.tag == FStar_Pervasives_Native_Some)
          res = res1.v;
        else
          res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        size_t res11 = res;
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern5 = split__uint8_t(out, size1);
          Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern5.snd;
          size_t res2;
          if (c14.tag == COSE_Format_Inl)
          {
            COSE_Format_evercddl_bstr c15 = c14.case_Inl;
            size_t res = COSE_Format_serialize_tstr(c15, out2);
            res2 = res;
          }
          else if (c14.tag == COSE_Format_Inr)
          {
            COSE_Format_evercddl_int_pretty c24 = c14.case_Inr;
            size_t res = COSE_Format_serialize_int(c24, out2);
            res2 = res;
          }
          else
            res2 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern6 = split__uint8_t(out, size2);
            Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern6.fst;
            size_t aout_len = len__uint8_t(out012);
            uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
            bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
            bool res1 = res;
            if (res1)
            {
              psize = size2;
              pcount = count + 1ULL;
              res0 = true;
            }
            else
              res0 = false;
          }
          else
            res0 = false;
        }
        else
          res0 = false;
      }
      else
        res0 = false;
      res20 = res0;
    }
    else if (c230.tag == FStar_Pervasives_Native_None)
      res20 = true;
    else
      res20 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
    res13 = res20;
  }
  else
    res13 = false;
  bool res14;
  if (res13)
  {
    bool res2;
    if (c220.tag == FStar_Pervasives_Native_Some)
    {
      COSE_Format_evercddl_bstr c13 = c220.v;
      uint64_t count = pcount;
      bool res0;
      if (count < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern3 = split__uint8_t(out, size0);
        Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 4ULL);
        size_t slen = len__uint8_t(out1);
        size_t len = cbor_det_size(c3, slen);
        option__size_t res1;
        if (len > (size_t)0U)
        {
          uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
          size_t len_ = cbor_det_serialize(c3, out2, len);
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
        }
        else
          res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res;
        if (res1.tag == FStar_Pervasives_Native_None)
          res = (size_t)0U;
        else if (res1.tag == FStar_Pervasives_Native_Some)
          res = res1.v;
        else
          res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        size_t res11 = res;
        if (res11 > (size_t)0U)
        {
          size_t size1 = size0 + res11;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern4 = split__uint8_t(out, size1);
          Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern4.snd;
          size_t res2 = COSE_Format_serialize_bstr(c13, out2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern5 = split__uint8_t(out, size2);
            Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern5.fst;
            size_t aout_len = len__uint8_t(out012);
            uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
            bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
            bool res1 = res;
            if (res1)
            {
              psize = size2;
              pcount = count + 1ULL;
              res0 = true;
            }
            else
              res0 = false;
          }
          else
            res0 = false;
        }
        else
          res0 = false;
      }
      else
        res0 = false;
      res2 = res0;
    }
    else if (c220.tag == FStar_Pervasives_Native_None)
      res2 = true;
    else
      res2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
    res14 = res2;
  }
  else
    res14 = false;
  bool res1;
  if (res14)
  {
    bool res20;
    if (c210.tag == COSE_Format_Inl)
    {
      K___COSE_Format_evercddl_bstr_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
      c12 = c210.case_Inl;
      K___COSE_Format_evercddl_bstr_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
      _letpattern2 = c12;
      COSE_Format_evercddl_bstr c13 = _letpattern2.fst;
      FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty
      c22 = _letpattern2.snd;
      uint64_t count0 = pcount;
      bool res11;
      if (count0 < 18446744073709551615ULL)
      {
        size_t size0 = psize;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern3 = split__uint8_t(out, size0);
        Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
        cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
        size_t slen = len__uint8_t(out1);
        size_t len = cbor_det_size(c3, slen);
        option__size_t res0;
        if (len > (size_t)0U)
        {
          uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
          size_t len_ = cbor_det_serialize(c3, out2, len);
          res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
        }
        else
          res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
        size_t res;
        if (res0.tag == FStar_Pervasives_Native_None)
          res = (size_t)0U;
        else if (res0.tag == FStar_Pervasives_Native_Some)
          res = res0.v;
        else
          res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
        size_t res110 = res;
        if (res110 > (size_t)0U)
        {
          size_t size1 = size0 + res110;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern4 = split__uint8_t(out, size1);
          Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern4.snd;
          size_t res2 = COSE_Format_serialize_bstr(c13, out2);
          if (res2 > (size_t)0U)
          {
            size_t size2 = size1 + res2;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern5 = split__uint8_t(out, size2);
            Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern5.fst;
            size_t aout_len = len__uint8_t(out012);
            uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
            bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
            bool res0 = res;
            if (res0)
            {
              psize = size2;
              pcount = count0 + 1ULL;
              res11 = true;
            }
            else
              res11 = false;
          }
          else
            res11 = false;
        }
        else
          res11 = false;
      }
      else
        res11 = false;
      bool res0;
      if (res11)
      {
        bool res2;
        if (c22.tag == FStar_Pervasives_Native_Some)
        {
          COSE_Format_evercddl_everparsenomatch_pretty c14 = c22.v;
          uint64_t count = pcount;
          bool res0;
          if (count < 18446744073709551615ULL)
          {
            size_t size0 = psize;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern3 = split__uint8_t(out, size0);
            Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
            cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
            size_t slen = len__uint8_t(out1);
            size_t len = cbor_det_size(c3, slen);
            option__size_t res1;
            if (len > (size_t)0U)
            {
              uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
              size_t len_ = cbor_det_serialize(c3, out2, len);
              res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
            }
            else
              res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
            size_t res;
            if (res1.tag == FStar_Pervasives_Native_None)
              res = (size_t)0U;
            else if (res1.tag == FStar_Pervasives_Native_Some)
              res = res1.v;
            else
              res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
            size_t res12 = res;
            if (res12 > (size_t)0U)
            {
              size_t size1 = size0 + res12;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern4 = split__uint8_t(out, size1);
              Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern4.snd;
              size_t res2 = COSE_Format_serialize_everparsenomatch(c14, out2);
              if (res2 > (size_t)0U)
              {
                size_t size2 = size1 + res2;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern5 = split__uint8_t(out, size2);
                Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern5.fst;
                size_t aout_len = len__uint8_t(out012);
                uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
                bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
                bool res1 = res;
                if (res1)
                {
                  psize = size2;
                  pcount = count + 1ULL;
                  res0 = true;
                }
                else
                  res0 = false;
              }
              else
                res0 = false;
            }
            else
              res0 = false;
          }
          else
            res0 = false;
          res2 = res0;
        }
        else if (c22.tag == FStar_Pervasives_Native_None)
          res2 = true;
        else
          res2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
        res0 = res2;
      }
      else
        res0 = false;
      res20 = res0;
    }
    else if (c210.tag == COSE_Format_Inr)
    {
      FStar_Pervasives_either___COSE_Format_evercddl_bstr_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_
      c22 = c210.case_Inr;
      bool res0;
      if (c22.tag == COSE_Format_Inl)
      {
        K___COSE_Format_evercddl_bstr_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
        c12 = c22.case_Inl;
        K___COSE_Format_evercddl_bstr_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
        _letpattern2 = c12;
        COSE_Format_evercddl_bstr c13 = _letpattern2.fst;
        FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty
        c23 = _letpattern2.snd;
        uint64_t count0 = pcount;
        bool res11;
        if (count0 < 18446744073709551615ULL)
        {
          size_t size0 = psize;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern3 = split__uint8_t(out, size0);
          Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
          cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
          size_t slen = len__uint8_t(out1);
          size_t len = cbor_det_size(c3, slen);
          option__size_t res0;
          if (len > (size_t)0U)
          {
            uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
            size_t len_ = cbor_det_serialize(c3, out2, len);
            res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
          }
          else
            res0 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
          size_t res;
          if (res0.tag == FStar_Pervasives_Native_None)
            res = (size_t)0U;
          else if (res0.tag == FStar_Pervasives_Native_Some)
            res = res0.v;
          else
            res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          size_t res110 = res;
          if (res110 > (size_t)0U)
          {
            size_t size1 = size0 + res110;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern4 = split__uint8_t(out, size1);
            Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern4.snd;
            size_t res2 = COSE_Format_serialize_bstr(c13, out2);
            if (res2 > (size_t)0U)
            {
              size_t size2 = size1 + res2;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern5 = split__uint8_t(out, size2);
              Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern5.fst;
              size_t aout_len = len__uint8_t(out012);
              uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
              bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
              bool res0 = res;
              if (res0)
              {
                psize = size2;
                pcount = count0 + 1ULL;
                res11 = true;
              }
              else
                res11 = false;
            }
            else
              res11 = false;
          }
          else
            res11 = false;
        }
        else
          res11 = false;
        bool res1;
        if (res11)
        {
          bool res2;
          if (c23.tag == FStar_Pervasives_Native_Some)
          {
            COSE_Format_evercddl_everparsenomatch_pretty c14 = c23.v;
            uint64_t count = pcount;
            bool res0;
            if (count < 18446744073709551615ULL)
            {
              size_t size0 = psize;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern3 = split__uint8_t(out, size0);
              Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
              cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
              size_t slen = len__uint8_t(out1);
              size_t len = cbor_det_size(c3, slen);
              option__size_t res1;
              if (len > (size_t)0U)
              {
                uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
                size_t len_ = cbor_det_serialize(c3, out2, len);
                res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
              }
              else
                res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
              size_t res;
              if (res1.tag == FStar_Pervasives_Native_None)
                res = (size_t)0U;
              else if (res1.tag == FStar_Pervasives_Native_Some)
                res = res1.v;
              else
                res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
              size_t res12 = res;
              if (res12 > (size_t)0U)
              {
                size_t size1 = size0 + res12;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern4 = split__uint8_t(out, size1);
                Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern4.snd;
                size_t res2 = COSE_Format_serialize_everparsenomatch(c14, out2);
                if (res2 > (size_t)0U)
                {
                  size_t size2 = size1 + res2;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  _letpattern5 = split__uint8_t(out, size2);
                  Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern5.fst;
                  size_t aout_len = len__uint8_t(out012);
                  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
                  bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
                  bool res1 = res;
                  if (res1)
                  {
                    psize = size2;
                    pcount = count + 1ULL;
                    res0 = true;
                  }
                  else
                    res0 = false;
                }
                else
                  res0 = false;
              }
              else
                res0 = false;
            }
            else
              res0 = false;
            res2 = res0;
          }
          else if (c23.tag == FStar_Pervasives_Native_None)
            res2 = true;
          else
            res2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          res1 = res2;
        }
        else
          res1 = false;
        res0 = res1;
      }
      else if (c22.tag == COSE_Format_Inr)
      {
        K___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
        c23 = c22.case_Inr;
        K___FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty_FStar_Pervasives_Native_option_COSE_Format_evercddl_everparsenomatch_pretty
        _letpattern2 = c23;
        FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty
        c12 = _letpattern2.fst;
        FStar_Pervasives_Native_option__COSE_Format_evercddl_everparsenomatch_pretty
        c24 = _letpattern2.snd;
        bool res11;
        if (c12.tag == FStar_Pervasives_Native_Some)
        {
          COSE_Format_evercddl_everparsenomatch_pretty c13 = c12.v;
          uint64_t count = pcount;
          bool res0;
          if (count < 18446744073709551615ULL)
          {
            size_t size0 = psize;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern3 = split__uint8_t(out, size0);
            Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
            cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 6ULL);
            size_t slen = len__uint8_t(out1);
            size_t len = cbor_det_size(c3, slen);
            option__size_t res1;
            if (len > (size_t)0U)
            {
              uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
              size_t len_ = cbor_det_serialize(c3, out2, len);
              res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
            }
            else
              res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
            size_t res;
            if (res1.tag == FStar_Pervasives_Native_None)
              res = (size_t)0U;
            else if (res1.tag == FStar_Pervasives_Native_Some)
              res = res1.v;
            else
              res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
            size_t res11 = res;
            if (res11 > (size_t)0U)
            {
              size_t size1 = size0 + res11;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern4 = split__uint8_t(out, size1);
              Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern4.snd;
              size_t res2 = COSE_Format_serialize_everparsenomatch(c13, out2);
              if (res2 > (size_t)0U)
              {
                size_t size2 = size1 + res2;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern5 = split__uint8_t(out, size2);
                Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern5.fst;
                size_t aout_len = len__uint8_t(out012);
                uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
                bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
                bool res1 = res;
                if (res1)
                {
                  psize = size2;
                  pcount = count + 1ULL;
                  res0 = true;
                }
                else
                  res0 = false;
              }
              else
                res0 = false;
            }
            else
              res0 = false;
          }
          else
            res0 = false;
          res11 = res0;
        }
        else if (c12.tag == FStar_Pervasives_Native_None)
          res11 = true;
        else
          res11 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
        bool res1;
        if (res11)
        {
          bool res2;
          if (c24.tag == FStar_Pervasives_Native_Some)
          {
            COSE_Format_evercddl_everparsenomatch_pretty c13 = c24.v;
            uint64_t count = pcount;
            bool res0;
            if (count < 18446744073709551615ULL)
            {
              size_t size0 = psize;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern3 = split__uint8_t(out, size0);
              Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
              cbor_det_t c3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, 5ULL);
              size_t slen = len__uint8_t(out1);
              size_t len = cbor_det_size(c3, slen);
              option__size_t res1;
              if (len > (size_t)0U)
              {
                uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
                size_t len_ = cbor_det_serialize(c3, out2, len);
                res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
              }
              else
                res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
              size_t res;
              if (res1.tag == FStar_Pervasives_Native_None)
                res = (size_t)0U;
              else if (res1.tag == FStar_Pervasives_Native_Some)
                res = res1.v;
              else
                res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
              size_t res12 = res;
              if (res12 > (size_t)0U)
              {
                size_t size1 = size0 + res12;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern4 = split__uint8_t(out, size1);
                Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern4.snd;
                size_t res2 = COSE_Format_serialize_everparsenomatch(c13, out2);
                if (res2 > (size_t)0U)
                {
                  size_t size2 = size1 + res2;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  _letpattern5 = split__uint8_t(out, size2);
                  Pulse_Lib_Slice_slice__uint8_t out012 = _letpattern5.fst;
                  size_t aout_len = len__uint8_t(out012);
                  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out012);
                  bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
                  bool res1 = res;
                  if (res1)
                  {
                    psize = size2;
                    pcount = count + 1ULL;
                    res0 = true;
                  }
                  else
                    res0 = false;
                }
                else
                  res0 = false;
              }
              else
                res0 = false;
            }
            else
              res0 = false;
            res2 = res0;
          }
          else if (c24.tag == FStar_Pervasives_Native_None)
            res2 = true;
          else
            res2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          res1 = res2;
        }
        else
          res1 = false;
        res0 = res1;
      }
      else
        res0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
      res20 = res0;
    }
    else
      res20 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
    res1 = res20;
  }
  else
    res1 = false;
  bool res0;
  if (res1)
  {
    bool res20;
    if (c2.tag == COSE_Format_Inl)
    {
      Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
      c11 = c2.case_Inl;
      Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
      i = c11;
      Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
      pi = i;
      KRML_HOST_IGNORE(&pi);
      Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
      pc = i;
      bool pres = true;
      bool res0 = pres;
      bool cond;
      if (res0)
      {
        Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
        c3 = pc;
        bool
        em =
          len___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_(c3) ==
            (size_t)0U;
        cond = !em;
      }
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
          Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
          i1 = pc;
          K___COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
          res =
            op_Array_Access___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_(i1,
              (size_t)0U);
          __Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty__Pulse_Lib_Slice_slice__COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
          _letpattern1 =
            split___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_(i1,
              (size_t)1U);
          Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
          ir = _letpattern1.snd;
          Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
          i_ = ir;
          pc = i_;
          K___COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
          _letpattern10 = res;
          COSE_Format_evercddl_label_pretty ck = _letpattern10.fst;
          COSE_Format_evercddl_values_pretty cv = _letpattern10.snd;
          size_t size0 = psize;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern2 = split__uint8_t(out, size0);
          Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
          size_t sz1 = COSE_Format_aux_env27_serialize_2(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            size_t len = len__uint8_t(out1);
            uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(out1);
            uint8_t *a1 = a0;
            size_t res = cbor_det_validate(a1, len);
            size_t len0 = res;
            option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_
            _letpattern3;
            if (len0 == (size_t)0U)
              _letpattern3 =
                (
                  (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                    .tag = FStar_Pervasives_Native_None
                  }
                );
            else
            {
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              s_ = split__uint8_t(out1, len0);
              Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
              Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern30 = { .fst = s1, .snd = s2 };
              Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern30.fst;
              Pulse_Lib_Slice_slice__uint8_t rem = _letpattern30.snd;
              size_t len1 = len__uint8_t(input2);
              uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
              uint8_t *a0 = a;
              cbor_det_t res = cbor_det_parse(a0, len1);
              cbor_det_t res0 = res;
              _letpattern3 =
                (
                  (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = { .fst = res0, .snd = rem }
                  }
                );
            }
            if (_letpattern3.tag == FStar_Pervasives_Native_Some)
            {
              __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t
              oo = _letpattern3.v;
              __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern4 = oo;
              cbor_det_t o = _letpattern4.fst;
              bool is_except = COSE_Format_aux_env27_validate_3(o);
              if (is_except)
                pres = false;
              else
              {
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern5 = split__uint8_t(out1, sz1);
                Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern5.snd;
                size_t sz2 = COSE_Format_aux_env27_serialize_4(cv, out2);
                if (sz2 == (size_t)0U)
                  pres = false;
                else
                {
                  size_t size1 = size0 + sz1;
                  size_t size2 = size1 + sz2;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  _letpattern6 = split__uint8_t(out, size2);
                  Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern6.fst;
                  Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern6.snd;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  _letpattern60 = { .fst = s1, .snd = s2 };
                  Pulse_Lib_Slice_slice__uint8_t outl = _letpattern60.fst;
                  size_t aout_len = len__uint8_t(outl);
                  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(outl);
                  bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
                  bool inserted = res;
                  if (!inserted)
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
        bool res = pres;
        bool ite;
        if (res)
        {
          Pulse_Lib_Slice_slice___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_
          c3 = pc;
          bool
          em =
            len___COSE_Format_aux_env27_type_2_pretty___COSE_Format_aux_env27_type_4_pretty_(c3) ==
              (size_t)0U;
          ite = !em;
        }
        else
          ite = false;
        cond = ite;
      }
      bool res = pres;
      bool res1 = res;
      res20 = res1;
    }
    else if (c2.tag == COSE_Format_Inr)
    {
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
      c21 = c2.case_Inr;
      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
      pc = c21;
      bool pres = true;
      bool res = pres;
      bool cond0;
      if (res)
      {
        CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
        c3 = pc;
        cbor_det_map_iterator_t pj = c3.cddl_map_iterator_contents;
        bool pres1 = true;
        bool res2 = pres1;
        bool cond;
        if (res2)
        {
          cbor_det_map_iterator_t j = pj;
          bool test = cbor_det_map_iterator_is_empty(j);
          cond = !test;
        }
        else
          cond = false;
        while (cond)
        {
          cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
          cbor_det_t elt_key = cbor_det_map_entry_key(elt);
          bool test_key = c3.cddl_map_iterator_impl_validate1(elt_key);
          if (!!test_key)
          {
            bool test_ex = c3.cddl_map_iterator_impl_validate_ex(elt_key);
            if (!test_ex)
            {
              cbor_det_t elt_value = cbor_det_map_entry_value(elt);
              bool test_value = c3.cddl_map_iterator_impl_validate2(elt_value);
              pres1 = !test_value;
            }
          }
          bool res2 = pres1;
          bool ite;
          if (res2)
          {
            cbor_det_map_iterator_t j = pj;
            bool test = cbor_det_map_iterator_is_empty(j);
            ite = !test;
          }
          else
            ite = false;
          cond = ite;
        }
        bool em = pres1;
        cond0 = !em;
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
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
          i = pc;
          cbor_det_map_iterator_t pj = i.cddl_map_iterator_contents;
          cbor_det_map_entry_t hd0 = cbor_det_map_iterator_next(&pj);
          cbor_det_map_entry_t phd = hd0;
          cbor_det_map_entry_t hd1 = phd;
          cbor_det_t hd_key0 = cbor_det_map_entry_key(hd1);
          bool test_key0 = i.cddl_map_iterator_impl_validate1(hd_key0);
          bool cond;
          if (!test_key0)
            cond = true;
          else
          {
            bool test_ex = i.cddl_map_iterator_impl_validate_ex(hd_key0);
            if (test_ex)
              cond = true;
            else
            {
              cbor_det_t hd_value = cbor_det_map_entry_value(hd1);
              bool test_value = i.cddl_map_iterator_impl_validate2(hd_value);
              cond = !test_value;
            }
          }
          while (cond)
          {
            cbor_det_map_entry_t hd = cbor_det_map_iterator_next(&pj);
            phd = hd;
            cbor_det_map_entry_t hd0 = phd;
            cbor_det_t hd_key = cbor_det_map_entry_key(hd0);
            bool test_key = i.cddl_map_iterator_impl_validate1(hd_key);
            bool ite;
            if (!test_key)
              ite = true;
            else
            {
              bool test_ex = i.cddl_map_iterator_impl_validate_ex(hd_key);
              if (test_ex)
                ite = true;
              else
              {
                cbor_det_t hd_value = cbor_det_map_entry_value(hd0);
                bool test_value = i.cddl_map_iterator_impl_validate2(hd_value);
                ite = !test_value;
              }
            }
            cond = ite;
          }
          cbor_det_map_entry_t hd = phd;
          cbor_det_t hd_key = cbor_det_map_entry_key(hd);
          COSE_Format_evercddl_label_pretty hd_key_res = i.cddl_map_iterator_impl_parse1(hd_key);
          cbor_det_t hd_value = cbor_det_map_entry_value(hd);
          COSE_Format_evercddl_values_pretty
          hd_value_res = i.cddl_map_iterator_impl_parse2(hd_value);
          cbor_det_map_iterator_t j = pj;
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
          i_ =
            {
              .cddl_map_iterator_contents = j,
              .cddl_map_iterator_impl_validate1 = i.cddl_map_iterator_impl_validate1,
              .cddl_map_iterator_impl_parse1 = i.cddl_map_iterator_impl_parse1,
              .cddl_map_iterator_impl_validate_ex = i.cddl_map_iterator_impl_validate_ex,
              .cddl_map_iterator_impl_validate2 = i.cddl_map_iterator_impl_validate2,
              .cddl_map_iterator_impl_parse2 = i.cddl_map_iterator_impl_parse2
            };
          pc = i_;
          K___COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
          _letpattern1 = { .fst = hd_key_res, .snd = hd_value_res };
          COSE_Format_evercddl_label_pretty ck = _letpattern1.fst;
          COSE_Format_evercddl_values_pretty cv = _letpattern1.snd;
          size_t size0 = psize;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern2 = split__uint8_t(out, size0);
          Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
          size_t sz1 = COSE_Format_aux_env27_serialize_2(ck, out1);
          if (sz1 == (size_t)0U)
            pres = false;
          else
          {
            size_t len = len__uint8_t(out1);
            uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(out1);
            uint8_t *a1 = a0;
            size_t res = cbor_det_validate(a1, len);
            size_t len0 = res;
            option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_
            _letpattern3;
            if (len0 == (size_t)0U)
              _letpattern3 =
                (
                  (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                    .tag = FStar_Pervasives_Native_None
                  }
                );
            else
            {
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              s_ = split__uint8_t(out1, len0);
              Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
              Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern30 = { .fst = s1, .snd = s2 };
              Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern30.fst;
              Pulse_Lib_Slice_slice__uint8_t rem = _letpattern30.snd;
              size_t len1 = len__uint8_t(input2);
              uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
              uint8_t *a0 = a;
              cbor_det_t res = cbor_det_parse(a0, len1);
              cbor_det_t res0 = res;
              _letpattern3 =
                (
                  (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = { .fst = res0, .snd = rem }
                  }
                );
            }
            if (_letpattern3.tag == FStar_Pervasives_Native_Some)
            {
              __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t
              oo = _letpattern3.v;
              __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern4 = oo;
              cbor_det_t o = _letpattern4.fst;
              bool is_except = COSE_Format_aux_env27_validate_3(o);
              if (is_except)
                pres = false;
              else
              {
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern5 = split__uint8_t(out1, sz1);
                Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern5.snd;
                size_t sz2 = COSE_Format_aux_env27_serialize_4(cv, out2);
                if (sz2 == (size_t)0U)
                  pres = false;
                else
                {
                  size_t size1 = size0 + sz1;
                  size_t size2 = size1 + sz2;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  _letpattern6 = split__uint8_t(out, size2);
                  Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern6.fst;
                  Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern6.snd;
                  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                  _letpattern60 = { .fst = s1, .snd = s2 };
                  Pulse_Lib_Slice_slice__uint8_t outl = _letpattern60.fst;
                  size_t aout_len = len__uint8_t(outl);
                  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(outl);
                  bool res = cbor_det_serialize_map_insert_to_array(aout, aout_len, size0, size1);
                  bool inserted = res;
                  if (!inserted)
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
        bool res = pres;
        bool ite0;
        if (res)
        {
          CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty
          c3 = pc;
          cbor_det_map_iterator_t pj = c3.cddl_map_iterator_contents;
          bool pres1 = true;
          bool res2 = pres1;
          bool cond;
          if (res2)
          {
            cbor_det_map_iterator_t j = pj;
            bool test = cbor_det_map_iterator_is_empty(j);
            cond = !test;
          }
          else
            cond = false;
          while (cond)
          {
            cbor_det_map_entry_t elt = cbor_det_map_iterator_next(&pj);
            cbor_det_t elt_key = cbor_det_map_entry_key(elt);
            bool test_key = c3.cddl_map_iterator_impl_validate1(elt_key);
            if (!!test_key)
            {
              bool test_ex = c3.cddl_map_iterator_impl_validate_ex(elt_key);
              if (!test_ex)
              {
                cbor_det_t elt_value = cbor_det_map_entry_value(elt);
                bool test_value = c3.cddl_map_iterator_impl_validate2(elt_value);
                pres1 = !test_value;
              }
            }
            bool res2 = pres1;
            bool ite;
            if (res2)
            {
              cbor_det_map_iterator_t j = pj;
              bool test = cbor_det_map_iterator_is_empty(j);
              ite = !test;
            }
            else
              ite = false;
            cond = ite;
          }
          bool em = pres1;
          ite0 = !em;
        }
        else
          ite0 = false;
        cond0 = ite0;
      }
      bool res0 = pres;
      res20 = res0;
    }
    else
      res20 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
    res0 = res20;
  }
  else
    res0 = false;
  size_t _bind_c;
  if (res0)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = len__uint8_t(out);
    uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
    size_t res1 = cbor_det_serialize_map_to_array(count, aout, aout_len, size);
    _bind_c = res1;
  }
  else
    _bind_c = (size_t)0U;
  size_t res = _bind_c;
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_header_map_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_header_map(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_header_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_header_map(rl);
    if (test)
    {
      COSE_Format_evercddl_header_map_pretty x = COSE_Format_parse_header_map(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_header_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_validate_empty_or_serialized_map(cbor_det_t c)
{
  uint8_t mt = cbor_det_major_type(c);
  bool test0 = mt == CBOR_MAJOR_TYPE_BYTE_STRING;
  bool test;
  if (test0)
  {
    uint64_t len0 = cbor_det_get_string_length(c);
    uint8_t *a0 = cbor_det_get_string(c);
    Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a0, (size_t)len0);
    Pulse_Lib_Slice_slice__uint8_t sl = s;
    Pulse_Lib_Slice_slice__uint8_t pl = sl;
    size_t len = len__uint8_t(pl);
    uint8_t *a1 = slice_to_arrayptr_intro__uint8_t(pl);
    uint8_t *a2 = a1;
    size_t res0 = cbor_det_validate(a2, len);
    size_t len2 = res0;
    option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ read;
    if (len2 == (size_t)0U)
      read =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(pl, len2);
      Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern = { .fst = s1, .snd = s2 };
      Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
      size_t len1 = len__uint8_t(input2);
      uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
      uint8_t *a0 = a;
      cbor_det_t res = cbor_det_parse(a0, len1);
      cbor_det_t res0 = res;
      read =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = res0, .snd = rem }
          }
        );
    }
    if (read.tag == FStar_Pervasives_Native_None)
      test = false;
    else if (read.tag == FStar_Pervasives_Native_Some)
    {
      __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t r = read.v;
      __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = r;
      cbor_det_t res = _letpattern.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
      if (len__uint8_t(rem) == (size_t)0U)
      {
        bool tres = COSE_Format_validate_header_map(res);
        test = tres;
      }
      else
        test = false;
    }
    else
      test = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  }
  else
    test = false;
  if (test)
    return true;
  else
  {
    uint8_t mt = cbor_det_major_type(c);
    if (mt == 2U)
    {
      uint64_t len = cbor_det_get_string_length(c);
      uint8_t *a = cbor_det_get_string(c);
      Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
      Pulse_Lib_Slice_slice__uint8_t sl = s;
      Pulse_Lib_Slice_slice__uint8_t str = sl;
      size_t len0 = len__uint8_t(str);
      return (size_t)0U <= len0 && len0 <= (size_t)0U;
    }
    else
      return false;
  }
}

bool
COSE_Format_uu___is_Mkevercddl_empty_or_serialized_map_pretty0(
  COSE_Format_evercddl_empty_or_serialized_map_pretty projectee
)
{
  if (projectee.tag == COSE_Format_Mkevercddl_empty_or_serialized_map_pretty0)
    return true;
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_empty_or_serialized_map_pretty1(
  COSE_Format_evercddl_empty_or_serialized_map_pretty projectee
)
{
  if (projectee.tag == COSE_Format_Mkevercddl_empty_or_serialized_map_pretty1)
    return true;
  else
    return false;
}

COSE_Format_evercddl_empty_or_serialized_map_pretty
COSE_Format_evercddl_empty_or_serialized_map_pretty_right(
  COSE_Format_evercddl_empty_or_serialized_map x2
)
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

COSE_Format_evercddl_empty_or_serialized_map
COSE_Format_evercddl_empty_or_serialized_map_pretty_left(
  COSE_Format_evercddl_empty_or_serialized_map_pretty x7
)
{
  if (x7.tag == COSE_Format_Mkevercddl_empty_or_serialized_map_pretty0)
  {
    COSE_Format_evercddl_header_map_pretty
    x10 = x7.case_Mkevercddl_empty_or_serialized_map_pretty0;
    return
      (
        (COSE_Format_evercddl_empty_or_serialized_map){
          .tag = COSE_Format_Inl,
          { .case_Inl = x10 }
        }
      );
  }
  else if (x7.tag == COSE_Format_Mkevercddl_empty_or_serialized_map_pretty1)
  {
    Pulse_Lib_Slice_slice__uint8_t x12 = x7.case_Mkevercddl_empty_or_serialized_map_pretty1;
    return
      (
        (COSE_Format_evercddl_empty_or_serialized_map){
          .tag = COSE_Format_Inr,
          { .case_Inr = x12 }
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

static cbor_det_t
fst__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t(
  __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t x
)
{
  return x.fst;
}

COSE_Format_evercddl_empty_or_serialized_map_pretty
COSE_Format_parse_empty_or_serialized_map(cbor_det_t c)
{
  uint8_t mt = cbor_det_major_type(c);
  bool test0 = mt == CBOR_MAJOR_TYPE_BYTE_STRING;
  bool test;
  if (test0)
  {
    uint64_t len0 = cbor_det_get_string_length(c);
    uint8_t *a0 = cbor_det_get_string(c);
    Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a0, (size_t)len0);
    Pulse_Lib_Slice_slice__uint8_t sl = s;
    Pulse_Lib_Slice_slice__uint8_t pl = sl;
    size_t len = len__uint8_t(pl);
    uint8_t *a1 = slice_to_arrayptr_intro__uint8_t(pl);
    uint8_t *a2 = a1;
    size_t res0 = cbor_det_validate(a2, len);
    size_t len2 = res0;
    option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ read;
    if (len2 == (size_t)0U)
      read =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(pl, len2);
      Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern = { .fst = s1, .snd = s2 };
      Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
      size_t len1 = len__uint8_t(input2);
      uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
      uint8_t *a0 = a;
      cbor_det_t res = cbor_det_parse(a0, len1);
      cbor_det_t res0 = res;
      read =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = res0, .snd = rem }
          }
        );
    }
    if (read.tag == FStar_Pervasives_Native_None)
      test = false;
    else if (read.tag == FStar_Pervasives_Native_Some)
    {
      __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t r = read.v;
      __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = r;
      cbor_det_t res = _letpattern.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
      if (len__uint8_t(rem) == (size_t)0U)
      {
        bool tres = COSE_Format_validate_header_map(res);
        test = tres;
      }
      else
        test = false;
    }
    else
      test = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
  }
  else
    test = false;
  COSE_Format_evercddl_empty_or_serialized_map res1;
  if (test)
  {
    uint64_t len0 = cbor_det_get_string_length(c);
    uint8_t *a0 = cbor_det_get_string(c);
    Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a0, (size_t)len0);
    Pulse_Lib_Slice_slice__uint8_t sl = s;
    Pulse_Lib_Slice_slice__uint8_t cs = sl;
    size_t len = len__uint8_t(cs);
    uint8_t *a1 = slice_to_arrayptr_intro__uint8_t(cs);
    uint8_t *a2 = a1;
    size_t res0 = cbor_det_validate(a2, len);
    size_t len2 = res0;
    option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ cp;
    if (len2 == (size_t)0U)
      cp =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(cs, len2);
      Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern = { .fst = s1, .snd = s2 };
      Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
      Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
      size_t len1 = len__uint8_t(input2);
      uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
      uint8_t *a0 = a;
      cbor_det_t res = cbor_det_parse(a0, len1);
      cbor_det_t res0 = res;
      cp =
        (
          (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = res0, .snd = rem }
          }
        );
    }
    COSE_Format_evercddl_header_map_pretty res;
    if (cp.tag == FStar_Pervasives_Native_Some)
    {
      __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t cp_ = cp.v;
      cbor_det_t cp1 = fst__CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t(cp_);
      COSE_Format_evercddl_header_map_pretty res0 = COSE_Format_parse_header_map(cp1);
      res = res0;
    }
    else
      res =
        KRML_EABORT(COSE_Format_evercddl_header_map_pretty,
          "unreachable (pattern matches are exhaustive in F*)");
    res1 =
      (
        (COSE_Format_evercddl_empty_or_serialized_map){
          .tag = COSE_Format_Inl,
          { .case_Inl = res }
        }
      );
  }
  else
  {
    uint64_t len = cbor_det_get_string_length(c);
    uint8_t *a = cbor_det_get_string(c);
    Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
    Pulse_Lib_Slice_slice__uint8_t sl = s;
    Pulse_Lib_Slice_slice__uint8_t s0 = sl;
    Pulse_Lib_Slice_slice__uint8_t res = s0;
    res1 =
      (
        (COSE_Format_evercddl_empty_or_serialized_map){
          .tag = COSE_Format_Inr,
          { .case_Inr = res }
        }
      );
  }
  COSE_Format_evercddl_empty_or_serialized_map_pretty
  res2 = COSE_Format_evercddl_empty_or_serialized_map_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_empty_or_serialized_map(
  COSE_Format_evercddl_empty_or_serialized_map_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_empty_or_serialized_map
  c_ = COSE_Format_evercddl_empty_or_serialized_map_pretty_left(c);
  if (c_.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_header_map_pretty c1 = c_.case_Inl;
    size_t sz = COSE_Format_serialize_header_map(c1, out);
    if (sz == (size_t)0U || sz > (size_t)18446744073709551615ULL)
      return (size_t)0U;
    else
    {
      size_t aout_len = len__uint8_t(out);
      uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
      size_t
      res =
        cbor_det_serialize_string_to_array(CBOR_MAJOR_TYPE_BYTE_STRING,
          (uint64_t)sz,
          aout,
          aout_len);
      return res;
    }
  }
  else if (c_.tag == COSE_Format_Inr)
  {
    Pulse_Lib_Slice_slice__uint8_t c2 = c_.case_Inr;
    size_t len = len__uint8_t(c2);
    if ((size_t)0ULL <= len && len <= (size_t)0ULL)
      if (2U == CBOR_MAJOR_TYPE_BYTE_STRING)
      {
        size_t len1 = len__uint8_t(c2);
        if (len1 <= (size_t)18446744073709551615ULL)
        {
          uint8_t *a = slice_to_arrayptr_intro__uint8_t(c2);
          uint8_t *a0 = a;
          cbor_det_t
          res =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_BYTE_STRING,
              a0,
              (uint64_t)len__uint8_t(c2));
          cbor_det_t x = res;
          size_t slen = len__uint8_t(out);
          size_t len2 = cbor_det_size(x, slen);
          option__size_t ser;
          if (len2 > (size_t)0U)
          {
            uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
            size_t len_ = cbor_det_serialize(x, out1, len2);
            ser = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
          }
          else
            ser = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
          if (ser.tag == FStar_Pervasives_Native_None)
            return (size_t)0U;
          else if (ser.tag == FStar_Pervasives_Native_Some)
            return ser.v;
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
      {
        size_t len1 = len__uint8_t(c2);
        if (len1 <= (size_t)18446744073709551615ULL)
        {
          size_t alen = len__uint8_t(c2);
          uint8_t *a = slice_to_arrayptr_intro__uint8_t(c2);
          bool res = cbor_det_impl_utf8_correct_from_array(a, alen);
          bool correct = res;
          if (correct)
          {
            uint8_t *a = slice_to_arrayptr_intro__uint8_t(c2);
            uint8_t *a0 = a;
            cbor_det_t
            res =
              cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
                a0,
                (uint64_t)len__uint8_t(c2));
            cbor_det_t x = res;
            size_t slen = len__uint8_t(out);
            size_t len2 = cbor_det_size(x, slen);
            option__size_t ser;
            if (len2 > (size_t)0U)
            {
              uint8_t *out1 = slice_to_arrayptr_intro__uint8_t(out);
              size_t len_ = cbor_det_serialize(x, out1, len2);
              ser = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
            }
            else
              ser = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
            if (ser.tag == FStar_Pervasives_Native_None)
              return (size_t)0U;
            else if (ser.tag == FStar_Pervasives_Native_Some)
              return ser.v;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_empty_or_serialized_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_empty_or_serialized_map(rl);
    if (test)
    {
      COSE_Format_evercddl_empty_or_serialized_map_pretty
      x = COSE_Format_parse_empty_or_serialized_map(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_empty_or_serialized_map_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t ty = cbor_det_major_type(c);
  if (ty == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_det_array_iterator_t i = cbor_det_array_iterator_start(c);
    cbor_det_array_iterator_t pi = i;
    cbor_det_array_iterator_t i10 = pi;
    bool is_done = cbor_det_array_iterator_is_empty(i10);
    bool test10;
    if (is_done)
      test10 = false;
    else
    {
      cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
      bool test = COSE_Format_validate_empty_or_serialized_map(c1);
      test10 = test;
    }
    bool test1;
    if (test10)
    {
      cbor_det_array_iterator_t i1 = pi;
      bool is_done = cbor_det_array_iterator_is_empty(i1);
      bool test2;
      if (is_done)
        test2 = false;
      else
      {
        cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
        bool test = COSE_Format_validate_header_map(c1);
        test2 = test;
      }
      test1 = test2;
    }
    else
      test1 = false;
    bool b_success;
    if (test1)
    {
      cbor_det_array_iterator_t i1 = pi;
      bool is_done = cbor_det_array_iterator_is_empty(i1);
      bool test2;
      if (is_done)
        test2 = false;
      else
      {
        cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
        bool test = COSE_Format_validate_bstr(c1);
        test2 = test;
      }
      b_success = test2;
    }
    else
      b_success = false;
    if (b_success)
    {
      cbor_det_array_iterator_t i_ = pi;
      bool b_end = cbor_det_array_iterator_is_empty(i_);
      return b_end;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Signature_pretty0(
  COSE_Format_evercddl_COSE_Signature_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_COSE_Signature_pretty
COSE_Format_evercddl_COSE_Signature_pretty_right(COSE_Format_evercddl_COSE_Signature x3)
{
  COSE_Format_evercddl_bstr x6 = x3.snd;
  COSE_Format_evercddl_header_map_pretty x5 = x3.fst.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x4 = x3.fst.fst;
  return ((COSE_Format_evercddl_COSE_Signature_pretty){ .x0 = x4, .x1 = x5, .x2 = x6 });
}

COSE_Format_evercddl_COSE_Signature
COSE_Format_evercddl_COSE_Signature_pretty_left(COSE_Format_evercddl_COSE_Signature_pretty x7)
{
  COSE_Format_evercddl_empty_or_serialized_map_pretty x12 = x7.x0;
  COSE_Format_evercddl_header_map_pretty x13 = x7.x1;
  COSE_Format_evercddl_bstr x14 = x7.x2;
  return
    ((COSE_Format_evercddl_COSE_Signature){ .fst = { .fst = x12, .snd = x13 }, .snd = x14 });
}

COSE_Format_evercddl_COSE_Signature_pretty COSE_Format_parse_COSE_Signature(cbor_det_t c)
{
  cbor_det_array_iterator_t ar = cbor_det_array_iterator_start(c);
  uint64_t rlen0 = cbor_det_array_iterator_length(ar);
  cbor_det_array_iterator_t pc = ar;
  cbor_det_array_iterator_t i0 = pc;
  bool is_done = cbor_det_array_iterator_is_empty(i0);
  bool test1;
  if (is_done)
    test1 = false;
  else
  {
    cbor_det_t c1 = cbor_det_array_iterator_next(&pc);
    bool test = COSE_Format_validate_empty_or_serialized_map(c1);
    test1 = test;
  }
  bool _tmp;
  if (test1)
  {
    cbor_det_array_iterator_t i = pc;
    bool is_done = cbor_det_array_iterator_is_empty(i);
    bool test2;
    if (is_done)
      test2 = false;
    else
    {
      cbor_det_t c1 = cbor_det_array_iterator_next(&pc);
      bool test = COSE_Format_validate_header_map(c1);
      test2 = test;
    }
    _tmp = test2;
  }
  else
    _tmp = false;
  KRML_MAYBE_UNUSED_VAR(_tmp);
  cbor_det_array_iterator_t c1 = pc;
  uint64_t rlen1 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t c0_ = cbor_det_array_iterator_truncate(ar, rlen0 - rlen1);
  uint64_t rlen01 = cbor_det_array_iterator_length(c0_);
  cbor_det_array_iterator_t pc10 = c0_;
  cbor_det_array_iterator_t i = pc10;
  bool is_done0 = cbor_det_array_iterator_is_empty(i);
  bool _tmp1;
  if (is_done0)
    _tmp1 = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc10);
    bool test = COSE_Format_validate_empty_or_serialized_map(c2);
    _tmp1 = test;
  }
  KRML_MAYBE_UNUSED_VAR(_tmp1);
  cbor_det_array_iterator_t c11 = pc10;
  uint64_t rlen11 = cbor_det_array_iterator_length(c11);
  cbor_det_array_iterator_t c0_1 = cbor_det_array_iterator_truncate(c0_, rlen01 - rlen11);
  cbor_det_array_iterator_t pc20 = c0_1;
  cbor_det_t x = cbor_det_array_iterator_next(&pc20);
  COSE_Format_evercddl_empty_or_serialized_map_pretty
  res = COSE_Format_parse_empty_or_serialized_map(x);
  COSE_Format_evercddl_empty_or_serialized_map_pretty w1 = res;
  cbor_det_array_iterator_t pc2 = c11;
  cbor_det_t x0 = cbor_det_array_iterator_next(&pc2);
  COSE_Format_evercddl_header_map_pretty res0 = COSE_Format_parse_header_map(x0);
  COSE_Format_evercddl_header_map_pretty w2 = res0;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  w10 = { .fst = w1, .snd = w2 };
  cbor_det_array_iterator_t pc1 = c1;
  cbor_det_t x1 = cbor_det_array_iterator_next(&pc1);
  COSE_Format_evercddl_bstr res1 = COSE_Format_parse_bstr(x1);
  COSE_Format_evercddl_bstr w20 = res1;
  COSE_Format_evercddl_COSE_Signature res2 = { .fst = w10, .snd = w20 };
  COSE_Format_evercddl_COSE_Signature res10 = res2;
  COSE_Format_evercddl_COSE_Signature_pretty
  res20 = COSE_Format_evercddl_COSE_Signature_pretty_right(res10);
  return res20;
}

size_t
COSE_Format_serialize_COSE_Signature(
  COSE_Format_evercddl_COSE_Signature_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Signature c_ = COSE_Format_evercddl_COSE_Signature_pretty_left(c);
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_evercddl_COSE_Signature _letpattern = c_;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  c1 = _letpattern.fst;
  COSE_Format_evercddl_bstr c2 = _letpattern.snd;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  _letpattern10 = c1;
  COSE_Format_evercddl_empty_or_serialized_map_pretty c11 = _letpattern10.fst;
  COSE_Format_evercddl_header_map_pretty c21 = _letpattern10.snd;
  uint64_t count0 = pcount;
  bool res10;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern2 = split__uint8_t(out, size);
    Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
    size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c11, out1);
    if (size1 == (size_t)0U)
      res10 = false;
    else
    {
      pcount = count0 + 1ULL;
      psize = size + size1;
      res10 = true;
    }
  }
  else
    res10 = false;
  bool res1;
  if (res10)
  {
    uint64_t count = pcount;
    bool res2;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(out, size);
      Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
      size_t size1 = COSE_Format_serialize_header_map(c21, out1);
      if (size1 == (size_t)0U)
        res2 = false;
      else
      {
        pcount = count + 1ULL;
        psize = size + size1;
        res2 = true;
      }
    }
    else
      res2 = false;
    res1 = res2;
  }
  else
    res1 = false;
  bool res;
  if (res1)
  {
    uint64_t count = pcount;
    bool res2;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern1 = split__uint8_t(out, size);
      Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern1.snd;
      size_t size1 = COSE_Format_serialize_bstr(c2, out1);
      if (size1 == (size_t)0U)
        res2 = false;
      else
      {
        pcount = count + 1ULL;
        psize = size + size1;
        res2 = true;
      }
    }
    else
      res2 = false;
    res = res2;
  }
  else
    res = false;
  size_t _bind_c;
  if (res)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = len__uint8_t(out);
    uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
    size_t res1 = cbor_det_serialize_array_to_array(count, aout, aout_len, size);
    _bind_c = res1;
  }
  else
    _bind_c = (size_t)0U;
  size_t res0 = _bind_c;
  return res0;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Signature_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Signature(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Signature_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Signature(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Signature_pretty x = COSE_Format_parse_COSE_Signature(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Signature_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_aux_env31_validate_1(cbor_det_array_iterator_t *pi)
{
  cbor_det_array_iterator_t i = *pi;
  bool is_done = cbor_det_array_iterator_is_empty(i);
  if (is_done)
    return false;
  else
  {
    cbor_det_t c = cbor_det_array_iterator_next(pi);
    bool test = COSE_Format_validate_COSE_Signature(c);
    return test;
  }
}

bool
COSE_Format_uu___is_Mkaux_env31_type_1_pretty0(
  COSE_Format_evercddl_COSE_Signature_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_COSE_Signature_pretty
COSE_Format_aux_env31_type_1_pretty_right(COSE_Format_evercddl_COSE_Signature_pretty x1)
{
  return x1;
}

COSE_Format_evercddl_COSE_Signature_pretty
COSE_Format_aux_env31_type_1_pretty_left(COSE_Format_evercddl_COSE_Signature_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_COSE_Signature_pretty
COSE_Format_aux_env31_parse_1(cbor_det_array_iterator_t c)
{
  cbor_det_array_iterator_t pc = c;
  cbor_det_t x = cbor_det_array_iterator_next(&pc);
  COSE_Format_evercddl_COSE_Signature_pretty res = COSE_Format_parse_COSE_Signature(x);
  return res;
}

bool
COSE_Format_aux_env31_serialize_1(
  COSE_Format_evercddl_COSE_Signature_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out,
  uint64_t *out_count,
  size_t *out_size
)
{
  uint64_t count = *out_count;
  if (count < 18446744073709551615ULL)
  {
    size_t size = *out_size;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = split__uint8_t(out, size);
    Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern.snd;
    size_t size1 = COSE_Format_serialize_COSE_Signature(c, out1);
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
  uint8_t ty = cbor_det_major_type(c);
  if (ty == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_det_array_iterator_t i = cbor_det_array_iterator_start(c);
    cbor_det_array_iterator_t pi = i;
    cbor_det_array_iterator_t i10 = pi;
    bool is_done = cbor_det_array_iterator_is_empty(i10);
    bool test10;
    if (is_done)
      test10 = false;
    else
    {
      cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
      bool test = COSE_Format_validate_empty_or_serialized_map(c1);
      test10 = test;
    }
    bool test1;
    if (test10)
    {
      cbor_det_array_iterator_t i1 = pi;
      bool is_done = cbor_det_array_iterator_is_empty(i1);
      bool test2;
      if (is_done)
        test2 = false;
      else
      {
        cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
        bool test = COSE_Format_validate_header_map(c1);
        test2 = test;
      }
      test1 = test2;
    }
    else
      test1 = false;
    bool b_success0;
    if (test1)
    {
      cbor_det_array_iterator_t i10 = pi;
      bool is_done = cbor_det_array_iterator_is_empty(i10);
      bool test11;
      if (is_done)
        test11 = false;
      else
      {
        cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
        bool test0 = COSE_Format_validate_bstr(c1);
        bool test;
        if (test0)
          test = true;
        else
          test = COSE_Format_validate_nil(c1);
        test11 = test;
      }
      bool test20;
      if (test11)
      {
        cbor_det_array_iterator_t i1 = pi;
        bool is_done = cbor_det_array_iterator_is_empty(i1);
        bool test2;
        if (is_done)
          test2 = false;
        else
        {
          cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
          uint8_t ty1 = cbor_det_major_type(c1);
          bool test;
          if (ty1 == CBOR_MAJOR_TYPE_ARRAY)
          {
            cbor_det_array_iterator_t i2 = cbor_det_array_iterator_start(c1);
            cbor_det_array_iterator_t pi1 = i2;
            cbor_det_array_iterator_t i30 = pi1;
            bool is_done1 = cbor_det_array_iterator_is_empty(i30);
            bool test12;
            if (is_done1)
              test12 = false;
            else
            {
              cbor_det_t c2 = cbor_det_array_iterator_next(&pi1);
              bool test = COSE_Format_validate_COSE_Signature(c2);
              test12 = test;
            }
            bool b_success;
            if (test12)
            {
              bool pcont = true;
              while (pcont)
              {
                cbor_det_array_iterator_t i11 = pi1;
                cbor_det_array_iterator_t i3 = pi1;
                bool is_done1 = cbor_det_array_iterator_is_empty(i3);
                bool cont;
                if (is_done1)
                  cont = false;
                else
                {
                  cbor_det_t c2 = cbor_det_array_iterator_next(&pi1);
                  bool test = COSE_Format_validate_COSE_Signature(c2);
                  cont = test;
                }
                if (!cont)
                {
                  pi1 = i11;
                  pcont = false;
                }
              }
              bool test2 = true;
              b_success = test2;
            }
            else
              b_success = false;
            bool _bind_c;
            if (b_success)
            {
              cbor_det_array_iterator_t i_ = pi1;
              bool b_end = cbor_det_array_iterator_is_empty(i_);
              _bind_c = b_end;
            }
            else
              _bind_c = false;
            test = _bind_c;
          }
          else
            test = false;
          test2 = test;
        }
        test20 = test2;
      }
      else
        test20 = false;
      b_success0 = test20;
    }
    else
      b_success0 = false;
    if (b_success0)
    {
      cbor_det_array_iterator_t i_ = pi;
      bool b_end = cbor_det_array_iterator_is_empty(i_);
      return b_end;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Sign_pretty0(
  COSE_Format_evercddl_COSE_Sign_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_COSE_Sign_pretty
COSE_Format_evercddl_COSE_Sign_pretty_right(COSE_Format_evercddl_COSE_Sign x4)
{
  FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_COSE_Signature_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
  x8 = x4.snd.snd;
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  x7 = x4.snd.fst;
  COSE_Format_evercddl_header_map_pretty x6 = x4.fst.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x5 = x4.fst.fst;
  return ((COSE_Format_evercddl_COSE_Sign_pretty){ .x0 = x5, .x1 = x6, .x2 = x7, .x3 = x8 });
}

COSE_Format_evercddl_COSE_Sign
COSE_Format_evercddl_COSE_Sign_pretty_left(COSE_Format_evercddl_COSE_Sign_pretty x9)
{
  COSE_Format_evercddl_empty_or_serialized_map_pretty x15 = x9.x0;
  COSE_Format_evercddl_header_map_pretty x16 = x9.x1;
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  x17 = x9.x2;
  FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_COSE_Signature_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
  x18 = x9.x3;
  return
    (
      (COSE_Format_evercddl_COSE_Sign){
        .fst = { .fst = x15, .snd = x16 },
        .snd = { .fst = x17, .snd = x18 }
      }
    );
}

COSE_Format_evercddl_COSE_Sign_pretty COSE_Format_parse_COSE_Sign(cbor_det_t c)
{
  cbor_det_array_iterator_t ar = cbor_det_array_iterator_start(c);
  uint64_t rlen0 = cbor_det_array_iterator_length(ar);
  cbor_det_array_iterator_t pc = ar;
  cbor_det_array_iterator_t i0 = pc;
  bool is_done = cbor_det_array_iterator_is_empty(i0);
  bool test1;
  if (is_done)
    test1 = false;
  else
  {
    cbor_det_t c1 = cbor_det_array_iterator_next(&pc);
    bool test = COSE_Format_validate_empty_or_serialized_map(c1);
    test1 = test;
  }
  bool _tmp;
  if (test1)
  {
    cbor_det_array_iterator_t i = pc;
    bool is_done = cbor_det_array_iterator_is_empty(i);
    bool test2;
    if (is_done)
      test2 = false;
    else
    {
      cbor_det_t c1 = cbor_det_array_iterator_next(&pc);
      bool test = COSE_Format_validate_header_map(c1);
      test2 = test;
    }
    _tmp = test2;
  }
  else
    _tmp = false;
  KRML_MAYBE_UNUSED_VAR(_tmp);
  cbor_det_array_iterator_t c1 = pc;
  uint64_t rlen1 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t c0_ = cbor_det_array_iterator_truncate(ar, rlen0 - rlen1);
  uint64_t rlen010 = cbor_det_array_iterator_length(c0_);
  cbor_det_array_iterator_t pc10 = c0_;
  cbor_det_array_iterator_t i1 = pc10;
  bool is_done0 = cbor_det_array_iterator_is_empty(i1);
  bool _tmp10;
  if (is_done0)
    _tmp10 = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc10);
    bool test = COSE_Format_validate_empty_or_serialized_map(c2);
    _tmp10 = test;
  }
  KRML_MAYBE_UNUSED_VAR(_tmp10);
  cbor_det_array_iterator_t c11 = pc10;
  uint64_t rlen110 = cbor_det_array_iterator_length(c11);
  cbor_det_array_iterator_t c0_1 = cbor_det_array_iterator_truncate(c0_, rlen010 - rlen110);
  cbor_det_array_iterator_t pc20 = c0_1;
  cbor_det_t x = cbor_det_array_iterator_next(&pc20);
  COSE_Format_evercddl_empty_or_serialized_map_pretty
  res0 = COSE_Format_parse_empty_or_serialized_map(x);
  COSE_Format_evercddl_empty_or_serialized_map_pretty w1 = res0;
  cbor_det_array_iterator_t pc21 = c11;
  cbor_det_t x0 = cbor_det_array_iterator_next(&pc21);
  COSE_Format_evercddl_header_map_pretty res1 = COSE_Format_parse_header_map(x0);
  COSE_Format_evercddl_header_map_pretty w2 = res1;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  w10 = { .fst = w1, .snd = w2 };
  uint64_t rlen01 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t pc1 = c1;
  cbor_det_array_iterator_t i = pc1;
  bool is_done1 = cbor_det_array_iterator_is_empty(i);
  bool _tmp1;
  if (is_done1)
    _tmp1 = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc1);
    bool test0 = COSE_Format_validate_bstr(c2);
    bool test;
    if (test0)
      test = true;
    else
      test = COSE_Format_validate_nil(c2);
    _tmp1 = test;
  }
  KRML_MAYBE_UNUSED_VAR(_tmp1);
  cbor_det_array_iterator_t c110 = pc1;
  uint64_t rlen11 = cbor_det_array_iterator_length(c110);
  cbor_det_array_iterator_t c0_10 = cbor_det_array_iterator_truncate(c1, rlen01 - rlen11);
  cbor_det_array_iterator_t pc22 = c0_10;
  cbor_det_t x1 = cbor_det_array_iterator_next(&pc22);
  bool test = COSE_Format_validate_bstr(x1);
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty res2;
  if (test)
  {
    COSE_Format_evercddl_bstr res = COSE_Format_parse_bstr(x1);
    res2 =
      (
        (FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty){
          .tag = COSE_Format_Inl,
          { .case_Inl = res }
        }
      );
  }
  else
  {
    COSE_Format_evercddl_nil_pretty res = COSE_Format_parse_nil(x1);
    res2 =
      (
        (FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty){
          .tag = COSE_Format_Inr,
          { .case_Inr = res }
        }
      );
  }
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  w11 = res2;
  cbor_det_array_iterator_t pc2 = c110;
  cbor_det_t x2 = cbor_det_array_iterator_next(&pc2);
  cbor_det_array_iterator_t ar1 = cbor_det_array_iterator_start(x2);
  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
  i2 =
    {
      .cddl_array_iterator_contents = ar1,
      .cddl_array_iterator_impl_validate = COSE_Format_aux_env31_validate_1,
      .cddl_array_iterator_impl_parse = COSE_Format_aux_env31_parse_1
    };
  FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_COSE_Signature_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
  res = { .tag = COSE_Format_Inr, { .case_Inr = i2 } };
  FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_COSE_Signature_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
  w20 = res;
  K___FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_COSE_Signature_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
  w21 = { .fst = w11, .snd = w20 };
  COSE_Format_evercddl_COSE_Sign res3 = { .fst = w10, .snd = w21 };
  COSE_Format_evercddl_COSE_Sign res10 = res3;
  COSE_Format_evercddl_COSE_Sign_pretty
  res20 = COSE_Format_evercddl_COSE_Sign_pretty_right(res10);
  return res20;
}

static size_t
len__COSE_Format_evercddl_COSE_Signature_pretty(
  Pulse_Lib_Slice_slice__COSE_Format_evercddl_COSE_Signature_pretty s
)
{
  return s.len;
}

static COSE_Format_evercddl_COSE_Signature_pretty
op_Array_Access__COSE_Format_evercddl_COSE_Signature_pretty(
  Pulse_Lib_Slice_slice__COSE_Format_evercddl_COSE_Signature_pretty a,
  size_t i
)
{
  return a.elt[i];
}

size_t
COSE_Format_serialize_COSE_Sign(
  COSE_Format_evercddl_COSE_Sign_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Sign c_ = COSE_Format_evercddl_COSE_Sign_pretty_left(c);
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_evercddl_COSE_Sign _letpattern = c_;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  c1 = _letpattern.fst;
  K___FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_COSE_Signature_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
  c2 = _letpattern.snd;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  _letpattern10 = c1;
  COSE_Format_evercddl_empty_or_serialized_map_pretty c110 = _letpattern10.fst;
  COSE_Format_evercddl_header_map_pretty c210 = _letpattern10.snd;
  uint64_t count0 = pcount;
  bool res10;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern2 = split__uint8_t(out, size);
    Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
    size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c110, out1);
    if (size1 == (size_t)0U)
      res10 = false;
    else
    {
      pcount = count0 + 1ULL;
      psize = size + size1;
      res10 = true;
    }
  }
  else
    res10 = false;
  bool res1;
  if (res10)
  {
    uint64_t count = pcount;
    bool res2;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(out, size);
      Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
      size_t size1 = COSE_Format_serialize_header_map(c210, out1);
      if (size1 == (size_t)0U)
        res2 = false;
      else
      {
        pcount = count + 1ULL;
        psize = size + size1;
        res2 = true;
      }
    }
    else
      res2 = false;
    res1 = res2;
  }
  else
    res1 = false;
  bool res0;
  if (res1)
  {
    K___FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_FStar_Pervasives_either_CDDL_Pulse_Types_slice_COSE_Format_evercddl_COSE_Signature_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
    _letpattern1 = c2;
    FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
    c11 = _letpattern1.fst;
    FStar_Pervasives_either__CDDL_Pulse_Types_slice_COSE_Format_evercddl_COSE_Signature_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
    c21 = _letpattern1.snd;
    uint64_t count0 = pcount;
    bool res11;
    if (count0 < 18446744073709551615ULL)
    {
      size_t size = psize;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(out, size);
      Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
      size_t size1;
      if (c11.tag == COSE_Format_Inl)
      {
        COSE_Format_evercddl_bstr c12 = c11.case_Inl;
        size_t res = COSE_Format_serialize_bstr(c12, out1);
        size1 = res;
      }
      else if (c11.tag == COSE_Format_Inr)
      {
        COSE_Format_evercddl_nil_pretty c22 = c11.case_Inr;
        size_t res = COSE_Format_serialize_nil(c22, out1);
        size1 = res;
      }
      else
        size1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (size1 == (size_t)0U)
        res11 = false;
      else
      {
        pcount = count0 + 1ULL;
        psize = size + size1;
        res11 = true;
      }
    }
    else
      res11 = false;
    bool res20;
    if (res11)
    {
      uint64_t count = pcount;
      bool res2;
      if (count < 18446744073709551615ULL)
      {
        size_t size = psize;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern2 = split__uint8_t(out, size);
        Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
        uint64_t pcount1 = 0ULL;
        size_t psize1 = (size_t)0U;
        bool res0;
        if (c21.tag == COSE_Format_Inl)
        {
          Pulse_Lib_Slice_slice__COSE_Format_evercddl_COSE_Signature_pretty c12 = c21.case_Inl;
          bool res1;
          if (len__COSE_Format_evercddl_COSE_Signature_pretty(c12) == (size_t)0U)
            res1 = false;
          else
          {
            bool pres = true;
            size_t pi = (size_t)0U;
            size_t slen = len__COSE_Format_evercddl_COSE_Signature_pretty(c12);
            bool res = pres;
            bool cond;
            if (res)
            {
              size_t i = pi;
              cond = i < slen;
            }
            else
              cond = false;
            while (cond)
            {
              size_t i0 = pi;
              COSE_Format_evercddl_COSE_Signature_pretty
              x = op_Array_Access__COSE_Format_evercddl_COSE_Signature_pretty(c12, i0);
              bool res = COSE_Format_aux_env31_serialize_1(x, out1, &pcount1, &psize1);
              if (res)
              {
                size_t i_ = i0 + (size_t)1U;
                pi = i_;
              }
              else
                pres = false;
              bool res0 = pres;
              bool ite;
              if (res0)
              {
                size_t i = pi;
                ite = i < slen;
              }
              else
                ite = false;
              cond = ite;
            }
            res1 = pres;
          }
          res0 = res1;
        }
        else if (c21.tag == COSE_Format_Inr)
        {
          CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
          c22 = c21.case_Inr;
          bool res1 = cbor_det_array_iterator_is_empty(c22.cddl_array_iterator_contents);
          bool em = res1;
          bool res2;
          if (em)
            res2 = false;
          else
          {
            CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
            pc = c22;
            bool pres = true;
            bool res = pres;
            bool cond;
            if (res)
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
              c3 = pc;
              bool res2 = cbor_det_array_iterator_is_empty(c3.cddl_array_iterator_contents);
              bool em1 = res2;
              cond = !em1;
            }
            else
              cond = false;
            while (cond)
            {
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
              i = pc;
              uint64_t len0 = cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
              cbor_det_array_iterator_t pj = i.cddl_array_iterator_contents;
              bool _test = i.cddl_array_iterator_impl_validate(&pj);
              KRML_MAYBE_UNUSED_VAR(_test);
              cbor_det_array_iterator_t ji = pj;
              uint64_t len1 = cbor_det_array_iterator_length(ji);
              CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
              j =
                {
                  .cddl_array_iterator_contents = ji,
                  .cddl_array_iterator_impl_validate = i.cddl_array_iterator_impl_validate,
                  .cddl_array_iterator_impl_parse = i.cddl_array_iterator_impl_parse
                };
              pc = j;
              cbor_det_array_iterator_t
              tri = cbor_det_array_iterator_truncate(i.cddl_array_iterator_contents, len0 - len1);
              COSE_Format_evercddl_COSE_Signature_pretty
              res = i.cddl_array_iterator_impl_parse(tri);
              COSE_Format_evercddl_COSE_Signature_pretty x = res;
              bool res0 = COSE_Format_aux_env31_serialize_1(x, out1, &pcount1, &psize1);
              if (!res0)
                pres = false;
              bool res1 = pres;
              bool ite;
              if (res1)
              {
                CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_COSE_Format_evercddl_COSE_Signature_pretty
                c3 = pc;
                bool res2 = cbor_det_array_iterator_is_empty(c3.cddl_array_iterator_contents);
                bool em1 = res2;
                ite = !em1;
              }
              else
                ite = false;
              cond = ite;
            }
            res2 = pres;
          }
          res0 = res2;
        }
        else
          res0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
        size_t _bind_c;
        if (res0)
        {
          size_t size1 = psize1;
          uint64_t count1 = pcount1;
          size_t aout_len = len__uint8_t(out1);
          uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out1);
          size_t res2 = cbor_det_serialize_array_to_array(count1, aout, aout_len, size1);
          _bind_c = res2;
        }
        else
          _bind_c = (size_t)0U;
        size_t size1 = _bind_c;
        if (size1 == (size_t)0U)
          res2 = false;
        else
        {
          pcount = count + 1ULL;
          psize = size + size1;
          res2 = true;
        }
      }
      else
        res2 = false;
      res20 = res2;
    }
    else
      res20 = false;
    res0 = res20;
  }
  else
    res0 = false;
  size_t _bind_c;
  if (res0)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = len__uint8_t(out);
    uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
    size_t res1 = cbor_det_serialize_array_to_array(count, aout, aout_len, size);
    _bind_c = res1;
  }
  else
    _bind_c = (size_t)0U;
  size_t res = _bind_c;
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Sign(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Sign(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Sign_pretty x = COSE_Format_parse_COSE_Sign(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (98ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_COSE_Sign(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Sign_Tagged_pretty0(
  COSE_Format_evercddl_COSE_Sign_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_COSE_Sign_pretty
COSE_Format_evercddl_COSE_Sign_Tagged_pretty_right(COSE_Format_evercddl_COSE_Sign_pretty x1)
{
  return x1;
}

COSE_Format_evercddl_COSE_Sign_pretty
COSE_Format_evercddl_COSE_Sign_Tagged_pretty_left(COSE_Format_evercddl_COSE_Sign_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_COSE_Sign_pretty COSE_Format_parse_COSE_Sign_Tagged(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_COSE_Sign_pretty res = COSE_Format_parse_COSE_Sign(cpl);
  COSE_Format_evercddl_COSE_Sign_pretty res1 = res;
  COSE_Format_evercddl_COSE_Sign_pretty
  res2 = COSE_Format_evercddl_COSE_Sign_Tagged_pretty_right(res1);
  return res2;
}

typedef struct __uint64_t_COSE_Format_evercddl_COSE_Sign_pretty_s
{
  uint64_t fst;
  COSE_Format_evercddl_COSE_Sign_pretty snd;
}
__uint64_t_COSE_Format_evercddl_COSE_Sign_pretty;

size_t
COSE_Format_serialize_COSE_Sign_Tagged(
  COSE_Format_evercddl_COSE_Sign_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Sign_pretty
  c_ = COSE_Format_evercddl_COSE_Sign_Tagged_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_COSE_Sign_pretty c_1 = { .fst = 98ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_COSE_Sign_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_COSE_Sign_pretty cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_COSE_Sign(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Sign_Tagged(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Sign_Tagged(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Sign_pretty x = COSE_Format_parse_COSE_Sign_Tagged(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t ty = cbor_det_major_type(c);
  if (ty == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_det_array_iterator_t i = cbor_det_array_iterator_start(c);
    cbor_det_array_iterator_t pi = i;
    cbor_det_array_iterator_t i10 = pi;
    bool is_done = cbor_det_array_iterator_is_empty(i10);
    bool test10;
    if (is_done)
      test10 = false;
    else
    {
      cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
      bool test = COSE_Format_validate_empty_or_serialized_map(c1);
      test10 = test;
    }
    bool test1;
    if (test10)
    {
      cbor_det_array_iterator_t i1 = pi;
      bool is_done = cbor_det_array_iterator_is_empty(i1);
      bool test2;
      if (is_done)
        test2 = false;
      else
      {
        cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
        bool test = COSE_Format_validate_header_map(c1);
        test2 = test;
      }
      test1 = test2;
    }
    else
      test1 = false;
    bool b_success;
    if (test1)
    {
      cbor_det_array_iterator_t i10 = pi;
      bool is_done = cbor_det_array_iterator_is_empty(i10);
      bool test11;
      if (is_done)
        test11 = false;
      else
      {
        cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
        bool test0 = COSE_Format_validate_bstr(c1);
        bool test;
        if (test0)
          test = true;
        else
          test = COSE_Format_validate_nil(c1);
        test11 = test;
      }
      bool test20;
      if (test11)
      {
        cbor_det_array_iterator_t i1 = pi;
        bool is_done = cbor_det_array_iterator_is_empty(i1);
        bool test2;
        if (is_done)
          test2 = false;
        else
        {
          cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
          bool test = COSE_Format_validate_bstr(c1);
          test2 = test;
        }
        test20 = test2;
      }
      else
        test20 = false;
      b_success = test20;
    }
    else
      b_success = false;
    if (b_success)
    {
      cbor_det_array_iterator_t i_ = pi;
      bool b_end = cbor_det_array_iterator_is_empty(i_);
      return b_end;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Sign1_pretty0(
  COSE_Format_evercddl_COSE_Sign1_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_COSE_Sign1_pretty
COSE_Format_evercddl_COSE_Sign1_pretty_right(COSE_Format_evercddl_COSE_Sign1 x4)
{
  COSE_Format_evercddl_bstr x8 = x4.snd.snd;
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  x7 = x4.snd.fst;
  COSE_Format_evercddl_header_map_pretty x6 = x4.fst.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x5 = x4.fst.fst;
  return ((COSE_Format_evercddl_COSE_Sign1_pretty){ .x0 = x5, .x1 = x6, .x2 = x7, .x3 = x8 });
}

COSE_Format_evercddl_COSE_Sign1
COSE_Format_evercddl_COSE_Sign1_pretty_left(COSE_Format_evercddl_COSE_Sign1_pretty x9)
{
  COSE_Format_evercddl_empty_or_serialized_map_pretty x15 = x9.x0;
  COSE_Format_evercddl_header_map_pretty x16 = x9.x1;
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  x17 = x9.x2;
  COSE_Format_evercddl_bstr x18 = x9.x3;
  return
    (
      (COSE_Format_evercddl_COSE_Sign1){
        .fst = { .fst = x15, .snd = x16 },
        .snd = { .fst = x17, .snd = x18 }
      }
    );
}

COSE_Format_evercddl_COSE_Sign1_pretty COSE_Format_parse_COSE_Sign1(cbor_det_t c)
{
  cbor_det_array_iterator_t ar = cbor_det_array_iterator_start(c);
  uint64_t rlen0 = cbor_det_array_iterator_length(ar);
  cbor_det_array_iterator_t pc = ar;
  cbor_det_array_iterator_t i0 = pc;
  bool is_done = cbor_det_array_iterator_is_empty(i0);
  bool test1;
  if (is_done)
    test1 = false;
  else
  {
    cbor_det_t c1 = cbor_det_array_iterator_next(&pc);
    bool test = COSE_Format_validate_empty_or_serialized_map(c1);
    test1 = test;
  }
  bool _tmp;
  if (test1)
  {
    cbor_det_array_iterator_t i = pc;
    bool is_done = cbor_det_array_iterator_is_empty(i);
    bool test2;
    if (is_done)
      test2 = false;
    else
    {
      cbor_det_t c1 = cbor_det_array_iterator_next(&pc);
      bool test = COSE_Format_validate_header_map(c1);
      test2 = test;
    }
    _tmp = test2;
  }
  else
    _tmp = false;
  KRML_MAYBE_UNUSED_VAR(_tmp);
  cbor_det_array_iterator_t c1 = pc;
  uint64_t rlen1 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t c0_ = cbor_det_array_iterator_truncate(ar, rlen0 - rlen1);
  uint64_t rlen010 = cbor_det_array_iterator_length(c0_);
  cbor_det_array_iterator_t pc10 = c0_;
  cbor_det_array_iterator_t i1 = pc10;
  bool is_done0 = cbor_det_array_iterator_is_empty(i1);
  bool _tmp10;
  if (is_done0)
    _tmp10 = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc10);
    bool test = COSE_Format_validate_empty_or_serialized_map(c2);
    _tmp10 = test;
  }
  KRML_MAYBE_UNUSED_VAR(_tmp10);
  cbor_det_array_iterator_t c11 = pc10;
  uint64_t rlen110 = cbor_det_array_iterator_length(c11);
  cbor_det_array_iterator_t c0_1 = cbor_det_array_iterator_truncate(c0_, rlen010 - rlen110);
  cbor_det_array_iterator_t pc20 = c0_1;
  cbor_det_t x = cbor_det_array_iterator_next(&pc20);
  COSE_Format_evercddl_empty_or_serialized_map_pretty
  res0 = COSE_Format_parse_empty_or_serialized_map(x);
  COSE_Format_evercddl_empty_or_serialized_map_pretty w1 = res0;
  cbor_det_array_iterator_t pc21 = c11;
  cbor_det_t x0 = cbor_det_array_iterator_next(&pc21);
  COSE_Format_evercddl_header_map_pretty res1 = COSE_Format_parse_header_map(x0);
  COSE_Format_evercddl_header_map_pretty w2 = res1;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  w10 = { .fst = w1, .snd = w2 };
  uint64_t rlen01 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t pc1 = c1;
  cbor_det_array_iterator_t i = pc1;
  bool is_done1 = cbor_det_array_iterator_is_empty(i);
  bool _tmp1;
  if (is_done1)
    _tmp1 = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc1);
    bool test0 = COSE_Format_validate_bstr(c2);
    bool test;
    if (test0)
      test = true;
    else
      test = COSE_Format_validate_nil(c2);
    _tmp1 = test;
  }
  KRML_MAYBE_UNUSED_VAR(_tmp1);
  cbor_det_array_iterator_t c110 = pc1;
  uint64_t rlen11 = cbor_det_array_iterator_length(c110);
  cbor_det_array_iterator_t c0_10 = cbor_det_array_iterator_truncate(c1, rlen01 - rlen11);
  cbor_det_array_iterator_t pc22 = c0_10;
  cbor_det_t x1 = cbor_det_array_iterator_next(&pc22);
  bool test = COSE_Format_validate_bstr(x1);
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty res2;
  if (test)
  {
    COSE_Format_evercddl_bstr res = COSE_Format_parse_bstr(x1);
    res2 =
      (
        (FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty){
          .tag = COSE_Format_Inl,
          { .case_Inl = res }
        }
      );
  }
  else
  {
    COSE_Format_evercddl_nil_pretty res = COSE_Format_parse_nil(x1);
    res2 =
      (
        (FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty){
          .tag = COSE_Format_Inr,
          { .case_Inr = res }
        }
      );
  }
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  w11 = res2;
  cbor_det_array_iterator_t pc2 = c110;
  cbor_det_t x2 = cbor_det_array_iterator_next(&pc2);
  COSE_Format_evercddl_bstr res = COSE_Format_parse_bstr(x2);
  COSE_Format_evercddl_bstr w20 = res;
  K___FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_COSE_Format_evercddl_bstr_pretty
  w21 = { .fst = w11, .snd = w20 };
  COSE_Format_evercddl_COSE_Sign1 res3 = { .fst = w10, .snd = w21 };
  COSE_Format_evercddl_COSE_Sign1 res10 = res3;
  COSE_Format_evercddl_COSE_Sign1_pretty
  res20 = COSE_Format_evercddl_COSE_Sign1_pretty_right(res10);
  return res20;
}

size_t
COSE_Format_serialize_COSE_Sign1(
  COSE_Format_evercddl_COSE_Sign1_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Sign1 c_ = COSE_Format_evercddl_COSE_Sign1_pretty_left(c);
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_evercddl_COSE_Sign1 _letpattern = c_;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  c1 = _letpattern.fst;
  K___FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_COSE_Format_evercddl_bstr_pretty
  c2 = _letpattern.snd;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_COSE_Format_evercddl_header_map_pretty
  _letpattern10 = c1;
  COSE_Format_evercddl_empty_or_serialized_map_pretty c110 = _letpattern10.fst;
  COSE_Format_evercddl_header_map_pretty c210 = _letpattern10.snd;
  uint64_t count0 = pcount;
  bool res10;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern2 = split__uint8_t(out, size);
    Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
    size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c110, out1);
    if (size1 == (size_t)0U)
      res10 = false;
    else
    {
      pcount = count0 + 1ULL;
      psize = size + size1;
      res10 = true;
    }
  }
  else
    res10 = false;
  bool res1;
  if (res10)
  {
    uint64_t count = pcount;
    bool res2;
    if (count < 18446744073709551615ULL)
    {
      size_t size = psize;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(out, size);
      Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
      size_t size1 = COSE_Format_serialize_header_map(c210, out1);
      if (size1 == (size_t)0U)
        res2 = false;
      else
      {
        pcount = count + 1ULL;
        psize = size + size1;
        res2 = true;
      }
    }
    else
      res2 = false;
    res1 = res2;
  }
  else
    res1 = false;
  bool res;
  if (res1)
  {
    K___FStar_Pervasives_either_COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty_COSE_Format_evercddl_bstr_pretty
    _letpattern1 = c2;
    FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
    c11 = _letpattern1.fst;
    COSE_Format_evercddl_bstr c21 = _letpattern1.snd;
    uint64_t count0 = pcount;
    bool res11;
    if (count0 < 18446744073709551615ULL)
    {
      size_t size = psize;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(out, size);
      Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
      size_t size1;
      if (c11.tag == COSE_Format_Inl)
      {
        COSE_Format_evercddl_bstr c12 = c11.case_Inl;
        size_t res = COSE_Format_serialize_bstr(c12, out1);
        size1 = res;
      }
      else if (c11.tag == COSE_Format_Inr)
      {
        COSE_Format_evercddl_nil_pretty c22 = c11.case_Inr;
        size_t res = COSE_Format_serialize_nil(c22, out1);
        size1 = res;
      }
      else
        size1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (size1 == (size_t)0U)
        res11 = false;
      else
      {
        pcount = count0 + 1ULL;
        psize = size + size1;
        res11 = true;
      }
    }
    else
      res11 = false;
    bool res20;
    if (res11)
    {
      uint64_t count = pcount;
      bool res2;
      if (count < 18446744073709551615ULL)
      {
        size_t size = psize;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern2 = split__uint8_t(out, size);
        Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
        size_t size1 = COSE_Format_serialize_bstr(c21, out1);
        if (size1 == (size_t)0U)
          res2 = false;
        else
        {
          pcount = count + 1ULL;
          psize = size + size1;
          res2 = true;
        }
      }
      else
        res2 = false;
      res20 = res2;
    }
    else
      res20 = false;
    res = res20;
  }
  else
    res = false;
  size_t _bind_c;
  if (res)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = len__uint8_t(out);
    uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
    size_t res1 = cbor_det_serialize_array_to_array(count, aout, aout_len, size);
    _bind_c = res1;
  }
  else
    _bind_c = (size_t)0U;
  size_t res0 = _bind_c;
  return res0;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Sign1(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Sign1(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Sign1_pretty x = COSE_Format_parse_COSE_Sign1(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  bool test = COSE_Format_validate_COSE_Sign(c);
  if (test)
    return true;
  else
    return COSE_Format_validate_COSE_Sign1(c);
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Untagged_Message_pretty0(
  COSE_Format_evercddl_COSE_Untagged_Message_pretty projectee
)
{
  if (projectee.tag == COSE_Format_Mkevercddl_COSE_Untagged_Message_pretty0)
    return true;
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Untagged_Message_pretty1(
  COSE_Format_evercddl_COSE_Untagged_Message_pretty projectee
)
{
  if (projectee.tag == COSE_Format_Mkevercddl_COSE_Untagged_Message_pretty1)
    return true;
  else
    return false;
}

COSE_Format_evercddl_COSE_Untagged_Message_pretty
COSE_Format_evercddl_COSE_Untagged_Message_pretty_right(
  COSE_Format_evercddl_COSE_Untagged_Message x2
)
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

COSE_Format_evercddl_COSE_Untagged_Message
COSE_Format_evercddl_COSE_Untagged_Message_pretty_left(
  COSE_Format_evercddl_COSE_Untagged_Message_pretty x7
)
{
  if (x7.tag == COSE_Format_Mkevercddl_COSE_Untagged_Message_pretty0)
  {
    COSE_Format_evercddl_COSE_Sign_pretty x10 = x7.case_Mkevercddl_COSE_Untagged_Message_pretty0;
    return
      ((COSE_Format_evercddl_COSE_Untagged_Message){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_COSE_Untagged_Message_pretty1)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty x12 = x7.case_Mkevercddl_COSE_Untagged_Message_pretty1;
    return
      ((COSE_Format_evercddl_COSE_Untagged_Message){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

COSE_Format_evercddl_COSE_Untagged_Message_pretty
COSE_Format_parse_COSE_Untagged_Message(cbor_det_t c)
{
  bool test = COSE_Format_validate_COSE_Sign(c);
  COSE_Format_evercddl_COSE_Untagged_Message res1;
  if (test)
  {
    COSE_Format_evercddl_COSE_Sign_pretty res = COSE_Format_parse_COSE_Sign(c);
    res1 =
      ((COSE_Format_evercddl_COSE_Untagged_Message){ .tag = COSE_Format_Inl, { .case_Inl = res } });
  }
  else
  {
    COSE_Format_evercddl_COSE_Sign1_pretty res = COSE_Format_parse_COSE_Sign1(c);
    res1 =
      ((COSE_Format_evercddl_COSE_Untagged_Message){ .tag = COSE_Format_Inr, { .case_Inr = res } });
  }
  COSE_Format_evercddl_COSE_Untagged_Message_pretty
  res2 = COSE_Format_evercddl_COSE_Untagged_Message_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_COSE_Untagged_Message(
  COSE_Format_evercddl_COSE_Untagged_Message_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Untagged_Message
  c_ = COSE_Format_evercddl_COSE_Untagged_Message_pretty_left(c);
  if (c_.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Sign_pretty c1 = c_.case_Inl;
    size_t res = COSE_Format_serialize_COSE_Sign(c1, out);
    return res;
  }
  else if (c_.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty c2 = c_.case_Inr;
    size_t res = COSE_Format_serialize_COSE_Sign1(c2, out);
    return res;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Untagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Untagged_Message(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Untagged_Message_pretty
      x = COSE_Format_parse_COSE_Untagged_Message(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Untagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (18ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_COSE_Sign1(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Sign1_Tagged_pretty0(
  COSE_Format_evercddl_COSE_Sign1_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_COSE_Sign1_pretty
COSE_Format_evercddl_COSE_Sign1_Tagged_pretty_right(COSE_Format_evercddl_COSE_Sign1_pretty x1)
{
  return x1;
}

COSE_Format_evercddl_COSE_Sign1_pretty
COSE_Format_evercddl_COSE_Sign1_Tagged_pretty_left(COSE_Format_evercddl_COSE_Sign1_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_COSE_Sign1_pretty COSE_Format_parse_COSE_Sign1_Tagged(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_COSE_Sign1_pretty res = COSE_Format_parse_COSE_Sign1(cpl);
  COSE_Format_evercddl_COSE_Sign1_pretty res1 = res;
  COSE_Format_evercddl_COSE_Sign1_pretty
  res2 = COSE_Format_evercddl_COSE_Sign1_Tagged_pretty_right(res1);
  return res2;
}

typedef struct __uint64_t_COSE_Format_evercddl_COSE_Sign1_pretty_s
{
  uint64_t fst;
  COSE_Format_evercddl_COSE_Sign1_pretty snd;
}
__uint64_t_COSE_Format_evercddl_COSE_Sign1_pretty;

size_t
COSE_Format_serialize_COSE_Sign1_Tagged(
  COSE_Format_evercddl_COSE_Sign1_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Sign1_pretty
  c_ = COSE_Format_evercddl_COSE_Sign1_Tagged_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_COSE_Sign1_pretty c_1 = { .fst = 18ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_COSE_Sign1_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_COSE_Sign1_pretty cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_COSE_Sign1(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_COSE_Sign1_Tagged(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Sign1_Tagged(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Sign1_pretty x = COSE_Format_parse_COSE_Sign1_Tagged(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  bool test = COSE_Format_validate_COSE_Sign_Tagged(c);
  if (test)
    return true;
  else
    return COSE_Format_validate_COSE_Sign1_Tagged(c);
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Tagged_Message_pretty0(
  COSE_Format_evercddl_COSE_Tagged_Message_pretty projectee
)
{
  if (projectee.tag == COSE_Format_Mkevercddl_COSE_Tagged_Message_pretty0)
    return true;
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Tagged_Message_pretty1(
  COSE_Format_evercddl_COSE_Tagged_Message_pretty projectee
)
{
  if (projectee.tag == COSE_Format_Mkevercddl_COSE_Tagged_Message_pretty1)
    return true;
  else
    return false;
}

COSE_Format_evercddl_COSE_Tagged_Message_pretty
COSE_Format_evercddl_COSE_Tagged_Message_pretty_right(
  COSE_Format_evercddl_COSE_Tagged_Message x2
)
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

COSE_Format_evercddl_COSE_Tagged_Message
COSE_Format_evercddl_COSE_Tagged_Message_pretty_left(
  COSE_Format_evercddl_COSE_Tagged_Message_pretty x7
)
{
  if (x7.tag == COSE_Format_Mkevercddl_COSE_Tagged_Message_pretty0)
  {
    COSE_Format_evercddl_COSE_Sign_pretty x10 = x7.case_Mkevercddl_COSE_Tagged_Message_pretty0;
    return
      ((COSE_Format_evercddl_COSE_Tagged_Message){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_COSE_Tagged_Message_pretty1)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty x12 = x7.case_Mkevercddl_COSE_Tagged_Message_pretty1;
    return
      ((COSE_Format_evercddl_COSE_Tagged_Message){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

COSE_Format_evercddl_COSE_Tagged_Message_pretty
COSE_Format_parse_COSE_Tagged_Message(cbor_det_t c)
{
  bool test = COSE_Format_validate_COSE_Sign_Tagged(c);
  COSE_Format_evercddl_COSE_Tagged_Message res1;
  if (test)
  {
    COSE_Format_evercddl_COSE_Sign_pretty res = COSE_Format_parse_COSE_Sign_Tagged(c);
    res1 =
      ((COSE_Format_evercddl_COSE_Tagged_Message){ .tag = COSE_Format_Inl, { .case_Inl = res } });
  }
  else
  {
    COSE_Format_evercddl_COSE_Sign1_pretty res = COSE_Format_parse_COSE_Sign1_Tagged(c);
    res1 =
      ((COSE_Format_evercddl_COSE_Tagged_Message){ .tag = COSE_Format_Inr, { .case_Inr = res } });
  }
  COSE_Format_evercddl_COSE_Tagged_Message_pretty
  res2 = COSE_Format_evercddl_COSE_Tagged_Message_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_COSE_Tagged_Message(
  COSE_Format_evercddl_COSE_Tagged_Message_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Tagged_Message
  c_ = COSE_Format_evercddl_COSE_Tagged_Message_pretty_left(c);
  if (c_.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Sign_pretty c1 = c_.case_Inl;
    size_t res = COSE_Format_serialize_COSE_Sign_Tagged(c1, out);
    return res;
  }
  else if (c_.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_COSE_Sign1_pretty c2 = c_.case_Inr;
    size_t res = COSE_Format_serialize_COSE_Sign1_Tagged(c2, out);
    return res;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Tagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Tagged_Message(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Tagged_Message_pretty x = COSE_Format_parse_COSE_Tagged_Message(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Tagged_Message_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  bool test = COSE_Format_validate_COSE_Untagged_Message(c);
  if (test)
    return true;
  else
    return COSE_Format_validate_COSE_Tagged_Message(c);
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Messages_pretty0(
  COSE_Format_evercddl_COSE_Messages_pretty projectee
)
{
  if (projectee.tag == COSE_Format_Mkevercddl_COSE_Messages_pretty0)
    return true;
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_COSE_Messages_pretty1(
  COSE_Format_evercddl_COSE_Messages_pretty projectee
)
{
  if (projectee.tag == COSE_Format_Mkevercddl_COSE_Messages_pretty1)
    return true;
  else
    return false;
}

COSE_Format_evercddl_COSE_Messages_pretty
COSE_Format_evercddl_COSE_Messages_pretty_right(COSE_Format_evercddl_COSE_Messages x2)
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

COSE_Format_evercddl_COSE_Messages
COSE_Format_evercddl_COSE_Messages_pretty_left(COSE_Format_evercddl_COSE_Messages_pretty x7)
{
  if (x7.tag == COSE_Format_Mkevercddl_COSE_Messages_pretty0)
  {
    COSE_Format_evercddl_COSE_Untagged_Message_pretty
    x10 = x7.case_Mkevercddl_COSE_Messages_pretty0;
    return ((COSE_Format_evercddl_COSE_Messages){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_COSE_Messages_pretty1)
  {
    COSE_Format_evercddl_COSE_Tagged_Message_pretty x12 = x7.case_Mkevercddl_COSE_Messages_pretty1;
    return ((COSE_Format_evercddl_COSE_Messages){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

COSE_Format_evercddl_COSE_Messages_pretty COSE_Format_parse_COSE_Messages(cbor_det_t c)
{
  bool test = COSE_Format_validate_COSE_Untagged_Message(c);
  COSE_Format_evercddl_COSE_Messages res1;
  if (test)
  {
    COSE_Format_evercddl_COSE_Untagged_Message_pretty
    res = COSE_Format_parse_COSE_Untagged_Message(c);
    res1 = ((COSE_Format_evercddl_COSE_Messages){ .tag = COSE_Format_Inl, { .case_Inl = res } });
  }
  else
  {
    COSE_Format_evercddl_COSE_Tagged_Message_pretty res = COSE_Format_parse_COSE_Tagged_Message(c);
    res1 = ((COSE_Format_evercddl_COSE_Messages){ .tag = COSE_Format_Inr, { .case_Inr = res } });
  }
  COSE_Format_evercddl_COSE_Messages_pretty
  res2 = COSE_Format_evercddl_COSE_Messages_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_COSE_Messages(
  COSE_Format_evercddl_COSE_Messages_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_COSE_Messages c_ = COSE_Format_evercddl_COSE_Messages_pretty_left(c);
  if (c_.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Untagged_Message_pretty c1 = c_.case_Inl;
    size_t res = COSE_Format_serialize_COSE_Untagged_Message(c1, out);
    return res;
  }
  else if (c_.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_COSE_Tagged_Message_pretty c2 = c_.case_Inr;
    size_t res = COSE_Format_serialize_COSE_Tagged_Message(c2, out);
    return res;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Messages_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_COSE_Messages(rl);
    if (test)
    {
      COSE_Format_evercddl_COSE_Messages_pretty x = COSE_Format_parse_COSE_Messages(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Messages_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t ty = cbor_det_major_type(c);
  if (ty == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_det_array_iterator_t i = cbor_det_array_iterator_start(c);
    cbor_det_array_iterator_t pi = i;
    cbor_det_array_iterator_t i10 = pi;
    bool is_done = cbor_det_array_iterator_is_empty(i10);
    bool test1;
    if (is_done)
      test1 = false;
    else
    {
      cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
      uint8_t mt0 = cbor_det_major_type(c1);
      bool test0 = mt0 == CBOR_MAJOR_TYPE_TEXT_STRING;
      bool test2;
      if (test0)
      {
        uint64_t len = cbor_det_get_string_length(c1);
        uint8_t *a = cbor_det_get_string(c1);
        Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
        Pulse_Lib_Slice_slice__uint8_t sl = s;
        Pulse_Lib_Slice_slice__uint8_t s0 = sl;
        if (len__uint8_t(s0) != (size_t)9ULL)
          test2 = false;
        else
        {
          uint8_t x = op_Array_Access__uint8_t(s0, (size_t)0U);
          size_t i_ = (size_t)1U;
          bool res;
          if (x == 83U)
          {
            uint8_t x1 = op_Array_Access__uint8_t(s0, i_);
            size_t i_1 = i_ + (size_t)1U;
            if (x1 == 105U)
            {
              uint8_t x2 = op_Array_Access__uint8_t(s0, i_1);
              size_t i_2 = i_1 + (size_t)1U;
              if (x2 == 103U)
              {
                uint8_t x3 = op_Array_Access__uint8_t(s0, i_2);
                size_t i_3 = i_2 + (size_t)1U;
                if (x3 == 110U)
                {
                  uint8_t x4 = op_Array_Access__uint8_t(s0, i_3);
                  size_t i_4 = i_3 + (size_t)1U;
                  if (x4 == 97U)
                  {
                    uint8_t x5 = op_Array_Access__uint8_t(s0, i_4);
                    size_t i_5 = i_4 + (size_t)1U;
                    if (x5 == 116U)
                    {
                      uint8_t x6 = op_Array_Access__uint8_t(s0, i_5);
                      size_t i_6 = i_5 + (size_t)1U;
                      if (x6 == 117U)
                      {
                        uint8_t x7 = op_Array_Access__uint8_t(s0, i_6);
                        size_t i_7 = i_6 + (size_t)1U;
                        if (x7 == 114U)
                        {
                          uint8_t x8 = op_Array_Access__uint8_t(s0, i_7);
                          if (x8 == 101U)
                            res = true;
                          else
                            res = false;
                        }
                        else
                          res = false;
                      }
                      else
                        res = false;
                    }
                    else
                      res = false;
                  }
                  else
                    res = false;
                }
                else
                  res = false;
              }
              else
                res = false;
            }
            else
              res = false;
          }
          else
            res = false;
          test2 = res;
        }
      }
      else
        test2 = false;
      bool test;
      if (test2)
        test = true;
      else
      {
        uint8_t mt = cbor_det_major_type(c1);
        bool test1 = mt == CBOR_MAJOR_TYPE_TEXT_STRING;
        if (test1)
        {
          uint64_t len = cbor_det_get_string_length(c1);
          uint8_t *a = cbor_det_get_string(c1);
          Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
          Pulse_Lib_Slice_slice__uint8_t sl = s;
          Pulse_Lib_Slice_slice__uint8_t s0 = sl;
          if (len__uint8_t(s0) != (size_t)10ULL)
            test = false;
          else
          {
            uint8_t x = op_Array_Access__uint8_t(s0, (size_t)0U);
            size_t i_ = (size_t)1U;
            bool res;
            if (x == 83U)
            {
              uint8_t x1 = op_Array_Access__uint8_t(s0, i_);
              size_t i_1 = i_ + (size_t)1U;
              if (x1 == 105U)
              {
                uint8_t x2 = op_Array_Access__uint8_t(s0, i_1);
                size_t i_2 = i_1 + (size_t)1U;
                if (x2 == 103U)
                {
                  uint8_t x3 = op_Array_Access__uint8_t(s0, i_2);
                  size_t i_3 = i_2 + (size_t)1U;
                  if (x3 == 110U)
                  {
                    uint8_t x4 = op_Array_Access__uint8_t(s0, i_3);
                    size_t i_4 = i_3 + (size_t)1U;
                    if (x4 == 97U)
                    {
                      uint8_t x5 = op_Array_Access__uint8_t(s0, i_4);
                      size_t i_5 = i_4 + (size_t)1U;
                      if (x5 == 116U)
                      {
                        uint8_t x6 = op_Array_Access__uint8_t(s0, i_5);
                        size_t i_6 = i_5 + (size_t)1U;
                        if (x6 == 117U)
                        {
                          uint8_t x7 = op_Array_Access__uint8_t(s0, i_6);
                          size_t i_7 = i_6 + (size_t)1U;
                          if (x7 == 114U)
                          {
                            uint8_t x8 = op_Array_Access__uint8_t(s0, i_7);
                            size_t i_8 = i_7 + (size_t)1U;
                            if (x8 == 101U)
                            {
                              uint8_t x9 = op_Array_Access__uint8_t(s0, i_8);
                              if (x9 == 49U)
                                res = true;
                              else
                                res = false;
                            }
                            else
                              res = false;
                          }
                          else
                            res = false;
                        }
                        else
                          res = false;
                      }
                      else
                        res = false;
                    }
                    else
                      res = false;
                  }
                  else
                    res = false;
                }
                else
                  res = false;
              }
              else
                res = false;
            }
            else
              res = false;
            test = res;
          }
        }
        else
          test = false;
      }
      test1 = test;
    }
    bool b_success;
    if (test1)
    {
      cbor_det_array_iterator_t i10 = pi;
      bool is_done = cbor_det_array_iterator_is_empty(i10);
      bool test11;
      if (is_done)
        test11 = false;
      else
      {
        cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
        bool test = COSE_Format_validate_empty_or_serialized_map(c1);
        test11 = test;
      }
      bool test20;
      if (test11)
      {
        cbor_det_array_iterator_t i1 = pi;
        cbor_det_array_iterator_t i20 = pi;
        bool is_done = cbor_det_array_iterator_is_empty(i20);
        bool test120;
        if (is_done)
          test120 = false;
        else
        {
          cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
          bool test = COSE_Format_validate_empty_or_serialized_map(c1);
          test120 = test;
        }
        bool test12;
        if (test120)
        {
          cbor_det_array_iterator_t i20 = pi;
          bool is_done = cbor_det_array_iterator_is_empty(i20);
          bool test13;
          if (is_done)
            test13 = false;
          else
          {
            cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
            bool test = COSE_Format_validate_bstr(c1);
            test13 = test;
          }
          bool test20;
          if (test13)
          {
            cbor_det_array_iterator_t i2 = pi;
            bool is_done = cbor_det_array_iterator_is_empty(i2);
            bool test2;
            if (is_done)
              test2 = false;
            else
            {
              cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
              bool test = COSE_Format_validate_bstr(c1);
              test2 = test;
            }
            test20 = test2;
          }
          else
            test20 = false;
          test12 = test20;
        }
        else
          test12 = false;
        bool test21;
        if (test12)
          test21 = true;
        else
        {
          pi = i1;
          cbor_det_array_iterator_t i20 = pi;
          bool is_done = cbor_det_array_iterator_is_empty(i20);
          bool test13;
          if (is_done)
            test13 = false;
          else
          {
            cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
            bool test = COSE_Format_validate_bstr(c1);
            test13 = test;
          }
          bool res;
          if (test13)
          {
            cbor_det_array_iterator_t i2 = pi;
            bool is_done = cbor_det_array_iterator_is_empty(i2);
            bool test2;
            if (is_done)
              test2 = false;
            else
            {
              cbor_det_t c1 = cbor_det_array_iterator_next(&pi);
              bool test = COSE_Format_validate_bstr(c1);
              test2 = test;
            }
            res = test2;
          }
          else
            res = false;
          test21 = res;
        }
        test20 = test21;
      }
      else
        test20 = false;
      b_success = test20;
    }
    else
      b_success = false;
    if (b_success)
    {
      cbor_det_array_iterator_t i_ = pi;
      bool b_end = cbor_det_array_iterator_is_empty(i_);
      return b_end;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_Sig_structure_pretty0(
  COSE_Format_evercddl_Sig_structure_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_Sig_structure_pretty
COSE_Format_evercddl_Sig_structure_pretty_right(COSE_Format_evercddl_Sig_structure x3)
{
  FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  x6 = x3.snd.snd;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x5 = x3.snd.fst;
  COSE_Format_evercddl_int_tags x4 = x3.fst;
  return ((COSE_Format_evercddl_Sig_structure_pretty){ .x0 = x4, .x1 = x5, .x2 = x6 });
}

COSE_Format_evercddl_Sig_structure
COSE_Format_evercddl_Sig_structure_pretty_left(COSE_Format_evercddl_Sig_structure_pretty x7)
{
  COSE_Format_evercddl_int_tags x12 = x7.x0;
  COSE_Format_evercddl_empty_or_serialized_map_pretty x13 = x7.x1;
  FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  x14 = x7.x2;
  return ((COSE_Format_evercddl_Sig_structure){ .fst = x12, .snd = { .fst = x13, .snd = x14 } });
}

COSE_Format_evercddl_Sig_structure_pretty COSE_Format_parse_Sig_structure(cbor_det_t c)
{
  cbor_det_array_iterator_t ar = cbor_det_array_iterator_start(c);
  uint64_t rlen0 = cbor_det_array_iterator_length(ar);
  cbor_det_array_iterator_t pc = ar;
  cbor_det_array_iterator_t i0 = pc;
  bool is_done = cbor_det_array_iterator_is_empty(i0);
  bool _tmp;
  if (is_done)
    _tmp = false;
  else
  {
    cbor_det_t c1 = cbor_det_array_iterator_next(&pc);
    uint8_t mt0 = cbor_det_major_type(c1);
    bool test0 = mt0 == CBOR_MAJOR_TYPE_TEXT_STRING;
    bool test1;
    if (test0)
    {
      uint64_t len = cbor_det_get_string_length(c1);
      uint8_t *a = cbor_det_get_string(c1);
      Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
      Pulse_Lib_Slice_slice__uint8_t sl = s;
      Pulse_Lib_Slice_slice__uint8_t s0 = sl;
      if (len__uint8_t(s0) != (size_t)9ULL)
        test1 = false;
      else
      {
        uint8_t x = op_Array_Access__uint8_t(s0, (size_t)0U);
        size_t i_ = (size_t)1U;
        bool res;
        if (x == 83U)
        {
          uint8_t x1 = op_Array_Access__uint8_t(s0, i_);
          size_t i_1 = i_ + (size_t)1U;
          if (x1 == 105U)
          {
            uint8_t x2 = op_Array_Access__uint8_t(s0, i_1);
            size_t i_2 = i_1 + (size_t)1U;
            if (x2 == 103U)
            {
              uint8_t x3 = op_Array_Access__uint8_t(s0, i_2);
              size_t i_3 = i_2 + (size_t)1U;
              if (x3 == 110U)
              {
                uint8_t x4 = op_Array_Access__uint8_t(s0, i_3);
                size_t i_4 = i_3 + (size_t)1U;
                if (x4 == 97U)
                {
                  uint8_t x5 = op_Array_Access__uint8_t(s0, i_4);
                  size_t i_5 = i_4 + (size_t)1U;
                  if (x5 == 116U)
                  {
                    uint8_t x6 = op_Array_Access__uint8_t(s0, i_5);
                    size_t i_6 = i_5 + (size_t)1U;
                    if (x6 == 117U)
                    {
                      uint8_t x7 = op_Array_Access__uint8_t(s0, i_6);
                      size_t i_7 = i_6 + (size_t)1U;
                      if (x7 == 114U)
                      {
                        uint8_t x8 = op_Array_Access__uint8_t(s0, i_7);
                        if (x8 == 101U)
                          res = true;
                        else
                          res = false;
                      }
                      else
                        res = false;
                    }
                    else
                      res = false;
                  }
                  else
                    res = false;
                }
                else
                  res = false;
              }
              else
                res = false;
            }
            else
              res = false;
          }
          else
            res = false;
        }
        else
          res = false;
        test1 = res;
      }
    }
    else
      test1 = false;
    bool test;
    if (test1)
      test = true;
    else
    {
      uint8_t mt = cbor_det_major_type(c1);
      bool test1 = mt == CBOR_MAJOR_TYPE_TEXT_STRING;
      if (test1)
      {
        uint64_t len = cbor_det_get_string_length(c1);
        uint8_t *a = cbor_det_get_string(c1);
        Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
        Pulse_Lib_Slice_slice__uint8_t sl = s;
        Pulse_Lib_Slice_slice__uint8_t s0 = sl;
        if (len__uint8_t(s0) != (size_t)10ULL)
          test = false;
        else
        {
          uint8_t x = op_Array_Access__uint8_t(s0, (size_t)0U);
          size_t i_ = (size_t)1U;
          bool res;
          if (x == 83U)
          {
            uint8_t x1 = op_Array_Access__uint8_t(s0, i_);
            size_t i_1 = i_ + (size_t)1U;
            if (x1 == 105U)
            {
              uint8_t x2 = op_Array_Access__uint8_t(s0, i_1);
              size_t i_2 = i_1 + (size_t)1U;
              if (x2 == 103U)
              {
                uint8_t x3 = op_Array_Access__uint8_t(s0, i_2);
                size_t i_3 = i_2 + (size_t)1U;
                if (x3 == 110U)
                {
                  uint8_t x4 = op_Array_Access__uint8_t(s0, i_3);
                  size_t i_4 = i_3 + (size_t)1U;
                  if (x4 == 97U)
                  {
                    uint8_t x5 = op_Array_Access__uint8_t(s0, i_4);
                    size_t i_5 = i_4 + (size_t)1U;
                    if (x5 == 116U)
                    {
                      uint8_t x6 = op_Array_Access__uint8_t(s0, i_5);
                      size_t i_6 = i_5 + (size_t)1U;
                      if (x6 == 117U)
                      {
                        uint8_t x7 = op_Array_Access__uint8_t(s0, i_6);
                        size_t i_7 = i_6 + (size_t)1U;
                        if (x7 == 114U)
                        {
                          uint8_t x8 = op_Array_Access__uint8_t(s0, i_7);
                          size_t i_8 = i_7 + (size_t)1U;
                          if (x8 == 101U)
                          {
                            uint8_t x9 = op_Array_Access__uint8_t(s0, i_8);
                            if (x9 == 49U)
                              res = true;
                            else
                              res = false;
                          }
                          else
                            res = false;
                        }
                        else
                          res = false;
                      }
                      else
                        res = false;
                    }
                    else
                      res = false;
                  }
                  else
                    res = false;
                }
                else
                  res = false;
              }
              else
                res = false;
            }
            else
              res = false;
          }
          else
            res = false;
          test = res;
        }
      }
      else
        test = false;
    }
    _tmp = test;
  }
  KRML_MAYBE_UNUSED_VAR(_tmp);
  cbor_det_array_iterator_t c1 = pc;
  uint64_t rlen1 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t c0_ = cbor_det_array_iterator_truncate(ar, rlen0 - rlen1);
  cbor_det_array_iterator_t pc10 = c0_;
  cbor_det_t x = cbor_det_array_iterator_next(&pc10);
  uint8_t mt = cbor_det_major_type(x);
  bool test0 = mt == CBOR_MAJOR_TYPE_TEXT_STRING;
  bool test;
  if (test0)
  {
    uint64_t len = cbor_det_get_string_length(x);
    uint8_t *a = cbor_det_get_string(x);
    Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
    Pulse_Lib_Slice_slice__uint8_t sl = s;
    Pulse_Lib_Slice_slice__uint8_t s0 = sl;
    if (len__uint8_t(s0) != (size_t)9ULL)
      test = false;
    else
    {
      uint8_t x1 = op_Array_Access__uint8_t(s0, (size_t)0U);
      size_t i_ = (size_t)1U;
      bool res;
      if (x1 == 83U)
      {
        uint8_t x2 = op_Array_Access__uint8_t(s0, i_);
        size_t i_1 = i_ + (size_t)1U;
        if (x2 == 105U)
        {
          uint8_t x3 = op_Array_Access__uint8_t(s0, i_1);
          size_t i_2 = i_1 + (size_t)1U;
          if (x3 == 103U)
          {
            uint8_t x4 = op_Array_Access__uint8_t(s0, i_2);
            size_t i_3 = i_2 + (size_t)1U;
            if (x4 == 110U)
            {
              uint8_t x5 = op_Array_Access__uint8_t(s0, i_3);
              size_t i_4 = i_3 + (size_t)1U;
              if (x5 == 97U)
              {
                uint8_t x6 = op_Array_Access__uint8_t(s0, i_4);
                size_t i_5 = i_4 + (size_t)1U;
                if (x6 == 116U)
                {
                  uint8_t x7 = op_Array_Access__uint8_t(s0, i_5);
                  size_t i_6 = i_5 + (size_t)1U;
                  if (x7 == 117U)
                  {
                    uint8_t x8 = op_Array_Access__uint8_t(s0, i_6);
                    size_t i_7 = i_6 + (size_t)1U;
                    if (x8 == 114U)
                    {
                      uint8_t x9 = op_Array_Access__uint8_t(s0, i_7);
                      if (x9 == 101U)
                        res = true;
                      else
                        res = false;
                    }
                    else
                      res = false;
                  }
                  else
                    res = false;
                }
                else
                  res = false;
              }
              else
                res = false;
            }
            else
              res = false;
          }
          else
            res = false;
        }
        else
          res = false;
      }
      else
        res = false;
      test = res;
    }
  }
  else
    test = false;
  COSE_Format_evercddl_int_tags res;
  if (test)
    res = COSE_Format_Inl;
  else
    res = COSE_Format_Inr;
  COSE_Format_evercddl_int_tags w1 = res;
  uint64_t rlen01 = cbor_det_array_iterator_length(c1);
  cbor_det_array_iterator_t pc1 = c1;
  cbor_det_array_iterator_t i1 = pc1;
  bool is_done0 = cbor_det_array_iterator_is_empty(i1);
  bool _tmp1;
  if (is_done0)
    _tmp1 = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc1);
    bool test = COSE_Format_validate_empty_or_serialized_map(c2);
    _tmp1 = test;
  }
  KRML_MAYBE_UNUSED_VAR(_tmp1);
  cbor_det_array_iterator_t c11 = pc1;
  uint64_t rlen11 = cbor_det_array_iterator_length(c11);
  cbor_det_array_iterator_t c0_1 = cbor_det_array_iterator_truncate(c1, rlen01 - rlen11);
  cbor_det_array_iterator_t pc20 = c0_1;
  cbor_det_t x0 = cbor_det_array_iterator_next(&pc20);
  COSE_Format_evercddl_empty_or_serialized_map_pretty
  res0 = COSE_Format_parse_empty_or_serialized_map(x0);
  COSE_Format_evercddl_empty_or_serialized_map_pretty w11 = res0;
  cbor_det_array_iterator_t pc2 = c11;
  cbor_det_array_iterator_t i2 = pc2;
  bool is_done1 = cbor_det_array_iterator_is_empty(i2);
  bool test10;
  if (is_done1)
    test10 = false;
  else
  {
    cbor_det_t c2 = cbor_det_array_iterator_next(&pc2);
    bool test = COSE_Format_validate_empty_or_serialized_map(c2);
    test10 = test;
  }
  bool test1;
  if (test10)
  {
    cbor_det_array_iterator_t i0 = pc2;
    bool is_done = cbor_det_array_iterator_is_empty(i0);
    bool test11;
    if (is_done)
      test11 = false;
    else
    {
      cbor_det_t c2 = cbor_det_array_iterator_next(&pc2);
      bool test = COSE_Format_validate_bstr(c2);
      test11 = test;
    }
    bool test20;
    if (test11)
    {
      cbor_det_array_iterator_t i = pc2;
      bool is_done = cbor_det_array_iterator_is_empty(i);
      bool test2;
      if (is_done)
        test2 = false;
      else
      {
        cbor_det_t c2 = cbor_det_array_iterator_next(&pc2);
        bool test = COSE_Format_validate_bstr(c2);
        test2 = test;
      }
      test20 = test2;
    }
    else
      test20 = false;
    test1 = test20;
  }
  else
    test1 = false;
  FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  _bind_c;
  if (test1)
  {
    uint64_t rlen02 = cbor_det_array_iterator_length(c11);
    cbor_det_array_iterator_t pc3 = c11;
    cbor_det_array_iterator_t i0 = pc3;
    bool is_done = cbor_det_array_iterator_is_empty(i0);
    bool _tmp2;
    if (is_done)
      _tmp2 = false;
    else
    {
      cbor_det_t c2 = cbor_det_array_iterator_next(&pc3);
      bool test = COSE_Format_validate_empty_or_serialized_map(c2);
      _tmp2 = test;
    }
    KRML_MAYBE_UNUSED_VAR(_tmp2);
    cbor_det_array_iterator_t c12 = pc3;
    uint64_t rlen12 = cbor_det_array_iterator_length(c12);
    cbor_det_array_iterator_t c0_2 = cbor_det_array_iterator_truncate(c11, rlen02 - rlen12);
    cbor_det_array_iterator_t pc40 = c0_2;
    cbor_det_t x = cbor_det_array_iterator_next(&pc40);
    COSE_Format_evercddl_empty_or_serialized_map_pretty
    res = COSE_Format_parse_empty_or_serialized_map(x);
    COSE_Format_evercddl_empty_or_serialized_map_pretty w12 = res;
    uint64_t rlen03 = cbor_det_array_iterator_length(c12);
    cbor_det_array_iterator_t pc4 = c12;
    cbor_det_array_iterator_t i = pc4;
    bool is_done0 = cbor_det_array_iterator_is_empty(i);
    bool _tmp3;
    if (is_done0)
      _tmp3 = false;
    else
    {
      cbor_det_t c2 = cbor_det_array_iterator_next(&pc4);
      bool test = COSE_Format_validate_bstr(c2);
      _tmp3 = test;
    }
    KRML_MAYBE_UNUSED_VAR(_tmp3);
    cbor_det_array_iterator_t c13 = pc4;
    uint64_t rlen13 = cbor_det_array_iterator_length(c13);
    cbor_det_array_iterator_t c0_3 = cbor_det_array_iterator_truncate(c12, rlen03 - rlen13);
    cbor_det_array_iterator_t pc50 = c0_3;
    cbor_det_t x0 = cbor_det_array_iterator_next(&pc50);
    COSE_Format_evercddl_bstr res0 = COSE_Format_parse_bstr(x0);
    COSE_Format_evercddl_bstr w13 = res0;
    cbor_det_array_iterator_t pc5 = c13;
    cbor_det_t x1 = cbor_det_array_iterator_next(&pc5);
    COSE_Format_evercddl_bstr res1 = COSE_Format_parse_bstr(x1);
    COSE_Format_evercddl_bstr w2 = res1;
    K___COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_bstr_pretty
    w20 = { .fst = w13, .snd = w2 };
    K___COSE_Format_evercddl_empty_or_serialized_map_pretty__COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
    w120 = { .fst = w12, .snd = w20 };
    _bind_c =
      (
        (FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_){
          .tag = COSE_Format_Inl,
          { .case_Inl = w120 }
        }
      );
  }
  else
  {
    uint64_t rlen02 = cbor_det_array_iterator_length(c11);
    cbor_det_array_iterator_t pc3 = c11;
    cbor_det_array_iterator_t i = pc3;
    bool is_done = cbor_det_array_iterator_is_empty(i);
    bool _tmp2;
    if (is_done)
      _tmp2 = false;
    else
    {
      cbor_det_t c2 = cbor_det_array_iterator_next(&pc3);
      bool test = COSE_Format_validate_bstr(c2);
      _tmp2 = test;
    }
    KRML_MAYBE_UNUSED_VAR(_tmp2);
    cbor_det_array_iterator_t c12 = pc3;
    uint64_t rlen12 = cbor_det_array_iterator_length(c12);
    cbor_det_array_iterator_t c0_2 = cbor_det_array_iterator_truncate(c11, rlen02 - rlen12);
    cbor_det_array_iterator_t pc40 = c0_2;
    cbor_det_t x = cbor_det_array_iterator_next(&pc40);
    COSE_Format_evercddl_bstr res = COSE_Format_parse_bstr(x);
    COSE_Format_evercddl_bstr w12 = res;
    cbor_det_array_iterator_t pc4 = c12;
    cbor_det_t x0 = cbor_det_array_iterator_next(&pc4);
    COSE_Format_evercddl_bstr res0 = COSE_Format_parse_bstr(x0);
    COSE_Format_evercddl_bstr w2 = res0;
    K___COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_bstr_pretty
    w20 = { .fst = w12, .snd = w2 };
    _bind_c =
      (
        (FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_){
          .tag = COSE_Format_Inr,
          { .case_Inr = w20 }
        }
      );
  }
  FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  w2 = _bind_c;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_FStar_Pervasives_either__COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  w20 = { .fst = w11, .snd = w2 };
  COSE_Format_evercddl_Sig_structure res1 = { .fst = w1, .snd = w20 };
  COSE_Format_evercddl_Sig_structure res10 = res1;
  COSE_Format_evercddl_Sig_structure_pretty
  res2 = COSE_Format_evercddl_Sig_structure_pretty_right(res10);
  return res2;
}

static Pulse_Lib_Slice_slice__uint8_t from_array__uint8_t(uint8_t *a, size_t alen)
{
  uint8_t *ptr = a;
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = ptr, .len = alen });
}

static void op_Array_Assignment__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i, uint8_t v)
{
  a.elt[i] = v;
}

size_t
COSE_Format_serialize_Sig_structure(
  COSE_Format_evercddl_Sig_structure_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_Sig_structure c_ = COSE_Format_evercddl_Sig_structure_pretty_left(c);
  uint64_t pcount = 0ULL;
  size_t psize = (size_t)0U;
  COSE_Format_evercddl_Sig_structure _letpattern = c_;
  COSE_Format_evercddl_int_tags c1 = _letpattern.fst;
  K___COSE_Format_evercddl_empty_or_serialized_map_pretty_FStar_Pervasives_either__COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
  c2 = _letpattern.snd;
  uint64_t count0 = pcount;
  bool res1;
  if (count0 < 18446744073709551615ULL)
  {
    size_t size = psize;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, size);
    Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern1.snd;
    size_t size1;
    switch (c1)
    {
      case COSE_Format_Inl:
        {
          uint8_t a[(size_t)9ULL];
          memset(a, 0U, (size_t)9ULL * sizeof (uint8_t));
          size_t len_sz = (size_t)9ULL;
          Pulse_Lib_Slice_slice__uint8_t s = from_array__uint8_t(a, len_sz);
          op_Array_Assignment__uint8_t(s, (size_t)0U, 83U);
          size_t i_ = (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_, 105U);
          size_t i_1 = i_ + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_1, 103U);
          size_t i_2 = i_1 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_2, 110U);
          size_t i_3 = i_2 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_3, 97U);
          size_t i_4 = i_3 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_4, 116U);
          size_t i_5 = i_4 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_5, 117U);
          size_t i_6 = i_5 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_6, 114U);
          size_t i_7 = i_6 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_7, 101U);
          uint8_t *a1 = slice_to_arrayptr_intro__uint8_t(s);
          uint8_t *a10 = a1;
          cbor_det_t
          res0 =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
              a10,
              (uint64_t)len__uint8_t(s));
          cbor_det_t c3 = res0;
          size_t slen = len__uint8_t(out1);
          size_t len = cbor_det_size(c3, slen);
          option__size_t res1;
          if (len > (size_t)0U)
          {
            uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
            size_t len_ = cbor_det_serialize(c3, out2, len);
            res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
          }
          else
            res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
          size_t res;
          if (res1.tag == FStar_Pervasives_Native_None)
            res = (size_t)0U;
          else if (res1.tag == FStar_Pervasives_Native_Some)
            res = res1.v;
          else
            res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          size_t res2 = res;
          size1 = res2;
          break;
        }
      case COSE_Format_Inr:
        {
          uint8_t a[(size_t)10ULL];
          memset(a, 0U, (size_t)10ULL * sizeof (uint8_t));
          size_t len_sz = (size_t)10ULL;
          Pulse_Lib_Slice_slice__uint8_t s = from_array__uint8_t(a, len_sz);
          op_Array_Assignment__uint8_t(s, (size_t)0U, 83U);
          size_t i_ = (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_, 105U);
          size_t i_1 = i_ + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_1, 103U);
          size_t i_2 = i_1 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_2, 110U);
          size_t i_3 = i_2 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_3, 97U);
          size_t i_4 = i_3 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_4, 116U);
          size_t i_5 = i_4 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_5, 117U);
          size_t i_6 = i_5 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_6, 114U);
          size_t i_7 = i_6 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_7, 101U);
          size_t i_8 = i_7 + (size_t)1U;
          op_Array_Assignment__uint8_t(s, i_8, 49U);
          uint8_t *a1 = slice_to_arrayptr_intro__uint8_t(s);
          uint8_t *a10 = a1;
          cbor_det_t
          res0 =
            cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING,
              a10,
              (uint64_t)len__uint8_t(s));
          cbor_det_t c3 = res0;
          size_t slen = len__uint8_t(out1);
          size_t len = cbor_det_size(c3, slen);
          option__size_t res1;
          if (len > (size_t)0U)
          {
            uint8_t *out2 = slice_to_arrayptr_intro__uint8_t(out1);
            size_t len_ = cbor_det_serialize(c3, out2, len);
            res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = len_ });
          }
          else
            res1 = ((option__size_t){ .tag = FStar_Pervasives_Native_None });
          size_t res;
          if (res1.tag == FStar_Pervasives_Native_None)
            res = (size_t)0U;
          else if (res1.tag == FStar_Pervasives_Native_Some)
            res = res1.v;
          else
            res = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
          size_t res2 = res;
          size1 = res2;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    if (size1 == (size_t)0U)
      res1 = false;
    else
    {
      pcount = count0 + 1ULL;
      psize = size + size1;
      res1 = true;
    }
  }
  else
    res1 = false;
  bool res0;
  if (res1)
  {
    K___COSE_Format_evercddl_empty_or_serialized_map_pretty_FStar_Pervasives_either__COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
    _letpattern1 = c2;
    COSE_Format_evercddl_empty_or_serialized_map_pretty c11 = _letpattern1.fst;
    FStar_Pervasives_either___COSE_Format_evercddl_empty_or_serialized_map_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty____COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
    c21 = _letpattern1.snd;
    uint64_t count0 = pcount;
    bool res11;
    if (count0 < 18446744073709551615ULL)
    {
      size_t size = psize;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(out, size);
      Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern2.snd;
      size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c11, out1);
      if (size1 == (size_t)0U)
        res11 = false;
      else
      {
        pcount = count0 + 1ULL;
        psize = size + size1;
        res11 = true;
      }
    }
    else
      res11 = false;
    bool res20;
    if (res11)
    {
      bool res21;
      if (c21.tag == COSE_Format_Inl)
      {
        K___COSE_Format_evercddl_empty_or_serialized_map_pretty__COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
        c12 = c21.case_Inl;
        K___COSE_Format_evercddl_empty_or_serialized_map_pretty__COSE_Format_evercddl_bstr_pretty___COSE_Format_evercddl_bstr_pretty_
        _letpattern2 = c12;
        COSE_Format_evercddl_empty_or_serialized_map_pretty c13 = _letpattern2.fst;
        K___COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_bstr_pretty
        c22 = _letpattern2.snd;
        uint64_t count0 = pcount;
        bool res12;
        if (count0 < 18446744073709551615ULL)
        {
          size_t size = psize;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern3 = split__uint8_t(out, size);
          Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
          size_t size1 = COSE_Format_serialize_empty_or_serialized_map(c13, out1);
          if (size1 == (size_t)0U)
            res12 = false;
          else
          {
            pcount = count0 + 1ULL;
            psize = size + size1;
            res12 = true;
          }
        }
        else
          res12 = false;
        bool res;
        if (res12)
        {
          K___COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_bstr_pretty _letpattern3 = c22;
          COSE_Format_evercddl_bstr c14 = _letpattern3.fst;
          COSE_Format_evercddl_bstr c23 = _letpattern3.snd;
          uint64_t count0 = pcount;
          bool res13;
          if (count0 < 18446744073709551615ULL)
          {
            size_t size = psize;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern4 = split__uint8_t(out, size);
            Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern4.snd;
            size_t size1 = COSE_Format_serialize_bstr(c14, out1);
            if (size1 == (size_t)0U)
              res13 = false;
            else
            {
              pcount = count0 + 1ULL;
              psize = size + size1;
              res13 = true;
            }
          }
          else
            res13 = false;
          bool res20;
          if (res13)
          {
            uint64_t count = pcount;
            bool res2;
            if (count < 18446744073709551615ULL)
            {
              size_t size = psize;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern4 = split__uint8_t(out, size);
              Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern4.snd;
              size_t size1 = COSE_Format_serialize_bstr(c23, out1);
              if (size1 == (size_t)0U)
                res2 = false;
              else
              {
                pcount = count + 1ULL;
                psize = size + size1;
                res2 = true;
              }
            }
            else
              res2 = false;
            res20 = res2;
          }
          else
            res20 = false;
          res = res20;
        }
        else
          res = false;
        res21 = res;
      }
      else if (c21.tag == COSE_Format_Inr)
      {
        K___COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_bstr_pretty c22 = c21.case_Inr;
        K___COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_bstr_pretty _letpattern2 = c22;
        COSE_Format_evercddl_bstr c12 = _letpattern2.fst;
        COSE_Format_evercddl_bstr c23 = _letpattern2.snd;
        uint64_t count0 = pcount;
        bool res12;
        if (count0 < 18446744073709551615ULL)
        {
          size_t size = psize;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern3 = split__uint8_t(out, size);
          Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
          size_t size1 = COSE_Format_serialize_bstr(c12, out1);
          if (size1 == (size_t)0U)
            res12 = false;
          else
          {
            pcount = count0 + 1ULL;
            psize = size + size1;
            res12 = true;
          }
        }
        else
          res12 = false;
        bool res;
        if (res12)
        {
          uint64_t count = pcount;
          bool res2;
          if (count < 18446744073709551615ULL)
          {
            size_t size = psize;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern3 = split__uint8_t(out, size);
            Pulse_Lib_Slice_slice__uint8_t out1 = _letpattern3.snd;
            size_t size1 = COSE_Format_serialize_bstr(c23, out1);
            if (size1 == (size_t)0U)
              res2 = false;
            else
            {
              pcount = count + 1ULL;
              psize = size + size1;
              res2 = true;
            }
          }
          else
            res2 = false;
          res = res2;
        }
        else
          res = false;
        res21 = res;
      }
      else
        res21 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
      res20 = res21;
    }
    else
      res20 = false;
    res0 = res20;
  }
  else
    res0 = false;
  size_t _bind_c;
  if (res0)
  {
    size_t size = psize;
    uint64_t count = pcount;
    size_t aout_len = len__uint8_t(out);
    uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
    size_t res1 = cbor_det_serialize_array_to_array(count, aout, aout_len, size);
    _bind_c = res1;
  }
  else
    _bind_c = (size_t)0U;
  size_t res = _bind_c;
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_Sig_structure_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_Sig_structure(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_Sig_structure_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_Sig_structure(rl);
    if (test)
    {
      COSE_Format_evercddl_Sig_structure_pretty x = COSE_Format_parse_Sig_structure(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_Sig_structure_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool
COSE_Format_uu___is_Mkevercddl_Internal_Types_pretty0(
  COSE_Format_evercddl_Sig_structure_pretty projectee
)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_Sig_structure_pretty
COSE_Format_evercddl_Internal_Types_pretty_right(COSE_Format_evercddl_Sig_structure_pretty x1)
{
  return x1;
}

COSE_Format_evercddl_Sig_structure_pretty
COSE_Format_evercddl_Internal_Types_pretty_left(COSE_Format_evercddl_Sig_structure_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_Sig_structure_pretty COSE_Format_parse_Internal_Types(cbor_det_t c)
{
  COSE_Format_evercddl_Sig_structure_pretty res1 = COSE_Format_parse_Sig_structure(c);
  COSE_Format_evercddl_Sig_structure_pretty
  res2 = COSE_Format_evercddl_Internal_Types_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_Internal_Types(
  COSE_Format_evercddl_Sig_structure_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_Sig_structure_pretty
  c_ = COSE_Format_evercddl_Internal_Types_pretty_left(c);
  size_t res = COSE_Format_serialize_Sig_structure(c_, out);
  return res;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_Internal_Types_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_Internal_Types(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_Internal_Types_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_Internal_Types(rl);
    if (test)
    {
      COSE_Format_evercddl_Sig_structure_pretty x = COSE_Format_parse_Internal_Types(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_Internal_Types_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  bool test = COSE_Format_validate_COSE_Messages(c);
  if (test)
    return true;
  else
    return COSE_Format_validate_Internal_Types(c);
}

bool COSE_Format_uu___is_Mkevercddl_start_pretty0(COSE_Format_evercddl_start_pretty projectee)
{
  if (projectee.tag == COSE_Format_Mkevercddl_start_pretty0)
    return true;
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_start_pretty1(COSE_Format_evercddl_start_pretty projectee)
{
  if (projectee.tag == COSE_Format_Mkevercddl_start_pretty1)
    return true;
  else
    return false;
}

COSE_Format_evercddl_start_pretty
COSE_Format_evercddl_start_pretty_right(COSE_Format_evercddl_start x2)
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

COSE_Format_evercddl_start
COSE_Format_evercddl_start_pretty_left(COSE_Format_evercddl_start_pretty x7)
{
  if (x7.tag == COSE_Format_Mkevercddl_start_pretty0)
  {
    COSE_Format_evercddl_COSE_Messages_pretty x10 = x7.case_Mkevercddl_start_pretty0;
    return ((COSE_Format_evercddl_start){ .tag = COSE_Format_Inl, { .case_Inl = x10 } });
  }
  else if (x7.tag == COSE_Format_Mkevercddl_start_pretty1)
  {
    COSE_Format_evercddl_Sig_structure_pretty x12 = x7.case_Mkevercddl_start_pretty1;
    return ((COSE_Format_evercddl_start){ .tag = COSE_Format_Inr, { .case_Inr = x12 } });
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

COSE_Format_evercddl_start_pretty COSE_Format_parse_start(cbor_det_t c)
{
  bool test = COSE_Format_validate_COSE_Messages(c);
  COSE_Format_evercddl_start res1;
  if (test)
  {
    COSE_Format_evercddl_COSE_Messages_pretty res = COSE_Format_parse_COSE_Messages(c);
    res1 = ((COSE_Format_evercddl_start){ .tag = COSE_Format_Inl, { .case_Inl = res } });
  }
  else
  {
    COSE_Format_evercddl_Sig_structure_pretty res = COSE_Format_parse_Internal_Types(c);
    res1 = ((COSE_Format_evercddl_start){ .tag = COSE_Format_Inr, { .case_Inr = res } });
  }
  COSE_Format_evercddl_start_pretty res2 = COSE_Format_evercddl_start_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_start(
  COSE_Format_evercddl_start_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_start c_ = COSE_Format_evercddl_start_pretty_left(c);
  if (c_.tag == COSE_Format_Inl)
  {
    COSE_Format_evercddl_COSE_Messages_pretty c1 = c_.case_Inl;
    size_t res = COSE_Format_serialize_COSE_Messages(c1, out);
    return res;
  }
  else if (c_.tag == COSE_Format_Inr)
  {
    COSE_Format_evercddl_Sig_structure_pretty c2 = c_.case_Inr;
    size_t res = COSE_Format_serialize_Internal_Types(c2, out);
    return res;
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
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_start_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_start(rl);
    if (test)
    {
      COSE_Format_evercddl_start_pretty x = COSE_Format_parse_start(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_start_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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

bool COSE_Format_validate_eb64url(cbor_det_t c)
{
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (21ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_any(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_eb64url_pretty0(COSE_Format_evercddl_any_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_any_pretty
COSE_Format_evercddl_eb64url_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

COSE_Format_evercddl_any
COSE_Format_evercddl_eb64url_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_any_pretty COSE_Format_parse_eb64url(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_any res = COSE_Format_parse_any(cpl);
  COSE_Format_evercddl_any res1 = res;
  COSE_Format_evercddl_any_pretty res2 = COSE_Format_evercddl_eb64url_pretty_right(res1);
  return res2;
}

typedef struct __uint64_t_COSE_Format_evercddl_any_pretty_s
{
  uint64_t fst;
  COSE_Format_evercddl_any snd;
}
__uint64_t_COSE_Format_evercddl_any_pretty;

size_t
COSE_Format_serialize_eb64url(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_any c_ = COSE_Format_evercddl_eb64url_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_any_pretty c_1 = { .fst = 21ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_any_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_any cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_any(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64url_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_eb64url(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_eb64url(rl);
    if (test)
    {
      COSE_Format_evercddl_any_pretty x = COSE_Format_parse_eb64url(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64url_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (22ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_any(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool
COSE_Format_uu___is_Mkevercddl_eb64legacy_pretty0(COSE_Format_evercddl_any_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_any_pretty
COSE_Format_evercddl_eb64legacy_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

COSE_Format_evercddl_any
COSE_Format_evercddl_eb64legacy_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_any_pretty COSE_Format_parse_eb64legacy(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_any res = COSE_Format_parse_any(cpl);
  COSE_Format_evercddl_any res1 = res;
  COSE_Format_evercddl_any_pretty res2 = COSE_Format_evercddl_eb64legacy_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_eb64legacy(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_any c_ = COSE_Format_evercddl_eb64legacy_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_any_pretty c_1 = { .fst = 22ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_any_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_any cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_any(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_eb64legacy(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_eb64legacy(rl);
    if (test)
    {
      COSE_Format_evercddl_any_pretty x = COSE_Format_parse_eb64legacy(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb64legacy_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (23ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_any(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_eb16_pretty0(COSE_Format_evercddl_any_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_any_pretty
COSE_Format_evercddl_eb16_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

COSE_Format_evercddl_any
COSE_Format_evercddl_eb16_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_any_pretty COSE_Format_parse_eb16(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_any res = COSE_Format_parse_any(cpl);
  COSE_Format_evercddl_any res1 = res;
  COSE_Format_evercddl_any_pretty res2 = COSE_Format_evercddl_eb16_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_eb16(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_any c_ = COSE_Format_evercddl_eb16_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_any_pretty c_1 = { .fst = 23ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_any_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_any cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_any(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_eb16_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_eb16(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb16_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_eb16(rl);
    if (test)
    {
      COSE_Format_evercddl_any_pretty x = COSE_Format_parse_eb16(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_eb16_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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
  uint8_t k = cbor_det_major_type(c);
  if (k == CBOR_MAJOR_TYPE_TAGGED)
  {
    uint64_t tag_ = cbor_det_get_tagged_tag(c);
    if (55799ULL == tag_)
    {
      cbor_det_t c_ = cbor_det_get_tagged_payload(c);
      bool res = COSE_Format_validate_any(c_);
      return res;
    }
    else
      return false;
  }
  else
    return false;
}

bool COSE_Format_uu___is_Mkevercddl_cborany_pretty0(COSE_Format_evercddl_any_pretty projectee)
{
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

COSE_Format_evercddl_any_pretty
COSE_Format_evercddl_cborany_pretty_right(COSE_Format_evercddl_any x1)
{
  return x1;
}

COSE_Format_evercddl_any
COSE_Format_evercddl_cborany_pretty_left(COSE_Format_evercddl_any_pretty x3)
{
  return x3;
}

COSE_Format_evercddl_any_pretty COSE_Format_parse_cborany(cbor_det_t c)
{
  cbor_det_t cpl = cbor_det_get_tagged_payload(c);
  COSE_Format_evercddl_any res = COSE_Format_parse_any(cpl);
  COSE_Format_evercddl_any res1 = res;
  COSE_Format_evercddl_any_pretty res2 = COSE_Format_evercddl_cborany_pretty_right(res1);
  return res2;
}

size_t
COSE_Format_serialize_cborany(
  COSE_Format_evercddl_any_pretty c,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  COSE_Format_evercddl_any c_ = COSE_Format_evercddl_cborany_pretty_left(c);
  __uint64_t_COSE_Format_evercddl_any_pretty c_1 = { .fst = 55799ULL, .snd = c_ };
  __uint64_t_COSE_Format_evercddl_any_pretty _letpattern = c_1;
  uint64_t ctag = _letpattern.fst;
  COSE_Format_evercddl_any cpayload = _letpattern.snd;
  size_t aout_len = len__uint8_t(out);
  uint8_t *aout = slice_to_arrayptr_intro__uint8_t(out);
  size_t res0 = cbor_det_serialize_tag_to_array(ctag, aout, aout_len);
  size_t tsz = res0;
  size_t res;
  if (tsz == (size_t)0U)
    res = (size_t)0U;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(out, tsz);
    Pulse_Lib_Slice_slice__uint8_t out2 = _letpattern1.snd;
    size_t psz = COSE_Format_serialize_any(cpayload, out2);
    if (psz == (size_t)0U)
      res = (size_t)0U;
    else
      res = tsz + psz;
  }
  size_t res1 = res;
  return res1;
}

FStar_Pervasives_Native_option___COSE_Format_evercddl_cborany_pretty___Pulse_Lib_Slice_slice_uint8_t_
COSE_Format_validate_and_parse_cborany(Pulse_Lib_Slice_slice__uint8_t s)
{
  size_t len = len__uint8_t(s);
  uint8_t *a0 = slice_to_arrayptr_intro__uint8_t(s);
  uint8_t *a1 = a0;
  size_t res = cbor_det_validate(a1, len);
  size_t len0 = res;
  option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_ q;
  if (len0 == (size_t)0U)
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(s, len0);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    size_t len1 = len__uint8_t(input2);
    uint8_t *a = slice_to_arrayptr_intro__uint8_t(input2);
    uint8_t *a0 = a;
    cbor_det_t res = cbor_det_parse(a0, len1);
    cbor_det_t res0 = res;
    q =
      (
        (option___CBOR_Pulse_API_Det_Type_cbor_det_t___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = rem }
        }
      );
  }
  if (q.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___COSE_Format_evercddl_cborany_pretty___Pulse_Lib_Slice_slice_uint8_t_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (q.tag == FStar_Pervasives_Native_Some)
  {
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t rlrem = q.v;
    __CBOR_Pulse_API_Det_Type_cbor_det_t_Pulse_Lib_Slice_slice_uint8_t _letpattern = rlrem;
    cbor_det_t rl = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = _letpattern.snd;
    bool test = COSE_Format_validate_cborany(rl);
    if (test)
    {
      COSE_Format_evercddl_any_pretty x = COSE_Format_parse_cborany(rl);
      return
        (
          (FStar_Pervasives_Native_option___COSE_Format_evercddl_cborany_pretty___Pulse_Lib_Slice_slice_uint8_t_){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = rem }
          }
        );
    }
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




#include "internal/CBORDet.h"

#include "CBORDetType.h"

static void
Pulse_Lib_Slice_copy__uint8_t(
  CBOR_Pulse_Raw_Slice_byte_slice dst,
  CBOR_Pulse_Raw_Slice_byte_slice src
)
{
  memcpy(dst.elt, src.elt, src.len * sizeof (uint8_t));
}

static void
CBOR_Pulse_Raw_Format_Match_cbor_match_serialized_payload_array_copy(
  CBOR_Pulse_Raw_Slice_byte_slice c,
  CBOR_Pulse_Raw_Slice_byte_slice c_
)
{
  Pulse_Lib_Slice_copy__uint8_t(c_, c);
}

static void
CBOR_Pulse_Raw_Format_Match_cbor_match_serialized_payload_map_copy(
  CBOR_Pulse_Raw_Slice_byte_slice c,
  CBOR_Pulse_Raw_Slice_byte_slice c_
)
{
  Pulse_Lib_Slice_copy__uint8_t(c_, c);
}

static void
CBOR_Pulse_Raw_Format_Match_cbor_match_serialized_payload_tagged_copy(
  CBOR_Pulse_Raw_Slice_byte_slice c,
  CBOR_Pulse_Raw_Slice_byte_slice c_
)
{
  Pulse_Lib_Slice_copy__uint8_t(c_, c);
}

static size_t Pulse_Lib_Slice_len__uint8_t(CBOR_Pulse_Raw_Slice_byte_slice s)
{
  return s.len;
}

static CBOR_Pulse_Raw_Slice_byte_slice
Pulse_Lib_Slice_from_array__uint8_t(uint8_t *a, size_t alen)
{
  return ((CBOR_Pulse_Raw_Slice_byte_slice){ .elt = a, .len = alen });
}

static size_t
Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s
)
{
  return s.len;
}

static cbor_raw
Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw a,
  size_t i
)
{
  return a.elt[i];
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_Type_cbor_raw(cbor_raw *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw){ .elt = a, .len = alen });
}

static size_t
Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry s
)
{
  return s.len;
}

static cbor_map_entry
Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a,
  size_t i
)
{
  return a.elt[i];
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(cbor_map_entry *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry){ .elt = a, .len = alen });
}

cbor_freeable cbor_copy0_with_depth(cbor_raw x)
{
  if (x.tag == CBOR_Case_Int)
  {
    uint8_t ty;
    if (x.tag == CBOR_Case_Int)
      ty = x.case_CBOR_Case_Int.cbor_int_type;
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 w;
    if (x.tag == CBOR_Case_Int)
    {
      cbor_int c_ = x.case_CBOR_Case_Int;
      w = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
    }
    else
      w =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Int,
            {
              .case_CBOR_Case_Int = {
                .cbor_int_type = ty,
                .cbor_int_size = w.size,
                .cbor_int_value = w.value
              }
            }
          },
          .footprint = { .tag = CBOR_Copy_Unit }
        }
      );
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    uint8_t ite;
    if (x.tag == CBOR_Case_Simple)
      ite = x.case_CBOR_Case_Simple;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_freeable){
          .cbor = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = ite } },
          .footprint = { .tag = CBOR_Copy_Unit }
        }
      );
  }
  else if (x.tag == CBOR_Case_String)
  {
    uint8_t ty;
    if (x.tag == CBOR_Case_String)
      ty = x.case_CBOR_Case_String.cbor_string_type;
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (x.tag == CBOR_Case_String)
    {
      cbor_string c_ = x.case_CBOR_Case_String;
      len =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_string_size,
            .value = (uint64_t)Pulse_Lib_Slice_len__uint8_t(c_.cbor_string_ptr)
          }
        );
    }
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Pulse_Raw_Slice_byte_slice pl;
    if (x.tag == CBOR_Case_String)
      pl = x.case_CBOR_Case_String.cbor_string_ptr;
    else
      pl =
        KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
          "unreachable (pattern matches are exhaustive in F*)");
    size_t len_sz = Pulse_Lib_Slice_len__uint8_t(pl);
    KRML_CHECK_SIZE(sizeof (uint8_t), len_sz);
    uint8_t *v_ = KRML_HOST_CALLOC(len_sz, sizeof (uint8_t));
    CBOR_Pulse_Raw_Slice_byte_slice s_ = Pulse_Lib_Slice_from_array__uint8_t(v_, len_sz);
    Pulse_Lib_Slice_copy__uint8_t(s_, pl);
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_String,
            {
              .case_CBOR_Case_String = {
                .cbor_string_type = ty,
                .cbor_string_size = len.size,
                .cbor_string_ptr = s_
              }
            }
          },
          .footprint = { .tag = CBOR_Copy_Bytes, { .case_CBOR_Copy_Bytes = v_ } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Tagged)
  {
    cbor_tagged a = x.case_CBOR_Case_Tagged;
    CBOR_Spec_Raw_Base_raw_uint64 tag = a.cbor_tagged_tag;
    cbor_freeable cpl_ = cbor_copy0_with_depth(a.cbor_tagged_ptr[0U]);
    cbor_raw *b = KRML_HOST_MALLOC(sizeof (cbor_raw));
    if (b != NULL)
      b[0U] = cpl_.cbor;
    cbor_freeable0 *buf = KRML_HOST_MALLOC(sizeof (cbor_freeable0));
    if (buf != NULL)
      buf[0U] = cpl_.footprint;
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Tagged,
            { .case_CBOR_Case_Tagged = { .cbor_tagged_tag = tag, .cbor_tagged_ptr = b } }
          },
          .footprint = {
            .tag = CBOR_Copy_Box,
            { .case_CBOR_Copy_Box = { .box_cbor = b, .box_footprint = buf } }
          }
        }
      );
  }
  else if (x.tag == CBOR_Case_Array)
  {
    cbor_array a1;
    if (x.tag == CBOR_Case_Array)
      a1 = x.case_CBOR_Case_Array;
    else
      a1 = KRML_EABORT(cbor_array, "unreachable (pattern matches are exhaustive in F*)");
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw ar = a1.cbor_array_ptr;
    size_t len = Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(ar);
    KRML_CHECK_SIZE(sizeof (cbor_raw), len);
    cbor_raw *v_ = KRML_HOST_MALLOC(sizeof (cbor_raw) * len);
    if (v_ != NULL)
      for (uint32_t _i = 0U; _i < len; ++_i)
        v_[_i] = ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } });
    KRML_CHECK_SIZE(sizeof (cbor_freeable0), len);
    cbor_freeable0 *vf = KRML_HOST_MALLOC(sizeof (cbor_freeable0) * len);
    if (vf != NULL)
      for (uint32_t _i = 0U; _i < len; ++_i)
        vf[_i] = ((cbor_freeable0){ .tag = CBOR_Copy_Unit });
    size_t pi = (size_t)0U;
    while (pi < len)
    {
      size_t i = pi;
      cbor_freeable
      c_ =
        cbor_copy0_with_depth(Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(ar, i));
      v_[i] = c_.cbor;
      vf[i] = c_.footprint;
      pi = i + (size_t)1U;
    }
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Array,
            {
              .case_CBOR_Case_Array = {
                .cbor_array_length_size = a1.cbor_array_length_size,
                .cbor_array_ptr = Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_Type_cbor_raw(v_, len)
              }
            }
          },
          .footprint = {
            .tag = CBOR_Copy_Array,
            {
              .case_CBOR_Copy_Array = { .array_cbor = v_, .array_footprint = vf, .array_len = len }
            }
          }
        }
      );
  }
  else if (x.tag == CBOR_Case_Map)
  {
    cbor_map a1;
    if (x.tag == CBOR_Case_Map)
      a1 = x.case_CBOR_Case_Map;
    else
      a1 = KRML_EABORT(cbor_map, "unreachable (pattern matches are exhaustive in F*)");
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry ar = a1.cbor_map_ptr;
    size_t len = Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(ar);
    KRML_CHECK_SIZE(sizeof (cbor_map_entry), len);
    cbor_map_entry *v_ = KRML_HOST_MALLOC(sizeof (cbor_map_entry) * len);
    if (v_ != NULL)
      for (uint32_t _i = 0U; _i < len; ++_i)
        v_[_i] =
          (
            (cbor_map_entry){
              .cbor_map_entry_key = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } },
              .cbor_map_entry_value = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } }
            }
          );
    KRML_CHECK_SIZE(sizeof (cbor_freeable_map_entry), len);
    cbor_freeable_map_entry *vf = KRML_HOST_MALLOC(sizeof (cbor_freeable_map_entry) * len);
    if (vf != NULL)
      for (uint32_t _i = 0U; _i < len; ++_i)
        vf[_i] =
          (
            (cbor_freeable_map_entry){
              .map_entry_key = { .tag = CBOR_Copy_Unit },
              .map_entry_value = { .tag = CBOR_Copy_Unit }
            }
          );
    size_t pi = (size_t)0U;
    while (pi < len)
    {
      size_t i = pi;
      cbor_map_entry c = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(ar, i);
      cbor_freeable key_ = cbor_copy0_with_depth(c.cbor_map_entry_key);
      cbor_freeable value_ = cbor_copy0_with_depth(c.cbor_map_entry_value);
      v_[i] =
        ((cbor_map_entry){ .cbor_map_entry_key = key_.cbor, .cbor_map_entry_value = value_.cbor });
      vf[i] =
        (
          (cbor_freeable_map_entry){
            .map_entry_key = key_.footprint,
            .map_entry_value = value_.footprint
          }
        );
      pi = i + (size_t)1U;
    }
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Map,
            {
              .case_CBOR_Case_Map = {
                .cbor_map_length_size = a1.cbor_map_length_size,
                .cbor_map_ptr = Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(v_,
                  len)
              }
            }
          },
          .footprint = {
            .tag = CBOR_Copy_Map,
            { .case_CBOR_Copy_Map = { .map_cbor = v_, .map_footprint = vf, .map_len = len } }
          }
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Array)
  {
    cbor_serialized a = x.case_CBOR_Case_Serialized_Array;
    size_t len = Pulse_Lib_Slice_len__uint8_t(a.cbor_serialized_payload);
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t *v_ = KRML_HOST_CALLOC(len, sizeof (uint8_t));
    CBOR_Pulse_Raw_Slice_byte_slice s_ = Pulse_Lib_Slice_from_array__uint8_t(v_, len);
    CBOR_Pulse_Raw_Format_Match_cbor_match_serialized_payload_array_copy(a.cbor_serialized_payload,
      s_);
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Serialized_Array,
            {
              .case_CBOR_Case_Serialized_Array = {
                .cbor_serialized_header = a.cbor_serialized_header,
                .cbor_serialized_payload = s_
              }
            }
          },
          .footprint = { .tag = CBOR_Copy_Bytes, { .case_CBOR_Copy_Bytes = v_ } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Map)
  {
    cbor_serialized a = x.case_CBOR_Case_Serialized_Map;
    size_t len = Pulse_Lib_Slice_len__uint8_t(a.cbor_serialized_payload);
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t *v_ = KRML_HOST_CALLOC(len, sizeof (uint8_t));
    CBOR_Pulse_Raw_Slice_byte_slice s_ = Pulse_Lib_Slice_from_array__uint8_t(v_, len);
    CBOR_Pulse_Raw_Format_Match_cbor_match_serialized_payload_map_copy(a.cbor_serialized_payload,
      s_);
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Serialized_Map,
            {
              .case_CBOR_Case_Serialized_Map = {
                .cbor_serialized_header = a.cbor_serialized_header,
                .cbor_serialized_payload = s_
              }
            }
          },
          .footprint = { .tag = CBOR_Copy_Bytes, { .case_CBOR_Copy_Bytes = v_ } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Tagged)
  {
    cbor_serialized a = x.case_CBOR_Case_Serialized_Tagged;
    size_t len = Pulse_Lib_Slice_len__uint8_t(a.cbor_serialized_payload);
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t *v_ = KRML_HOST_CALLOC(len, sizeof (uint8_t));
    CBOR_Pulse_Raw_Slice_byte_slice s_ = Pulse_Lib_Slice_from_array__uint8_t(v_, len);
    CBOR_Pulse_Raw_Format_Match_cbor_match_serialized_payload_tagged_copy(a.cbor_serialized_payload,
      s_);
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Serialized_Tagged,
            {
              .case_CBOR_Case_Serialized_Tagged = {
                .cbor_serialized_header = a.cbor_serialized_header,
                .cbor_serialized_payload = s_
              }
            }
          },
          .footprint = { .tag = CBOR_Copy_Bytes, { .case_CBOR_Copy_Bytes = v_ } }
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

static cbor_freeable cbor_copy0(cbor_raw x)
{
  return cbor_copy0_with_depth(x);
}

void cbor_free_(cbor_freeable0 x)
{
  if (!(x.tag == CBOR_Copy_Unit))
  {
    if (x.tag == CBOR_Copy_Bytes)
      KRML_HOST_FREE(x.case_CBOR_Copy_Bytes);
    else if (x.tag == CBOR_Copy_Box)
    {
      cbor_freeable_box b = x.case_CBOR_Copy_Box;
      KRML_HOST_FREE(b.box_cbor);
      cbor_free_(b.box_footprint[0U]);
      KRML_HOST_FREE(b.box_footprint);
    }
    else if (x.tag == CBOR_Copy_Array)
    {
      cbor_freeable_array a = x.case_CBOR_Copy_Array;
      KRML_HOST_FREE(a.array_cbor);
      size_t len = a.array_len;
      size_t pi = (size_t)0U;
      while (pi < len)
      {
        size_t i = pi;
        cbor_free_(a.array_footprint[i]);
        pi = i + (size_t)1U;
      }
      KRML_HOST_FREE(a.array_footprint);
    }
    else if (x.tag == CBOR_Copy_Map)
    {
      cbor_freeable_map a = x.case_CBOR_Copy_Map;
      KRML_HOST_FREE(a.map_cbor);
      size_t len = a.map_len;
      size_t pi = (size_t)0U;
      while (pi < len)
      {
        size_t i = pi;
        cbor_freeable_map_entry x_ = a.map_footprint[i];
        cbor_free_(x_.map_entry_key);
        cbor_free_(x_.map_entry_value);
        pi = i + (size_t)1U;
      }
      KRML_HOST_FREE(a.map_footprint);
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

static void cbor_free0(cbor_freeable x)
{
  cbor_free_(x.footprint);
}

static uint8_t LowParse_BitFields_get_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi)
{
  return ((uint32_t)x << (8U - hi) & 0xFFU) >> (8U - hi + lo);
}

static uint8_t
LowParse_BitFields_set_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi, uint8_t v)
{
  return ((uint32_t)x & (~(255U >> (8U - (hi - lo)) << lo) & 0xFFU)) | (uint32_t)v << lo;
}

static uint8_t
Pulse_Lib_Slice_op_Array_Access__uint8_t(CBOR_Pulse_Raw_Slice_byte_slice a, size_t i)
{
  return a.elt[i];
}

static bool CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(CBOR_Pulse_Raw_Slice_byte_slice s)
{
  bool pres = true;
  size_t pi = (size_t)0U;
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  while (pres && pi < len)
  {
    size_t i = pi;
    uint8_t byte1 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s, i);
    size_t i1 = i + (size_t)1U;
    if (byte1 <= 0x7fU)
      pi = i1;
    else if (i1 == len)
      pres = false;
    else
    {
      uint8_t byte2 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s, i1);
      size_t i2 = i1 + (size_t)1U;
      if (0xc2U <= byte1 && byte1 <= 0xdfU && 0x80U <= byte2 && byte2 <= 0xbfU)
        pi = i2;
      else if (i2 == len)
        pres = false;
      else
      {
        uint8_t byte3 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s, i2);
        size_t i3 = i2 + (size_t)1U;
        if (!(0x80U <= byte3 && byte3 <= 0xbfU))
          pres = false;
        else if (byte1 == 0xe0U)
          if (0xa0U <= byte2 && byte2 <= 0xbfU)
            pi = i3;
          else
            pres = false;
        else if (byte1 == 0xedU)
          if (0x80U <= byte2 && byte2 <= 0x9fU)
            pi = i3;
          else
            pres = false;
        else if (0xe1U <= byte1 && byte1 <= 0xefU && 0x80U <= byte2 && byte2 <= 0xbfU)
          pi = i3;
        else if (i3 == len)
          pres = false;
        else
        {
          uint8_t byte4 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s, i3);
          size_t i4 = i3 + (size_t)1U;
          if (!(0x80U <= byte4 && byte4 <= 0xbfU))
            pres = false;
          else if (byte1 == 0xf0U && 0x90U <= byte2 && byte2 <= 0xbfU)
            pi = i4;
          else if (0xf1U <= byte1 && byte1 <= 0xf3U && 0x80U <= byte2 && byte2 <= 0xbfU)
            pi = i4;
          else if (byte1 == 0xf4U && 0x80U <= byte2 && byte2 <= 0x8fU)
            pi = i4;
          else
            pres = false;
        }
      }
    }
  }
  return pres;
}

typedef struct CBOR_Spec_Raw_EverParse_initial_byte_t_s
{
  uint8_t major_type;
  uint8_t additional_info;
}
CBOR_Spec_Raw_EverParse_initial_byte_t;

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS (24U)

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_UNASSIGNED_MIN (28U)

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS (25U)

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS (26U)

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS (27U)

#define CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue 0
#define CBOR_Spec_Raw_EverParse_LongArgumentU8 1
#define CBOR_Spec_Raw_EverParse_LongArgumentU16 2
#define CBOR_Spec_Raw_EverParse_LongArgumentU32 3
#define CBOR_Spec_Raw_EverParse_LongArgumentU64 4
#define CBOR_Spec_Raw_EverParse_LongArgumentOther 5

typedef uint8_t CBOR_Spec_Raw_EverParse_long_argument_tags;

typedef struct CBOR_Spec_Raw_EverParse_long_argument_s
{
  CBOR_Spec_Raw_EverParse_long_argument_tags tag;
  union {
    uint8_t case_LongArgumentSimpleValue;
    uint8_t case_LongArgumentU8;
    uint16_t case_LongArgumentU16;
    uint32_t case_LongArgumentU32;
    uint64_t case_LongArgumentU64;
  }
  ;
}
CBOR_Spec_Raw_EverParse_long_argument;

static uint64_t
CBOR_Spec_Raw_EverParse_argument_as_uint64(
  CBOR_Spec_Raw_EverParse_initial_byte_t b,
  CBOR_Spec_Raw_EverParse_long_argument x
)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
    ite =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = 1U,
          .value = (uint64_t)(uint32_t)x.case_LongArgumentU8
        }
      );
  else if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
    ite =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = 2U,
          .value = (uint64_t)(uint32_t)x.case_LongArgumentU16
        }
      );
  else if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
    ite =
      ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)x.case_LongArgumentU32 });
  else if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = x.case_LongArgumentU64 });
  else if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
    ite =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = 0U,
          .value = (uint64_t)(uint32_t)b.additional_info
        }
      );
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

typedef struct
Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument_s
{
  CBOR_Spec_Raw_EverParse_initial_byte_t _1;
  CBOR_Spec_Raw_EverParse_long_argument _2;
}
Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument;

static uint8_t
CBOR_Spec_Raw_EverParse_get_header_major_type(
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h
)
{
  return h._1.major_type;
}

static Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(uint8_t t, CBOR_Spec_Raw_Base_raw_uint64 x)
{
  return
    x.size == 0U ? (
                   (Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
                     ._1 = { .major_type = t, .additional_info = (uint8_t)x.value },
                     ._2 = { .tag = CBOR_Spec_Raw_EverParse_LongArgumentOther }
                   }
                 )
                 : x.size == 1U ? (
                                  (Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
                                    ._1 = {
                                      .major_type = t,
                                      .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS
                                    },
                                    ._2 = {
                                      .tag = CBOR_Spec_Raw_EverParse_LongArgumentU8,
                                      { .case_LongArgumentU8 = (uint8_t)x.value }
                                    }
                                  }
                                )
                                : x.size == 2U ? (
                                                 (Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
                                                   ._1 = {
                                                     .major_type = t,
                                                     .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS
                                                   },
                                                   ._2 = {
                                                     .tag = CBOR_Spec_Raw_EverParse_LongArgumentU16,
                                                     { .case_LongArgumentU16 = (uint16_t)x.value }
                                                   }
                                                 }
                                               )
                                               : x.size == 3U ? (
                                                                (Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
                                                                  ._1 = {
                                                                    .major_type = t,
                                                                    .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS
                                                                  },
                                                                  ._2 = {
                                                                    .tag = CBOR_Spec_Raw_EverParse_LongArgumentU32,
                                                                    {
                                                                      .case_LongArgumentU32 = (uint32_t)x.value
                                                                    }
                                                                  }
                                                                }
                                                              )
                                                              : (
                                                                (Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
                                                                  ._1 = {
                                                                    .major_type = t,
                                                                    .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS
                                                                  },
                                                                  ._2 = {
                                                                    .tag = CBOR_Spec_Raw_EverParse_LongArgumentU64,
                                                                    {
                                                                      .case_LongArgumentU64 = x.value
                                                                    }
                                                                  }
                                                                }
                                                              );
}

static Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
CBOR_Spec_Raw_EverParse_simple_value_as_argument(uint8_t x)
{
  return
    x <= MAX_SIMPLE_VALUE_ADDITIONAL_INFO ? (
                                            (Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
                                              ._1 = {
                                                .major_type = CBOR_MAJOR_TYPE_SIMPLE_VALUE,
                                                .additional_info = x
                                              },
                                              ._2 = {
                                                .tag = CBOR_Spec_Raw_EverParse_LongArgumentOther
                                              }
                                            }
                                          )
                                          : (
                                            (Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
                                              ._1 = {
                                                .major_type = CBOR_MAJOR_TYPE_SIMPLE_VALUE,
                                                .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS
                                              },
                                              ._2 = {
                                                .tag = CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue,
                                                { .case_LongArgumentSimpleValue = x }
                                              }
                                            }
                                          );
}

static CBOR_Spec_Raw_EverParse_initial_byte_t
CBOR_Pulse_Raw_EverParse_Format_read_initial_byte_t(CBOR_Pulse_Raw_Slice_byte_slice input)
{
  uint8_t x = Pulse_Lib_Slice_op_Array_Access__uint8_t(input, (size_t)0U);
  return
    (
      (CBOR_Spec_Raw_EverParse_initial_byte_t){
        .major_type = LowParse_BitFields_get_bitfield_gen8(x, 5U, 8U),
        .additional_info = LowParse_BitFields_get_bitfield_gen8(x, 0U, 5U)
      }
    );
}

typedef struct
FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice_s
{
  CBOR_Pulse_Raw_Slice_byte_slice _1;
  CBOR_Pulse_Raw_Slice_byte_slice _2;
}
FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice;

static FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
Pulse_Lib_Slice_split__uint8_t(CBOR_Pulse_Raw_Slice_byte_slice s, size_t i)
{
  return
    (
      (FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice){
        ._1 = { .elt = s.elt, .len = i },
        ._2 = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static bool
CBOR_Pulse_Raw_EverParse_Format_validate_header(
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t *poffset
)
{
  size_t offset = poffset[0U];
  size_t offset1 = poffset[0U];
  size_t offset2 = poffset[0U];
  bool ite0;
  if (Pulse_Lib_Slice_len__uint8_t(input) - offset2 < (size_t)1U)
    ite0 = false;
  else
  {
    poffset[0U] = offset2 + (size_t)1U;
    ite0 = true;
  }
  bool ite1;
  if (ite0)
  {
    size_t off = poffset[0U];
    CBOR_Spec_Raw_EverParse_initial_byte_t
    x =
      CBOR_Pulse_Raw_EverParse_Format_read_initial_byte_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
            offset1)._2,
          off - offset1)._1);
    ite1 =
      (!(x.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE) ||
        x.additional_info <= CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
      && x.additional_info < CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_UNASSIGNED_MIN;
  }
  else
    ite1 = false;
  if (ite1)
  {
    size_t off = poffset[0U];
    CBOR_Spec_Raw_EverParse_initial_byte_t
    x =
      CBOR_Pulse_Raw_EverParse_Format_read_initial_byte_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
            offset)._2,
          off - offset)._1);
    if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
      if (x.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      {
        size_t offset3 = poffset[0U];
        size_t offset4 = poffset[0U];
        bool ite;
        if (Pulse_Lib_Slice_len__uint8_t(input) - offset4 < (size_t)1U)
          ite = false;
        else
        {
          poffset[0U] = offset4 + (size_t)1U;
          ite = true;
        }
        if (ite)
        {
          size_t off1 = poffset[0U];
          return
            MIN_SIMPLE_VALUE_LONG_ARGUMENT <=
              Pulse_Lib_Slice_op_Array_Access__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
                    offset3)._2,
                  off1 - offset3)._1,
                (size_t)0U);
        }
        else
          return false;
      }
      else
      {
        size_t offset3 = poffset[0U];
        if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < (size_t)1U)
          return false;
        else
        {
          poffset[0U] = offset3 + (size_t)1U;
          return true;
        }
      }
    else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    {
      size_t offset3 = poffset[0U];
      if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < (size_t)2U)
        return false;
      else
      {
        poffset[0U] = offset3 + (size_t)2U;
        return true;
      }
    }
    else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    {
      size_t offset3 = poffset[0U];
      if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < (size_t)4U)
        return false;
      else
      {
        poffset[0U] = offset3 + (size_t)4U;
        return true;
      }
    }
    else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    {
      size_t offset3 = poffset[0U];
      if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < (size_t)8U)
        return false;
      else
      {
        poffset[0U] = offset3 + (size_t)8U;
        return true;
      }
    }
    else
      return true;
  }
  else
    return false;
}

static Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
CBOR_Pulse_Raw_EverParse_Format_read_header(CBOR_Pulse_Raw_Slice_byte_slice input)
{
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut = Pulse_Lib_Slice_split__uint8_t(input, (size_t)1U);
  CBOR_Pulse_Raw_Slice_byte_slice input2 = scrut._2;
  CBOR_Spec_Raw_EverParse_initial_byte_t
  x1 = CBOR_Pulse_Raw_EverParse_Format_read_initial_byte_t(scrut._1);
  CBOR_Spec_Raw_EverParse_long_argument ite;
  if (x1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    if (x1.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      ite =
        (
          (CBOR_Spec_Raw_EverParse_long_argument){
            .tag = CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue,
            {
              .case_LongArgumentSimpleValue = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2,
                (size_t)0U)
            }
          }
        );
    else
      ite =
        (
          (CBOR_Spec_Raw_EverParse_long_argument){
            .tag = CBOR_Spec_Raw_EverParse_LongArgumentU8,
            { .case_LongArgumentU8 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)0U) }
          }
        );
  else if (x1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
  {
    uint8_t last = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)1U);
    ite =
      (
        (CBOR_Spec_Raw_EverParse_long_argument){
          .tag = CBOR_Spec_Raw_EverParse_LongArgumentU16,
          {
            .case_LongArgumentU16 = (uint32_t)(uint16_t)(uint32_t)last +
              (uint32_t)(uint16_t)(uint32_t)Pulse_Lib_Slice_op_Array_Access__uint8_t(input2,
                (size_t)0U)
              * 256U
          }
        }
      );
  }
  else if (x1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
  {
    uint8_t last = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)3U);
    uint8_t last1 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)3U - (size_t)1U);
    uint8_t
    last2 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)3U - (size_t)1U - (size_t)1U);
    ite =
      (
        (CBOR_Spec_Raw_EverParse_long_argument){
          .tag = CBOR_Spec_Raw_EverParse_LongArgumentU32,
          {
            .case_LongArgumentU32 = (uint32_t)last +
              ((uint32_t)last1 +
                ((uint32_t)last2 +
                  (uint32_t)Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)0U) * 256U)
                * 256U)
              * 256U
          }
        }
      );
  }
  else if (x1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
  {
    uint8_t last = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)7U);
    uint8_t last1 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)7U - (size_t)1U);
    uint8_t
    last2 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)7U - (size_t)1U - (size_t)1U);
    uint8_t
    last3 =
      Pulse_Lib_Slice_op_Array_Access__uint8_t(input2,
        (size_t)7U - (size_t)1U - (size_t)1U - (size_t)1U);
    size_t pos_4 = (size_t)7U - (size_t)1U - (size_t)1U - (size_t)1U - (size_t)1U;
    uint8_t last4 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, pos_4);
    size_t pos_5 = pos_4 - (size_t)1U;
    uint8_t last5 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, pos_5);
    uint8_t last6 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, pos_5 - (size_t)1U);
    ite =
      (
        (CBOR_Spec_Raw_EverParse_long_argument){
          .tag = CBOR_Spec_Raw_EverParse_LongArgumentU64,
          {
            .case_LongArgumentU64 = (uint64_t)(uint32_t)last +
              ((uint64_t)(uint32_t)last1 +
                ((uint64_t)(uint32_t)last2 +
                  ((uint64_t)(uint32_t)last3 +
                    ((uint64_t)(uint32_t)last4 +
                      ((uint64_t)(uint32_t)last5 +
                        ((uint64_t)(uint32_t)last6 +
                          (uint64_t)(uint32_t)Pulse_Lib_Slice_op_Array_Access__uint8_t(input2,
                            (size_t)0U)
                          * 256ULL)
                        * 256ULL)
                      * 256ULL)
                    * 256ULL)
                  * 256ULL)
                * 256ULL)
              * 256ULL
          }
        }
      );
  }
  else
    ite =
      ((CBOR_Spec_Raw_EverParse_long_argument){ .tag = CBOR_Spec_Raw_EverParse_LongArgumentOther });
  return
    (
      (Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
        ._1 = x1,
        ._2 = ite
      }
    );
}

static size_t
CBOR_Pulse_Raw_EverParse_Format_jump_header(
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t offset
)
{
  size_t off1 = offset + (size_t)1U;
  CBOR_Spec_Raw_EverParse_initial_byte_t
  x =
    CBOR_Pulse_Raw_EverParse_Format_read_initial_byte_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
          offset)._2,
        off1 - offset)._1);
  return
    x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS ? off1 +
                                                                                        (size_t)1U
                                                                                      : x.additional_info
                                                                                      ==
                                                                                        CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS ? off1
                                                                                                                                                      +
                                                                                                                                                        (size_t)2U
                                                                                                                                                      : x.additional_info
                                                                                                                                                      ==
                                                                                                                                                        CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS ? off1
                                                                                                                                                                                                                      +
                                                                                                                                                                                                                        (size_t)4U
                                                                                                                                                                                                                      : x.additional_info
                                                                                                                                                                                                                      ==
                                                                                                                                                                                                                        CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS ? off1
                                                                                                                                                                                                                                                                                      +
                                                                                                                                                                                                                                                                                        (size_t)8U
                                                                                                                                                                                                                                                                                      : off1;
}

static bool
CBOR_Pulse_Raw_EverParse_Format_validate_recursive_step_count_leaf(
  CBOR_Pulse_Raw_Slice_byte_slice a,
  size_t bound,
  size_t *prem
)
{
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h =
    CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(a,
        CBOR_Pulse_Raw_EverParse_Format_jump_header(a, (size_t)0U))._1);
  uint8_t typ = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
  if (typ == CBOR_MAJOR_TYPE_ARRAY)
  {
    uint64_t arg64 = CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
    if
    (
      bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U >= (size_t)16U ||
        arg64 <= bound
    )
    {
      prem[0U] = (size_t)arg64;
      return false;
    }
    else
      return true;
  }
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t arg64 = CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
    if
    (
      bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U >= (size_t)16U ||
        arg64 <= bound
    )
    {
      size_t arg = (size_t)arg64;
      if (bound - arg < arg)
        return true;
      else
      {
        prem[0U] = arg + arg;
        return false;
      }
    }
    else
      return true;
  }
  else if (typ == CBOR_MAJOR_TYPE_TAGGED)
  {
    prem[0U] = (size_t)1U;
    return false;
  }
  else
  {
    prem[0U] = (size_t)0U;
    return false;
  }
}

static bool
CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item(
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t *poffset
)
{
  size_t pn = (size_t)1U;
  bool pres = true;
  while (pres && pn > (size_t)0U)
  {
    size_t off = poffset[0U];
    size_t n = pn;
    if (n > Pulse_Lib_Slice_len__uint8_t(input) - off)
      pres = false;
    else
    {
      size_t offset = poffset[0U];
      bool ite0;
      if (CBOR_Pulse_Raw_EverParse_Format_validate_header(input, poffset))
      {
        size_t off1 = poffset[0U];
        Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
        x =
          CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
                offset)._2,
              off1 - offset)._1);
        CBOR_Spec_Raw_EverParse_initial_byte_t b = x._1;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        {
          size_t offset1 = poffset[0U];
          size_t offset2 = poffset[0U];
          size_t remaining = Pulse_Lib_Slice_len__uint8_t(input) - offset2;
          bool ite1;
          if
          (
            remaining / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U >=
              (size_t)16U
          )
            ite1 = true;
          else
          {
            uint64_t b64 = (uint64_t)remaining;
            ite1 = CBOR_Spec_Raw_EverParse_argument_as_uint64(x._1, x._2) <= b64;
          }
          bool ite;
          if (ite1)
          {
            poffset[0U] = offset2 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x._1, x._2);
            ite = true;
          }
          else
            ite = false;
          if (ite)
          {
            size_t off2 = poffset[0U];
            CBOR_Pulse_Raw_Slice_byte_slice
            x1 =
              Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, offset1)._2,
                off2 - offset1)._1;
            if (CBOR_Spec_Raw_EverParse_get_header_major_type(x) == CBOR_MAJOR_TYPE_BYTE_STRING)
              ite0 = true;
            else
              ite0 = CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(x1);
          }
          else
            ite0 = false;
        }
        else
          ite0 = true;
      }
      else
        ite0 = false;
      if (!ite0)
        pres = false;
      else
      {
        size_t offset1 = poffset[0U];
        CBOR_Pulse_Raw_Slice_byte_slice
        input1 =
          Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, off)._2,
            offset1 - off)._1;
        size_t bound = Pulse_Lib_Slice_len__uint8_t(input) - off - n;
        bool
        res2 =
          CBOR_Pulse_Raw_EverParse_Format_validate_recursive_step_count_leaf(input1,
            bound,
            &pn);
        size_t count = pn;
        if (res2 || count > bound)
          pres = false;
        else
          pn = n - (size_t)1U + count;
      }
    }
  }
  return pres;
}

static size_t
CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h
)
{
  uint8_t typ = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
  if (typ == CBOR_MAJOR_TYPE_ARRAY)
    return (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    size_t arg = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
    return arg + arg;
  }
  else
    return typ == CBOR_MAJOR_TYPE_TAGGED ? (size_t)1U : (size_t)0U;
}

static size_t
CBOR_Pulse_Raw_EverParse_Format_jump_recursive_step_count_leaf(
  CBOR_Pulse_Raw_Slice_byte_slice a
)
{
  return
    CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(a,
          CBOR_Pulse_Raw_EverParse_Format_jump_header(a, (size_t)0U))._1));
}

static size_t
CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t offset
)
{
  size_t poffset = offset;
  size_t pn = (size_t)1U;
  while (pn > (size_t)0U)
  {
    size_t off = poffset;
    size_t off1 = CBOR_Pulse_Raw_EverParse_Format_jump_header(input, off);
    Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    x =
      CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
            off)._2,
          off1 - off)._1);
    CBOR_Spec_Raw_EverParse_initial_byte_t b = x._1;
    size_t off11;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
      off11 = off1 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x._1, x._2);
    else
      off11 = off1;
    poffset = off11;
    CBOR_Pulse_Raw_Slice_byte_slice
    input1 =
      Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, off)._2,
        off11 - off)._1;
    size_t n = pn;
    size_t unused = Pulse_Lib_Slice_len__uint8_t(input) - off11;
    KRML_MAYBE_UNUSED_VAR(unused);
    pn = n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Format_jump_recursive_step_count_leaf(input1);
  }
  return poffset;
}

static int16_t CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(uint8_t x1, uint8_t x2)
{
  return x1 < x2 ? -1 : x1 > x2 ? 1 : 0;
}

static int16_t
CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(
  CBOR_Pulse_Raw_Slice_byte_slice s1,
  CBOR_Pulse_Raw_Slice_byte_slice s2
)
{
  size_t pi1 = (size_t)0U;
  size_t pi2 = (size_t)0U;
  size_t n1 = Pulse_Lib_Slice_len__uint8_t(s1);
  size_t n2 = Pulse_Lib_Slice_len__uint8_t(s2);
  int16_t pres = (size_t)0U < n1 ? (size_t)0U < n2 ? 0 : 1 : (size_t)0U < n2 ? -1 : 0;
  while (pres == 0 && pi1 < n1)
  {
    size_t i1 = pi1;
    uint8_t x1 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s1, i1);
    size_t i2 = pi2;
    int16_t
    c =
      CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(x1,
        Pulse_Lib_Slice_op_Array_Access__uint8_t(s2, i2));
    if (c == 0)
    {
      size_t i1_ = i1 + (size_t)1U;
      size_t i2_ = i2 + (size_t)1U;
      bool ci1_ = i1_ < n1;
      bool ci2_ = i2_ < n2;
      if (ci2_ && !ci1_)
        pres = -1;
      else if (ci1_ && !ci2_)
        pres = 1;
      else
      {
        pi1 = i1_;
        pi2 = i2_;
      }
    }
    else
      pres = c;
  }
  return pres;
}

static cbor_raw
CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(CBOR_Pulse_Raw_Slice_byte_slice input)
{
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  ph =
    {
      ._1 = { .major_type = CBOR_MAJOR_TYPE_SIMPLE_VALUE, .additional_info = 0U },
      ._2 = { .tag = CBOR_Spec_Raw_EverParse_LongArgumentOther }
    };
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut =
    Pulse_Lib_Slice_split__uint8_t(input,
      CBOR_Pulse_Raw_EverParse_Format_jump_header(input, (size_t)0U));
  CBOR_Pulse_Raw_Slice_byte_slice outc = scrut._2;
  ph = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut._1);
  CBOR_Pulse_Raw_Slice_byte_slice pc = outc;
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h = ph;
  uint8_t typ = h._1.major_type;
  if (typ == CBOR_MAJOR_TYPE_UINT64 || typ == CBOR_MAJOR_TYPE_NEG_INT64)
  {
    CBOR_Spec_Raw_Base_raw_uint64 i1;
    if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      i1 =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 1U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU8
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      i1 =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 2U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU16
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      i1 =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 3U,
            .value = (uint64_t)h._2.case_LongArgumentU32
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      i1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h._2.case_LongArgumentU64 });
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      i1 =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 0U,
            .value = (uint64_t)(uint32_t)h._1.additional_info
          }
        );
    else
      i1 =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Int,
          {
            .case_CBOR_Case_Int = {
              .cbor_int_type = typ,
              .cbor_int_size = i1.size,
              .cbor_int_value = i1.value
            }
          }
        }
      );
  }
  else if (typ == CBOR_MAJOR_TYPE_TEXT_STRING || typ == CBOR_MAJOR_TYPE_BYTE_STRING)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 1U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU8
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 2U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU16
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 3U,
            .value = (uint64_t)h._2.case_LongArgumentU32
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h._2.case_LongArgumentU64 });
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 0U,
            .value = (uint64_t)(uint32_t)h._1.additional_info
          }
        );
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_String,
          {
            .case_CBOR_Case_String = {
              .cbor_string_type = typ,
              .cbor_string_size = ite.size,
              .cbor_string_ptr = pc
            }
          }
        }
      );
  }
  else if (typ == CBOR_MAJOR_TYPE_TAGGED)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 1U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU8
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 2U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU16
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 3U,
            .value = (uint64_t)h._2.case_LongArgumentU32
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h._2.case_LongArgumentU64 });
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 0U,
            .value = (uint64_t)(uint32_t)h._1.additional_info
          }
        );
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Tagged,
          {
            .case_CBOR_Case_Serialized_Tagged = {
              .cbor_serialized_header = ite,
              .cbor_serialized_payload = pc
            }
          }
        }
      );
  }
  else if (typ == CBOR_MAJOR_TYPE_ARRAY)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 1U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU8
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 2U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU16
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 3U,
            .value = (uint64_t)h._2.case_LongArgumentU32
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h._2.case_LongArgumentU64 });
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 0U,
            .value = (uint64_t)(uint32_t)h._1.additional_info
          }
        );
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Array,
          {
            .case_CBOR_Case_Serialized_Array = {
              .cbor_serialized_header = ite,
              .cbor_serialized_payload = pc
            }
          }
        }
      );
  }
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 1U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU8
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 2U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU16
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 3U,
            .value = (uint64_t)h._2.case_LongArgumentU32
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h._2.case_LongArgumentU64 });
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 0U,
            .value = (uint64_t)(uint32_t)h._1.additional_info
          }
        );
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Map,
          {
            .case_CBOR_Case_Serialized_Map = {
              .cbor_serialized_header = ite,
              .cbor_serialized_payload = pc
            }
          }
        }
      );
  }
  else
  {
    uint8_t ite;
    if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite = h._1.additional_info;
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
      ite = h._2.case_LongArgumentSimpleValue;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = ite } });
  }
}

static size_t CBOR_Pulse_Raw_Format_Parse_cbor_validate(CBOR_Pulse_Raw_Slice_byte_slice input)
{
  size_t poffset = (size_t)0U;
  if (CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item(input, &poffset))
    return poffset;
  else
    return (size_t)0U;
}

static bool
CBOR_Pulse_Raw_Format_Parse_impl_raw_uint64_optimal(CBOR_Spec_Raw_Base_raw_uint64 x)
{
  return
    x.value <= (uint32_t)MAX_SIMPLE_VALUE_ADDITIONAL_INFO == (x.size == 0U) &&
      (x.size <= 1U ||
        (x.size == 2U ? 256ULL <= x.value
                      : x.size == 3U ? 65536ULL <= x.value : 4294967296ULL <= x.value));
}

static bool
CBOR_Pulse_Raw_Format_Parse_cbor_raw_ints_optimal(CBOR_Pulse_Raw_Slice_byte_slice a)
{
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h =
    CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(a,
        CBOR_Pulse_Raw_EverParse_Format_jump_header(a, (size_t)0U))._1);
  if (CBOR_Spec_Raw_EverParse_get_header_major_type(h) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return true;
  else
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 1U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU8
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 2U,
            .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU16
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 3U,
            .value = (uint64_t)h._2.case_LongArgumentU32
          }
        );
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h._2.case_LongArgumentU64 });
    else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 0U,
            .value = (uint64_t)(uint32_t)h._1.additional_info
          }
        );
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return CBOR_Pulse_Raw_Format_Parse_impl_raw_uint64_optimal(ite);
  }
}

static bool
CBOR_Pulse_Raw_Format_Parse_impl_deterministically_encoded_cbor_map_key_order(
  CBOR_Pulse_Raw_Slice_byte_slice a1,
  CBOR_Pulse_Raw_Slice_byte_slice a2
)
{
  return CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(a1, a2) < 0;
}

static bool CBOR_Pulse_Raw_Format_Parse_cbor_raw_sorted(CBOR_Pulse_Raw_Slice_byte_slice a)
{
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut =
    Pulse_Lib_Slice_split__uint8_t(a,
      CBOR_Pulse_Raw_EverParse_Format_jump_header(a, (size_t)0U));
  CBOR_Pulse_Raw_Slice_byte_slice input2 = scrut._2;
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut._1);
  if (CBOR_Spec_Raw_EverParse_get_header_major_type(h) == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t nbpairs = CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
    if (nbpairs < 2ULL)
      return true;
    else
    {
      CBOR_Spec_Raw_EverParse_initial_byte_t b = h._1;
      size_t ite;
      if
      (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        ite = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
      else
        ite = (size_t)0U;
      CBOR_Pulse_Raw_Slice_byte_slice input3 = Pulse_Lib_Slice_split__uint8_t(input2, ite)._2;
      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
      scrut =
        Pulse_Lib_Slice_split__uint8_t(input3,
          CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(input3, (size_t)0U));
      CBOR_Pulse_Raw_Slice_byte_slice input4 = scrut._2;
      CBOR_Pulse_Raw_Slice_byte_slice pkey = scrut._1;
      uint64_t ppairs = nbpairs - 1ULL;
      CBOR_Pulse_Raw_Slice_byte_slice
      ptail =
        Pulse_Lib_Slice_split__uint8_t(input4,
          CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(input4, (size_t)0U))._2;
      bool pres = true;
      while (pres && ppairs > 0ULL)
      {
        CBOR_Pulse_Raw_Slice_byte_slice tail = ptail;
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
        scrut =
          Pulse_Lib_Slice_split__uint8_t(tail,
            CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(tail, (size_t)0U));
        CBOR_Pulse_Raw_Slice_byte_slice key2 = scrut._1;
        CBOR_Pulse_Raw_Slice_byte_slice tail2 = scrut._2;
        if
        (CBOR_Pulse_Raw_Format_Parse_impl_deterministically_encoded_cbor_map_key_order(pkey, key2))
        {
          CBOR_Pulse_Raw_Slice_byte_slice
          tail_ =
            Pulse_Lib_Slice_split__uint8_t(tail2,
              CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(tail2, (size_t)0U))._2;
          pkey = key2;
          ppairs--;
          ptail = tail_;
        }
        else
          pres = false;
      }
      return pres;
    }
  }
  else
    return true;
}

static size_t
CBOR_Pulse_Raw_Format_Parse_cbor_validate_det_(CBOR_Pulse_Raw_Slice_byte_slice input)
{
  size_t len = CBOR_Pulse_Raw_Format_Parse_cbor_validate(input);
  if (len == (size_t)0U)
    return len;
  else
  {
    CBOR_Pulse_Raw_Slice_byte_slice
    input1 =
      Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, (size_t)0U)._2,
        len - (size_t)0U)._1;
    bool buf = false;
    KRML_HOST_IGNORE(&buf);
    size_t pn = (size_t)1U;
    bool pres = true;
    CBOR_Pulse_Raw_Slice_byte_slice ppi = input1;
    while (pres && pn > (size_t)0U)
    {
      size_t n = pn;
      CBOR_Pulse_Raw_Slice_byte_slice pi = ppi;
      if (!CBOR_Pulse_Raw_Format_Parse_cbor_raw_ints_optimal(pi))
        pres = false;
      else
      {
        size_t off1 = CBOR_Pulse_Raw_EverParse_Format_jump_header(pi, (size_t)0U);
        Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
        x =
          CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(pi,
                (size_t)0U)._2,
              off1 - (size_t)0U)._1);
        CBOR_Spec_Raw_EverParse_initial_byte_t b = x._1;
        size_t ite;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
          ite = off1 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x._1, x._2);
        else
          ite = off1;
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
        scrut = Pulse_Lib_Slice_split__uint8_t(pi, ite);
        CBOR_Pulse_Raw_Slice_byte_slice ph = scrut._1;
        CBOR_Pulse_Raw_Slice_byte_slice pc = scrut._2;
        size_t unused = Pulse_Lib_Slice_len__uint8_t(pc);
        KRML_MAYBE_UNUSED_VAR(unused);
        pn = n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Format_jump_recursive_step_count_leaf(ph);
        ppi = pc;
      }
    }
    if (!pres)
      return (size_t)0U;
    else
    {
      size_t pn1 = (size_t)1U;
      bool pres1 = true;
      CBOR_Pulse_Raw_Slice_byte_slice ppi1 = input1;
      while (pres1 && pn1 > (size_t)0U)
      {
        size_t n = pn1;
        CBOR_Pulse_Raw_Slice_byte_slice pi = ppi1;
        if (!CBOR_Pulse_Raw_Format_Parse_cbor_raw_sorted(pi))
          pres1 = false;
        else
        {
          size_t off1 = CBOR_Pulse_Raw_EverParse_Format_jump_header(pi, (size_t)0U);
          Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
          x =
            CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(pi,
                  (size_t)0U)._2,
                off1 - (size_t)0U)._1);
          CBOR_Spec_Raw_EverParse_initial_byte_t b = x._1;
          size_t ite;
          if
          (
            b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
              b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
          )
            ite = off1 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x._1, x._2);
          else
            ite = off1;
          FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
          scrut = Pulse_Lib_Slice_split__uint8_t(pi, ite);
          CBOR_Pulse_Raw_Slice_byte_slice ph = scrut._1;
          CBOR_Pulse_Raw_Slice_byte_slice pc = scrut._2;
          size_t unused = Pulse_Lib_Slice_len__uint8_t(pc);
          KRML_MAYBE_UNUSED_VAR(unused);
          pn1 = n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Format_jump_recursive_step_count_leaf(ph);
          ppi1 = pc;
        }
      }
      return !pres1 ? (size_t)0U : len;
    }
  }
}

static size_t
CBOR_Pulse_Raw_Format_Parse_cbor_validate_det(CBOR_Pulse_Raw_Slice_byte_slice input)
{
  return CBOR_Pulse_Raw_Format_Parse_cbor_validate_det_(input);
}

static cbor_raw
CBOR_Pulse_Raw_Format_Parse_cbor_parse(CBOR_Pulse_Raw_Slice_byte_slice input, size_t len)
{
  return
    CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
          (size_t)0U)._2,
        len - (size_t)0U)._1);
}

static size_t
CBOR_Pulse_Raw_Format_Parse_cbor_jump(CBOR_Pulse_Raw_Slice_byte_slice input, size_t offset)
{
  return CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(input, offset);
}

#define CBOR_Pulse_Raw_Insert_CFailure 0
#define CBOR_Pulse_Raw_Insert_CInProgress 1
#define CBOR_Pulse_Raw_Insert_CSuccess 2

typedef uint8_t CBOR_Pulse_Raw_Insert_cbor_raw_map_insert_result;

static void
Pulse_Lib_Slice_op_Array_Assignment__uint8_t(
  CBOR_Pulse_Raw_Slice_byte_slice a,
  size_t i,
  uint8_t v
)
{
  a.elt[i] = v;
}

static bool
CBOR_Pulse_Raw_Insert_cbor_raw_map_insert(
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t off2,
  size_t off3
)
{
  size_t poff = (size_t)0U;
  CBOR_Pulse_Raw_Insert_cbor_raw_map_insert_result pres = CBOR_Pulse_Raw_Insert_CInProgress;
  size_t off0 = poff;
  bool cond = pres == CBOR_Pulse_Raw_Insert_CInProgress && off0 < off2;
  while (cond)
  {
    size_t off = poff;
    CBOR_Pulse_Raw_Slice_byte_slice out2kv = Pulse_Lib_Slice_split__uint8_t(out, off)._2;
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
    scrut0 = Pulse_Lib_Slice_split__uint8_t(out2kv, off2 - off);
    CBOR_Pulse_Raw_Slice_byte_slice out2 = scrut0._1;
    CBOR_Pulse_Raw_Slice_byte_slice
    outk = Pulse_Lib_Slice_split__uint8_t(scrut0._2, off3 - off2)._1;
    size_t offk = CBOR_Pulse_Raw_Format_Parse_cbor_jump(out2, (size_t)0U);
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
    scrut = Pulse_Lib_Slice_split__uint8_t(out2, offk);
    CBOR_Pulse_Raw_Slice_byte_slice outvq = scrut._2;
    int16_t c = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(scrut._1, outk);
    if (c < 0)
      poff = off + (offk + CBOR_Pulse_Raw_Format_Parse_cbor_jump(outvq, (size_t)0U));
    else if (c > 0)
    {
      if (!(off2 - off == (size_t)0U || off2 - off == Pulse_Lib_Slice_len__uint8_t(out2kv)))
      {
        size_t pn = Pulse_Lib_Slice_len__uint8_t(out2kv);
        size_t pl = off2 - off;
        while (pl > (size_t)0U)
        {
          size_t l = pl;
          size_t l_ = pn % l;
          pn = l;
          pl = l_;
        }
        size_t d = pn;
        size_t q = Pulse_Lib_Slice_len__uint8_t(out2kv) / d;
        size_t pi = (size_t)0U;
        while (pi < d)
        {
          size_t i = pi;
          uint8_t save = Pulse_Lib_Slice_op_Array_Access__uint8_t(out2kv, i);
          size_t pj = (size_t)0U;
          size_t pidx = i;
          while (pj < q - (size_t)1U)
          {
            size_t j = pj;
            size_t idx = pidx;
            size_t idx_;
            if (idx - (size_t)0U >= Pulse_Lib_Slice_len__uint8_t(out2kv) - (off2 - off))
              idx_ = idx - (Pulse_Lib_Slice_len__uint8_t(out2kv) - (off2 - off));
            else
              idx_ = idx + (off2 - off - (size_t)0U);
            size_t j_ = j + (size_t)1U;
            Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out2kv,
              idx,
              Pulse_Lib_Slice_op_Array_Access__uint8_t(out2kv, idx_));
            pj = j_;
            pidx = idx_;
          }
          Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out2kv, pidx, save);
          pi = i + (size_t)1U;
        }
      }
      pres = CBOR_Pulse_Raw_Insert_CSuccess;
    }
    else
      pres = CBOR_Pulse_Raw_Insert_CFailure;
    size_t off0 = poff;
    cond = pres == CBOR_Pulse_Raw_Insert_CInProgress && off0 < off2;
  }
  switch (pres)
  {
    case CBOR_Pulse_Raw_Insert_CSuccess:
      {
        return true;
      }
    case CBOR_Pulse_Raw_Insert_CFailure:
      {
        return false;
      }
    case CBOR_Pulse_Raw_Insert_CInProgress:
      {
        return true;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static cbor_raw
CBOR_Pulse_Raw_Format_Serialized_cbor_match_serialized_tagged_get_payload(cbor_serialized c)
{
  return CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(c.cbor_serialized_payload);
}

static CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_init(cbor_serialized c)
{
  return
    (
      (CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator){
        .s = c.cbor_serialized_payload,
        .len = c.cbor_serialized_header.value
      }
    );
}

static bool
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator c
)
{
  return c.len == 0ULL;
}

static cbor_raw
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_next_with_depth(
  cbor_det_array_iterator_t *pi,
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator i
)
{
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut =
    Pulse_Lib_Slice_split__uint8_t(i.s,
      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(i.s, (size_t)0U));
  CBOR_Pulse_Raw_Slice_byte_slice s2 = scrut._2;
  cbor_raw res = CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(scrut._1);
  pi[0U] =
    (
      (cbor_det_array_iterator_t){
        .tag = CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = { .s = s2, .len = i.len - 1ULL } }
      }
    );
  return res;
}

static CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_init(cbor_serialized c)
{
  return
    (
      (CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator){
        .s = c.cbor_serialized_payload,
        .len = c.cbor_serialized_header.value
      }
    );
}

static bool
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator c
)
{
  return c.len == 0ULL;
}

static cbor_map_entry
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_next_with_depth(
  cbor_det_map_iterator_t *pi,
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator i
)
{
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut0 =
    Pulse_Lib_Slice_split__uint8_t(i.s,
      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(i.s,
        CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(i.s, (size_t)0U)));
  CBOR_Pulse_Raw_Slice_byte_slice s1 = scrut0._1;
  CBOR_Pulse_Raw_Slice_byte_slice s2 = scrut0._2;
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut =
    Pulse_Lib_Slice_split__uint8_t(s1,
      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(s1, (size_t)0U));
  CBOR_Pulse_Raw_Slice_byte_slice s21 = scrut._2;
  cbor_raw res1 = CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(scrut._1);
  cbor_map_entry
  res =
    {
      .cbor_map_entry_key = res1,
      .cbor_map_entry_value = CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(s21)
    };
  pi[0U] =
    (
      (cbor_det_map_iterator_t){
        .tag = CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = { .s = s2, .len = i.len - 1ULL } }
      }
    );
  return res;
}

static uint64_t
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_length(
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator c
)
{
  return c.len;
}

static cbor_raw
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_next(
  cbor_det_array_iterator_t *pi,
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator i
)
{
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut =
    Pulse_Lib_Slice_split__uint8_t(i.s,
      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(i.s, (size_t)0U));
  CBOR_Pulse_Raw_Slice_byte_slice s2 = scrut._2;
  cbor_raw res = CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(scrut._1);
  pi[0U] =
    (
      (cbor_det_array_iterator_t){
        .tag = CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = { .s = s2, .len = i.len - 1ULL } }
      }
    );
  return res;
}

static CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_truncate(
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator c,
  uint64_t len
)
{
  return ((CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator){ .s = c.s, .len = len });
}

static cbor_raw
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_item(cbor_serialized c, uint64_t i)
{
  size_t j = (size_t)i;
  size_t pi = (size_t)0U;
  CBOR_Pulse_Raw_Slice_byte_slice pres = c.cbor_serialized_payload;
  while (pi < j)
  {
    CBOR_Pulse_Raw_Slice_byte_slice res = pres;
    size_t i1 = pi;
    CBOR_Pulse_Raw_Slice_byte_slice
    res2 =
      Pulse_Lib_Slice_split__uint8_t(res,
        CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(res, (size_t)0U))._2;
    pi = i1 + (size_t)1U;
    pres = res2;
  }
  CBOR_Pulse_Raw_Slice_byte_slice res = pres;
  return
    CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(Pulse_Lib_Slice_split__uint8_t(res,
        CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(res, (size_t)0U))._1);
}

static cbor_map_entry
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_next(
  cbor_det_map_iterator_t *pi,
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator i
)
{
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut0 =
    Pulse_Lib_Slice_split__uint8_t(i.s,
      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(i.s,
        CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(i.s, (size_t)0U)));
  CBOR_Pulse_Raw_Slice_byte_slice s1 = scrut0._1;
  CBOR_Pulse_Raw_Slice_byte_slice s2 = scrut0._2;
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut =
    Pulse_Lib_Slice_split__uint8_t(s1,
      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(s1, (size_t)0U));
  CBOR_Pulse_Raw_Slice_byte_slice s21 = scrut._2;
  cbor_raw res1 = CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(scrut._1);
  cbor_map_entry
  res =
    {
      .cbor_map_entry_key = res1,
      .cbor_map_entry_value = CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(s21)
    };
  pi[0U] =
    (
      (cbor_det_map_iterator_t){
        .tag = CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = { .s = s2, .len = i.len - 1ULL } }
      }
    );
  return res;
}

static cbor_raw CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Tagged)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_match_serialized_tagged_get_payload(c.case_CBOR_Case_Serialized_Tagged);
  else if (c.tag == CBOR_Case_Tagged)
    return c.case_CBOR_Case_Tagged.cbor_tagged_ptr[0U];
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_det_array_iterator_t
CBOR_Pulse_Raw_Read_cbor_array_iterator_init_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Array)
    return
      (
        (cbor_det_array_iterator_t){
          .tag = CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_init(c.case_CBOR_Case_Serialized_Array)
          }
        }
      );
  else if (c.tag == CBOR_Case_Array)
    return
      (
        (cbor_det_array_iterator_t){
          .tag = CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = c.case_CBOR_Case_Array.cbor_array_ptr }
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

static cbor_det_map_iterator_t
CBOR_Pulse_Raw_Read_cbor_map_iterator_init_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Map)
    return
      (
        (cbor_det_map_iterator_t){
          .tag = CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_init(c.case_CBOR_Case_Serialized_Map)
          }
        }
      );
  else if (c.tag == CBOR_Case_Map)
    return
      (
        (cbor_det_map_iterator_t){
          .tag = CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = c.case_CBOR_Case_Map.cbor_map_ptr }
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

static cbor_raw CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Tagged)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_match_serialized_tagged_get_payload(c.case_CBOR_Case_Serialized_Tagged);
  else if (c.tag == CBOR_Case_Tagged)
    return c.case_CBOR_Case_Tagged.cbor_tagged_ptr[0U];
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_det_array_iterator_t CBOR_Pulse_Raw_Read_cbor_array_iterator_init(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Array)
    return
      (
        (cbor_det_array_iterator_t){
          .tag = CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_init(c.case_CBOR_Case_Serialized_Array)
          }
        }
      );
  else if (c.tag == CBOR_Case_Array)
    return
      (
        (cbor_det_array_iterator_t){
          .tag = CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = c.case_CBOR_Case_Array.cbor_array_ptr }
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

static bool CBOR_Pulse_Raw_Read_cbor_array_iterator_is_empty(cbor_det_array_iterator_t c)
{
  if (c.tag == CBOR_Raw_Iterator_Slice)
    return
      Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(c.case_CBOR_Raw_Iterator_Slice) ==
        (size_t)0U;
  else if (c.tag == CBOR_Raw_Iterator_Serialized)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_is_empty(c.case_CBOR_Raw_Iterator_Serialized);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static uint64_t CBOR_Pulse_Raw_Read_cbor_array_iterator_length(cbor_det_array_iterator_t c)
{
  if (c.tag == CBOR_Raw_Iterator_Slice)
    return
      (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(c.case_CBOR_Raw_Iterator_Slice);
  else if (c.tag == CBOR_Raw_Iterator_Serialized)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_length(c.case_CBOR_Raw_Iterator_Serialized);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct
FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw _1;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw _2;
}
FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw;

static FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s,
  size_t i
)
{
  return
    (
      (FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw){
        ._1 = { .elt = s.elt, .len = i },
        ._2 = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static cbor_raw CBOR_Pulse_Raw_Read_cbor_array_iterator_next(cbor_det_array_iterator_t *pi)
{
  cbor_det_array_iterator_t scrut = pi[0U];
  if (scrut.tag == CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i = scrut.case_CBOR_Raw_Iterator_Slice;
    cbor_raw res = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)0U);
    pi[0U] =
      (
        (cbor_det_array_iterator_t){
          .tag = CBOR_Raw_Iterator_Slice,
          {
            .case_CBOR_Raw_Iterator_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_raw(i,
              (size_t)1U)._2
          }
        }
      );
    return res;
  }
  else if (scrut.tag == CBOR_Raw_Iterator_Serialized)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_next(pi,
        scrut.case_CBOR_Raw_Iterator_Serialized);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_det_array_iterator_t
CBOR_Pulse_Raw_Read_cbor_array_iterator_truncate(cbor_det_array_iterator_t c, uint64_t len)
{
  if (c.tag == CBOR_Raw_Iterator_Slice)
    return
      (
        (cbor_det_array_iterator_t){
          .tag = CBOR_Raw_Iterator_Slice,
          {
            .case_CBOR_Raw_Iterator_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_raw(c.case_CBOR_Raw_Iterator_Slice,
              (size_t)len)._1
          }
        }
      );
  else if (c.tag == CBOR_Raw_Iterator_Serialized)
    return
      (
        (cbor_det_array_iterator_t){
          .tag = CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_truncate(c.case_CBOR_Raw_Iterator_Serialized,
              len)
          }
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

static cbor_raw CBOR_Pulse_Raw_Read_cbor_array_item(cbor_raw c, uint64_t i)
{
  if (c.tag == CBOR_Case_Serialized_Array)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_item(c.case_CBOR_Case_Serialized_Array,
        i);
  else if (c.tag == CBOR_Case_Array)
    return
      Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(c.case_CBOR_Case_Array.cbor_array_ptr,
        (size_t)i);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_det_map_iterator_t CBOR_Pulse_Raw_Read_cbor_map_iterator_init(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Map)
    return
      (
        (cbor_det_map_iterator_t){
          .tag = CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_init(c.case_CBOR_Case_Serialized_Map)
          }
        }
      );
  else if (c.tag == CBOR_Case_Map)
    return
      (
        (cbor_det_map_iterator_t){
          .tag = CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = c.case_CBOR_Case_Map.cbor_map_ptr }
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

static bool CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty(cbor_det_map_iterator_t c)
{
  if (c.tag == CBOR_Raw_Iterator_Slice)
    return
      Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(c.case_CBOR_Raw_Iterator_Slice) ==
        (size_t)0U;
  else if (c.tag == CBOR_Raw_Iterator_Serialized)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_is_empty(c.case_CBOR_Raw_Iterator_Serialized);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct
FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry _1;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry _2;
}
FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry;

static FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry s,
  size_t i
)
{
  return
    (
      (FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry){
        ._1 = { .elt = s.elt, .len = i },
        ._2 = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static cbor_map_entry CBOR_Pulse_Raw_Read_cbor_map_iterator_next(cbor_det_map_iterator_t *pi)
{
  cbor_det_map_iterator_t scrut = pi[0U];
  if (scrut.tag == CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
    i = scrut.case_CBOR_Raw_Iterator_Slice;
    cbor_map_entry
    res = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i, (size_t)0U);
    pi[0U] =
      (
        (cbor_det_map_iterator_t){
          .tag = CBOR_Raw_Iterator_Slice,
          {
            .case_CBOR_Raw_Iterator_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_map_entry(i,
              (size_t)1U)._2
          }
        }
      );
    return res;
  }
  else if (scrut.tag == CBOR_Raw_Iterator_Serialized)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_next(pi,
        scrut.case_CBOR_Raw_Iterator_Serialized);
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static CBOR_Spec_Raw_Base_raw_uint64 CBOR_Spec_Raw_Optimal_mk_raw_uint64(uint64_t x)
{
  return
    (
      (CBOR_Spec_Raw_Base_raw_uint64){
        .size = x <= (uint32_t)MAX_SIMPLE_VALUE_ADDITIONAL_INFO ? 0U
                                                                : x < 256ULL ? 1U
                                                                             : x < 65536ULL ? 2U
                                                                                            : x <
                                                                                              4294967296ULL ? 3U
                                                                                                            : 4U,
        .value = x
      }
    );
}

static int16_t
CBOR_Pulse_Raw_Format_Compare_cbor_match_compare_serialized_tagged(
  cbor_serialized c1,
  cbor_serialized c2
)
{
  return
    CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(c1.cbor_serialized_payload,
      c2.cbor_serialized_payload);
}

static int16_t
CBOR_Pulse_Raw_Format_Compare_cbor_match_compare_serialized_array(
  cbor_serialized c1,
  cbor_serialized c2
)
{
  return
    CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(c1.cbor_serialized_payload,
      c2.cbor_serialized_payload);
}

static int16_t
CBOR_Pulse_Raw_Format_Compare_cbor_match_compare_serialized_map(
  cbor_serialized c1,
  cbor_serialized c2
)
{
  return
    CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(c1.cbor_serialized_payload,
      c2.cbor_serialized_payload);
}

static uint8_t CBOR_Pulse_Raw_Compare_impl_major_type_with_depth(cbor_raw x)
{
  if (x.tag == CBOR_Case_Simple)
    return CBOR_MAJOR_TYPE_SIMPLE_VALUE;
  else if (x.tag == CBOR_Case_Int)
    if (x.tag == CBOR_Case_Int)
      return x.case_CBOR_Case_Int.cbor_int_type;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  else if (x.tag == CBOR_Case_String)
    if (x.tag == CBOR_Case_String)
      return x.case_CBOR_Case_String.cbor_string_type;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  else if (x.tag == CBOR_Case_Tagged)
    return CBOR_MAJOR_TYPE_TAGGED;
  else if (x.tag == CBOR_Case_Serialized_Tagged)
    return CBOR_MAJOR_TYPE_TAGGED;
  else if (x.tag == CBOR_Case_Array)
    return CBOR_MAJOR_TYPE_ARRAY;
  else if (x.tag == CBOR_Case_Serialized_Array)
    return CBOR_MAJOR_TYPE_ARRAY;
  else if (x.tag == CBOR_Case_Map)
    return CBOR_MAJOR_TYPE_MAP;
  else if (x.tag == CBOR_Case_Serialized_Map)
    return CBOR_MAJOR_TYPE_MAP;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static int16_t CBOR_Pulse_Raw_Compare_uint64_compare(uint64_t x1, uint64_t x2)
{
  return x1 < x2 ? -1 : x1 > x2 ? 1 : 0;
}

static int16_t
CBOR_Pulse_Raw_Compare_impl_raw_uint64_compare(
  CBOR_Spec_Raw_Base_raw_uint64 x1,
  CBOR_Spec_Raw_Base_raw_uint64 x2
)
{
  int16_t c = CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(x1.size, x2.size);
  if (c == 0)
    return CBOR_Pulse_Raw_Compare_uint64_compare(x1.value, x2.value);
  else
    return c;
}

static CBOR_Spec_Raw_Base_raw_uint64
CBOR_Pulse_Raw_Compare_cbor_match_tagged_get_tag_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Tagged)
    return c.case_CBOR_Case_Tagged.cbor_tagged_tag;
  else if (c.tag == CBOR_Case_Serialized_Tagged)
    if (c.tag == CBOR_Case_Tagged)
      return c.case_CBOR_Case_Tagged.cbor_tagged_tag;
    else if (c.tag == CBOR_Case_Serialized_Tagged)
      return c.case_CBOR_Case_Serialized_Tagged.cbor_serialized_header;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
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

static CBOR_Spec_Raw_Base_raw_uint64
CBOR_Pulse_Raw_Compare_cbor_match_array_get_length_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Array)
  {
    cbor_array a = c.case_CBOR_Case_Array;
    return
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = a.cbor_array_length_size,
          .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(a.cbor_array_ptr)
        }
      );
  }
  else if (c.tag == CBOR_Case_Serialized_Array)
    if (c.tag == CBOR_Case_Array)
    {
      cbor_array c_ = c.case_CBOR_Case_Array;
      return
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_array_length_size,
            .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
          }
        );
    }
    else if (c.tag == CBOR_Case_Serialized_Array)
      return c.case_CBOR_Case_Serialized_Array.cbor_serialized_header;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
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

static CBOR_Spec_Raw_Base_raw_uint64
CBOR_Pulse_Raw_Compare_cbor_match_map_get_length_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Map)
  {
    cbor_map a = c.case_CBOR_Case_Map;
    return
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = a.cbor_map_length_size,
          .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(a.cbor_map_ptr)
        }
      );
  }
  else if (c.tag == CBOR_Case_Serialized_Map)
    if (c.tag == CBOR_Case_Map)
    {
      cbor_map c_ = c.case_CBOR_Case_Map;
      return
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_map_length_size,
            .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
          }
        );
    }
    else if (c.tag == CBOR_Case_Serialized_Map)
      return c.case_CBOR_Case_Serialized_Map.cbor_serialized_header;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
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

typedef struct
FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw_s
{
  cbor_raw _1;
  cbor_raw _2;
}
FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw;

int16_t CBOR_Pulse_Raw_Compare_cbor_compare_with_depth(cbor_raw x1, cbor_raw x2)
{
  uint8_t ty1 = CBOR_Pulse_Raw_Compare_impl_major_type_with_depth(x1);
  int16_t
  c =
    CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(ty1,
      CBOR_Pulse_Raw_Compare_impl_major_type_with_depth(x2));
  if (c == 0)
    if (ty1 == CBOR_MAJOR_TYPE_UINT64 || ty1 == CBOR_MAJOR_TYPE_NEG_INT64)
    {
      CBOR_Spec_Raw_Base_raw_uint64 i1;
      if (x1.tag == CBOR_Case_Int)
      {
        cbor_int c_ = x1.case_CBOR_Case_Int;
        i1 =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
      }
      else
        i1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Int)
      {
        cbor_int c_ = x2.case_CBOR_Case_Int;
        ite =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
      }
      else
        ite =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      return CBOR_Pulse_Raw_Compare_impl_raw_uint64_compare(i1, ite);
    }
    else if (ty1 == CBOR_MAJOR_TYPE_BYTE_STRING || ty1 == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      CBOR_Spec_Raw_Base_raw_uint64 i1;
      if (x1.tag == CBOR_Case_String)
      {
        cbor_string c_ = x1.case_CBOR_Case_String;
        i1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_string_size,
              .value = (uint64_t)Pulse_Lib_Slice_len__uint8_t(c_.cbor_string_ptr)
            }
          );
      }
      else
        i1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 ite0;
      if (x2.tag == CBOR_Case_String)
      {
        cbor_string c_ = x2.case_CBOR_Case_String;
        ite0 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_string_size,
              .value = (uint64_t)Pulse_Lib_Slice_len__uint8_t(c_.cbor_string_ptr)
            }
          );
      }
      else
        ite0 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      int16_t c1 = CBOR_Pulse_Raw_Compare_impl_raw_uint64_compare(i1, ite0);
      if (c1 == 0)
      {
        CBOR_Pulse_Raw_Slice_byte_slice pl1;
        if (x1.tag == CBOR_Case_String)
          pl1 = x1.case_CBOR_Case_String.cbor_string_ptr;
        else
          pl1 =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        CBOR_Pulse_Raw_Slice_byte_slice ite;
        if (x2.tag == CBOR_Case_String)
          ite = x2.case_CBOR_Case_String.cbor_string_ptr;
        else
          ite =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        return CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(pl1, ite);
      }
      else
        return c1;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_TAGGED)
    {
      CBOR_Spec_Raw_Base_raw_uint64
      tag1 = CBOR_Pulse_Raw_Compare_cbor_match_tagged_get_tag_with_depth(x1);
      int16_t
      c1 =
        CBOR_Pulse_Raw_Compare_impl_raw_uint64_compare(tag1,
          CBOR_Pulse_Raw_Compare_cbor_match_tagged_get_tag_with_depth(x2));
      if (c1 == 0)
      {
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw
        scrut = { ._1 = x1, ._2 = x2 };
        if
        (scrut._1.tag == CBOR_Case_Serialized_Tagged && scrut._2.tag == CBOR_Case_Serialized_Tagged)
          if (x1.tag == CBOR_Case_Serialized_Tagged)
          {
            cbor_serialized cs1 = x1.case_CBOR_Case_Serialized_Tagged;
            if (x2.tag == CBOR_Case_Serialized_Tagged)
              return
                CBOR_Pulse_Raw_Format_Compare_cbor_match_compare_serialized_tagged(cs1,
                  x2.case_CBOR_Case_Serialized_Tagged);
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
        else
        {
          cbor_raw pl1 = CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload_with_depth(x1);
          return
            CBOR_Pulse_Raw_Compare_cbor_compare_with_depth(pl1,
              CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload_with_depth(x2));
        }
      }
      else
        return c1;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_ARRAY)
    {
      CBOR_Spec_Raw_Base_raw_uint64
      len1 = CBOR_Pulse_Raw_Compare_cbor_match_array_get_length_with_depth(x1);
      int16_t
      c1 =
        CBOR_Pulse_Raw_Compare_impl_raw_uint64_compare(len1,
          CBOR_Pulse_Raw_Compare_cbor_match_array_get_length_with_depth(x2));
      if (c1 == 0)
      {
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw
        scrut0 = { ._1 = x1, ._2 = x2 };
        if
        (scrut0._1.tag == CBOR_Case_Serialized_Array && scrut0._2.tag == CBOR_Case_Serialized_Array)
          if (x1.tag == CBOR_Case_Serialized_Array)
          {
            cbor_serialized cs1 = x1.case_CBOR_Case_Serialized_Array;
            if (x2.tag == CBOR_Case_Serialized_Array)
              return
                CBOR_Pulse_Raw_Format_Compare_cbor_match_compare_serialized_array(cs1,
                  x2.case_CBOR_Case_Serialized_Array);
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
        else if (len1.value == 0ULL)
          return 0;
        else
        {
          cbor_det_array_iterator_t
          i1 = CBOR_Pulse_Raw_Read_cbor_array_iterator_init_with_depth(x1);
          cbor_det_array_iterator_t
          i2 = CBOR_Pulse_Raw_Read_cbor_array_iterator_init_with_depth(x2);
          bool fin1;
          if (i1.tag == CBOR_Raw_Iterator_Slice)
            fin1 =
              Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(i1.case_CBOR_Raw_Iterator_Slice) ==
                (size_t)0U;
          else if (i1.tag == CBOR_Raw_Iterator_Serialized)
            fin1 =
              CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_is_empty(i1.case_CBOR_Raw_Iterator_Serialized);
          else
            fin1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          bool fin2;
          if (i2.tag == CBOR_Raw_Iterator_Slice)
            fin2 =
              Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(i2.case_CBOR_Raw_Iterator_Slice) ==
                (size_t)0U;
          else if (i2.tag == CBOR_Raw_Iterator_Serialized)
            fin2 =
              CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_is_empty(i2.case_CBOR_Raw_Iterator_Serialized);
          else
            fin2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          if (fin1)
            return fin2 ? 0 : -1;
          else if (fin2)
            return 1;
          else
          {
            cbor_det_array_iterator_t pi1 = i1;
            cbor_det_array_iterator_t pi2 = i2;
            int16_t pres = 0;
            bool pfin1 = false;
            while (pres == 0 && !pfin1)
            {
              cbor_det_array_iterator_t scrut0 = pi1;
              cbor_raw elt1;
              if (scrut0.tag == CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
                i = scrut0.case_CBOR_Raw_Iterator_Slice;
                cbor_raw
                res = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)0U);
                pi1 =
                  (
                    (cbor_det_array_iterator_t){
                      .tag = CBOR_Raw_Iterator_Slice,
                      {
                        .case_CBOR_Raw_Iterator_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_raw(i,
                          (size_t)1U)._2
                      }
                    }
                  );
                elt1 = res;
              }
              else if (scrut0.tag == CBOR_Raw_Iterator_Serialized)
                elt1 =
                  CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_next_with_depth(&pi1,
                    scrut0.case_CBOR_Raw_Iterator_Serialized);
              else
                elt1 = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
              cbor_det_array_iterator_t scrut1 = pi2;
              cbor_raw ite0;
              if (scrut1.tag == CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
                i = scrut1.case_CBOR_Raw_Iterator_Slice;
                cbor_raw
                res = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)0U);
                pi2 =
                  (
                    (cbor_det_array_iterator_t){
                      .tag = CBOR_Raw_Iterator_Slice,
                      {
                        .case_CBOR_Raw_Iterator_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_raw(i,
                          (size_t)1U)._2
                      }
                    }
                  );
                ite0 = res;
              }
              else if (scrut1.tag == CBOR_Raw_Iterator_Serialized)
                ite0 =
                  CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_next_with_depth(&pi2,
                    scrut1.case_CBOR_Raw_Iterator_Serialized);
              else
                ite0 = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
              int16_t c2 = CBOR_Pulse_Raw_Compare_cbor_compare_with_depth(elt1, ite0);
              if (c2 == 0)
              {
                cbor_det_array_iterator_t scrut0 = pi1;
                bool fin11;
                if (scrut0.tag == CBOR_Raw_Iterator_Slice)
                  fin11 =
                    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(scrut0.case_CBOR_Raw_Iterator_Slice)
                    == (size_t)0U;
                else if (scrut0.tag == CBOR_Raw_Iterator_Serialized)
                  fin11 =
                    CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_is_empty(scrut0.case_CBOR_Raw_Iterator_Serialized);
                else
                  fin11 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                cbor_det_array_iterator_t scrut = pi2;
                bool ite;
                if (scrut.tag == CBOR_Raw_Iterator_Slice)
                  ite =
                    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(scrut.case_CBOR_Raw_Iterator_Slice)
                    == (size_t)0U;
                else if (scrut.tag == CBOR_Raw_Iterator_Serialized)
                  ite =
                    CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_is_empty(scrut.case_CBOR_Raw_Iterator_Serialized);
                else
                  ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                if (fin11 == ite)
                  pfin1 = fin11;
                else if (fin11)
                  pres = -1;
                else
                  pres = 1;
              }
              else
                pres = c2;
            }
            return pres;
          }
        }
      }
      else
        return c1;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_MAP)
    {
      CBOR_Spec_Raw_Base_raw_uint64
      len1 = CBOR_Pulse_Raw_Compare_cbor_match_map_get_length_with_depth(x1);
      int16_t
      c1 =
        CBOR_Pulse_Raw_Compare_impl_raw_uint64_compare(len1,
          CBOR_Pulse_Raw_Compare_cbor_match_map_get_length_with_depth(x2));
      if (c1 == 0)
      {
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw
        scrut0 = { ._1 = x1, ._2 = x2 };
        if (scrut0._1.tag == CBOR_Case_Serialized_Map && scrut0._2.tag == CBOR_Case_Serialized_Map)
          if (x1.tag == CBOR_Case_Serialized_Map)
          {
            cbor_serialized cs1 = x1.case_CBOR_Case_Serialized_Map;
            if (x2.tag == CBOR_Case_Serialized_Map)
              return
                CBOR_Pulse_Raw_Format_Compare_cbor_match_compare_serialized_map(cs1,
                  x2.case_CBOR_Case_Serialized_Map);
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
        else if (len1.value == 0ULL)
          return 0;
        else
        {
          cbor_det_map_iterator_t i1 = CBOR_Pulse_Raw_Read_cbor_map_iterator_init_with_depth(x1);
          cbor_det_map_iterator_t i2 = CBOR_Pulse_Raw_Read_cbor_map_iterator_init_with_depth(x2);
          bool fin1;
          if (i1.tag == CBOR_Raw_Iterator_Slice)
            fin1 =
              Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(i1.case_CBOR_Raw_Iterator_Slice)
              == (size_t)0U;
          else if (i1.tag == CBOR_Raw_Iterator_Serialized)
            fin1 =
              CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_is_empty(i1.case_CBOR_Raw_Iterator_Serialized);
          else
            fin1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          bool fin2;
          if (i2.tag == CBOR_Raw_Iterator_Slice)
            fin2 =
              Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(i2.case_CBOR_Raw_Iterator_Slice)
              == (size_t)0U;
          else if (i2.tag == CBOR_Raw_Iterator_Serialized)
            fin2 =
              CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_is_empty(i2.case_CBOR_Raw_Iterator_Serialized);
          else
            fin2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          if (fin1)
            return fin2 ? 0 : -1;
          else if (fin2)
            return 1;
          else
          {
            cbor_det_map_iterator_t pi1 = i1;
            cbor_det_map_iterator_t pi2 = i2;
            int16_t pres = 0;
            bool pfin1 = false;
            while (pres == 0 && !pfin1)
            {
              cbor_det_map_iterator_t scrut0 = pi1;
              cbor_map_entry elt1;
              if (scrut0.tag == CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
                i = scrut0.case_CBOR_Raw_Iterator_Slice;
                cbor_map_entry
                res =
                  Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i,
                    (size_t)0U);
                pi1 =
                  (
                    (cbor_det_map_iterator_t){
                      .tag = CBOR_Raw_Iterator_Slice,
                      {
                        .case_CBOR_Raw_Iterator_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_map_entry(i,
                          (size_t)1U)._2
                      }
                    }
                  );
                elt1 = res;
              }
              else if (scrut0.tag == CBOR_Raw_Iterator_Serialized)
                elt1 =
                  CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_next_with_depth(&pi1,
                    scrut0.case_CBOR_Raw_Iterator_Serialized);
              else
                elt1 =
                  KRML_EABORT(cbor_map_entry,
                    "unreachable (pattern matches are exhaustive in F*)");
              cbor_det_map_iterator_t scrut1 = pi2;
              cbor_map_entry elt2;
              if (scrut1.tag == CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
                i = scrut1.case_CBOR_Raw_Iterator_Slice;
                cbor_map_entry
                res =
                  Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i,
                    (size_t)0U);
                pi2 =
                  (
                    (cbor_det_map_iterator_t){
                      .tag = CBOR_Raw_Iterator_Slice,
                      {
                        .case_CBOR_Raw_Iterator_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_map_entry(i,
                          (size_t)1U)._2
                      }
                    }
                  );
                elt2 = res;
              }
              else if (scrut1.tag == CBOR_Raw_Iterator_Serialized)
                elt2 =
                  CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_next_with_depth(&pi2,
                    scrut1.case_CBOR_Raw_Iterator_Serialized);
              else
                elt2 =
                  KRML_EABORT(cbor_map_entry,
                    "unreachable (pattern matches are exhaustive in F*)");
              int16_t
              c2 =
                CBOR_Pulse_Raw_Compare_cbor_compare_with_depth(elt1.cbor_map_entry_key,
                  elt2.cbor_map_entry_key);
              int16_t c3;
              if (c2 == 0)
                c3 =
                  CBOR_Pulse_Raw_Compare_cbor_compare_with_depth(elt1.cbor_map_entry_value,
                    elt2.cbor_map_entry_value);
              else
                c3 = c2;
              if (c3 == 0)
              {
                cbor_det_map_iterator_t scrut0 = pi1;
                bool fin11;
                if (scrut0.tag == CBOR_Raw_Iterator_Slice)
                  fin11 =
                    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(scrut0.case_CBOR_Raw_Iterator_Slice)
                    == (size_t)0U;
                else if (scrut0.tag == CBOR_Raw_Iterator_Serialized)
                  fin11 =
                    CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_is_empty(scrut0.case_CBOR_Raw_Iterator_Serialized);
                else
                  fin11 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                cbor_det_map_iterator_t scrut = pi2;
                bool ite;
                if (scrut.tag == CBOR_Raw_Iterator_Slice)
                  ite =
                    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(scrut.case_CBOR_Raw_Iterator_Slice)
                    == (size_t)0U;
                else if (scrut.tag == CBOR_Raw_Iterator_Serialized)
                  ite =
                    CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_is_empty(scrut.case_CBOR_Raw_Iterator_Serialized);
                else
                  ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                if (fin11 == ite)
                  pfin1 = fin11;
                else if (fin11)
                  pres = -1;
                else
                  pres = 1;
              }
              else
                pres = c3;
            }
            return pres;
          }
        }
      }
      else
        return c1;
    }
    else
    {
      uint8_t val1;
      if (x1.tag == CBOR_Case_Simple)
        val1 = x1.case_CBOR_Case_Simple;
      else
        val1 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      uint8_t ite;
      if (x2.tag == CBOR_Case_Simple)
        ite = x2.case_CBOR_Case_Simple;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      return CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(val1, ite);
    }
  else
    return c;
}

static int16_t CBOR_Pulse_Raw_Compare_impl_cbor_compare(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Compare_cbor_compare_with_depth(x1, x2);
}

static uint8_t CBOR_Pulse_Raw_Compare_impl_major_type(cbor_raw x)
{
  if (x.tag == CBOR_Case_Simple)
    return CBOR_MAJOR_TYPE_SIMPLE_VALUE;
  else if (x.tag == CBOR_Case_Int)
    if (x.tag == CBOR_Case_Int)
      return x.case_CBOR_Case_Int.cbor_int_type;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  else if (x.tag == CBOR_Case_String)
    if (x.tag == CBOR_Case_String)
      return x.case_CBOR_Case_String.cbor_string_type;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  else if (x.tag == CBOR_Case_Tagged)
    return CBOR_MAJOR_TYPE_TAGGED;
  else if (x.tag == CBOR_Case_Serialized_Tagged)
    return CBOR_MAJOR_TYPE_TAGGED;
  else if (x.tag == CBOR_Case_Array)
    return CBOR_MAJOR_TYPE_ARRAY;
  else if (x.tag == CBOR_Case_Serialized_Array)
    return CBOR_MAJOR_TYPE_ARRAY;
  else if (x.tag == CBOR_Case_Map)
    return CBOR_MAJOR_TYPE_MAP;
  else if (x.tag == CBOR_Case_Serialized_Map)
    return CBOR_MAJOR_TYPE_MAP;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static bool CBOR_Pulse_Raw_Format_Serialize_compute_deep(cbor_raw c)
{
  if (c.tag == CBOR_Case_Tagged)
    return true;
  else if (c.tag == CBOR_Case_Array)
    return
      !(Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(c.case_CBOR_Case_Array.cbor_array_ptr) ==
        (size_t)0U);
  else if (c.tag == CBOR_Case_Map)
    return
      !(Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(c.case_CBOR_Case_Map.cbor_map_ptr)
      == (size_t)0U);
  else
    return false;
}

static CBOR_Spec_Raw_Base_raw_uint64
CBOR_Pulse_Raw_Format_Serialize_cbor_match_tagged_get_tag_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Tagged)
    return c.case_CBOR_Case_Tagged.cbor_tagged_tag;
  else if (c.tag == CBOR_Case_Serialized_Tagged)
    if (c.tag == CBOR_Case_Tagged)
      return c.case_CBOR_Case_Tagged.cbor_tagged_tag;
    else if (c.tag == CBOR_Case_Serialized_Tagged)
      return c.case_CBOR_Case_Serialized_Tagged.cbor_serialized_header;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
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

static CBOR_Spec_Raw_Base_raw_uint64
CBOR_Pulse_Raw_Format_Serialize_cbor_match_array_get_length_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Array)
  {
    cbor_array a = c.case_CBOR_Case_Array;
    return
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = a.cbor_array_length_size,
          .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(a.cbor_array_ptr)
        }
      );
  }
  else if (c.tag == CBOR_Case_Serialized_Array)
    if (c.tag == CBOR_Case_Array)
    {
      cbor_array c_ = c.case_CBOR_Case_Array;
      return
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_array_length_size,
            .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
          }
        );
    }
    else if (c.tag == CBOR_Case_Serialized_Array)
      return c.case_CBOR_Case_Serialized_Array.cbor_serialized_header;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
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

static CBOR_Spec_Raw_Base_raw_uint64
CBOR_Pulse_Raw_Format_Serialize_cbor_match_map_get_length_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Map)
  {
    cbor_map a = c.case_CBOR_Case_Map;
    return
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = a.cbor_map_length_size,
          .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(a.cbor_map_ptr)
        }
      );
  }
  else if (c.tag == CBOR_Case_Serialized_Map)
    if (c.tag == CBOR_Case_Map)
    {
      cbor_map c_ = c.case_CBOR_Case_Map;
      return
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_map_length_size,
            .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
          }
        );
    }
    else if (c.tag == CBOR_Case_Serialized_Map)
      return c.case_CBOR_Case_Serialized_Map.cbor_serialized_header;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
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

static Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
CBOR_Pulse_Raw_Format_Serialize_cbor_raw_get_header_d(cbor_raw xl)
{
  if (xl.tag == CBOR_Case_Int)
  {
    uint8_t ty;
    if (xl.tag == CBOR_Case_Int)
      ty = xl.case_CBOR_Case_Int.cbor_int_type;
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_Int)
    {
      cbor_int c_ = xl.case_CBOR_Case_Int;
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
    }
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(ty, ite);
  }
  else if (xl.tag == CBOR_Case_String)
  {
    uint8_t ty;
    if (xl.tag == CBOR_Case_String)
      ty = xl.case_CBOR_Case_String.cbor_string_type;
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_String)
    {
      cbor_string c_ = xl.case_CBOR_Case_String;
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_string_size,
            .value = (uint64_t)Pulse_Lib_Slice_len__uint8_t(c_.cbor_string_ptr)
          }
        );
    }
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(ty, ite);
  }
  else if (xl.tag == CBOR_Case_Tagged)
    return
      CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED,
        CBOR_Pulse_Raw_Format_Serialize_cbor_match_tagged_get_tag_with_depth(xl));
  else if (xl.tag == CBOR_Case_Serialized_Tagged)
    return
      CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED,
        CBOR_Pulse_Raw_Format_Serialize_cbor_match_tagged_get_tag_with_depth(xl));
  else if (xl.tag == CBOR_Case_Array)
    return
      CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY,
        CBOR_Pulse_Raw_Format_Serialize_cbor_match_array_get_length_with_depth(xl));
  else if (xl.tag == CBOR_Case_Serialized_Array)
    return
      CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY,
        CBOR_Pulse_Raw_Format_Serialize_cbor_match_array_get_length_with_depth(xl));
  else if (xl.tag == CBOR_Case_Map)
    return
      CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP,
        CBOR_Pulse_Raw_Format_Serialize_cbor_match_map_get_length_with_depth(xl));
  else if (xl.tag == CBOR_Case_Serialized_Map)
    return
      CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP,
        CBOR_Pulse_Raw_Format_Serialize_cbor_match_map_get_length_with_depth(xl));
  else if (xl.tag == CBOR_Case_Simple)
  {
    uint8_t ite;
    if (xl.tag == CBOR_Case_Simple)
      ite = xl.case_CBOR_Case_Simple;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return CBOR_Spec_Raw_EverParse_simple_value_as_argument(ite);
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

static Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
CBOR_Pulse_Raw_Format_Serialize_cbor_raw_with_perm_get_header_d(cbor_raw xl)
{
  return CBOR_Pulse_Raw_Format_Serialize_cbor_raw_get_header_d(xl);
}

static CBOR_Spec_Raw_EverParse_initial_byte_t
Custard_FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  t
)
{
  return t._1;
}

static bool
CBOR_Pulse_Raw_Format_Serialize_size_header(
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  x,
  size_t *out
)
{
  CBOR_Spec_Raw_EverParse_initial_byte_t
  xh1 =
    Custard_FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  size_t capacity = out[0U];
  bool ite;
  if (capacity < (size_t)1U)
    ite = false;
  else
  {
    out[0U] = capacity - (size_t)1U;
    ite = true;
  }
  if (ite)
    if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    {
      size_t capacity1 = out[0U];
      if (capacity1 < (size_t)1U)
        return false;
      else
      {
        out[0U] = capacity1 - (size_t)1U;
        return true;
      }
    }
    else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    {
      size_t capacity1 = out[0U];
      if (capacity1 < (size_t)2U)
        return false;
      else
      {
        out[0U] = capacity1 - (size_t)2U;
        return true;
      }
    }
    else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    {
      size_t capacity1 = out[0U];
      if (capacity1 < (size_t)4U)
        return false;
      else
      {
        out[0U] = capacity1 - (size_t)4U;
        return true;
      }
    }
    else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    {
      size_t capacity1 = out[0U];
      if (capacity1 < (size_t)8U)
        return false;
      else
      {
        out[0U] = capacity1 - (size_t)8U;
        return true;
      }
    }
    else
      return true;
  else
    return false;
}

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t
FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_tags;

typedef struct
FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw v;
}
FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw;

typedef struct
FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry v;
}
FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry;

bool CBOR_Pulse_Raw_Format_Serialize_siz__d(cbor_raw x_, size_t *out)
{
  if (CBOR_Pulse_Raw_Format_Serialize_compute_deep(x_))
  {
    Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    xh1 = CBOR_Pulse_Raw_Format_Serialize_cbor_raw_with_perm_get_header_d(x_);
    if (CBOR_Pulse_Raw_Format_Serialize_size_header(xh1, out))
    {
      CBOR_Spec_Raw_EverParse_initial_byte_t b = xh1._1;
      if
      (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
      {
        CBOR_Pulse_Raw_Slice_byte_slice ite;
        if (x_.tag == CBOR_Case_String)
          ite = x_.case_CBOR_Case_String.cbor_string_ptr;
        else
          ite =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = Pulse_Lib_Slice_len__uint8_t(ite);
        size_t cur = out[0U];
        if (cur < length)
          return false;
        else
        {
          out[0U] = cur - length;
          return true;
        }
      }
      else if (xh1._1.major_type == CBOR_MAJOR_TYPE_ARRAY)
        if (x_.tag == CBOR_Case_Array)
        {
          FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
          scrut =
            x_.tag == CBOR_Case_Array ? (
                                        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw){
                                          .tag = FStar_Pervasives_Native_Some,
                                          .v = x_.case_CBOR_Case_Array.cbor_array_ptr
                                        }
                                      )
                                      : (
                                        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw){
                                          .tag = FStar_Pervasives_Native_None
                                        }
                                      );
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw a;
          if (scrut.tag == FStar_Pervasives_Native_Some)
            a = scrut.v;
          else
            a =
              KRML_EABORT(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          bool pres = true;
          size_t pi = (size_t)0U;
          size_t len = Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(a);
          while (pres && pi < len)
          {
            size_t i = pi;
            if
            (
              CBOR_Pulse_Raw_Format_Serialize_siz__d(Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(a,
                  i),
                out)
            )
              pi = i + (size_t)1U;
            else
              pres = false;
          }
          return pres;
        }
        else
        {
          CBOR_Pulse_Raw_Slice_byte_slice ite;
          if (x_.tag == CBOR_Case_Serialized_Array)
            ite = x_.case_CBOR_Case_Serialized_Array.cbor_serialized_payload;
          else
            ite =
              KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
                "unreachable (pattern matches are exhaustive in F*)");
          size_t length = Pulse_Lib_Slice_len__uint8_t(ite);
          size_t cur = out[0U];
          if (cur < length)
            return false;
          else
          {
            out[0U] = cur - length;
            return true;
          }
        }
      else if (xh1._1.major_type == CBOR_MAJOR_TYPE_MAP)
        if (x_.tag == CBOR_Case_Map)
        {
          FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
          scrut =
            x_.tag == CBOR_Case_Map ? (
                                      (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry){
                                        .tag = FStar_Pervasives_Native_Some,
                                        .v = x_.case_CBOR_Case_Map.cbor_map_ptr
                                      }
                                    )
                                    : (
                                      (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry){
                                        .tag = FStar_Pervasives_Native_None
                                      }
                                    );
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a;
          if (scrut.tag == FStar_Pervasives_Native_Some)
            a = scrut.v;
          else
            a =
              KRML_EABORT(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry,
                "unreachable (pattern matches are exhaustive in F*)");
          bool pres = true;
          size_t pi = (size_t)0U;
          size_t len = Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(a);
          while (pres && pi < len)
          {
            size_t i = pi;
            cbor_map_entry
            e = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i);
            bool ite;
            if (CBOR_Pulse_Raw_Format_Serialize_siz__d(e.cbor_map_entry_key, out))
              ite = CBOR_Pulse_Raw_Format_Serialize_siz__d(e.cbor_map_entry_value, out);
            else
              ite = false;
            if (ite)
              pi = i + (size_t)1U;
            else
              pres = false;
          }
          return pres;
        }
        else
        {
          CBOR_Pulse_Raw_Slice_byte_slice ite;
          if (x_.tag == CBOR_Case_Serialized_Map)
            ite = x_.case_CBOR_Case_Serialized_Map.cbor_serialized_payload;
          else
            ite =
              KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
                "unreachable (pattern matches are exhaustive in F*)");
          size_t length = Pulse_Lib_Slice_len__uint8_t(ite);
          size_t cur = out[0U];
          if (cur < length)
            return false;
          else
          {
            out[0U] = cur - length;
            return true;
          }
        }
      else if (xh1._1.major_type == CBOR_MAJOR_TYPE_TAGGED)
        if (x_.tag == CBOR_Case_Tagged)
        {
          cbor_raw ite;
          if (x_.tag == CBOR_Case_Tagged)
            ite = x_.case_CBOR_Case_Tagged.cbor_tagged_ptr[0U];
          else
            ite = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
          return CBOR_Pulse_Raw_Format_Serialize_siz__d(ite, out);
        }
        else
        {
          CBOR_Pulse_Raw_Slice_byte_slice ite;
          if (x_.tag == CBOR_Case_Serialized_Tagged)
            ite = x_.case_CBOR_Case_Serialized_Tagged.cbor_serialized_payload;
          else
            ite =
              KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
                "unreachable (pattern matches are exhaustive in F*)");
          size_t length = Pulse_Lib_Slice_len__uint8_t(ite);
          size_t cur = out[0U];
          if (cur < length)
            return false;
          else
          {
            out[0U] = cur - length;
            return true;
          }
        }
      else
        return true;
    }
    else
      return false;
  }
  else
  {
    Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    xh1 = CBOR_Pulse_Raw_Format_Serialize_cbor_raw_with_perm_get_header_d(x_);
    if (CBOR_Pulse_Raw_Format_Serialize_size_header(xh1, out))
    {
      CBOR_Spec_Raw_EverParse_initial_byte_t b = xh1._1;
      if
      (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
      {
        CBOR_Pulse_Raw_Slice_byte_slice ite;
        if (x_.tag == CBOR_Case_String)
          ite = x_.case_CBOR_Case_String.cbor_string_ptr;
        else
          ite =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = Pulse_Lib_Slice_len__uint8_t(ite);
        size_t cur = out[0U];
        if (cur < length)
          return false;
        else
        {
          out[0U] = cur - length;
          return true;
        }
      }
      else if (xh1._1.major_type == CBOR_MAJOR_TYPE_ARRAY)
        if (x_.tag == CBOR_Case_Array)
          return true;
        else
        {
          CBOR_Pulse_Raw_Slice_byte_slice ite;
          if (x_.tag == CBOR_Case_Serialized_Array)
            ite = x_.case_CBOR_Case_Serialized_Array.cbor_serialized_payload;
          else
            ite =
              KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
                "unreachable (pattern matches are exhaustive in F*)");
          size_t length = Pulse_Lib_Slice_len__uint8_t(ite);
          size_t cur = out[0U];
          if (cur < length)
            return false;
          else
          {
            out[0U] = cur - length;
            return true;
          }
        }
      else if (xh1._1.major_type == CBOR_MAJOR_TYPE_MAP)
        if (x_.tag == CBOR_Case_Map)
          return true;
        else
        {
          CBOR_Pulse_Raw_Slice_byte_slice ite;
          if (x_.tag == CBOR_Case_Serialized_Map)
            ite = x_.case_CBOR_Case_Serialized_Map.cbor_serialized_payload;
          else
            ite =
              KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
                "unreachable (pattern matches are exhaustive in F*)");
          size_t length = Pulse_Lib_Slice_len__uint8_t(ite);
          size_t cur = out[0U];
          if (cur < length)
            return false;
          else
          {
            out[0U] = cur - length;
            return true;
          }
        }
      else if (xh1._1.major_type == CBOR_MAJOR_TYPE_TAGGED)
        if (x_.tag == CBOR_Case_Tagged)
          if (x_.tag == CBOR_Case_Tagged)
            return false;
          else
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        else
        {
          CBOR_Pulse_Raw_Slice_byte_slice ite;
          if (x_.tag == CBOR_Case_Serialized_Tagged)
            ite = x_.case_CBOR_Case_Serialized_Tagged.cbor_serialized_payload;
          else
            ite =
              KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
                "unreachable (pattern matches are exhaustive in F*)");
          size_t length = Pulse_Lib_Slice_len__uint8_t(ite);
          size_t cur = out[0U];
          if (cur < length)
            return false;
          else
          {
            out[0U] = cur - length;
            return true;
          }
        }
      else
        return true;
    }
    else
      return false;
  }
}

static size_t CBOR_Pulse_Raw_Format_Serialize_cbor_size(cbor_raw x, size_t bound)
{
  size_t output = bound;
  if (CBOR_Pulse_Raw_Format_Serialize_siz__d(x, &output))
    return bound - output;
  else
    return (size_t)0U;
}

static CBOR_Spec_Raw_EverParse_long_argument
Custard_FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  t
)
{
  return t._2;
}

static size_t
CBOR_Pulse_Raw_Format_Serialize_write_header(
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  x,
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t offset
)
{
  CBOR_Spec_Raw_EverParse_initial_byte_t
  xh1 =
    Custard_FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  size_t pos_ = offset + (size_t)1U;
  Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out,
    pos_ - (size_t)1U,
    LowParse_BitFields_set_bitfield_gen8(LowParse_BitFields_set_bitfield_gen8(0U,
        0U,
        5U,
        xh1.additional_info),
      5U,
      8U,
      xh1.major_type));
  CBOR_Spec_Raw_EverParse_long_argument
  x2_ =
    Custard_FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    if (xh1.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    {
      size_t pos_1 = pos_ + (size_t)1U;
      uint8_t ite;
      if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
        ite = x2_.case_LongArgumentSimpleValue;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_1 - (size_t)1U, ite);
      return pos_1;
    }
    else
    {
      size_t pos_1 = pos_ + (size_t)1U;
      uint8_t ite;
      if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
        ite = x2_.case_LongArgumentU8;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_1 - (size_t)1U, ite);
      return pos_1;
    }
  else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
  {
    size_t pos_1 = pos_ + (size_t)2U;
    uint16_t ite0;
    if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite0 = x2_.case_LongArgumentU16;
    else
      ite0 = KRML_EABORT(uint16_t, "unreachable (pattern matches are exhaustive in F*)");
    uint8_t lo = (uint8_t)(uint32_t)ite0;
    size_t pos_2 = pos_1 - (size_t)1U;
    uint16_t ite;
    if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite = x2_.case_LongArgumentU16;
    else
      ite = KRML_EABORT(uint16_t, "unreachable (pattern matches are exhaustive in F*)");
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out,
      pos_2 - (size_t)1U,
      (uint8_t)((uint32_t)ite / 256U & 0xFFFFU));
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_2, lo);
    return pos_1;
  }
  else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
  {
    size_t pos_1 = pos_ + (size_t)4U;
    uint32_t ite0;
    if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite0 = x2_.case_LongArgumentU32;
    else
      ite0 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
    uint8_t lo = (uint8_t)ite0;
    uint32_t ite;
    if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite = x2_.case_LongArgumentU32;
    else
      ite = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
    uint32_t hi = ite / 256U;
    size_t pos_2 = pos_1 - (size_t)1U;
    uint8_t lo1 = (uint8_t)hi;
    uint32_t hi1 = hi / 256U;
    size_t pos_3 = pos_2 - (size_t)1U;
    uint8_t lo2 = (uint8_t)hi1;
    size_t pos_4 = pos_3 - (size_t)1U;
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_4 - (size_t)1U, (uint8_t)(hi1 / 256U));
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_4, lo2);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_3, lo1);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_2, lo);
    return pos_1;
  }
  else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
  {
    size_t pos_1 = pos_ + (size_t)8U;
    uint64_t ite0;
    if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite0 = x2_.case_LongArgumentU64;
    else
      ite0 = KRML_EABORT(uint64_t, "unreachable (pattern matches are exhaustive in F*)");
    uint8_t lo = (uint8_t)ite0;
    uint64_t ite;
    if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = x2_.case_LongArgumentU64;
    else
      ite = KRML_EABORT(uint64_t, "unreachable (pattern matches are exhaustive in F*)");
    uint64_t hi = ite / 256ULL;
    size_t pos_2 = pos_1 - (size_t)1U;
    uint8_t lo1 = (uint8_t)hi;
    uint64_t hi1 = hi / 256ULL;
    size_t pos_3 = pos_2 - (size_t)1U;
    uint8_t lo2 = (uint8_t)hi1;
    uint64_t hi2 = hi1 / 256ULL;
    size_t pos_4 = pos_3 - (size_t)1U;
    uint8_t lo3 = (uint8_t)hi2;
    uint64_t hi3 = hi2 / 256ULL;
    size_t pos_5 = pos_4 - (size_t)1U;
    uint8_t lo4 = (uint8_t)hi3;
    uint64_t hi4 = hi3 / 256ULL;
    size_t pos_6 = pos_5 - (size_t)1U;
    uint8_t lo5 = (uint8_t)hi4;
    uint64_t hi5 = hi4 / 256ULL;
    size_t pos_7 = pos_6 - (size_t)1U;
    uint8_t lo6 = (uint8_t)hi5;
    size_t pos_8 = pos_7 - (size_t)1U;
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_8 - (size_t)1U, (uint8_t)(hi5 / 256ULL));
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_8, lo6);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_7, lo5);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_6, lo4);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_5, lo3);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_4, lo2);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_3, lo1);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_2, lo);
    return pos_1;
  }
  else
    return pos_;
}

size_t
CBOR_Pulse_Raw_Format_Serialize_ser__d(
  cbor_raw x_,
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t offset
)
{
  if (CBOR_Pulse_Raw_Format_Serialize_compute_deep(x_))
  {
    Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    xh1 = CBOR_Pulse_Raw_Format_Serialize_cbor_raw_with_perm_get_header_d(x_);
    size_t res1 = CBOR_Pulse_Raw_Format_Serialize_write_header(xh1, out, offset);
    CBOR_Spec_Raw_EverParse_initial_byte_t b = xh1._1;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      CBOR_Pulse_Raw_Slice_byte_slice x2_;
      if (x_.tag == CBOR_Case_String)
        x2_ = x_.case_CBOR_Case_String.cbor_string_ptr;
      else
        x2_ =
          KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
            "unreachable (pattern matches are exhaustive in F*)");
      size_t length = Pulse_Lib_Slice_len__uint8_t(x2_);
      Pulse_Lib_Slice_copy__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out,
            res1)._2,
          length)._1,
        x2_);
      return res1 + length;
    }
    else if (xh1._1.major_type == CBOR_MAJOR_TYPE_ARRAY)
      if (x_.tag == CBOR_Case_Array)
      {
        FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
        scrut =
          x_.tag == CBOR_Case_Array ? (
                                      (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw){
                                        .tag = FStar_Pervasives_Native_Some,
                                        .v = x_.case_CBOR_Case_Array.cbor_array_ptr
                                      }
                                    )
                                    : (
                                      (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw){
                                        .tag = FStar_Pervasives_Native_None
                                      }
                                    );
        Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw a;
        if (scrut.tag == FStar_Pervasives_Native_Some)
          a = scrut.v;
        else
          a =
            KRML_EABORT(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t pres = res1;
        size_t pi = (size_t)0U;
        size_t len = Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(a);
        while (pi < len)
        {
          size_t i = pi;
          size_t off = pres;
          size_t i_ = i + (size_t)1U;
          size_t
          res =
            CBOR_Pulse_Raw_Format_Serialize_ser__d(Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(a,
                i),
              out,
              off);
          pi = i_;
          pres = res;
        }
        return pres;
      }
      else
      {
        CBOR_Pulse_Raw_Slice_byte_slice x2_;
        if (x_.tag == CBOR_Case_Serialized_Array)
          x2_ = x_.case_CBOR_Case_Serialized_Array.cbor_serialized_payload;
        else
          x2_ =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = Pulse_Lib_Slice_len__uint8_t(x2_);
        Pulse_Lib_Slice_copy__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out,
              res1)._2,
            length)._1,
          x2_);
        return res1 + length;
      }
    else if (xh1._1.major_type == CBOR_MAJOR_TYPE_MAP)
      if (x_.tag == CBOR_Case_Map)
      {
        FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
        scrut =
          x_.tag == CBOR_Case_Map ? (
                                    (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry){
                                      .tag = FStar_Pervasives_Native_Some,
                                      .v = x_.case_CBOR_Case_Map.cbor_map_ptr
                                    }
                                  )
                                  : (
                                    (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry){
                                      .tag = FStar_Pervasives_Native_None
                                    }
                                  );
        Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a;
        if (scrut.tag == FStar_Pervasives_Native_Some)
          a = scrut.v;
        else
          a =
            KRML_EABORT(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t pres = res1;
        size_t pi = (size_t)0U;
        size_t len = Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(a);
        while (pi < len)
        {
          size_t i = pi;
          size_t off = pres;
          cbor_map_entry
          e = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i);
          size_t i_ = i + (size_t)1U;
          size_t
          res =
            CBOR_Pulse_Raw_Format_Serialize_ser__d(e.cbor_map_entry_value,
              out,
              CBOR_Pulse_Raw_Format_Serialize_ser__d(e.cbor_map_entry_key, out, off));
          pi = i_;
          pres = res;
        }
        return pres;
      }
      else
      {
        CBOR_Pulse_Raw_Slice_byte_slice x2_;
        if (x_.tag == CBOR_Case_Serialized_Map)
          x2_ = x_.case_CBOR_Case_Serialized_Map.cbor_serialized_payload;
        else
          x2_ =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = Pulse_Lib_Slice_len__uint8_t(x2_);
        Pulse_Lib_Slice_copy__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out,
              res1)._2,
            length)._1,
          x2_);
        return res1 + length;
      }
    else if (xh1._1.major_type == CBOR_MAJOR_TYPE_TAGGED)
      if (x_.tag == CBOR_Case_Tagged)
      {
        cbor_raw ite;
        if (x_.tag == CBOR_Case_Tagged)
          ite = x_.case_CBOR_Case_Tagged.cbor_tagged_ptr[0U];
        else
          ite = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
        return CBOR_Pulse_Raw_Format_Serialize_ser__d(ite, out, res1);
      }
      else
      {
        CBOR_Pulse_Raw_Slice_byte_slice x2_;
        if (x_.tag == CBOR_Case_Serialized_Tagged)
          x2_ = x_.case_CBOR_Case_Serialized_Tagged.cbor_serialized_payload;
        else
          x2_ =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = Pulse_Lib_Slice_len__uint8_t(x2_);
        Pulse_Lib_Slice_copy__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out,
              res1)._2,
            length)._1,
          x2_);
        return res1 + length;
      }
    else
      return res1;
  }
  else
  {
    Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    xh1 = CBOR_Pulse_Raw_Format_Serialize_cbor_raw_with_perm_get_header_d(x_);
    size_t res1 = CBOR_Pulse_Raw_Format_Serialize_write_header(xh1, out, offset);
    CBOR_Spec_Raw_EverParse_initial_byte_t b = xh1._1;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      CBOR_Pulse_Raw_Slice_byte_slice x2_;
      if (x_.tag == CBOR_Case_String)
        x2_ = x_.case_CBOR_Case_String.cbor_string_ptr;
      else
        x2_ =
          KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
            "unreachable (pattern matches are exhaustive in F*)");
      size_t length = Pulse_Lib_Slice_len__uint8_t(x2_);
      Pulse_Lib_Slice_copy__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out,
            res1)._2,
          length)._1,
        x2_);
      return res1 + length;
    }
    else if (xh1._1.major_type == CBOR_MAJOR_TYPE_ARRAY)
      if (x_.tag == CBOR_Case_Array)
        return res1;
      else
      {
        CBOR_Pulse_Raw_Slice_byte_slice x2_;
        if (x_.tag == CBOR_Case_Serialized_Array)
          x2_ = x_.case_CBOR_Case_Serialized_Array.cbor_serialized_payload;
        else
          x2_ =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = Pulse_Lib_Slice_len__uint8_t(x2_);
        Pulse_Lib_Slice_copy__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out,
              res1)._2,
            length)._1,
          x2_);
        return res1 + length;
      }
    else if (xh1._1.major_type == CBOR_MAJOR_TYPE_MAP)
      if (x_.tag == CBOR_Case_Map)
        return res1;
      else
      {
        CBOR_Pulse_Raw_Slice_byte_slice x2_;
        if (x_.tag == CBOR_Case_Serialized_Map)
          x2_ = x_.case_CBOR_Case_Serialized_Map.cbor_serialized_payload;
        else
          x2_ =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = Pulse_Lib_Slice_len__uint8_t(x2_);
        Pulse_Lib_Slice_copy__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out,
              res1)._2,
            length)._1,
          x2_);
        return res1 + length;
      }
    else if (xh1._1.major_type == CBOR_MAJOR_TYPE_TAGGED)
      if (x_.tag == CBOR_Case_Tagged)
        if (x_.tag == CBOR_Case_Tagged)
          return res1;
        else
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
      else
      {
        CBOR_Pulse_Raw_Slice_byte_slice x2_;
        if (x_.tag == CBOR_Case_Serialized_Tagged)
          x2_ = x_.case_CBOR_Case_Serialized_Tagged.cbor_serialized_payload;
        else
          x2_ =
            KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = Pulse_Lib_Slice_len__uint8_t(x2_);
        Pulse_Lib_Slice_copy__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out,
              res1)._2,
            length)._1,
          x2_);
        return res1 + length;
      }
    else
      return res1;
  }
}

static size_t
CBOR_Pulse_Raw_Format_Serialize_cbor_serialize(
  cbor_raw x,
  CBOR_Pulse_Raw_Slice_byte_slice output
)
{
  return CBOR_Pulse_Raw_Format_Serialize_ser__d(x, output, (size_t)0U);
}

static size_t
CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_tag(
  CBOR_Spec_Raw_Base_raw_uint64 tag,
  CBOR_Pulse_Raw_Slice_byte_slice output
)
{
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED, tag);
  size_t buf = Pulse_Lib_Slice_len__uint8_t(output);
  if (CBOR_Pulse_Raw_Format_Serialize_size_header(h, &buf))
    return CBOR_Pulse_Raw_Format_Serialize_write_header(h, output, (size_t)0U);
  else
    return (size_t)0U;
}

static size_t
CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_array_(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t off
)
{
  size_t rem = Pulse_Lib_Slice_len__uint8_t(out) - off;
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY, len);
  if (CBOR_Pulse_Raw_Format_Serialize_size_header(h, &rem))
  {
    size_t llen = CBOR_Pulse_Raw_Format_Serialize_write_header(h, out, off);
    CBOR_Pulse_Raw_Slice_byte_slice sp1 = Pulse_Lib_Slice_split__uint8_t(out, llen)._1;
    if (!(off == (size_t)0U || off == Pulse_Lib_Slice_len__uint8_t(sp1)))
    {
      size_t pn = Pulse_Lib_Slice_len__uint8_t(sp1);
      size_t pl = off;
      while (pl > (size_t)0U)
      {
        size_t l = pl;
        size_t l_ = pn % l;
        pn = l;
        pl = l_;
      }
      size_t d = pn;
      size_t q = Pulse_Lib_Slice_len__uint8_t(sp1) / d;
      size_t pi = (size_t)0U;
      while (pi < d)
      {
        size_t i = pi;
        uint8_t save = Pulse_Lib_Slice_op_Array_Access__uint8_t(sp1, i);
        size_t pj = (size_t)0U;
        size_t pidx = i;
        while (pj < q - (size_t)1U)
        {
          size_t j = pj;
          size_t idx = pidx;
          size_t idx_;
          if (idx - (size_t)0U >= Pulse_Lib_Slice_len__uint8_t(sp1) - off)
            idx_ = idx - (Pulse_Lib_Slice_len__uint8_t(sp1) - off);
          else
            idx_ = idx + (off - (size_t)0U);
          size_t j_ = j + (size_t)1U;
          Pulse_Lib_Slice_op_Array_Assignment__uint8_t(sp1,
            idx,
            Pulse_Lib_Slice_op_Array_Access__uint8_t(sp1, idx_));
          pj = j_;
          pidx = idx_;
        }
        Pulse_Lib_Slice_op_Array_Assignment__uint8_t(sp1, pidx, save);
        pi = i + (size_t)1U;
      }
    }
    return llen;
  }
  else
    return (size_t)0U;
}

static size_t
CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_array(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t off
)
{
  return CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_array_(len, out, off);
}

static size_t
CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_string(
  uint8_t ty,
  CBOR_Spec_Raw_Base_raw_uint64 off,
  CBOR_Pulse_Raw_Slice_byte_slice out
)
{
  size_t soff = (size_t)off.value;
  size_t rem = Pulse_Lib_Slice_len__uint8_t(out) - soff;
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(ty, off);
  if (CBOR_Pulse_Raw_Format_Serialize_size_header(h, &rem))
  {
    size_t llen = CBOR_Pulse_Raw_Format_Serialize_write_header(h, out, soff);
    CBOR_Pulse_Raw_Slice_byte_slice sp1 = Pulse_Lib_Slice_split__uint8_t(out, llen)._1;
    if (!(soff == (size_t)0U || soff == Pulse_Lib_Slice_len__uint8_t(sp1)))
    {
      size_t pn = Pulse_Lib_Slice_len__uint8_t(sp1);
      size_t pl = soff;
      while (pl > (size_t)0U)
      {
        size_t l = pl;
        size_t l_ = pn % l;
        pn = l;
        pl = l_;
      }
      size_t d = pn;
      size_t q = Pulse_Lib_Slice_len__uint8_t(sp1) / d;
      size_t pi = (size_t)0U;
      while (pi < d)
      {
        size_t i = pi;
        uint8_t save = Pulse_Lib_Slice_op_Array_Access__uint8_t(sp1, i);
        size_t pj = (size_t)0U;
        size_t pidx = i;
        while (pj < q - (size_t)1U)
        {
          size_t j = pj;
          size_t idx = pidx;
          size_t idx_;
          if (idx - (size_t)0U >= Pulse_Lib_Slice_len__uint8_t(sp1) - soff)
            idx_ = idx - (Pulse_Lib_Slice_len__uint8_t(sp1) - soff);
          else
            idx_ = idx + (soff - (size_t)0U);
          size_t j_ = j + (size_t)1U;
          Pulse_Lib_Slice_op_Array_Assignment__uint8_t(sp1,
            idx,
            Pulse_Lib_Slice_op_Array_Access__uint8_t(sp1, idx_));
          pj = j_;
          pidx = idx_;
        }
        Pulse_Lib_Slice_op_Array_Assignment__uint8_t(sp1, pidx, save);
        pi = i + (size_t)1U;
      }
    }
    return llen;
  }
  else
    return (size_t)0U;
}

static size_t
CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_map_(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t off
)
{
  size_t rem = Pulse_Lib_Slice_len__uint8_t(out) - off;
  Custard_Prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP, len);
  if (CBOR_Pulse_Raw_Format_Serialize_size_header(h, &rem))
  {
    size_t llen = CBOR_Pulse_Raw_Format_Serialize_write_header(h, out, off);
    CBOR_Pulse_Raw_Slice_byte_slice sp1 = Pulse_Lib_Slice_split__uint8_t(out, llen)._1;
    if (!(off == (size_t)0U || off == Pulse_Lib_Slice_len__uint8_t(sp1)))
    {
      size_t pn = Pulse_Lib_Slice_len__uint8_t(sp1);
      size_t pl = off;
      while (pl > (size_t)0U)
      {
        size_t l = pl;
        size_t l_ = pn % l;
        pn = l;
        pl = l_;
      }
      size_t d = pn;
      size_t q = Pulse_Lib_Slice_len__uint8_t(sp1) / d;
      size_t pi = (size_t)0U;
      while (pi < d)
      {
        size_t i = pi;
        uint8_t save = Pulse_Lib_Slice_op_Array_Access__uint8_t(sp1, i);
        size_t pj = (size_t)0U;
        size_t pidx = i;
        while (pj < q - (size_t)1U)
        {
          size_t j = pj;
          size_t idx = pidx;
          size_t idx_;
          if (idx - (size_t)0U >= Pulse_Lib_Slice_len__uint8_t(sp1) - off)
            idx_ = idx - (Pulse_Lib_Slice_len__uint8_t(sp1) - off);
          else
            idx_ = idx + (off - (size_t)0U);
          size_t j_ = j + (size_t)1U;
          Pulse_Lib_Slice_op_Array_Assignment__uint8_t(sp1,
            idx,
            Pulse_Lib_Slice_op_Array_Access__uint8_t(sp1, idx_));
          pj = j_;
          pidx = idx_;
        }
        Pulse_Lib_Slice_op_Array_Assignment__uint8_t(sp1, pidx, save);
        pi = i + (size_t)1U;
      }
    }
    return llen;
  }
  else
    return (size_t)0U;
}

static size_t
CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_map(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t off
)
{
  return CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_map_(len, out, off);
}

static int16_t CBOR_Pulse_API_Det_Common_cbor_raw_compare(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Compare_impl_cbor_compare(x1, x2);
}

static int16_t
CBOR_Pulse_API_Det_Common_cbor_map_entry_raw_compare(cbor_map_entry x1, cbor_map_entry x2)
{
  return
    CBOR_Pulse_API_Det_Common_cbor_raw_compare(x1.cbor_map_entry_key,
      x2.cbor_map_entry_key);
}

static void
Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a,
  size_t i,
  cbor_map_entry v
)
{
  a.elt[i] = v;
}

bool
CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a
)
{
  size_t len = Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(a);
  if (len < (size_t)2U)
    return true;
  else
  {
    size_t len_half = len / (size_t)2U;
    FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
    scrut = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_map_entry(a, len_half);
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a2 = scrut._2;
    if (!CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(scrut._1))
      return false;
    else if (!CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(a2))
      return false;
    else
    {
      size_t pi1 = (size_t)0U;
      size_t pi2 = len_half;
      bool pres = true;
      size_t i10 = pi1;
      size_t i20 = pi2;
      bool res20 = pres;
      bool
      cond =
        res20 && !(i10 == i20 || i20 == Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(a));
      while (cond)
      {
        size_t i1 = pi1;
        cbor_map_entry
        x1 = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i1);
        size_t i20 = pi2;
        int16_t
        comp =
          CBOR_Pulse_API_Det_Common_cbor_map_entry_raw_compare(x1,
            Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i20));
        if (comp == 0)
          pres = false;
        else if (comp < 0)
          pi1 = i1 + (size_t)1U;
        else
        {
          size_t i2_ = i20 + (size_t)1U;
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
          ac1 =
            Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_map_entry(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_Type_cbor_map_entry(a,
                i2_)._1,
              i1)._2;
          if
          (
            !(i20 - i1 == (size_t)0U ||
              i20 - i1 == Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1))
          )
          {
            size_t pn = Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1);
            size_t pl = i20 - i1;
            while (pl > (size_t)0U)
            {
              size_t l = pl;
              size_t l_ = pn % l;
              pn = l;
              pl = l_;
            }
            size_t d = pn;
            size_t q = Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1) / d;
            size_t pi = (size_t)0U;
            while (pi < d)
            {
              size_t i = pi;
              cbor_map_entry
              save = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1, i);
              size_t pj = (size_t)0U;
              size_t pidx = i;
              while (pj < q - (size_t)1U)
              {
                size_t j = pj;
                size_t idx = pidx;
                size_t idx_;
                if
                (
                  idx - (size_t)0U >=
                    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1) - (i20 - i1)
                )
                  idx_ =
                    idx -
                      (Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1) - (i20 - i1));
                else
                  idx_ = idx + (i20 - i1 - (size_t)0U);
                size_t j_ = j + (size_t)1U;
                Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1,
                  idx,
                  Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1, idx_));
                pj = j_;
                pidx = idx_;
              }
              Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1,
                pidx,
                save);
              pi = i + (size_t)1U;
            }
          }
          pi1 = i1 + (size_t)1U;
          pi2 = i2_;
        }
        size_t i10 = pi1;
        size_t i2 = pi2;
        bool res2 = pres;
        cond =
          res2 && !(i10 == i2 || i2 == Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(a));
      }
      return pres;
    }
  }
}

static bool
CBOR_Pulse_API_Det_Common_cbor_raw_sort(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a
)
{
  return CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(a);
}

static int16_t CBOR_Pulse_API_Det_Common_impl_cbor_det_compare(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Compare_impl_cbor_compare(x1, x2);
}

static cbor_raw CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot(cbor_raw c)
{
  return c;
}

static cbor_map_entry CBOR_Pulse_Raw_Match_cbor_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  return
    (
      (cbor_map_entry){
        .cbor_map_entry_key = CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot(xk),
        .cbor_map_entry_value = CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot(xv)
      }
    );
}

cbor_raw cbor_det_reset_perm(cbor_raw x1)
{
  return CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot(x1);
}

static CBOR_Pulse_Raw_Slice_byte_slice
Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((CBOR_Pulse_Raw_Slice_byte_slice){ .elt = a, .len = alen });
}

size_t cbor_det_validate(uint8_t *input, size_t input_len)
{
  return
    CBOR_Pulse_Raw_Format_Parse_cbor_validate_det(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input,
        input_len));
}

cbor_raw cbor_det_parse(uint8_t *input, size_t len)
{
  CBOR_Pulse_Raw_Slice_byte_slice
  s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input, len);
  return CBOR_Pulse_Raw_Format_Parse_cbor_parse(s, Pulse_Lib_Slice_len__uint8_t(s));
}

size_t cbor_det_size(cbor_raw x, size_t bound)
{
  return CBOR_Pulse_Raw_Format_Serialize_cbor_size(x, bound);
}

size_t cbor_det_serialize(cbor_raw x, uint8_t *output, size_t output_len)
{
  return
    CBOR_Pulse_Raw_Format_Serialize_cbor_serialize(x,
      Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(output, output_len));
}

size_t cbor_det_serialize_safe(cbor_raw x, uint8_t *output, size_t output_len)
{
  size_t sz = cbor_det_size(x, output_len);
  if (sz == (size_t)0U)
    return (size_t)0U;
  else
    return cbor_det_serialize(x, output, sz);
}

bool cbor_det_impl_utf8_correct_from_array(uint8_t *s, size_t len)
{
  return
    CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(s,
        len));
}

cbor_raw cbor_det_mk_simple_value(uint8_t v)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = v } });
}

cbor_raw cbor_det_mk_int64(uint8_t ty, uint64_t v)
{
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Int,
        {
          .case_CBOR_Case_Int = {
            .cbor_int_type = ty,
            .cbor_int_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64(v).size,
            .cbor_int_value = CBOR_Spec_Raw_Optimal_mk_raw_uint64(v).value
          }
        }
      }
    );
}

cbor_raw cbor_det_mk_tagged(uint64_t tag, cbor_raw *r)
{
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Tagged,
        {
          .case_CBOR_Case_Tagged = {
            .cbor_tagged_tag = CBOR_Spec_Raw_Optimal_mk_raw_uint64(tag),
            .cbor_tagged_ptr = r
          }
        }
      }
    );
}

bool cbor_det_mk_byte_string_from_arrayptr(uint8_t *a, uint64_t len, cbor_raw *dest)
{
  bool __anf0 = a == NULL;
  if (__anf0 || dest == NULL)
    return false;
  else
  {
    CBOR_Pulse_Raw_Slice_byte_slice
    s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
    bool ite;
    if (CBOR_MAJOR_TYPE_BYTE_STRING == CBOR_MAJOR_TYPE_TEXT_STRING)
      ite = CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(s);
    else
      ite = true;
    if (ite)
    {
      dest[0U] =
        (
          (cbor_raw){
            .tag = CBOR_Case_String,
            {
              .case_CBOR_Case_String = {
                .cbor_string_type = CBOR_MAJOR_TYPE_BYTE_STRING,
                .cbor_string_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__uint8_t(s)).size,
                .cbor_string_ptr = s
              }
            }
          }
        );
      return true;
    }
    else
      return false;
  }
}

bool cbor_det_mk_text_string_from_arrayptr(uint8_t *a, uint64_t len, cbor_raw *dest)
{
  bool __anf0 = a == NULL;
  if (__anf0 || dest == NULL)
    return false;
  else
  {
    CBOR_Pulse_Raw_Slice_byte_slice
    s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
    if (CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(s))
    {
      dest[0U] =
        (
          (cbor_raw){
            .tag = CBOR_Case_String,
            {
              .case_CBOR_Case_String = {
                .cbor_string_type = CBOR_MAJOR_TYPE_TEXT_STRING,
                .cbor_string_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__uint8_t(s)).size,
                .cbor_string_ptr = s
              }
            }
          }
        );
      return true;
    }
    else
      return false;
  }
}

cbor_raw cbor_det_mk_array_from_array(cbor_raw *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
  s = Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_Type_cbor_raw(a, (size_t)len);
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Array,
        {
          .case_CBOR_Case_Array = {
            .cbor_array_length_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(s)).size,
            .cbor_array_ptr = s
          }
        }
      }
    );
}

cbor_map_entry cbor_det_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  return CBOR_Pulse_Raw_Match_cbor_mk_map_entry(xk, xv);
}

cbor_raw cbor_det_mk_map_from_array(cbor_map_entry *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
  s = Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(a, (size_t)len);
  cbor_raw dest = dummy_cbor_det_t();
  bool ite0;
  if
  (
    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(s) / (size_t)32768U / (size_t)32768U /
      (size_t)32768U
    / (size_t)32768U
    < (size_t)16U
  )
    ite0 = true;
  else
    ite0 = false;
  bool ite;
  if (!ite0)
    ite = false;
  else if (CBOR_Pulse_API_Det_Common_cbor_raw_sort(s))
  {
    dest =
      (
        (cbor_raw){
          .tag = CBOR_Case_Map,
          {
            .case_CBOR_Case_Map = {
              .cbor_map_length_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(s)).size,
              .cbor_map_ptr = s
            }
          }
        }
      );
    ite = true;
  }
  else
    ite = false;
  KRML_MAYBE_UNUSED_VAR(ite);
  return dest;
}

bool cbor_det_mk_map_from_array_safe(cbor_map_entry *a, uint64_t len, cbor_raw *dest)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
  s = Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(a, (size_t)len);
  bool ite;
  if
  (
    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(s) / (size_t)32768U / (size_t)32768U /
      (size_t)32768U
    / (size_t)32768U
    < (size_t)16U
  )
    ite = true;
  else
    ite = false;
  if (!ite)
    return false;
  else if (CBOR_Pulse_API_Det_Common_cbor_raw_sort(s))
  {
    dest[0U] =
      (
        (cbor_raw){
          .tag = CBOR_Case_Map,
          {
            .case_CBOR_Case_Map = {
              .cbor_map_length_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(s)).size,
              .cbor_map_ptr = s
            }
          }
        }
      );
    return true;
  }
  else
    return false;
}

bool cbor_det_equal(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Compare_impl_cbor_compare(x1, x2) == 0;
}

uint8_t cbor_det_major_type(cbor_raw x)
{
  return CBOR_Pulse_Raw_Compare_impl_major_type(x);
}

uint8_t cbor_det_read_simple_value(cbor_raw x)
{
  if (x.tag == CBOR_Case_Simple)
    return x.case_CBOR_Case_Simple;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint64_t cbor_det_read_uint64(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_Int)
  {
    cbor_int c_ = x.case_CBOR_Case_Int;
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
  }
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

uint64_t cbor_det_get_string_length(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_String)
  {
    cbor_string c_ = x.case_CBOR_Case_String;
    ite =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = c_.cbor_string_size,
          .value = (uint64_t)Pulse_Lib_Slice_len__uint8_t(c_.cbor_string_ptr)
        }
      );
  }
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

uint64_t cbor_det_get_tagged_tag(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_Tagged)
    ite = x.case_CBOR_Case_Tagged.cbor_tagged_tag;
  else if (x.tag == CBOR_Case_Serialized_Tagged)
    ite = x.case_CBOR_Case_Serialized_Tagged.cbor_serialized_header;
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

cbor_raw cbor_det_get_tagged_payload(cbor_raw x)
{
  return CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload(x);
}

static uint8_t
*Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(CBOR_Pulse_Raw_Slice_byte_slice s)
{
  return s.elt;
}

uint8_t *cbor_det_get_string(cbor_raw x)
{
  CBOR_Pulse_Raw_Slice_byte_slice ite;
  if (x.tag == CBOR_Case_String)
    ite = x.case_CBOR_Case_String.cbor_string_ptr;
  else
    ite =
      KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
        "unreachable (pattern matches are exhaustive in F*)");
  return Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(ite);
}

uint64_t cbor_det_get_array_length(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_Array)
  {
    cbor_array c_ = x.case_CBOR_Case_Array;
    ite =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = c_.cbor_array_length_size,
          .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Array)
    ite = x.case_CBOR_Case_Serialized_Array.cbor_serialized_header;
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

cbor_det_array_iterator_t cbor_det_array_iterator_start(cbor_raw x)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_init(x);
}

bool cbor_det_array_iterator_is_empty(cbor_det_array_iterator_t x)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_is_empty(x);
}

uint64_t cbor_det_array_iterator_length(cbor_det_array_iterator_t x)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_length(x);
}

cbor_raw cbor_det_array_iterator_next(cbor_det_array_iterator_t *x)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_next(x);
}

cbor_det_array_iterator_t
cbor_det_array_iterator_truncate(cbor_det_array_iterator_t x, uint64_t len)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_truncate(x, len);
}

cbor_raw cbor_det_get_array_item(cbor_raw x, uint64_t i)
{
  return CBOR_Pulse_Raw_Read_cbor_array_item(x, i);
}

uint64_t cbor_det_get_map_length(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_Map)
  {
    cbor_map c_ = x.case_CBOR_Case_Map;
    ite =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = c_.cbor_map_length_size,
          .value = (uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Map)
    ite = x.case_CBOR_Case_Serialized_Map.cbor_serialized_header;
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

cbor_det_map_iterator_t cbor_det_map_iterator_start(cbor_raw x)
{
  return CBOR_Pulse_Raw_Read_cbor_map_iterator_init(x);
}

bool cbor_det_map_iterator_is_empty(cbor_det_map_iterator_t x)
{
  return CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty(x);
}

cbor_map_entry cbor_det_map_iterator_next(cbor_det_map_iterator_t *x)
{
  return CBOR_Pulse_Raw_Read_cbor_map_iterator_next(x);
}

cbor_raw cbor_det_map_entry_key(cbor_map_entry x2)
{
  return x2.cbor_map_entry_key;
}

cbor_raw cbor_det_map_entry_value(cbor_map_entry x2)
{
  return x2.cbor_map_entry_value;
}

typedef struct FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  cbor_raw v;
}
FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw;

bool cbor_det_map_get(cbor_raw x, cbor_raw k, cbor_raw *dest)
{
  cbor_det_map_iterator_t i = CBOR_Pulse_Raw_Read_cbor_map_iterator_init(x);
  cbor_det_map_iterator_t pi = i;
  FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw
  pres = { .tag = FStar_Pervasives_Native_None };
  bool pcont = !CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty(i);
  while (pcont)
  {
    cbor_map_entry entry = CBOR_Pulse_Raw_Read_cbor_map_iterator_next(&pi);
    int16_t comp = CBOR_Pulse_API_Det_Common_impl_cbor_det_compare(entry.cbor_map_entry_key, k);
    if (comp == 0)
    {
      pres =
        (
          (FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw){
            .tag = FStar_Pervasives_Native_Some,
            .v = entry.cbor_map_entry_value
          }
        );
      pcont = false;
    }
    else if (comp > 0)
      pcont = false;
    else
      pcont = !CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty(pi);
  }
  FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw scrut = pres;
  if (scrut.tag == FStar_Pervasives_Native_None)
    return false;
  else if (scrut.tag == FStar_Pervasives_Native_Some)
  {
    dest[0U] = scrut.v;
    return true;
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

size_t cbor_det_serialize_tag_to_array(uint64_t tag, uint8_t *out, size_t out_len)
{
  CBOR_Pulse_Raw_Slice_byte_slice
  sout = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out, out_len);
  return
    CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_tag(CBOR_Spec_Raw_Optimal_mk_raw_uint64(tag),
      sout);
}

size_t
cbor_det_serialize_array_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off)
{
  CBOR_Pulse_Raw_Slice_byte_slice
  sout = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out, out_len);
  return
    CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_array(CBOR_Spec_Raw_Optimal_mk_raw_uint64(len),
      sout,
      off);
}

size_t
cbor_det_serialize_string_to_array(uint8_t ty, uint64_t off, uint8_t *out, size_t out_len)
{
  CBOR_Pulse_Raw_Slice_byte_slice
  sout = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out, out_len);
  return
    CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_string(ty,
      CBOR_Spec_Raw_Optimal_mk_raw_uint64(off),
      sout);
}

bool
cbor_det_serialize_map_insert_to_array(uint8_t *out, size_t out_len, size_t off2, size_t off3)
{
  return
    CBOR_Pulse_Raw_Insert_cbor_raw_map_insert(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out,
        out_len),
      off2,
      off3);
}

size_t cbor_det_serialize_map_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off)
{
  CBOR_Pulse_Raw_Slice_byte_slice
  sout = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out, out_len);
  return
    CBOR_Pulse_Raw_Format_Serialize_cbor_serialize_map(CBOR_Spec_Raw_Optimal_mk_raw_uint64(len),
      sout,
      off);
}

cbor_raw cbor_get_from_freeable(cbor_freeable x)
{
  return x.cbor;
}

cbor_freeable cbor_copy(cbor_raw c)
{
  return cbor_copy0(c);
}

void cbor_free(cbor_freeable x)
{
  cbor_free0(x);
}

cbor_raw dummy_cbor_det_t(void)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } });
}


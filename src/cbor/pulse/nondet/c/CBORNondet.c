

#include "internal/CBORNondet.h"

#include "CBORNondetType.h"
#include "CBORNondetAlloc.h"

static uint8_t LowParse_BitFields_get_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi)
{
  return ((uint32_t)x << (8U - hi) & 0xFFU) >> (8U - hi + lo);
}

static uint8_t
LowParse_BitFields_set_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi, uint8_t v)
{
  return ((uint32_t)x & (~(255U >> (8U - (hi - lo)) << lo) & 0xFFU)) | (uint32_t)v << lo;
}

static size_t Pulse_Lib_Slice_len__uint8_t(CBOR_Pulse_Raw_Slice_byte_slice s)
{
  return s.len;
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
  while (true)
  {
    size_t i = pi;
    if (!(pres && i < len))
      break;
    size_t i0 = pi;
    uint8_t byte1 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s, i0);
    size_t i1 = i0 + (size_t)1U;
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
          else if (0xf1U <= byte1 && byte1 < 0xf4U && 0x80U <= byte2 && byte2 <= 0xbfU)
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

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS ((uint8_t)24U)

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_UNASSIGNED_MIN ((uint8_t)28U)

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS ((uint8_t)25U)

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS ((uint8_t)26U)

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS ((uint8_t)27U)

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
prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument_s
{
  CBOR_Spec_Raw_EverParse_initial_byte_t _1;
  CBOR_Spec_Raw_EverParse_long_argument _2;
}
prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument;

static uint8_t
CBOR_Spec_Raw_EverParse_get_header_major_type(
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument h
)
{
  return h._1.major_type;
}

static prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(uint8_t t, CBOR_Spec_Raw_Base_raw_uint64 x)
{
  return
    x.size == 0U ? (
                   (prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
                     ._1 = { .major_type = t, .additional_info = (uint8_t)x.value },
                     ._2 = { .tag = CBOR_Spec_Raw_EverParse_LongArgumentOther }
                   }
                 )
                 : x.size == 1U ? (
                                  (prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
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
                                                 (prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
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
                                                                (prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
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
                                                                (prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
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

static prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
CBOR_Spec_Raw_EverParse_simple_value_as_argument(uint8_t x)
{
  return
    x <= MAX_SIMPLE_VALUE_ADDITIONAL_INFO ? (
                                            (prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
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
                                            (prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
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
  size_t offset = *poffset;
  size_t offset1 = *poffset;
  size_t offset2 = *poffset;
  bool ite0;
  if (Pulse_Lib_Slice_len__uint8_t(input) - offset2 < (size_t)1U)
    ite0 = false;
  else
  {
    *poffset = offset2 + (size_t)1U;
    ite0 = true;
  }
  bool ite1;
  if (ite0)
  {
    size_t off = *poffset;
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
    size_t off = *poffset;
    CBOR_Spec_Raw_EverParse_initial_byte_t
    x =
      CBOR_Pulse_Raw_EverParse_Format_read_initial_byte_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
            offset)._2,
          off - offset)._1);
    if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
      if (x.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      {
        size_t offset3 = *poffset;
        size_t offset4 = *poffset;
        bool ite;
        if (Pulse_Lib_Slice_len__uint8_t(input) - offset4 < (size_t)1U)
          ite = false;
        else
        {
          *poffset = offset4 + (size_t)1U;
          ite = true;
        }
        if (ite)
        {
          size_t off1 = *poffset;
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
        size_t offset3 = *poffset;
        if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < (size_t)1U)
          return false;
        else
        {
          *poffset = offset3 + (size_t)1U;
          return true;
        }
      }
    else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    {
      size_t offset3 = *poffset;
      if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < (size_t)2U)
        return false;
      else
      {
        *poffset = offset3 + (size_t)2U;
        return true;
      }
    }
    else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    {
      size_t offset3 = *poffset;
      if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < (size_t)4U)
        return false;
      else
      {
        *poffset = offset3 + (size_t)4U;
        return true;
      }
    }
    else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    {
      size_t offset3 = *poffset;
      if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < (size_t)8U)
        return false;
      else
      {
        *poffset = offset3 + (size_t)8U;
        return true;
      }
    }
    else
      return true;
  }
  else
    return false;
}

static prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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
    uint8_t
    last4 =
      Pulse_Lib_Slice_op_Array_Access__uint8_t(input2,
        (size_t)7U - (size_t)1U - (size_t)1U - (size_t)1U - (size_t)1U);
    size_t pos_4 = (size_t)7U - (size_t)1U - (size_t)1U - (size_t)1U - (size_t)1U - (size_t)1U;
    uint8_t last5 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, pos_4);
    uint8_t last6 = Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, pos_4 - (size_t)1U);
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
      (prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument){
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
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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
        arg64 <= (uint64_t)bound
    )
    {
      *prem = (size_t)arg64;
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
        arg64 <= (uint64_t)bound
    )
    {
      size_t arg = (size_t)arg64;
      if (bound - arg < arg)
        return true;
      else
      {
        *prem = arg + arg;
        return false;
      }
    }
    else
      return true;
  }
  else if (typ == CBOR_MAJOR_TYPE_TAGGED)
  {
    *prem = (size_t)1U;
    return false;
  }
  else
  {
    *prem = (size_t)0U;
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
  while (true)
  {
    size_t n0 = pn;
    if (!(pres && n0 > (size_t)0U))
      break;
    size_t off = *poffset;
    size_t n = pn;
    if (n > Pulse_Lib_Slice_len__uint8_t(input) - off)
      pres = false;
    else
    {
      size_t offset = *poffset;
      bool ite0;
      if (CBOR_Pulse_Raw_EverParse_Format_validate_header(input, poffset))
      {
        size_t off1 = *poffset;
        prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
        x =
          CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
                offset)._2,
              off1 - offset)._1);
        CBOR_Spec_Raw_EverParse_initial_byte_t b = x._1;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        {
          size_t offset1 = *poffset;
          size_t offset2 = *poffset;
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
            *poffset = offset2 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x._1, x._2);
            ite = true;
          }
          else
            ite = false;
          if (ite)
          {
            size_t off2 = *poffset;
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
        size_t offset1 = *poffset;
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
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument h
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
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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

static bool
CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_map_length_bounded(
  size_t n,
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t *poffset
)
{
  size_t pn = (size_t)1U;
  bool pres = true;
  while (true)
  {
    size_t n10 = pn;
    if (!(pres && n10 > (size_t)0U))
      break;
    size_t off = *poffset;
    size_t n1 = pn;
    if (n1 > Pulse_Lib_Slice_len__uint8_t(input) - off)
      pres = false;
    else
    {
      size_t offset = *poffset;
      bool ite0;
      if (CBOR_Pulse_Raw_EverParse_Format_validate_header(input, poffset))
      {
        size_t off1 = *poffset;
        prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
        x =
          CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
                offset)._2,
              off1 - offset)._1);
        CBOR_Spec_Raw_EverParse_initial_byte_t b = x._1;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        {
          size_t offset1 = *poffset;
          size_t offset2 = *poffset;
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
            *poffset = offset2 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x._1, x._2);
            ite = true;
          }
          else
            ite = false;
          if (ite)
          {
            size_t off2 = *poffset;
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
        size_t offset1 = *poffset;
        CBOR_Pulse_Raw_Slice_byte_slice
        input1 =
          Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, off)._2,
            offset1 - off)._1;
        prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
        h =
          CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(input1,
              CBOR_Pulse_Raw_EverParse_Format_jump_header(input1, (size_t)0U))._1);
        bool ite;
        if (CBOR_Spec_Raw_EverParse_get_header_major_type(h) == CBOR_MAJOR_TYPE_MAP)
        {
          uint64_t arg64 = CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
          ite =
            n / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U >= (size_t)16U ||
              arg64 <= (uint64_t)n;
        }
        else
          ite = true;
        if (!ite)
          pres = false;
        else
        {
          size_t bound = Pulse_Lib_Slice_len__uint8_t(input) - off - n1;
          bool
          res2 =
            CBOR_Pulse_Raw_EverParse_Format_validate_recursive_step_count_leaf(input1,
              bound,
              &pn);
          size_t count = pn;
          if (res2 || count > bound)
            pres = false;
          else
            pn = n1 - (size_t)1U + count;
        }
      }
    }
  }
  return pres;
}

bool
CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_nlist_bounded(
  size_t map_length_bound,
  size_t d,
  size_t n,
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t *poffset
)
{
  size_t pn = n;
  bool pres = true;
  while (true)
  {
    size_t n10 = pn;
    if (!(pres && n10 > (size_t)0U))
      break;
    size_t off = *poffset;
    size_t n1 = pn;
    if (n1 > Pulse_Lib_Slice_len__uint8_t(input) - off)
      pres = false;
    else
    {
      size_t offset = *poffset;
      bool ite0;
      if (CBOR_Pulse_Raw_EverParse_Format_validate_header(input, poffset))
      {
        size_t off1 = *poffset;
        prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
        x =
          CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
                offset)._2,
              off1 - offset)._1);
        CBOR_Spec_Raw_EverParse_initial_byte_t b = x._1;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        {
          size_t offset1 = *poffset;
          size_t offset2 = *poffset;
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
            *poffset = offset2 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x._1, x._2);
            ite = true;
          }
          else
            ite = false;
          if (ite)
          {
            size_t off2 = *poffset;
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
        size_t offset1 = *poffset;
        CBOR_Pulse_Raw_Slice_byte_slice
        input1 =
          Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, off)._2,
            offset1 - off)._1;
        size_t bound = Pulse_Lib_Slice_len__uint8_t(input) - off - n1;
        prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
        h =
          CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(input1,
              CBOR_Pulse_Raw_EverParse_Format_jump_header(input1, (size_t)0U))._1);
        uint8_t typ = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
        uint8_t r;
        if (typ == CBOR_MAJOR_TYPE_ARRAY)
        {
          uint64_t arg64 = CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
          if
          (
            bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U >= (size_t)16U
            || arg64 <= (uint64_t)bound
          )
          {
            pn = (size_t)arg64;
            r = 2U;
          }
          else
            r = 1U;
        }
        else if (typ == CBOR_MAJOR_TYPE_MAP)
        {
          uint64_t arg64 = CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
          if
          (
            !(map_length_bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U
            >= (size_t)16U
            || arg64 <= (uint64_t)map_length_bound)
          )
            r = 0U;
          else if
          (
            bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U >= (size_t)16U
            || arg64 <= (uint64_t)bound
          )
          {
            size_t arg = (size_t)arg64;
            if (bound - arg < arg)
              r = 1U;
            else
            {
              pn = arg + arg;
              r = 3U;
            }
          }
          else
            r = 1U;
        }
        else if (typ == CBOR_MAJOR_TYPE_TAGGED)
        {
          pn = (size_t)1U;
          r = 2U;
        }
        else
        {
          pn = (size_t)0U;
          r = 2U;
        }
        if (r == 0U)
          pres = false;
        else
        {
          size_t count = pn;
          if (r == 1U || count > bound)
            pres = false;
          else if (r == 3U)
            if (d == (size_t)0U)
              pres = false;
            else if
            (
              !CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_nlist_bounded(map_length_bound,
                d - (size_t)1U,
                count,
                input,
                poffset)
            )
              pres = false;
            else
              pn = n1 - (size_t)1U;
          else
            pn = n1 - (size_t)1U + count;
        }
      }
    }
  }
  return pres;
}

static bool
CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_bounded(
  size_t map_depth_bound,
  size_t map_length_bound,
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t *poffset
)
{
  return
    CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_nlist_bounded(map_length_bound,
      map_depth_bound,
      (size_t)1U,
      input,
      poffset);
}

static cbor_raw
CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(CBOR_Pulse_Raw_Slice_byte_slice input)
{
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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

static cbor_raw
CBOR_Pulse_Raw_Format_Parse_cbor_parse(CBOR_Pulse_Raw_Slice_byte_slice input, size_t len)
{
  return
    CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input,
          (size_t)0U)._2,
        len - (size_t)0U)._1);
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

static uint64_t
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_length(
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator c
)
{
  return c.len;
}

static cbor_raw
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_next(
  cbor_nondet_array_iterator_t *pi,
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator i
)
{
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut =
    Pulse_Lib_Slice_split__uint8_t(i.s,
      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(i.s, (size_t)0U));
  CBOR_Pulse_Raw_Slice_byte_slice s2 = scrut._2;
  cbor_raw res = CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(scrut._1);
  *pi =
    (
      (cbor_nondet_array_iterator_t){
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
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_next(
  cbor_nondet_map_iterator_t *pi,
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
  *pi =
    (
      (cbor_nondet_map_iterator_t){
        .tag = CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = { .s = s2, .len = i.len - 1ULL } }
      }
    );
  return res;
}

static cbor_raw
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_next_with_depth(
  cbor_nondet_array_iterator_t *pi,
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator i
)
{
  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
  scrut =
    Pulse_Lib_Slice_split__uint8_t(i.s,
      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(i.s, (size_t)0U));
  CBOR_Pulse_Raw_Slice_byte_slice s2 = scrut._2;
  cbor_raw res = CBOR_Pulse_Raw_EverParse_Serialized_Base_cbor_read(scrut._1);
  *pi =
    (
      (cbor_nondet_array_iterator_t){
        .tag = CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = { .s = s2, .len = i.len - 1ULL } }
      }
    );
  return res;
}

static cbor_map_entry
CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_next_with_depth(
  cbor_nondet_map_iterator_t *pi,
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
  *pi =
    (
      (cbor_nondet_map_iterator_t){
        .tag = CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = { .s = s2, .len = i.len - 1ULL } }
      }
    );
  return res;
}

static cbor_raw CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Tagged)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_match_serialized_tagged_get_payload(c.case_CBOR_Case_Serialized_Tagged);
  else if (c.tag == CBOR_Case_Tagged)
    return *c.case_CBOR_Case_Tagged.cbor_tagged_ptr;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_nondet_array_iterator_t CBOR_Pulse_Raw_Read_cbor_array_iterator_init(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Array)
    return
      (
        (cbor_nondet_array_iterator_t){
          .tag = CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_init(c.case_CBOR_Case_Serialized_Array)
          }
        }
      );
  else if (c.tag == CBOR_Case_Array)
    return
      (
        (cbor_nondet_array_iterator_t){
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

static size_t
Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s
)
{
  return s.len;
}

static bool CBOR_Pulse_Raw_Read_cbor_array_iterator_is_empty(cbor_nondet_array_iterator_t c)
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

static uint64_t CBOR_Pulse_Raw_Read_cbor_array_iterator_length(cbor_nondet_array_iterator_t c)
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

static cbor_raw
Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw a,
  size_t i
)
{
  return a.elt[i];
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

static cbor_raw CBOR_Pulse_Raw_Read_cbor_array_iterator_next(cbor_nondet_array_iterator_t *pi)
{
  cbor_nondet_array_iterator_t scrut = *pi;
  if (scrut.tag == CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i = scrut.case_CBOR_Raw_Iterator_Slice;
    cbor_raw res = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)0U);
    *pi =
      (
        (cbor_nondet_array_iterator_t){
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

static cbor_nondet_array_iterator_t
CBOR_Pulse_Raw_Read_cbor_array_iterator_truncate(cbor_nondet_array_iterator_t c, uint64_t len)
{
  if (c.tag == CBOR_Raw_Iterator_Slice)
    return
      (
        (cbor_nondet_array_iterator_t){
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
        (cbor_nondet_array_iterator_t){
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

static cbor_nondet_map_iterator_t CBOR_Pulse_Raw_Read_cbor_map_iterator_init(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Map)
    return
      (
        (cbor_nondet_map_iterator_t){
          .tag = CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_init(c.case_CBOR_Case_Serialized_Map)
          }
        }
      );
  else if (c.tag == CBOR_Case_Map)
    return
      (
        (cbor_nondet_map_iterator_t){
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

static size_t
Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry s
)
{
  return s.len;
}

static bool CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty(cbor_nondet_map_iterator_t c)
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

static cbor_map_entry
Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a,
  size_t i
)
{
  return a.elt[i];
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

static cbor_map_entry
CBOR_Pulse_Raw_Read_cbor_map_iterator_next(cbor_nondet_map_iterator_t *pi)
{
  cbor_nondet_map_iterator_t scrut = *pi;
  if (scrut.tag == CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
    i = scrut.case_CBOR_Raw_Iterator_Slice;
    cbor_map_entry
    res = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i, (size_t)0U);
    *pi =
      (
        (cbor_nondet_map_iterator_t){
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

static cbor_raw CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Tagged)
    return
      CBOR_Pulse_Raw_Format_Serialized_cbor_match_serialized_tagged_get_payload(c.case_CBOR_Case_Serialized_Tagged);
  else if (c.tag == CBOR_Case_Tagged)
    return *c.case_CBOR_Case_Tagged.cbor_tagged_ptr;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_nondet_array_iterator_t
CBOR_Pulse_Raw_Read_cbor_array_iterator_init_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Array)
    return
      (
        (cbor_nondet_array_iterator_t){
          .tag = CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_init(c.case_CBOR_Case_Serialized_Array)
          }
        }
      );
  else if (c.tag == CBOR_Case_Array)
    return
      (
        (cbor_nondet_array_iterator_t){
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

static bool
CBOR_Pulse_Raw_Read_cbor_array_iterator_is_empty_with_depth(cbor_nondet_array_iterator_t c)
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

static cbor_raw
CBOR_Pulse_Raw_Read_cbor_array_iterator_next_with_depth(cbor_nondet_array_iterator_t *pi)
{
  cbor_nondet_array_iterator_t scrut = *pi;
  if (scrut.tag == CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i = scrut.case_CBOR_Raw_Iterator_Slice;
    cbor_raw res = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)0U);
    *pi =
      (
        (cbor_nondet_array_iterator_t){
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
      CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_array_iterator_next_with_depth(pi,
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

static cbor_nondet_map_iterator_t
CBOR_Pulse_Raw_Read_cbor_map_iterator_init_with_depth(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Map)
    return
      (
        (cbor_nondet_map_iterator_t){
          .tag = CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_init(c.case_CBOR_Case_Serialized_Map)
          }
        }
      );
  else if (c.tag == CBOR_Case_Map)
    return
      (
        (cbor_nondet_map_iterator_t){
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

static bool
CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty_with_depth(cbor_nondet_map_iterator_t c)
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

static cbor_map_entry
CBOR_Pulse_Raw_Read_cbor_map_iterator_next_with_depth(cbor_nondet_map_iterator_t *pi)
{
  cbor_nondet_map_iterator_t scrut = *pi;
  if (scrut.tag == CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
    i = scrut.case_CBOR_Raw_Iterator_Slice;
    cbor_map_entry
    res = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i, (size_t)0U);
    *pi =
      (
        (cbor_nondet_map_iterator_t){
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
      CBOR_Pulse_Raw_Format_Serialized_cbor_serialized_map_iterator_next_with_depth(pi,
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
        .size = x <= (uint64_t)(uint32_t)MAX_SIMPLE_VALUE_ADDITIONAL_INFO ? 0U
                                                                          : x < 256ULL ? 1U
                                                                                       : x <
                                                                                         65536ULL ? 2U
                                                                                                  : x
                                                                                                  <
                                                                                                    4294967296ULL ? 3U
                                                                                                                  : 4U,
        .value = x
      }
    );
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

static prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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

static prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
CBOR_Pulse_Raw_Format_Serialize_cbor_raw_with_perm_get_header_d(cbor_raw xl)
{
  return CBOR_Pulse_Raw_Format_Serialize_cbor_raw_get_header_d(xl);
}

static CBOR_Spec_Raw_EverParse_initial_byte_t
fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument t
)
{
  return t._1;
}

static bool
CBOR_Pulse_Raw_Format_Serialize_size_header(
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument x,
  size_t *out
)
{
  CBOR_Spec_Raw_EverParse_initial_byte_t
  xh1 =
    fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  size_t capacity = *out;
  bool ite;
  if (capacity < (size_t)1U)
    ite = false;
  else
  {
    *out = capacity - (size_t)1U;
    ite = true;
  }
  if (ite)
    if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    {
      size_t capacity1 = *out;
      if (capacity1 < (size_t)1U)
        return false;
      else
      {
        *out = capacity1 - (size_t)1U;
        return true;
      }
    }
    else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    {
      size_t capacity1 = *out;
      if (capacity1 < (size_t)2U)
        return false;
      else
      {
        *out = capacity1 - (size_t)2U;
        return true;
      }
    }
    else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    {
      size_t capacity1 = *out;
      if (capacity1 < (size_t)4U)
        return false;
      else
      {
        *out = capacity1 - (size_t)4U;
        return true;
      }
    }
    else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    {
      size_t capacity1 = *out;
      if (capacity1 < (size_t)8U)
        return false;
      else
      {
        *out = capacity1 - (size_t)8U;
        return true;
      }
    }
    else
      return true;
  else
    return false;
}

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
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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
        size_t cur = *out;
        if (cur < length)
          return false;
        else
        {
          *out = cur - length;
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
          while (true)
          {
            size_t i = pi;
            if (!(pres && i < len))
              break;
            size_t i0 = pi;
            if
            (
              CBOR_Pulse_Raw_Format_Serialize_siz__d(Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(a,
                  i0),
                out)
            )
              pi = i0 + (size_t)1U;
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
          size_t cur = *out;
          if (cur < length)
            return false;
          else
          {
            *out = cur - length;
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
          while (true)
          {
            size_t i = pi;
            if (!(pres && i < len))
              break;
            size_t i0 = pi;
            cbor_map_entry
            e = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i0);
            bool ite;
            if (CBOR_Pulse_Raw_Format_Serialize_siz__d(e.cbor_map_entry_key, out))
              ite = CBOR_Pulse_Raw_Format_Serialize_siz__d(e.cbor_map_entry_value, out);
            else
              ite = false;
            if (ite)
              pi = i0 + (size_t)1U;
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
          size_t cur = *out;
          if (cur < length)
            return false;
          else
          {
            *out = cur - length;
            return true;
          }
        }
      else if (xh1._1.major_type == CBOR_MAJOR_TYPE_TAGGED)
        if (x_.tag == CBOR_Case_Tagged)
        {
          cbor_raw ite;
          if (x_.tag == CBOR_Case_Tagged)
            ite = *x_.case_CBOR_Case_Tagged.cbor_tagged_ptr;
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
          size_t cur = *out;
          if (cur < length)
            return false;
          else
          {
            *out = cur - length;
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
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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
        size_t cur = *out;
        if (cur < length)
          return false;
        else
        {
          *out = cur - length;
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
          size_t cur = *out;
          if (cur < length)
            return false;
          else
          {
            *out = cur - length;
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
          size_t cur = *out;
          if (cur < length)
            return false;
          else
          {
            *out = cur - length;
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
          size_t cur = *out;
          if (cur < length)
            return false;
          else
          {
            *out = cur - length;
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

static void
Pulse_Lib_Slice_op_Array_Assignment__uint8_t(
  CBOR_Pulse_Raw_Slice_byte_slice a,
  size_t i,
  uint8_t v
)
{
  a.elt[i] = v;
}

static CBOR_Spec_Raw_EverParse_long_argument
fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument t
)
{
  return t._2;
}

static size_t
CBOR_Pulse_Raw_Format_Serialize_write_header(
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument x,
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t offset
)
{
  CBOR_Spec_Raw_EverParse_initial_byte_t
  xh1 =
    fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
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
    fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
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

static void
Pulse_Lib_Slice_copy__uint8_t(
  CBOR_Pulse_Raw_Slice_byte_slice dst,
  CBOR_Pulse_Raw_Slice_byte_slice src
)
{
  memcpy(dst.elt, src.elt, src.len * sizeof (uint8_t));
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
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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
          ite = *x_.case_CBOR_Case_Tagged.cbor_tagged_ptr;
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
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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
  while (true)
  {
    size_t i1 = pi1;
    if (!(pres == 0 && i1 < n1))
      break;
    size_t i10 = pi1;
    uint8_t x1 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s1, i10);
    size_t i2 = pi2;
    int16_t
    c =
      CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(x1,
        Pulse_Lib_Slice_op_Array_Access__uint8_t(s2, i2));
    if (c == 0)
    {
      size_t i1_ = i10 + (size_t)1U;
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

static bool CBOR_Pulse_Raw_Util_eq_Some_true(FStar_Pervasives_Native_option__bool x)
{
  return x.tag == FStar_Pervasives_Native_Some && x.v;
}

static bool CBOR_Pulse_Raw_Util_eq_Some_false(FStar_Pervasives_Native_option__bool x)
{
  return x.tag == FStar_Pervasives_Native_Some && !x.v;
}

static bool CBOR_Pulse_Raw_Util_eq_Some_0sz(FStar_Pervasives_Native_option__size_t x)
{
  return x.tag == FStar_Pervasives_Native_Some && x.v == (size_t)0U;
}

bool
CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_aux(
  size_t bound,
  CBOR_Pulse_Raw_Slice_byte_slice *pl,
  size_t n1
)
{
  size_t pn = n1;
  bool pres = true;
  while (true)
  {
    size_t n = pn;
    if (!(pres && n > (size_t)0U))
      break;
    CBOR_Pulse_Raw_Slice_byte_slice l = *pl;
    size_t n_ = pn - (size_t)1U;
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
    scrut =
      Pulse_Lib_Slice_split__uint8_t(l,
        CBOR_Pulse_Raw_EverParse_Format_jump_header(l, (size_t)0U));
    CBOR_Pulse_Raw_Slice_byte_slice tl_ = scrut._2;
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    h = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut._1);
    CBOR_Spec_Raw_EverParse_initial_byte_t b = h._1;
    size_t ite;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
      ite = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h._1, h._2);
    else
      ite = (size_t)0U;
    CBOR_Pulse_Raw_Slice_byte_slice tl = Pulse_Lib_Slice_split__uint8_t(tl_, ite)._2;
    uint8_t m = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
    if (m == CBOR_MAJOR_TYPE_TAGGED)
      *pl = tl;
    else if (m == CBOR_MAJOR_TYPE_ARRAY)
    {
      *pl = tl;
      pn = CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h) + n_;
    }
    else if (m == CBOR_MAJOR_TYPE_MAP)
      if (bound == (size_t)0U)
        pres = false;
      else
      {
        *pl = tl;
        if
        (
          CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_aux(bound - (size_t)1U,
            pl,
            CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h))
        )
          pn = n_;
        else
          pres = false;
      }
    else
    {
      *pl = tl;
      pn = n_;
    }
  }
  return pres;
}

static bool
CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth(
  size_t bound,
  size_t n0,
  CBOR_Pulse_Raw_Slice_byte_slice l0
)
{
  CBOR_Pulse_Raw_Slice_byte_slice buf = l0;
  return CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_aux(bound, &buf, n0);
}

static bool
CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_opt(
  FStar_Pervasives_Native_option__size_t bound,
  size_t n0,
  CBOR_Pulse_Raw_Slice_byte_slice l0
)
{
  if (bound.tag == FStar_Pervasives_Native_None)
    return true;
  else
  {
    size_t ite;
    if (bound.tag == FStar_Pervasives_Native_Some)
      ite = bound.v;
    else
      ite = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
    return CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth(ite, n0, l0);
  }
}

static bool
CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_key_depth(
  size_t bound,
  CBOR_Pulse_Raw_Slice_byte_slice l1
)
{
  size_t pn = (size_t)1U;
  bool pres = true;
  CBOR_Pulse_Raw_Slice_byte_slice ppi = l1;
  while (true)
  {
    size_t n = pn;
    if (!(pres && n > (size_t)0U))
      break;
    size_t n0 = pn;
    CBOR_Pulse_Raw_Slice_byte_slice pi = ppi;
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    h =
      CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(pi,
          CBOR_Pulse_Raw_EverParse_Format_jump_header(pi, (size_t)0U))._1);
    bool ite0;
    if (CBOR_Spec_Raw_EverParse_get_header_major_type(h) == CBOR_MAJOR_TYPE_MAP)
    {
      CBOR_Pulse_Raw_Slice_byte_slice
      hd =
        Pulse_Lib_Slice_split__uint8_t(pi,
          CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(pi, (size_t)0U))._1;
      prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
      ph = h;
      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
      scrut =
        Pulse_Lib_Slice_split__uint8_t(hd,
          CBOR_Pulse_Raw_EverParse_Format_jump_header(hd, (size_t)0U));
      CBOR_Pulse_Raw_Slice_byte_slice outc = scrut._2;
      ph = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut._1);
      CBOR_Pulse_Raw_Slice_byte_slice pl = outc;
      size_t
      pn1 =
        (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h),
          fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h));
      bool pres1 = true;
      while (true)
      {
        bool res = pres1;
        if (!(pn1 > (size_t)0U && res))
          break;
        size_t n_ = pn1 - (size_t)1U;
        CBOR_Pulse_Raw_Slice_byte_slice l = pl;
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
        scrut =
          Pulse_Lib_Slice_split__uint8_t(l,
            CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l, (size_t)0U));
        CBOR_Pulse_Raw_Slice_byte_slice lh = scrut._1;
        CBOR_Pulse_Raw_Slice_byte_slice lt = scrut._2;
        CBOR_Pulse_Raw_Slice_byte_slice
        lt_ =
          Pulse_Lib_Slice_split__uint8_t(lt,
            CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(lt, (size_t)0U))._2;
        if (CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth(bound, (size_t)1U, lh))
        {
          pn1 = n_;
          pl = lt_;
        }
        else
          pres1 = false;
      }
      ite0 = pres1;
    }
    else
      ite0 = true;
    if (!ite0)
      pres = false;
    else
    {
      size_t off1 = CBOR_Pulse_Raw_EverParse_Format_jump_header(pi, (size_t)0U);
      prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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
      pn = n0 - (size_t)1U + CBOR_Pulse_Raw_EverParse_Format_jump_recursive_step_count_leaf(ph);
      ppi = pc;
    }
  }
  return pres;
}

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(
  FStar_Pervasives_Native_option__size_t map_bound,
  CBOR_Pulse_Raw_Slice_byte_slice l1,
  CBOR_Pulse_Raw_Slice_byte_slice l2
)
{
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h1 =
    CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(l1,
        CBOR_Pulse_Raw_EverParse_Format_jump_header(l1, (size_t)0U))._1);
  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
  h2 =
    CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(l2,
        CBOR_Pulse_Raw_EverParse_Format_jump_header(l2, (size_t)0U))._1);
  uint8_t mt1 = CBOR_Spec_Raw_EverParse_get_header_major_type(h1);
  uint8_t mt2 = CBOR_Spec_Raw_EverParse_get_header_major_type(h2);
  if (mt1 == CBOR_MAJOR_TYPE_MAP && mt2 == CBOR_MAJOR_TYPE_MAP)
    if (CBOR_Pulse_Raw_Util_eq_Some_0sz(map_bound))
      return ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_None });
    else
    {
      FStar_Pervasives_Native_option__size_t map_bound_;
      if (map_bound.tag == FStar_Pervasives_Native_None)
        map_bound_ =
          ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
      else if (map_bound.tag == FStar_Pervasives_Native_Some)
        map_bound_ =
          (
            (FStar_Pervasives_Native_option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = map_bound.v - (size_t)1U
            }
          );
      else
        map_bound_ =
          KRML_EABORT(FStar_Pervasives_Native_option__size_t,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Pulse_Raw_Slice_byte_slice
      map1 =
        Pulse_Lib_Slice_split__uint8_t(l1,
          CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l1, (size_t)0U))._1;
      prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
      ph = h1;
      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
      scrut0 =
        Pulse_Lib_Slice_split__uint8_t(map1,
          CBOR_Pulse_Raw_EverParse_Format_jump_header(map1, (size_t)0U));
      CBOR_Pulse_Raw_Slice_byte_slice outc0 = scrut0._2;
      ph = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut0._1);
      CBOR_Pulse_Raw_Slice_byte_slice c1 = outc0;
      size_t
      nv1 =
        (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1),
          fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1));
      CBOR_Pulse_Raw_Slice_byte_slice
      map2 =
        Pulse_Lib_Slice_split__uint8_t(l2,
          CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l2, (size_t)0U))._1;
      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
      scrut1 =
        Pulse_Lib_Slice_split__uint8_t(map2,
          CBOR_Pulse_Raw_EverParse_Format_jump_header(map2, (size_t)0U));
      CBOR_Pulse_Raw_Slice_byte_slice outc = scrut1._2;
      ph = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut1._1);
      CBOR_Pulse_Raw_Slice_byte_slice c2 = outc;
      size_t
      nv2 =
        (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2),
          fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2));
      CBOR_Pulse_Raw_Slice_byte_slice pl = c1;
      size_t pn = nv1;
      FStar_Pervasives_Native_option__bool
      pres = { .tag = FStar_Pervasives_Native_Some, .v = true };
      while (true)
      {
        FStar_Pervasives_Native_option__bool res0 = pres;
        if (!(pn > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(res0)))
          break;
        CBOR_Pulse_Raw_Slice_byte_slice l = pl;
        size_t n_ = pn - (size_t)1U;
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
        scrut0 =
          Pulse_Lib_Slice_split__uint8_t(l,
            CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l, (size_t)0U));
        CBOR_Pulse_Raw_Slice_byte_slice lh = scrut0._1;
        CBOR_Pulse_Raw_Slice_byte_slice lt = scrut0._2;
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
        scrut1 =
          Pulse_Lib_Slice_split__uint8_t(lt,
            CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(lt, (size_t)0U));
        CBOR_Pulse_Raw_Slice_byte_slice lv = scrut1._1;
        CBOR_Pulse_Raw_Slice_byte_slice lt_ = scrut1._2;
        CBOR_Pulse_Raw_Slice_byte_slice pll = c2;
        size_t pn1 = nv2;
        FStar_Pervasives_Native_option__bool
        pres1 = { .tag = FStar_Pervasives_Native_Some, .v = false };
        bool pcont = true;
        while (true)
        {
          FStar_Pervasives_Native_option__bool res = pres1;
          bool cont = pcont;
          if (!(pn1 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(res) && cont))
            break;
          CBOR_Pulse_Raw_Slice_byte_slice l3 = pll;
          size_t n_1 = pn1 - (size_t)1U;
          FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
          scrut0 =
            Pulse_Lib_Slice_split__uint8_t(l3,
              CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l3, (size_t)0U));
          CBOR_Pulse_Raw_Slice_byte_slice lt1 = scrut0._2;
          size_t pn2 = (size_t)1U;
          CBOR_Pulse_Raw_Slice_byte_slice pl1 = lh;
          CBOR_Pulse_Raw_Slice_byte_slice pl2 = scrut0._1;
          FStar_Pervasives_Native_option__bool
          pres2 = { .tag = FStar_Pervasives_Native_Some, .v = true };
          while (true)
          {
            size_t n20 = pn2;
            if (!(CBOR_Pulse_Raw_Util_eq_Some_true(pres2) && n20 > (size_t)0U))
              break;
            CBOR_Pulse_Raw_Slice_byte_slice l1_ = pl1;
            CBOR_Pulse_Raw_Slice_byte_slice l2_ = pl2;
            FStar_Pervasives_Native_option__bool
            r =
              CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound_,
                l1_,
                l2_);
            if (r.tag == FStar_Pervasives_Native_None)
              pres2 = r;
            else
            {
              size_t n2 = pn2;
              if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
              {
                size_t n_2 = n2 - (size_t)1U;
                CBOR_Pulse_Raw_Slice_byte_slice
                tl1 =
                  Pulse_Lib_Slice_split__uint8_t(l1_,
                    CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l1_, (size_t)0U))._2;
                CBOR_Pulse_Raw_Slice_byte_slice
                tl2 =
                  Pulse_Lib_Slice_split__uint8_t(l2_,
                    CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l2_, (size_t)0U))._2;
                pn2 = n_2;
                pl1 = tl1;
                pl2 = tl2;
              }
              else
              {
                FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                scrut0 =
                  Pulse_Lib_Slice_split__uint8_t(l1_,
                    CBOR_Pulse_Raw_EverParse_Format_jump_header(l1_, (size_t)0U));
                CBOR_Pulse_Raw_Slice_byte_slice tl1 = scrut0._2;
                prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
                h11 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut0._1);
                uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                scrut1 =
                  Pulse_Lib_Slice_split__uint8_t(l2_,
                    CBOR_Pulse_Raw_EverParse_Format_jump_header(l2_, (size_t)0U));
                CBOR_Pulse_Raw_Slice_byte_slice tl2 = scrut1._2;
                prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
                h21 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut1._1);
                if (mt11 != CBOR_Spec_Raw_EverParse_get_header_major_type(h21))
                  pres2 =
                    (
                      (FStar_Pervasives_Native_option__bool){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = false
                      }
                    );
                else
                {
                  CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h11._1;
                  size_t ite0;
                  if
                  (
                    b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                      b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                  )
                    ite0 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h11._1, h11._2);
                  else
                    ite0 = (size_t)0U;
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                  scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
                  CBOR_Pulse_Raw_Slice_byte_slice lc1 = scrut0._1;
                  CBOR_Pulse_Raw_Slice_byte_slice tl1_ = scrut0._2;
                  size_t
                  n_2 =
                    CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h11) +
                      (n2 - (size_t)1U);
                  CBOR_Spec_Raw_EverParse_initial_byte_t b = h21._1;
                  size_t ite1;
                  if
                  (
                    b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                      b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                  )
                    ite1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h21._1, h21._2);
                  else
                    ite1 = (size_t)0U;
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                  scrut1 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
                  CBOR_Pulse_Raw_Slice_byte_slice lc2 = scrut1._1;
                  CBOR_Pulse_Raw_Slice_byte_slice tl2_ = scrut1._2;
                  uint8_t mt12 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                  bool ite2;
                  if (mt12 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
                  {
                    CBOR_Spec_Raw_EverParse_long_argument
                    scrut0 =
                      fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11);
                    uint8_t sv1;
                    if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                      sv1 =
                        fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11).additional_info;
                    else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                      sv1 = scrut0.case_LongArgumentSimpleValue;
                    else
                      sv1 =
                        KRML_EABORT(uint8_t,
                          "unreachable (pattern matches are exhaustive in F*)");
                    CBOR_Spec_Raw_EverParse_long_argument
                    scrut =
                      fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21);
                    uint8_t ite;
                    if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                      ite =
                        fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21).additional_info;
                    else if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                      ite = scrut.case_LongArgumentSimpleValue;
                    else
                      ite =
                        KRML_EABORT(uint8_t,
                          "unreachable (pattern matches are exhaustive in F*)");
                    ite2 = sv1 == ite;
                  }
                  else
                  {
                    uint64_t
                    len =
                      CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11),
                        fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11));
                    if
                    (
                      len !=
                        CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21),
                          fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21))
                    )
                      ite2 = false;
                    else if
                    (mt12 == CBOR_MAJOR_TYPE_BYTE_STRING || mt12 == CBOR_MAJOR_TYPE_TEXT_STRING)
                      ite2 = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == 0;
                    else
                      ite2 = mt12 != CBOR_MAJOR_TYPE_MAP;
                  }
                  if (ite2)
                  {
                    pn2 = n_2;
                    pl1 = tl1_;
                    pl2 = tl2_;
                  }
                  else
                    pres2 =
                      (
                        (FStar_Pervasives_Native_option__bool){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = false
                        }
                      );
                }
              }
            }
          }
          FStar_Pervasives_Native_option__bool res0 = pres2;
          if (res0.tag == FStar_Pervasives_Native_None)
            pres1 = res0;
          else
          {
            FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
            scrut0 =
              Pulse_Lib_Slice_split__uint8_t(lt1,
                CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(lt1, (size_t)0U));
            CBOR_Pulse_Raw_Slice_byte_slice lv1 = scrut0._1;
            CBOR_Pulse_Raw_Slice_byte_slice lt_1 = scrut0._2;
            bool ite0;
            if (res0.tag == FStar_Pervasives_Native_Some)
              ite0 = res0.v;
            else
              ite0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
            if (ite0)
            {
              size_t pn3 = (size_t)1U;
              CBOR_Pulse_Raw_Slice_byte_slice pl11 = lv;
              CBOR_Pulse_Raw_Slice_byte_slice pl21 = lv1;
              FStar_Pervasives_Native_option__bool
              pres3 = { .tag = FStar_Pervasives_Native_Some, .v = true };
              while (true)
              {
                size_t n20 = pn3;
                if (!(CBOR_Pulse_Raw_Util_eq_Some_true(pres3) && n20 > (size_t)0U))
                  break;
                CBOR_Pulse_Raw_Slice_byte_slice l1_ = pl11;
                CBOR_Pulse_Raw_Slice_byte_slice l2_ = pl21;
                FStar_Pervasives_Native_option__bool
                r =
                  CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound_,
                    l1_,
                    l2_);
                if (r.tag == FStar_Pervasives_Native_None)
                  pres3 = r;
                else
                {
                  size_t n2 = pn3;
                  if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
                  {
                    size_t n_2 = n2 - (size_t)1U;
                    CBOR_Pulse_Raw_Slice_byte_slice
                    tl1 =
                      Pulse_Lib_Slice_split__uint8_t(l1_,
                        CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l1_, (size_t)0U))._2;
                    CBOR_Pulse_Raw_Slice_byte_slice
                    tl2 =
                      Pulse_Lib_Slice_split__uint8_t(l2_,
                        CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l2_, (size_t)0U))._2;
                    pn3 = n_2;
                    pl11 = tl1;
                    pl21 = tl2;
                  }
                  else
                  {
                    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                    scrut0 =
                      Pulse_Lib_Slice_split__uint8_t(l1_,
                        CBOR_Pulse_Raw_EverParse_Format_jump_header(l1_, (size_t)0U));
                    CBOR_Pulse_Raw_Slice_byte_slice tl1 = scrut0._2;
                    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
                    h11 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut0._1);
                    uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                    scrut1 =
                      Pulse_Lib_Slice_split__uint8_t(l2_,
                        CBOR_Pulse_Raw_EverParse_Format_jump_header(l2_, (size_t)0U));
                    CBOR_Pulse_Raw_Slice_byte_slice tl2 = scrut1._2;
                    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
                    h21 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut1._1);
                    if (mt11 != CBOR_Spec_Raw_EverParse_get_header_major_type(h21))
                      pres3 =
                        (
                          (FStar_Pervasives_Native_option__bool){
                            .tag = FStar_Pervasives_Native_Some,
                            .v = false
                          }
                        );
                    else
                    {
                      CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h11._1;
                      size_t ite0;
                      if
                      (
                        b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                          b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                      )
                        ite0 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h11._1, h11._2);
                      else
                        ite0 = (size_t)0U;
                      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                      scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
                      CBOR_Pulse_Raw_Slice_byte_slice lc1 = scrut0._1;
                      CBOR_Pulse_Raw_Slice_byte_slice tl1_ = scrut0._2;
                      size_t
                      n_2 =
                        CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h11) +
                          (n2 - (size_t)1U);
                      CBOR_Spec_Raw_EverParse_initial_byte_t b = h21._1;
                      size_t ite1;
                      if
                      (
                        b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                          b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                      )
                        ite1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h21._1, h21._2);
                      else
                        ite1 = (size_t)0U;
                      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                      scrut1 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
                      CBOR_Pulse_Raw_Slice_byte_slice lc2 = scrut1._1;
                      CBOR_Pulse_Raw_Slice_byte_slice tl2_ = scrut1._2;
                      uint8_t mt12 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                      bool ite2;
                      if (mt12 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
                      {
                        CBOR_Spec_Raw_EverParse_long_argument
                        scrut0 =
                          fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11);
                        uint8_t sv1;
                        if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                          sv1 =
                            fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11).additional_info;
                        else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                          sv1 = scrut0.case_LongArgumentSimpleValue;
                        else
                          sv1 =
                            KRML_EABORT(uint8_t,
                              "unreachable (pattern matches are exhaustive in F*)");
                        CBOR_Spec_Raw_EverParse_long_argument
                        scrut =
                          fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21);
                        uint8_t ite;
                        if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                          ite =
                            fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21).additional_info;
                        else if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                          ite = scrut.case_LongArgumentSimpleValue;
                        else
                          ite =
                            KRML_EABORT(uint8_t,
                              "unreachable (pattern matches are exhaustive in F*)");
                        ite2 = sv1 == ite;
                      }
                      else
                      {
                        uint64_t
                        len =
                          CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11),
                            fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11));
                        if
                        (
                          len !=
                            CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21),
                              fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21))
                        )
                          ite2 = false;
                        else if
                        (mt12 == CBOR_MAJOR_TYPE_BYTE_STRING || mt12 == CBOR_MAJOR_TYPE_TEXT_STRING)
                          ite2 = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == 0;
                        else
                          ite2 = mt12 != CBOR_MAJOR_TYPE_MAP;
                      }
                      if (ite2)
                      {
                        pn3 = n_2;
                        pl11 = tl1_;
                        pl21 = tl2_;
                      }
                      else
                        pres3 =
                          (
                            (FStar_Pervasives_Native_option__bool){
                              .tag = FStar_Pervasives_Native_Some,
                              .v = false
                            }
                          );
                    }
                  }
                }
              }
              pres1 = pres3;
              pcont = false;
            }
            else
            {
              pll = lt_1;
              pn1 = n_1;
            }
          }
        }
        FStar_Pervasives_Native_option__bool res = pres1;
        if (CBOR_Pulse_Raw_Util_eq_Some_true(res))
        {
          pl = lt_;
          pn = n_;
        }
        else
          pres = res;
      }
      FStar_Pervasives_Native_option__bool res = pres;
      if (CBOR_Pulse_Raw_Util_eq_Some_true(res))
      {
        CBOR_Pulse_Raw_Slice_byte_slice pl1 = c2;
        size_t pn1 = nv2;
        FStar_Pervasives_Native_option__bool
        pres1 = { .tag = FStar_Pervasives_Native_Some, .v = true };
        while (true)
        {
          FStar_Pervasives_Native_option__bool res10 = pres1;
          if (!(pn1 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(res10)))
            break;
          CBOR_Pulse_Raw_Slice_byte_slice l = pl1;
          size_t n_ = pn1 - (size_t)1U;
          FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
          scrut0 =
            Pulse_Lib_Slice_split__uint8_t(l,
              CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l, (size_t)0U));
          CBOR_Pulse_Raw_Slice_byte_slice lh = scrut0._1;
          CBOR_Pulse_Raw_Slice_byte_slice lt = scrut0._2;
          FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
          scrut1 =
            Pulse_Lib_Slice_split__uint8_t(lt,
              CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(lt, (size_t)0U));
          CBOR_Pulse_Raw_Slice_byte_slice lv = scrut1._1;
          CBOR_Pulse_Raw_Slice_byte_slice lt_ = scrut1._2;
          CBOR_Pulse_Raw_Slice_byte_slice pll = c1;
          size_t pn2 = nv1;
          FStar_Pervasives_Native_option__bool
          pres2 = { .tag = FStar_Pervasives_Native_Some, .v = false };
          bool pcont = true;
          while (true)
          {
            FStar_Pervasives_Native_option__bool res1 = pres2;
            bool cont = pcont;
            if (!(pn2 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(res1) && cont))
              break;
            CBOR_Pulse_Raw_Slice_byte_slice l3 = pll;
            size_t n_1 = pn2 - (size_t)1U;
            FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
            scrut0 =
              Pulse_Lib_Slice_split__uint8_t(l3,
                CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l3, (size_t)0U));
            CBOR_Pulse_Raw_Slice_byte_slice lt1 = scrut0._2;
            size_t pn3 = (size_t)1U;
            CBOR_Pulse_Raw_Slice_byte_slice pl11 = lh;
            CBOR_Pulse_Raw_Slice_byte_slice pl2 = scrut0._1;
            FStar_Pervasives_Native_option__bool
            pres3 = { .tag = FStar_Pervasives_Native_Some, .v = true };
            while (true)
            {
              size_t n20 = pn3;
              if (!(CBOR_Pulse_Raw_Util_eq_Some_true(pres3) && n20 > (size_t)0U))
                break;
              CBOR_Pulse_Raw_Slice_byte_slice l1_ = pl11;
              CBOR_Pulse_Raw_Slice_byte_slice l2_ = pl2;
              FStar_Pervasives_Native_option__bool
              r =
                CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound_,
                  l1_,
                  l2_);
              if (r.tag == FStar_Pervasives_Native_None)
                pres3 = r;
              else
              {
                size_t n2 = pn3;
                if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
                {
                  size_t n_2 = n2 - (size_t)1U;
                  CBOR_Pulse_Raw_Slice_byte_slice
                  tl1 =
                    Pulse_Lib_Slice_split__uint8_t(l1_,
                      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l1_, (size_t)0U))._2;
                  CBOR_Pulse_Raw_Slice_byte_slice
                  tl2 =
                    Pulse_Lib_Slice_split__uint8_t(l2_,
                      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l2_, (size_t)0U))._2;
                  pn3 = n_2;
                  pl11 = tl1;
                  pl2 = tl2;
                }
                else
                {
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                  scrut0 =
                    Pulse_Lib_Slice_split__uint8_t(l1_,
                      CBOR_Pulse_Raw_EverParse_Format_jump_header(l1_, (size_t)0U));
                  CBOR_Pulse_Raw_Slice_byte_slice tl1 = scrut0._2;
                  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
                  h11 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut0._1);
                  uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                  FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                  scrut1 =
                    Pulse_Lib_Slice_split__uint8_t(l2_,
                      CBOR_Pulse_Raw_EverParse_Format_jump_header(l2_, (size_t)0U));
                  CBOR_Pulse_Raw_Slice_byte_slice tl2 = scrut1._2;
                  prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
                  h21 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut1._1);
                  if (mt11 != CBOR_Spec_Raw_EverParse_get_header_major_type(h21))
                    pres3 =
                      (
                        (FStar_Pervasives_Native_option__bool){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = false
                        }
                      );
                  else
                  {
                    CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h11._1;
                    size_t ite0;
                    if
                    (
                      b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                        b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                    )
                      ite0 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h11._1, h11._2);
                    else
                      ite0 = (size_t)0U;
                    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                    scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
                    CBOR_Pulse_Raw_Slice_byte_slice lc1 = scrut0._1;
                    CBOR_Pulse_Raw_Slice_byte_slice tl1_ = scrut0._2;
                    size_t
                    n_2 =
                      CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h11) +
                        (n2 - (size_t)1U);
                    CBOR_Spec_Raw_EverParse_initial_byte_t b = h21._1;
                    size_t ite1;
                    if
                    (
                      b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                        b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                    )
                      ite1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h21._1, h21._2);
                    else
                      ite1 = (size_t)0U;
                    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                    scrut1 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
                    CBOR_Pulse_Raw_Slice_byte_slice lc2 = scrut1._1;
                    CBOR_Pulse_Raw_Slice_byte_slice tl2_ = scrut1._2;
                    uint8_t mt12 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                    bool ite2;
                    if (mt12 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
                    {
                      CBOR_Spec_Raw_EverParse_long_argument
                      scrut0 =
                        fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11);
                      uint8_t sv1;
                      if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                        sv1 =
                          fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11).additional_info;
                      else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                        sv1 = scrut0.case_LongArgumentSimpleValue;
                      else
                        sv1 =
                          KRML_EABORT(uint8_t,
                            "unreachable (pattern matches are exhaustive in F*)");
                      CBOR_Spec_Raw_EverParse_long_argument
                      scrut =
                        fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21);
                      uint8_t ite;
                      if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                        ite =
                          fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21).additional_info;
                      else if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                        ite = scrut.case_LongArgumentSimpleValue;
                      else
                        ite =
                          KRML_EABORT(uint8_t,
                            "unreachable (pattern matches are exhaustive in F*)");
                      ite2 = sv1 == ite;
                    }
                    else
                    {
                      uint64_t
                      len =
                        CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11),
                          fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11));
                      if
                      (
                        len !=
                          CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21),
                            fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21))
                      )
                        ite2 = false;
                      else if
                      (mt12 == CBOR_MAJOR_TYPE_BYTE_STRING || mt12 == CBOR_MAJOR_TYPE_TEXT_STRING)
                        ite2 = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == 0;
                      else
                        ite2 = mt12 != CBOR_MAJOR_TYPE_MAP;
                    }
                    if (ite2)
                    {
                      pn3 = n_2;
                      pl11 = tl1_;
                      pl2 = tl2_;
                    }
                    else
                      pres3 =
                        (
                          (FStar_Pervasives_Native_option__bool){
                            .tag = FStar_Pervasives_Native_Some,
                            .v = false
                          }
                        );
                  }
                }
              }
            }
            FStar_Pervasives_Native_option__bool res10 = pres3;
            if (res10.tag == FStar_Pervasives_Native_None)
              pres2 = res10;
            else
            {
              FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
              scrut0 =
                Pulse_Lib_Slice_split__uint8_t(lt1,
                  CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(lt1, (size_t)0U));
              CBOR_Pulse_Raw_Slice_byte_slice lv1 = scrut0._1;
              CBOR_Pulse_Raw_Slice_byte_slice lt_1 = scrut0._2;
              bool ite0;
              if (res10.tag == FStar_Pervasives_Native_Some)
                ite0 = res10.v;
              else
                ite0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
              if (ite0)
              {
                size_t pn4 = (size_t)1U;
                CBOR_Pulse_Raw_Slice_byte_slice pl12 = lv;
                CBOR_Pulse_Raw_Slice_byte_slice pl21 = lv1;
                FStar_Pervasives_Native_option__bool
                pres4 = { .tag = FStar_Pervasives_Native_Some, .v = true };
                while (true)
                {
                  size_t n20 = pn4;
                  if (!(CBOR_Pulse_Raw_Util_eq_Some_true(pres4) && n20 > (size_t)0U))
                    break;
                  CBOR_Pulse_Raw_Slice_byte_slice l1_ = pl12;
                  CBOR_Pulse_Raw_Slice_byte_slice l2_ = pl21;
                  FStar_Pervasives_Native_option__bool
                  r =
                    CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound_,
                      l1_,
                      l2_);
                  if (r.tag == FStar_Pervasives_Native_None)
                    pres4 = r;
                  else
                  {
                    size_t n2 = pn4;
                    if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
                    {
                      size_t n_2 = n2 - (size_t)1U;
                      CBOR_Pulse_Raw_Slice_byte_slice
                      tl1 =
                        Pulse_Lib_Slice_split__uint8_t(l1_,
                          CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l1_, (size_t)0U))._2;
                      CBOR_Pulse_Raw_Slice_byte_slice
                      tl2 =
                        Pulse_Lib_Slice_split__uint8_t(l2_,
                          CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l2_, (size_t)0U))._2;
                      pn4 = n_2;
                      pl12 = tl1;
                      pl21 = tl2;
                    }
                    else
                    {
                      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                      scrut0 =
                        Pulse_Lib_Slice_split__uint8_t(l1_,
                          CBOR_Pulse_Raw_EverParse_Format_jump_header(l1_, (size_t)0U));
                      CBOR_Pulse_Raw_Slice_byte_slice tl1 = scrut0._2;
                      prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
                      h11 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut0._1);
                      uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                      scrut1 =
                        Pulse_Lib_Slice_split__uint8_t(l2_,
                          CBOR_Pulse_Raw_EverParse_Format_jump_header(l2_, (size_t)0U));
                      CBOR_Pulse_Raw_Slice_byte_slice tl2 = scrut1._2;
                      prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
                      h21 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut1._1);
                      if (mt11 != CBOR_Spec_Raw_EverParse_get_header_major_type(h21))
                        pres4 =
                          (
                            (FStar_Pervasives_Native_option__bool){
                              .tag = FStar_Pervasives_Native_Some,
                              .v = false
                            }
                          );
                      else
                      {
                        CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h11._1;
                        size_t ite0;
                        if
                        (
                          b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                            b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                        )
                          ite0 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h11._1, h11._2);
                        else
                          ite0 = (size_t)0U;
                        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                        scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
                        CBOR_Pulse_Raw_Slice_byte_slice lc1 = scrut0._1;
                        CBOR_Pulse_Raw_Slice_byte_slice tl1_ = scrut0._2;
                        size_t
                        n_2 =
                          CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h11) +
                            (n2 - (size_t)1U);
                        CBOR_Spec_Raw_EverParse_initial_byte_t b = h21._1;
                        size_t ite1;
                        if
                        (
                          b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                            b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                        )
                          ite1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h21._1, h21._2);
                        else
                          ite1 = (size_t)0U;
                        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
                        scrut1 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
                        CBOR_Pulse_Raw_Slice_byte_slice lc2 = scrut1._1;
                        CBOR_Pulse_Raw_Slice_byte_slice tl2_ = scrut1._2;
                        uint8_t mt12 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                        bool ite2;
                        if (mt12 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
                        {
                          CBOR_Spec_Raw_EverParse_long_argument
                          scrut0 =
                            fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11);
                          uint8_t sv1;
                          if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                            sv1 =
                              fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11).additional_info;
                          else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                            sv1 = scrut0.case_LongArgumentSimpleValue;
                          else
                            sv1 =
                              KRML_EABORT(uint8_t,
                                "unreachable (pattern matches are exhaustive in F*)");
                          CBOR_Spec_Raw_EverParse_long_argument
                          scrut =
                            fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21);
                          uint8_t ite;
                          if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                            ite =
                              fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21).additional_info;
                          else if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                            ite = scrut.case_LongArgumentSimpleValue;
                          else
                            ite =
                              KRML_EABORT(uint8_t,
                                "unreachable (pattern matches are exhaustive in F*)");
                          ite2 = sv1 == ite;
                        }
                        else
                        {
                          uint64_t
                          len =
                            CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11),
                              fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11));
                          if
                          (
                            len !=
                              CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21),
                                fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21))
                          )
                            ite2 = false;
                          else if
                          (
                            mt12 == CBOR_MAJOR_TYPE_BYTE_STRING ||
                              mt12 == CBOR_MAJOR_TYPE_TEXT_STRING
                          )
                            ite2 = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == 0;
                          else
                            ite2 = mt12 != CBOR_MAJOR_TYPE_MAP;
                        }
                        if (ite2)
                        {
                          pn4 = n_2;
                          pl12 = tl1_;
                          pl21 = tl2_;
                        }
                        else
                          pres4 =
                            (
                              (FStar_Pervasives_Native_option__bool){
                                .tag = FStar_Pervasives_Native_Some,
                                .v = false
                              }
                            );
                      }
                    }
                  }
                }
                pres2 = pres4;
                pcont = false;
              }
              else
              {
                pll = lt_1;
                pn2 = n_1;
              }
            }
          }
          FStar_Pervasives_Native_option__bool res1 = pres2;
          if (CBOR_Pulse_Raw_Util_eq_Some_true(res1))
          {
            pl1 = lt_;
            pn1 = n_;
          }
          else
            pres1 = res1;
        }
        return pres1;
      }
      else
        return res;
    }
  else
    return
      ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = false });
}

static FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_list_basic(
  FStar_Pervasives_Native_option__size_t map_bound,
  size_t n1,
  CBOR_Pulse_Raw_Slice_byte_slice l1,
  size_t n2,
  CBOR_Pulse_Raw_Slice_byte_slice l2
)
{
  if (n1 != n2)
    return
      ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = false });
  else
  {
    size_t pn = n1;
    CBOR_Pulse_Raw_Slice_byte_slice pl1 = l1;
    CBOR_Pulse_Raw_Slice_byte_slice pl2 = l2;
    FStar_Pervasives_Native_option__bool pres = { .tag = FStar_Pervasives_Native_Some, .v = true };
    while (true)
    {
      size_t n0 = pn;
      if (!(CBOR_Pulse_Raw_Util_eq_Some_true(pres) && n0 > (size_t)0U))
        break;
      CBOR_Pulse_Raw_Slice_byte_slice l1_ = pl1;
      CBOR_Pulse_Raw_Slice_byte_slice l2_ = pl2;
      FStar_Pervasives_Native_option__bool
      r = CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound, l1_, l2_);
      if (r.tag == FStar_Pervasives_Native_None)
        pres = r;
      else
      {
        size_t n = pn;
        if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
        {
          size_t n_ = n - (size_t)1U;
          CBOR_Pulse_Raw_Slice_byte_slice
          tl1 =
            Pulse_Lib_Slice_split__uint8_t(l1_,
              CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l1_, (size_t)0U))._2;
          CBOR_Pulse_Raw_Slice_byte_slice
          tl2 =
            Pulse_Lib_Slice_split__uint8_t(l2_,
              CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l2_, (size_t)0U))._2;
          pn = n_;
          pl1 = tl1;
          pl2 = tl2;
        }
        else
        {
          FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
          scrut0 =
            Pulse_Lib_Slice_split__uint8_t(l1_,
              CBOR_Pulse_Raw_EverParse_Format_jump_header(l1_, (size_t)0U));
          CBOR_Pulse_Raw_Slice_byte_slice tl1 = scrut0._2;
          prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
          h1 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut0._1);
          uint8_t mt1 = CBOR_Spec_Raw_EverParse_get_header_major_type(h1);
          FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
          scrut1 =
            Pulse_Lib_Slice_split__uint8_t(l2_,
              CBOR_Pulse_Raw_EverParse_Format_jump_header(l2_, (size_t)0U));
          CBOR_Pulse_Raw_Slice_byte_slice tl2 = scrut1._2;
          prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
          h2 = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut1._1);
          if (mt1 != CBOR_Spec_Raw_EverParse_get_header_major_type(h2))
            pres =
              (
                (FStar_Pervasives_Native_option__bool){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = false
                }
              );
          else
          {
            CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h1._1;
            size_t ite0;
            if
            (
              b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
            )
              ite0 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h1._1, h1._2);
            else
              ite0 = (size_t)0U;
            FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
            scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
            CBOR_Pulse_Raw_Slice_byte_slice lc1 = scrut0._1;
            CBOR_Pulse_Raw_Slice_byte_slice tl1_ = scrut0._2;
            size_t
            n_ =
              CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h1) +
                (n - (size_t)1U);
            CBOR_Spec_Raw_EverParse_initial_byte_t b = h2._1;
            size_t ite1;
            if
            (
              b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
            )
              ite1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h2._1, h2._2);
            else
              ite1 = (size_t)0U;
            FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
            scrut1 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
            CBOR_Pulse_Raw_Slice_byte_slice lc2 = scrut1._1;
            CBOR_Pulse_Raw_Slice_byte_slice tl2_ = scrut1._2;
            uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h1);
            bool ite2;
            if (mt11 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
            {
              CBOR_Spec_Raw_EverParse_long_argument
              scrut0 =
                fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1);
              uint8_t sv1;
              if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                sv1 =
                  fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1).additional_info;
              else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                sv1 = scrut0.case_LongArgumentSimpleValue;
              else
                sv1 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
              CBOR_Spec_Raw_EverParse_long_argument
              scrut =
                fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2);
              uint8_t ite;
              if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                ite =
                  fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2).additional_info;
              else if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                ite = scrut.case_LongArgumentSimpleValue;
              else
                ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
              ite2 = sv1 == ite;
            }
            else
            {
              uint64_t
              len =
                CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1),
                  fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1));
              if
              (
                len !=
                  CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2),
                    fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2))
              )
                ite2 = false;
              else if (mt11 == CBOR_MAJOR_TYPE_BYTE_STRING || mt11 == CBOR_MAJOR_TYPE_TEXT_STRING)
                ite2 = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == 0;
              else
                ite2 = mt11 != CBOR_MAJOR_TYPE_MAP;
            }
            if (ite2)
            {
              pn = n_;
              pl1 = tl1_;
              pl2 = tl2_;
            }
            else
              pres =
                (
                  (FStar_Pervasives_Native_option__bool){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = false
                  }
                );
          }
        }
      }
    }
    return pres;
  }
}

static FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_basic(
  FStar_Pervasives_Native_option__size_t map_bound,
  CBOR_Pulse_Raw_Slice_byte_slice l1,
  CBOR_Pulse_Raw_Slice_byte_slice l2
)
{
  if ((size_t)1U == (size_t)0U)
    return
      ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = true });
  else
    return
      CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_list_basic(map_bound,
        (size_t)1U,
        l1,
        (size_t)1U,
        l2);
}

static bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_valid_basic(
  FStar_Pervasives_Native_option__size_t map_bound,
  bool strict_bound_check,
  CBOR_Pulse_Raw_Slice_byte_slice l1
)
{
  size_t pn = (size_t)1U;
  bool pres = true;
  CBOR_Pulse_Raw_Slice_byte_slice ppi = l1;
  while (true)
  {
    size_t n = pn;
    if (!(pres && n > (size_t)0U))
      break;
    size_t n0 = pn;
    CBOR_Pulse_Raw_Slice_byte_slice pi = ppi;
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    h =
      CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(pi,
          CBOR_Pulse_Raw_EverParse_Format_jump_header(pi, (size_t)0U))._1);
    bool ite0;
    if (CBOR_Spec_Raw_EverParse_get_header_major_type(h) == CBOR_MAJOR_TYPE_MAP)
    {
      CBOR_Pulse_Raw_Slice_byte_slice
      hd =
        Pulse_Lib_Slice_split__uint8_t(pi,
          CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(pi, (size_t)0U))._1;
      prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
      ph = h;
      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
      scrut =
        Pulse_Lib_Slice_split__uint8_t(hd,
          CBOR_Pulse_Raw_EverParse_Format_jump_header(hd, (size_t)0U));
      CBOR_Pulse_Raw_Slice_byte_slice outc = scrut._2;
      ph = CBOR_Pulse_Raw_EverParse_Format_read_header(scrut._1);
      CBOR_Pulse_Raw_Slice_byte_slice pl = outc;
      size_t
      pn1 =
        (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(fstar_pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h),
          fstar_pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h));
      FStar_Pervasives_Native_option__bool
      pres1 = { .tag = FStar_Pervasives_Native_Some, .v = true };
      while (true)
      {
        FStar_Pervasives_Native_option__bool res0 = pres1;
        if (!(pn1 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(res0)))
          break;
        size_t n_ = pn1 - (size_t)1U;
        CBOR_Pulse_Raw_Slice_byte_slice l = pl;
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
        scrut =
          Pulse_Lib_Slice_split__uint8_t(l,
            CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l, (size_t)0U));
        CBOR_Pulse_Raw_Slice_byte_slice lh = scrut._1;
        CBOR_Pulse_Raw_Slice_byte_slice lt = scrut._2;
        CBOR_Pulse_Raw_Slice_byte_slice
        lt_ =
          Pulse_Lib_Slice_split__uint8_t(lt,
            CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(lt, (size_t)0U))._2;
        CBOR_Pulse_Raw_Slice_byte_slice pl1 = lt_;
        size_t pn2 = n_;
        FStar_Pervasives_Native_option__bool
        pres2 = { .tag = FStar_Pervasives_Native_Some, .v = false };
        while (true)
        {
          FStar_Pervasives_Native_option__bool res0 = pres2;
          if (!(pn2 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(res0)))
            break;
          size_t n_1 = pn2 - (size_t)1U;
          CBOR_Pulse_Raw_Slice_byte_slice l2 = pl1;
          FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
          scrut =
            Pulse_Lib_Slice_split__uint8_t(l2,
              CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l2, (size_t)0U));
          CBOR_Pulse_Raw_Slice_byte_slice lt1 = scrut._2;
          FStar_Pervasives_Native_option__bool
          res =
            CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_basic(map_bound,
              lh,
              scrut._1);
          if (CBOR_Pulse_Raw_Util_eq_Some_false(res))
          {
            pl1 =
              Pulse_Lib_Slice_split__uint8_t(lt1,
                CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(lt1, (size_t)0U))._2;
            pn2 = n_1;
          }
          else
            pres2 = res;
        }
        FStar_Pervasives_Native_option__bool res = pres2;
        if (res.tag == FStar_Pervasives_Native_None)
          pres1 = ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_None });
        else
        {
          bool ite;
          if (res.tag == FStar_Pervasives_Native_Some)
            ite = res.v;
          else
            ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          if (ite)
            pres1 =
              (
                (FStar_Pervasives_Native_option__bool){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = false
                }
              );
          else if
          (
            CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_opt(strict_bound_check ? map_bound
                                                                                            : (
                                                                                              (FStar_Pervasives_Native_option__size_t){
                                                                                                .tag = FStar_Pervasives_Native_None
                                                                                              }
                                                                                            ),
              (size_t)1U,
              lh)
          )
          {
            pn1 = n_;
            pl = lt_;
          }
          else
            pres1 = ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_None });
        }
      }
      ite0 = CBOR_Pulse_Raw_Util_eq_Some_true(pres1);
    }
    else
      ite0 = true;
    if (!ite0)
      pres = false;
    else
    {
      size_t off1 = CBOR_Pulse_Raw_EverParse_Format_jump_header(pi, (size_t)0U);
      prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
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
      pn = n0 - (size_t)1U + CBOR_Pulse_Raw_EverParse_Format_jump_recursive_step_count_leaf(ph);
      ppi = pc;
    }
  }
  return pres;
}

static FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_basic(
  size_t nl1,
  CBOR_Pulse_Raw_Slice_byte_slice l1,
  size_t nl2,
  CBOR_Pulse_Raw_Slice_byte_slice l2
)
{
  CBOR_Pulse_Raw_Slice_byte_slice pl = l2;
  size_t pn = nl2;
  FStar_Pervasives_Native_option__bool pres = { .tag = FStar_Pervasives_Native_Some, .v = true };
  while (true)
  {
    FStar_Pervasives_Native_option__bool res0 = pres;
    if (!(pn > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(res0)))
      break;
    CBOR_Pulse_Raw_Slice_byte_slice l = pl;
    size_t n_ = pn - (size_t)1U;
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
    scrut0 =
      Pulse_Lib_Slice_split__uint8_t(l,
        CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l, (size_t)0U));
    CBOR_Pulse_Raw_Slice_byte_slice lh = scrut0._1;
    CBOR_Pulse_Raw_Slice_byte_slice lt = scrut0._2;
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
    scrut1 =
      Pulse_Lib_Slice_split__uint8_t(lt,
        CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(lt, (size_t)0U));
    CBOR_Pulse_Raw_Slice_byte_slice lv = scrut1._1;
    CBOR_Pulse_Raw_Slice_byte_slice lt_ = scrut1._2;
    CBOR_Pulse_Raw_Slice_byte_slice pll = l1;
    size_t pn1 = nl1;
    FStar_Pervasives_Native_option__bool
    pres1 = { .tag = FStar_Pervasives_Native_Some, .v = false };
    bool pcont = true;
    while (true)
    {
      FStar_Pervasives_Native_option__bool res0 = pres1;
      bool cont = pcont;
      if (!(pn1 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(res0) && cont))
        break;
      CBOR_Pulse_Raw_Slice_byte_slice l3 = pll;
      size_t n_1 = pn1 - (size_t)1U;
      FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
      scrut0 =
        Pulse_Lib_Slice_split__uint8_t(l3,
          CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(l3, (size_t)0U));
      CBOR_Pulse_Raw_Slice_byte_slice lt1 = scrut0._2;
      FStar_Pervasives_Native_option__bool
      res =
        CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_basic((
            (FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None }
          ),
          lh,
          scrut0._1);
      if (res.tag == FStar_Pervasives_Native_None)
        pres1 = res;
      else
      {
        FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Slice_byte_slice_CBOR_Pulse_Raw_Slice_byte_slice
        scrut =
          Pulse_Lib_Slice_split__uint8_t(lt1,
            CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(lt1, (size_t)0U));
        CBOR_Pulse_Raw_Slice_byte_slice lv1 = scrut._1;
        CBOR_Pulse_Raw_Slice_byte_slice lt_1 = scrut._2;
        bool ite;
        if (res.tag == FStar_Pervasives_Native_Some)
          ite = res.v;
        else
          ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
        if (ite)
        {
          pres1 =
            CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_basic((
                (FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None }
              ),
              lv,
              lv1);
          pcont = false;
        }
        else
        {
          pll = lt_1;
          pn1 = n_1;
        }
      }
    }
    FStar_Pervasives_Native_option__bool res = pres1;
    if (CBOR_Pulse_Raw_Util_eq_Some_true(res))
    {
      pl = lt_;
      pn = n_;
    }
    else
      pres = res;
  }
  return pres;
}

static bool
CBOR_Pulse_Raw_Format_Nondet_Compare_cbor_match_equal_serialized_tagged(
  cbor_serialized c1,
  cbor_serialized c2
)
{
  if (c1.cbor_serialized_header.value != c2.cbor_serialized_header.value)
    return false;
  else
    return
      CBOR_Pulse_Raw_Util_eq_Some_true(CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_basic((
            (FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None }
          ),
          c1.cbor_serialized_payload,
          c2.cbor_serialized_payload));
}

static bool
CBOR_Pulse_Raw_Format_Nondet_Compare_cbor_match_compare_serialized_array(
  cbor_serialized c1,
  cbor_serialized c2
)
{
  return
    CBOR_Pulse_Raw_Util_eq_Some_true(CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_list_basic((
          (FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None }
        ),
        (size_t)c1.cbor_serialized_header.value,
        c1.cbor_serialized_payload,
        (size_t)c2.cbor_serialized_header.value,
        c2.cbor_serialized_payload));
}

static bool
CBOR_Pulse_Raw_Format_Nondet_Compare_cbor_match_compare_serialized_map(
  cbor_serialized c1,
  cbor_serialized c2
)
{
  size_t n1 = (size_t)c1.cbor_serialized_header.value;
  size_t n2 = (size_t)c2.cbor_serialized_header.value;
  if
  (
    CBOR_Pulse_Raw_Util_eq_Some_true(CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_basic(n2,
        c2.cbor_serialized_payload,
        n1,
        c1.cbor_serialized_payload))
  )
    return
      CBOR_Pulse_Raw_Util_eq_Some_true(CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_basic(n1,
          c1.cbor_serialized_payload,
          n2,
          c2.cbor_serialized_payload));
  else
    return false;
}

static uint8_t CBOR_Pulse_Raw_Nondet_Compare_impl_major_type_with_depth(cbor_raw x)
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

static CBOR_Spec_Raw_Base_raw_uint64
CBOR_Pulse_Raw_Nondet_Compare_cbor_match_tagged_get_tag_with_depth(cbor_raw c)
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
CBOR_Pulse_Raw_Nondet_Compare_cbor_match_array_get_length_with_depth(cbor_raw c)
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

typedef struct
FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw_s
{
  cbor_raw _1;
  cbor_raw _2;
}
FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw;

bool CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv_with_depth(cbor_raw x1, cbor_raw x2)
{
  uint8_t mt1 = CBOR_Pulse_Raw_Nondet_Compare_impl_major_type_with_depth(x1);
  if (mt1 != CBOR_Pulse_Raw_Nondet_Compare_impl_major_type_with_depth(x2))
    return false;
  else if (mt1 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
  {
    uint8_t w1;
    if (x1.tag == CBOR_Case_Simple)
      w1 = x1.case_CBOR_Case_Simple;
    else
      w1 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    uint8_t ite;
    if (x2.tag == CBOR_Case_Simple)
      ite = x2.case_CBOR_Case_Simple;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return w1 == ite;
  }
  else if (mt1 == CBOR_MAJOR_TYPE_UINT64 || mt1 == CBOR_MAJOR_TYPE_NEG_INT64)
  {
    CBOR_Spec_Raw_Base_raw_uint64 w1;
    if (x1.tag == CBOR_Case_Int)
    {
      cbor_int c_ = x1.case_CBOR_Case_Int;
      w1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
    }
    else
      w1 =
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
    return w1.value == ite.value;
  }
  else if (mt1 == CBOR_MAJOR_TYPE_BYTE_STRING || mt1 == CBOR_MAJOR_TYPE_TEXT_STRING)
  {
    CBOR_Spec_Raw_Base_raw_uint64 len1;
    if (x1.tag == CBOR_Case_String)
    {
      cbor_string c_ = x1.case_CBOR_Case_String;
      len1 =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_string_size,
            .value = (uint64_t)Pulse_Lib_Slice_len__uint8_t(c_.cbor_string_ptr)
          }
        );
    }
    else
      len1 =
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
    if (len1.value != ite0.value)
      return false;
    else
    {
      CBOR_Pulse_Raw_Slice_byte_slice w1;
      if (x1.tag == CBOR_Case_String)
        w1 = x1.case_CBOR_Case_String.cbor_string_ptr;
      else
        w1 =
          KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Pulse_Raw_Slice_byte_slice ite;
      if (x2.tag == CBOR_Case_String)
        ite = x2.case_CBOR_Case_String.cbor_string_ptr;
      else
        ite =
          KRML_EABORT(CBOR_Pulse_Raw_Slice_byte_slice,
            "unreachable (pattern matches are exhaustive in F*)");
      return CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(w1, ite) == 0;
    }
  }
  else if (mt1 == CBOR_MAJOR_TYPE_TAGGED)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw
    scrut = { ._1 = x1, ._2 = x2 };
    if (scrut._1.tag == CBOR_Case_Serialized_Tagged && scrut._2.tag == CBOR_Case_Serialized_Tagged)
      if (x1.tag == CBOR_Case_Serialized_Tagged)
      {
        cbor_serialized cs1 = x1.case_CBOR_Case_Serialized_Tagged;
        if (x2.tag == CBOR_Case_Serialized_Tagged)
          return
            CBOR_Pulse_Raw_Format_Nondet_Compare_cbor_match_equal_serialized_tagged(cs1,
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
      CBOR_Spec_Raw_Base_raw_uint64
      tag1 = CBOR_Pulse_Raw_Nondet_Compare_cbor_match_tagged_get_tag_with_depth(x1);
      if
      (tag1.value != CBOR_Pulse_Raw_Nondet_Compare_cbor_match_tagged_get_tag_with_depth(x2).value)
        return false;
      else
      {
        cbor_raw w1 = CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload_with_depth(x1);
        return
          CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv_with_depth(w1,
            CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload_with_depth(x2));
      }
    }
  }
  else if (mt1 == CBOR_MAJOR_TYPE_ARRAY)
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw
    scrut = { ._1 = x1, ._2 = x2 };
    if (scrut._1.tag == CBOR_Case_Serialized_Array && scrut._2.tag == CBOR_Case_Serialized_Array)
      if (x1.tag == CBOR_Case_Serialized_Array)
      {
        cbor_serialized cs1 = x1.case_CBOR_Case_Serialized_Array;
        if (x2.tag == CBOR_Case_Serialized_Array)
          return
            CBOR_Pulse_Raw_Format_Nondet_Compare_cbor_match_compare_serialized_array(cs1,
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
    else
    {
      CBOR_Spec_Raw_Base_raw_uint64
      len1 = CBOR_Pulse_Raw_Nondet_Compare_cbor_match_array_get_length_with_depth(x1);
      if
      (len1.value != CBOR_Pulse_Raw_Nondet_Compare_cbor_match_array_get_length_with_depth(x2).value)
        return false;
      else
      {
        cbor_nondet_array_iterator_t
        pi1 = CBOR_Pulse_Raw_Read_cbor_array_iterator_init_with_depth(x1);
        cbor_nondet_array_iterator_t
        pi2 = CBOR_Pulse_Raw_Read_cbor_array_iterator_init_with_depth(x2);
        bool pres = true;
        while (true)
        {
          bool res = pres;
          bool __anf0 = CBOR_Pulse_Raw_Read_cbor_array_iterator_is_empty_with_depth(pi1);
          if (!(res && !__anf0))
            break;
          cbor_raw y1 = CBOR_Pulse_Raw_Read_cbor_array_iterator_next_with_depth(&pi1);
          pres =
            CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv_with_depth(y1,
              CBOR_Pulse_Raw_Read_cbor_array_iterator_next_with_depth(&pi2));
        }
        return pres;
      }
    }
  }
  else
  {
    FStar_Pervasives_Native_tuple2__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_raw
    scrut = { ._1 = x1, ._2 = x2 };
    if (scrut._1.tag == CBOR_Case_Serialized_Map && scrut._2.tag == CBOR_Case_Serialized_Map)
      if (x1.tag == CBOR_Case_Serialized_Map)
      {
        cbor_serialized cs1 = x1.case_CBOR_Case_Serialized_Map;
        if (x2.tag == CBOR_Case_Serialized_Map)
          return
            CBOR_Pulse_Raw_Format_Nondet_Compare_cbor_match_compare_serialized_map(cs1,
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
    else
    {
      cbor_nondet_map_iterator_t i1 = CBOR_Pulse_Raw_Read_cbor_map_iterator_init_with_depth(x1);
      cbor_nondet_map_iterator_t i2 = CBOR_Pulse_Raw_Read_cbor_map_iterator_init_with_depth(x2);
      cbor_nondet_map_iterator_t pi2 = i1;
      bool pres = true;
      while (true)
      {
        bool res0 = pres;
        bool __anf00 = CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty_with_depth(pi2);
        if (!(res0 && !__anf00))
          break;
        cbor_map_entry x21 = CBOR_Pulse_Raw_Read_cbor_map_iterator_next_with_depth(&pi2);
        cbor_nondet_map_iterator_t pi1 = i2;
        FStar_Pervasives_Native_option__bool pres1 = { .tag = FStar_Pervasives_Native_None };
        while (true)
        {
          FStar_Pervasives_Native_option__bool res = pres1;
          bool __anf0 = CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty_with_depth(pi1);
          if (!(res.tag == FStar_Pervasives_Native_None && !__anf0))
            break;
          cbor_map_entry x11 = CBOR_Pulse_Raw_Read_cbor_map_iterator_next_with_depth(&pi1);
          if
          (
            CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv_with_depth(x21.cbor_map_entry_key,
              x11.cbor_map_entry_key)
          )
            pres1 =
              (
                (FStar_Pervasives_Native_option__bool){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv_with_depth(x21.cbor_map_entry_value,
                    x11.cbor_map_entry_value)
                }
              );
        }
        pres = CBOR_Pulse_Raw_Util_eq_Some_true(pres1);
      }
      if (!pres)
        return false;
      else
      {
        cbor_nondet_map_iterator_t pi21 = i2;
        bool pres1 = true;
        while (true)
        {
          bool res0 = pres1;
          bool __anf010 = CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty_with_depth(pi21);
          if (!(res0 && !__anf010))
            break;
          cbor_map_entry x21 = CBOR_Pulse_Raw_Read_cbor_map_iterator_next_with_depth(&pi21);
          cbor_nondet_map_iterator_t pi1 = i1;
          FStar_Pervasives_Native_option__bool pres2 = { .tag = FStar_Pervasives_Native_None };
          while (true)
          {
            FStar_Pervasives_Native_option__bool res = pres2;
            bool __anf01 = CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty_with_depth(pi1);
            if (!(res.tag == FStar_Pervasives_Native_None && !__anf01))
              break;
            cbor_map_entry x11 = CBOR_Pulse_Raw_Read_cbor_map_iterator_next_with_depth(&pi1);
            if
            (
              CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv_with_depth(x21.cbor_map_entry_key,
                x11.cbor_map_entry_key)
            )
              pres2 =
                (
                  (FStar_Pervasives_Native_option__bool){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv_with_depth(x21.cbor_map_entry_value,
                      x11.cbor_map_entry_value)
                  }
                );
          }
          pres1 = CBOR_Pulse_Raw_Util_eq_Some_true(pres2);
        }
        return pres1;
      }
    }
  }
}

static bool CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv_with_depth(x1, x2);
}

static bool
CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_no_setoid_repeats(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry x
)
{
  size_t pn1 = (size_t)0U;
  bool pres = true;
  while (true)
  {
    size_t __anf00 = pn1;
    if (!(pres && __anf00 < Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(x)))
      break;
    size_t n1 = pn1;
    cbor_map_entry x1 = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(x, n1);
    size_t n2 = n1 + (size_t)1U;
    pn1 = n2;
    size_t pn2 = n2;
    while (true)
    {
      size_t __anf0 = pn2;
      if (!(pres && __anf0 < Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(x)))
        break;
      size_t n21 = pn2;
      pres =
        !CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv(x1.cbor_map_entry_key,
          Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(x,
            n21).cbor_map_entry_key);
      pn2 = n21 + (size_t)1U;
    }
  }
  return pres;
}

static CBOR_Spec_Raw_Hash_sip CBOR_Spec_Raw_Hash_sip_round(CBOR_Spec_Raw_Hash_sip s)
{
  uint64_t v0 = s.v0 + s.v1;
  uint64_t v11 = (s.v1 << 13U | s.v1 >> 51U) ^ v0;
  uint64_t v2 = s.v2 + s.v3;
  uint64_t v31 = (s.v3 << 16U | s.v3 >> 48U) ^ v2;
  uint64_t v02 = (v0 << 32U | v0 >> 32U) + v31;
  uint64_t v21 = v2 + v11;
  return
    (
      (CBOR_Spec_Raw_Hash_sip){
        .v0 = v02,
        .v1 = (v11 << 17U | v11 >> 47U) ^ v21,
        .v2 = v21 << 32U | v21 >> 32U,
        .v3 = (v31 << 21U | v31 >> 43U) ^ v02,
        .nw = s.nw
      }
    );
}

static CBOR_Spec_Raw_Hash_sip
CBOR_Spec_Raw_Hash_sip_absorb(CBOR_Spec_Raw_Hash_sip s, uint64_t m)
{
  CBOR_Spec_Raw_Hash_sip
  s1 =
    CBOR_Spec_Raw_Hash_sip_round((
        (CBOR_Spec_Raw_Hash_sip){ .v0 = s.v0, .v1 = s.v1, .v2 = s.v2, .v3 = s.v3 ^ m, .nw = s.nw }
      ));
  return
    (
      (CBOR_Spec_Raw_Hash_sip){
        .v0 = s1.v0 ^ m,
        .v1 = s1.v1,
        .v2 = s1.v2,
        .v3 = s1.v3,
        .nw = s.nw + 1ULL
      }
    );
}

static uint64_t CBOR_Spec_Raw_Hash_sip_fin(CBOR_Spec_Raw_Hash_sip s)
{
  uint64_t m = s.nw << 59U;
  CBOR_Spec_Raw_Hash_sip
  s1 =
    CBOR_Spec_Raw_Hash_sip_round((
        (CBOR_Spec_Raw_Hash_sip){ .v0 = s.v0, .v1 = s.v1, .v2 = s.v2, .v3 = s.v3 ^ m, .nw = s.nw }
      ));
  CBOR_Spec_Raw_Hash_sip
  s3 =
    CBOR_Spec_Raw_Hash_sip_round(CBOR_Spec_Raw_Hash_sip_round(CBOR_Spec_Raw_Hash_sip_round((
            (CBOR_Spec_Raw_Hash_sip){
              .v0 = s1.v0 ^ m,
              .v1 = s1.v1,
              .v2 = s1.v2 ^ 0xffULL,
              .v3 = s1.v3,
              .nw = s1.nw
            }
          ))));
  return (s3.v0 ^ s3.v1) ^ (s3.v2 ^ s3.v3);
}

static uint64_t
CBOR_Pulse_Raw_EverParse_DupCheck_hash_word(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  size_t x,
  size_t c
)
{
  size_t pj = c;
  uint64_t pw = 0ULL;
  while (pj > (size_t)0U)
  {
    uint64_t w = pw;
    size_t j_ = pj - (size_t)1U;
    pw = (uint64_t)(uint32_t)Pulse_Lib_Slice_op_Array_Access__uint8_t(b, x + j_) | w << 8U;
    pj = j_;
  }
  return pw;
}

static CBOR_Spec_Raw_Hash_sip
CBOR_Pulse_Raw_EverParse_DupCheck_hash_bytes(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  CBOR_Spec_Raw_Hash_sip st0,
  size_t o,
  size_t len
)
{
  size_t pi = (size_t)0U;
  CBOR_Spec_Raw_Hash_sip pst = st0;
  while (pi < len)
  {
    size_t i = pi;
    CBOR_Spec_Raw_Hash_sip st = pst;
    size_t rem = len - i;
    size_t c = rem < (size_t)8U ? rem : (size_t)8U;
    pst =
      CBOR_Spec_Raw_Hash_sip_absorb(st,
        CBOR_Pulse_Raw_EverParse_DupCheck_hash_word(b, o + i, c));
    pi = i + c;
  }
  return pst;
}

static CBOR_Spec_Raw_Hash_sip
CBOR_Pulse_Raw_EverParse_DupCheck_hash_leaf(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  bool is_string,
  CBOR_Spec_Raw_Hash_sip st0,
  size_t o,
  size_t len
)
{
  if (is_string)
    return CBOR_Pulse_Raw_EverParse_DupCheck_hash_bytes(b, st0, o, len);
  else
    return st0;
}

CBOR_Spec_Raw_Hash_sip
CBOR_Pulse_Raw_EverParse_DupCheck_hash_items(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  uint64_t k0,
  uint64_t k1,
  CBOR_Spec_Raw_Hash_sip st0,
  size_t o0,
  size_t c0,
  size_t *pout
)
{
  size_t po = o0;
  size_t pc = c0;
  CBOR_Spec_Raw_Hash_sip pst = st0;
  while (pc > (size_t)0U)
  {
    size_t o = po;
    size_t c = pc;
    CBOR_Spec_Raw_Hash_sip st = pst;
    size_t oh = CBOR_Pulse_Raw_EverParse_Format_jump_header(b, o);
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    h =
      CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(b,
            o)._2,
          oh - o)._1);
    uint8_t mt = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
    uint8_t mt1 = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
    uint64_t hval;
    if (mt1 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    {
      uint8_t ite;
      if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
        ite = h._1.additional_info;
      else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
        ite = h._2.case_LongArgumentSimpleValue;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      hval = (uint64_t)(uint32_t)ite;
    }
    else if (mt1 == CBOR_MAJOR_TYPE_UINT64 || mt1 == CBOR_MAJOR_TYPE_NEG_INT64)
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
      hval = ite.value;
    }
    else if (mt1 == CBOR_MAJOR_TYPE_BYTE_STRING || mt1 == CBOR_MAJOR_TYPE_TEXT_STRING)
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
      hval = ite.value;
    }
    else if (mt1 == CBOR_MAJOR_TYPE_TAGGED)
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
      hval = ite.value;
    }
    else if (mt1 == CBOR_MAJOR_TYPE_ARRAY)
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
      hval = ite.value;
    }
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
      hval = ite.value;
    }
    CBOR_Spec_Raw_Hash_sip
    st1 =
      CBOR_Spec_Raw_Hash_sip_absorb(CBOR_Spec_Raw_Hash_sip_absorb(st, (uint64_t)(uint32_t)mt),
        hval);
    if (mt == CBOR_MAJOR_TYPE_MAP)
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
      size_t k = (size_t)ite.value;
      size_t pi = (size_t)0U;
      size_t pe = oh;
      uint64_t pacc = 0ULL;
      while (pi < k)
      {
        size_t i = pi;
        uint64_t acc = pacc;
        CBOR_Spec_Raw_Hash_sip
        sk =
          CBOR_Pulse_Raw_EverParse_DupCheck_hash_items(b,
            k0,
            k1,
            (
              (CBOR_Spec_Raw_Hash_sip){
                .v0 = k0 ^ 0x736f6d6570736575ULL,
                .v1 = k1 ^ 0x646f72616e646f6dULL,
                .v2 = k0 ^ 0x6c7967656e657261ULL,
                .v3 = k1 ^ 0x7465646279746573ULL,
                .nw = 0ULL
              }
            ),
            pe,
            (size_t)1U,
            pout);
        CBOR_Spec_Raw_Hash_sip
        sv =
          CBOR_Pulse_Raw_EverParse_DupCheck_hash_items(b,
            k0,
            k1,
            (
              (CBOR_Spec_Raw_Hash_sip){
                .v0 = k0 ^ 0x736f6d6570736575ULL,
                .v1 = k1 ^ 0x646f72616e646f6dULL,
                .v2 = k0 ^ 0x6c7967656e657261ULL,
                .v3 = k1 ^ 0x7465646279746573ULL,
                .nw = 0ULL
              }
            ),
            *pout,
            (size_t)1U,
            pout);
        size_t o2 = *pout;
        pacc =
          acc +
            CBOR_Spec_Raw_Hash_sip_fin(CBOR_Spec_Raw_Hash_sip_absorb(CBOR_Spec_Raw_Hash_sip_absorb((
                    (CBOR_Spec_Raw_Hash_sip){
                      .v0 = k0 ^ 0x736f6d6570736575ULL,
                      .v1 = k1 ^ 0x646f72616e646f6dULL,
                      .v2 = k0 ^ 0x6c7967656e657261ULL,
                      .v3 = k1 ^ 0x7465646279746573ULL,
                      .nw = 0ULL
                    }
                  ),
                  CBOR_Spec_Raw_Hash_sip_fin(sk)),
                CBOR_Spec_Raw_Hash_sip_fin(sv)));
        pe = o2;
        pi = i + (size_t)1U;
      }
      size_t e = pe;
      pst = CBOR_Spec_Raw_Hash_sip_absorb(st1, pacc);
      po = e;
      pc = c - (size_t)1U;
    }
    else
    {
      bool is_string = mt == CBOR_MAJOR_TYPE_BYTE_STRING || mt == CBOR_MAJOR_TYPE_TEXT_STRING;
      size_t leaf;
      if (is_string)
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
        leaf = (size_t)ite.value;
      }
      else
        leaf = (size_t)0U;
      CBOR_Spec_Raw_Hash_sip
      st2 = CBOR_Pulse_Raw_EverParse_DupCheck_hash_leaf(b, is_string, st1, oh, leaf);
      size_t rem = CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h);
      pst = st2;
      po = oh + leaf;
      pc = rem + (c - (size_t)1U);
    }
  }
  *pout = po;
  return pst;
}

static size_t Pulse_Lib_Slice_len__size_t(Pulse_Lib_Slice_slice__size_t s)
{
  return s.len;
}

static void
Pulse_Lib_Slice_op_Array_Assignment__size_t(
  Pulse_Lib_Slice_slice__size_t a,
  size_t i,
  size_t v
)
{
  a.elt[i] = v;
}

static size_t
CBOR_Pulse_Raw_EverParse_DupCheck_fill_offsets(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  Pulse_Lib_Slice_slice__size_t ks,
  size_t o0
)
{
  size_t k = Pulse_Lib_Slice_len__size_t(ks);
  size_t pi = (size_t)0U;
  size_t po = o0;
  while (pi < k)
  {
    size_t i = pi;
    size_t o = po;
    Pulse_Lib_Slice_op_Array_Assignment__size_t(ks, i, o);
    size_t
    o2 =
      CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(b,
        CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(b, o));
    pi = i + (size_t)1U;
    po = o2;
  }
  return po;
}

static CBOR_Pulse_Raw_Slice_byte_slice
Pulse_Lib_Slice_subslice__uint8_t(CBOR_Pulse_Raw_Slice_byte_slice s, size_t i, size_t j)
{
  return ((CBOR_Pulse_Raw_Slice_byte_slice){ .elt = s.elt + i, .len = j - i });
}

static int16_t
CBOR_Pulse_Raw_EverParse_DupCheck_cmp_str(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  size_t o1,
  size_t o2,
  size_t len
)
{
  CBOR_Pulse_Raw_Slice_byte_slice s1 = Pulse_Lib_Slice_subslice__uint8_t(b, o1, o1 + len);
  return
    CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(s1,
      Pulse_Lib_Slice_subslice__uint8_t(b, o2, o2 + len));
}

static int16_t
CBOR_Pulse_Raw_EverParse_DupCheck_cmp_leaf(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  bool is_string,
  size_t o1,
  size_t o2,
  size_t len
)
{
  if (is_string)
    return CBOR_Pulse_Raw_EverParse_DupCheck_cmp_str(b, o1, o2, len);
  else
    return 0;
}

typedef struct
FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t_s
{
  Pulse_Lib_Slice_slice__size_t _1;
  Pulse_Lib_Slice_slice__size_t _2;
}
FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t;

static FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t
Pulse_Lib_Slice_split__size_t(Pulse_Lib_Slice_slice__size_t s, size_t i)
{
  return
    (
      (FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t){
        ._1 = { .elt = s.elt, .len = i },
        ._2 = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static size_t
Pulse_Lib_Slice_op_Array_Access__size_t(Pulse_Lib_Slice_slice__size_t a, size_t i)
{
  return a.elt[i];
}

static void
Pulse_Lib_Slice_copy__size_t(
  Pulse_Lib_Slice_slice__size_t dst,
  Pulse_Lib_Slice_slice__size_t src
)
{
  memcpy(dst.elt, src.elt, src.len * sizeof (size_t));
}

int16_t
CBOR_Pulse_Raw_EverParse_DupCheck_cmp_one(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  Pulse_Lib_Slice_slice__size_t sc,
  size_t x,
  size_t y
)
{
  size_t po1 = x;
  size_t po2 = y;
  size_t pc = (size_t)1U;
  int16_t pres = 0;
  while (true)
  {
    size_t c0 = pc;
    if (!(pres == 0 && c0 > (size_t)0U))
      break;
    size_t o1 = po1;
    size_t o2 = po2;
    size_t c = pc;
    size_t oh1 = CBOR_Pulse_Raw_EverParse_Format_jump_header(b, o1);
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    h1 =
      CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(b,
            o1)._2,
          oh1 - o1)._1);
    size_t oh2 = CBOR_Pulse_Raw_EverParse_Format_jump_header(b, o2);
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    h2 =
      CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(b,
            o2)._2,
          oh2 - o2)._1);
    uint8_t mt1 = CBOR_Spec_Raw_EverParse_get_header_major_type(h1);
    uint8_t mt2 = CBOR_Spec_Raw_EverParse_get_header_major_type(h2);
    if (mt1 != mt2)
      pres = mt1 < mt2 ? -1 : 1;
    else
    {
      uint8_t mt = CBOR_Spec_Raw_EverParse_get_header_major_type(h1);
      int16_t hc;
      if (mt == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      {
        uint8_t ite0;
        if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite0 = h1._1.additional_info;
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
          ite0 = h1._2.case_LongArgumentSimpleValue;
        else
          ite0 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
        uint8_t ite1;
        if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite1 = h2._1.additional_info;
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
          ite1 = h2._2.case_LongArgumentSimpleValue;
        else
          ite1 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
        if (ite0 < ite1)
          hc = -1;
        else
        {
          uint8_t ite0;
          if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite0 = h1._1.additional_info;
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
            ite0 = h1._2.case_LongArgumentSimpleValue;
          else
            ite0 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
          uint8_t ite;
          if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite = h2._1.additional_info;
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
            ite = h2._2.case_LongArgumentSimpleValue;
          else
            ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
          if (ite0 > ite)
            hc = 1;
          else
            hc = 0;
        }
      }
      else if (mt == CBOR_MAJOR_TYPE_UINT64 || mt == CBOR_MAJOR_TYPE_NEG_INT64)
      {
        CBOR_Spec_Raw_Base_raw_uint64 ite0;
        if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h1._2.case_LongArgumentU32
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite0 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h1._1.additional_info
              }
            );
        else
          ite0 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        CBOR_Spec_Raw_Base_raw_uint64 ite1;
        if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h2._2.case_LongArgumentU32
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite1 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h2._1.additional_info
              }
            );
        else
          ite1 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        if (ite0.value < ite1.value)
          hc = -1;
        else
        {
          CBOR_Spec_Raw_Base_raw_uint64 ite0;
          if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h1._2.case_LongArgumentU32
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite0 =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h1._1.additional_info
                }
              );
          else
            ite0 =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          CBOR_Spec_Raw_Base_raw_uint64 ite;
          if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h2._2.case_LongArgumentU32
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h2._1.additional_info
                }
              );
          else
            ite =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          if (ite0.value > ite.value)
            hc = 1;
          else
            hc = 0;
        }
      }
      else if (mt == CBOR_MAJOR_TYPE_BYTE_STRING || mt == CBOR_MAJOR_TYPE_TEXT_STRING)
      {
        CBOR_Spec_Raw_Base_raw_uint64 ite0;
        if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h1._2.case_LongArgumentU32
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite0 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h1._1.additional_info
              }
            );
        else
          ite0 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        CBOR_Spec_Raw_Base_raw_uint64 ite1;
        if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h2._2.case_LongArgumentU32
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite1 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h2._1.additional_info
              }
            );
        else
          ite1 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        if (ite0.value < ite1.value)
          hc = -1;
        else
        {
          CBOR_Spec_Raw_Base_raw_uint64 ite0;
          if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h1._2.case_LongArgumentU32
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite0 =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h1._1.additional_info
                }
              );
          else
            ite0 =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          CBOR_Spec_Raw_Base_raw_uint64 ite;
          if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h2._2.case_LongArgumentU32
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h2._1.additional_info
                }
              );
          else
            ite =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          if (ite0.value > ite.value)
            hc = 1;
          else
            hc = 0;
        }
      }
      else if (mt == CBOR_MAJOR_TYPE_TAGGED)
      {
        CBOR_Spec_Raw_Base_raw_uint64 ite0;
        if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h1._2.case_LongArgumentU32
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite0 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h1._1.additional_info
              }
            );
        else
          ite0 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        CBOR_Spec_Raw_Base_raw_uint64 ite1;
        if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h2._2.case_LongArgumentU32
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite1 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h2._1.additional_info
              }
            );
        else
          ite1 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        if (ite0.value < ite1.value)
          hc = -1;
        else
        {
          CBOR_Spec_Raw_Base_raw_uint64 ite0;
          if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h1._2.case_LongArgumentU32
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite0 =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h1._1.additional_info
                }
              );
          else
            ite0 =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          CBOR_Spec_Raw_Base_raw_uint64 ite;
          if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h2._2.case_LongArgumentU32
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h2._1.additional_info
                }
              );
          else
            ite =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          if (ite0.value > ite.value)
            hc = 1;
          else
            hc = 0;
        }
      }
      else if (mt == CBOR_MAJOR_TYPE_ARRAY)
      {
        CBOR_Spec_Raw_Base_raw_uint64 ite0;
        if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h1._2.case_LongArgumentU32
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite0 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h1._1.additional_info
              }
            );
        else
          ite0 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        CBOR_Spec_Raw_Base_raw_uint64 ite1;
        if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h2._2.case_LongArgumentU32
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite1 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h2._1.additional_info
              }
            );
        else
          ite1 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        if (ite0.value < ite1.value)
          hc = -1;
        else
        {
          CBOR_Spec_Raw_Base_raw_uint64 ite0;
          if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h1._2.case_LongArgumentU32
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite0 =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h1._1.additional_info
                }
              );
          else
            ite0 =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          CBOR_Spec_Raw_Base_raw_uint64 ite;
          if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h2._2.case_LongArgumentU32
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h2._1.additional_info
                }
              );
          else
            ite =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          if (ite0.value > ite.value)
            hc = 1;
          else
            hc = 0;
        }
      }
      else
      {
        CBOR_Spec_Raw_Base_raw_uint64 ite0;
        if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h1._2.case_LongArgumentU32
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite0 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite0 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h1._1.additional_info
              }
            );
        else
          ite0 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        CBOR_Spec_Raw_Base_raw_uint64 ite1;
        if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h2._2.case_LongArgumentU32
              }
            );
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite1 =
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
        else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite1 =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h2._1.additional_info
              }
            );
        else
          ite1 =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        if (ite0.value < ite1.value)
          hc = -1;
        else
        {
          CBOR_Spec_Raw_Base_raw_uint64 ite0;
          if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h1._2.case_LongArgumentU32
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite0 =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite0 =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h1._1.additional_info
                }
              );
          else
            ite0 =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          CBOR_Spec_Raw_Base_raw_uint64 ite;
          if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU8
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h2._2.case_LongArgumentU16
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h2._2.case_LongArgumentU32
                }
              );
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h2._2.case_LongArgumentU64 });
          else if (h2._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h2._1.additional_info
                }
              );
          else
            ite =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          if (ite0.value > ite.value)
            hc = 1;
          else
            hc = 0;
        }
      }
      if (hc != 0)
        pres = hc;
      else if (mt1 == CBOR_MAJOR_TYPE_MAP)
      {
        CBOR_Spec_Raw_Base_raw_uint64 ite;
        if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
          ite =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 1U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
          ite =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 2U,
                .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
          ite =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 3U,
                .value = (uint64_t)h1._2.case_LongArgumentU32
              }
            );
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
          ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
        else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
          ite =
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = 0U,
                .value = (uint64_t)(uint32_t)h1._1.additional_info
              }
            );
        else
          ite =
            KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t k = (size_t)ite.value;
        FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t
        scrut0 = Pulse_Lib_Slice_split__size_t(sc, k);
        Pulse_Lib_Slice_slice__size_t ks1 = scrut0._1;
        FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t
        scrut1 = Pulse_Lib_Slice_split__size_t(scrut0._2, k);
        Pulse_Lib_Slice_slice__size_t ks2 = scrut1._1;
        FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t
        scrut = Pulse_Lib_Slice_split__size_t(scrut1._2, k);
        Pulse_Lib_Slice_slice__size_t tmp = scrut._1;
        Pulse_Lib_Slice_slice__size_t rest = scrut._2;
        size_t o_ = CBOR_Pulse_Raw_EverParse_DupCheck_fill_offsets(b, ks1, oh1);
        size_t n = Pulse_Lib_Slice_len__size_t(ks1);
        size_t pw = (size_t)1U;
        bool pok = true;
        bool pdone = n <= (size_t)1U;
        while (true)
        {
          bool done = pdone;
          if (!(pok && !done))
            break;
          size_t w = pw;
          size_t n1 = Pulse_Lib_Slice_len__size_t(ks1);
          size_t plo = (size_t)0U;
          bool pok1 = true;
          while (true)
          {
            size_t lo = plo;
            if (!(pok1 && lo < n1))
              break;
            size_t lo0 = plo;
            size_t mid = w <= n1 - lo0 ? lo0 + w : n1;
            size_t hi = w <= n1 - mid ? mid + w : n1;
            size_t pi1 = lo0;
            size_t pi2 = mid;
            size_t pk = lo0;
            bool pok2 = true;
            while (true)
            {
              size_t i1 = pi1;
              size_t i20 = pi2;
              if (!(pok2 && (i1 != mid || i20 != hi)))
                break;
              size_t i10 = pi1;
              size_t i2 = pi2;
              size_t k1 = pk;
              if (i10 == mid)
              {
                Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp,
                  k1,
                  Pulse_Lib_Slice_op_Array_Access__size_t(ks1, i2));
                pi2 = i2 + (size_t)1U;
                pk = k1 + (size_t)1U;
              }
              else if (i2 == hi)
              {
                Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp,
                  k1,
                  Pulse_Lib_Slice_op_Array_Access__size_t(ks1, i10));
                pi1 = i10 + (size_t)1U;
                pk = k1 + (size_t)1U;
              }
              else
              {
                size_t x1 = Pulse_Lib_Slice_op_Array_Access__size_t(ks1, i10);
                size_t x2 = Pulse_Lib_Slice_op_Array_Access__size_t(ks1, i2);
                int16_t c1 = CBOR_Pulse_Raw_EverParse_DupCheck_cmp_one(b, rest, x1, x2);
                if (c1 == 0)
                  pok2 = false;
                else if (c1 < 0)
                {
                  Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp, k1, x1);
                  pi1 = i10 + (size_t)1U;
                  pk = k1 + (size_t)1U;
                }
                else
                {
                  Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp, k1, x2);
                  pi2 = i2 + (size_t)1U;
                  pk = k1 + (size_t)1U;
                }
              }
            }
            if (pok2)
              plo = hi;
            else
              pok1 = false;
          }
          if (pok1)
          {
            Pulse_Lib_Slice_copy__size_t(ks1, tmp);
            if (n - w <= w)
              pdone = true;
            else
              pw = w + w;
          }
          else
            pok = false;
        }
        size_t o_1 = CBOR_Pulse_Raw_EverParse_DupCheck_fill_offsets(b, ks2, oh2);
        size_t n1 = Pulse_Lib_Slice_len__size_t(ks2);
        size_t pw1 = (size_t)1U;
        bool pok1 = true;
        bool pdone1 = n1 <= (size_t)1U;
        while (true)
        {
          bool done = pdone1;
          if (!(pok1 && !done))
            break;
          size_t w = pw1;
          size_t n2 = Pulse_Lib_Slice_len__size_t(ks2);
          size_t plo = (size_t)0U;
          bool pok2 = true;
          while (true)
          {
            size_t lo = plo;
            if (!(pok2 && lo < n2))
              break;
            size_t lo0 = plo;
            size_t mid = w <= n2 - lo0 ? lo0 + w : n2;
            size_t hi = w <= n2 - mid ? mid + w : n2;
            size_t pi1 = lo0;
            size_t pi2 = mid;
            size_t pk = lo0;
            bool pok3 = true;
            while (true)
            {
              size_t i1 = pi1;
              size_t i20 = pi2;
              if (!(pok3 && (i1 != mid || i20 != hi)))
                break;
              size_t i10 = pi1;
              size_t i2 = pi2;
              size_t k1 = pk;
              if (i10 == mid)
              {
                Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp,
                  k1,
                  Pulse_Lib_Slice_op_Array_Access__size_t(ks2, i2));
                pi2 = i2 + (size_t)1U;
                pk = k1 + (size_t)1U;
              }
              else if (i2 == hi)
              {
                Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp,
                  k1,
                  Pulse_Lib_Slice_op_Array_Access__size_t(ks2, i10));
                pi1 = i10 + (size_t)1U;
                pk = k1 + (size_t)1U;
              }
              else
              {
                size_t x1 = Pulse_Lib_Slice_op_Array_Access__size_t(ks2, i10);
                size_t x2 = Pulse_Lib_Slice_op_Array_Access__size_t(ks2, i2);
                int16_t c1 = CBOR_Pulse_Raw_EverParse_DupCheck_cmp_one(b, rest, x1, x2);
                if (c1 == 0)
                  pok3 = false;
                else if (c1 < 0)
                {
                  Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp, k1, x1);
                  pi1 = i10 + (size_t)1U;
                  pk = k1 + (size_t)1U;
                }
                else
                {
                  Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp, k1, x2);
                  pi2 = i2 + (size_t)1U;
                  pk = k1 + (size_t)1U;
                }
              }
            }
            if (pok3)
              plo = hi;
            else
              pok2 = false;
          }
          if (pok2)
          {
            Pulse_Lib_Slice_copy__size_t(ks2, tmp);
            if (n1 - w <= w)
              pdone1 = true;
            else
              pw1 = w + w;
          }
          else
            pok1 = false;
        }
        size_t k1 = Pulse_Lib_Slice_len__size_t(ks1);
        size_t pi = (size_t)0U;
        int16_t pr = 0;
        while (true)
        {
          size_t i = pi;
          if (!(pr == 0 && i < k1))
            break;
          size_t i0 = pi;
          size_t x1 = Pulse_Lib_Slice_op_Array_Access__size_t(ks1, i0);
          size_t x2 = Pulse_Lib_Slice_op_Array_Access__size_t(ks2, i0);
          int16_t rk = CBOR_Pulse_Raw_EverParse_DupCheck_cmp_one(b, rest, x1, x2);
          if (rk == 0)
          {
            size_t v1 = CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(b, x1);
            pr =
              CBOR_Pulse_Raw_EverParse_DupCheck_cmp_one(b,
                rest,
                v1,
                CBOR_Pulse_Raw_EverParse_Format_jump_raw_data_item(b, x2));
            pi = i0 + (size_t)1U;
          }
          else
          {
            pr = rk;
            pi = i0 + (size_t)1U;
          }
        }
        int16_t r = pr;
        int16_t r3 = r == 0 ? r : r;
        po1 = o_;
        po2 = o_1;
        int16_t r0 = r3;
        if (r0 != 0)
        {
          po1 = o1;
          po2 = o2;
          pres = r0;
        }
        else
          pc = c - (size_t)1U;
      }
      else
      {
        bool is_string = mt1 == CBOR_MAJOR_TYPE_BYTE_STRING || mt1 == CBOR_MAJOR_TYPE_TEXT_STRING;
        size_t leaf;
        if (is_string)
        {
          CBOR_Spec_Raw_Base_raw_uint64 ite;
          if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 1U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU8
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 2U,
                  .value = (uint64_t)(uint32_t)h1._2.case_LongArgumentU16
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 3U,
                  .value = (uint64_t)h1._2.case_LongArgumentU32
                }
              );
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
            ite =
              ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h1._2.case_LongArgumentU64 });
          else if (h1._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
            ite =
              (
                (CBOR_Spec_Raw_Base_raw_uint64){
                  .size = 0U,
                  .value = (uint64_t)(uint32_t)h1._1.additional_info
                }
              );
          else
            ite =
              KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
                "unreachable (pattern matches are exhaustive in F*)");
          leaf = (size_t)ite.value;
        }
        else
          leaf = (size_t)0U;
        int16_t rs = CBOR_Pulse_Raw_EverParse_DupCheck_cmp_leaf(b, is_string, oh1, oh2, leaf);
        if (rs != 0)
          pres = rs;
        else
        {
          size_t rem = CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h1);
          po1 = oh1 + leaf;
          po2 = oh2 + leaf;
          pc = rem + (c - (size_t)1U);
        }
      }
    }
  }
  return pres;
}

static size_t Pulse_Lib_Slice_len__uint64_t(Pulse_Lib_Slice_slice__uint64_t s)
{
  return s.len;
}

typedef struct
FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint64_t_Pulse_Lib_Slice_slice__uint64_t_s
{
  Pulse_Lib_Slice_slice__uint64_t _1;
  Pulse_Lib_Slice_slice__uint64_t _2;
}
FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint64_t_Pulse_Lib_Slice_slice__uint64_t;

static FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint64_t_Pulse_Lib_Slice_slice__uint64_t
Pulse_Lib_Slice_split__uint64_t(Pulse_Lib_Slice_slice__uint64_t s, size_t i)
{
  return
    (
      (FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__uint64_t_Pulse_Lib_Slice_slice__uint64_t){
        ._1 = { .elt = s.elt, .len = i },
        ._2 = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static void
Pulse_Lib_Slice_op_Array_Assignment__uint64_t(
  Pulse_Lib_Slice_slice__uint64_t a,
  size_t i,
  uint64_t v
)
{
  a.elt[i] = v;
}

static uint64_t
Pulse_Lib_Slice_op_Array_Access__uint64_t(Pulse_Lib_Slice_slice__uint64_t a, size_t i)
{
  return a.elt[i];
}

bool
CBOR_Pulse_Raw_EverParse_DupCheck_check_items(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  Pulse_Lib_Slice_slice__size_t sc,
  uint64_t k0,
  uint64_t k1,
  Pulse_Lib_Slice_slice__uint64_t hv,
  Pulse_Lib_Slice_slice__size_t idx,
  size_t o0,
  size_t c0,
  size_t *pout
)
{
  size_t po = o0;
  size_t pc = c0;
  bool pres = true;
  while (true)
  {
    size_t c0 = pc;
    if (!(pres && c0 > (size_t)0U))
      break;
    size_t o = po;
    size_t c = pc;
    size_t oh = CBOR_Pulse_Raw_EverParse_Format_jump_header(b, o);
    prims_dtuple2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument
    h =
      CBOR_Pulse_Raw_EverParse_Format_read_header(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(b,
            o)._2,
          oh - o)._1);
    uint8_t mt = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
    if (mt == CBOR_MAJOR_TYPE_MAP)
    {
      CBOR_Spec_Raw_Base_raw_uint64 ite0;
      if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
        ite0 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = 1U,
              .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU8
            }
          );
      else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
        ite0 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = 2U,
              .value = (uint64_t)(uint32_t)h._2.case_LongArgumentU16
            }
          );
      else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
        ite0 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = 3U,
              .value = (uint64_t)h._2.case_LongArgumentU32
            }
          );
      else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
        ite0 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = h._2.case_LongArgumentU64 });
      else if (h._2.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
        ite0 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = 0U,
              .value = (uint64_t)(uint32_t)h._1.additional_info
            }
          );
      else
        ite0 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      size_t k = (size_t)ite0.value;
      FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t
      scrut0 = Pulse_Lib_Slice_split__size_t(sc, k);
      Pulse_Lib_Slice_slice__size_t ks = scrut0._1;
      FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t
      scrut = Pulse_Lib_Slice_split__size_t(scrut0._2, k);
      Pulse_Lib_Slice_slice__size_t tmp = scrut._1;
      Pulse_Lib_Slice_slice__size_t rest = scrut._2;
      size_t pi = (size_t)0U;
      size_t pe = oh;
      bool pr = true;
      while (true)
      {
        size_t i = pi;
        if (!(pr && i < k))
          break;
        size_t i0 = pi;
        size_t e = pe;
        if
        (
          CBOR_Pulse_Raw_EverParse_DupCheck_check_items(b,
            rest,
            k0,
            k1,
            hv,
            idx,
            e,
            (size_t)2U,
            pout)
        )
        {
          size_t o_ = *pout;
          Pulse_Lib_Slice_op_Array_Assignment__size_t(ks, i0, e);
          pi = i0 + (size_t)1U;
          pe = o_;
        }
        else
          pr = false;
      }
      size_t e = pe;
      bool ite;
      if (pr)
      {
        *pout = e;
        size_t k2 = Pulse_Lib_Slice_len__size_t(ks);
        if (k2 <= Pulse_Lib_Slice_len__uint64_t(hv) && k2 <= Pulse_Lib_Slice_len__size_t(idx))
        {
          Pulse_Lib_Slice_slice__uint64_t hv1 = Pulse_Lib_Slice_split__uint64_t(hv, k2)._1;
          Pulse_Lib_Slice_slice__size_t idx1 = Pulse_Lib_Slice_split__size_t(idx, k2)._1;
          size_t k3 = Pulse_Lib_Slice_len__size_t(ks);
          size_t pi1 = (size_t)0U;
          size_t po1 = (size_t)0U;
          while (pi1 < k3)
          {
            size_t i = pi1;
            Pulse_Lib_Slice_op_Array_Assignment__uint64_t(hv1,
              i,
              CBOR_Spec_Raw_Hash_sip_fin(CBOR_Pulse_Raw_EverParse_DupCheck_hash_items(b,
                  k0,
                  k1,
                  (
                    (CBOR_Spec_Raw_Hash_sip){
                      .v0 = k0 ^ 0x736f6d6570736575ULL,
                      .v1 = k1 ^ 0x646f72616e646f6dULL,
                      .v2 = k0 ^ 0x6c7967656e657261ULL,
                      .v3 = k1 ^ 0x7465646279746573ULL,
                      .nw = 0ULL
                    }
                  ),
                  Pulse_Lib_Slice_op_Array_Access__size_t(ks, i),
                  (size_t)1U,
                  &po1)));
            Pulse_Lib_Slice_op_Array_Assignment__size_t(idx1, i, i);
            pi1 = i + (size_t)1U;
          }
          size_t n = Pulse_Lib_Slice_len__size_t(idx1);
          size_t pw = (size_t)1U;
          bool pok = true;
          bool pdone = n <= (size_t)1U;
          while (true)
          {
            bool done = pdone;
            if (!(pok && !done))
              break;
            size_t w = pw;
            size_t n1 = Pulse_Lib_Slice_len__size_t(idx1);
            size_t plo = (size_t)0U;
            bool pok1 = true;
            while (true)
            {
              size_t lo = plo;
              if (!(pok1 && lo < n1))
                break;
              size_t lo0 = plo;
              size_t mid = w <= n1 - lo0 ? lo0 + w : n1;
              size_t hi = w <= n1 - mid ? mid + w : n1;
              size_t pi11 = lo0;
              size_t pi2 = mid;
              size_t pk = lo0;
              bool pok2 = true;
              while (true)
              {
                size_t i1 = pi11;
                size_t i20 = pi2;
                if (!(pok2 && (i1 != mid || i20 != hi)))
                  break;
                size_t i10 = pi11;
                size_t i2 = pi2;
                size_t k4 = pk;
                if (i10 == mid)
                {
                  Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp,
                    k4,
                    Pulse_Lib_Slice_op_Array_Access__size_t(idx1, i2));
                  pi2 = i2 + (size_t)1U;
                  pk = k4 + (size_t)1U;
                }
                else if (i2 == hi)
                {
                  Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp,
                    k4,
                    Pulse_Lib_Slice_op_Array_Access__size_t(idx1, i10));
                  pi11 = i10 + (size_t)1U;
                  pk = k4 + (size_t)1U;
                }
                else
                {
                  size_t x1 = Pulse_Lib_Slice_op_Array_Access__size_t(idx1, i10);
                  size_t x2 = Pulse_Lib_Slice_op_Array_Access__size_t(idx1, i2);
                  uint64_t hi1 = Pulse_Lib_Slice_op_Array_Access__uint64_t(hv1, x1);
                  uint64_t hj = Pulse_Lib_Slice_op_Array_Access__uint64_t(hv1, x2);
                  int16_t c1;
                  if (hi1 < hj)
                    c1 = -1;
                  else if (hj < hi1)
                    c1 = 1;
                  else
                  {
                    size_t xi = Pulse_Lib_Slice_op_Array_Access__size_t(ks, x1);
                    c1 =
                      CBOR_Pulse_Raw_EverParse_DupCheck_cmp_one(b,
                        rest,
                        xi,
                        Pulse_Lib_Slice_op_Array_Access__size_t(ks, x2));
                  }
                  if (c1 == 0)
                    pok2 = false;
                  else if (c1 < 0)
                  {
                    Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp, k4, x1);
                    pi11 = i10 + (size_t)1U;
                    pk = k4 + (size_t)1U;
                  }
                  else
                  {
                    Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp, k4, x2);
                    pi2 = i2 + (size_t)1U;
                    pk = k4 + (size_t)1U;
                  }
                }
              }
              if (pok2)
                plo = hi;
              else
                pok1 = false;
            }
            if (pok1)
            {
              Pulse_Lib_Slice_copy__size_t(idx1, tmp);
              if (n - w <= w)
                pdone = true;
              else
                pw = w + w;
            }
            else
              pok = false;
          }
          ite = pok;
        }
        else
        {
          size_t n = Pulse_Lib_Slice_len__size_t(ks);
          size_t pw = (size_t)1U;
          bool pok = true;
          bool pdone = n <= (size_t)1U;
          while (true)
          {
            bool done = pdone;
            if (!(pok && !done))
              break;
            size_t w = pw;
            size_t n1 = Pulse_Lib_Slice_len__size_t(ks);
            size_t plo = (size_t)0U;
            bool pok1 = true;
            while (true)
            {
              size_t lo = plo;
              if (!(pok1 && lo < n1))
                break;
              size_t lo0 = plo;
              size_t mid = w <= n1 - lo0 ? lo0 + w : n1;
              size_t hi = w <= n1 - mid ? mid + w : n1;
              size_t pi1 = lo0;
              size_t pi2 = mid;
              size_t pk = lo0;
              bool pok2 = true;
              while (true)
              {
                size_t i1 = pi1;
                size_t i20 = pi2;
                if (!(pok2 && (i1 != mid || i20 != hi)))
                  break;
                size_t i10 = pi1;
                size_t i2 = pi2;
                size_t k3 = pk;
                if (i10 == mid)
                {
                  Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp,
                    k3,
                    Pulse_Lib_Slice_op_Array_Access__size_t(ks, i2));
                  pi2 = i2 + (size_t)1U;
                  pk = k3 + (size_t)1U;
                }
                else if (i2 == hi)
                {
                  Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp,
                    k3,
                    Pulse_Lib_Slice_op_Array_Access__size_t(ks, i10));
                  pi1 = i10 + (size_t)1U;
                  pk = k3 + (size_t)1U;
                }
                else
                {
                  size_t x1 = Pulse_Lib_Slice_op_Array_Access__size_t(ks, i10);
                  size_t x2 = Pulse_Lib_Slice_op_Array_Access__size_t(ks, i2);
                  int16_t c1 = CBOR_Pulse_Raw_EverParse_DupCheck_cmp_one(b, rest, x1, x2);
                  if (c1 == 0)
                    pok2 = false;
                  else if (c1 < 0)
                  {
                    Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp, k3, x1);
                    pi1 = i10 + (size_t)1U;
                    pk = k3 + (size_t)1U;
                  }
                  else
                  {
                    Pulse_Lib_Slice_op_Array_Assignment__size_t(tmp, k3, x2);
                    pi2 = i2 + (size_t)1U;
                    pk = k3 + (size_t)1U;
                  }
                }
              }
              if (pok2)
                plo = hi;
              else
                pok1 = false;
            }
            if (pok1)
            {
              Pulse_Lib_Slice_copy__size_t(ks, tmp);
              if (n - w <= w)
                pdone = true;
              else
                pw = w + w;
            }
            else
              pok = false;
          }
          bool ok = pok;
          ite = ok ? ok : ok;
        }
      }
      else
        ite = false;
      if (ite)
      {
        po = *pout;
        pc = c - (size_t)1U;
      }
      else
        pres = false;
    }
    else
    {
      size_t leaf;
      if (mt == CBOR_MAJOR_TYPE_BYTE_STRING || mt == CBOR_MAJOR_TYPE_TEXT_STRING)
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
        leaf = (size_t)ite.value;
      }
      else
        leaf = (size_t)0U;
      size_t rem = CBOR_Pulse_Raw_EverParse_Format_impl_remaining_data_items_header(h);
      po = oh + leaf;
      pc = rem + (c - (size_t)1U);
    }
  }
  bool r = pres;
  if (r)
  {
    *pout = po;
    return r;
  }
  else
    return r;
}

static bool
CBOR_Pulse_Raw_EverParse_DupCheck_Top_dupcheck_sort_scratch_ok(
  size_t map_depth_bound,
  size_t map_length_bound,
  size_t scratch_len
)
{
  return
    map_depth_bound == (size_t)0U || map_length_bound <= scratch_len / (size_t)3U / map_depth_bound;
}

static bool
CBOR_Pulse_Raw_EverParse_DupCheck_Top_check_dups_top_gen(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  Pulse_Lib_Slice_slice__size_t sc,
  uint64_t k0,
  uint64_t k1,
  Pulse_Lib_Slice_slice__uint64_t hv,
  Pulse_Lib_Slice_slice__size_t idx
)
{
  size_t buf = (size_t)0U;
  return
    CBOR_Pulse_Raw_EverParse_DupCheck_check_items(b,
      sc,
      k0,
      k1,
      hv,
      idx,
      (size_t)0U,
      (size_t)1U,
      &buf);
}

static Pulse_Lib_Slice_slice__uint64_t
Pulse_Lib_Slice_from_array__uint64_t(uint64_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint64_t){ .elt = a, .len = alen });
}

static bool
CBOR_Pulse_Raw_EverParse_DupCheck_Top_check_dups_top(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  Pulse_Lib_Slice_slice__size_t sc
)
{
  FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t
  scrut = Pulse_Lib_Slice_split__size_t(sc, (size_t)0U);
  Pulse_Lib_Slice_slice__size_t idx = scrut._1;
  Pulse_Lib_Slice_slice__size_t sc_ = scrut._2;
  uint64_t buf = 0ULL;
  return
    CBOR_Pulse_Raw_EverParse_DupCheck_Top_check_dups_top_gen(b,
      sc_,
      0ULL,
      0ULL,
      Pulse_Lib_Slice_from_array__uint64_t(&buf, (size_t)1U),
      idx);
}

static bool
CBOR_Pulse_Raw_EverParse_DupCheck_Top_dupcheck_hash_scratch_ok(
  size_t map_depth_bound,
  size_t map_length_bound,
  size_t scratch_len,
  size_t hash_scratch_len
)
{
  if (map_length_bound <= scratch_len && map_length_bound <= hash_scratch_len)
    return
      CBOR_Pulse_Raw_EverParse_DupCheck_Top_dupcheck_sort_scratch_ok(map_depth_bound,
        map_length_bound,
        scratch_len - map_length_bound);
  else
    return false;
}

static bool
CBOR_Pulse_Raw_EverParse_DupCheck_Top_check_dups_top_hash(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  size_t n,
  uint64_t k0,
  uint64_t k1,
  Pulse_Lib_Slice_slice__size_t sc,
  Pulse_Lib_Slice_slice__uint64_t hv
)
{
  FStar_Pervasives_Native_tuple2__Pulse_Lib_Slice_slice__size_t_Pulse_Lib_Slice_slice__size_t
  scrut = Pulse_Lib_Slice_split__size_t(sc, n);
  return
    CBOR_Pulse_Raw_EverParse_DupCheck_Top_check_dups_top_gen(b,
      scrut._2,
      k0,
      k1,
      hv,
      scrut._1);
}

static size_t
CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet(
  FStar_Pervasives_Native_option__size_t map_key_bound,
  bool strict_check,
  CBOR_Pulse_Raw_Slice_byte_slice input
)
{
  size_t poff = (size_t)0U;
  if (CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item(input, &poff))
  {
    size_t off = poff;
    if
    (
      CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_valid_basic(map_key_bound,
        strict_check,
        Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, (size_t)0U)._2,
          off - (size_t)0U)._1)
    )
      return off;
    else
      return (size_t)0U;
  }
  else
    return (size_t)0U;
}

static size_t
CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_map_length_bounded(
  size_t map_length_bound,
  FStar_Pervasives_Native_option__size_t map_key_bound,
  bool strict_check,
  CBOR_Pulse_Raw_Slice_byte_slice input
)
{
  size_t poff = (size_t)0U;
  if
  (
    CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_map_length_bounded(map_length_bound,
      input,
      &poff)
  )
  {
    size_t off = poff;
    if
    (
      CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_valid_basic(map_key_bound,
        strict_check,
        Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, (size_t)0U)._2,
          off - (size_t)0U)._1)
    )
      return off;
    else
      return (size_t)0U;
  }
  else
    return (size_t)0U;
}

static bool
CBOR_Pulse_Raw_Format_Nondet_Validate_check_map_key_bound_after_validate(
  FStar_Pervasives_Native_option__size_t map_key_bound,
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t off
)
{
  if (map_key_bound.tag == FStar_Pervasives_Native_None)
    return true;
  else if (map_key_bound.tag == FStar_Pervasives_Native_Some)
  {
    size_t kb = map_key_bound.v;
    return
      CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_key_depth(kb,
        Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, (size_t)0U)._2,
          off - (size_t)0U)._1);
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

static size_t
CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded(
  size_t map_depth_bound,
  size_t map_length_bound,
  FStar_Pervasives_Native_option__size_t map_key_bound,
  CBOR_Pulse_Raw_Slice_byte_slice input
)
{
  size_t poff = (size_t)0U;
  if
  (
    CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_bounded(map_depth_bound,
      map_length_bound,
      input,
      &poff)
  )
  {
    size_t off = poff;
    if
    (
      CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_valid_basic((
          (FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None }
        ),
        false,
        Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(input, (size_t)0U)._2,
          off - (size_t)0U)._1)
    )
      if
      (
        CBOR_Pulse_Raw_Format_Nondet_Validate_check_map_key_bound_after_validate(map_key_bound,
          input,
          off)
      )
        return off;
      else
        return (size_t)0U;
    else
      return (size_t)0U;
  }
  else
    return (size_t)0U;
}

static bool
CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded_sort_scratch_ok_impl(
  size_t map_depth_bound,
  size_t map_length_bound,
  size_t scratch_len
)
{
  return
    CBOR_Pulse_Raw_EverParse_DupCheck_Top_dupcheck_sort_scratch_ok(map_depth_bound,
      map_length_bound,
      scratch_len);
}

static size_t
CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded_sort(
  size_t map_depth_bound,
  size_t map_length_bound,
  FStar_Pervasives_Native_option__size_t map_key_bound,
  CBOR_Pulse_Raw_Slice_byte_slice input,
  Pulse_Lib_Slice_slice__size_t scratch
)
{
  if
  (
    !CBOR_Pulse_Raw_EverParse_DupCheck_Top_dupcheck_sort_scratch_ok(map_depth_bound,
      map_length_bound,
      Pulse_Lib_Slice_len__size_t(scratch))
  )
    return (size_t)0U;
  else
  {
    size_t poff = (size_t)0U;
    if
    (
      CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_bounded(map_depth_bound,
        map_length_bound,
        input,
        &poff)
    )
    {
      size_t off = poff;
      if (CBOR_Pulse_Raw_EverParse_DupCheck_Top_check_dups_top(input, scratch))
        if
        (
          CBOR_Pulse_Raw_Format_Nondet_Validate_check_map_key_bound_after_validate(map_key_bound,
            input,
            off)
        )
          return off;
        else
          return (size_t)0U;
      else
        return (size_t)0U;
    }
    else
      return (size_t)0U;
  }
}

static bool
CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded_hash_scratch_ok_impl(
  size_t map_depth_bound,
  size_t map_length_bound,
  size_t scratch_len,
  size_t hash_scratch_len
)
{
  return
    CBOR_Pulse_Raw_EverParse_DupCheck_Top_dupcheck_hash_scratch_ok(map_depth_bound,
      map_length_bound,
      scratch_len,
      hash_scratch_len);
}

static size_t
CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded_hash(
  size_t map_depth_bound,
  size_t map_length_bound,
  FStar_Pervasives_Native_option__size_t map_key_bound,
  uint64_t k0,
  uint64_t k1,
  CBOR_Pulse_Raw_Slice_byte_slice input,
  Pulse_Lib_Slice_slice__size_t scratch,
  Pulse_Lib_Slice_slice__uint64_t hash_scratch
)
{
  if
  (
    !CBOR_Pulse_Raw_EverParse_DupCheck_Top_dupcheck_hash_scratch_ok(map_depth_bound,
      map_length_bound,
      Pulse_Lib_Slice_len__size_t(scratch),
      Pulse_Lib_Slice_len__uint64_t(hash_scratch))
  )
    return (size_t)0U;
  else
  {
    size_t poff = (size_t)0U;
    if
    (
      CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_bounded(map_depth_bound,
        map_length_bound,
        input,
        &poff)
    )
    {
      size_t off = poff;
      if
      (
        CBOR_Pulse_Raw_EverParse_DupCheck_Top_check_dups_top_hash(input,
          map_length_bound,
          k0,
          k1,
          scratch,
          hash_scratch)
      )
        if
        (
          CBOR_Pulse_Raw_Format_Nondet_Validate_check_map_key_bound_after_validate(map_key_bound,
            input,
            off)
        )
          return off;
        else
          return (size_t)0U;
      else
        return (size_t)0U;
    }
    else
      return (size_t)0U;
  }
}

static cbor_raw CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot(cbor_raw c)
{
  return c;
}

static size_t
CBOR_Pulse_Raw_Nondet_cbor_nondet_validate(
  FStar_Pervasives_Native_option__size_t map_key_bound,
  bool strict_check,
  CBOR_Pulse_Raw_Slice_byte_slice input
)
{
  return
    CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet(map_key_bound,
      strict_check,
      input);
}

static cbor_raw
CBOR_Pulse_Raw_Nondet_cbor_nondet_parse_valid(
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t len
)
{
  return CBOR_Pulse_Raw_Format_Parse_cbor_parse(input, len);
}

static size_t
CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_map_length_bounded(
  size_t map_length_bound,
  FStar_Pervasives_Native_option__size_t map_key_bound,
  bool strict_check,
  CBOR_Pulse_Raw_Slice_byte_slice input
)
{
  return
    CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_map_length_bounded(map_length_bound,
      map_key_bound,
      strict_check,
      input);
}

static size_t
CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_bounded(
  size_t map_depth_bound,
  size_t map_length_bound,
  FStar_Pervasives_Native_option__size_t map_key_bound,
  CBOR_Pulse_Raw_Slice_byte_slice input
)
{
  return
    CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded(map_depth_bound,
      map_length_bound,
      map_key_bound,
      input);
}

static bool
CBOR_Pulse_Raw_Nondet_cbor_nondet_bounded_sort_scratch_ok_impl(
  size_t map_depth_bound,
  size_t map_length_bound,
  size_t scratch_len
)
{
  return
    CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded_sort_scratch_ok_impl(map_depth_bound,
      map_length_bound,
      scratch_len);
}

static size_t
CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_bounded_sort(
  size_t map_depth_bound,
  size_t map_length_bound,
  FStar_Pervasives_Native_option__size_t map_key_bound,
  Pulse_Lib_Slice_slice__size_t scratch,
  CBOR_Pulse_Raw_Slice_byte_slice input
)
{
  return
    CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded_sort(map_depth_bound,
      map_length_bound,
      map_key_bound,
      input,
      scratch);
}

static bool
CBOR_Pulse_Raw_Nondet_cbor_nondet_bounded_hash_scratch_ok_impl(
  size_t map_depth_bound,
  size_t map_length_bound,
  size_t scratch_len,
  size_t hash_scratch_len
)
{
  return
    CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded_hash_scratch_ok_impl(map_depth_bound,
      map_length_bound,
      scratch_len,
      hash_scratch_len);
}

static size_t
CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_bounded_hash(
  size_t map_depth_bound,
  size_t map_length_bound,
  FStar_Pervasives_Native_option__size_t map_key_bound,
  uint64_t k0,
  uint64_t k1,
  Pulse_Lib_Slice_slice__size_t scratch,
  Pulse_Lib_Slice_slice__uint64_t hash_scratch,
  CBOR_Pulse_Raw_Slice_byte_slice input
)
{
  return
    CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet_bounded_hash(map_depth_bound,
      map_length_bound,
      map_key_bound,
      k0,
      k1,
      input,
      scratch,
      hash_scratch);
}

static size_t CBOR_Pulse_Raw_Nondet_cbor_nondet_size(cbor_raw x, size_t bound)
{
  return CBOR_Pulse_Raw_Format_Serialize_cbor_size(x, bound);
}

static FStar_Pervasives_Native_option__size_t
CBOR_Pulse_Raw_Nondet_cbor_nondet_serialize(cbor_raw x, CBOR_Pulse_Raw_Slice_byte_slice output)
{
  size_t
  len = CBOR_Pulse_Raw_Format_Serialize_cbor_size(x, Pulse_Lib_Slice_len__uint8_t(output));
  if (len == (size_t)0U)
    return ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
  else
    return
      (
        (FStar_Pervasives_Native_option__size_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_Pulse_Raw_Format_Serialize_cbor_serialize(x,
            Pulse_Lib_Slice_split__uint8_t(output, len)._1)
        }
      );
}

static uint8_t CBOR_Pulse_Raw_Nondet_cbor_nondet_major_type(cbor_raw x)
{
  return CBOR_Pulse_Raw_Compare_impl_major_type(x);
}

static uint8_t CBOR_Pulse_Raw_Nondet_cbor_nondet_read_simple_value(cbor_raw x)
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

static uint64_t CBOR_Pulse_Raw_Nondet_cbor_nondet_read_uint64(cbor_raw x)
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

static uint64_t CBOR_Pulse_Raw_Nondet_cbor_nondet_get_string_length(cbor_raw x)
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

static CBOR_Pulse_Raw_Slice_byte_slice CBOR_Pulse_Raw_Nondet_cbor_nondet_get_string(cbor_raw x)
{
  if (x.tag == CBOR_Case_String)
    return x.case_CBOR_Case_String.cbor_string_ptr;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static uint64_t CBOR_Pulse_Raw_Nondet_cbor_nondet_get_tagged_tag(cbor_raw x)
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

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_get_tagged_payload(cbor_raw x)
{
  return CBOR_Pulse_Raw_Read_cbor_match_tagged_get_payload(x);
}

static uint64_t CBOR_Pulse_Raw_Nondet_cbor_nondet_get_array_length(cbor_raw x)
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

static cbor_nondet_array_iterator_t
CBOR_Pulse_Raw_Nondet_cbor_nondet_array_iterator_start(cbor_raw x)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_init(x);
}

static bool
CBOR_Pulse_Raw_Nondet_cbor_nondet_array_iterator_is_empty(cbor_nondet_array_iterator_t x)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_is_empty(x);
}

static cbor_raw
CBOR_Pulse_Raw_Nondet_cbor_nondet_array_iterator_next(cbor_nondet_array_iterator_t *x)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_next(x);
}

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_get_array_item(cbor_raw x, uint64_t i)
{
  return CBOR_Pulse_Raw_Read_cbor_array_item(x, i);
}

static uint64_t CBOR_Pulse_Raw_Nondet_cbor_nondet_get_map_length(cbor_raw x)
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

static cbor_nondet_map_iterator_t
CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_start(cbor_raw x)
{
  return CBOR_Pulse_Raw_Read_cbor_map_iterator_init(x);
}

static bool
CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_is_empty(cbor_nondet_map_iterator_t x)
{
  return CBOR_Pulse_Raw_Read_cbor_map_iterator_is_empty(x);
}

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_map_entry_key(cbor_map_entry x2)
{
  return x2.cbor_map_entry_key;
}

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_map_entry_value(cbor_map_entry x2)
{
  return x2.cbor_map_entry_value;
}

static cbor_map_entry
CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_next(cbor_nondet_map_iterator_t *x)
{
  return CBOR_Pulse_Raw_Read_cbor_map_iterator_next(x);
}

static bool CBOR_Pulse_Raw_Nondet_cbor_nondet_equal(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv(x1, x2);
}

typedef struct FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  cbor_raw v;
}
FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw;

static FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw
CBOR_Pulse_Raw_Nondet_cbor_nondet_map_get(cbor_raw x, cbor_raw k)
{
  cbor_raw dest = k;
  cbor_nondet_map_iterator_t i = CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_start(x);
  cbor_nondet_map_iterator_t pi = i;
  bool pres = false;
  bool pcont = !CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_is_empty(i);
  while (true)
  {
    bool res = pres;
    if (!(pcont && !res))
      break;
    cbor_map_entry y = CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_next(&pi);
    if (CBOR_Pulse_Raw_Nondet_cbor_nondet_equal(y.cbor_map_entry_key, k))
    {
      dest = y.cbor_map_entry_value;
      pres = true;
    }
    else
      pcont = !CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_is_empty(pi);
  }
  return
    pres ? (
           (FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw){
             .tag = FStar_Pervasives_Native_Some,
             .v = dest
           }
         )
         : (
           (FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw){
             .tag = FStar_Pervasives_Native_None
           }
         );
}

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_simple_value(uint8_t v)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = v } });
}

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_int64_gen(uint8_t ty, uint64_t v)
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

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_uint64(uint64_t v)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_int64_gen(CBOR_MAJOR_TYPE_UINT64, v);
}

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_neg_int64(uint64_t v)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_int64_gen(CBOR_MAJOR_TYPE_NEG_INT64, v);
}

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_int64(int64_t v)
{
  if (v < 0LL)
    return
      CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_int64_gen(CBOR_MAJOR_TYPE_NEG_INT64,
        (uint64_t)(-1LL - v));
  else
    return CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_int64_gen(CBOR_MAJOR_TYPE_UINT64, (uint64_t)v);
}

static cbor_raw
CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_string(uint8_t ty, CBOR_Pulse_Raw_Slice_byte_slice s)
{
  return
    CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot((
        (cbor_raw){
          .tag = CBOR_Case_String,
          {
            .case_CBOR_Case_String = {
              .cbor_string_type = ty,
              .cbor_string_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__uint8_t(s)).size,
              .cbor_string_ptr = s
            }
          }
        }
      ));
}

static cbor_raw CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_tagged(uint64_t tag, cbor_raw *r)
{
  return
    CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot((
        (cbor_raw){
          .tag = CBOR_Case_Tagged,
          {
            .case_CBOR_Case_Tagged = {
              .cbor_tagged_tag = CBOR_Spec_Raw_Optimal_mk_raw_uint64(tag),
              .cbor_tagged_ptr = r
            }
          }
        }
      ));
}

static cbor_raw
CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_array(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw a
)
{
  return
    CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot((
        (cbor_raw){
          .tag = CBOR_Case_Array,
          {
            .case_CBOR_Case_Array = {
              .cbor_array_length_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_raw(a)).size,
              .cbor_array_ptr = a
            }
          }
        }
      ));
}

static cbor_map_entry CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  cbor_raw xk_ = CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot(xk);
  return
    (
      (cbor_map_entry){
        .cbor_map_entry_key = xk_,
        .cbor_map_entry_value = CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot(xv)
      }
    );
}

static FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw
CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_map(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a
)
{
  cbor_raw dest = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } };
  bool ite0;
  if
  (
    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(a) / (size_t)32768U / (size_t)32768U /
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
  else if (CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_no_setoid_repeats(a))
  {
    dest =
      CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot((
          (cbor_raw){
            .tag = CBOR_Case_Map,
            {
              .case_CBOR_Case_Map = {
                .cbor_map_length_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_Type_cbor_map_entry(a)).size,
                .cbor_map_ptr = a
              }
            }
          }
        ));
    ite = true;
  }
  else
    ite = false;
  if (ite)
    return
      (
        (FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = FStar_Pervasives_Native_Some,
          .v = dest
        }
      );
  else
    return
      (
        (FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = FStar_Pervasives_Native_None
        }
      );
}

extern size_t *cbor_nondet_malloc_size_t(uint64_t x0);

extern void cbor_nondet_free_size_t(size_t *x0);

extern uint64_t *cbor_nondet_malloc_uint64_t(uint64_t x0);

extern void cbor_nondet_free_uint64_t(uint64_t *x0);

static CBOR_Pulse_Raw_Slice_byte_slice
Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((CBOR_Pulse_Raw_Slice_byte_slice){ .elt = a, .len = alen });
}

bool
cbor_nondet_parse(
  bool check_map_key_bound,
  size_t map_key_bound,
  uint8_t **pinput,
  size_t *plen,
  cbor_raw *dest
)
{
  if (pinput == NULL || plen == NULL || dest == NULL)
    return false;
  else
  {
    uint8_t *input = *pinput;
    if (*pinput == NULL)
      return false;
    else
    {
      size_t len = *plen;
      CBOR_Pulse_Raw_Slice_byte_slice
      s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input, len);
      size_t
      consume =
        CBOR_Pulse_Raw_Nondet_cbor_nondet_validate(check_map_key_bound ? (
                                                                         (FStar_Pervasives_Native_option__size_t){
                                                                           .tag = FStar_Pervasives_Native_Some,
                                                                           .v = map_key_bound
                                                                         }
                                                                       )
                                                                       : (
                                                                         (FStar_Pervasives_Native_option__size_t){
                                                                           .tag = FStar_Pervasives_Native_None
                                                                         }
                                                                       ),
          check_map_key_bound,
          s);
      if (consume == (size_t)0U)
        return false;
      else
      {
        *pinput = input + consume;
        *plen = len - consume;
        *dest =
          CBOR_Pulse_Raw_Nondet_cbor_nondet_parse_valid(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input,
              consume),
            consume);
        return true;
      }
    }
  }
}

bool
cbor_nondet_parse_map_length_bounded(
  size_t map_length_bound,
  bool check_map_key_bound,
  size_t map_key_bound,
  uint8_t **pinput,
  size_t *plen,
  cbor_raw *dest
)
{
  if (pinput == NULL || plen == NULL || dest == NULL)
    return false;
  else
  {
    uint8_t *input = *pinput;
    if (*pinput == NULL)
      return false;
    else
    {
      size_t len = *plen;
      CBOR_Pulse_Raw_Slice_byte_slice
      s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input, len);
      size_t
      consume =
        CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_map_length_bounded(map_length_bound,
          check_map_key_bound ? (
                                (FStar_Pervasives_Native_option__size_t){
                                  .tag = FStar_Pervasives_Native_Some,
                                  .v = map_key_bound
                                }
                              )
                              : (
                                (FStar_Pervasives_Native_option__size_t){
                                  .tag = FStar_Pervasives_Native_None
                                }
                              ),
          check_map_key_bound,
          s);
      if (consume == (size_t)0U)
        return false;
      else
      {
        *pinput = input + consume;
        *plen = len - consume;
        *dest =
          CBOR_Pulse_Raw_Nondet_cbor_nondet_parse_valid(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input,
              consume),
            consume);
        return true;
      }
    }
  }
}

bool
cbor_nondet_parse_bounded(
  size_t map_depth_bound,
  size_t map_length_bound,
  bool check_map_key_bound,
  size_t map_key_bound,
  uint8_t **pinput,
  size_t *plen,
  cbor_raw *dest
)
{
  if (pinput == NULL || plen == NULL || dest == NULL)
    return false;
  else
  {
    uint8_t *input = *pinput;
    if (*pinput == NULL)
      return false;
    else
    {
      size_t len = *plen;
      CBOR_Pulse_Raw_Slice_byte_slice
      s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input, len);
      size_t
      consume =
        CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_bounded(map_depth_bound,
          map_length_bound,
          check_map_key_bound ? (
                                (FStar_Pervasives_Native_option__size_t){
                                  .tag = FStar_Pervasives_Native_Some,
                                  .v = map_key_bound
                                }
                              )
                              : (
                                (FStar_Pervasives_Native_option__size_t){
                                  .tag = FStar_Pervasives_Native_None
                                }
                              ),
          s);
      if (consume == (size_t)0U)
        return false;
      else
      {
        *pinput = input + consume;
        *plen = len - consume;
        *dest =
          CBOR_Pulse_Raw_Nondet_cbor_nondet_parse_valid(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input,
              consume),
            consume);
        return true;
      }
    }
  }
}

bool
cbor_nondet_bounded_sort_scratch_ok(
  size_t map_depth_bound,
  size_t map_length_bound,
  size_t scratch_len
)
{
  return
    CBOR_Pulse_Raw_Nondet_cbor_nondet_bounded_sort_scratch_ok_impl(map_depth_bound,
      map_length_bound,
      scratch_len);
}

static Pulse_Lib_Slice_slice__size_t
Pulse_Lib_Slice_arrayptr_to_slice_intro__size_t(size_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__size_t){ .elt = a, .len = alen });
}

bool
cbor_nondet_parse_bounded_sort(
  size_t map_depth_bound,
  size_t map_length_bound,
  bool check_map_key_bound,
  size_t map_key_bound,
  size_t *scratch,
  size_t scratch_len,
  uint8_t **pinput,
  size_t *plen,
  cbor_raw *dest
)
{
  if (pinput == NULL || plen == NULL || dest == NULL)
    return false;
  else
  {
    uint8_t *input = *pinput;
    if (*pinput == NULL)
      return false;
    else if (scratch == NULL)
      return false;
    else
    {
      size_t len = *plen;
      CBOR_Pulse_Raw_Slice_byte_slice
      s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input, len);
      Pulse_Lib_Slice_slice__size_t
      sc = Pulse_Lib_Slice_arrayptr_to_slice_intro__size_t(scratch, scratch_len);
      size_t
      consume =
        CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_bounded_sort(map_depth_bound,
          map_length_bound,
          check_map_key_bound ? (
                                (FStar_Pervasives_Native_option__size_t){
                                  .tag = FStar_Pervasives_Native_Some,
                                  .v = map_key_bound
                                }
                              )
                              : (
                                (FStar_Pervasives_Native_option__size_t){
                                  .tag = FStar_Pervasives_Native_None
                                }
                              ),
          sc,
          s);
      if (consume == (size_t)0U)
        return false;
      else
      {
        *pinput = input + consume;
        *plen = len - consume;
        *dest =
          CBOR_Pulse_Raw_Nondet_cbor_nondet_parse_valid(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input,
              consume),
            consume);
        return true;
      }
    }
  }
}

bool
cbor_nondet_bounded_hash_scratch_ok(
  size_t map_depth_bound,
  size_t map_length_bound,
  size_t scratch_len,
  size_t hash_scratch_len
)
{
  return
    CBOR_Pulse_Raw_Nondet_cbor_nondet_bounded_hash_scratch_ok_impl(map_depth_bound,
      map_length_bound,
      scratch_len,
      hash_scratch_len);
}

static Pulse_Lib_Slice_slice__uint64_t
Pulse_Lib_Slice_arrayptr_to_slice_intro__uint64_t(uint64_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint64_t){ .elt = a, .len = alen });
}

bool
cbor_nondet_parse_bounded_hash(
  size_t map_depth_bound,
  size_t map_length_bound,
  bool check_map_key_bound,
  size_t map_key_bound,
  uint64_t k0,
  uint64_t k1,
  size_t *scratch,
  size_t scratch_len,
  uint64_t *hash_scratch,
  size_t hash_scratch_len,
  uint8_t **pinput,
  size_t *plen,
  cbor_raw *dest
)
{
  if (pinput == NULL || plen == NULL || dest == NULL)
    return false;
  else
  {
    uint8_t *input = *pinput;
    if (*pinput == NULL)
      return false;
    else
    {
      bool __anf1 = scratch == NULL;
      bool __anf02 = hash_scratch == NULL;
      if (__anf1 || __anf02)
        return false;
      else
      {
        size_t len = *plen;
        CBOR_Pulse_Raw_Slice_byte_slice
        s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input, len);
        Pulse_Lib_Slice_slice__size_t
        sc = Pulse_Lib_Slice_arrayptr_to_slice_intro__size_t(scratch, scratch_len);
        Pulse_Lib_Slice_slice__uint64_t
        hsc = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint64_t(hash_scratch, hash_scratch_len);
        size_t
        consume =
          CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_bounded_hash(map_depth_bound,
            map_length_bound,
            check_map_key_bound ? (
                                  (FStar_Pervasives_Native_option__size_t){
                                    .tag = FStar_Pervasives_Native_Some,
                                    .v = map_key_bound
                                  }
                                )
                                : (
                                  (FStar_Pervasives_Native_option__size_t){
                                    .tag = FStar_Pervasives_Native_None
                                  }
                                ),
            k0,
            k1,
            sc,
            hsc,
            s);
        if (consume == (size_t)0U)
          return false;
        else
        {
          *pinput = input + consume;
          *plen = len - consume;
          *dest =
            CBOR_Pulse_Raw_Nondet_cbor_nondet_parse_valid(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input,
                consume),
              consume);
          return true;
        }
      }
    }
  }
}

typedef struct FStar_Pervasives_Native_option__uint64_t_s
{
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  uint64_t v;
}
FStar_Pervasives_Native_option__uint64_t;

bool
cbor_nondet_parse_bounded_sort_alloc(
  size_t map_depth_bound,
  size_t map_length_bound,
  bool check_map_key_bound,
  size_t map_key_bound,
  uint8_t **pinput,
  size_t *plen,
  cbor_raw *dest
)
{
  if (pinput == NULL || plen == NULL || dest == NULL)
    return false;
  else
  {
    uint8_t *input = *pinput;
    if (*pinput == NULL)
      return false;
    else
    {
      size_t len = *plen;
      CBOR_Pulse_Raw_Slice_byte_slice
      s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input, len);
      FStar_Pervasives_Native_option__uint64_t
      od =
        map_depth_bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U <
          (size_t)16U ? (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = (uint64_t)map_depth_bound
                        }
                      )
                      : (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_None
                        }
                      );
      FStar_Pervasives_Native_option__uint64_t
      on =
        map_length_bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U <
          (size_t)16U ? (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = (uint64_t)map_length_bound
                        }
                      )
                      : (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_None
                        }
                      );
      FStar_Pervasives_Native_option__uint64_t scrut;
      if (od.tag == FStar_Pervasives_Native_None)
        scrut = ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
      else if (od.tag == FStar_Pervasives_Native_Some)
      {
        uint64_t d = od.v;
        if (on.tag == FStar_Pervasives_Native_None)
          scrut =
            ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
        else if (on.tag == FStar_Pervasives_Native_Some)
        {
          uint64_t n = on.v;
          if (d > 0x5555555555555554ULL)
            scrut =
              ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
          else
          {
            uint64_t k = 3ULL * d;
            scrut =
              k == 0ULL ? (
                          (FStar_Pervasives_Native_option__uint64_t){
                            .tag = FStar_Pervasives_Native_Some,
                            .v = 0ULL
                          }
                        )
                        : n > 0xffffffffffffffffULL / k ? (
                                                          (FStar_Pervasives_Native_option__uint64_t){
                                                            .tag = FStar_Pervasives_Native_None
                                                          }
                                                        )
                                                        : (
                                                          (FStar_Pervasives_Native_option__uint64_t){
                                                            .tag = FStar_Pervasives_Native_Some,
                                                            .v = n * k
                                                          }
                                                        );
          }
        }
        else
          scrut =
            KRML_EABORT(FStar_Pervasives_Native_option__uint64_t,
              "unreachable (pattern matches are exhaustive in F*)");
      }
      else
        scrut =
          KRML_EABORT(FStar_Pervasives_Native_option__uint64_t,
            "unreachable (pattern matches are exhaustive in F*)");
      size_t consume;
      if (scrut.tag == FStar_Pervasives_Native_None)
        consume = (size_t)0U;
      else if (scrut.tag == FStar_Pervasives_Native_Some)
      {
        uint64_t c = scrut.v;
        size_t *p = cbor_nondet_malloc_size_t(c);
        if (p == NULL)
          consume = (size_t)0U;
        else
        {
          Pulse_Lib_Slice_slice__size_t
          sc = Pulse_Lib_Slice_arrayptr_to_slice_intro__size_t(p, (size_t)c);
          size_t
          res =
            CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_bounded_sort(map_depth_bound,
              map_length_bound,
              check_map_key_bound ? (
                                    (FStar_Pervasives_Native_option__size_t){
                                      .tag = FStar_Pervasives_Native_Some,
                                      .v = map_key_bound
                                    }
                                  )
                                  : (
                                    (FStar_Pervasives_Native_option__size_t){
                                      .tag = FStar_Pervasives_Native_None
                                    }
                                  ),
              sc,
              s);
          cbor_nondet_free_size_t(p);
          consume = res;
        }
      }
      else
        consume = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (consume == (size_t)0U)
        return false;
      else
      {
        *pinput = input + consume;
        *plen = len - consume;
        *dest =
          CBOR_Pulse_Raw_Nondet_cbor_nondet_parse_valid(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input,
              consume),
            consume);
        return true;
      }
    }
  }
}

bool
cbor_nondet_parse_bounded_hash_alloc(
  size_t map_depth_bound,
  size_t map_length_bound,
  bool check_map_key_bound,
  size_t map_key_bound,
  uint64_t k0,
  uint64_t k1,
  uint8_t **pinput,
  size_t *plen,
  cbor_raw *dest
)
{
  if (pinput == NULL || plen == NULL || dest == NULL)
    return false;
  else
  {
    uint8_t *input = *pinput;
    if (*pinput == NULL)
      return false;
    else
    {
      size_t len = *plen;
      CBOR_Pulse_Raw_Slice_byte_slice
      s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input, len);
      FStar_Pervasives_Native_option__uint64_t
      od =
        map_depth_bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U <
          (size_t)16U ? (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = (uint64_t)map_depth_bound
                        }
                      )
                      : (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_None
                        }
                      );
      FStar_Pervasives_Native_option__uint64_t
      on =
        map_length_bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U <
          (size_t)16U ? (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = (uint64_t)map_length_bound
                        }
                      )
                      : (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_None
                        }
                      );
      FStar_Pervasives_Native_option__uint64_t oc;
      if (od.tag == FStar_Pervasives_Native_None)
        oc = ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
      else if (od.tag == FStar_Pervasives_Native_Some)
      {
        uint64_t d = od.v;
        if (on.tag == FStar_Pervasives_Native_None)
          oc = ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
        else if (on.tag == FStar_Pervasives_Native_Some)
        {
          uint64_t n = on.v;
          if (d > 0x5555555555555554ULL)
            oc = ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
          else
          {
            uint64_t k = 3ULL * d + 1ULL;
            oc =
              k == 0ULL ? (
                          (FStar_Pervasives_Native_option__uint64_t){
                            .tag = FStar_Pervasives_Native_Some,
                            .v = 0ULL
                          }
                        )
                        : n > 0xffffffffffffffffULL / k ? (
                                                          (FStar_Pervasives_Native_option__uint64_t){
                                                            .tag = FStar_Pervasives_Native_None
                                                          }
                                                        )
                                                        : (
                                                          (FStar_Pervasives_Native_option__uint64_t){
                                                            .tag = FStar_Pervasives_Native_Some,
                                                            .v = n * k
                                                          }
                                                        );
          }
        }
        else
          oc =
            KRML_EABORT(FStar_Pervasives_Native_option__uint64_t,
              "unreachable (pattern matches are exhaustive in F*)");
      }
      else
        oc =
          KRML_EABORT(FStar_Pervasives_Native_option__uint64_t,
            "unreachable (pattern matches are exhaustive in F*)");
      FStar_Pervasives_Native_option__uint64_t
      ohc =
        map_length_bound / (size_t)32768U / (size_t)32768U / (size_t)32768U / (size_t)32768U <
          (size_t)16U ? (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = (uint64_t)map_length_bound
                        }
                      )
                      : (
                        (FStar_Pervasives_Native_option__uint64_t){
                          .tag = FStar_Pervasives_Native_None
                        }
                      );
      size_t consume;
      if (oc.tag == FStar_Pervasives_Native_None)
        consume = (size_t)0U;
      else if (oc.tag == FStar_Pervasives_Native_Some)
      {
        uint64_t c = oc.v;
        if (ohc.tag == FStar_Pervasives_Native_None)
          consume = (size_t)0U;
        else if (ohc.tag == FStar_Pervasives_Native_Some)
        {
          uint64_t hc = ohc.v;
          size_t *p = cbor_nondet_malloc_size_t(c);
          if (p == NULL)
            consume = (size_t)0U;
          else
          {
            uint64_t *hp = cbor_nondet_malloc_uint64_t(hc);
            if (hp == NULL)
            {
              cbor_nondet_free_size_t(p);
              consume = (size_t)0U;
            }
            else
            {
              Pulse_Lib_Slice_slice__size_t
              sc = Pulse_Lib_Slice_arrayptr_to_slice_intro__size_t(p, (size_t)c);
              Pulse_Lib_Slice_slice__uint64_t
              hsc = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint64_t(hp, (size_t)hc);
              size_t
              res =
                CBOR_Pulse_Raw_Nondet_cbor_nondet_validate_bounded_hash(map_depth_bound,
                  map_length_bound,
                  check_map_key_bound ? (
                                        (FStar_Pervasives_Native_option__size_t){
                                          .tag = FStar_Pervasives_Native_Some,
                                          .v = map_key_bound
                                        }
                                      )
                                      : (
                                        (FStar_Pervasives_Native_option__size_t){
                                          .tag = FStar_Pervasives_Native_None
                                        }
                                      ),
                  k0,
                  k1,
                  sc,
                  hsc,
                  s);
              cbor_nondet_free_uint64_t(hp);
              cbor_nondet_free_size_t(p);
              consume = res;
            }
          }
        }
        else
          consume = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      }
      else
        consume = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
      if (consume == (size_t)0U)
        return false;
      else
      {
        *pinput = input + consume;
        *plen = len - consume;
        *dest =
          CBOR_Pulse_Raw_Nondet_cbor_nondet_parse_valid(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input,
              consume),
            consume);
        return true;
      }
    }
  }
}

size_t cbor_nondet_size(cbor_raw x, size_t bound)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_size(x, bound);
}

size_t cbor_nondet_serialize(cbor_raw x, uint8_t *output, size_t len)
{
  if (output == NULL)
    return (size_t)0U;
  else
  {
    FStar_Pervasives_Native_option__size_t
    scrut =
      CBOR_Pulse_Raw_Nondet_cbor_nondet_serialize(x,
        Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(output, len));
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
}

uint8_t cbor_nondet_major_type(cbor_raw x)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_major_type(x);
}

bool cbor_nondet_read_simple_value(cbor_raw x, uint8_t *dest)
{
  if (dest == NULL)
    return false;
  else if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_read_simple_value(x);
    return true;
  }
}

bool cbor_nondet_read_uint64(cbor_raw x, uint64_t *dest)
{
  if (dest == NULL)
    return false;
  else
  {
    uint8_t ty = cbor_nondet_major_type(x);
    if (ty != CBOR_MAJOR_TYPE_UINT64 && ty != CBOR_MAJOR_TYPE_NEG_INT64)
      return false;
    else
    {
      *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_read_uint64(x);
      return true;
    }
  }
}

bool cbor_nondet_read_int64(cbor_raw x, int64_t *dest)
{
  if (dest == NULL)
    return false;
  else
  {
    uint8_t ty = cbor_nondet_major_type(x);
    if (ty == CBOR_MAJOR_TYPE_UINT64)
    {
      uint64_t raw = CBOR_Pulse_Raw_Nondet_cbor_nondet_read_uint64(x);
      if (raw > 9223372036854775807ULL)
        return false;
      else
      {
        *dest = (int64_t)raw;
        return true;
      }
    }
    else if (ty == CBOR_MAJOR_TYPE_NEG_INT64)
    {
      uint64_t raw = CBOR_Pulse_Raw_Nondet_cbor_nondet_read_uint64(x);
      if (raw > 9223372036854775807ULL)
        return false;
      else
      {
        *dest = -1LL - (int64_t)raw;
        return true;
      }
    }
    else
      return false;
  }
}

static uint8_t
*Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(CBOR_Pulse_Raw_Slice_byte_slice s)
{
  return s.elt;
}

bool cbor_nondet_get_string(cbor_raw x, uint8_t **dest, uint64_t *dlen)
{
  if (dest == NULL || dlen == NULL)
    return false;
  else
  {
    uint8_t ty = cbor_nondet_major_type(x);
    if (ty != CBOR_MAJOR_TYPE_BYTE_STRING && ty != CBOR_MAJOR_TYPE_TEXT_STRING)
      return false;
    else
    {
      uint64_t len = CBOR_Pulse_Raw_Nondet_cbor_nondet_get_string_length(x);
      uint8_t
      *res =
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(CBOR_Pulse_Raw_Nondet_cbor_nondet_get_string(x));
      *dlen = len;
      *dest = res;
      return true;
    }
  }
}

bool cbor_nondet_get_byte_string(cbor_raw x, uint8_t **dest, uint64_t *dlen)
{
  if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_BYTE_STRING)
    return false;
  else
    return cbor_nondet_get_string(x, dest, dlen);
}

bool cbor_nondet_get_text_string(cbor_raw x, uint8_t **dest, uint64_t *dlen)
{
  if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_TEXT_STRING)
    return false;
  else
    return cbor_nondet_get_string(x, dest, dlen);
}

bool cbor_nondet_get_tagged(cbor_raw x, cbor_raw *dest, uint64_t *dtag)
{
  if (dest == NULL || dtag == NULL)
    return false;
  else if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_TAGGED)
    return false;
  else
  {
    uint64_t tag = CBOR_Pulse_Raw_Nondet_cbor_nondet_get_tagged_tag(x);
    cbor_raw res = CBOR_Pulse_Raw_Nondet_cbor_nondet_get_tagged_payload(x);
    *dtag = tag;
    *dest = res;
    return true;
  }
}

bool cbor_nondet_get_array_length(cbor_raw x, uint64_t *dest)
{
  if (dest == NULL)
    return false;
  else if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_ARRAY)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_get_array_length(x);
    return true;
  }
}

bool cbor_nondet_array_iterator_start(cbor_raw x, cbor_nondet_array_iterator_t *dest)
{
  if (dest == NULL)
    return false;
  else if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_ARRAY)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_array_iterator_start(x);
    return true;
  }
}

bool cbor_nondet_array_iterator_is_empty(cbor_nondet_array_iterator_t x)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_array_iterator_is_empty(x);
}

uint64_t cbor_nondet_array_iterator_length(cbor_nondet_array_iterator_t x)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_length(x);
}

bool cbor_nondet_array_iterator_next(cbor_nondet_array_iterator_t *x, cbor_raw *dest)
{
  if (x == NULL || dest == NULL)
    return false;
  else if (cbor_nondet_array_iterator_is_empty(*x))
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_array_iterator_next(x);
    return true;
  }
}

cbor_nondet_array_iterator_t
cbor_nondet_array_iterator_truncate(cbor_nondet_array_iterator_t x, uint64_t len)
{
  return CBOR_Pulse_Raw_Read_cbor_array_iterator_truncate(x, len);
}

bool cbor_nondet_get_array_item(cbor_raw x, uint64_t i, cbor_raw *dest)
{
  if (dest == NULL)
    return false;
  else if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_ARRAY)
    return false;
  else if (CBOR_Pulse_Raw_Nondet_cbor_nondet_get_array_length(x) <= i)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_get_array_item(x, i);
    return true;
  }
}

bool cbor_nondet_get_map_length(cbor_raw x, uint64_t *dest)
{
  if (dest == NULL)
    return false;
  else if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_MAP)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_get_map_length(x);
    return true;
  }
}

bool cbor_nondet_map_iterator_start(cbor_raw x, cbor_nondet_map_iterator_t *dest)
{
  if (dest == NULL)
    return false;
  else if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_MAP)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_start(x);
    return true;
  }
}

bool cbor_nondet_map_iterator_is_empty(cbor_nondet_map_iterator_t x)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_is_empty(x);
}

cbor_raw cbor_nondet_map_entry_key(cbor_map_entry x)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_map_entry_key(x);
}

cbor_raw cbor_nondet_map_entry_value(cbor_map_entry x)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_map_entry_value(x);
}

bool
cbor_nondet_map_iterator_next(
  cbor_nondet_map_iterator_t *x,
  cbor_raw *dest_key,
  cbor_raw *dest_value
)
{
  if (x == NULL || dest_key == NULL || dest_value == NULL)
    return false;
  else if (cbor_nondet_map_iterator_is_empty(*x))
    return false;
  else
  {
    cbor_map_entry res = CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_next(x);
    cbor_raw res_key = cbor_nondet_map_entry_key(res);
    cbor_raw res_value = cbor_nondet_map_entry_value(res);
    *dest_key = res_key;
    *dest_value = res_value;
    return true;
  }
}

bool cbor_nondet_equal(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_equal(x1, x2);
}

bool cbor_nondet_map_get(cbor_raw x, cbor_raw k, cbor_raw *dest)
{
  if (dest == NULL)
    return false;
  else if (cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_MAP)
    return false;
  else
  {
    FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw
    scrut = CBOR_Pulse_Raw_Nondet_cbor_nondet_map_get(x, k);
    if (scrut.tag == FStar_Pervasives_Native_None)
      return false;
    else if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      *dest = scrut.v;
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
}

bool cbor_nondet_mk_simple_value(uint8_t v, cbor_raw *dest)
{
  if
  (
    dest == NULL || !(v <= MAX_SIMPLE_VALUE_ADDITIONAL_INFO || MIN_SIMPLE_VALUE_LONG_ARGUMENT <= v)
  )
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_simple_value(v);
    return true;
  }
}

cbor_raw cbor_nondet_mk_uint64(uint64_t v)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_uint64(v);
}

cbor_raw cbor_nondet_mk_neg_int64(uint64_t v)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_neg_int64(v);
}

cbor_raw cbor_nondet_mk_int64(int64_t v)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_int64(v);
}

bool cbor_nondet_mk_byte_string(uint8_t *a, uint64_t len, cbor_raw *dest)
{
  if (a == NULL || dest == NULL)
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
      *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_string(CBOR_MAJOR_TYPE_BYTE_STRING, s);
      return true;
    }
    else
      return false;
  }
}

bool cbor_nondet_mk_text_string(uint8_t *a, uint64_t len, cbor_raw *dest)
{
  if (a == NULL || dest == NULL)
    return false;
  else
  {
    CBOR_Pulse_Raw_Slice_byte_slice
    s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
    if (CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(s))
    {
      *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, s);
      return true;
    }
    else
      return false;
  }
}

bool cbor_nondet_mk_tagged(uint64_t tag, cbor_raw *r, cbor_raw *dest)
{
  if (r == NULL || dest == NULL)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_tagged(tag, r);
    return true;
  }
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_Raw_Type_cbor_raw(cbor_raw *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw){ .elt = a, .len = alen });
}

bool cbor_nondet_mk_array(cbor_raw *a, uint64_t len, cbor_raw *dest)
{
  if (a == NULL || dest == NULL)
    return false;
  else
  {
    *dest =
      CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_array(Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_Raw_Type_cbor_raw(a,
          (size_t)len));
    return true;
  }
}

cbor_map_entry cbor_nondet_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  return CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_map_entry(xk, xv);
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_Raw_Type_cbor_map_entry(
  cbor_map_entry *a,
  size_t alen
)
{
  return ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry){ .elt = a, .len = alen });
}

bool cbor_nondet_mk_map(cbor_map_entry *a, uint64_t len, cbor_raw *dest)
{
  if (a == NULL || dest == NULL)
    return false;
  else
  {
    FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw
    scrut =
      CBOR_Pulse_Raw_Nondet_cbor_nondet_mk_map(Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_Raw_Type_cbor_map_entry(a,
          (size_t)len));
    if (scrut.tag == FStar_Pervasives_Native_None)
      return false;
    else if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      *dest = scrut.v;
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
}

typedef struct
Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t_s
{
  cbor_nondet_map_get_multiple_entry_t *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t;

static Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t
Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(
  cbor_nondet_map_get_multiple_entry_t *a,
  size_t alen
)
{
  return
    (
      (Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t){
        .elt = a,
        .len = alen
      }
    );
}

static size_t
Pulse_Lib_Slice_len__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t s
)
{
  return s.len;
}

static cbor_nondet_map_get_multiple_entry_t
Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t a,
  size_t i
)
{
  return a.elt[i];
}

static void
Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t a,
  size_t i,
  cbor_nondet_map_get_multiple_entry_t v
)
{
  a.elt[i] = v;
}

bool
cbor_nondet_map_get_multiple(
  cbor_raw map,
  cbor_nondet_map_get_multiple_entry_t *dest,
  size_t len
)
{
  if (dest == NULL)
    return false;
  else if (cbor_nondet_major_type(map) != CBOR_MAJOR_TYPE_MAP)
    return false;
  else
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t
    dests =
      Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(dest,
        len);
    size_t pi = (size_t)0U;
    while (true)
    {
      size_t i = pi;
      if
      (
        !(i <
          Pulse_Lib_Slice_len__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(dests))
      )
        break;
      size_t i0 = pi;
      cbor_nondet_map_get_multiple_entry_t
      x =
        Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(dests,
          i0);
      Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(dests,
        i0,
        ((cbor_nondet_map_get_multiple_entry_t){ .key = x.key, .value = x.value, .found = false }));
      pi = i0 + (size_t)1U;
    }
    cbor_nondet_map_iterator_t piter = CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_start(map);
    while (true)
    {
      size_t i0 = pi;
      bool __anf02 = CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_is_empty(piter);
      if (!(i0 != (size_t)0U && !__anf02))
        break;
      cbor_map_entry entry = CBOR_Pulse_Raw_Nondet_cbor_nondet_map_iterator_next(&piter);
      size_t pj = (size_t)0U;
      while (true)
      {
        size_t j = pj;
        size_t i = pi;
        if
        (
          !(j <
            Pulse_Lib_Slice_len__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(dests)
          && i > (size_t)0U)
        )
          break;
        size_t j0 = pj;
        pj = j0 + (size_t)1U;
        cbor_nondet_map_get_multiple_entry_t
        dest_entry =
          Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(dests,
            j0);
        if (CBOR_Pulse_Raw_Nondet_cbor_nondet_equal(dest_entry.key, entry.cbor_map_entry_key))
        {
          Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_Type_cbor_raw(dests,
            j0,
            (
              (cbor_nondet_map_get_multiple_entry_t){
                .key = dest_entry.key,
                .value = CBOR_Pulse_Raw_Match_cbor_raw_reset_perm_tot(entry.cbor_map_entry_value),
                .found = true
              }
            ));
          if (!dest_entry.found)
            pi--;
        }
      }
    }
    return true;
  }
}


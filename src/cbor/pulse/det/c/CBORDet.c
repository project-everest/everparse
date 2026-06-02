

#include "internal/CBORDet.h"

#include "CBORDetType.h"

static uint8_t LowParse_BitFields_get_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi)
{
  return ((uint32_t)x << (8U - hi) & 0xFFU) >> (8U - hi + lo);
}

static uint8_t
LowParse_BitFields_set_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi, uint8_t v)
{
  return ((uint32_t)x & (uint32_t)~(255U >> (8U - (hi - lo)) << lo)) | (uint32_t)v << lo;
}

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS (24U)

#define CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_UNASSIGNED_MIN (28U)

typedef struct CBOR_Spec_Raw_EverParse_initial_byte_t_s
{
  uint8_t major_type;
  uint8_t additional_info;
}
CBOR_Spec_Raw_EverParse_initial_byte_t;

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

typedef struct CBOR_Spec_Raw_EverParse_header_s
{
  CBOR_Spec_Raw_EverParse_initial_byte_t fst;
  CBOR_Spec_Raw_EverParse_long_argument snd;
}
CBOR_Spec_Raw_EverParse_header;

static uint64_t
CBOR_Spec_Raw_EverParse_argument_as_uint64(
  CBOR_Spec_Raw_EverParse_initial_byte_t b,
  CBOR_Spec_Raw_EverParse_long_argument x
)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)x.case_LongArgumentU8 });
  else if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
    ite =
      ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)x.case_LongArgumentU16 });
  else if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
    ite =
      ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)x.case_LongArgumentU32 });
  else if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = x.case_LongArgumentU64 });
  else if (x.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

static CBOR_Spec_Raw_EverParse_header
CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(uint8_t t, CBOR_Spec_Raw_Base_raw_uint64 x)
{
  if (x.size == 0U)
    return
      (
        (CBOR_Spec_Raw_EverParse_header){
          .fst = { .major_type = t, .additional_info = (uint8_t)x.value },
          .snd = { .tag = CBOR_Spec_Raw_EverParse_LongArgumentOther }
        }
      );
  else if (x.size == 1U)
    return
      (
        (CBOR_Spec_Raw_EverParse_header){
          .fst = {
            .major_type = t,
            .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS
          },
          .snd = {
            .tag = CBOR_Spec_Raw_EverParse_LongArgumentU8,
            { .case_LongArgumentU8 = (uint8_t)x.value }
          }
        }
      );
  else if (x.size == 2U)
    return
      (
        (CBOR_Spec_Raw_EverParse_header){
          .fst = {
            .major_type = t,
            .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS
          },
          .snd = {
            .tag = CBOR_Spec_Raw_EverParse_LongArgumentU16,
            { .case_LongArgumentU16 = (uint16_t)x.value }
          }
        }
      );
  else if (x.size == 3U)
    return
      (
        (CBOR_Spec_Raw_EverParse_header){
          .fst = {
            .major_type = t,
            .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS
          },
          .snd = {
            .tag = CBOR_Spec_Raw_EverParse_LongArgumentU32,
            { .case_LongArgumentU32 = (uint32_t)x.value }
          }
        }
      );
  else
    return
      (
        (CBOR_Spec_Raw_EverParse_header){
          .fst = {
            .major_type = t,
            .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS
          },
          .snd = {
            .tag = CBOR_Spec_Raw_EverParse_LongArgumentU64,
            { .case_LongArgumentU64 = x.value }
          }
        }
      );
}

static CBOR_Spec_Raw_EverParse_header
CBOR_Spec_Raw_EverParse_simple_value_as_argument(uint8_t x)
{
  if (x <= MAX_SIMPLE_VALUE_ADDITIONAL_INFO)
    return
      (
        (CBOR_Spec_Raw_EverParse_header){
          .fst = { .major_type = CBOR_MAJOR_TYPE_SIMPLE_VALUE, .additional_info = x },
          .snd = { .tag = CBOR_Spec_Raw_EverParse_LongArgumentOther }
        }
      );
  else
    return
      (
        (CBOR_Spec_Raw_EverParse_header){
          .fst = {
            .major_type = CBOR_MAJOR_TYPE_SIMPLE_VALUE,
            .additional_info = CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS
          },
          .snd = {
            .tag = CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue,
            { .case_LongArgumentSimpleValue = x }
          }
        }
      );
}

static uint8_t CBOR_Spec_Raw_EverParse_get_header_major_type(CBOR_Spec_Raw_EverParse_header h)
{
  return h.fst.major_type;
}

static CBOR_Spec_Raw_Base_raw_uint64 CBOR_Spec_Raw_Optimal_mk_raw_uint64(uint64_t x)
{
  uint8_t ite;
  if (x <= (uint64_t)MAX_SIMPLE_VALUE_ADDITIONAL_INFO)
    ite = 0U;
  else if (x < 256ULL)
    ite = 1U;
  else if (x < 65536ULL)
    ite = 2U;
  else if (x < 4294967296ULL)
    ite = 3U;
  else
    ite = 4U;
  return ((CBOR_Spec_Raw_Base_raw_uint64){ .size = ite, .value = x });
}

static int16_t CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(uint8_t x1, uint8_t x2)
{
  if (x1 < x2)
    return (int16_t)-1;
  else if (x1 > x2)
    return (int16_t)1;
  else
    return (int16_t)0;
}

static size_t Pulse_Lib_Slice_len__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.len;
}

static uint8_t
Pulse_Lib_Slice_op_Array_Access__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i)
{
  return a.elt[i];
}

static int16_t
CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(
  Pulse_Lib_Slice_slice__uint8_t s1,
  Pulse_Lib_Slice_slice__uint8_t s2
)
{
  Pulse_Lib_Slice_slice__uint8_t sp1 = s1;
  Pulse_Lib_Slice_slice__uint8_t sp2 = s2;
  size_t pi1 = (size_t)0U;
  size_t pi2 = (size_t)0U;
  size_t n1 = Pulse_Lib_Slice_len__uint8_t(sp1);
  size_t n2 = Pulse_Lib_Slice_len__uint8_t(sp2);
  int16_t ite;
  if ((size_t)0U < n1)
    if ((size_t)0U < n2)
      ite = (int16_t)0;
    else
      ite = (int16_t)1;
  else if ((size_t)0U < n2)
    ite = (int16_t)-1;
  else
    ite = (int16_t)0;
  int16_t pres = ite;
  while (pres == (int16_t)0 && pi1 < n1)
  {
    size_t i1 = pi1;
    uint8_t x1 = Pulse_Lib_Slice_op_Array_Access__uint8_t(sp1, i1);
    size_t i2 = pi2;
    int16_t
    c =
      CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(x1,
        Pulse_Lib_Slice_op_Array_Access__uint8_t(sp2, i2));
    if (c == (int16_t)0)
    {
      size_t i1_ = i1 + (size_t)1U;
      size_t i2_ = i2 + (size_t)1U;
      bool ci1_ = i1_ < n1;
      bool ci2_ = i2_ < n2;
      if (ci2_ && !ci1_)
        pres = (int16_t)-1;
      else if (ci1_ && !ci2_)
        pres = (int16_t)1;
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

static size_t LowParse_PulseParse_Iterator_append_n_before_sz(size_t off, size_t n, size_t cb)
{
  if (off >= cb)
    return (size_t)0U;
  else
  {
    size_t diff = cb - off;
    if (n <= diff)
      return n;
    else
      return diff;
  }
}

static size_t LowParse_PulseParse_Iterator_append_n_after_sz(size_t off, size_t n, size_t cb)
{
  return n - LowParse_PulseParse_Iterator_append_n_before_sz(off, n, cb);
}

static size_t
LowParse_PulseParse_Iterator_append_off_before_sz(size_t off, size_t ob, size_t cb)
{
  size_t ite;
  if (off >= cb)
    ite = cb;
  else
    ite = off;
  return ob + ite;
}

static size_t
LowParse_PulseParse_Iterator_append_off_after_sz(size_t off, size_t oa, size_t cb)
{
  size_t ite;
  if (off >= cb)
    ite = off - cb;
  else
    ite = (size_t)0U;
  return oa + ite;
}

static bool CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(Pulse_Lib_Slice_slice__uint8_t s)
{
  bool pres = true;
  size_t pi = (size_t)0U;
  size_t len = Pulse_Lib_Slice_len__uint8_t(s);
  while (pres && pi < len)
  {
    size_t i = pi;
    uint8_t byte1 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s, i);
    size_t i1 = i + (size_t)1U;
    if (byte1 <= 0x7FU)
      pi = i1;
    else if (i1 == len)
      pres = false;
    else
    {
      uint8_t byte2 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s, i1);
      size_t i2 = i1 + (size_t)1U;
      if (0xC2U <= byte1 && byte1 <= 0xDFU && 0x80U <= byte2 && byte2 <= 0xBFU)
        pi = i2;
      else if (i2 == len)
        pres = false;
      else
      {
        uint8_t byte3 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s, i2);
        size_t i3 = i2 + (size_t)1U;
        if (!(0x80U <= byte3 && byte3 <= 0xBFU))
          pres = false;
        else if (byte1 == 0xE0U)
          if (0xA0U <= byte2 && byte2 <= 0xBFU)
            pi = i3;
          else
            pres = false;
        else if (byte1 == 0xEDU)
          if (0x80U <= byte2 && byte2 <= 0x9FU)
            pi = i3;
          else
            pres = false;
        else if (0xE1U <= byte1 && byte1 <= 0xEFU && 0x80U <= byte2 && byte2 <= 0xBFU)
          pi = i3;
        else if (i3 == len)
          pres = false;
        else
        {
          uint8_t byte4 = Pulse_Lib_Slice_op_Array_Access__uint8_t(s, i3);
          size_t i4 = i3 + (size_t)1U;
          if (!(0x80U <= byte4 && byte4 <= 0xBFU))
            pres = false;
          else if (byte1 == 0xF0U && 0x90U <= byte2 && byte2 <= 0xBFU)
            pi = i4;
          else if (0xF1U <= byte1 && byte1 <= 0xF3U && 0x80U <= byte2 && byte2 <= 0xBFU)
            pi = i4;
          else if (byte1 == 0xF4U && 0x80U <= byte2 && byte2 <= 0x8FU)
            pi = i4;
          else
            pres = false;
        }
      }
    }
  }
  return pres;
}

static CBOR_Spec_Raw_EverParse_initial_byte_t
CBOR_Pulse_Raw_EverParse_Validate_read_initial_byte_t(Pulse_Lib_Slice_slice__uint8_t input)
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

typedef struct K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t_s
{
  Pulse_Lib_Slice_slice__uint8_t fst;
  Pulse_Lib_Slice_slice__uint8_t snd;
}
K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t;

static K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_slice__uint8_t s, size_t i)
{
  return
    (
      (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static CBOR_Spec_Raw_EverParse_header
CBOR_Pulse_Raw_EverParse_Validate_read_header(Pulse_Lib_Slice_slice__uint8_t input)
{
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut = Pulse_Lib_Slice_split__uint8_t(input, (size_t)1U);
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.snd;
  CBOR_Spec_Raw_EverParse_initial_byte_t
  x1 = CBOR_Pulse_Raw_EverParse_Validate_read_initial_byte_t(scrut1.fst);
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
            .case_LongArgumentU16 = (uint32_t)(uint16_t)last +
              (uint32_t)(uint16_t)Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)0U) *
                256U
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
            .case_LongArgumentU64 = (uint64_t)last +
              ((uint64_t)last1 +
                ((uint64_t)last2 +
                  ((uint64_t)last3 +
                    ((uint64_t)last4 +
                      ((uint64_t)last5 +
                        ((uint64_t)last6 +
                          (uint64_t)Pulse_Lib_Slice_op_Array_Access__uint8_t(input2, (size_t)0U) *
                            256ULL)
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
  return ((CBOR_Spec_Raw_EverParse_header){ .fst = x1, .snd = ite });
}

static bool
CBOR_Pulse_Raw_EverParse_Validate_validate_header(
  Pulse_Lib_Slice_slice__uint8_t input,
  size_t *poffset
)
{
  size_t offset1 = *poffset;
  size_t offset2 = *poffset;
  size_t offset30 = *poffset;
  bool ite0;
  if (Pulse_Lib_Slice_len__uint8_t(input) - offset30 < (size_t)1U)
    ite0 = false;
  else
  {
    *poffset = offset30 + (size_t)1U;
    ite0 = true;
  }
  bool ite1;
  if (ite0)
  {
    size_t off = *poffset;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = Pulse_Lib_Slice_split__uint8_t(input, offset2);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 =
      Pulse_Lib_Slice_split__uint8_t((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut.fst,
            .snd = scrut.snd
          }
        ).snd,
        off - offset2);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
    CBOR_Spec_Raw_EverParse_initial_byte_t
    x =
      CBOR_Pulse_Raw_EverParse_Validate_read_initial_byte_t((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut1.fst,
            .snd = scrut1.snd
          }
        ).fst);
    bool ite;
    if (x.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      ite = x.additional_info <= CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS;
    else
      ite = true;
    ite1 = ite && x.additional_info < CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_UNASSIGNED_MIN;
  }
  else
    ite1 = false;
  if (ite1)
  {
    size_t off = *poffset;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = Pulse_Lib_Slice_split__uint8_t(input, offset1);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 =
      Pulse_Lib_Slice_split__uint8_t((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).snd,
        off - offset1);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    CBOR_Spec_Raw_EverParse_initial_byte_t
    x =
      CBOR_Pulse_Raw_EverParse_Validate_read_initial_byte_t((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut2.fst,
            .snd = scrut2.snd
          }
        ).fst);
    if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
      if (x.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      {
        size_t offset2 = *poffset;
        size_t offset3 = *poffset;
        bool ite;
        if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < (size_t)1U)
          ite = false;
        else
        {
          *poffset = offset3 + (size_t)1U;
          ite = true;
        }
        if (ite)
        {
          size_t off1 = *poffset;
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut = Pulse_Lib_Slice_split__uint8_t(input, offset2);
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut0 =
            Pulse_Lib_Slice_split__uint8_t((
                (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                  .fst = scrut.fst,
                  .snd = scrut.snd
                }
              ).snd,
              off1 - offset2);
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          return
            MIN_SIMPLE_VALUE_LONG_ARGUMENT <=
              Pulse_Lib_Slice_op_Array_Access__uint8_t((
                  (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                    .fst = scrut1.fst,
                    .snd = scrut1.snd
                  }
                ).fst,
                (size_t)0U);
        }
        else
          return false;
      }
      else
      {
        size_t offset2 = *poffset;
        if (Pulse_Lib_Slice_len__uint8_t(input) - offset2 < (size_t)1U)
          return false;
        else
        {
          *poffset = offset2 + (size_t)1U;
          return true;
        }
      }
    else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    {
      size_t offset2 = *poffset;
      if (Pulse_Lib_Slice_len__uint8_t(input) - offset2 < (size_t)2U)
        return false;
      else
      {
        *poffset = offset2 + (size_t)2U;
        return true;
      }
    }
    else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    {
      size_t offset2 = *poffset;
      if (Pulse_Lib_Slice_len__uint8_t(input) - offset2 < (size_t)4U)
        return false;
      else
      {
        *poffset = offset2 + (size_t)4U;
        return true;
      }
    }
    else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    {
      size_t offset2 = *poffset;
      if (Pulse_Lib_Slice_len__uint8_t(input) - offset2 < (size_t)8U)
        return false;
      else
      {
        *poffset = offset2 + (size_t)8U;
        return true;
      }
    }
    else
      return true;
  }
  else
    return false;
}

static size_t
CBOR_Pulse_Raw_EverParse_Validate_jump_header(
  Pulse_Lib_Slice_slice__uint8_t input,
  size_t offset
)
{
  size_t off1 = offset + (size_t)1U;
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut = Pulse_Lib_Slice_split__uint8_t(input, offset);
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 =
    Pulse_Lib_Slice_split__uint8_t((
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut.fst,
          .snd = scrut.snd
        }
      ).snd,
      off1 - offset);
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  CBOR_Spec_Raw_EverParse_initial_byte_t
  x =
    CBOR_Pulse_Raw_EverParse_Validate_read_initial_byte_t((
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut1.fst,
          .snd = scrut1.snd
        }
      ).fst);
  if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    return off1 + (size_t)1U;
  else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    return off1 + (size_t)2U;
  else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    return off1 + (size_t)4U;
  else if (x.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    return off1 + (size_t)8U;
  else
    return off1;
}

static bool
CBOR_Pulse_Raw_EverParse_Validate_validate_recursive_step_count_leaf(
  Pulse_Lib_Slice_slice__uint8_t a,
  size_t bound,
  size_t *prem
)
{
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut =
    Pulse_Lib_Slice_split__uint8_t(a,
      CBOR_Pulse_Raw_EverParse_Validate_jump_header(a, (size_t)0U));
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  CBOR_Spec_Raw_EverParse_header
  h =
    CBOR_Pulse_Raw_EverParse_Validate_read_header((
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut0.fst,
          .snd = scrut0.snd
        }
      ).fst);
  uint8_t typ = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
  if (typ == CBOR_MAJOR_TYPE_ARRAY)
  {
    *prem = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h.fst, h.snd);
    return false;
  }
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    size_t arg = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h.fst, h.snd);
    if (arg > bound)
      return true;
    else if (bound - arg < arg)
      return true;
    else
    {
      *prem = arg + arg;
      return false;
    }
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

static size_t
CBOR_Pulse_Raw_EverParse_Validate_impl_remaining_data_items_header(
  CBOR_Spec_Raw_EverParse_header h
)
{
  uint8_t typ = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
  if (typ == CBOR_MAJOR_TYPE_ARRAY)
    return (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h.fst, h.snd);
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    size_t arg = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h.fst, h.snd);
    return arg + arg;
  }
  else if (typ == CBOR_MAJOR_TYPE_TAGGED)
    return (size_t)1U;
  else
    return (size_t)0U;
}

static size_t
CBOR_Pulse_Raw_EverParse_Validate_jump_recursive_step_count_leaf(
  Pulse_Lib_Slice_slice__uint8_t a
)
{
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut =
    Pulse_Lib_Slice_split__uint8_t(a,
      CBOR_Pulse_Raw_EverParse_Validate_jump_header(a, (size_t)0U));
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  return
    CBOR_Pulse_Raw_EverParse_Validate_impl_remaining_data_items_header(CBOR_Pulse_Raw_EverParse_Validate_read_header((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).fst));
}

static bool
CBOR_Pulse_Raw_EverParse_Validate_validate_raw_data_item(
  Pulse_Lib_Slice_slice__uint8_t input,
  size_t *poffset
)
{
  size_t pn = (size_t)1U;
  bool pres = true;
  while (pres && pn > (size_t)0U)
  {
    size_t off = *poffset;
    size_t n = pn;
    if (n > Pulse_Lib_Slice_len__uint8_t(input) - off)
      pres = false;
    else
    {
      size_t offset1 = *poffset;
      bool ite0;
      if (CBOR_Pulse_Raw_EverParse_Validate_validate_header(input, poffset))
      {
        size_t off1 = *poffset;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 = Pulse_Lib_Slice_split__uint8_t(input, offset1);
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 =
          Pulse_Lib_Slice_split__uint8_t((
              (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                .fst = scrut0.fst,
                .snd = scrut0.snd
              }
            ).snd,
            off1 - offset1);
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        CBOR_Spec_Raw_EverParse_header
        x =
          CBOR_Pulse_Raw_EverParse_Validate_read_header((
              (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                .fst = scrut2.fst,
                .snd = scrut2.snd
              }
            ).fst);
        CBOR_Spec_Raw_EverParse_initial_byte_t b = x.fst;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        {
          size_t n1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x.fst, x.snd);
          size_t offset2 = *poffset;
          size_t offset3 = *poffset;
          bool ite;
          if (Pulse_Lib_Slice_len__uint8_t(input) - offset3 < n1)
            ite = false;
          else
          {
            *poffset = offset3 + n1;
            ite = true;
          }
          if (ite)
          {
            size_t off2 = *poffset;
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut = Pulse_Lib_Slice_split__uint8_t(input, offset2);
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 =
              Pulse_Lib_Slice_split__uint8_t((
                  (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                    .fst = scrut.fst,
                    .snd = scrut.snd
                  }
                ).snd,
                off2 - offset2);
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
            Pulse_Lib_Slice_slice__uint8_t
            x1 =
              (
                (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                  .fst = scrut1.fst,
                  .snd = scrut1.snd
                }
              ).fst;
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
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut = Pulse_Lib_Slice_split__uint8_t(input, off);
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 =
          Pulse_Lib_Slice_split__uint8_t((
              (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                .fst = scrut.fst,
                .snd = scrut.snd
              }
            ).snd,
            offset1 - off);
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        Pulse_Lib_Slice_slice__uint8_t
        input1 =
          (
            (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
              .fst = scrut1.fst,
              .snd = scrut1.snd
            }
          ).fst;
        size_t bound = Pulse_Lib_Slice_len__uint8_t(input) - off - n;
        bool
        res2 =
          CBOR_Pulse_Raw_EverParse_Validate_validate_recursive_step_count_leaf(input1,
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
CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(
  Pulse_Lib_Slice_slice__uint8_t input,
  size_t offset
)
{
  size_t poffset = offset;
  size_t pn = (size_t)1U;
  while (pn > (size_t)0U)
  {
    size_t off = poffset;
    size_t off10 = CBOR_Pulse_Raw_EverParse_Validate_jump_header(input, off);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = Pulse_Lib_Slice_split__uint8_t(input, off);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 =
      Pulse_Lib_Slice_split__uint8_t((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).snd,
        off10 - off);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    CBOR_Spec_Raw_EverParse_header
    x =
      CBOR_Pulse_Raw_EverParse_Validate_read_header((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut2.fst,
            .snd = scrut2.snd
          }
        ).fst);
    CBOR_Spec_Raw_EverParse_initial_byte_t b = x.fst;
    size_t off1;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
      off1 = off10 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x.fst, x.snd);
    else
      off1 = off10;
    poffset = off1;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = Pulse_Lib_Slice_split__uint8_t(input, off);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut3 =
      Pulse_Lib_Slice_split__uint8_t((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut.fst,
            .snd = scrut.snd
          }
        ).snd,
        off1 - off);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
    Pulse_Lib_Slice_slice__uint8_t
    input1 =
      (
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut4.fst,
          .snd = scrut4.snd
        }
      ).fst;
    size_t n = pn;
    size_t unused = Pulse_Lib_Slice_len__uint8_t(input) - off1;
    KRML_MAYBE_UNUSED_VAR(unused);
    pn = n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Validate_jump_recursive_step_count_leaf(input1);
  }
  return poffset;
}

static size_t
CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(
  Pulse_Lib_Slice_slice__uint8_t input,
  size_t offset
)
{
  return CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(input, offset);
}

static size_t
CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(
  Pulse_Lib_Slice_slice__uint8_t input,
  size_t offset
)
{
  return
    CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(input,
      CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(input, offset));
}

static CBOR_Spec_Raw_EverParse_initial_byte_t
Prims___proj__Mkdtuple2__item___1__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  CBOR_Spec_Raw_EverParse_header pair
)
{
  return pair.fst;
}

static CBOR_Spec_Raw_EverParse_initial_byte_t
FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  CBOR_Spec_Raw_EverParse_header t
)
{
  return
    Prims___proj__Mkdtuple2__item___1__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(t);
}

static CBOR_Spec_Raw_EverParse_long_argument
Prims___proj__Mkdtuple2__item___2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  CBOR_Spec_Raw_EverParse_header pair
)
{
  return pair.snd;
}

static CBOR_Spec_Raw_EverParse_long_argument
FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  CBOR_Spec_Raw_EverParse_header t
)
{
  return
    Prims___proj__Mkdtuple2__item___2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(t);
}

static cbor_raw
CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_match_aux(Pulse_Lib_Slice_slice__uint8_t input)
{
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 =
    Pulse_Lib_Slice_split__uint8_t(input,
      CBOR_Pulse_Raw_EverParse_Validate_jump_header(input, (size_t)0U));
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.snd;
  CBOR_Spec_Raw_EverParse_header v1 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut1.fst);
  CBOR_Spec_Raw_EverParse_initial_byte_t
  b =
    FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(v1);
  CBOR_Spec_Raw_EverParse_long_argument
  la =
    FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(v1);
  if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
  {
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut =
      Pulse_Lib_Slice_split__uint8_t(input2,
        (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(b, la));
    Pulse_Lib_Slice_slice__uint8_t
    input11 =
      (
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut.fst,
          .snd = scrut.snd
        }
      ).fst;
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
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
              .cbor_string_type = b.major_type,
              .cbor_string_size = ite.size,
              .cbor_string_ptr = input11
            }
          }
        }
      );
  }
  else if (b.major_type == CBOR_MAJOR_TYPE_ARRAY)
  {
    size_t n = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(b, la);
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Array,
          {
            .case_CBOR_Case_Array = {
              .cbor_array_length_size = ite.size,
              .cbor_array_ptr = {
                .tag = LowParse_PulseParse_Iterator_Type_Base,
                {
                  .case_Base = {
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    { .case_Serialized = { .count = n, .payload = input2 } }
                  }
                }
              }
            }
          }
        }
      );
  }
  else if (b.major_type == CBOR_MAJOR_TYPE_MAP)
  {
    size_t n = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(b, la);
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Map,
          {
            .case_CBOR_Case_Map = {
              .cbor_map_length_size = ite.size,
              .cbor_map_ptr = {
                .tag = LowParse_PulseParse_Iterator_Type_Base,
                {
                  .case_Base = {
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    { .case_Serialized = { .count = n, .payload = input2 } }
                  }
                }
              }
            }
          }
        }
      );
  }
  else if (b.major_type == CBOR_MAJOR_TYPE_TAGGED)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Tagged_Serialized,
          {
            .case_CBOR_Case_Tagged_Serialized = {
              .cbor_tagged_serialized_tag = ite,
              .cbor_tagged_serialized_ptr = input2
            }
          }
        }
      );
  }
  else if (b.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
  {
    uint8_t ite;
    if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite = b.additional_info;
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
      ite = la.case_LongArgumentSimpleValue;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = ite } });
  }
  else
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite0;
    if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite0 =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite0 =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite0 =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite0 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite0 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite0 =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Int,
          {
            .case_CBOR_Case_Int = {
              .cbor_int_type = b.major_type,
              .cbor_int_size = ite0.size,
              .cbor_int_value = ite.value
            }
          }
        }
      );
  }
}

static cbor_raw
CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read(Pulse_Lib_Slice_slice__uint8_t input)
{
  return CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_match_aux(input);
}

static cbor_raw
CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(Pulse_Lib_Slice_slice__uint8_t input)
{
  return CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_match_aux(input);
}

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__uint8_t_tags;

typedef struct FStar_Pervasives_Native_option__uint8_t_s
{
  FStar_Pervasives_Native_option__uint8_t_tags tag;
  uint8_t v;
}
FStar_Pervasives_Native_option__uint8_t;

static uint8_t CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_major_type_aux(cbor_raw x)
{
  FStar_Pervasives_Native_option__uint8_t scrut;
  if (x.tag == CBOR_Case_Int)
    scrut =
      (
        (FStar_Pervasives_Native_option__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = x.case_CBOR_Case_Int.cbor_int_type
        }
      );
  else if (x.tag == CBOR_Case_Simple)
    scrut =
      (
        (FStar_Pervasives_Native_option__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_MAJOR_TYPE_SIMPLE_VALUE
        }
      );
  else if (x.tag == CBOR_Case_String)
    scrut =
      (
        (FStar_Pervasives_Native_option__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = x.case_CBOR_Case_String.cbor_string_type
        }
      );
  else if (x.tag == CBOR_Case_Array)
    scrut =
      (
        (FStar_Pervasives_Native_option__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_MAJOR_TYPE_ARRAY
        }
      );
  else if (x.tag == CBOR_Case_Map)
    scrut =
      (
        (FStar_Pervasives_Native_option__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_MAJOR_TYPE_MAP
        }
      );
  else if (x.tag == CBOR_Case_Tagged)
    scrut =
      (
        (FStar_Pervasives_Native_option__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_MAJOR_TYPE_TAGGED
        }
      );
  else if (x.tag == CBOR_Case_Tagged_Serialized)
    scrut =
      (
        (FStar_Pervasives_Native_option__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_MAJOR_TYPE_TAGGED
        }
      );
  else if (x.tag == CBOR_Case_Invalid)
    scrut = ((FStar_Pervasives_Native_option__uint8_t){ .tag = FStar_Pervasives_Native_None });
  else
    scrut =
      KRML_EABORT(FStar_Pervasives_Native_option__uint8_t,
        "unreachable (pattern matches are exhaustive in F*)");
  if (scrut.tag == FStar_Pervasives_Native_Some)
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

static uint8_t CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_major_type(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_major_type_aux(x);
}

static Pulse_Lib_Slice_slice__uint8_t
CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string_aux(cbor_raw x)
{
  if (x.tag == CBOR_Case_String)
    return x.case_CBOR_Case_String.cbor_string_ptr;
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Array)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Map)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged_Serialized)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
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

static Pulse_Lib_Slice_slice__uint8_t
CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string_aux(x);
}

static cbor_raw CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_tagged_payload(cbor_raw x)
{
  if (x.tag == CBOR_Case_Tagged)
    return *x.case_CBOR_Case_Tagged.cbor_tagged_ptr;
  else if (x.tag == CBOR_Case_Tagged_Serialized)
    return
      CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read(x.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_ptr);
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_String)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Array)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Map)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
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

#define LowParse_PulseParse_Iterator_EElement 0
#define LowParse_PulseParse_Iterator_ESerialized 1

typedef uint8_t
LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags;

typedef struct
LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags
  tag;
  union {
    cbor_raw case_EElement;
    Pulse_Lib_Slice_slice__uint8_t case_ESerialized;
  }
  ;
}
LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_tagged_payload_aux_eos(cbor_raw x)
{
  if (x.tag == CBOR_Case_Tagged)
    return
      (
        (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_EElement,
          { .case_EElement = *x.case_CBOR_Case_Tagged.cbor_tagged_ptr }
        }
      );
  else if (x.tag == CBOR_Case_Tagged_Serialized)
    return
      (
        (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_ESerialized,
          { .case_ESerialized = x.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_ptr }
        }
      );
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_String)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Array)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Map)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
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

static LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array_aux(cbor_raw x)
{
  if (x.tag == CBOR_Case_Array)
    return x.case_CBOR_Case_Array.cbor_array_ptr;
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_String)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Map)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged_Serialized)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
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

static LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array_aux(x);
}

static LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map_aux(cbor_raw x)
{
  if (x.tag == CBOR_Case_Map)
    return x.case_CBOR_Case_Map.cbor_map_ptr;
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_String)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Array)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged_Serialized)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
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

static LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map_aux(x);
}

static size_t
Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw s
)
{
  return s.len;
}

static size_t
LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw i
)
{
  if (i.tag == LowParse_PulseParse_Iterator_Type_Empty)
    return (size_t)0U;
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Singleton)
    return (size_t)1U;
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Slice)
    return Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i.case_Slice);
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Serialized)
    return i.case_Serialized.count;
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
LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw i
)
{
  if (i.tag == LowParse_PulseParse_Iterator_Type_Base)
    return
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i.case_Base);
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Append)
    return i.case_Append.cb + i.case_Append.ca;
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
LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw projectee
)
{
  if (projectee.tag == LowParse_PulseParse_Iterator_Type_Base)
    return true;
  else
    return false;
}

typedef struct
K___Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw fst;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw snd;
}
K___Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static K___Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw s,
  size_t i
)
{
  return
    (
      (K___Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

typedef struct
K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw fst;
  size_t snd;
}
K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t;

static LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
  K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
  x
)
{
  return x.fst;
}

static size_t
FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
  K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
  x
)
{
  return x.snd;
}

static cbor_det_array_iterator_t
CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_start_raw_data_item_fuel(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ml
)
{
  size_t
  total_sz =
    LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  if (total_sz == (size_t)0U)
    return
      (
        (cbor_det_array_iterator_t){
          .tag = IBase,
          { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
        }
      );
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    r_node = ml;
    size_t r_off = (size_t)0U;
    size_t r_n = total_sz;
    bool
    pcontinue =
      !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    while (pcontinue)
    {
      size_t cur_off_v = r_off;
      size_t cur_n_v = r_n;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      scrut = r_node;
      if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = scrut.case_Append.after;
        size_t oa = scrut.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = scrut.case_Append.before;
        size_t ob = scrut.case_Append.ob;
        size_t cb = scrut.case_Append.cb;
        size_t
        child_n_before = LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v, cur_n_v, cb);
        if (child_n_before > (size_t)0U)
        {
          size_t
          child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ib = *before;
          r_node = ib;
          r_off = child_off_sz;
          r_n = child_n_before;
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
        }
        else
        {
          size_t child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
          size_t
          child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ia = *after;
          r_node = ia;
          r_off = child_off_sz;
          r_n = child_n_sz;
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
        }
      }
      else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    size_t cur_off_v = r_off;
    size_t cur_n_v = r_n;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut = r_node;
    K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
    res;
    if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = scrut.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw bi_;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi.case_Singleton;
        if (cur_n_v == (size_t)0U)
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    cur_off_v).snd,
                  cur_n_v).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = cur_off_v;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = cur_n_v,
                  .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        bi_ =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      res =
        (
          (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
            .fst = bi_,
            .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
          }
        );
    }
    else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      res =
        KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "Pulse.Lib.Dv.unreachable");
    else
      res =
        KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "unreachable (pattern matches are exhaustive in F*)");
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi_ =
      FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t
    len_sz =
      FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t rest_sz = total_sz - len_sz;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi.case_Singleton;
        if (rest_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    len_sz).snd,
                  rest_sz).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = len_sz;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = rest_sz,
                  .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
      size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
      size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = LowParse_PulseParse_Iterator_append_off_after_sz(len_sz, oa, cb),
                .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_det_array_iterator_t){
          .tag = IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
        }
      );
  }
}

static size_t
Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s
)
{
  return s.len;
}

static size_t
LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  i
)
{
  if (i.tag == LowParse_PulseParse_Iterator_Type_Empty)
    return (size_t)0U;
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Singleton)
    return (size_t)1U;
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Slice)
    return
      Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i.case_Slice);
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Serialized)
    return i.case_Serialized.count;
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
LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  i
)
{
  if (i.tag == LowParse_PulseParse_Iterator_Type_Base)
    return
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i.case_Base);
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Append)
    return i.case_Append.cb + i.case_Append.ca;
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
LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  projectee
)
{
  if (projectee.tag == LowParse_PulseParse_Iterator_Type_Base)
    return true;
  else
    return false;
}

typedef struct
K___Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  fst;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  snd;
}
K___Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static K___Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s,
  size_t i
)
{
  return
    (
      (K___Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

typedef struct
K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  fst;
  size_t snd;
}
K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t;

static LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
  K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
  x
)
{
  return x.fst;
}

static size_t
FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
  K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
  x
)
{
  return x.snd;
}

static cbor_det_map_iterator_t
CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_start_map_entry_raw_data_item_fuel(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml
)
{
  size_t
  total_sz =
    LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  if (total_sz == (size_t)0U)
    return
      (
        (cbor_det_map_iterator_t){
          .tag = IBase,
          { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
        }
      );
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    r_node = ml;
    size_t r_off = (size_t)0U;
    size_t r_n = total_sz;
    bool
    pcontinue =
      !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    while (pcontinue)
    {
      size_t cur_off_v = r_off;
      size_t cur_n_v = r_n;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      scrut = r_node;
      if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = scrut.case_Append.after;
        size_t oa = scrut.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = scrut.case_Append.before;
        size_t ob = scrut.case_Append.ob;
        size_t cb = scrut.case_Append.cb;
        size_t
        child_n_before = LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v, cur_n_v, cb);
        if (child_n_before > (size_t)0U)
        {
          size_t
          child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ib = *before;
          r_node = ib;
          r_off = child_off_sz;
          r_n = child_n_before;
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
        }
        else
        {
          size_t child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
          size_t
          child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ia = *after;
          r_node = ia;
          r_off = child_off_sz;
          r_n = child_n_sz;
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
        }
      }
      else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    size_t cur_off_v = r_off;
    size_t cur_n_v = r_n;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut = r_node;
    K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
    res;
    if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = scrut.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi_;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
        if (cur_n_v == (size_t)0U)
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    cur_off_v).snd,
                  cur_n_v).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = cur_off_v;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t
          offset_ =
            CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
              poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = cur_n_v,
                  .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        bi_ =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      res =
        (
          (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
            .fst = bi_,
            .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
          }
        );
    }
    else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      res =
        KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "Pulse.Lib.Dv.unreachable");
    else
      res =
        KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "unreachable (pattern matches are exhaustive in F*)");
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi_ =
      FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t
    len_sz =
      FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t rest_sz = total_sz - len_sz;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      ite;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
        if (rest_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    len_sz).snd,
                  rest_sz).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = len_sz;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t
          offset_ =
            CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
              poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = rest_sz,
                  .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
      size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
      size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = LowParse_PulseParse_Iterator_append_off_after_sz(len_sz, oa, cb),
                .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_det_map_iterator_t){
          .tag = IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
        }
      );
  }
}

static cbor_raw
Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw a,
  size_t i
)
{
  return a.elt[i];
}

static LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_eos_raw_data_item_fuel_byref(
  cbor_det_array_iterator_t *r
)
{
  cbor_det_array_iterator_t scrut0 = *r;
  if (scrut0.tag == IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IBase;
    size_t
    len_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              {
                .case_EElement = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_ESerialized,
              {
                .case_ESerialized = Pulse_Lib_Slice_split__uint8_t(pl_suffix,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        *r =
          (
            (cbor_det_array_iterator_t){
              .tag = IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
        return x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n1 = pn;
            size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
            pn = n1 - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        *r = ((cbor_det_array_iterator_t){ .tag = IBase, { .case_IBase = ite } });
        return x1;
      }
    }
  }
  else if (scrut0.tag == IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = scrut0.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IPair.before;
    size_t
    len_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              {
                .case_EElement = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_ESerialized,
              {
                .case_ESerialized = Pulse_Lib_Slice_split__uint8_t(pl_suffix,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        size_t
        total_sz =
          LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        cbor_det_array_iterator_t ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (cbor_det_array_iterator_t){
                .tag = IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = ml;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz;
          bool
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t
              child_n_before =
                LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v,
                  cur_n_v,
                  cb);
              if (child_n_before > (size_t)0U)
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
                size_t
                child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_ =
            FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz1 =
            FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz - len_sz1;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite1;
          if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = ml.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (rest_sz == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          len_sz1).snd,
                        rest_sz).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = len_sz1;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = rest_sz,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = ml.case_Append.after;
            size_t oa = ml.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = ml.case_Append.before;
            size_t ob = ml.case_Append.ob;
            size_t cb = ml.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz1, rest_sz, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz1, rest_sz, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz1, ob, cb);
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(len_sz1, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (cbor_det_array_iterator_t){
                .tag = IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        *r = ite0;
        return x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n1 = pn;
            size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
            pn = n1 - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        *r =
          (
            (cbor_det_array_iterator_t){
              .tag = IPair,
              { .case_IPair = { .before = ite, .after = ml } }
            }
          );
        return x1;
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

static cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a,
  size_t i
)
{
  return a.elt[i];
}

typedef struct
LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags
  tag;
  union {
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw case_EElement;
    Pulse_Lib_Slice_slice__uint8_t case_ESerialized;
  }
  ;
}
LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_eos_map_entry_raw_data_item_fuel_byref(
  cbor_det_map_iterator_t *r
)
{
  cbor_det_map_iterator_t scrut0 = *r;
  if (scrut0.tag == IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IBase;
    size_t
    len_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              {
                .case_EElement = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t
          offset_ =
            CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
              poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_ESerialized,
              {
                .case_ESerialized = Pulse_Lib_Slice_split__uint8_t(pl_suffix,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl_suffix,
                    (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        *r =
          (
            (cbor_det_map_iterator_t){
              .tag = IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
        return x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n1 = pn;
            size_t
            offset_ =
              CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                poffset);
            pn = n1 - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        *r = ((cbor_det_map_iterator_t){ .tag = IBase, { .case_IBase = ite } });
        return x1;
      }
    }
  }
  else if (scrut0.tag == IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = scrut0.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IPair.before;
    size_t
    len_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              {
                .case_EElement = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t
          offset_ =
            CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
              poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_ESerialized,
              {
                .case_ESerialized = Pulse_Lib_Slice_split__uint8_t(pl_suffix,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl_suffix,
                    (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        size_t
        total_sz =
          LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        cbor_det_map_iterator_t ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (cbor_det_map_iterator_t){
                .tag = IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = ml;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz;
          bool
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t
              child_n_before =
                LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v,
                  cur_n_v,
                  cb);
              if (child_n_before > (size_t)0U)
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
                size_t
                child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ =
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                    poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_ =
            FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz1 =
            FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz - len_sz1;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite1;
          if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = ml.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (rest_sz == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          len_sz1).snd,
                        rest_sz).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = len_sz1;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ =
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                    poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = rest_sz,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = ml.case_Append.after;
            size_t oa = ml.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = ml.case_Append.before;
            size_t ob = ml.case_Append.ob;
            size_t cb = ml.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz1, rest_sz, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz1, rest_sz, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz1, ob, cb);
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(len_sz1, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (cbor_det_map_iterator_t){
                .tag = IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        *r = ite0;
        return x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n1 = pn;
            size_t
            offset_ =
              CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                poffset);
            pn = n1 - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        *r =
          (
            (cbor_det_map_iterator_t){
              .tag = IPair,
              { .case_IPair = { .before = ite, .after = ml } }
            }
          );
        return x1;
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

static int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_Base_uint64_compare(uint64_t x1, uint64_t x2)
{
  if (x1 < x2)
    return (int16_t)-1;
  else if (x1 > x2)
    return (int16_t)1;
  else
    return (int16_t)0;
}

static int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_Base_impl_raw_uint64_compare(
  CBOR_Spec_Raw_Base_raw_uint64 x1,
  CBOR_Spec_Raw_Base_raw_uint64 x2
)
{
  int16_t c = CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(x1.size, x2.size);
  if (c == (int16_t)0)
    return CBOR_Pulse_Raw_EverParse_Det_Compare_Base_uint64_compare(x1.value, x2.value);
  else
    return c;
}

static int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_Base_byte_compare_pts_to_parsed_data_item(
  Pulse_Lib_Slice_slice__uint8_t s1,
  Pulse_Lib_Slice_slice__uint8_t s2
)
{
  return CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(s1, s2);
}

static size_t
CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_validate(Pulse_Lib_Slice_slice__uint8_t input)
{
  size_t poffset = (size_t)0U;
  if (CBOR_Pulse_Raw_EverParse_Validate_validate_raw_data_item(input, &poffset))
    return poffset;
  else
    return (size_t)0U;
}

static bool
CBOR_Pulse_Raw_EverParse_Det_Validate_impl_raw_uint64_optimal(CBOR_Spec_Raw_Base_raw_uint64 x)
{
  if (x.value <= (uint64_t)MAX_SIMPLE_VALUE_ADDITIONAL_INFO == (x.size == 0U))
    if (x.size <= 1U)
      return true;
    else if (x.size == 2U)
      return 256ULL <= x.value;
    else if (x.size == 3U)
      return 65536ULL <= x.value;
    else
      return 4294967296ULL <= x.value;
  else
    return false;
}

static bool
CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_raw_ints_optimal(Pulse_Lib_Slice_slice__uint8_t a)
{
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 =
    Pulse_Lib_Slice_split__uint8_t(a,
      CBOR_Pulse_Raw_EverParse_Validate_jump_header(a, (size_t)0U));
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
  CBOR_Spec_Raw_EverParse_header
  h =
    CBOR_Pulse_Raw_EverParse_Validate_read_header((
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut2.fst,
          .snd = scrut2.snd
        }
      ).fst);
  if (CBOR_Spec_Raw_EverParse_get_header_major_type(h) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return true;
  else
  {
    CBOR_Spec_Raw_EverParse_long_argument scrut = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 1U,
            .value = (uint64_t)scrut.case_LongArgumentU8
          }
        );
    else if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 2U,
            .value = (uint64_t)scrut.case_LongArgumentU16
          }
        );
    else if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentU32)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 3U,
            .value = (uint64_t)scrut.case_LongArgumentU32
          }
        );
    else if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = scrut.case_LongArgumentU64 });
    else if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)h.fst.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return CBOR_Pulse_Raw_EverParse_Det_Validate_impl_raw_uint64_optimal(ite);
  }
}

static bool
CBOR_Pulse_Raw_EverParse_Det_Validate_impl_deterministically_encoded_cbor_map_key_order(
  Pulse_Lib_Slice_slice__uint8_t a1,
  Pulse_Lib_Slice_slice__uint8_t a2
)
{
  return CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(a1, a2) < (int16_t)0;
}

static bool
CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_raw_sorted(Pulse_Lib_Slice_slice__uint8_t a)
{
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 =
    Pulse_Lib_Slice_split__uint8_t(a,
      CBOR_Pulse_Raw_EverParse_Validate_jump_header(a, (size_t)0U));
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
  Pulse_Lib_Slice_slice__uint8_t input2 = scrut3.snd;
  CBOR_Spec_Raw_EverParse_header h = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut3.fst);
  if (CBOR_Spec_Raw_EverParse_get_header_major_type(h) == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t nbpairs = CBOR_Spec_Raw_EverParse_argument_as_uint64(h.fst, h.snd);
    if (nbpairs < 2ULL)
      return true;
    else
    {
      CBOR_Spec_Raw_EverParse_initial_byte_t b = h.fst;
      size_t ite;
      if
      (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        ite = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h.fst, h.snd);
      else
        ite = (size_t)0U;
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut0 = Pulse_Lib_Slice_split__uint8_t(input2, ite);
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
      Pulse_Lib_Slice_slice__uint8_t
      input3 =
        (
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut2.fst,
            .snd = scrut2.snd
          }
        ).snd;
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut3 =
        Pulse_Lib_Slice_split__uint8_t(input3,
          CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(input3, (size_t)0U));
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut5 = { .fst = scrut4.fst, .snd = scrut4.snd };
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
      Pulse_Lib_Slice_slice__uint8_t input4 = scrut7.snd;
      Pulse_Lib_Slice_slice__uint8_t pkey = scrut7.fst;
      uint64_t ppairs = nbpairs - 1ULL;
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut =
        Pulse_Lib_Slice_split__uint8_t(input4,
          CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(input4, (size_t)0U));
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut8 = { .fst = scrut.fst, .snd = scrut.snd };
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut10 = { .fst = scrut9.fst, .snd = scrut9.snd };
      Pulse_Lib_Slice_slice__uint8_t
      ptail =
        (
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut10.fst,
            .snd = scrut10.snd
          }
        ).snd;
      bool pres = true;
      while (pres && ppairs > 0ULL)
      {
        Pulse_Lib_Slice_slice__uint8_t tail = ptail;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut =
          Pulse_Lib_Slice_split__uint8_t(tail,
            CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(tail, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
        Pulse_Lib_Slice_slice__uint8_t key2 = scrut3.fst;
        Pulse_Lib_Slice_slice__uint8_t tail2 = scrut3.snd;
        if
        (
          CBOR_Pulse_Raw_EverParse_Det_Validate_impl_deterministically_encoded_cbor_map_key_order(pkey,
            key2)
        )
        {
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut =
            Pulse_Lib_Slice_split__uint8_t(tail2,
              CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(tail2, (size_t)0U));
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
          Pulse_Lib_Slice_slice__uint8_t
          tail_ =
            (
              (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                .fst = scrut2.fst,
                .snd = scrut2.snd
              }
            ).snd;
          pkey = key2;
          ppairs = ppairs - 1ULL;
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
CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_validate_det_(Pulse_Lib_Slice_slice__uint8_t input)
{
  size_t len = CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_validate(input);
  if (len == (size_t)0U)
    return len;
  else
  {
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = Pulse_Lib_Slice_split__uint8_t(input, (size_t)0U);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 =
      Pulse_Lib_Slice_split__uint8_t((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).snd,
        len - (size_t)0U);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    Pulse_Lib_Slice_slice__uint8_t
    input1 =
      (
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut2.fst,
          .snd = scrut2.snd
        }
      ).fst;
    bool buf = false;
    KRML_HOST_IGNORE(&buf);
    size_t pn = (size_t)1U;
    bool pres0 = true;
    Pulse_Lib_Slice_slice__uint8_t ppi0 = input1;
    while (pres0 && pn > (size_t)0U)
    {
      size_t n = pn;
      Pulse_Lib_Slice_slice__uint8_t pi = ppi0;
      if (!CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_raw_ints_optimal(pi))
        pres0 = false;
      else
      {
        size_t off1 = CBOR_Pulse_Raw_EverParse_Validate_jump_header(pi, (size_t)0U);
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut = Pulse_Lib_Slice_split__uint8_t(pi, (size_t)0U);
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 =
          Pulse_Lib_Slice_split__uint8_t((
              (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                .fst = scrut.fst,
                .snd = scrut.snd
              }
            ).snd,
            off1 - (size_t)0U);
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        CBOR_Spec_Raw_EverParse_header
        x =
          CBOR_Pulse_Raw_EverParse_Validate_read_header((
              (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                .fst = scrut1.fst,
                .snd = scrut1.snd
              }
            ).fst);
        CBOR_Spec_Raw_EverParse_initial_byte_t b = x.fst;
        size_t ite;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
          ite = off1 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x.fst, x.snd);
        else
          ite = off1;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = Pulse_Lib_Slice_split__uint8_t(pi, ite);
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
        Pulse_Lib_Slice_slice__uint8_t ph = scrut4.fst;
        Pulse_Lib_Slice_slice__uint8_t pc = scrut4.snd;
        size_t unused = Pulse_Lib_Slice_len__uint8_t(pc);
        KRML_MAYBE_UNUSED_VAR(unused);
        pn = n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Validate_jump_recursive_step_count_leaf(ph);
        ppi0 = pc;
      }
    }
    if (!pres0)
      return (size_t)0U;
    else
    {
      size_t pn = (size_t)1U;
      bool pres = true;
      Pulse_Lib_Slice_slice__uint8_t ppi = input1;
      while (pres && pn > (size_t)0U)
      {
        size_t n = pn;
        Pulse_Lib_Slice_slice__uint8_t pi = ppi;
        if (!CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_raw_sorted(pi))
          pres = false;
        else
        {
          size_t off1 = CBOR_Pulse_Raw_EverParse_Validate_jump_header(pi, (size_t)0U);
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut = Pulse_Lib_Slice_split__uint8_t(pi, (size_t)0U);
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut0 =
            Pulse_Lib_Slice_split__uint8_t((
                (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                  .fst = scrut.fst,
                  .snd = scrut.snd
                }
              ).snd,
              off1 - (size_t)0U);
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          CBOR_Spec_Raw_EverParse_header
          x =
            CBOR_Pulse_Raw_EverParse_Validate_read_header((
                (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                  .fst = scrut1.fst,
                  .snd = scrut1.snd
                }
              ).fst);
          CBOR_Spec_Raw_EverParse_initial_byte_t b = x.fst;
          size_t ite;
          if
          (
            b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
              b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
          )
            ite = off1 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x.fst, x.snd);
          else
            ite = off1;
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut2 = Pulse_Lib_Slice_split__uint8_t(pi, ite);
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
          Pulse_Lib_Slice_slice__uint8_t ph = scrut4.fst;
          Pulse_Lib_Slice_slice__uint8_t pc = scrut4.snd;
          size_t unused = Pulse_Lib_Slice_len__uint8_t(pc);
          KRML_MAYBE_UNUSED_VAR(unused);
          pn = n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Validate_jump_recursive_step_count_leaf(ph);
          ppi = pc;
        }
      }
      if (!pres)
        return (size_t)0U;
      else
        return len;
    }
  }
}

static size_t
CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_validate_det(Pulse_Lib_Slice_slice__uint8_t input)
{
  return CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_validate_det_(input);
}

static cbor_raw
CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_parse_valid(Pulse_Lib_Slice_slice__uint8_t input)
{
  size_t len = Pulse_Lib_Slice_len__uint8_t(input);
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut = Pulse_Lib_Slice_split__uint8_t(input, (size_t)0U);
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 =
    Pulse_Lib_Slice_split__uint8_t((
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut.fst,
          .snd = scrut.snd
        }
      ).snd,
      len - (size_t)0U);
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  return
    CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read((
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut1.fst,
          .snd = scrut1.snd
        }
      ).fst);
}

static cbor_raw CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm_tot(cbor_raw c)
{
  if (c.tag == CBOR_Case_String)
  {
    cbor_string v = c.case_CBOR_Case_String;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_String,
          {
            .case_CBOR_Case_String = {
              .cbor_string_type = v.cbor_string_type,
              .cbor_string_size = v.cbor_string_size,
              .cbor_string_ptr = v.cbor_string_ptr
            }
          }
        }
      );
  }
  else if (c.tag == CBOR_Case_Tagged)
  {
    cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = c.case_CBOR_Case_Tagged;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Tagged,
          {
            .case_CBOR_Case_Tagged = {
              .cbor_tagged_tag = v.cbor_tagged_tag,
              .cbor_tagged_ptr = v.cbor_tagged_ptr
            }
          }
        }
      );
  }
  else if (c.tag == CBOR_Case_Tagged_Serialized)
  {
    cbor_tagged_serialized v = c.case_CBOR_Case_Tagged_Serialized;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Tagged_Serialized,
          {
            .case_CBOR_Case_Tagged_Serialized = {
              .cbor_tagged_serialized_tag = v.cbor_tagged_serialized_tag,
              .cbor_tagged_serialized_ptr = v.cbor_tagged_serialized_ptr
            }
          }
        }
      );
  }
  else if (c.tag == CBOR_Case_Array)
  {
    cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = c.case_CBOR_Case_Array;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Array,
          {
            .case_CBOR_Case_Array = {
              .cbor_array_length_size = v.cbor_array_length_size,
              .cbor_array_ptr = v.cbor_array_ptr
            }
          }
        }
      );
  }
  else if (c.tag == CBOR_Case_Map)
  {
    cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = c.case_CBOR_Case_Map;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Map,
          {
            .case_CBOR_Case_Map = {
              .cbor_map_length_size = v.cbor_map_length_size,
              .cbor_map_ptr = v.cbor_map_ptr
            }
          }
        }
      );
  }
  else
    return c;
}

static cbor_raw CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(cbor_raw c)
{
  return CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm_tot(c);
}

#define CBOR_Pulse_Raw_EverParse_Insert_CFailure 0
#define CBOR_Pulse_Raw_EverParse_Insert_CInProgress 1
#define CBOR_Pulse_Raw_EverParse_Insert_CSuccess 2

typedef uint8_t CBOR_Pulse_Raw_EverParse_Insert_cbor_raw_map_insert_result;

static bool
CBOR_Pulse_Raw_EverParse_Insert_uu___is_CInProgress(
  CBOR_Pulse_Raw_EverParse_Insert_cbor_raw_map_insert_result projectee
)
{
  switch (projectee)
  {
    case CBOR_Pulse_Raw_EverParse_Insert_CInProgress:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

static void
Pulse_Lib_Slice_op_Array_Assignment__uint8_t(
  Pulse_Lib_Slice_slice__uint8_t a,
  size_t i,
  uint8_t v
)
{
  a.elt[i] = v;
}

static bool
CBOR_Pulse_Raw_EverParse_Insert_cbor_raw_map_insert(
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t off2,
  size_t off3
)
{
  size_t poff = (size_t)0U;
  CBOR_Pulse_Raw_EverParse_Insert_cbor_raw_map_insert_result
  pres = CBOR_Pulse_Raw_EverParse_Insert_CInProgress;
  size_t off0 = poff;
  bool cond = CBOR_Pulse_Raw_EverParse_Insert_uu___is_CInProgress(pres) && off0 < off2;
  while (cond)
  {
    size_t off = poff;
    Pulse_Lib_Slice_slice__uint8_t out2kv = Pulse_Lib_Slice_split__uint8_t(out, off).snd;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = Pulse_Lib_Slice_split__uint8_t(out2kv, off2 - off);
    Pulse_Lib_Slice_slice__uint8_t out2 = scrut0.fst;
    Pulse_Lib_Slice_slice__uint8_t
    outk = Pulse_Lib_Slice_split__uint8_t(scrut0.snd, off3 - off2).fst;
    size_t offk = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(out2, (size_t)0U);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = Pulse_Lib_Slice_split__uint8_t(out2, offk);
    Pulse_Lib_Slice_slice__uint8_t outvq = scrut.snd;
    int16_t c = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(scrut.fst, outk);
    if (c < (int16_t)0)
      poff = off + offk + CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(outvq, (size_t)0U);
    else if (c > (int16_t)0)
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
              idx_ = idx + off2 - off - (size_t)0U;
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
      pres = CBOR_Pulse_Raw_EverParse_Insert_CSuccess;
    }
    else
      pres = CBOR_Pulse_Raw_EverParse_Insert_CFailure;
    size_t off0 = poff;
    cond = CBOR_Pulse_Raw_EverParse_Insert_uu___is_CInProgress(pres) && off0 < off2;
  }
  switch (pres)
  {
    case CBOR_Pulse_Raw_EverParse_Insert_CSuccess:
      {
        return true;
      }
    case CBOR_Pulse_Raw_EverParse_Insert_CFailure:
      {
        return false;
      }
    case CBOR_Pulse_Raw_EverParse_Insert_CInProgress:
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

static size_t
CBOR_Pulse_Raw_EverParse_Serialize_write_header(
  CBOR_Spec_Raw_EverParse_header x,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t offset
)
{
  CBOR_Spec_Raw_EverParse_initial_byte_t
  xh1 =
    FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
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
  size_t res1 = pos_;
  CBOR_Spec_Raw_EverParse_long_argument
  x2_ =
    FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    if (xh1.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    {
      size_t pos_ = res1 + (size_t)1U;
      uint8_t ite;
      if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
        ite = x2_.case_LongArgumentSimpleValue;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_ - (size_t)1U, ite);
      return pos_;
    }
    else
    {
      size_t pos_ = res1 + (size_t)1U;
      uint8_t ite;
      if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU8)
        ite = x2_.case_LongArgumentU8;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_ - (size_t)1U, ite);
      return pos_;
    }
  else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
  {
    size_t pos_ = res1 + (size_t)2U;
    uint16_t ite0;
    if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite0 = x2_.case_LongArgumentU16;
    else
      ite0 = KRML_EABORT(uint16_t, "unreachable (pattern matches are exhaustive in F*)");
    uint8_t lo = (uint8_t)ite0;
    size_t pos_1 = pos_ - (size_t)1U;
    uint16_t ite;
    if (x2_.tag == CBOR_Spec_Raw_EverParse_LongArgumentU16)
      ite = x2_.case_LongArgumentU16;
    else
      ite = KRML_EABORT(uint16_t, "unreachable (pattern matches are exhaustive in F*)");
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out,
      pos_1 - (size_t)1U,
      (uint8_t)((uint32_t)ite / 256U));
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_1, lo);
    return pos_;
  }
  else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
  {
    size_t pos_ = res1 + (size_t)4U;
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
    size_t pos_1 = pos_ - (size_t)1U;
    uint8_t lo1 = (uint8_t)hi;
    uint32_t hi1 = hi / 256U;
    size_t pos_2 = pos_1 - (size_t)1U;
    uint8_t lo2 = (uint8_t)hi1;
    size_t pos_3 = pos_2 - (size_t)1U;
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_3 - (size_t)1U, (uint8_t)(hi1 / 256U));
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_3, lo2);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_2, lo1);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_1, lo);
    return pos_;
  }
  else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
  {
    size_t pos_ = res1 + (size_t)8U;
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
    size_t pos_1 = pos_ - (size_t)1U;
    uint8_t lo1 = (uint8_t)hi;
    uint64_t hi1 = hi / 256ULL;
    size_t pos_2 = pos_1 - (size_t)1U;
    uint8_t lo2 = (uint8_t)hi1;
    uint64_t hi2 = hi1 / 256ULL;
    size_t pos_3 = pos_2 - (size_t)1U;
    uint8_t lo3 = (uint8_t)hi2;
    uint64_t hi3 = hi2 / 256ULL;
    size_t pos_4 = pos_3 - (size_t)1U;
    uint8_t lo4 = (uint8_t)hi3;
    uint64_t hi4 = hi3 / 256ULL;
    size_t pos_5 = pos_4 - (size_t)1U;
    uint8_t lo5 = (uint8_t)hi4;
    uint64_t hi5 = hi4 / 256ULL;
    size_t pos_6 = pos_5 - (size_t)1U;
    uint8_t lo6 = (uint8_t)hi5;
    size_t pos_7 = pos_6 - (size_t)1U;
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_7 - (size_t)1U, (uint8_t)(hi5 / 256ULL));
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_7, lo6);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_6, lo5);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_5, lo4);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_4, lo3);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_3, lo2);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_2, lo1);
    Pulse_Lib_Slice_op_Array_Assignment__uint8_t(out, pos_1, lo);
    return pos_;
  }
  else
    return res1;
}

static bool
CBOR_Pulse_Raw_EverParse_Serialize_size_header(CBOR_Spec_Raw_EverParse_header x, size_t *out)
{
  CBOR_Spec_Raw_EverParse_initial_byte_t
  xh1 =
    FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
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
  {
    FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
    if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    {
      size_t capacity = *out;
      if (capacity < (size_t)1U)
        return false;
      else
      {
        *out = capacity - (size_t)1U;
        return true;
      }
    }
    else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    {
      size_t capacity = *out;
      if (capacity < (size_t)2U)
        return false;
      else
      {
        *out = capacity - (size_t)2U;
        return true;
      }
    }
    else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    {
      size_t capacity = *out;
      if (capacity < (size_t)4U)
        return false;
      else
      {
        *out = capacity - (size_t)4U;
        return true;
      }
    }
    else if (xh1.additional_info == CBOR_SPEC_RAW_EVERPARSE_ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    {
      size_t capacity = *out;
      if (capacity < (size_t)8U)
        return false;
      else
      {
        *out = capacity - (size_t)8U;
        return true;
      }
    }
    else
      return true;
  }
  else
    return false;
}

typedef struct FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header_s
{
  FStar_Pervasives_Native_option__uint8_t_tags tag;
  CBOR_Spec_Raw_EverParse_header v;
}
FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header;

static CBOR_Spec_Raw_EverParse_header
CBOR_Pulse_Raw_EverParse_Serialize_cbor_raw_get_header_impl(cbor_raw xl)
{
  FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header scrut;
  if (xl.tag == CBOR_Case_Int)
  {
    cbor_int v = xl.case_CBOR_Case_Int;
    scrut =
      (
        (FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(v.cbor_int_type,
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = v.cbor_int_size, .value = v.cbor_int_value }))
        }
      );
  }
  else if (xl.tag == CBOR_Case_Simple)
    scrut =
      (
        (FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_Spec_Raw_EverParse_simple_value_as_argument(xl.case_CBOR_Case_Simple)
        }
      );
  else if (xl.tag == CBOR_Case_String)
  {
    cbor_string v = xl.case_CBOR_Case_String;
    scrut =
      (
        (FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(v.cbor_string_type,
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = v.cbor_string_size,
                .value = (uint64_t)Pulse_Lib_Slice_len__uint8_t(v.cbor_string_ptr)
              }
            ))
        }
      );
  }
  else if (xl.tag == CBOR_Case_Array)
  {
    cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = xl.case_CBOR_Case_Array;
    scrut =
      (
        (FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY,
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = v.cbor_array_length_size,
                .value = (uint64_t)LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_array_ptr)
              }
            ))
        }
      );
  }
  else if (xl.tag == CBOR_Case_Map)
  {
    cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = xl.case_CBOR_Case_Map;
    scrut =
      (
        (FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP,
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = v.cbor_map_length_size,
                .value = (uint64_t)LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_map_ptr)
              }
            ))
        }
      );
  }
  else if (xl.tag == CBOR_Case_Tagged)
    scrut =
      (
        (FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED,
            xl.case_CBOR_Case_Tagged.cbor_tagged_tag)
        }
      );
  else if (xl.tag == CBOR_Case_Tagged_Serialized)
    scrut =
      (
        (FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header){
          .tag = FStar_Pervasives_Native_Some,
          .v = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED,
            xl.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag)
        }
      );
  else if (xl.tag == CBOR_Case_Invalid)
    scrut =
      (
        (FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
    scrut =
      KRML_EABORT(FStar_Pervasives_Native_option__CBOR_Spec_Raw_EverParse_header,
        "unreachable (pattern matches are exhaustive in F*)");
  if (scrut.tag == FStar_Pervasives_Native_Some)
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

static CBOR_Spec_Raw_EverParse_header
CBOR_Pulse_Raw_EverParse_Serialize_cbor_raw_with_perm_get_header(cbor_raw xl)
{
  return CBOR_Pulse_Raw_EverParse_Serialize_cbor_raw_get_header_impl(xl);
}

static void
Pulse_Lib_Slice_copy__uint8_t(
  Pulse_Lib_Slice_slice__uint8_t dst,
  Pulse_Lib_Slice_slice__uint8_t src
)
{
  memcpy(dst.elt, src.elt, src.len * sizeof (uint8_t));
}

size_t
CBOR_Pulse_Raw_EverParse_Serialize_ser_(
  cbor_raw x_,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t offset
)
{
  CBOR_Spec_Raw_EverParse_header
  xh1 = CBOR_Pulse_Raw_EverParse_Serialize_cbor_raw_with_perm_get_header(x_);
  size_t res1 = CBOR_Pulse_Raw_EverParse_Serialize_write_header(xh1, out, offset);
  CBOR_Spec_Raw_EverParse_initial_byte_t b = xh1.fst;
  if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
  {
    Pulse_Lib_Slice_slice__uint8_t x2_ = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string(x_);
    size_t length = Pulse_Lib_Slice_len__uint8_t(x2_);
    Pulse_Lib_Slice_copy__uint8_t(Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out,
          res1).snd,
        length).fst,
      x2_);
    return res1 + length;
  }
  else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_ARRAY)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    arr = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array(x_);
    size_t n = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(xh1.fst, xh1.snd);
    if (n == (size_t)0U)
      return res1;
    else
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      p_node = arr;
      size_t p_offset = res1;
      size_t p_remaining = n;
      while (p_remaining > (size_t)0U)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        cur = p_node;
        size_t cur_off = p_offset;
        size_t cur_rem = p_remaining;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        r_node = cur;
        size_t r_off = (size_t)0U;
        size_t r_n = cur_rem;
        bool
        pcontinue =
          !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur);
        while (pcontinue)
        {
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = scrut.case_Append.after;
            size_t oa = scrut.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = scrut.case_Append.before;
            size_t ob = scrut.case_Append.ob;
            size_t cb = scrut.case_Append.cb;
            size_t
            child_n_before = LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v, cur_n_v, cb);
            if (child_n_before > (size_t)0U)
            {
              size_t
              child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ib = *before;
              r_node = ib;
              r_off = child_off_sz;
              r_n = child_n_before;
              pcontinue =
                !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
            }
            else
            {
              size_t
              child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
              size_t
              child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ia = *after;
              r_node = ia;
              r_off = child_off_sz;
              r_n = child_n_sz;
              pcontinue =
                !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
            }
          }
          else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        size_t cur_off_v = r_off;
        size_t cur_n_v = r_n;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        scrut = r_node;
        K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
        res;
        if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
        {
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi = scrut.case_Base;
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_;
          if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
          {
            cbor_raw *s = bi.case_Singleton;
            if (cur_n_v == (size_t)0U)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                    { .case_Singleton = s }
                  }
                );
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Slice,
                  {
                    .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                        cur_off_v).snd,
                      cur_n_v).fst
                  }
                }
              );
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
          {
            Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
            size_t pn = cur_off_v;
            size_t poffset = (size_t)0U;
            while (pn > (size_t)0U)
            {
              size_t n1 = pn;
              size_t
              offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
              pn = n1 - (size_t)1U;
              poffset = offset_;
            }
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                  {
                    .case_Serialized = {
                      .count = cur_n_v,
                      .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                    }
                  }
                }
              );
          }
          else
            bi_ =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          res =
            (
              (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                .fst = bi_,
                .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
              }
            );
        }
        else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
          res =
            KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
              "Pulse.Lib.Dv.unreachable");
        else
          res =
            KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
              "unreachable (pattern matches are exhaustive in F*)");
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        bi =
          FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        size_t
        chunk_len =
          FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl_bi = bi.case_Serialized.payload;
          size_t pn0 = chunk_len;
          size_t poffset0 = (size_t)0U;
          while (pn0 > (size_t)0U)
          {
            size_t n1 = pn0;
            size_t
            offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl_bi, poffset0);
            pn0 = n1 - (size_t)1U;
            poffset0 = offset_;
          }
          size_t byte_len = poffset0;
          Pulse_Lib_Slice_slice__uint8_t
          out21 =
            Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out, cur_off).snd,
              byte_len).fst;
          Pulse_Lib_Slice_copy__uint8_t(out21, Pulse_Lib_Slice_split__uint8_t(pl_bi, byte_len).fst);
          size_t off_ = cur_off + byte_len;
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        {
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ss_bi = bi.case_Slice;
          size_t pres = cur_off;
          size_t pi = (size_t)0U;
          while (pi < chunk_len)
          {
            size_t i1 = pi;
            size_t off = pres;
            size_t i_ = i1 + (size_t)1U;
            size_t
            off_ =
              CBOR_Pulse_Raw_EverParse_Serialize_ser_(Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ss_bi,
                  i1),
                out,
                off);
            pi = i_;
            pres = off_;
          }
          size_t off_ = pres;
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          size_t off_ = CBOR_Pulse_Raw_EverParse_Serialize_ser_(*bi.case_Singleton, out, cur_off);
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (!(bi.tag == LowParse_PulseParse_Iterator_Type_Empty))
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
      }
      return p_offset;
    }
  }
  else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_MAP)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    arr = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map(x_);
    size_t n = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(xh1.fst, xh1.snd);
    if (n == (size_t)0U)
      return res1;
    else
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      p_node = arr;
      size_t p_offset = res1;
      size_t p_remaining = n;
      while (p_remaining > (size_t)0U)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        cur = p_node;
        size_t cur_off = p_offset;
        size_t cur_rem = p_remaining;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        r_node = cur;
        size_t r_off = (size_t)0U;
        size_t r_n = cur_rem;
        bool
        pcontinue =
          !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur);
        while (pcontinue)
        {
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = scrut.case_Append.after;
            size_t oa = scrut.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = scrut.case_Append.before;
            size_t ob = scrut.case_Append.ob;
            size_t cb = scrut.case_Append.cb;
            size_t
            child_n_before = LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v, cur_n_v, cb);
            if (child_n_before > (size_t)0U)
            {
              size_t
              child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ib = *before;
              r_node = ib;
              r_off = child_off_sz;
              r_n = child_n_before;
              pcontinue =
                !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
            }
            else
            {
              size_t
              child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
              size_t
              child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ia = *after;
              r_node = ia;
              r_off = child_off_sz;
              r_n = child_n_sz;
              pcontinue =
                !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
            }
          }
          else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        size_t cur_off_v = r_off;
        size_t cur_n_v = r_n;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        scrut = r_node;
        K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
        res;
        if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
        {
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi = scrut.case_Base;
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_;
          if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
          {
            cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
            if (cur_n_v == (size_t)0U)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                    { .case_Singleton = s }
                  }
                );
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Slice,
                  {
                    .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                        cur_off_v).snd,
                      cur_n_v).fst
                  }
                }
              );
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
          {
            Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
            size_t pn = cur_off_v;
            size_t poffset = (size_t)0U;
            while (pn > (size_t)0U)
            {
              size_t n1 = pn;
              size_t
              offset_ =
                CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                  poffset);
              pn = n1 - (size_t)1U;
              poffset = offset_;
            }
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                  {
                    .case_Serialized = {
                      .count = cur_n_v,
                      .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                    }
                  }
                }
              );
          }
          else
            bi_ =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          res =
            (
              (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                .fst = bi_,
                .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
              }
            );
        }
        else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
          res =
            KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
              "Pulse.Lib.Dv.unreachable");
        else
          res =
            KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
              "unreachable (pattern matches are exhaustive in F*)");
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        bi =
          FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        size_t
        chunk_len =
          FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl_bi = bi.case_Serialized.payload;
          size_t pn0 = chunk_len;
          size_t poffset0 = (size_t)0U;
          while (pn0 > (size_t)0U)
          {
            size_t n1 = pn0;
            size_t
            offset_ =
              CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl_bi,
                poffset0);
            pn0 = n1 - (size_t)1U;
            poffset0 = offset_;
          }
          size_t byte_len = poffset0;
          Pulse_Lib_Slice_slice__uint8_t
          out21 =
            Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_split__uint8_t(out, cur_off).snd,
              byte_len).fst;
          Pulse_Lib_Slice_copy__uint8_t(out21, Pulse_Lib_Slice_split__uint8_t(pl_bi, byte_len).fst);
          size_t off_ = cur_off + byte_len;
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ =
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                    poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        {
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ss_bi = bi.case_Slice;
          size_t pres = cur_off;
          size_t pi = (size_t)0U;
          while (pi < chunk_len)
          {
            size_t i1 = pi;
            size_t off = pres;
            cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            e =
              Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ss_bi,
                i1);
            size_t i_ = i1 + (size_t)1U;
            size_t
            off_ =
              CBOR_Pulse_Raw_EverParse_Serialize_ser_(e.cbor_map_entry_value,
                out,
                CBOR_Pulse_Raw_EverParse_Serialize_ser_(e.cbor_map_entry_key, out, off));
            pi = i_;
            pres = off_;
          }
          size_t off_ = pres;
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ =
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                    poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw xv = *bi.case_Singleton;
          size_t
          off_ =
            CBOR_Pulse_Raw_EverParse_Serialize_ser_(xv.cbor_map_entry_value,
              out,
              CBOR_Pulse_Raw_EverParse_Serialize_ser_(xv.cbor_map_entry_key, out, cur_off));
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ =
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                    poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (!(bi.tag == LowParse_PulseParse_Iterator_Type_Empty))
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
      }
      return p_offset;
    }
  }
  else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_TAGGED)
    return
      CBOR_Pulse_Raw_EverParse_Serialize_ser_(CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_tagged_payload(x_),
        out,
        res1);
  else
    return res1;
}

static size_t
CBOR_Pulse_Raw_EverParse_Serialize_ser(
  cbor_raw x1_,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t offset
)
{
  return CBOR_Pulse_Raw_EverParse_Serialize_ser_(x1_, out, offset);
}

static size_t
CBOR_Pulse_Raw_EverParse_Serialize_cbor_serialize(
  cbor_raw x,
  Pulse_Lib_Slice_slice__uint8_t output
)
{
  return CBOR_Pulse_Raw_EverParse_Serialize_ser(x, output, (size_t)0U);
}

bool CBOR_Pulse_Raw_EverParse_Serialize_siz_(cbor_raw x_, size_t *out)
{
  CBOR_Spec_Raw_EverParse_header
  xh1 = CBOR_Pulse_Raw_EverParse_Serialize_cbor_raw_with_perm_get_header(x_);
  if (CBOR_Pulse_Raw_EverParse_Serialize_size_header(xh1, out))
  {
    CBOR_Spec_Raw_EverParse_initial_byte_t b = xh1.fst;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      size_t
      length = Pulse_Lib_Slice_len__uint8_t(CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string(x_));
      size_t cur = *out;
      if (cur < length)
        return false;
      else
      {
        *out = cur - length;
        return true;
      }
    }
    else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_ARRAY)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      arr = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array(x_);
      size_t n = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(xh1.fst, xh1.snd);
      if (n == (size_t)0U)
        return true;
      else
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        p_node = arr;
        size_t p_remaining = n;
        bool p_result = true;
        while (p_result && p_remaining > (size_t)0U)
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          cur = p_node;
          size_t cur_rem = p_remaining;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = cur;
          size_t r_off = (size_t)0U;
          size_t r_n = cur_rem;
          bool
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t
              child_n_before =
                LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v,
                  cur_n_v,
                  cb);
              if (child_n_before > (size_t)0U)
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
                size_t
                child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi =
            FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          chunk_len =
            FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
          {
            Pulse_Lib_Slice_slice__uint8_t pl_bi = bi.case_Serialized.payload;
            size_t pn0 = chunk_len;
            size_t poffset0 = (size_t)0U;
            while (pn0 > (size_t)0U)
            {
              size_t n1 = pn0;
              size_t
              offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl_bi, poffset0);
              pn0 = n1 - (size_t)1U;
              poffset0 = offset_;
            }
            size_t byte_len = poffset0;
            size_t remaining = *out;
            bool chunk_res;
            if (byte_len <= remaining)
            {
              *out = remaining - byte_len;
              chunk_res = true;
            }
            else
              chunk_res = false;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t
                  offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t
              cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
              size_t
              ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                        .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          {
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ss_bi = bi.case_Slice;
            bool pres = true;
            size_t pi = (size_t)0U;
            while (pres && pi < chunk_len)
            {
              size_t i1 = pi;
              if
              (
                CBOR_Pulse_Raw_EverParse_Serialize_siz_(Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ss_bi,
                    i1),
                  out)
              )
                pi = i1 + (size_t)1U;
              else
                pres = false;
            }
            bool chunk_res = pres;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t
                  offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t
              cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
              size_t
              ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                        .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
          {
            bool chunk_res = CBOR_Pulse_Raw_EverParse_Serialize_siz_(*bi.case_Singleton, out);
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t
                  offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t
              cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
              size_t
              ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                        .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (!(bi.tag == LowParse_PulseParse_Iterator_Type_Empty))
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        return p_result;
      }
    }
    else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_MAP)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      arr = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map(x_);
      size_t n = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(xh1.fst, xh1.snd);
      if (n == (size_t)0U)
        return true;
      else
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        p_node = arr;
        size_t p_remaining = n;
        bool p_result = true;
        while (p_result && p_remaining > (size_t)0U)
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          cur = p_node;
          size_t cur_rem = p_remaining;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = cur;
          size_t r_off = (size_t)0U;
          size_t r_n = cur_rem;
          bool
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t
              child_n_before =
                LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v,
                  cur_n_v,
                  cb);
              if (child_n_before > (size_t)0U)
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
                size_t
                child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t
                offset_ =
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                    poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi =
            FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          chunk_len =
            FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
          {
            Pulse_Lib_Slice_slice__uint8_t pl_bi = bi.case_Serialized.payload;
            size_t pn0 = chunk_len;
            size_t poffset0 = (size_t)0U;
            while (pn0 > (size_t)0U)
            {
              size_t n1 = pn0;
              size_t
              offset_ =
                CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl_bi,
                  poffset0);
              pn0 = n1 - (size_t)1U;
              poffset0 = offset_;
            }
            size_t byte_len = poffset0;
            size_t remaining = *out;
            bool chunk_res;
            if (byte_len <= remaining)
            {
              *out = remaining - byte_len;
              chunk_res = true;
            }
            else
              chunk_res = false;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t
                  offset_ =
                    CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                      poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t
              cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
              size_t
              ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                        .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          {
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ss_bi = bi.case_Slice;
            bool pres = true;
            size_t pi = (size_t)0U;
            while (pres && pi < chunk_len)
            {
              size_t i1 = pi;
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              e =
                Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ss_bi,
                  i1);
              bool ite;
              if (CBOR_Pulse_Raw_EverParse_Serialize_siz_(e.cbor_map_entry_key, out))
                ite = CBOR_Pulse_Raw_EverParse_Serialize_siz_(e.cbor_map_entry_value, out);
              else
                ite = false;
              if (ite)
                pi = i1 + (size_t)1U;
              else
                pres = false;
            }
            bool chunk_res = pres;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t
                  offset_ =
                    CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                      poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t
              cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
              size_t
              ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                        .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
          {
            cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw xv = *bi.case_Singleton;
            bool chunk_res;
            if (CBOR_Pulse_Raw_EverParse_Serialize_siz_(xv.cbor_map_entry_key, out))
              chunk_res = CBOR_Pulse_Raw_EverParse_Serialize_siz_(xv.cbor_map_entry_value, out);
            else
              chunk_res = false;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t
                  offset_ =
                    CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                      poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t
              cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(chunk_len, new_rem, cb);
              size_t
              ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = LowParse_PulseParse_Iterator_append_off_after_sz(chunk_len, oa, cb),
                        .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (!(bi.tag == LowParse_PulseParse_Iterator_Type_Empty))
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        return p_result;
      }
    }
    else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_TAGGED)
      return
        CBOR_Pulse_Raw_EverParse_Serialize_siz_(CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_tagged_payload(x_),
          out);
    else
      return true;
  }
  else
    return false;
}

static bool CBOR_Pulse_Raw_EverParse_Serialize_siz(cbor_raw x1_, size_t *out)
{
  return CBOR_Pulse_Raw_EverParse_Serialize_siz_(x1_, out);
}

static size_t CBOR_Pulse_Raw_EverParse_Serialize_cbor_size(cbor_raw x, size_t bound)
{
  size_t output = bound;
  if (CBOR_Pulse_Raw_EverParse_Serialize_siz(x, &output))
    return bound - output;
  else
    return (size_t)0U;
}

static size_t
CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_tag(
  CBOR_Spec_Raw_Base_raw_uint64 tag,
  Pulse_Lib_Slice_slice__uint8_t output
)
{
  CBOR_Spec_Raw_EverParse_header
  h = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED, tag);
  size_t buf = Pulse_Lib_Slice_len__uint8_t(output);
  if (CBOR_Pulse_Raw_EverParse_Serialize_size_header(h, &buf))
    return CBOR_Pulse_Raw_EverParse_Serialize_write_header(h, output, (size_t)0U);
  else
    return (size_t)0U;
}

static size_t
CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_array_(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t off
)
{
  size_t rem = Pulse_Lib_Slice_len__uint8_t(out) - off;
  CBOR_Spec_Raw_EverParse_header
  h = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY, len);
  if (CBOR_Pulse_Raw_EverParse_Serialize_size_header(h, &rem))
  {
    size_t llen = CBOR_Pulse_Raw_EverParse_Serialize_write_header(h, out, off);
    Pulse_Lib_Slice_slice__uint8_t sp1 = Pulse_Lib_Slice_split__uint8_t(out, llen).fst;
    if (!(off == (size_t)0U || off == Pulse_Lib_Slice_len__uint8_t(sp1)))
    {
      size_t pn = Pulse_Lib_Slice_len__uint8_t(sp1);
      size_t pl = off;
      while (pl > (size_t)0U)
      {
        size_t l1 = pl;
        size_t l_ = pn % l1;
        pn = l1;
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
            idx_ = idx + off - (size_t)0U;
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
CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_array(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t off
)
{
  return CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_array_(len, out, off);
}

static size_t
CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_string(
  uint8_t ty,
  CBOR_Spec_Raw_Base_raw_uint64 off,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  size_t soff = (size_t)off.value;
  size_t rem = Pulse_Lib_Slice_len__uint8_t(out) - soff;
  CBOR_Spec_Raw_EverParse_header h = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(ty, off);
  if (CBOR_Pulse_Raw_EverParse_Serialize_size_header(h, &rem))
  {
    size_t llen = CBOR_Pulse_Raw_EverParse_Serialize_write_header(h, out, soff);
    Pulse_Lib_Slice_slice__uint8_t sp1 = Pulse_Lib_Slice_split__uint8_t(out, llen).fst;
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
            idx_ = idx + soff - (size_t)0U;
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
CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_map_(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t off
)
{
  size_t rem = Pulse_Lib_Slice_len__uint8_t(out) - off;
  CBOR_Spec_Raw_EverParse_header
  h = CBOR_Spec_Raw_EverParse_raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP, len);
  if (CBOR_Pulse_Raw_EverParse_Serialize_size_header(h, &rem))
  {
    size_t llen = CBOR_Pulse_Raw_EverParse_Serialize_write_header(h, out, off);
    Pulse_Lib_Slice_slice__uint8_t sp1 = Pulse_Lib_Slice_split__uint8_t(out, llen).fst;
    if (!(off == (size_t)0U || off == Pulse_Lib_Slice_len__uint8_t(sp1)))
    {
      size_t pn = Pulse_Lib_Slice_len__uint8_t(sp1);
      size_t pl = off;
      while (pl > (size_t)0U)
      {
        size_t l1 = pl;
        size_t l_ = pn % l1;
        pn = l1;
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
            idx_ = idx + off - (size_t)0U;
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
CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_map(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t off
)
{
  return CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_map_(len, out, off);
}

static FStar_Pervasives_Native_option__uint8_t
CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_simple_value(cbor_raw x)
{
  if (x.tag == CBOR_Case_Simple)
    return
      (
        (FStar_Pervasives_Native_option__uint8_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = x.case_CBOR_Case_Simple
        }
      );
  else
    return ((FStar_Pervasives_Native_option__uint8_t){ .tag = FStar_Pervasives_Native_None });
}

static uint8_t CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_simple_value(cbor_raw x)
{
  FStar_Pervasives_Native_option__uint8_t
  x0 = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_simple_value(x);
  if (x0.tag == FStar_Pervasives_Native_Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct FStar_Pervasives_Native_option__uint64_t_s
{
  FStar_Pervasives_Native_option__uint8_t_tags tag;
  uint64_t v;
}
FStar_Pervasives_Native_option__uint64_t;

static FStar_Pervasives_Native_option__uint64_t
CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_int64_value(cbor_raw x)
{
  if (x.tag == CBOR_Case_Int)
    return
      (
        (FStar_Pervasives_Native_option__uint64_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = x.case_CBOR_Case_Int.cbor_int_value
        }
      );
  else
    return ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
}

static uint64_t CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_int64_value(cbor_raw x)
{
  FStar_Pervasives_Native_option__uint64_t
  x0 = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_int64_value(x);
  if (x0.tag == FStar_Pervasives_Native_Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static FStar_Pervasives_Native_option__uint64_t
CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_tagged_tag(cbor_raw x)
{
  if (x.tag == CBOR_Case_Tagged)
    return
      (
        (FStar_Pervasives_Native_option__uint64_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = x.case_CBOR_Case_Tagged.cbor_tagged_tag.value
        }
      );
  else if (x.tag == CBOR_Case_Tagged_Serialized)
    return
      (
        (FStar_Pervasives_Native_option__uint64_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = x.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag.value
        }
      );
  else
    return ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
}

static uint64_t CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_tagged_tag(cbor_raw x)
{
  FStar_Pervasives_Native_option__uint64_t
  x0 = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_tagged_tag(x);
  if (x0.tag == FStar_Pervasives_Native_Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static FStar_Pervasives_Native_option__uint64_t
CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_array_length(cbor_raw x)
{
  if (x.tag == CBOR_Case_Array)
    return
      (
        (FStar_Pervasives_Native_option__uint64_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = (uint64_t)LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_CBOR_Case_Array.cbor_array_ptr)
        }
      );
  else
    return ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
}

static uint64_t CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_array_length(cbor_raw x)
{
  FStar_Pervasives_Native_option__uint64_t
  x0 = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_array_length(x);
  if (x0.tag == FStar_Pervasives_Native_Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static FStar_Pervasives_Native_option__uint64_t
CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_map_length(cbor_raw x)
{
  if (x.tag == CBOR_Case_Map)
    return
      (
        (FStar_Pervasives_Native_option__uint64_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = (uint64_t)LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_CBOR_Case_Map.cbor_map_ptr)
        }
      );
  else
    return ((FStar_Pervasives_Native_option__uint64_t){ .tag = FStar_Pervasives_Native_None });
}

static uint64_t CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_map_length(cbor_raw x)
{
  FStar_Pervasives_Native_option__uint64_t
  x0 = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_map_length(x);
  if (x0.tag == FStar_Pervasives_Native_Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_raw CBOR_Pulse_Raw_EverParse_Make_cbor_mk_simple_value(uint8_t v)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = v } });
}

static cbor_raw CBOR_Pulse_Raw_EverParse_Make_cbor_mk_int64(uint8_t ty, uint64_t v)
{
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Int,
        {
          .case_CBOR_Case_Int = {
            .cbor_int_type = ty,
            .cbor_int_size = CBOR_Spec_Raw_Optimal_mk_raw_uint64(v).size,
            .cbor_int_value = v
          }
        }
      }
    );
}

static cbor_raw
CBOR_Pulse_Raw_EverParse_Make_cbor_mk_string(uint8_t ty, Pulse_Lib_Slice_slice__uint8_t s)
{
  return
    (
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
    );
}

static cbor_raw CBOR_Pulse_Raw_EverParse_Make_cbor_mk_tagged(uint64_t tag, cbor_raw *r)
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

static cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_Raw_EverParse_Make_cbor_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  return
    (
      (cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .cbor_map_entry_key = xk,
        .cbor_map_entry_value = xv
      }
    );
}

static cbor_raw
CBOR_Pulse_Raw_EverParse_Make_cbor_mk_array(
  uint8_t len_size,
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ml
)
{
  LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Array,
        { .case_CBOR_Case_Array = { .cbor_array_length_size = len_size, .cbor_array_ptr = ml } }
      }
    );
}

static cbor_raw
CBOR_Pulse_Raw_EverParse_Make_cbor_mk_map(
  uint8_t len_size,
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml
)
{
  LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Map,
        { .case_CBOR_Case_Map = { .cbor_map_length_size = len_size, .cbor_map_ptr = ml } }
      }
    );
}

static cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_Raw_EverParse_ReadMapEntry_cbor_raw_read_map_entry(
  Pulse_Lib_Slice_slice__uint8_t input
)
{
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut =
    Pulse_Lib_Slice_split__uint8_t(input,
      CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(input, (size_t)0U));
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.snd;
  cbor_raw xk = CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read(scrut1.fst);
  return
    CBOR_Pulse_Raw_EverParse_Make_cbor_mk_map_entry(xk,
      CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read(input2));
}

typedef struct
K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_s
{
  cbor_raw fst;
  cbor_det_array_iterator_t snd;
}
K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t;

static K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t
CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_raw_data_item(cbor_det_array_iterator_t x)
{
  cbor_det_array_iterator_t r = x;
  cbor_det_array_iterator_t scrut0 = r;
  LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw scrut1;
  if (scrut0.tag == IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IBase;
    size_t
    len_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
      scrut1 =
        KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "Pulse.Lib.Dv.unreachable");
    else
    {
      LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              {
                .case_EElement = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_ESerialized,
              {
                .case_ESerialized = Pulse_Lib_Slice_split__uint8_t(pl_suffix,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        r =
          (
            (cbor_det_array_iterator_t){
              .tag = IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
        scrut1 = x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n = pn;
            size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
            pn = n - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        r = ((cbor_det_array_iterator_t){ .tag = IBase, { .case_IBase = ite } });
        scrut1 = x1;
      }
    }
  }
  else if (scrut0.tag == IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = scrut0.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IPair.before;
    size_t
    len_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
      scrut1 =
        KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "Pulse.Lib.Dv.unreachable");
    else
    {
      LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              {
                .case_EElement = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_ESerialized,
              {
                .case_ESerialized = Pulse_Lib_Slice_split__uint8_t(pl_suffix,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        size_t
        total_sz =
          LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        cbor_det_array_iterator_t ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (cbor_det_array_iterator_t){
                .tag = IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = ml;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz;
          bool
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t
              child_n_before =
                LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v,
                  cur_n_v,
                  cb);
              if (child_n_before > (size_t)0U)
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
                size_t
                child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n = pn;
                size_t
                offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                pn = n - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_ =
            FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz1 =
            FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz - len_sz1;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite1;
          if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = ml.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (rest_sz == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          len_sz1).snd,
                        rest_sz).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = len_sz1;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n = pn;
                size_t
                offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
                pn = n - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = rest_sz,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = ml.case_Append.after;
            size_t oa = ml.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = ml.case_Append.before;
            size_t ob = ml.case_Append.ob;
            size_t cb = ml.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz1, rest_sz, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz1, rest_sz, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz1, ob, cb);
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(len_sz1, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (cbor_det_array_iterator_t){
                .tag = IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        r = ite0;
        scrut1 = x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n = pn;
            size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
            pn = n - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        r =
          (
            (cbor_det_array_iterator_t){
              .tag = IPair,
              { .case_IPair = { .before = ite, .after = ml } }
            }
          );
        scrut1 = x1;
      }
    }
  }
  else
    scrut1 =
      KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        "unreachable (pattern matches are exhaustive in F*)");
  cbor_raw elt;
  if (scrut1.tag == LowParse_PulseParse_Iterator_EElement)
    elt = scrut1.case_EElement;
  else if (scrut1.tag == LowParse_PulseParse_Iterator_ESerialized)
    elt = CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read(scrut1.case_ESerialized);
  else
    elt = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
  return
    (
      (K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t){
        .fst = elt,
        .snd = r
      }
    );
}

typedef struct
K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_s
{
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw fst;
  cbor_det_map_iterator_t snd;
}
K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t;

static K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t
CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_map_entry_raw_data_item(
  cbor_det_map_iterator_t x
)
{
  cbor_det_map_iterator_t r = x;
  cbor_det_map_iterator_t scrut0 = r;
  LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  scrut1;
  if (scrut0.tag == IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IBase;
    size_t
    len_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
      scrut1 =
        KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "Pulse.Lib.Dv.unreachable");
    else
    {
      LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              {
                .case_EElement = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t
          offset_ =
            CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
              poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_ESerialized,
              {
                .case_ESerialized = Pulse_Lib_Slice_split__uint8_t(pl_suffix,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl_suffix,
                    (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        r =
          (
            (cbor_det_map_iterator_t){
              .tag = IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
        scrut1 = x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n = pn;
            size_t
            offset_ =
              CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                poffset);
            pn = n - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        r = ((cbor_det_map_iterator_t){ .tag = IBase, { .case_IBase = ite } });
        scrut1 = x1;
      }
    }
  }
  else if (scrut0.tag == IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = scrut0.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IPair.before;
    size_t
    len_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
      scrut1 =
        KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "Pulse.Lib.Dv.unreachable");
    else
    {
      LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_EElement,
              {
                .case_EElement = Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t
          offset_ =
            CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
              poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_ESerialized,
              {
                .case_ESerialized = Pulse_Lib_Slice_split__uint8_t(pl_suffix,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl_suffix,
                    (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        size_t
        total_sz =
          LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        cbor_det_map_iterator_t ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (cbor_det_map_iterator_t){
                .tag = IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = ml;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz;
          bool
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t
              child_n_before =
                LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v,
                  cur_n_v,
                  cb);
              if (child_n_before > (size_t)0U)
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t
                child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
                size_t
                child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue =
                  !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n = pn;
                size_t
                offset_ =
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                    poffset);
                pn = n - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_ =
            FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz1 =
            FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz - len_sz1;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite1;
          if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = ml.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (rest_sz == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          len_sz1).snd,
                        rest_sz).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = len_sz1;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n = pn;
                size_t
                offset_ =
                  CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                    poffset);
                pn = n - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = rest_sz,
                        .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = ml.case_Append.after;
            size_t oa = ml.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = ml.case_Append.before;
            size_t ob = ml.case_Append.ob;
            size_t cb = ml.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz1, rest_sz, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz1, rest_sz, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz1, ob, cb);
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = LowParse_PulseParse_Iterator_append_off_after_sz(len_sz1, oa, cb),
                      .after = after
                    }
                  }
                }
              );
          }
          else
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (cbor_det_map_iterator_t){
                .tag = IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        r = ite0;
        scrut1 = x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n = pn;
            size_t
            offset_ =
              CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
                poffset);
            pn = n - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        r =
          (
            (cbor_det_map_iterator_t){
              .tag = IPair,
              { .case_IPair = { .before = ite, .after = ml } }
            }
          );
        scrut1 = x1;
      }
    }
  }
  else
    scrut1 =
      KRML_EABORT(LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        "unreachable (pattern matches are exhaustive in F*)");
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw elt;
  if (scrut1.tag == LowParse_PulseParse_Iterator_EElement)
    elt = scrut1.case_EElement;
  else if (scrut1.tag == LowParse_PulseParse_Iterator_ESerialized)
    elt = CBOR_Pulse_Raw_EverParse_ReadMapEntry_cbor_raw_read_map_entry(scrut1.case_ESerialized);
  else
    elt =
      KRML_EABORT(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        "unreachable (pattern matches are exhaustive in F*)");
  return
    (
      (K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t){
        .fst = elt,
        .snd = r
      }
    );
}

static int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(cbor_raw x1, cbor_raw x2)
{
  uint8_t ty1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_major_type_aux(x1);
  int16_t
  c =
    CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(ty1,
      CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_major_type_aux(x2));
  if (c == (int16_t)0)
    if (ty1 == CBOR_MAJOR_TYPE_UINT64 || ty1 == CBOR_MAJOR_TYPE_NEG_INT64)
    {
      CBOR_Spec_Raw_Base_raw_uint64 ru1;
      if (x1.tag == CBOR_Case_Int)
      {
        cbor_int v = x1.case_CBOR_Case_Int;
        ru1 =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = v.cbor_int_size, .value = v.cbor_int_value });
      }
      else
        ru1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Int)
      {
        cbor_int v = x2.case_CBOR_Case_Int;
        ite =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = v.cbor_int_size, .value = v.cbor_int_value });
      }
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      return CBOR_Pulse_Raw_EverParse_Det_Compare_Base_impl_raw_uint64_compare(ru1, ite);
    }
    else if (ty1 == CBOR_MAJOR_TYPE_BYTE_STRING || ty1 == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      CBOR_Spec_Raw_Base_raw_uint64 len1;
      if (x1.tag == CBOR_Case_String)
      {
        cbor_string v = x1.case_CBOR_Case_String;
        len1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_string_size,
              .value = (uint64_t)Pulse_Lib_Slice_len__uint8_t(v.cbor_string_ptr)
            }
          );
      }
      else
        len1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_String)
      {
        cbor_string v = x2.case_CBOR_Case_String;
        ite =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_string_size,
              .value = (uint64_t)Pulse_Lib_Slice_len__uint8_t(v.cbor_string_ptr)
            }
          );
      }
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      int16_t cl = CBOR_Pulse_Raw_EverParse_Det_Compare_Base_impl_raw_uint64_compare(len1, ite);
      if (cl == (int16_t)0)
      {
        Pulse_Lib_Slice_slice__uint8_t
        s1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string_aux(x1);
        return
          CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(s1,
            CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string_aux(x2));
      }
      else
        return cl;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_TAGGED)
    {
      CBOR_Spec_Raw_Base_raw_uint64 tag1;
      if (x1.tag == CBOR_Case_Tagged)
        tag1 = x1.case_CBOR_Case_Tagged.cbor_tagged_tag;
      else if (x1.tag == CBOR_Case_Tagged_Serialized)
        tag1 = x1.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag;
      else
        tag1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Tagged)
        ite = x2.case_CBOR_Case_Tagged.cbor_tagged_tag;
      else if (x2.tag == CBOR_Case_Tagged_Serialized)
        ite = x2.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag;
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      int16_t ct = CBOR_Pulse_Raw_EverParse_Det_Compare_Base_impl_raw_uint64_compare(tag1, ite);
      if (ct == (int16_t)0)
        return CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_tagged(x1, x2);
      else
        return ct;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_ARRAY)
    {
      CBOR_Spec_Raw_Base_raw_uint64 len1;
      if (x1.tag == CBOR_Case_Array)
      {
        cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = x1.case_CBOR_Case_Array;
        len1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_array_length_size,
              .value = (uint64_t)LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_array_ptr)
            }
          );
      }
      else
        len1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Array)
      {
        cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = x2.case_CBOR_Case_Array;
        ite =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_array_length_size,
              .value = (uint64_t)LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_array_ptr)
            }
          );
      }
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      int16_t cl = CBOR_Pulse_Raw_EverParse_Det_Compare_Base_impl_raw_uint64_compare(len1, ite);
      if (cl == (int16_t)0)
        return
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_array(x1,
            x2,
            (size_t)len1.value);
      else
        return cl;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_MAP)
    {
      CBOR_Spec_Raw_Base_raw_uint64 len1;
      if (x1.tag == CBOR_Case_Map)
      {
        cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = x1.case_CBOR_Case_Map;
        len1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_map_length_size,
              .value = (uint64_t)LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_map_ptr)
            }
          );
      }
      else
        len1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Map)
      {
        cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = x2.case_CBOR_Case_Map;
        ite =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_map_length_size,
              .value = (uint64_t)LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_map_ptr)
            }
          );
      }
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      int16_t cl = CBOR_Pulse_Raw_EverParse_Det_Compare_Base_impl_raw_uint64_compare(len1, ite);
      if (cl == (int16_t)0)
        return
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_map(x1,
            x2,
            (size_t)len1.value);
      else
        return cl;
    }
    else
    {
      uint8_t sv1;
      if (x1.tag == CBOR_Case_Simple)
        sv1 = x1.case_CBOR_Case_Simple;
      else
        sv1 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      uint8_t ite;
      if (x2.tag == CBOR_Case_Simple)
        ite = x2.case_CBOR_Case_Simple;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      return CBOR_Pulse_Raw_Compare_Bytes_impl_uint8_compare(sv1, ite);
    }
  else
    return c;
}

int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_tagged(cbor_raw x1, cbor_raw x2)
{
  LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  e1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_tagged_payload_aux_eos(x1);
  LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  e2 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_tagged_payload_aux_eos(x2);
  if (e1.tag == LowParse_PulseParse_Iterator_EElement)
  {
    cbor_raw xx1 = e1.case_EElement;
    if (e2.tag == LowParse_PulseParse_Iterator_EElement)
      return CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(xx1, e2.case_EElement);
    else if (e2.tag == LowParse_PulseParse_Iterator_ESerialized)
      return
        CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(xx1,
          CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(e2.case_ESerialized));
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (e1.tag == LowParse_PulseParse_Iterator_ESerialized)
  {
    Pulse_Lib_Slice_slice__uint8_t s1 = e1.case_ESerialized;
    if (e2.tag == LowParse_PulseParse_Iterator_EElement)
    {
      cbor_raw xx2 = e2.case_EElement;
      return
        CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(s1),
          xx2);
    }
    else if (e2.tag == LowParse_PulseParse_Iterator_ESerialized)
    {
      Pulse_Lib_Slice_slice__uint8_t s2 = e2.case_ESerialized;
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut0 =
        Pulse_Lib_Slice_split__uint8_t(s1,
          CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(s1, (size_t)0U));
      Pulse_Lib_Slice_slice__uint8_t
      ex1 =
        (
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).fst;
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut =
        Pulse_Lib_Slice_split__uint8_t(s2,
          CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(s2, (size_t)0U));
      return
        CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(ex1,
          (
            (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
              .fst = scrut.fst,
              .snd = scrut.snd
            }
          ).fst);
    }
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

int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_array(
  cbor_raw x1,
  cbor_raw x2,
  size_t len
)
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ar_ml1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array_aux(x1);
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ar_ml2 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array_aux(x2);
  cbor_det_array_iterator_t
  r_it1 = CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_start_raw_data_item_fuel(ar_ml1);
  cbor_det_array_iterator_t
  r_it2 = CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_start_raw_data_item_fuel(ar_ml2);
  int16_t r_acc = (int16_t)0;
  size_t r_cnt = (size_t)0U;
  while (r_cnt < len && r_acc == (int16_t)0)
  {
    LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    e1 = CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_eos_raw_data_item_fuel_byref(&r_it1);
    LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    e2 = CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_eos_raw_data_item_fuel_byref(&r_it2);
    size_t old_cnt = r_cnt;
    if (e1.tag == LowParse_PulseParse_Iterator_EElement)
    {
      cbor_raw xx1 = e1.case_EElement;
      if (e2.tag == LowParse_PulseParse_Iterator_EElement)
      {
        r_acc = CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(xx1, e2.case_EElement);
        r_cnt = old_cnt + (size_t)1U;
      }
      else if (e2.tag == LowParse_PulseParse_Iterator_ESerialized)
      {
        r_acc =
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(xx1,
            CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(e2.case_ESerialized));
        r_cnt = old_cnt + (size_t)1U;
      }
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    else if (e1.tag == LowParse_PulseParse_Iterator_ESerialized)
    {
      Pulse_Lib_Slice_slice__uint8_t s1 = e1.case_ESerialized;
      if (e2.tag == LowParse_PulseParse_Iterator_EElement)
      {
        cbor_raw xx2 = e2.case_EElement;
        r_acc =
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(s1),
            xx2);
        r_cnt = old_cnt + (size_t)1U;
      }
      else if (e2.tag == LowParse_PulseParse_Iterator_ESerialized)
      {
        r_acc =
          CBOR_Pulse_Raw_EverParse_Det_Compare_Base_byte_compare_pts_to_parsed_data_item(s1,
            e2.case_ESerialized);
        r_cnt = old_cnt + (size_t)1U;
      }
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
  return r_acc;
}

typedef struct
K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  cbor_raw fst;
  cbor_raw snd;
}
K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static cbor_raw
FStar_Pervasives_Native_fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw x
)
{
  return x.fst;
}

static cbor_raw
FStar_Pervasives_Native_snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw x
)
{
  return x.snd;
}

int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_map(
  cbor_raw x1,
  cbor_raw x2,
  size_t len
)
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  map_ml1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map_aux(x1);
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  map_ml2 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map_aux(x2);
  cbor_det_map_iterator_t
  r_it1 =
    CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_start_map_entry_raw_data_item_fuel(map_ml1);
  cbor_det_map_iterator_t
  r_it2 =
    CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_start_map_entry_raw_data_item_fuel(map_ml2);
  int16_t r_acc = (int16_t)0;
  size_t r_cnt = (size_t)0U;
  while (r_cnt < len && r_acc == (int16_t)0)
  {
    LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    e1 =
      CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_eos_map_entry_raw_data_item_fuel_byref(&r_it1);
    LowParse_PulseParse_Iterator_elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    e2 =
      CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_eos_map_entry_raw_data_item_fuel_byref(&r_it2);
    size_t old_cnt = r_cnt;
    if (e1.tag == LowParse_PulseParse_Iterator_EElement)
    {
      cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw entry1 = e1.case_EElement;
      if (e2.tag == LowParse_PulseParse_Iterator_EElement)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw entry2 = e2.case_EElement;
        int16_t
        ck =
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(entry1.cbor_map_entry_key,
            entry2.cbor_map_entry_key);
        if (ck == (int16_t)0)
        {
          r_acc =
            CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(entry1.cbor_map_entry_value,
              entry2.cbor_map_entry_value);
          r_cnt = old_cnt + (size_t)1U;
        }
        else
        {
          r_acc = ck;
          r_cnt = old_cnt + (size_t)1U;
        }
      }
      else if (e2.tag == LowParse_PulseParse_Iterator_ESerialized)
      {
        Pulse_Lib_Slice_slice__uint8_t s2 = e2.case_ESerialized;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut =
          Pulse_Lib_Slice_split__uint8_t(s2,
            CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(s2, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
        Pulse_Lib_Slice_slice__uint8_t input2 = scrut0.snd;
        cbor_raw res1 = CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(scrut0.fst);
        K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        pair = { .fst = res1, .snd = CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(input2) };
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        entry2 =
          {
            .cbor_map_entry_key = FStar_Pervasives_Native_fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair),
            .cbor_map_entry_value = FStar_Pervasives_Native_snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair)
          };
        int16_t
        ck =
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(entry1.cbor_map_entry_key,
            entry2.cbor_map_entry_key);
        if (ck == (int16_t)0)
        {
          r_acc =
            CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(entry1.cbor_map_entry_value,
              entry2.cbor_map_entry_value);
          r_cnt = old_cnt + (size_t)1U;
        }
        else
        {
          r_acc = ck;
          r_cnt = old_cnt + (size_t)1U;
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
    else if (e1.tag == LowParse_PulseParse_Iterator_ESerialized)
    {
      Pulse_Lib_Slice_slice__uint8_t s1 = e1.case_ESerialized;
      if (e2.tag == LowParse_PulseParse_Iterator_EElement)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw entry2 = e2.case_EElement;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut =
          Pulse_Lib_Slice_split__uint8_t(s1,
            CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(s1, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
        Pulse_Lib_Slice_slice__uint8_t input2 = scrut0.snd;
        cbor_raw res1 = CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(scrut0.fst);
        K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        pair = { .fst = res1, .snd = CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(input2) };
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        entry1 =
          {
            .cbor_map_entry_key = FStar_Pervasives_Native_fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair),
            .cbor_map_entry_value = FStar_Pervasives_Native_snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair)
          };
        int16_t
        ck =
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(entry1.cbor_map_entry_key,
            entry2.cbor_map_entry_key);
        if (ck == (int16_t)0)
        {
          r_acc =
            CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(entry1.cbor_map_entry_value,
              entry2.cbor_map_entry_value);
          r_cnt = old_cnt + (size_t)1U;
        }
        else
        {
          r_acc = ck;
          r_cnt = old_cnt + (size_t)1U;
        }
      }
      else if (e2.tag == LowParse_PulseParse_Iterator_ESerialized)
      {
        r_acc = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(s1, e2.case_ESerialized);
        r_cnt = old_cnt + (size_t)1U;
      }
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
  return r_acc;
}

static int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_call(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(x1, x2);
}

static int16_t CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_call(x1, x2);
}

static Pulse_Lib_Slice_slice__uint8_t
Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

static size_t
CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_det_serialize_arrayptr(
  cbor_raw x,
  uint8_t *output,
  size_t output_len
)
{
  return
    CBOR_Pulse_Raw_EverParse_Serialize_cbor_serialize(x,
      Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(output, output_len));
}

static Pulse_Lib_Slice_slice__uint8_t
FStar_Pervasives_Native_fst__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t(
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t x
)
{
  return x.fst;
}

static size_t
CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_det_serialize_safe_arrayptr(
  cbor_raw x,
  uint8_t *output,
  size_t output_len
)
{
  Pulse_Lib_Slice_slice__uint8_t
  s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(output, output_len);
  size_t sz = CBOR_Pulse_Raw_EverParse_Serialize_cbor_size(x, output_len);
  if (sz == (size_t)0U)
    return (size_t)0U;
  else
    return
      CBOR_Pulse_Raw_EverParse_Serialize_cbor_serialize(x,
        FStar_Pervasives_Native_fst__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t(Pulse_Lib_Slice_split__uint8_t(s,
            sz)));
}

static void
Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a,
  size_t i,
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v
)
{
  a.elt[i] = v;
}

bool
CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a
)
{
  size_t
  len =
    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a);
  if (len < (size_t)2U)
    return true;
  else
  {
    size_t mi = len / (size_t)2U;
    K___Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut =
      Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
        mi);
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    a2 = scrut.snd;
    if (!CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(scrut.fst))
      return false;
    else if (!CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(a2))
      return false;
    else
    {
      size_t pi1 = (size_t)0U;
      size_t pi2 = mi;
      bool pres = true;
      size_t i10 = pi1;
      size_t i20 = pi2;
      bool res20 = pres;
      bool
      cond =
        res20 &&
          !(i10 == i20 ||
            i20 ==
              Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a));
      while (cond)
      {
        size_t i1 = pi1;
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        x1 =
          Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
            i1);
        size_t i20 = pi2;
        int16_t
        comp =
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare(x1.cbor_map_entry_key,
            Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
              i20).cbor_map_entry_key);
        if (comp == (int16_t)0)
          pres = false;
        else if (comp < (int16_t)0)
          pi1 = i1 + (size_t)1U;
        else
        {
          size_t i2_ = i20 + (size_t)1U;
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ac1 =
            Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
                i2_).fst,
              i1).snd;
          if
          (
            !(i20 - i1 == (size_t)0U ||
              i20 - i1 ==
                Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1))
          )
          {
            size_t
            pn =
              Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1);
            size_t pl = i20 - i1;
            while (pl > (size_t)0U)
            {
              size_t l3 = pl;
              size_t l_ = pn % l3;
              pn = l3;
              pl = l_;
            }
            size_t d = pn;
            size_t
            q =
              Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1)
              / d;
            size_t pi = (size_t)0U;
            while (pi < d)
            {
              size_t i = pi;
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              save =
                Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1,
                  i);
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
                    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1)
                    - (i20 - i1)
                )
                  idx_ =
                    idx -
                      (Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1)
                      - (i20 - i1));
                else
                  idx_ = idx + i20 - i1 - (size_t)0U;
                size_t j_ = j + (size_t)1U;
                Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1,
                  idx,
                  Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1,
                    idx_));
                pj = j_;
                pidx = idx_;
              }
              Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1,
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
          res2 &&
            !(i10 == i2 ||
              i2 ==
                Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a));
      }
      return pres;
    }
  }
}

static bool
CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a
)
{
  return CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(a);
}

cbor_raw cbor_det_reset_perm(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(x);
}

size_t cbor_det_validate(uint8_t *input, size_t input_len)
{
  return
    CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_validate_det(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input,
        input_len));
}

cbor_raw cbor_det_parse(uint8_t *input, size_t len)
{
  Pulse_Lib_Slice_slice__uint8_t
  s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input, len);
  Pulse_Lib_Slice_len__uint8_t(s);
  return CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_parse_valid(s);
}

size_t cbor_det_size(cbor_raw x, size_t bound)
{
  return CBOR_Pulse_Raw_EverParse_Serialize_cbor_size(x, bound);
}

size_t cbor_det_serialize(cbor_raw x, uint8_t *output, size_t output_len)
{
  return CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_det_serialize_arrayptr(x, output, output_len);
}

size_t cbor_det_serialize_safe(cbor_raw x, uint8_t *output, size_t output_len)
{
  return
    CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_det_serialize_safe_arrayptr(x,
      output,
      output_len);
}

bool cbor_det_impl_utf8_correct_from_array(uint8_t *s, size_t len)
{
  return
    CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(s,
        len));
}

cbor_raw cbor_det_mk_simple_value(uint8_t v)
{
  return CBOR_Pulse_Raw_EverParse_Make_cbor_mk_simple_value(v);
}

cbor_raw cbor_det_mk_int64(uint8_t ty, uint64_t v)
{
  return CBOR_Pulse_Raw_EverParse_Make_cbor_mk_int64(ty, v);
}

cbor_raw cbor_det_mk_tagged(uint64_t tag, cbor_raw *r)
{
  CBOR_Spec_Raw_Optimal_mk_raw_uint64(tag);
  return CBOR_Pulse_Raw_EverParse_Make_cbor_mk_tagged(tag, r);
}

bool cbor_det_mk_byte_string_from_arrayptr(uint8_t *a, uint64_t len, cbor_raw *dest)
{
  bool __anf0 = a == NULL;
  if (__anf0 || dest == NULL)
    return false;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t
    s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
    bool ite;
    if (CBOR_MAJOR_TYPE_BYTE_STRING == CBOR_MAJOR_TYPE_TEXT_STRING)
      ite = CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(s);
    else
      ite = true;
    if (ite)
    {
      CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__uint8_t(s));
      *dest = CBOR_Pulse_Raw_EverParse_Make_cbor_mk_string(CBOR_MAJOR_TYPE_BYTE_STRING, s);
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
    Pulse_Lib_Slice_slice__uint8_t
    s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
    if (CBOR_Pulse_Raw_EverParse_UTF8_impl_correct(s))
    {
      CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__uint8_t(s));
      *dest = CBOR_Pulse_Raw_EverParse_Make_cbor_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, s);
      return true;
    }
    else
      return false;
  }
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cbor_raw *a, size_t alen)
{
  return
    ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){ .elt = a, .len = alen });
}

cbor_raw cbor_det_mk_array_from_array(cbor_raw *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s = Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a, (size_t)len);
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml =
    {
      .tag = LowParse_PulseParse_Iterator_Type_Base,
      { .case_Base = { .tag = LowParse_PulseParse_Iterator_Type_Slice, { .case_Slice = s } } }
    };
  return
    CBOR_Pulse_Raw_EverParse_Make_cbor_mk_array(CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)).size,
      ml);
}

cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  cbor_raw xk_ = CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(xk);
  return
    CBOR_Pulse_Raw_EverParse_Make_cbor_mk_map_entry(xk_,
      CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(xv));
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *a,
  size_t alen
)
{
  return
    (
      (Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .elt = a,
        .len = alen
      }
    );
}

cbor_raw
cbor_det_mk_map_from_array(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *a,
  uint64_t len
)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s =
    Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
      (size_t)len);
  cbor_raw dest = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } };
  bool ite;
  if
  (
    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)
    > (size_t)18446744073709551615ULL
  )
    ite = false;
  else if (CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort(s))
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml =
      {
        .tag = LowParse_PulseParse_Iterator_Type_Base,
        { .case_Base = { .tag = LowParse_PulseParse_Iterator_Type_Slice, { .case_Slice = s } } }
      };
    dest =
      CBOR_Pulse_Raw_EverParse_Make_cbor_mk_map(CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)).size,
        ml);
    ite = true;
  }
  else
    ite = false;
  KRML_MAYBE_UNUSED_VAR(ite);
  return dest;
}

bool
cbor_det_mk_map_from_array_safe(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *a,
  uint64_t len,
  cbor_raw *dest
)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s =
    Pulse_Lib_Slice_from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
      (size_t)len);
  if
  (
    Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)
    > (size_t)18446744073709551615ULL
  )
    return false;
  else if (CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort(s))
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml =
      {
        .tag = LowParse_PulseParse_Iterator_Type_Base,
        { .case_Base = { .tag = LowParse_PulseParse_Iterator_Type_Slice, { .case_Slice = s } } }
      };
    *dest =
      CBOR_Pulse_Raw_EverParse_Make_cbor_mk_map(CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)).size,
        ml);
    return true;
  }
  else
    return false;
}

bool cbor_det_equal(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare(x1, x2) == (int16_t)0;
}

uint8_t cbor_det_major_type(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_major_type(x);
}

uint8_t cbor_det_read_simple_value(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_simple_value(x);
}

uint64_t cbor_det_read_uint64(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_int64_value(x);
}

uint64_t cbor_det_get_string_length(cbor_raw x)
{
  return
    (uint64_t)Pulse_Lib_Slice_len__uint8_t(CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string(x));
}

uint64_t cbor_det_get_tagged_tag(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_tagged_tag(x);
}

cbor_raw cbor_det_get_tagged_payload(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_tagged_payload(x);
}

static uint8_t
*Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.elt;
}

uint8_t *cbor_det_get_string(cbor_raw x)
{
  return
    Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string(x));
}

uint64_t cbor_det_get_array_length(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_array_length(x);
}

cbor_det_array_iterator_t cbor_det_array_iterator_start(cbor_raw x)
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array(x);
  size_t
  total_sz =
    LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  if (total_sz == (size_t)0U)
    return
      (
        (cbor_det_array_iterator_t){
          .tag = IBase,
          { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
        }
      );
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    r_node = ml;
    size_t r_off = (size_t)0U;
    size_t r_n = total_sz;
    bool
    pcontinue =
      !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    while (pcontinue)
    {
      size_t cur_off_v = r_off;
      size_t cur_n_v = r_n;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      scrut = r_node;
      if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = scrut.case_Append.after;
        size_t oa = scrut.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = scrut.case_Append.before;
        size_t ob = scrut.case_Append.ob;
        size_t cb = scrut.case_Append.cb;
        size_t
        child_n_before = LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v, cur_n_v, cb);
        if (child_n_before > (size_t)0U)
        {
          size_t
          child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ib = *before;
          r_node = ib;
          r_off = child_off_sz;
          r_n = child_n_before;
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
        }
        else
        {
          size_t child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
          size_t
          child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ia = *after;
          r_node = ia;
          r_off = child_off_sz;
          r_n = child_n_sz;
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
        }
      }
      else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    size_t cur_off_v = r_off;
    size_t cur_n_v = r_n;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut = r_node;
    K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
    res;
    if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = scrut.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw bi_;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi.case_Singleton;
        if (cur_n_v == (size_t)0U)
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    cur_off_v).snd,
                  cur_n_v).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = cur_off_v;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = cur_n_v,
                  .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        bi_ =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      res =
        (
          (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
            .fst = bi_,
            .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
          }
        );
    }
    else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      res =
        KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "Pulse.Lib.Dv.unreachable");
    else
      res =
        KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "unreachable (pattern matches are exhaustive in F*)");
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi_ =
      FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t
    len_sz =
      FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t rest_sz = total_sz - len_sz;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi.case_Singleton;
        if (rest_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    len_sz).snd,
                  rest_sz).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = len_sz;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = rest_sz,
                  .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
      size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
      size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = LowParse_PulseParse_Iterator_append_off_after_sz(len_sz, oa, cb),
                .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_det_array_iterator_t){
          .tag = IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
        }
      );
  }
}

bool cbor_det_array_iterator_is_empty(cbor_det_array_iterator_t x)
{
  if (x.tag == IBase)
    return
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IBase)
      == (size_t)0U;
  else if (x.tag == IPair)
    return
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IPair.before)
      == (size_t)0U;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint64_t cbor_det_array_iterator_length(cbor_det_array_iterator_t x)
{
  if (x.tag == IBase)
    return
      (uint64_t)LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IBase);
  else if (x.tag == IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = x.case_IPair.after;
    size_t
    len_before =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IPair.before);
    return
      (uint64_t)(len_before +
        LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml));
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

cbor_raw cbor_det_array_iterator_next(cbor_det_array_iterator_t *x)
{
  K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t
  scrut = CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_raw_data_item(*x);
  cbor_raw res = scrut.fst;
  *x = scrut.snd;
  return res;
}

cbor_det_array_iterator_t
cbor_det_array_iterator_truncate(cbor_det_array_iterator_t x, uint64_t len)
{
  size_t len_sz = (size_t)len;
  if (x.tag == IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = x.case_IBase;
    LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite;
    if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
      ite =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Empty
          }
        );
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
    {
      cbor_raw *s = bi.case_Singleton;
      if (len_sz == (size_t)0U)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Singleton,
              { .case_Singleton = s }
            }
          );
    }
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
      ite =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Slice,
            {
              .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U).snd,
                len_sz).fst
            }
          }
        );
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
    {
      Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
      size_t pn = (size_t)0U;
      size_t poffset = (size_t)0U;
      while (pn > (size_t)0U)
      {
        size_t n1 = pn;
        size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
        pn = n1 - (size_t)1U;
        poffset = offset_;
      }
      ite =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Serialized,
            {
              .case_Serialized = {
                .count = len_sz,
                .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
              }
            }
          }
        );
    }
    else
      ite =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return ((cbor_det_array_iterator_t){ .tag = IBase, { .case_IBase = ite } });
  }
  else if (x.tag == IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = x.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = x.case_IPair.before;
    size_t
    cb_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    size_t len_before_sz;
    if (len_sz <= cb_sz)
      len_before_sz = len_sz;
    else
      len_before_sz = cb_sz;
    size_t len_after_sz;
    if (len_sz <= cb_sz)
      len_after_sz = (size_t)0U;
    else
      len_after_sz = len_sz - cb_sz;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw bi_;
    if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
      bi_ =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Empty
          }
        );
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
    {
      cbor_raw *s = bi.case_Singleton;
      if (len_before_sz == (size_t)0U)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Singleton,
              { .case_Singleton = s }
            }
          );
    }
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
      bi_ =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Slice,
            {
              .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U).snd,
                len_before_sz).fst
            }
          }
        );
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
    {
      Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
      size_t pn = (size_t)0U;
      size_t poffset = (size_t)0U;
      while (pn > (size_t)0U)
      {
        size_t n1 = pn;
        size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
        pn = n1 - (size_t)1U;
        poffset = offset_;
      }
      bi_ =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Serialized,
            {
              .case_Serialized = {
                .count = len_before_sz,
                .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
              }
            }
          }
        );
    }
    else
      bi_ =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi1 = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite;
      if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi1.case_Singleton;
        if (len_after_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                    (size_t)0U).snd,
                  len_after_sz).fst
              }
            }
          );
      else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = len_after_sz,
                  .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz((size_t)0U, len_after_sz, cb);
      size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz((size_t)0U, len_after_sz, cb);
      size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz((size_t)0U, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = LowParse_PulseParse_Iterator_append_off_after_sz((size_t)0U, oa, cb),
                .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_det_array_iterator_t){
          .tag = IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
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

cbor_raw cbor_det_get_array_item(cbor_raw x, uint64_t i)
{
  cbor_det_array_iterator_t pit = cbor_det_array_iterator_start(x);
  uint64_t pj = 0ULL;
  bool pcont = 0ULL < i;
  while (pcont)
  {
    cbor_det_array_iterator_next(&pit);
    uint64_t j_val = pj;
    pj = j_val + 1ULL;
    pcont = j_val + 1ULL < i;
  }
  return cbor_det_array_iterator_next(&pit);
}

uint64_t cbor_det_get_map_length(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_map_length(x);
}

cbor_det_map_iterator_t cbor_det_map_iterator_start(cbor_raw x)
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map(x);
  size_t
  total_sz =
    LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  if (total_sz == (size_t)0U)
    return
      (
        (cbor_det_map_iterator_t){
          .tag = IBase,
          { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
        }
      );
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    r_node = ml;
    size_t r_off = (size_t)0U;
    size_t r_n = total_sz;
    bool
    pcontinue =
      !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    while (pcontinue)
    {
      size_t cur_off_v = r_off;
      size_t cur_n_v = r_n;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      scrut = r_node;
      if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = scrut.case_Append.after;
        size_t oa = scrut.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = scrut.case_Append.before;
        size_t ob = scrut.case_Append.ob;
        size_t cb = scrut.case_Append.cb;
        size_t
        child_n_before = LowParse_PulseParse_Iterator_append_n_before_sz(cur_off_v, cur_n_v, cb);
        if (child_n_before > (size_t)0U)
        {
          size_t
          child_off_sz = LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v, ob, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ib = *before;
          r_node = ib;
          r_off = child_off_sz;
          r_n = child_n_before;
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
        }
        else
        {
          size_t child_off_sz = LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v, oa, cb);
          size_t
          child_n_sz = LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v, cur_n_v, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ia = *after;
          r_node = ia;
          r_off = child_off_sz;
          r_n = child_n_sz;
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
        }
      }
      else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    size_t cur_off_v = r_off;
    size_t cur_n_v = r_n;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut = r_node;
    K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
    res;
    if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = scrut.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi_;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
        if (cur_n_v == (size_t)0U)
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    cur_off_v).snd,
                  cur_n_v).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = cur_off_v;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t
          offset_ =
            CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
              poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = cur_n_v,
                  .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        bi_ =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      res =
        (
          (K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
            .fst = bi_,
            .snd = LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
          }
        );
    }
    else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      res =
        KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "Pulse.Lib.Dv.unreachable");
    else
      res =
        KRML_EABORT(K___LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "unreachable (pattern matches are exhaustive in F*)");
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi_ =
      FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t
    len_sz =
      FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t rest_sz = total_sz - len_sz;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      ite;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
        if (rest_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(Pulse_Lib_Slice_split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    len_sz).snd,
                  rest_sz).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = len_sz;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t
          offset_ =
            CBOR_Pulse_Raw_EverParse_Validate_jump_nondep_then_raw_data_item_eta(pl,
              poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = rest_sz,
                  .payload = Pulse_Lib_Slice_split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
      size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
      size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = LowParse_PulseParse_Iterator_append_off_after_sz(len_sz, oa, cb),
                .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_det_map_iterator_t){
          .tag = IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
        }
      );
  }
}

bool cbor_det_map_iterator_is_empty(cbor_det_map_iterator_t x)
{
  if (x.tag == IBase)
    return
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IBase)
      == (size_t)0U;
  else if (x.tag == IPair)
    return
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IPair.before)
      == (size_t)0U;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_map_iterator_next(cbor_det_map_iterator_t *x)
{
  K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t
  scrut = CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_map_entry_raw_data_item(*x);
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw res = scrut.fst;
  *x = scrut.snd;
  return res;
}

cbor_raw cbor_det_map_entry_key(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e)
{
  return e.cbor_map_entry_key;
}

cbor_raw cbor_det_map_entry_value(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e)
{
  return e.cbor_map_entry_value;
}

typedef struct FStar_Pervasives_Native_option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  FStar_Pervasives_Native_option__uint8_t_tags tag;
  cbor_raw v;
}
FStar_Pervasives_Native_option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

bool cbor_det_map_get(cbor_raw x, cbor_raw k, cbor_raw *dest)
{
  cbor_det_map_iterator_t it = cbor_det_map_iterator_start(x);
  cbor_det_map_iterator_t pit = it;
  FStar_Pervasives_Native_option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  pres = { .tag = FStar_Pervasives_Native_None };
  bool pcont = !cbor_det_map_iterator_is_empty(it);
  while (pcont)
  {
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    entry = cbor_det_map_iterator_next(&pit);
    if (cbor_det_equal(cbor_det_map_entry_key(entry), k))
    {
      pres =
        (
          (FStar_Pervasives_Native_option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = FStar_Pervasives_Native_Some,
            .v = cbor_det_map_entry_value(entry)
          }
        );
      pcont = false;
    }
    else
      pcont = !cbor_det_map_iterator_is_empty(pit);
  }
  FStar_Pervasives_Native_option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw scrut = pres;
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

size_t cbor_det_serialize_tag_to_array(uint64_t tag, uint8_t *out, size_t out_len)
{
  Pulse_Lib_Slice_slice__uint8_t
  sout = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out, out_len);
  return
    CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_tag(CBOR_Spec_Raw_Optimal_mk_raw_uint64(tag),
      sout);
}

size_t
cbor_det_serialize_array_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off)
{
  Pulse_Lib_Slice_slice__uint8_t
  sout = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out, out_len);
  return
    CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_array(CBOR_Spec_Raw_Optimal_mk_raw_uint64(len),
      sout,
      off);
}

size_t
cbor_det_serialize_string_to_array(uint8_t ty, uint64_t off, uint8_t *out, size_t out_len)
{
  Pulse_Lib_Slice_slice__uint8_t
  sout = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out, out_len);
  return
    CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_string(ty,
      CBOR_Spec_Raw_Optimal_mk_raw_uint64(off),
      sout);
}

bool
cbor_det_serialize_map_insert_to_array(uint8_t *out, size_t out_len, size_t off2, size_t off3)
{
  return
    CBOR_Pulse_Raw_EverParse_Insert_cbor_raw_map_insert(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out,
        out_len),
      off2,
      off3);
}

size_t cbor_det_serialize_map_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off)
{
  Pulse_Lib_Slice_slice__uint8_t
  sout = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(out, out_len);
  return
    CBOR_Pulse_Raw_EverParse_Det_Serialize_cbor_serialize_map(CBOR_Spec_Raw_Optimal_mk_raw_uint64(len),
      sout,
      off);
}

cbor_raw cbor_get_from_freeable(cbor_det_freeable_t_ r)
{
  return r.cbor;
}

void panic____(void)
{
  panic____();
}

static Pulse_Lib_Slice_slice__uint8_t
Pulse_Lib_Slice_from_array__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

static cbor_det_freeable_t_ cbor_copy_impl(cbor_raw c)
{
  size_t size = CBOR_Pulse_Raw_EverParse_Serialize_cbor_size(c, (size_t)0xFFFFFFFFFFFFFFFFULL);
  if (size == (size_t)0U)
    panic____();
  KRML_CHECK_SIZE(sizeof (uint8_t), size);
  uint8_t *buf = KRML_HOST_CALLOC(size, sizeof (uint8_t));
  Pulse_Lib_Slice_slice__uint8_t sl = Pulse_Lib_Slice_from_array__uint8_t(buf, size);
  CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_det_serialize_arrayptr(c,
    Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(sl),
    size);
  Pulse_Lib_Slice_len__uint8_t(sl);
  return
    (
      (cbor_det_freeable_t_){
        .cbor = CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_parse_valid(sl),
        .buf = buf,
        .len = size
      }
    );
}

cbor_det_freeable_t_ cbor_copy(cbor_raw c)
{
  return cbor_copy_impl(c);
}

static void cbor_free_(cbor_det_freeable_t_ x)
{
  KRML_HOST_FREE(x.buf);
}

void cbor_free(cbor_det_freeable_t_ x)
{
  cbor_free_(x);
}

cbor_raw dummy_cbor_det_t(void)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } });
}


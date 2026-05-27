

#include "internal/CBORNondet.h"

#include "CBORNondetType.h"

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

static bool CBOR_Pulse_Raw_Util_eq_Some_true(FStar_Pervasives_Native_option__bool x)
{
  if (x.tag == FStar_Pervasives_Native_Some)
    return x.v;
  else
    return false;
}

static bool CBOR_Pulse_Raw_Util_eq_Some_false(FStar_Pervasives_Native_option__bool x)
{
  if (x.tag == FStar_Pervasives_Native_Some)
    return !x.v;
  else
    return false;
}

static bool CBOR_Pulse_Raw_Util_eq_Some_0sz(FStar_Pervasives_Native_option__size_t x)
{
  if (x.tag == FStar_Pervasives_Native_Some)
    return x.v == (size_t)0U;
  else
    return false;
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

typedef struct FStar_Pervasives_Native_option__uint8_t_s
{
  FStar_Pervasives_Native_option__bool_tags tag;
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

static cbor_raw
Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw a,
  size_t i
)
{
  return a.elt[i];
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

typedef struct
K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t_s
{
  cbor_raw fst;
  cbor_nondet_array_iterator_t snd;
}
K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t;

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

static K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t
CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_raw_data_item_fuel(
  cbor_nondet_array_iterator_t x
)
{
  cbor_nondet_array_iterator_t r = x;
  cbor_nondet_array_iterator_t scrut0 = r;
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
        r =
          (
            (cbor_nondet_array_iterator_t){
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
        r = ((cbor_nondet_array_iterator_t){ .tag = IBase, { .case_IBase = ite } });
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
        cbor_nondet_array_iterator_t ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (cbor_nondet_array_iterator_t){
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
              (cbor_nondet_array_iterator_t){
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
        r =
          (
            (cbor_nondet_array_iterator_t){
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
    elt = CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(scrut1.case_ESerialized);
  else
    elt = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
  return
    (
      (K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t){
        .fst = elt,
        .snd = r
      }
    );
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

typedef struct
K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t_s
{
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw fst;
  cbor_nondet_map_iterator_t snd;
}
K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t;

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

static K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_map_entry_raw_data_item_fuel(
  cbor_nondet_map_iterator_t x
)
{
  cbor_nondet_map_iterator_t r = x;
  cbor_nondet_map_iterator_t scrut0 = r;
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
        r =
          (
            (cbor_nondet_map_iterator_t){
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
        r = ((cbor_nondet_map_iterator_t){ .tag = IBase, { .case_IBase = ite } });
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
        cbor_nondet_map_iterator_t ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (cbor_nondet_map_iterator_t){
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
              (cbor_nondet_map_iterator_t){
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
        r =
          (
            (cbor_nondet_map_iterator_t){
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
  {
    Pulse_Lib_Slice_slice__uint8_t pl = scrut1.case_ESerialized;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut =
      Pulse_Lib_Slice_split__uint8_t(pl,
        CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, (size_t)0U));
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
    Pulse_Lib_Slice_slice__uint8_t input2 = scrut0.snd;
    cbor_raw res1 = CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(scrut0.fst);
    K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    pair = { .fst = res1, .snd = CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(input2) };
    elt =
      (
        (cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .cbor_map_entry_key = FStar_Pervasives_Native_fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair),
          .cbor_map_entry_value = FStar_Pervasives_Native_snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair)
        }
      );
  }
  else
    elt =
      KRML_EABORT(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        "unreachable (pattern matches are exhaustive in F*)");
  return
    (
      (K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t){
        .fst = elt,
        .snd = r
      }
    );
}

bool
CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_aux(
  size_t bound,
  Pulse_Lib_Slice_slice__uint8_t *pl,
  size_t n1
)
{
  size_t pn = n1;
  bool pres = true;
  while (pres && pn > (size_t)0U)
  {
    Pulse_Lib_Slice_slice__uint8_t l = *pl;
    size_t n_ = pn - (size_t)1U;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut =
      Pulse_Lib_Slice_split__uint8_t(l,
        CBOR_Pulse_Raw_EverParse_Validate_jump_header(l, (size_t)0U));
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
    Pulse_Lib_Slice_slice__uint8_t tl_ = scrut3.snd;
    CBOR_Spec_Raw_EverParse_header h = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut3.fst);
    CBOR_Spec_Raw_EverParse_initial_byte_t b = h.fst;
    size_t ite;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
      ite = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h.fst, h.snd);
    else
      ite = (size_t)0U;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut4 = Pulse_Lib_Slice_split__uint8_t(tl_, ite);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut5 = { .fst = scrut4.fst, .snd = scrut4.snd };
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
    Pulse_Lib_Slice_slice__uint8_t
    tl =
      (
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut7.fst,
          .snd = scrut7.snd
        }
      ).snd;
    uint8_t m = CBOR_Spec_Raw_EverParse_get_header_major_type(h);
    if (m == CBOR_MAJOR_TYPE_TAGGED)
      *pl = tl;
    else if (m == CBOR_MAJOR_TYPE_ARRAY)
    {
      *pl = tl;
      pn =
        (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h),
          FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h))
        + n_;
    }
    else if (m == CBOR_MAJOR_TYPE_MAP)
      if (bound == (size_t)0U)
        pres = false;
      else
      {
        *pl = tl;
        size_t
        npairs =
          (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h),
            FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h));
        if
        (
          CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_aux(bound - (size_t)1U,
            pl,
            npairs + npairs)
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
CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_serialized(
  size_t bound,
  size_t n0,
  Pulse_Lib_Slice_slice__uint8_t l0
)
{
  Pulse_Lib_Slice_slice__uint8_t buf = l0;
  return CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_aux(bound, &buf, n0);
}

static bool
FStar_Pervasives_Native_uu___is_None__size_t(FStar_Pervasives_Native_option__size_t projectee)
{
  if (projectee.tag == FStar_Pervasives_Native_None)
    return true;
  else
    return false;
}

static bool
CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_opt(
  FStar_Pervasives_Native_option__size_t bound,
  size_t n0,
  Pulse_Lib_Slice_slice__uint8_t l0
)
{
  if (FStar_Pervasives_Native_uu___is_None__size_t(bound))
    return true;
  else
  {
    size_t ite;
    if (bound.tag == FStar_Pervasives_Native_Some)
      ite = bound.v;
    else
      ite = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
    return CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_serialized(ite, n0, l0);
  }
}

static FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(
  FStar_Pervasives_Native_option__size_t map_bound,
  cbor_raw x1,
  cbor_raw x2
)
{
  uint8_t mt1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_major_type_aux(x1);
  if (mt1 != CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_major_type_aux(x2))
    return
      ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = false });
  else if (mt1 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
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
    return
      (
        (FStar_Pervasives_Native_option__bool){
          .tag = FStar_Pervasives_Native_Some,
          .v = sv1 == ite
        }
      );
  }
  else if (mt1 == CBOR_MAJOR_TYPE_UINT64 || mt1 == CBOR_MAJOR_TYPE_NEG_INT64)
  {
    cbor_int vi1;
    if (x1.tag == CBOR_Case_Int)
      vi1 = x1.case_CBOR_Case_Int;
    else
      vi1 = KRML_EABORT(cbor_int, "unreachable (pattern matches are exhaustive in F*)");
    cbor_int vi2;
    if (x2.tag == CBOR_Case_Int)
      vi2 = x2.case_CBOR_Case_Int;
    else
      vi2 = KRML_EABORT(cbor_int, "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (FStar_Pervasives_Native_option__bool){
          .tag = FStar_Pervasives_Native_Some,
          .v = vi1.cbor_int_type == vi2.cbor_int_type && vi1.cbor_int_value == vi2.cbor_int_value
        }
      );
  }
  else if (mt1 == CBOR_MAJOR_TYPE_BYTE_STRING || mt1 == CBOR_MAJOR_TYPE_TEXT_STRING)
  {
    cbor_string vs1;
    if (x1.tag == CBOR_Case_String)
      vs1 = x1.case_CBOR_Case_String;
    else
      vs1 = KRML_EABORT(cbor_string, "unreachable (pattern matches are exhaustive in F*)");
    cbor_string ite;
    if (x2.tag == CBOR_Case_String)
      ite = x2.case_CBOR_Case_String;
    else
      ite = KRML_EABORT(cbor_string, "unreachable (pattern matches are exhaustive in F*)");
    if (vs1.cbor_string_type != ite.cbor_string_type)
      return
        ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = false });
    else
    {
      Pulse_Lib_Slice_slice__uint8_t
      s1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string_aux(x1);
      return
        (
          (FStar_Pervasives_Native_option__bool){
            .tag = FStar_Pervasives_Native_Some,
            .v = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(s1,
              CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string_aux(x2))
            == (int16_t)0
          }
        );
    }
  }
  else if (mt1 == CBOR_MAJOR_TYPE_TAGGED)
    return
      CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_tagged(map_bound,
        x1,
        x2);
  else if (mt1 == CBOR_MAJOR_TYPE_ARRAY)
  {
    cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
    if (x1.tag == CBOR_Case_Array)
      ite0 = x1.case_CBOR_Case_Array;
    else
      ite0 =
        KRML_EABORT(cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    size_t
    len1 =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ite0.cbor_array_ptr);
    cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite;
    if (x2.tag == CBOR_Case_Array)
      ite = x2.case_CBOR_Case_Array;
    else
      ite =
        KRML_EABORT(cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    if
    (
      len1 !=
        LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ite.cbor_array_ptr)
    )
      return
        ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = false });
    else
      return
        CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_array(map_bound,
          x1,
          x2,
          len1);
  }
  else
    return
      CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_map(map_bound,
        x1,
        x2);
}

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_tagged(
  FStar_Pervasives_Native_option__size_t map_bound,
  cbor_raw x1,
  cbor_raw x2
)
{
  uint64_t tag1;
  if (x1.tag == CBOR_Case_Tagged)
    tag1 = x1.case_CBOR_Case_Tagged.cbor_tagged_tag.value;
  else if (x1.tag == CBOR_Case_Tagged_Serialized)
    tag1 = x1.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag.value;
  else
    tag1 = 0ULL;
  uint64_t ite0;
  if (x2.tag == CBOR_Case_Tagged)
    ite0 = x2.case_CBOR_Case_Tagged.cbor_tagged_tag.value;
  else if (x2.tag == CBOR_Case_Tagged_Serialized)
    ite0 = x2.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag.value;
  else
    ite0 = 0ULL;
  if (tag1 != ite0)
    return
      ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = false });
  else
  {
    cbor_raw payload1;
    if (x1.tag == CBOR_Case_Tagged)
      payload1 = *x1.case_CBOR_Case_Tagged.cbor_tagged_ptr;
    else if (x1.tag == CBOR_Case_Tagged_Serialized)
      payload1 =
        CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(x1.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_ptr);
    else if (x1.tag == CBOR_Case_Invalid)
      payload1 = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x1.tag == CBOR_Case_Int)
      payload1 = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x1.tag == CBOR_Case_Simple)
      payload1 = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x1.tag == CBOR_Case_String)
      payload1 = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x1.tag == CBOR_Case_Array)
      payload1 = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x1.tag == CBOR_Case_Map)
      payload1 = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else
      payload1 = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
    cbor_raw ite;
    if (x2.tag == CBOR_Case_Tagged)
      ite = *x2.case_CBOR_Case_Tagged.cbor_tagged_ptr;
    else if (x2.tag == CBOR_Case_Tagged_Serialized)
      ite =
        CBOR_Pulse_Raw_EverParse_Read_cbor_raw_read_fuel(x2.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_ptr);
    else if (x2.tag == CBOR_Case_Invalid)
      ite = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x2.tag == CBOR_Case_Int)
      ite = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x2.tag == CBOR_Case_Simple)
      ite = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x2.tag == CBOR_Case_String)
      ite = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x2.tag == CBOR_Case_Array)
      ite = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else if (x2.tag == CBOR_Case_Map)
      ite = KRML_EABORT(cbor_raw, "Pulse.Lib.Dv.unreachable");
    else
      ite = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
    return
      CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(map_bound,
        payload1,
        ite);
  }
}

static bool
__eq__FStar_Pervasives_Native_option__bool(
  FStar_Pervasives_Native_option__bool y,
  FStar_Pervasives_Native_option__bool x
)
{
  if (x.tag == FStar_Pervasives_Native_None)
    if (y.tag == FStar_Pervasives_Native_None)
      return true;
    else
      return false;
  else if (x.tag == FStar_Pervasives_Native_Some)
  {
    bool x_v = x.v;
    if (y.tag == FStar_Pervasives_Native_Some)
      return true && y.v == x_v;
    else
      return false;
  }
  else
    return false;
}

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_array(
  FStar_Pervasives_Native_option__size_t map_bound,
  cbor_raw x1,
  cbor_raw x2,
  size_t len
)
{
  if (len == (size_t)0U)
    return
      ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = true });
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ar_ml1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array_aux(x1);
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ar_ml2 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array_aux(x2);
    size_t
    total_sz0 =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ar_ml1);
    cbor_nondet_array_iterator_t ite0;
    if (total_sz0 == (size_t)0U)
      ite0 =
        (
          (cbor_nondet_array_iterator_t){
            .tag = IBase,
            { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
          }
        );
    else
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      r_node = ar_ml1;
      size_t r_off = (size_t)0U;
      size_t r_n = total_sz0;
      bool
      pcontinue =
        !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ar_ml1);
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
            size_t n2 = pn;
            size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
            pn = n2 - (size_t)1U;
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
      size_t rest_sz = total_sz0 - len_sz;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite1;
      if (ar_ml1.tag == LowParse_PulseParse_Iterator_Type_Base)
      {
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        bi = ar_ml1.case_Base;
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
            size_t n2 = pn;
            size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
            pn = n2 - (size_t)1U;
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
      else if (ar_ml1.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = ar_ml1.case_Append.after;
        size_t oa = ar_ml1.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = ar_ml1.case_Append.before;
        size_t ob = ar_ml1.case_Append.ob;
        size_t cb = ar_ml1.case_Append.cb;
        size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
        size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
        size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
        ite1 =
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
        ite1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (cbor_nondet_array_iterator_t){
            .tag = IPair,
            { .case_IPair = { .before = bi_, .after = ite1 } }
          }
        );
    }
    cbor_nondet_array_iterator_t r_it1 = ite0;
    size_t
    total_sz =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ar_ml2);
    cbor_nondet_array_iterator_t ite1;
    if (total_sz == (size_t)0U)
      ite1 =
        (
          (cbor_nondet_array_iterator_t){
            .tag = IBase,
            { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
          }
        );
    else
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      r_node = ar_ml2;
      size_t r_off = (size_t)0U;
      size_t r_n = total_sz;
      bool
      pcontinue =
        !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ar_ml2);
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
            size_t n2 = pn;
            size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
            pn = n2 - (size_t)1U;
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
      if (ar_ml2.tag == LowParse_PulseParse_Iterator_Type_Base)
      {
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        bi = ar_ml2.case_Base;
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
            size_t n2 = pn;
            size_t offset_ = CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item_eta(pl, poffset);
            pn = n2 - (size_t)1U;
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
      else if (ar_ml2.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = ar_ml2.case_Append.after;
        size_t oa = ar_ml2.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = ar_ml2.case_Append.before;
        size_t ob = ar_ml2.case_Append.ob;
        size_t cb = ar_ml2.case_Append.cb;
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
      ite1 =
        (
          (cbor_nondet_array_iterator_t){
            .tag = IPair,
            { .case_IPair = { .before = bi_, .after = ite0 } }
          }
        );
    }
    cbor_nondet_array_iterator_t r_it2 = ite1;
    FStar_Pervasives_Native_option__bool
    r_acc = { .tag = FStar_Pervasives_Native_Some, .v = true };
    size_t r_cnt = (size_t)0U;
    size_t cnt = r_cnt;
    bool
    cond =
      cnt < len &&
        __eq__FStar_Pervasives_Native_option__bool(r_acc,
          ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = true }));
    while (cond)
    {
      K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t
      scrut0 = CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_raw_data_item_fuel(r_it1);
      cbor_raw e1 = scrut0.fst;
      r_it1 = scrut0.snd;
      K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t
      scrut1 = CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_raw_data_item_fuel(r_it2);
      cbor_raw e2 = scrut1.fst;
      r_it2 = scrut1.snd;
      FStar_Pervasives_Native_option__bool
      pair_res =
        CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(map_bound,
          e1,
          e2);
      size_t old_cnt = r_cnt;
      FStar_Pervasives_Native_option__bool scrut = r_acc;
      FStar_Pervasives_Native_option__bool ite;
      if (scrut.tag == FStar_Pervasives_Native_None)
        ite = ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_None });
      else if (scrut.tag == FStar_Pervasives_Native_Some)
        if (scrut.v)
          ite = pair_res;
        else
          ite =
            (
              (FStar_Pervasives_Native_option__bool){
                .tag = FStar_Pervasives_Native_Some,
                .v = false
              }
            );
      else
        ite =
          KRML_EABORT(FStar_Pervasives_Native_option__bool,
            "unreachable (pattern matches are exhaustive in F*)");
      r_acc = ite;
      r_cnt = old_cnt + (size_t)1U;
      size_t cnt = r_cnt;
      cond =
        cnt < len &&
          __eq__FStar_Pervasives_Native_option__bool(r_acc,
            (
              (FStar_Pervasives_Native_option__bool){
                .tag = FStar_Pervasives_Native_Some,
                .v = true
              }
            ));
    }
    return r_acc;
  }
}

typedef struct FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool_s
{
  FStar_Pervasives_Native_option__bool_tags tag;
  FStar_Pervasives_Native_option__bool v;
}
FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool;

static bool
FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool projectee
)
{
  if (projectee.tag == FStar_Pervasives_Native_None)
    return true;
  else
    return false;
}

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_map(
  FStar_Pervasives_Native_option__size_t map_bound,
  cbor_raw x1,
  cbor_raw x2
)
{
  if (map_bound.tag == FStar_Pervasives_Native_Some)
    if (map_bound.v == (size_t)0U)
      return ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_None });
    else
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      map_ml1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map_aux(x1);
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      map_ml2 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map_aux(x2);
      size_t
      len =
        LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
      size_t
      total_sz0 =
        LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
      cbor_nondet_map_iterator_t ite0;
      if (total_sz0 == (size_t)0U)
        ite0 =
          (
            (cbor_nondet_map_iterator_t){
              .tag = IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
      else
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        r_node = map_ml1;
        size_t r_off = (size_t)0U;
        size_t r_n = total_sz0;
        bool
        pcontinue =
          !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
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
        bi_ =
          FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        size_t
        len_sz =
          FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        size_t rest_sz = total_sz0 - len_sz;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite1;
        if (map_ml1.tag == LowParse_PulseParse_Iterator_Type_Base)
        {
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi = map_ml1.case_Base;
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
          ite1 =
            (
              (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Base,
                { .case_Base = ite }
              }
            );
        }
        else if (map_ml1.tag == LowParse_PulseParse_Iterator_Type_Append)
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          *after = map_ml1.case_Append.after;
          size_t oa = map_ml1.case_Append.oa;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          *before = map_ml1.case_Append.before;
          size_t ob = map_ml1.case_Append.ob;
          size_t cb = map_ml1.case_Append.cb;
          size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
          size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
          size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
          ite1 =
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
          ite1 =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        ite0 =
          (
            (cbor_nondet_map_iterator_t){
              .tag = IPair,
              { .case_IPair = { .before = bi_, .after = ite1 } }
            }
          );
      }
      cbor_nondet_map_iterator_t r_it = ite0;
      FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool
      r_done0 = { .tag = FStar_Pervasives_Native_None };
      size_t r_cnt0 = (size_t)0U;
      size_t cnt0 = r_cnt0;
      bool
      cond =
        FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done0) &&
          cnt0 < len;
      while (cond)
      {
        K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
        scrut0 =
          CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_map_entry_raw_data_item_fuel(r_it);
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e = scrut0.fst;
        r_it = scrut0.snd;
        size_t
        len1 =
          LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
        size_t
        total_sz =
          LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
        cbor_nondet_map_iterator_t ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (cbor_nondet_map_iterator_t){
                .tag = IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = map_ml2;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz;
          bool
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
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
          bi_ =
            FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz =
            FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz - len_sz;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite1;
          if (map_ml2.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi = map_ml2.case_Base;
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
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (map_ml2.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = map_ml2.case_Append.after;
            size_t oa = map_ml2.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = map_ml2.case_Append.before;
            size_t ob = map_ml2.case_Append.ob;
            size_t cb = map_ml2.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
            ite1 =
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
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (cbor_nondet_map_iterator_t){
                .tag = IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        cbor_nondet_map_iterator_t r_it1 = ite0;
        FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool
        r_done1 = { .tag = FStar_Pervasives_Native_None };
        size_t r_cnt1 = (size_t)0U;
        size_t cnt = r_cnt1;
        bool
        cond0 =
          FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done1) &&
            cnt < len1;
        while (cond0)
        {
          K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
          scrut =
            CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_map_entry_raw_data_item_fuel(r_it1);
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e1 = scrut.fst;
          r_it1 = scrut.snd;
          FStar_Pervasives_Native_option__size_t ite;
          if (map_bound.tag == FStar_Pervasives_Native_None)
            ite = ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
          else if (map_bound.tag == FStar_Pervasives_Native_Some)
          {
            size_t n1 = map_bound.v;
            if (n1 == (size_t)0U)
              ite =
                (
                  (FStar_Pervasives_Native_option__size_t){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = (size_t)0U
                  }
                );
            else
              ite =
                (
                  (FStar_Pervasives_Native_option__size_t){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = n1 - (size_t)1U
                  }
                );
          }
          else
            ite =
              KRML_EABORT(FStar_Pervasives_Native_option__size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          FStar_Pervasives_Native_option__bool
          scrut0 =
            CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(ite,
              e.cbor_map_entry_key,
              e1.cbor_map_entry_key);
          if (scrut0.tag == FStar_Pervasives_Native_None)
          {
            r_done1 =
              (
                (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = { .tag = FStar_Pervasives_Native_None }
                }
              );
            r_cnt1 = r_cnt1 + (size_t)1U;
          }
          else if (scrut0.tag == FStar_Pervasives_Native_Some)
            if (scrut0.v)
            {
              FStar_Pervasives_Native_option__size_t ite;
              if (map_bound.tag == FStar_Pervasives_Native_None)
                ite =
                  ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
              else if (map_bound.tag == FStar_Pervasives_Native_Some)
              {
                size_t n1 = map_bound.v;
                if (n1 == (size_t)0U)
                  ite =
                    (
                      (FStar_Pervasives_Native_option__size_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = (size_t)0U
                      }
                    );
                else
                  ite =
                    (
                      (FStar_Pervasives_Native_option__size_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = n1 - (size_t)1U
                      }
                    );
              }
              else
                ite =
                  KRML_EABORT(FStar_Pervasives_Native_option__size_t,
                    "unreachable (pattern matches are exhaustive in F*)");
              r_done1 =
                (
                  (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(ite,
                      e.cbor_map_entry_value,
                      e1.cbor_map_entry_value)
                  }
                );
              r_cnt1 = r_cnt1 + (size_t)1U;
            }
            else
              r_cnt1 = r_cnt1 + (size_t)1U;
          else
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
          size_t cnt = r_cnt1;
          cond0 =
            FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done1) &&
              cnt < len1;
        }
        FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool scrut1 = r_done1;
        FStar_Pervasives_Native_option__bool scrut;
        if (scrut1.tag == FStar_Pervasives_Native_Some)
          scrut = scrut1.v;
        else if (scrut1.tag == FStar_Pervasives_Native_None)
          scrut =
            (
              (FStar_Pervasives_Native_option__bool){
                .tag = FStar_Pervasives_Native_Some,
                .v = false
              }
            );
        else
          scrut =
            KRML_EABORT(FStar_Pervasives_Native_option__bool,
              "unreachable (pattern matches are exhaustive in F*)");
        if (scrut.tag == FStar_Pervasives_Native_Some)
          if (scrut.v)
            r_cnt0 = r_cnt0 + (size_t)1U;
          else
          {
            r_done0 =
              (
                (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = { .tag = FStar_Pervasives_Native_Some, .v = false }
                }
              );
            r_cnt0 = r_cnt0 + (size_t)1U;
          }
        else if (scrut.tag == FStar_Pervasives_Native_None)
        {
          r_done0 =
            (
              (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                .tag = FStar_Pervasives_Native_Some,
                .v = { .tag = FStar_Pervasives_Native_None }
              }
            );
          r_cnt0 = r_cnt0 + (size_t)1U;
        }
        else
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
        size_t cnt0 = r_cnt0;
        cond =
          FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done0) &&
            cnt0 < len;
      }
      FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool scrut0 = r_done0;
      FStar_Pervasives_Native_option__bool scrut1;
      if (scrut0.tag == FStar_Pervasives_Native_Some)
        scrut1 = scrut0.v;
      else if (scrut0.tag == FStar_Pervasives_Native_None)
        scrut1 =
          ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = true });
      else
        scrut1 =
          KRML_EABORT(FStar_Pervasives_Native_option__bool,
            "unreachable (pattern matches are exhaustive in F*)");
      if (scrut1.tag == FStar_Pervasives_Native_Some)
        if (scrut1.v)
        {
          size_t
          len =
            LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
          size_t
          total_sz0 =
            LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
          cbor_nondet_map_iterator_t ite0;
          if (total_sz0 == (size_t)0U)
            ite0 =
              (
                (cbor_nondet_map_iterator_t){
                  .tag = IBase,
                  { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
                }
              );
          else
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            r_node = map_ml2;
            size_t r_off = (size_t)0U;
            size_t r_n = total_sz0;
            bool
            pcontinue =
              !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
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
                  child_off_sz =
                    LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v,
                      ob,
                      cb);
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
                  child_n_sz =
                    LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v,
                      cur_n_v,
                      cb);
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
            size_t rest_sz = total_sz0 - len_sz;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite1;
            if (map_ml2.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi = map_ml2.case_Base;
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
              ite1 =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (map_ml2.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = map_ml2.case_Append.after;
              size_t oa = map_ml2.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = map_ml2.case_Append.before;
              size_t ob = map_ml2.case_Append.ob;
              size_t cb = map_ml2.case_Append.cb;
              size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
              size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
              size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
              ite1 =
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
              ite1 =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (cbor_nondet_map_iterator_t){
                  .tag = IPair,
                  { .case_IPair = { .before = bi_, .after = ite1 } }
                }
              );
          }
          cbor_nondet_map_iterator_t r_it = ite0;
          FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool
          r_done = { .tag = FStar_Pervasives_Native_None };
          size_t r_cnt = (size_t)0U;
          size_t cnt0 = r_cnt;
          bool
          cond =
            FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done) &&
              cnt0 < len;
          while (cond)
          {
            K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
            scrut0 =
              CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_map_entry_raw_data_item_fuel(r_it);
            cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e = scrut0.fst;
            r_it = scrut0.snd;
            size_t
            len1 =
              LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
            size_t
            total_sz =
              LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
            cbor_nondet_map_iterator_t ite0;
            if (total_sz == (size_t)0U)
              ite0 =
                (
                  (cbor_nondet_map_iterator_t){
                    .tag = IBase,
                    { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
                  }
                );
            else
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              r_node = map_ml1;
              size_t r_off = (size_t)0U;
              size_t r_n = total_sz;
              bool
              pcontinue =
                !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
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
                    child_off_sz =
                      LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v,
                        ob,
                        cb);
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
                    child_off_sz =
                      LowParse_PulseParse_Iterator_append_off_after_sz(cur_off_v,
                        oa,
                        cb);
                    size_t
                    child_n_sz =
                      LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v,
                        cur_n_v,
                        cb);
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
              ite1;
              if (map_ml1.tag == LowParse_PulseParse_Iterator_Type_Base)
              {
                LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                bi = map_ml1.case_Base;
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
                ite1 =
                  (
                    (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Base,
                      { .case_Base = ite }
                    }
                  );
              }
              else if (map_ml1.tag == LowParse_PulseParse_Iterator_Type_Append)
              {
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                *after = map_ml1.case_Append.after;
                size_t oa = map_ml1.case_Append.oa;
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                *before = map_ml1.case_Append.before;
                size_t ob = map_ml1.case_Append.ob;
                size_t cb = map_ml1.case_Append.cb;
                size_t
                cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
                size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
                size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
                ite1 =
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
                ite1 =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              ite0 =
                (
                  (cbor_nondet_map_iterator_t){
                    .tag = IPair,
                    { .case_IPair = { .before = bi_, .after = ite1 } }
                  }
                );
            }
            cbor_nondet_map_iterator_t r_it1 = ite0;
            FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool
            r_done1 = { .tag = FStar_Pervasives_Native_None };
            size_t r_cnt1 = (size_t)0U;
            size_t cnt = r_cnt1;
            bool
            cond0 =
              FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done1) &&
                cnt < len1;
            while (cond0)
            {
              K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
              scrut =
                CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_map_entry_raw_data_item_fuel(r_it1);
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e1 = scrut.fst;
              r_it1 = scrut.snd;
              FStar_Pervasives_Native_option__size_t ite;
              if (map_bound.tag == FStar_Pervasives_Native_None)
                ite =
                  ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
              else if (map_bound.tag == FStar_Pervasives_Native_Some)
              {
                size_t n1 = map_bound.v;
                if (n1 == (size_t)0U)
                  ite =
                    (
                      (FStar_Pervasives_Native_option__size_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = (size_t)0U
                      }
                    );
                else
                  ite =
                    (
                      (FStar_Pervasives_Native_option__size_t){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = n1 - (size_t)1U
                      }
                    );
              }
              else
                ite =
                  KRML_EABORT(FStar_Pervasives_Native_option__size_t,
                    "unreachable (pattern matches are exhaustive in F*)");
              FStar_Pervasives_Native_option__bool
              scrut0 =
                CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(ite,
                  e.cbor_map_entry_key,
                  e1.cbor_map_entry_key);
              if (scrut0.tag == FStar_Pervasives_Native_None)
              {
                r_done1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = { .tag = FStar_Pervasives_Native_None }
                    }
                  );
                r_cnt1 = r_cnt1 + (size_t)1U;
              }
              else if (scrut0.tag == FStar_Pervasives_Native_Some)
                if (scrut0.v)
                {
                  FStar_Pervasives_Native_option__size_t ite;
                  if (map_bound.tag == FStar_Pervasives_Native_None)
                    ite =
                      (
                        (FStar_Pervasives_Native_option__size_t){
                          .tag = FStar_Pervasives_Native_None
                        }
                      );
                  else if (map_bound.tag == FStar_Pervasives_Native_Some)
                  {
                    size_t n1 = map_bound.v;
                    if (n1 == (size_t)0U)
                      ite =
                        (
                          (FStar_Pervasives_Native_option__size_t){
                            .tag = FStar_Pervasives_Native_Some,
                            .v = (size_t)0U
                          }
                        );
                    else
                      ite =
                        (
                          (FStar_Pervasives_Native_option__size_t){
                            .tag = FStar_Pervasives_Native_Some,
                            .v = n1 - (size_t)1U
                          }
                        );
                  }
                  else
                    ite =
                      KRML_EABORT(FStar_Pervasives_Native_option__size_t,
                        "unreachable (pattern matches are exhaustive in F*)");
                  r_done1 =
                    (
                      (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(ite,
                          e.cbor_map_entry_value,
                          e1.cbor_map_entry_value)
                      }
                    );
                  r_cnt1 = r_cnt1 + (size_t)1U;
                }
                else
                  r_cnt1 = r_cnt1 + (size_t)1U;
              else
              {
                KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                  __FILE__,
                  __LINE__,
                  "unreachable (pattern matches are exhaustive in F*)");
                KRML_HOST_EXIT(255U);
              }
              size_t cnt = r_cnt1;
              cond0 =
                FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done1)
                && cnt < len1;
            }
            FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool scrut1 = r_done1;
            FStar_Pervasives_Native_option__bool scrut;
            if (scrut1.tag == FStar_Pervasives_Native_Some)
              scrut = scrut1.v;
            else if (scrut1.tag == FStar_Pervasives_Native_None)
              scrut =
                (
                  (FStar_Pervasives_Native_option__bool){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = false
                  }
                );
            else
              scrut =
                KRML_EABORT(FStar_Pervasives_Native_option__bool,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (scrut.tag == FStar_Pervasives_Native_Some)
              if (scrut.v)
                r_cnt = r_cnt + (size_t)1U;
              else
              {
                r_done =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = { .tag = FStar_Pervasives_Native_Some, .v = false }
                    }
                  );
                r_cnt = r_cnt + (size_t)1U;
              }
            else if (scrut.tag == FStar_Pervasives_Native_None)
            {
              r_done =
                (
                  (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = { .tag = FStar_Pervasives_Native_None }
                  }
                );
              r_cnt = r_cnt + (size_t)1U;
            }
            else
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
            size_t cnt0 = r_cnt;
            cond =
              FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done) &&
                cnt0 < len;
          }
          FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool scrut = r_done;
          if (scrut.tag == FStar_Pervasives_Native_Some)
            return scrut.v;
          else if (scrut.tag == FStar_Pervasives_Native_None)
            return
              (
                (FStar_Pervasives_Native_option__bool){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = true
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
        else
          return
            (
              (FStar_Pervasives_Native_option__bool){
                .tag = FStar_Pervasives_Native_Some,
                .v = false
              }
            );
      else if (scrut1.tag == FStar_Pervasives_Native_None)
        return ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_None });
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
  else if (map_bound.tag == FStar_Pervasives_Native_None)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    map_ml1 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map_aux(x1);
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    map_ml2 = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map_aux(x2);
    size_t
    len =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
    size_t
    total_sz0 =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
    cbor_nondet_map_iterator_t ite0;
    if (total_sz0 == (size_t)0U)
      ite0 =
        (
          (cbor_nondet_map_iterator_t){
            .tag = IBase,
            { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
          }
        );
    else
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      r_node = map_ml1;
      size_t r_off = (size_t)0U;
      size_t r_n = total_sz0;
      bool
      pcontinue =
        !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
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
      bi_ =
        FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
      size_t
      len_sz =
        FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
      size_t rest_sz = total_sz0 - len_sz;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      ite1;
      if (map_ml1.tag == LowParse_PulseParse_Iterator_Type_Base)
      {
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        bi = map_ml1.case_Base;
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
        ite1 =
          (
            (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Base,
              { .case_Base = ite }
            }
          );
      }
      else if (map_ml1.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = map_ml1.case_Append.after;
        size_t oa = map_ml1.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = map_ml1.case_Append.before;
        size_t ob = map_ml1.case_Append.ob;
        size_t cb = map_ml1.case_Append.cb;
        size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
        size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
        size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
        ite1 =
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
        ite1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (cbor_nondet_map_iterator_t){
            .tag = IPair,
            { .case_IPair = { .before = bi_, .after = ite1 } }
          }
        );
    }
    cbor_nondet_map_iterator_t r_it = ite0;
    FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool
    r_done0 = { .tag = FStar_Pervasives_Native_None };
    size_t r_cnt0 = (size_t)0U;
    size_t cnt0 = r_cnt0;
    bool
    cond =
      FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done0) &&
        cnt0 < len;
    while (cond)
    {
      K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
      scrut0 =
        CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_map_entry_raw_data_item_fuel(r_it);
      cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e = scrut0.fst;
      r_it = scrut0.snd;
      size_t
      len1 =
        LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
      size_t
      total_sz =
        LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
      cbor_nondet_map_iterator_t ite0;
      if (total_sz == (size_t)0U)
        ite0 =
          (
            (cbor_nondet_map_iterator_t){
              .tag = IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
      else
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        r_node = map_ml2;
        size_t r_off = (size_t)0U;
        size_t r_n = total_sz;
        bool
        pcontinue =
          !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
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
        bi_ =
          FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        size_t
        len_sz =
          FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        size_t rest_sz = total_sz - len_sz;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite1;
        if (map_ml2.tag == LowParse_PulseParse_Iterator_Type_Base)
        {
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi = map_ml2.case_Base;
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
          ite1 =
            (
              (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Base,
                { .case_Base = ite }
              }
            );
        }
        else if (map_ml2.tag == LowParse_PulseParse_Iterator_Type_Append)
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          *after = map_ml2.case_Append.after;
          size_t oa = map_ml2.case_Append.oa;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          *before = map_ml2.case_Append.before;
          size_t ob = map_ml2.case_Append.ob;
          size_t cb = map_ml2.case_Append.cb;
          size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
          size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
          size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
          ite1 =
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
          ite1 =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        ite0 =
          (
            (cbor_nondet_map_iterator_t){
              .tag = IPair,
              { .case_IPair = { .before = bi_, .after = ite1 } }
            }
          );
      }
      cbor_nondet_map_iterator_t r_it1 = ite0;
      FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool
      r_done1 = { .tag = FStar_Pervasives_Native_None };
      size_t r_cnt1 = (size_t)0U;
      size_t cnt = r_cnt1;
      bool
      cond0 =
        FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done1) &&
          cnt < len1;
      while (cond0)
      {
        K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
        scrut =
          CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_map_entry_raw_data_item_fuel(r_it1);
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e1 = scrut.fst;
        r_it1 = scrut.snd;
        FStar_Pervasives_Native_option__size_t ite;
        if (map_bound.tag == FStar_Pervasives_Native_None)
          ite = ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
        else if (map_bound.tag == FStar_Pervasives_Native_Some)
        {
          size_t n1 = map_bound.v;
          if (n1 == (size_t)0U)
            ite =
              (
                (FStar_Pervasives_Native_option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = (size_t)0U
                }
              );
          else
            ite =
              (
                (FStar_Pervasives_Native_option__size_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = n1 - (size_t)1U
                }
              );
        }
        else
          ite =
            KRML_EABORT(FStar_Pervasives_Native_option__size_t,
              "unreachable (pattern matches are exhaustive in F*)");
        FStar_Pervasives_Native_option__bool
        scrut0 =
          CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(ite,
            e.cbor_map_entry_key,
            e1.cbor_map_entry_key);
        if (scrut0.tag == FStar_Pervasives_Native_None)
        {
          r_done1 =
            (
              (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                .tag = FStar_Pervasives_Native_Some,
                .v = { .tag = FStar_Pervasives_Native_None }
              }
            );
          r_cnt1 = r_cnt1 + (size_t)1U;
        }
        else if (scrut0.tag == FStar_Pervasives_Native_Some)
          if (scrut0.v)
          {
            FStar_Pervasives_Native_option__size_t ite;
            if (map_bound.tag == FStar_Pervasives_Native_None)
              ite =
                ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
            else if (map_bound.tag == FStar_Pervasives_Native_Some)
            {
              size_t n1 = map_bound.v;
              if (n1 == (size_t)0U)
                ite =
                  (
                    (FStar_Pervasives_Native_option__size_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = (size_t)0U
                    }
                  );
              else
                ite =
                  (
                    (FStar_Pervasives_Native_option__size_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = n1 - (size_t)1U
                    }
                  );
            }
            else
              ite =
                KRML_EABORT(FStar_Pervasives_Native_option__size_t,
                  "unreachable (pattern matches are exhaustive in F*)");
            r_done1 =
              (
                (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(ite,
                    e.cbor_map_entry_value,
                    e1.cbor_map_entry_value)
                }
              );
            r_cnt1 = r_cnt1 + (size_t)1U;
          }
          else
            r_cnt1 = r_cnt1 + (size_t)1U;
        else
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
        size_t cnt = r_cnt1;
        cond0 =
          FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done1) &&
            cnt < len1;
      }
      FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool scrut1 = r_done1;
      FStar_Pervasives_Native_option__bool scrut;
      if (scrut1.tag == FStar_Pervasives_Native_Some)
        scrut = scrut1.v;
      else if (scrut1.tag == FStar_Pervasives_Native_None)
        scrut =
          (
            (FStar_Pervasives_Native_option__bool){
              .tag = FStar_Pervasives_Native_Some,
              .v = false
            }
          );
      else
        scrut =
          KRML_EABORT(FStar_Pervasives_Native_option__bool,
            "unreachable (pattern matches are exhaustive in F*)");
      if (scrut.tag == FStar_Pervasives_Native_Some)
        if (scrut.v)
          r_cnt0 = r_cnt0 + (size_t)1U;
        else
        {
          r_done0 =
            (
              (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                .tag = FStar_Pervasives_Native_Some,
                .v = { .tag = FStar_Pervasives_Native_Some, .v = false }
              }
            );
          r_cnt0 = r_cnt0 + (size_t)1U;
        }
      else if (scrut.tag == FStar_Pervasives_Native_None)
      {
        r_done0 =
          (
            (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
              .tag = FStar_Pervasives_Native_Some,
              .v = { .tag = FStar_Pervasives_Native_None }
            }
          );
        r_cnt0 = r_cnt0 + (size_t)1U;
      }
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
      size_t cnt0 = r_cnt0;
      cond =
        FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done0) &&
          cnt0 < len;
    }
    FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool scrut0 = r_done0;
    FStar_Pervasives_Native_option__bool scrut1;
    if (scrut0.tag == FStar_Pervasives_Native_Some)
      scrut1 = scrut0.v;
    else if (scrut0.tag == FStar_Pervasives_Native_None)
      scrut1 =
        ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = true });
    else
      scrut1 =
        KRML_EABORT(FStar_Pervasives_Native_option__bool,
          "unreachable (pattern matches are exhaustive in F*)");
    if (scrut1.tag == FStar_Pervasives_Native_Some)
      if (scrut1.v)
      {
        size_t
        len =
          LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
        size_t
        total_sz0 =
          LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
        cbor_nondet_map_iterator_t ite0;
        if (total_sz0 == (size_t)0U)
          ite0 =
            (
              (cbor_nondet_map_iterator_t){
                .tag = IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = map_ml2;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz0;
          bool
          pcontinue =
            !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml2);
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
          bi_ =
            FStar_Pervasives_Native_fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz =
            FStar_Pervasives_Native_snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz0 - len_sz;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite1;
          if (map_ml2.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi = map_ml2.case_Base;
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
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (map_ml2.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = map_ml2.case_Append.after;
            size_t oa = map_ml2.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = map_ml2.case_Append.before;
            size_t ob = map_ml2.case_Append.ob;
            size_t cb = map_ml2.case_Append.cb;
            size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
            size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
            size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
            ite1 =
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
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (cbor_nondet_map_iterator_t){
                .tag = IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        cbor_nondet_map_iterator_t r_it = ite0;
        FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool
        r_done = { .tag = FStar_Pervasives_Native_None };
        size_t r_cnt = (size_t)0U;
        size_t cnt0 = r_cnt;
        bool
        cond =
          FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done) &&
            cnt0 < len;
        while (cond)
        {
          K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
          scrut0 =
            CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_map_entry_raw_data_item_fuel(r_it);
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e = scrut0.fst;
          r_it = scrut0.snd;
          size_t
          len1 =
            LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
          size_t
          total_sz =
            LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
          cbor_nondet_map_iterator_t ite0;
          if (total_sz == (size_t)0U)
            ite0 =
              (
                (cbor_nondet_map_iterator_t){
                  .tag = IBase,
                  { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
                }
              );
          else
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            r_node = map_ml1;
            size_t r_off = (size_t)0U;
            size_t r_n = total_sz;
            bool
            pcontinue =
              !LowParse_PulseParse_Iterator_Type_uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(map_ml1);
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
                  child_off_sz =
                    LowParse_PulseParse_Iterator_append_off_before_sz(cur_off_v,
                      ob,
                      cb);
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
                  child_n_sz =
                    LowParse_PulseParse_Iterator_append_n_after_sz(cur_off_v,
                      cur_n_v,
                      cb);
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
            ite1;
            if (map_ml1.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi = map_ml1.case_Base;
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
              ite1 =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (map_ml1.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = map_ml1.case_Append.after;
              size_t oa = map_ml1.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = map_ml1.case_Append.before;
              size_t ob = map_ml1.case_Append.ob;
              size_t cb = map_ml1.case_Append.cb;
              size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
              size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
              size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
              ite1 =
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
              ite1 =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (cbor_nondet_map_iterator_t){
                  .tag = IPair,
                  { .case_IPair = { .before = bi_, .after = ite1 } }
                }
              );
          }
          cbor_nondet_map_iterator_t r_it1 = ite0;
          FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool
          r_done1 = { .tag = FStar_Pervasives_Native_None };
          size_t r_cnt1 = (size_t)0U;
          size_t cnt = r_cnt1;
          bool
          cond0 =
            FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done1) &&
              cnt < len1;
          while (cond0)
          {
            K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
            scrut =
              CBOR_Pulse_Raw_EverParse_MapEntry_Fuel_iterator_next_map_entry_raw_data_item_fuel(r_it1);
            cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e1 = scrut.fst;
            r_it1 = scrut.snd;
            FStar_Pervasives_Native_option__size_t ite;
            if (map_bound.tag == FStar_Pervasives_Native_None)
              ite =
                ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
            else if (map_bound.tag == FStar_Pervasives_Native_Some)
            {
              size_t n1 = map_bound.v;
              if (n1 == (size_t)0U)
                ite =
                  (
                    (FStar_Pervasives_Native_option__size_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = (size_t)0U
                    }
                  );
              else
                ite =
                  (
                    (FStar_Pervasives_Native_option__size_t){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = n1 - (size_t)1U
                    }
                  );
            }
            else
              ite =
                KRML_EABORT(FStar_Pervasives_Native_option__size_t,
                  "unreachable (pattern matches are exhaustive in F*)");
            FStar_Pervasives_Native_option__bool
            scrut0 =
              CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(ite,
                e.cbor_map_entry_key,
                e1.cbor_map_entry_key);
            if (scrut0.tag == FStar_Pervasives_Native_None)
            {
              r_done1 =
                (
                  (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = { .tag = FStar_Pervasives_Native_None }
                  }
                );
              r_cnt1 = r_cnt1 + (size_t)1U;
            }
            else if (scrut0.tag == FStar_Pervasives_Native_Some)
              if (scrut0.v)
              {
                FStar_Pervasives_Native_option__size_t ite;
                if (map_bound.tag == FStar_Pervasives_Native_None)
                  ite =
                    (
                      (FStar_Pervasives_Native_option__size_t){
                        .tag = FStar_Pervasives_Native_None
                      }
                    );
                else if (map_bound.tag == FStar_Pervasives_Native_Some)
                {
                  size_t n1 = map_bound.v;
                  if (n1 == (size_t)0U)
                    ite =
                      (
                        (FStar_Pervasives_Native_option__size_t){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = (size_t)0U
                        }
                      );
                  else
                    ite =
                      (
                        (FStar_Pervasives_Native_option__size_t){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = n1 - (size_t)1U
                        }
                      );
                }
                else
                  ite =
                    KRML_EABORT(FStar_Pervasives_Native_option__size_t,
                      "unreachable (pattern matches are exhaustive in F*)");
                r_done1 =
                  (
                    (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel(ite,
                        e.cbor_map_entry_value,
                        e1.cbor_map_entry_value)
                    }
                  );
                r_cnt1 = r_cnt1 + (size_t)1U;
              }
              else
                r_cnt1 = r_cnt1 + (size_t)1U;
            else
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
            size_t cnt = r_cnt1;
            cond0 =
              FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done1) &&
                cnt < len1;
          }
          FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool scrut1 = r_done1;
          FStar_Pervasives_Native_option__bool scrut;
          if (scrut1.tag == FStar_Pervasives_Native_Some)
            scrut = scrut1.v;
          else if (scrut1.tag == FStar_Pervasives_Native_None)
            scrut =
              (
                (FStar_Pervasives_Native_option__bool){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = false
                }
              );
          else
            scrut =
              KRML_EABORT(FStar_Pervasives_Native_option__bool,
                "unreachable (pattern matches are exhaustive in F*)");
          if (scrut.tag == FStar_Pervasives_Native_Some)
            if (scrut.v)
              r_cnt = r_cnt + (size_t)1U;
            else
            {
              r_done =
                (
                  (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = { .tag = FStar_Pervasives_Native_Some, .v = false }
                  }
                );
              r_cnt = r_cnt + (size_t)1U;
            }
          else if (scrut.tag == FStar_Pervasives_Native_None)
          {
            r_done =
              (
                (FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = { .tag = FStar_Pervasives_Native_None }
                }
              );
            r_cnt = r_cnt + (size_t)1U;
          }
          else
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
          size_t cnt0 = r_cnt;
          cond =
            FStar_Pervasives_Native_uu___is_None__FStar_Pervasives_Native_option_bool(r_done) &&
              cnt0 < len;
        }
        FStar_Pervasives_Native_option__FStar_Pervasives_Native_option__bool scrut = r_done;
        if (scrut.tag == FStar_Pervasives_Native_Some)
          return scrut.v;
        else if (scrut.tag == FStar_Pervasives_Native_None)
          return
            (
              (FStar_Pervasives_Native_option__bool){
                .tag = FStar_Pervasives_Native_Some,
                .v = true
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
      else
        return
          (
            (FStar_Pervasives_Native_option__bool){
              .tag = FStar_Pervasives_Native_Some,
              .v = false
            }
          );
    else if (scrut1.tag == FStar_Pervasives_Native_None)
      return ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_None });
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

static void
Pulse_Lib_Slice_op_Array_Assignment__uint8_t(
  Pulse_Lib_Slice_slice__uint8_t a,
  size_t i,
  uint8_t v
)
{
  a.elt[i] = v;
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
  FStar_Pervasives_Native_option__bool_tags tag;
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
  FStar_Pervasives_Native_option__bool_tags tag;
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

static K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t
CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_raw_data_item(
  cbor_nondet_array_iterator_t x
)
{
  cbor_nondet_array_iterator_t r = x;
  cbor_nondet_array_iterator_t scrut0 = r;
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
            (cbor_nondet_array_iterator_t){
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
        r = ((cbor_nondet_array_iterator_t){ .tag = IBase, { .case_IBase = ite } });
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
        cbor_nondet_array_iterator_t ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (cbor_nondet_array_iterator_t){
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
              (cbor_nondet_array_iterator_t){
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
            (cbor_nondet_array_iterator_t){
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
      (K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t){
        .fst = elt,
        .snd = r
      }
    );
}

static K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_map_entry_raw_data_item(
  cbor_nondet_map_iterator_t x
)
{
  cbor_nondet_map_iterator_t r = x;
  cbor_nondet_map_iterator_t scrut0 = r;
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
            (cbor_nondet_map_iterator_t){
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
        r = ((cbor_nondet_map_iterator_t){ .tag = IBase, { .case_IBase = ite } });
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
        cbor_nondet_map_iterator_t ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (cbor_nondet_map_iterator_t){
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
              (cbor_nondet_map_iterator_t){
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
            (cbor_nondet_map_iterator_t){
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
      (K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t){
        .fst = elt,
        .snd = r
      }
    );
}

static bool
FStar_Pervasives_Native_uu___is_None__bool(FStar_Pervasives_Native_option__bool projectee)
{
  if (projectee.tag == FStar_Pervasives_Native_None)
    return true;
  else
    return false;
}

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(
  FStar_Pervasives_Native_option__size_t map_bound,
  size_t n1,
  Pulse_Lib_Slice_slice__uint8_t l1,
  size_t n2,
  Pulse_Lib_Slice_slice__uint8_t l2
)
{
  if (false)
    return
      ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = true });
  else
  {
    size_t poffset0 = (size_t)0U;
    size_t pn0 = n1;
    while (pn0 > (size_t)0U)
    {
      size_t off = poffset0;
      size_t off10 = CBOR_Pulse_Raw_EverParse_Validate_jump_header(l1, off);
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut0 = Pulse_Lib_Slice_split__uint8_t(l1, off);
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
      if
      (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        off1 = off10 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x.fst, x.snd);
      else
        off1 = off10;
      poffset0 = off1;
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut = Pulse_Lib_Slice_split__uint8_t(l1, off);
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
      size_t n = pn0;
      size_t unused = Pulse_Lib_Slice_len__uint8_t(l1) - off1;
      KRML_MAYBE_UNUSED_VAR(unused);
      pn0 =
        n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Validate_jump_recursive_step_count_leaf(input1);
    }
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = Pulse_Lib_Slice_split__uint8_t(l1, poffset0);
    Pulse_Lib_Slice_slice__uint8_t
    exact1 =
      (
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut0.fst,
          .snd = scrut0.snd
        }
      ).fst;
    size_t poffset = (size_t)0U;
    size_t pn3 = n2;
    while (pn3 > (size_t)0U)
    {
      size_t off = poffset;
      size_t off10 = CBOR_Pulse_Raw_EverParse_Validate_jump_header(l2, off);
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut0 = Pulse_Lib_Slice_split__uint8_t(l2, off);
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
      if
      (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        off1 = off10 + (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(x.fst, x.snd);
      else
        off1 = off10;
      poffset = off1;
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut = Pulse_Lib_Slice_split__uint8_t(l2, off);
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
      size_t n = pn3;
      size_t unused = Pulse_Lib_Slice_len__uint8_t(l2) - off1;
      KRML_MAYBE_UNUSED_VAR(unused);
      pn3 =
        n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Validate_jump_recursive_step_count_leaf(input1);
    }
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 = Pulse_Lib_Slice_split__uint8_t(l2, poffset);
    Pulse_Lib_Slice_slice__uint8_t
    exact2 =
      (
        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut1.fst,
          .snd = scrut1.snd
        }
      ).fst;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut2 =
      Pulse_Lib_Slice_split__uint8_t(exact1,
        CBOR_Pulse_Raw_EverParse_Validate_jump_header(exact1, (size_t)0U));
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
    CBOR_Spec_Raw_EverParse_header
    h1 =
      CBOR_Pulse_Raw_EverParse_Validate_read_header((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut4.fst,
            .snd = scrut4.snd
          }
        ).fst);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut5 =
      Pulse_Lib_Slice_split__uint8_t(exact2,
        CBOR_Pulse_Raw_EverParse_Validate_jump_header(exact2, (size_t)0U));
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
    CBOR_Spec_Raw_EverParse_header
    h2 =
      CBOR_Pulse_Raw_EverParse_Validate_read_header((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut7.fst,
            .snd = scrut7.snd
          }
        ).fst);
    uint8_t mt1 = CBOR_Spec_Raw_EverParse_get_header_major_type(h1);
    if
    (
      mt1 == CBOR_MAJOR_TYPE_MAP &&
        CBOR_Spec_Raw_EverParse_get_header_major_type(h2) == CBOR_MAJOR_TYPE_MAP
    )
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
        size_t
        nv1 =
          (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1),
            FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1));
        size_t
        nv2 =
          (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2),
            FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 =
          Pulse_Lib_Slice_split__uint8_t(exact1,
            CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(exact1, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        Pulse_Lib_Slice_slice__uint8_t
        map1 =
          (
            (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
              .fst = scrut2.fst,
              .snd = scrut2.snd
            }
          ).fst;
        CBOR_Spec_Raw_EverParse_header ph = h1;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut3 =
          Pulse_Lib_Slice_split__uint8_t(map1,
            CBOR_Pulse_Raw_EverParse_Validate_jump_header(map1, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut5 = { .fst = scrut4.fst, .snd = scrut4.snd };
        Pulse_Lib_Slice_slice__uint8_t outc0 = scrut5.snd;
        ph = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut5.fst);
        Pulse_Lib_Slice_slice__uint8_t c1 = outc0;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut6 =
          Pulse_Lib_Slice_split__uint8_t(exact2,
            CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(exact2, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
        Pulse_Lib_Slice_slice__uint8_t
        map2 =
          (
            (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
              .fst = scrut8.fst,
              .snd = scrut8.snd
            }
          ).fst;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut9 =
          Pulse_Lib_Slice_split__uint8_t(map2,
            CBOR_Pulse_Raw_EverParse_Validate_jump_header(map2, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut10 = { .fst = scrut9.fst, .snd = scrut9.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut11 = { .fst = scrut10.fst, .snd = scrut10.snd };
        Pulse_Lib_Slice_slice__uint8_t outc = scrut11.snd;
        ph = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut11.fst);
        Pulse_Lib_Slice_slice__uint8_t c2 = outc;
        Pulse_Lib_Slice_slice__uint8_t pl = c1;
        size_t pn0 = nv1;
        FStar_Pervasives_Native_option__bool
        pres0 = { .tag = FStar_Pervasives_Native_Some, .v = true };
        size_t n0 = pn0;
        bool cond = n0 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(pres0);
        while (cond)
        {
          Pulse_Lib_Slice_slice__uint8_t l = pl;
          size_t n_ = pn0 - (size_t)1U;
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut0 =
            Pulse_Lib_Slice_split__uint8_t(l,
              CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l, (size_t)0U));
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
          Pulse_Lib_Slice_slice__uint8_t lh = scrut4.fst;
          Pulse_Lib_Slice_slice__uint8_t lt = scrut4.snd;
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut5 =
            Pulse_Lib_Slice_split__uint8_t(lt,
              CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(lt, (size_t)0U));
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
          Pulse_Lib_Slice_slice__uint8_t lv = scrut9.fst;
          Pulse_Lib_Slice_slice__uint8_t lt_ = scrut9.snd;
          Pulse_Lib_Slice_slice__uint8_t pll = c2;
          size_t pn1 = nv2;
          FStar_Pervasives_Native_option__bool
          pres1 = { .tag = FStar_Pervasives_Native_Some, .v = false };
          bool pcont = true;
          size_t n3 = pn1;
          bool cont0 = pcont;
          bool cond0 = n3 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(pres1) && cont0;
          while (cond0)
          {
            Pulse_Lib_Slice_slice__uint8_t l3 = pll;
            size_t n_1 = pn1 - (size_t)1U;
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 =
              Pulse_Lib_Slice_split__uint8_t(l3,
                CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l3, (size_t)0U));
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
            Pulse_Lib_Slice_slice__uint8_t lt1 = scrut4.snd;
            size_t pn2 = (size_t)1U;
            Pulse_Lib_Slice_slice__uint8_t pl10 = lh;
            Pulse_Lib_Slice_slice__uint8_t pl20 = scrut4.fst;
            FStar_Pervasives_Native_option__bool
            pres20 = { .tag = FStar_Pervasives_Native_Some, .v = true };
            size_t n40 = pn2;
            bool cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres20) && n40 > (size_t)0U;
            while (cond)
            {
              Pulse_Lib_Slice_slice__uint8_t l1_ = pl10;
              Pulse_Lib_Slice_slice__uint8_t l2_ = pl20;
              size_t n4 = pn2;
              FStar_Pervasives_Native_option__bool
              r =
                CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound_,
                  n4,
                  l1_,
                  n4,
                  l2_);
              if (FStar_Pervasives_Native_uu___is_None__bool(r))
                pres20 = r;
              else if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
              {
                size_t n_2 = n4 - (size_t)1U;
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut0 =
                  Pulse_Lib_Slice_split__uint8_t(l1_,
                    CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l1_, (size_t)0U));
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                Pulse_Lib_Slice_slice__uint8_t
                tl1 =
                  (
                    (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                      .fst = scrut2.fst,
                      .snd = scrut2.snd
                    }
                  ).snd;
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut =
                  Pulse_Lib_Slice_split__uint8_t(l2_,
                    CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l2_, (size_t)0U));
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut3 = { .fst = scrut.fst, .snd = scrut.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                Pulse_Lib_Slice_slice__uint8_t
                tl2 =
                  (
                    (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                      .fst = scrut4.fst,
                      .snd = scrut4.snd
                    }
                  ).snd;
                pn2 = n_2;
                pl10 = tl1;
                pl20 = tl2;
              }
              else
              {
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut0 =
                  Pulse_Lib_Slice_split__uint8_t(l1_,
                    CBOR_Pulse_Raw_EverParse_Validate_jump_header(l1_, (size_t)0U));
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                Pulse_Lib_Slice_slice__uint8_t tl1 = scrut4.snd;
                CBOR_Spec_Raw_EverParse_header
                h11 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut4.fst);
                uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut5 =
                  Pulse_Lib_Slice_split__uint8_t(l2_,
                    CBOR_Pulse_Raw_EverParse_Validate_jump_header(l2_, (size_t)0U));
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
                Pulse_Lib_Slice_slice__uint8_t tl2 = scrut9.snd;
                CBOR_Spec_Raw_EverParse_header
                h21 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut9.fst);
                if (mt11 != CBOR_Spec_Raw_EverParse_get_header_major_type(h21))
                  pres20 =
                    (
                      (FStar_Pervasives_Native_option__bool){
                        .tag = FStar_Pervasives_Native_Some,
                        .v = false
                      }
                    );
                else
                {
                  CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h11.fst;
                  size_t ite0;
                  if
                  (
                    b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                      b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                  )
                    ite0 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h11.fst, h11.snd);
                  else
                    ite0 = (size_t)0U;
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                  Pulse_Lib_Slice_slice__uint8_t lc1 = scrut4.fst;
                  Pulse_Lib_Slice_slice__uint8_t tl1_ = scrut4.snd;
                  size_t
                  n_2 =
                    CBOR_Pulse_Raw_EverParse_Validate_impl_remaining_data_items_header(h11) +
                      n4 - (size_t)1U;
                  CBOR_Spec_Raw_EverParse_initial_byte_t b = h21.fst;
                  size_t ite1;
                  if
                  (
                    b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                      b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                  )
                    ite1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h21.fst, h21.snd);
                  else
                    ite1 = (size_t)0U;
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut5 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
                  Pulse_Lib_Slice_slice__uint8_t lc2 = scrut9.fst;
                  Pulse_Lib_Slice_slice__uint8_t tl2_ = scrut9.snd;
                  uint8_t mt12 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                  bool ite2;
                  if (mt12 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
                  {
                    CBOR_Spec_Raw_EverParse_long_argument
                    scrut0 =
                      FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11);
                    uint8_t sv1;
                    if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                      sv1 =
                        FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11).additional_info;
                    else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                      sv1 = scrut0.case_LongArgumentSimpleValue;
                    else
                      sv1 =
                        KRML_EABORT(uint8_t,
                          "unreachable (pattern matches are exhaustive in F*)");
                    CBOR_Spec_Raw_EverParse_long_argument
                    scrut =
                      FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21);
                    uint8_t ite;
                    if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                      ite =
                        FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21).additional_info;
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
                      CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11),
                        FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11));
                    if
                    (
                      len !=
                        CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21),
                          FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21))
                    )
                      ite2 = false;
                    else if
                    (mt12 == CBOR_MAJOR_TYPE_BYTE_STRING || mt12 == CBOR_MAJOR_TYPE_TEXT_STRING)
                      ite2 = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == (int16_t)0;
                    else
                      ite2 = mt12 != CBOR_MAJOR_TYPE_MAP;
                  }
                  if (ite2)
                  {
                    pn2 = n_2;
                    pl10 = tl1_;
                    pl20 = tl2_;
                  }
                  else
                    pres20 =
                      (
                        (FStar_Pervasives_Native_option__bool){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = false
                        }
                      );
                }
              }
              size_t n40 = pn2;
              cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres20) && n40 > (size_t)0U;
            }
            FStar_Pervasives_Native_option__bool res = pres20;
            if (FStar_Pervasives_Native_uu___is_None__bool(res))
              pres1 = res;
            else
            {
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut0 =
                Pulse_Lib_Slice_split__uint8_t(lt1,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(lt1, (size_t)0U));
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
              Pulse_Lib_Slice_slice__uint8_t lv1 = scrut4.fst;
              Pulse_Lib_Slice_slice__uint8_t lt_1 = scrut4.snd;
              bool ite0;
              if (res.tag == FStar_Pervasives_Native_Some)
                ite0 = res.v;
              else
                ite0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
              if (ite0)
              {
                size_t pn2 = (size_t)1U;
                Pulse_Lib_Slice_slice__uint8_t pl1 = lv;
                Pulse_Lib_Slice_slice__uint8_t pl2 = lv1;
                FStar_Pervasives_Native_option__bool
                pres2 = { .tag = FStar_Pervasives_Native_Some, .v = true };
                size_t n40 = pn2;
                bool cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres2) && n40 > (size_t)0U;
                while (cond)
                {
                  Pulse_Lib_Slice_slice__uint8_t l1_ = pl1;
                  Pulse_Lib_Slice_slice__uint8_t l2_ = pl2;
                  size_t n4 = pn2;
                  FStar_Pervasives_Native_option__bool
                  r =
                    CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound_,
                      n4,
                      l1_,
                      n4,
                      l2_);
                  if (FStar_Pervasives_Native_uu___is_None__bool(r))
                    pres2 = r;
                  else if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
                  {
                    size_t n_2 = n4 - (size_t)1U;
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut0 =
                      Pulse_Lib_Slice_split__uint8_t(l1_,
                        CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l1_, (size_t)0U));
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                    Pulse_Lib_Slice_slice__uint8_t
                    tl1 =
                      (
                        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                          .fst = scrut2.fst,
                          .snd = scrut2.snd
                        }
                      ).snd;
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut =
                      Pulse_Lib_Slice_split__uint8_t(l2_,
                        CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l2_, (size_t)0U));
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut3 = { .fst = scrut.fst, .snd = scrut.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                    Pulse_Lib_Slice_slice__uint8_t
                    tl2 =
                      (
                        (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                          .fst = scrut4.fst,
                          .snd = scrut4.snd
                        }
                      ).snd;
                    pn2 = n_2;
                    pl1 = tl1;
                    pl2 = tl2;
                  }
                  else
                  {
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut0 =
                      Pulse_Lib_Slice_split__uint8_t(l1_,
                        CBOR_Pulse_Raw_EverParse_Validate_jump_header(l1_, (size_t)0U));
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                    Pulse_Lib_Slice_slice__uint8_t tl1 = scrut4.snd;
                    CBOR_Spec_Raw_EverParse_header
                    h11 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut4.fst);
                    uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut5 =
                      Pulse_Lib_Slice_split__uint8_t(l2_,
                        CBOR_Pulse_Raw_EverParse_Validate_jump_header(l2_, (size_t)0U));
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
                    Pulse_Lib_Slice_slice__uint8_t tl2 = scrut9.snd;
                    CBOR_Spec_Raw_EverParse_header
                    h21 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut9.fst);
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
                      CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h11.fst;
                      size_t ite0;
                      if
                      (
                        b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                          b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                      )
                        ite0 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h11.fst, h11.snd);
                      else
                        ite0 = (size_t)0U;
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                      Pulse_Lib_Slice_slice__uint8_t lc1 = scrut4.fst;
                      Pulse_Lib_Slice_slice__uint8_t tl1_ = scrut4.snd;
                      size_t
                      n_2 =
                        CBOR_Pulse_Raw_EverParse_Validate_impl_remaining_data_items_header(h11) +
                          n4 - (size_t)1U;
                      CBOR_Spec_Raw_EverParse_initial_byte_t b = h21.fst;
                      size_t ite1;
                      if
                      (
                        b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                          b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                      )
                        ite1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h21.fst, h21.snd);
                      else
                        ite1 = (size_t)0U;
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut5 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
                      Pulse_Lib_Slice_slice__uint8_t lc2 = scrut9.fst;
                      Pulse_Lib_Slice_slice__uint8_t tl2_ = scrut9.snd;
                      uint8_t mt12 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                      bool ite2;
                      if (mt12 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
                      {
                        CBOR_Spec_Raw_EverParse_long_argument
                        scrut0 =
                          FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11);
                        uint8_t sv1;
                        if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                          sv1 =
                            FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11).additional_info;
                        else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                          sv1 = scrut0.case_LongArgumentSimpleValue;
                        else
                          sv1 =
                            KRML_EABORT(uint8_t,
                              "unreachable (pattern matches are exhaustive in F*)");
                        CBOR_Spec_Raw_EverParse_long_argument
                        scrut =
                          FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21);
                        uint8_t ite;
                        if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                          ite =
                            FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21).additional_info;
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
                          CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11),
                            FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11));
                        if
                        (
                          len !=
                            CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21),
                              FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21))
                        )
                          ite2 = false;
                        else if
                        (mt12 == CBOR_MAJOR_TYPE_BYTE_STRING || mt12 == CBOR_MAJOR_TYPE_TEXT_STRING)
                          ite2 =
                            CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == (int16_t)0;
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
                  size_t n40 = pn2;
                  cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres2) && n40 > (size_t)0U;
                }
                pres1 = pres2;
                pcont = false;
              }
              else
              {
                pll = lt_1;
                pn1 = n_1;
              }
            }
            size_t n3 = pn1;
            bool cont = pcont;
            cond0 = n3 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(pres1) && cont;
          }
          FStar_Pervasives_Native_option__bool res = pres1;
          if (CBOR_Pulse_Raw_Util_eq_Some_true(res))
          {
            pl = lt_;
            pn0 = n_;
          }
          else
            pres0 = res;
          size_t n = pn0;
          cond = n > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(pres0);
        }
        FStar_Pervasives_Native_option__bool res = pres0;
        if (CBOR_Pulse_Raw_Util_eq_Some_true(res))
        {
          Pulse_Lib_Slice_slice__uint8_t pl = c2;
          size_t pn = nv2;
          FStar_Pervasives_Native_option__bool
          pres = { .tag = FStar_Pervasives_Native_Some, .v = true };
          size_t n = pn;
          bool cond = n > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(pres);
          while (cond)
          {
            Pulse_Lib_Slice_slice__uint8_t l = pl;
            size_t n_ = pn - (size_t)1U;
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 =
              Pulse_Lib_Slice_split__uint8_t(l,
                CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l, (size_t)0U));
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
            Pulse_Lib_Slice_slice__uint8_t lh = scrut4.fst;
            Pulse_Lib_Slice_slice__uint8_t lt = scrut4.snd;
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut5 =
              Pulse_Lib_Slice_split__uint8_t(lt,
                CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(lt, (size_t)0U));
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
            Pulse_Lib_Slice_slice__uint8_t lv = scrut9.fst;
            Pulse_Lib_Slice_slice__uint8_t lt_ = scrut9.snd;
            Pulse_Lib_Slice_slice__uint8_t pll = c1;
            size_t pn1 = nv1;
            FStar_Pervasives_Native_option__bool
            pres1 = { .tag = FStar_Pervasives_Native_Some, .v = false };
            bool pcont = true;
            size_t n3 = pn1;
            bool cont0 = pcont;
            bool cond0 = n3 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(pres1) && cont0;
            while (cond0)
            {
              Pulse_Lib_Slice_slice__uint8_t l3 = pll;
              size_t n_1 = pn1 - (size_t)1U;
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut0 =
                Pulse_Lib_Slice_split__uint8_t(l3,
                  CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l3, (size_t)0U));
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
              K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
              scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
              Pulse_Lib_Slice_slice__uint8_t lt1 = scrut4.snd;
              size_t pn2 = (size_t)1U;
              Pulse_Lib_Slice_slice__uint8_t pl10 = lh;
              Pulse_Lib_Slice_slice__uint8_t pl20 = scrut4.fst;
              FStar_Pervasives_Native_option__bool
              pres20 = { .tag = FStar_Pervasives_Native_Some, .v = true };
              size_t n40 = pn2;
              bool cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres20) && n40 > (size_t)0U;
              while (cond)
              {
                Pulse_Lib_Slice_slice__uint8_t l1_ = pl10;
                Pulse_Lib_Slice_slice__uint8_t l2_ = pl20;
                size_t n4 = pn2;
                FStar_Pervasives_Native_option__bool
                r =
                  CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound_,
                    n4,
                    l1_,
                    n4,
                    l2_);
                if (FStar_Pervasives_Native_uu___is_None__bool(r))
                  pres20 = r;
                else if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
                {
                  size_t n_2 = n4 - (size_t)1U;
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut0 =
                    Pulse_Lib_Slice_split__uint8_t(l1_,
                      CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l1_, (size_t)0U));
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                  Pulse_Lib_Slice_slice__uint8_t
                  tl1 =
                    (
                      (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                        .fst = scrut2.fst,
                        .snd = scrut2.snd
                      }
                    ).snd;
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut =
                    Pulse_Lib_Slice_split__uint8_t(l2_,
                      CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l2_, (size_t)0U));
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut3 = { .fst = scrut.fst, .snd = scrut.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                  Pulse_Lib_Slice_slice__uint8_t
                  tl2 =
                    (
                      (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                        .fst = scrut4.fst,
                        .snd = scrut4.snd
                      }
                    ).snd;
                  pn2 = n_2;
                  pl10 = tl1;
                  pl20 = tl2;
                }
                else
                {
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut0 =
                    Pulse_Lib_Slice_split__uint8_t(l1_,
                      CBOR_Pulse_Raw_EverParse_Validate_jump_header(l1_, (size_t)0U));
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                  Pulse_Lib_Slice_slice__uint8_t tl1 = scrut4.snd;
                  CBOR_Spec_Raw_EverParse_header
                  h11 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut4.fst);
                  uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut5 =
                    Pulse_Lib_Slice_split__uint8_t(l2_,
                      CBOR_Pulse_Raw_EverParse_Validate_jump_header(l2_, (size_t)0U));
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
                  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                  scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
                  Pulse_Lib_Slice_slice__uint8_t tl2 = scrut9.snd;
                  CBOR_Spec_Raw_EverParse_header
                  h21 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut9.fst);
                  if (mt11 != CBOR_Spec_Raw_EverParse_get_header_major_type(h21))
                    pres20 =
                      (
                        (FStar_Pervasives_Native_option__bool){
                          .tag = FStar_Pervasives_Native_Some,
                          .v = false
                        }
                      );
                  else
                  {
                    CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h11.fst;
                    size_t ite0;
                    if
                    (
                      b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                        b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                    )
                      ite0 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h11.fst, h11.snd);
                    else
                      ite0 = (size_t)0U;
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                    Pulse_Lib_Slice_slice__uint8_t lc1 = scrut4.fst;
                    Pulse_Lib_Slice_slice__uint8_t tl1_ = scrut4.snd;
                    size_t
                    n_2 =
                      CBOR_Pulse_Raw_EverParse_Validate_impl_remaining_data_items_header(h11) +
                        n4 - (size_t)1U;
                    CBOR_Spec_Raw_EverParse_initial_byte_t b = h21.fst;
                    size_t ite1;
                    if
                    (
                      b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                        b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                    )
                      ite1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h21.fst, h21.snd);
                    else
                      ite1 = (size_t)0U;
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut5 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
                    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                    scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
                    Pulse_Lib_Slice_slice__uint8_t lc2 = scrut9.fst;
                    Pulse_Lib_Slice_slice__uint8_t tl2_ = scrut9.snd;
                    uint8_t mt12 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                    bool ite2;
                    if (mt12 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
                    {
                      CBOR_Spec_Raw_EverParse_long_argument
                      scrut0 =
                        FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11);
                      uint8_t sv1;
                      if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                        sv1 =
                          FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11).additional_info;
                      else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                        sv1 = scrut0.case_LongArgumentSimpleValue;
                      else
                        sv1 =
                          KRML_EABORT(uint8_t,
                            "unreachable (pattern matches are exhaustive in F*)");
                      CBOR_Spec_Raw_EverParse_long_argument
                      scrut =
                        FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21);
                      uint8_t ite;
                      if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                        ite =
                          FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21).additional_info;
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
                        CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11),
                          FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11));
                      if
                      (
                        len !=
                          CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21),
                            FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21))
                      )
                        ite2 = false;
                      else if
                      (mt12 == CBOR_MAJOR_TYPE_BYTE_STRING || mt12 == CBOR_MAJOR_TYPE_TEXT_STRING)
                        ite2 =
                          CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == (int16_t)0;
                      else
                        ite2 = mt12 != CBOR_MAJOR_TYPE_MAP;
                    }
                    if (ite2)
                    {
                      pn2 = n_2;
                      pl10 = tl1_;
                      pl20 = tl2_;
                    }
                    else
                      pres20 =
                        (
                          (FStar_Pervasives_Native_option__bool){
                            .tag = FStar_Pervasives_Native_Some,
                            .v = false
                          }
                        );
                  }
                }
                size_t n40 = pn2;
                cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres20) && n40 > (size_t)0U;
              }
              FStar_Pervasives_Native_option__bool res1 = pres20;
              if (FStar_Pervasives_Native_uu___is_None__bool(res1))
                pres1 = res1;
              else
              {
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut0 =
                  Pulse_Lib_Slice_split__uint8_t(lt1,
                    CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(lt1, (size_t)0U));
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
                K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                Pulse_Lib_Slice_slice__uint8_t lv1 = scrut4.fst;
                Pulse_Lib_Slice_slice__uint8_t lt_1 = scrut4.snd;
                bool ite0;
                if (res1.tag == FStar_Pervasives_Native_Some)
                  ite0 = res1.v;
                else
                  ite0 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                if (ite0)
                {
                  size_t pn2 = (size_t)1U;
                  Pulse_Lib_Slice_slice__uint8_t pl1 = lv;
                  Pulse_Lib_Slice_slice__uint8_t pl2 = lv1;
                  FStar_Pervasives_Native_option__bool
                  pres2 = { .tag = FStar_Pervasives_Native_Some, .v = true };
                  size_t n40 = pn2;
                  bool cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres2) && n40 > (size_t)0U;
                  while (cond)
                  {
                    Pulse_Lib_Slice_slice__uint8_t l1_ = pl1;
                    Pulse_Lib_Slice_slice__uint8_t l2_ = pl2;
                    size_t n4 = pn2;
                    FStar_Pervasives_Native_option__bool
                    r =
                      CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound_,
                        n4,
                        l1_,
                        n4,
                        l2_);
                    if (FStar_Pervasives_Native_uu___is_None__bool(r))
                      pres2 = r;
                    else if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
                    {
                      size_t n_2 = n4 - (size_t)1U;
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut0 =
                        Pulse_Lib_Slice_split__uint8_t(l1_,
                          CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l1_, (size_t)0U));
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                      Pulse_Lib_Slice_slice__uint8_t
                      tl1 =
                        (
                          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                            .fst = scrut2.fst,
                            .snd = scrut2.snd
                          }
                        ).snd;
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut =
                        Pulse_Lib_Slice_split__uint8_t(l2_,
                          CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l2_, (size_t)0U));
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut3 = { .fst = scrut.fst, .snd = scrut.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                      Pulse_Lib_Slice_slice__uint8_t
                      tl2 =
                        (
                          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                            .fst = scrut4.fst,
                            .snd = scrut4.snd
                          }
                        ).snd;
                      pn2 = n_2;
                      pl1 = tl1;
                      pl2 = tl2;
                    }
                    else
                    {
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut0 =
                        Pulse_Lib_Slice_split__uint8_t(l1_,
                          CBOR_Pulse_Raw_EverParse_Validate_jump_header(l1_, (size_t)0U));
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                      Pulse_Lib_Slice_slice__uint8_t tl1 = scrut4.snd;
                      CBOR_Spec_Raw_EverParse_header
                      h11 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut4.fst);
                      uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut5 =
                        Pulse_Lib_Slice_split__uint8_t(l2_,
                          CBOR_Pulse_Raw_EverParse_Validate_jump_header(l2_, (size_t)0U));
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
                      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                      scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
                      Pulse_Lib_Slice_slice__uint8_t tl2 = scrut9.snd;
                      CBOR_Spec_Raw_EverParse_header
                      h21 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut9.fst);
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
                        CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h11.fst;
                        size_t ite0;
                        if
                        (
                          b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                            b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                        )
                          ite0 =
                            (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h11.fst, h11.snd);
                        else
                          ite0 = (size_t)0U;
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
                        Pulse_Lib_Slice_slice__uint8_t lc1 = scrut4.fst;
                        Pulse_Lib_Slice_slice__uint8_t tl1_ = scrut4.snd;
                        size_t
                        n_2 =
                          CBOR_Pulse_Raw_EverParse_Validate_impl_remaining_data_items_header(h11) +
                            n4 - (size_t)1U;
                        CBOR_Spec_Raw_EverParse_initial_byte_t b = h21.fst;
                        size_t ite1;
                        if
                        (
                          b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
                            b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
                        )
                          ite1 =
                            (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h21.fst, h21.snd);
                        else
                          ite1 = (size_t)0U;
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut5 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
                        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
                        scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
                        Pulse_Lib_Slice_slice__uint8_t lc2 = scrut9.fst;
                        Pulse_Lib_Slice_slice__uint8_t tl2_ = scrut9.snd;
                        uint8_t mt12 = CBOR_Spec_Raw_EverParse_get_header_major_type(h11);
                        bool ite2;
                        if (mt12 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
                        {
                          CBOR_Spec_Raw_EverParse_long_argument
                          scrut0 =
                            FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11);
                          uint8_t sv1;
                          if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                            sv1 =
                              FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11).additional_info;
                          else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
                            sv1 = scrut0.case_LongArgumentSimpleValue;
                          else
                            sv1 =
                              KRML_EABORT(uint8_t,
                                "unreachable (pattern matches are exhaustive in F*)");
                          CBOR_Spec_Raw_EverParse_long_argument
                          scrut =
                            FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21);
                          uint8_t ite;
                          if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
                            ite =
                              FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21).additional_info;
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
                            CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11),
                              FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h11));
                          if
                          (
                            len !=
                              CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21),
                                FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h21))
                          )
                            ite2 = false;
                          else if
                          (
                            mt12 == CBOR_MAJOR_TYPE_BYTE_STRING ||
                              mt12 == CBOR_MAJOR_TYPE_TEXT_STRING
                          )
                            ite2 =
                              CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == (int16_t)0;
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
                    size_t n40 = pn2;
                    cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres2) && n40 > (size_t)0U;
                  }
                  pres1 = pres2;
                  pcont = false;
                }
                else
                {
                  pll = lt_1;
                  pn1 = n_1;
                }
              }
              size_t n3 = pn1;
              bool cont = pcont;
              cond0 = n3 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(pres1) && cont;
            }
            FStar_Pervasives_Native_option__bool res1 = pres1;
            if (CBOR_Pulse_Raw_Util_eq_Some_true(res1))
            {
              pl = lt_;
              pn = n_;
            }
            else
              pres = res1;
            size_t n = pn;
            cond = n > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(pres);
          }
          return pres;
        }
        else
          return res;
      }
    else
      return
        ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = false });
  }
}

static FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_list_basic(
  FStar_Pervasives_Native_option__size_t map_bound,
  size_t n1,
  Pulse_Lib_Slice_slice__uint8_t l1,
  size_t n2,
  Pulse_Lib_Slice_slice__uint8_t l2
)
{
  size_t poffset0 = (size_t)0U;
  size_t pn0 = n1;
  while (pn0 > (size_t)0U)
  {
    size_t off = poffset0;
    size_t off10 = CBOR_Pulse_Raw_EverParse_Validate_jump_header(l1, off);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = Pulse_Lib_Slice_split__uint8_t(l1, off);
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
    poffset0 = off1;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = Pulse_Lib_Slice_split__uint8_t(l1, off);
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
    size_t n = pn0;
    size_t unused = Pulse_Lib_Slice_len__uint8_t(l1) - off1;
    KRML_MAYBE_UNUSED_VAR(unused);
    pn0 = n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Validate_jump_recursive_step_count_leaf(input1);
  }
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = Pulse_Lib_Slice_split__uint8_t(l1, poffset0);
  Pulse_Lib_Slice_slice__uint8_t
  exact1 =
    (
      (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
        .fst = scrut0.fst,
        .snd = scrut0.snd
      }
    ).fst;
  size_t poffset = (size_t)0U;
  size_t pn1 = n2;
  while (pn1 > (size_t)0U)
  {
    size_t off = poffset;
    size_t off10 = CBOR_Pulse_Raw_EverParse_Validate_jump_header(l2, off);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = Pulse_Lib_Slice_split__uint8_t(l2, off);
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
    scrut = Pulse_Lib_Slice_split__uint8_t(l2, off);
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
    size_t n = pn1;
    size_t unused = Pulse_Lib_Slice_len__uint8_t(l2) - off1;
    KRML_MAYBE_UNUSED_VAR(unused);
    pn1 = n - (size_t)1U + CBOR_Pulse_Raw_EverParse_Validate_jump_recursive_step_count_leaf(input1);
  }
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = Pulse_Lib_Slice_split__uint8_t(l2, poffset);
  Pulse_Lib_Slice_slice__uint8_t
  exact2 =
    (
      (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
        .fst = scrut1.fst,
        .snd = scrut1.snd
      }
    ).fst;
  if (n1 != n2)
    return
      ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_Some, .v = false });
  else
  {
    size_t pn = n1;
    Pulse_Lib_Slice_slice__uint8_t pl1 = exact1;
    Pulse_Lib_Slice_slice__uint8_t pl2 = exact2;
    FStar_Pervasives_Native_option__bool pres = { .tag = FStar_Pervasives_Native_Some, .v = true };
    size_t n0 = pn;
    bool cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres) && n0 > (size_t)0U;
    while (cond)
    {
      Pulse_Lib_Slice_slice__uint8_t l1_ = pl1;
      Pulse_Lib_Slice_slice__uint8_t l2_ = pl2;
      size_t n = pn;
      FStar_Pervasives_Native_option__bool
      r =
        CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(map_bound,
          n,
          l1_,
          n,
          l2_);
      if (FStar_Pervasives_Native_uu___is_None__bool(r))
        pres = r;
      else if (CBOR_Pulse_Raw_Util_eq_Some_true(r))
      {
        size_t n_ = n - (size_t)1U;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 =
          Pulse_Lib_Slice_split__uint8_t(l1_,
            CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l1_, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        Pulse_Lib_Slice_slice__uint8_t
        tl1 =
          (
            (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
              .fst = scrut2.fst,
              .snd = scrut2.snd
            }
          ).snd;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut =
          Pulse_Lib_Slice_split__uint8_t(l2_,
            CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l2_, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut3 = { .fst = scrut.fst, .snd = scrut.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
        Pulse_Lib_Slice_slice__uint8_t
        tl2 =
          (
            (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
              .fst = scrut4.fst,
              .snd = scrut4.snd
            }
          ).snd;
        pn = n_;
        pl1 = tl1;
        pl2 = tl2;
      }
      else
      {
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 =
          Pulse_Lib_Slice_split__uint8_t(l1_,
            CBOR_Pulse_Raw_EverParse_Validate_jump_header(l1_, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
        Pulse_Lib_Slice_slice__uint8_t tl1 = scrut4.snd;
        CBOR_Spec_Raw_EverParse_header
        h1 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut4.fst);
        uint8_t mt1 = CBOR_Spec_Raw_EverParse_get_header_major_type(h1);
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut5 =
          Pulse_Lib_Slice_split__uint8_t(l2_,
            CBOR_Pulse_Raw_EverParse_Validate_jump_header(l2_, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
        Pulse_Lib_Slice_slice__uint8_t tl2 = scrut9.snd;
        CBOR_Spec_Raw_EverParse_header
        h2 = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut9.fst);
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
          CBOR_Spec_Raw_EverParse_initial_byte_t b0 = h1.fst;
          size_t ite0;
          if
          (
            b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
              b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
          )
            ite0 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h1.fst, h1.snd);
          else
            ite0 = (size_t)0U;
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut0 = Pulse_Lib_Slice_split__uint8_t(tl1, ite0);
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
          Pulse_Lib_Slice_slice__uint8_t lc1 = scrut4.fst;
          Pulse_Lib_Slice_slice__uint8_t tl1_ = scrut4.snd;
          size_t
          n_ =
            CBOR_Pulse_Raw_EverParse_Validate_impl_remaining_data_items_header(h1) + n - (size_t)1U;
          CBOR_Spec_Raw_EverParse_initial_byte_t b = h2.fst;
          size_t ite1;
          if
          (
            b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
              b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
          )
            ite1 = (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(h2.fst, h2.snd);
          else
            ite1 = (size_t)0U;
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut5 = Pulse_Lib_Slice_split__uint8_t(tl2, ite1);
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut8 = { .fst = scrut7.fst, .snd = scrut7.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
          Pulse_Lib_Slice_slice__uint8_t lc2 = scrut9.fst;
          Pulse_Lib_Slice_slice__uint8_t tl2_ = scrut9.snd;
          uint8_t mt11 = CBOR_Spec_Raw_EverParse_get_header_major_type(h1);
          bool ite2;
          if (mt11 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
          {
            CBOR_Spec_Raw_EverParse_long_argument
            scrut0 =
              FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1);
            uint8_t sv1;
            if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
              sv1 =
                FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1).additional_info;
            else if (scrut0.tag == CBOR_Spec_Raw_EverParse_LongArgumentSimpleValue)
              sv1 = scrut0.case_LongArgumentSimpleValue;
            else
              sv1 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
            CBOR_Spec_Raw_EverParse_long_argument
            scrut =
              FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2);
            uint8_t ite;
            if (scrut.tag == CBOR_Spec_Raw_EverParse_LongArgumentOther)
              ite =
                FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2).additional_info;
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
              CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1),
                FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h1));
            if
            (
              len !=
                CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2),
                  FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h2))
            )
              ite2 = false;
            else if (mt11 == CBOR_MAJOR_TYPE_BYTE_STRING || mt11 == CBOR_MAJOR_TYPE_TEXT_STRING)
              ite2 = CBOR_Pulse_Raw_Compare_Bytes_lex_compare_bytes(lc1, lc2) == (int16_t)0;
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
      size_t n0 = pn;
      cond = CBOR_Pulse_Raw_Util_eq_Some_true(pres) && n0 > (size_t)0U;
    }
    return pres;
  }
}

static FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_basic(
  FStar_Pervasives_Native_option__size_t map_bound,
  Pulse_Lib_Slice_slice__uint8_t l1,
  Pulse_Lib_Slice_slice__uint8_t l2
)
{
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
  Pulse_Lib_Slice_slice__uint8_t l1
)
{
  size_t pn = (size_t)1U;
  bool pres = true;
  Pulse_Lib_Slice_slice__uint8_t ppi = l1;
  while (pres && pn > (size_t)0U)
  {
    size_t n = pn;
    Pulse_Lib_Slice_slice__uint8_t pi = ppi;
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 =
      Pulse_Lib_Slice_split__uint8_t(pi,
        CBOR_Pulse_Raw_EverParse_Validate_jump_header(pi, (size_t)0U));
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
    CBOR_Spec_Raw_EverParse_header
    h =
      CBOR_Pulse_Raw_EverParse_Validate_read_header((
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut3.fst,
            .snd = scrut3.snd
          }
        ).fst);
    bool ite0;
    if (CBOR_Spec_Raw_EverParse_get_header_major_type(h) == CBOR_MAJOR_TYPE_MAP)
    {
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut0 =
        Pulse_Lib_Slice_split__uint8_t(pi,
          CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(pi, (size_t)0U));
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
      Pulse_Lib_Slice_slice__uint8_t
      hd =
        (
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut2.fst,
            .snd = scrut2.snd
          }
        ).fst;
      CBOR_Spec_Raw_EverParse_header ph = h;
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut =
        Pulse_Lib_Slice_split__uint8_t(hd,
          CBOR_Pulse_Raw_EverParse_Validate_jump_header(hd, (size_t)0U));
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut3 = { .fst = scrut.fst, .snd = scrut.snd };
      K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
      Pulse_Lib_Slice_slice__uint8_t outc = scrut4.snd;
      ph = CBOR_Pulse_Raw_EverParse_Validate_read_header(scrut4.fst);
      Pulse_Lib_Slice_slice__uint8_t pl = outc;
      size_t
      pn1 =
        (size_t)CBOR_Spec_Raw_EverParse_argument_as_uint64(FStar_Pervasives_dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h),
          FStar_Pervasives_dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(h));
      FStar_Pervasives_Native_option__bool
      pres1 = { .tag = FStar_Pervasives_Native_Some, .v = true };
      size_t n1 = pn1;
      bool cond = n1 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(pres1);
      while (cond)
      {
        size_t n_ = pn1 - (size_t)1U;
        Pulse_Lib_Slice_slice__uint8_t l = pl;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut =
          Pulse_Lib_Slice_split__uint8_t(l,
            CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
        Pulse_Lib_Slice_slice__uint8_t lh = scrut3.fst;
        Pulse_Lib_Slice_slice__uint8_t lt = scrut3.snd;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut4 =
          Pulse_Lib_Slice_split__uint8_t(lt,
            CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(lt, (size_t)0U));
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut5 = { .fst = scrut4.fst, .snd = scrut4.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
        Pulse_Lib_Slice_slice__uint8_t
        lt_ =
          (
            (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
              .fst = scrut7.fst,
              .snd = scrut7.snd
            }
          ).snd;
        Pulse_Lib_Slice_slice__uint8_t pl1 = lt_;
        size_t pn2 = n_;
        FStar_Pervasives_Native_option__bool
        pres2 = { .tag = FStar_Pervasives_Native_Some, .v = false };
        size_t n2 = pn2;
        bool cond0 = n2 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(pres2);
        while (cond0)
        {
          size_t n_1 = pn2 - (size_t)1U;
          Pulse_Lib_Slice_slice__uint8_t l2 = pl1;
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut =
            Pulse_Lib_Slice_split__uint8_t(l2,
              CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(l2, (size_t)0U));
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
          K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
          Pulse_Lib_Slice_slice__uint8_t lt1 = scrut3.snd;
          FStar_Pervasives_Native_option__bool
          res =
            CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_basic(map_bound,
              lh,
              scrut3.fst);
          if (CBOR_Pulse_Raw_Util_eq_Some_false(res))
          {
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut =
              Pulse_Lib_Slice_split__uint8_t(lt1,
                CBOR_Pulse_Raw_EverParse_Validate_jump_raw_data_item(lt1, (size_t)0U));
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
            K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
            pl1 =
              (
                (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                  .fst = scrut2.fst,
                  .snd = scrut2.snd
                }
              ).snd;
            pn2 = n_1;
          }
          else
            pres2 = res;
          size_t n2 = pn2;
          cond0 = n2 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_false(pres2);
        }
        FStar_Pervasives_Native_option__bool res = pres2;
        if (FStar_Pervasives_Native_uu___is_None__bool(res))
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
          else
          {
            FStar_Pervasives_Native_option__size_t ite;
            if (strict_bound_check)
              ite = map_bound;
            else
              ite =
                ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
            if (CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_opt(ite, (size_t)1U, lh))
            {
              pn1 = n_;
              pl = lt_;
            }
            else
              pres1 =
                ((FStar_Pervasives_Native_option__bool){ .tag = FStar_Pervasives_Native_None });
          }
        }
        size_t n1 = pn1;
        cond = n1 > (size_t)0U && CBOR_Pulse_Raw_Util_eq_Some_true(pres1);
      }
      ite0 = CBOR_Pulse_Raw_Util_eq_Some_true(pres1);
    }
    else
      ite0 = true;
    if (!ite0)
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
      ppi = pc;
    }
  }
  return pres;
}

static size_t
CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet(
  FStar_Pervasives_Native_option__size_t map_key_bound,
  bool strict_check,
  Pulse_Lib_Slice_slice__uint8_t input
)
{
  size_t poff = (size_t)0U;
  if (CBOR_Pulse_Raw_EverParse_Validate_validate_raw_data_item(input, &poff))
  {
    size_t off = poff;
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
        off - (size_t)0U);
    K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
    if
    (
      CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_valid_basic(map_key_bound,
        strict_check,
        (
          (K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut1.fst,
            .snd = scrut1.snd
          }
        ).fst)
    )
      return off;
    else
      return (size_t)0U;
  }
  else
    return (size_t)0U;
}

static size_t CBOR_Pulse_API_Nondet_Common_cbor_nondet_size(cbor_raw x, size_t bound)
{
  return CBOR_Pulse_Raw_EverParse_Serialize_cbor_size(x, bound);
}

static uint8_t CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(cbor_raw x)
{
  return CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_major_type(x);
}

static bool
CBOR_Pulse_API_Nondet_Common_cbor_nondet_read_simple_value(cbor_raw x, uint8_t *dest)
{
  if (dest == NULL)
    return false;
  else if
  (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_simple_value(x);
    return true;
  }
}

static bool CBOR_Pulse_API_Nondet_Common_cbor_nondet_read_uint64(cbor_raw x, uint64_t *dest)
{
  if (dest == NULL)
    return false;
  else
  {
    uint8_t ty = CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x);
    if (ty != CBOR_MAJOR_TYPE_UINT64 && ty != CBOR_MAJOR_TYPE_NEG_INT64)
      return false;
    else
    {
      *dest = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_int64_value(x);
      return true;
    }
  }
}

static bool CBOR_Pulse_API_Nondet_Common_cbor_nondet_read_int64(cbor_raw x, int64_t *dest)
{
  if (dest == NULL)
    return false;
  else
  {
    uint8_t ty = CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x);
    if (ty == CBOR_MAJOR_TYPE_UINT64)
    {
      uint64_t raw = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_int64_value(x);
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
      uint64_t raw = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_int64_value(x);
      if (raw > 9223372036854775807ULL)
        return false;
      else
      {
        *dest = (int64_t)-1 - (int64_t)raw;
        return true;
      }
    }
    else
      return false;
  }
}

static bool
CBOR_Pulse_API_Nondet_Common_cbor_nondet_get_array_length(cbor_raw x, uint64_t *dest)
{
  if (dest == NULL)
    return false;
  else if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_ARRAY)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_array_length(x);
    return true;
  }
}

static bool
CBOR_Pulse_API_Nondet_Common_cbor_nondet_array_iterator_is_empty(
  cbor_nondet_array_iterator_t x
)
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

static uint64_t
CBOR_Pulse_API_Nondet_Common_cbor_nondet_array_iterator_length(cbor_nondet_array_iterator_t x)
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

static cbor_nondet_array_iterator_t
CBOR_Pulse_API_Nondet_Common_cbor_nondet_array_iterator_truncate(
  cbor_nondet_array_iterator_t x,
  uint64_t len
)
{
  size_t len_sz = (size_t)len;
  if (x.tag == IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = x.case_IBase;
    size_t
    cb_sz =
      LowParse_PulseParse_Iterator_Type_base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    size_t len_before_sz;
    if (len_sz <= cb_sz)
      len_before_sz = len_sz;
    else
      len_before_sz = cb_sz;
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
      if (len_before_sz == (size_t)0U)
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
      ite =
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
      ite =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return ((cbor_nondet_array_iterator_t){ .tag = IBase, { .case_IBase = ite } });
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
        (cbor_nondet_array_iterator_t){
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

static bool CBOR_Pulse_API_Nondet_Common_cbor_nondet_get_map_length(cbor_raw x, uint64_t *dest)
{
  if (dest == NULL)
    return false;
  else if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_MAP)
    return false;
  else
  {
    *dest = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_map_length(x);
    return true;
  }
}

static bool
CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_iterator_is_empty(cbor_nondet_map_iterator_t x)
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

static cbor_raw
CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_entry_key(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x2
)
{
  return x2.cbor_map_entry_key;
}

static cbor_raw
CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_entry_value(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x2
)
{
  return x2.cbor_map_entry_value;
}

static bool CBOR_Pulse_API_Nondet_Common_cbor_nondet_equal(cbor_raw x1, cbor_raw x2)
{
  FStar_Pervasives_Native_option__bool
  scrut =
    CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel((
        (FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None }
      ),
      x1,
      x2);
  if (scrut.tag == FStar_Pervasives_Native_Some)
    return scrut.v;
  else if (scrut.tag == FStar_Pervasives_Native_None)
    return false;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_raw CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_uint64(uint64_t v)
{
  return CBOR_Pulse_Raw_EverParse_Make_cbor_mk_int64(CBOR_MAJOR_TYPE_UINT64, v);
}

static cbor_raw CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_neg_int64(uint64_t v)
{
  return CBOR_Pulse_Raw_EverParse_Make_cbor_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, v);
}

static cbor_raw CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_int64(int64_t v)
{
  if (v < (int64_t)0)
    if (CBOR_MAJOR_TYPE_NEG_INT64 == CBOR_MAJOR_TYPE_UINT64)
      return CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_uint64((uint64_t)((int64_t)-1 - v));
    else
      return CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_neg_int64((uint64_t)((int64_t)-1 - v));
  else if (CBOR_MAJOR_TYPE_UINT64 == CBOR_MAJOR_TYPE_UINT64)
    return CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_uint64((uint64_t)v);
  else
    return CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_neg_int64((uint64_t)v);
}

static cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  cbor_raw xk_ = CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(xk);
  return
    (
      (cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .cbor_map_entry_key = xk_,
        .cbor_map_entry_value = CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(xv)
      }
    );
}

static bool
CBOR_Pulse_API_Nondet_Common_cbor_nondet_no_setoid_repeats(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  x
)
{
  size_t pn1 = (size_t)0U;
  bool pres = true;
  bool res0 = pres;
  size_t __anf00 = pn1;
  bool
  cond =
    res0 &&
      __anf00 <
        Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x);
  while (cond)
  {
    size_t n1 = pn1;
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    x1 =
      Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x,
        n1);
    size_t n2 = n1 + (size_t)1U;
    pn1 = n2;
    size_t pn2 = n2;
    bool res = pres;
    size_t __anf00 = pn2;
    bool
    cond0 =
      res &&
        __anf00 <
          Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x);
    while (cond0)
    {
      size_t n21 = pn2;
      FStar_Pervasives_Native_option__bool
      scrut =
        CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel((
            (FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None }
          ),
          x1.cbor_map_entry_key,
          Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x,
            n21).cbor_map_entry_key);
      bool ite;
      if (scrut.tag == FStar_Pervasives_Native_Some)
        ite = scrut.v;
      else if (scrut.tag == FStar_Pervasives_Native_None)
        ite = false;
      else
        ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
      pres = !ite;
      pn2 = n21 + (size_t)1U;
      bool res = pres;
      size_t __anf0 = pn2;
      cond0 =
        res &&
          __anf0 <
            Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x);
    }
    bool res0 = pres;
    size_t __anf0 = pn1;
    cond =
      res0 &&
        __anf0 <
          Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x);
  }
  return pres;
}

static Pulse_Lib_Slice_slice__uint8_t
Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

static Pulse_Lib_Slice_slice__uint8_t
FStar_Pervasives_Native_fst__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t(
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t x
)
{
  return x.fst;
}

static Pulse_Lib_Slice_slice__uint8_t
FStar_Pervasives_Native_snd__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t(
  K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t x
)
{
  return x.snd;
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
    uint8_t *input1 = *pinput;
    if (*pinput == NULL)
      return false;
    else
    {
      size_t len1 = *plen;
      Pulse_Lib_Slice_slice__uint8_t
      s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input1, len1);
      FStar_Pervasives_Native_option__size_t ite;
      if (check_map_key_bound)
        ite =
          (
            (FStar_Pervasives_Native_option__size_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = map_key_bound
            }
          );
      else
        ite = ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
      size_t
      consume =
        CBOR_Pulse_Raw_Format_Nondet_Validate_cbor_validate_nondet(ite,
          check_map_key_bound,
          s);
      if (consume == (size_t)0U)
        return false;
      else
      {
        *pinput = input1 + consume;
        *plen = len1 - consume;
        K___Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        s1s2 =
          Pulse_Lib_Slice_split__uint8_t(Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(input1,
              consume),
            consume);
        Pulse_Lib_Slice_slice__uint8_t
        s11 =
          FStar_Pervasives_Native_fst__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t(s1s2);
        FStar_Pervasives_Native_snd__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t(s1s2);
        *dest = CBOR_Pulse_Raw_EverParse_Det_Validate_cbor_parse_valid(s11);
        return true;
      }
    }
  }
}

size_t cbor_nondet_size(cbor_raw x, size_t bound)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_size(x, bound);
}

size_t cbor_nondet_serialize(cbor_raw x, uint8_t *output, size_t len)
{
  if (output == NULL)
    return (size_t)0U;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t
    s = Pulse_Lib_Slice_arrayptr_to_slice_intro__uint8_t(output, len);
    size_t len1 = CBOR_Pulse_Raw_EverParse_Serialize_cbor_size(x, Pulse_Lib_Slice_len__uint8_t(s));
    FStar_Pervasives_Native_option__size_t scrut;
    if (len1 == (size_t)0U)
      scrut = ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
    else
      scrut =
        (
          (FStar_Pervasives_Native_option__size_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = CBOR_Pulse_Raw_EverParse_Serialize_cbor_serialize(x,
              Pulse_Lib_Slice_split__uint8_t(s, len1).fst)
          }
        );
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
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x);
}

bool cbor_nondet_read_simple_value(cbor_raw x, uint8_t *dest)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_read_simple_value(x, dest);
}

bool cbor_nondet_read_uint64(cbor_raw x, uint64_t *dest)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_read_uint64(x, dest);
}

bool cbor_nondet_read_int64(cbor_raw x, int64_t *dest)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_read_int64(x, dest);
}

static uint8_t
*Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.elt;
}

bool cbor_nondet_get_string(cbor_raw x, uint8_t **dest, uint64_t *dlen)
{
  if (dest == NULL || dlen == NULL)
    return false;
  else
  {
    uint8_t ty = CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x);
    if (ty != CBOR_MAJOR_TYPE_BYTE_STRING && ty != CBOR_MAJOR_TYPE_TEXT_STRING)
      return false;
    else
    {
      uint64_t
      len =
        (uint64_t)Pulse_Lib_Slice_len__uint8_t(CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string(x));
      uint8_t
      *res =
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_string(x));
      *dlen = len;
      *dest = res;
      return true;
    }
  }
}

bool cbor_nondet_get_byte_string(cbor_raw x, uint8_t **dest, uint64_t *dlen)
{
  if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_BYTE_STRING)
    return false;
  else
    return cbor_nondet_get_string(x, dest, dlen);
}

bool cbor_nondet_get_text_string(cbor_raw x, uint8_t **dest, uint64_t *dlen)
{
  if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_TEXT_STRING)
    return false;
  else
    return cbor_nondet_get_string(x, dest, dlen);
}

bool cbor_nondet_get_tagged(cbor_raw x, cbor_raw *dest, uint64_t *dtag)
{
  if (dest == NULL || dtag == NULL)
    return false;
  else if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_TAGGED)
    return false;
  else
  {
    uint64_t tag = CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_tagged_tag(x);
    cbor_raw res = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_tagged_payload(x);
    *dtag = tag;
    *dest = res;
    return true;
  }
}

bool cbor_nondet_get_array_length(cbor_raw x, uint64_t *dest)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_get_array_length(x, dest);
}

bool cbor_nondet_array_iterator_start(cbor_raw x, cbor_nondet_array_iterator_t *dest)
{
  if (dest == NULL)
    return false;
  else if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_ARRAY)
    return false;
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array(x);
    size_t
    total_sz =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    cbor_nondet_array_iterator_t ite0;
    if (total_sz == (size_t)0U)
      ite0 =
        (
          (cbor_nondet_array_iterator_t){
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
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite1;
      if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
      {
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        bi = ml.case_Base;
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
        size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
        size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
        size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
        ite1 =
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
        ite1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (cbor_nondet_array_iterator_t){
            .tag = IPair,
            { .case_IPair = { .before = bi_, .after = ite1 } }
          }
        );
    }
    *dest = ite0;
    return true;
  }
}

bool cbor_nondet_array_iterator_is_empty(cbor_nondet_array_iterator_t x)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_array_iterator_is_empty(x);
}

uint64_t cbor_nondet_array_iterator_length(cbor_nondet_array_iterator_t x)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_array_iterator_length(x);
}

bool cbor_nondet_array_iterator_next(cbor_nondet_array_iterator_t *x, cbor_raw *dest)
{
  if (x == NULL || dest == NULL)
    return false;
  else if (cbor_nondet_array_iterator_is_empty(*x))
    return false;
  else
  {
    K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t
    scrut = CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_raw_data_item(*x);
    cbor_raw res = scrut.fst;
    *x = scrut.snd;
    *dest = res;
    return true;
  }
}

cbor_nondet_array_iterator_t
cbor_nondet_array_iterator_truncate(cbor_nondet_array_iterator_t x, uint64_t len)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_array_iterator_truncate(x, len);
}

bool cbor_nondet_get_array_item(cbor_raw x, uint64_t i, cbor_raw *dest)
{
  if (dest == NULL)
    return false;
  else if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_ARRAY)
    return false;
  else if (CBOR_Pulse_Raw_EverParse_ReadFields_cbor_raw_read_array_length(x) <= i)
    return false;
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_array(x);
    size_t
    total_sz =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    cbor_nondet_array_iterator_t ite0;
    if (total_sz == (size_t)0U)
      ite0 =
        (
          (cbor_nondet_array_iterator_t){
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
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite1;
      if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
      {
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        bi = ml.case_Base;
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
        size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
        size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
        size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
        ite1 =
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
        ite1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (cbor_nondet_array_iterator_t){
            .tag = IPair,
            { .case_IPair = { .before = bi_, .after = ite1 } }
          }
        );
    }
    cbor_nondet_array_iterator_t pit = ite0;
    uint64_t pj = 0ULL;
    bool pcont = 0ULL < i;
    while (pcont)
    {
      K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t
      scrut = CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_raw_data_item(pit);
      cbor_raw res = scrut.fst;
      pit = scrut.snd;
      KRML_MAYBE_UNUSED_VAR(res);
      uint64_t j_val = pj;
      pj = j_val + 1ULL;
      pcont = j_val + 1ULL < i;
    }
    K___CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_array_iterator_t
    scrut = CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_raw_data_item(pit);
    cbor_raw res = scrut.fst;
    pit = scrut.snd;
    *dest = res;
    return true;
  }
}

bool cbor_nondet_get_map_length(cbor_raw x, uint64_t *dest)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_get_map_length(x, dest);
}

bool cbor_nondet_map_iterator_start(cbor_raw x, cbor_nondet_map_iterator_t *dest)
{
  if (dest == NULL)
    return false;
  else if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_MAP)
    return false;
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map(x);
    size_t
    total_sz =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    cbor_nondet_map_iterator_t ite0;
    if (total_sz == (size_t)0U)
      ite0 =
        (
          (cbor_nondet_map_iterator_t){
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
      ite1;
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
        size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
        size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
        size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
        ite1 =
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
        ite1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (cbor_nondet_map_iterator_t){
            .tag = IPair,
            { .case_IPair = { .before = bi_, .after = ite1 } }
          }
        );
    }
    *dest = ite0;
    return true;
  }
}

bool cbor_nondet_map_iterator_is_empty(cbor_nondet_map_iterator_t x)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_iterator_is_empty(x);
}

cbor_raw cbor_nondet_map_entry_key(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_entry_key(x);
}

cbor_raw cbor_nondet_map_entry_value(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_entry_value(x);
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
    K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
    scrut = CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_map_entry_raw_data_item(*x);
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw res = scrut.fst;
    *x = scrut.snd;
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw res0 = res;
    cbor_raw res_key = cbor_nondet_map_entry_key(res0);
    cbor_raw res_value = cbor_nondet_map_entry_value(res0);
    *dest_key = res_key;
    *dest_value = res_value;
    return true;
  }
}

bool cbor_nondet_equal(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_equal(x1, x2);
}

bool cbor_nondet_map_get(cbor_raw x, cbor_raw k, cbor_raw *dest)
{
  if (dest == NULL)
    return false;
  else if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(x) != CBOR_MAJOR_TYPE_MAP)
    return false;
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map(x);
    size_t
    total_sz =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    cbor_nondet_map_iterator_t i;
    if (total_sz == (size_t)0U)
      i =
        (
          (cbor_nondet_map_iterator_t){
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
      i =
        (
          (cbor_nondet_map_iterator_t){
            .tag = IPair,
            { .case_IPair = { .before = bi_, .after = ite0 } }
          }
        );
    }
    cbor_nondet_map_iterator_t pi = i;
    bool pres = false;
    bool pcont = !CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_iterator_is_empty(i);
    while (pcont && !pres)
    {
      K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
      scrut = CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_map_entry_raw_data_item(pi);
      cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw res = scrut.fst;
      pi = scrut.snd;
      cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw y = res;
      if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_equal(y.cbor_map_entry_key, k))
      {
        *dest = y.cbor_map_entry_value;
        pres = true;
      }
      else
        pcont = !CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_iterator_is_empty(pi);
    }
    return pres;
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
    *dest = CBOR_Pulse_Raw_EverParse_Make_cbor_mk_simple_value(v);
    return true;
  }
}

cbor_raw cbor_nondet_mk_uint64(uint64_t v)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_uint64(v);
}

cbor_raw cbor_nondet_mk_neg_int64(uint64_t v)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_neg_int64(v);
}

cbor_raw cbor_nondet_mk_int64(int64_t v)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_int64(v);
}

bool cbor_nondet_mk_byte_string(uint8_t *a, uint64_t len, cbor_raw *dest)
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
      *dest =
        CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(CBOR_Pulse_Raw_EverParse_Make_cbor_mk_string(CBOR_MAJOR_TYPE_BYTE_STRING,
            s));
      return true;
    }
    else
      return false;
  }
}

bool cbor_nondet_mk_text_string(uint8_t *a, uint64_t len, cbor_raw *dest)
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
      *dest =
        CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(CBOR_Pulse_Raw_EverParse_Make_cbor_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING,
            s));
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
    CBOR_Spec_Raw_Optimal_mk_raw_uint64(tag);
    *dest =
      CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(CBOR_Pulse_Raw_EverParse_Make_cbor_mk_tagged(tag,
          r));
    return true;
  }
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  cbor_raw *a,
  size_t alen
)
{
  return
    ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){ .elt = a, .len = alen });
}

bool cbor_nondet_mk_array(cbor_raw *a, uint64_t len, cbor_raw *dest)
{
  bool __anf0 = a == NULL;
  if (__anf0 || dest == NULL)
    return false;
  else
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    s =
      Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
        (size_t)len);
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml =
      {
        .tag = LowParse_PulseParse_Iterator_Type_Base,
        { .case_Base = { .tag = LowParse_PulseParse_Iterator_Type_Slice, { .case_Slice = s } } }
      };
    *dest =
      CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(CBOR_Pulse_Raw_EverParse_Make_cbor_mk_array(CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)).size,
          ml));
    return true;
  }
}

cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_nondet_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  return CBOR_Pulse_API_Nondet_Common_cbor_nondet_mk_map_entry(xk, xv);
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
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

bool
cbor_nondet_mk_map(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *a,
  uint64_t len,
  cbor_raw *dest
)
{
  bool __anf0 = a == NULL;
  if (__anf0 || dest == NULL)
    return false;
  else
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    s =
      Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
        (size_t)len);
    if
    (
      Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)
      > (size_t)18446744073709551615ULL
    )
      return false;
    else if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_no_setoid_repeats(s))
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      ml =
        {
          .tag = LowParse_PulseParse_Iterator_Type_Base,
          { .case_Base = { .tag = LowParse_PulseParse_Iterator_Type_Slice, { .case_Slice = s } } }
        };
      *dest =
        CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(CBOR_Pulse_Raw_EverParse_Make_cbor_mk_map(CBOR_Spec_Raw_Optimal_mk_raw_uint64((uint64_t)Pulse_Lib_Slice_len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)).size,
            ml));
      return true;
    }
    else
      return false;
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
Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
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
Pulse_Lib_Slice_len__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t s
)
{
  return s.len;
}

static cbor_nondet_map_get_multiple_entry_t
Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t a,
  size_t i
)
{
  return a.elt[i];
}

static void
Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
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
  else if (CBOR_Pulse_API_Nondet_Common_cbor_nondet_major_type(map) != CBOR_MAJOR_TYPE_MAP)
    return false;
  else
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_API_Nondet_C_cbor_nondet_map_get_multiple_entry_t
    dests =
      Pulse_Lib_Slice_arrayptr_to_slice_intro__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(dest,
        len);
    size_t pi = (size_t)0U;
    size_t i0 = pi;
    bool
    cond =
      i0 <
        Pulse_Lib_Slice_len__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(dests);
    while (cond)
    {
      size_t i = pi;
      cbor_nondet_map_get_multiple_entry_t
      x =
        Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(dests,
          i);
      Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(dests,
        i,
        ((cbor_nondet_map_get_multiple_entry_t){ .key = x.key, .value = x.value, .found = false }));
      pi = i + (size_t)1U;
      size_t i0 = pi;
      cond =
        i0 <
          Pulse_Lib_Slice_len__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(dests);
    }
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = CBOR_Pulse_Raw_EverParse_Access_cbor_raw_get_map(map);
    size_t
    total_sz =
      LowParse_PulseParse_Iterator_Type_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    cbor_nondet_map_iterator_t ite0;
    if (total_sz == (size_t)0U)
      ite0 =
        (
          (cbor_nondet_map_iterator_t){
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
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s1 = bi.case_Singleton;
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
                  { .case_Singleton = s1 }
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
      ite1;
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
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s1 = bi.case_Singleton;
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
                  { .case_Singleton = s1 }
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
        size_t cb__sz = LowParse_PulseParse_Iterator_append_n_before_sz(len_sz, rest_sz, cb);
        size_t ca__sz = LowParse_PulseParse_Iterator_append_n_after_sz(len_sz, rest_sz, cb);
        size_t ob__sz = LowParse_PulseParse_Iterator_append_off_before_sz(len_sz, ob, cb);
        ite1 =
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
        ite1 =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (cbor_nondet_map_iterator_t){
            .tag = IPair,
            { .case_IPair = { .before = bi_, .after = ite1 } }
          }
        );
    }
    cbor_nondet_map_iterator_t piter = ite0;
    size_t i1 = pi;
    bool
    cond0 =
      i1 != (size_t)0U && !CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_iterator_is_empty(piter);
    while (cond0)
    {
      K___CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_API_Nondet_Type_cbor_nondet_map_iterator_t
      scrut = CBOR_Pulse_Raw_EverParse_ReadMapEntry_iterator_next_map_entry_raw_data_item(piter);
      cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw res = scrut.fst;
      piter = scrut.snd;
      cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw entry = res;
      size_t pj = (size_t)0U;
      size_t j0 = pj;
      size_t i0 = pi;
      bool
      cond =
        j0 <
          Pulse_Lib_Slice_len__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(dests)
        && i0 > (size_t)0U;
      while (cond)
      {
        size_t j = pj;
        pj = j + (size_t)1U;
        cbor_nondet_map_get_multiple_entry_t
        dest_entry =
          Pulse_Lib_Slice_op_Array_Access__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(dests,
            j);
        if
        (CBOR_Pulse_API_Nondet_Common_cbor_nondet_equal(dest_entry.key, entry.cbor_map_entry_key))
        {
          Pulse_Lib_Slice_op_Array_Assignment__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(dests,
            j,
            (
              (cbor_nondet_map_get_multiple_entry_t){
                .key = dest_entry.key,
                .value = CBOR_Pulse_Raw_EverParse_ResetPerm_cbor_raw_reset_perm(entry.cbor_map_entry_value),
                .found = true
              }
            ));
          if (!dest_entry.found)
            pi = pi - (size_t)1U;
        }
        size_t j0 = pj;
        size_t i = pi;
        cond =
          j0 <
            Pulse_Lib_Slice_len__CBOR_Pulse_API_Base_cbor_map_get_multiple_entry_t_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(dests)
          && i > (size_t)0U;
      }
      size_t i = pi;
      cond0 =
        i != (size_t)0U && !CBOR_Pulse_API_Nondet_Common_cbor_nondet_map_iterator_is_empty(piter);
    }
    return true;
  }
}


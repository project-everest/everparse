

#include "EverParquet.h"

typedef FStar_Pervasives_Native_option__int8_t variant_type;

typedef FStar_Pervasives_Native_option__Prims_string geometry_type;

bool
Parquet_Pulse_Toplevel_uu___is_ENCRYPTION_WITH_FOOTER_KEY(
  Parquet_Pulse_Toplevel_column_crypto_meta_data projectee
)
{
  if (projectee.tag == Parquet_Pulse_Toplevel_ENCRYPTION_WITH_FOOTER_KEY)
    return true;
  else
    return false;
}

bool
Parquet_Pulse_Toplevel_uu___is_ENCRYPTION_WITH_COLUMN_KEY(
  Parquet_Pulse_Toplevel_column_crypto_meta_data projectee
)
{
  if (projectee.tag == Parquet_Pulse_Toplevel_ENCRYPTION_WITH_COLUMN_KEY)
    return true;
  else
    return false;
}

static uint8_t op_Array_Access__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i)
{
  return a.elt[i];
}

bool Parquet_Pulse_Toplevel0_validate_is_PAR1(Pulse_Lib_Slice_slice__uint8_t input)
{
  uint8_t v0 = op_Array_Access__uint8_t(input, (size_t)0U);
  uint8_t v1 = op_Array_Access__uint8_t(input, (size_t)1U);
  uint8_t v2 = op_Array_Access__uint8_t(input, (size_t)2U);
  uint8_t v3 = op_Array_Access__uint8_t(input, (size_t)3U);
  return 80U == v0 && 65U == v1 && 82U == v2 && 49U == v3;
}

bool Parquet_Pulse_Toplevel0_impl_validate_row_group_aux(Parquet_Pulse_Toplevel_row_group rg)
{
  KRML_MAYBE_UNUSED_VAR(rg);
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__, "");
  KRML_HOST_EXIT(255U);
}

static bool uu___is_Some__int64_t(FStar_Pervasives_Native_option__int64_t projectee)
{
  if (projectee.tag == FStar_Pervasives_Native_Some)
    return true;
  else
    return false;
}

FStar_Pervasives_Native_option__int64_t
Parquet_Pulse_Toplevel0_compute_cols_size(
  bool *poverflow,
  Parquet_Pulse_Vec_vec__Parquet_Pulse_Toplevel_column_chunk cc,
  int64_t bound
)
{
  *poverflow = bound < (int64_t)0;
  FStar_Pervasives_Native_option__int64_t
  paccu = { .tag = FStar_Pervasives_Native_Some, .v = (int64_t)0 };
  size_t pi = (size_t)0U;
  FStar_Pervasives_Native_option__int64_t accu0 = paccu;
  bool cond;
  if (uu___is_Some__int64_t(accu0))
  {
    size_t i = pi;
    cond = i < cc.len;
  }
  else
    cond = false;
  while (cond)
  {
    size_t i0 = pi;
    Parquet_Pulse_Toplevel_column_chunk impl = cc.data[i0];
    if (impl.meta_data.tag == FStar_Pervasives_Native_None)
      paccu = ((FStar_Pervasives_Native_option__int64_t){ .tag = FStar_Pervasives_Native_None });
    else if (impl.meta_data.tag == FStar_Pervasives_Native_Some)
    {
      Parquet_Pulse_Toplevel_column_meta_data md = impl.meta_data.v;
      bool overflow = *poverflow;
      pi = i0 + (size_t)1U;
      if (!overflow)
      {
        FStar_Pervasives_Native_option__int64_t __anf0 = paccu;
        int64_t accu;
        if (__anf0.tag == FStar_Pervasives_Native_Some)
          accu = __anf0.v;
        else
          accu = KRML_EABORT(int64_t, "unreachable (pattern matches are exhaustive in F*)");
        if (bound - accu < md.total_compressed_size)
          *poverflow = true;
        else
          paccu =
            (
              (FStar_Pervasives_Native_option__int64_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = accu + md.total_compressed_size
              }
            );
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
    FStar_Pervasives_Native_option__int64_t accu = paccu;
    bool ite;
    if (uu___is_Some__int64_t(accu))
    {
      size_t i = pi;
      ite = i < cc.len;
    }
    else
      ite = false;
    cond = ite;
  }
  return paccu;
}

bool
Parquet_Pulse_Toplevel0_impl_column_size_nonnegative(Parquet_Pulse_Toplevel_column_chunk cc)
{
  if (cc.meta_data.tag == FStar_Pervasives_Native_None)
    return true;
  else if (cc.meta_data.tag == FStar_Pervasives_Native_Some)
  {
    Parquet_Pulse_Toplevel_column_meta_data md = cc.meta_data.v;
    return (int64_t)0 <= md.total_compressed_size;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

int64_t
Parquet_Pulse_Toplevel0_impl_offset_of_column_chunk(Parquet_Pulse_Toplevel_column_meta_data cc)
{
  if (cc.dictionary_page_offset.tag == FStar_Pervasives_Native_Some)
    return cc.dictionary_page_offset.v;
  else if (cc.dictionary_page_offset.tag == FStar_Pervasives_Native_None)
    if (cc.index_page_offset.tag == FStar_Pervasives_Native_Some)
    {
      int64_t off = cc.index_page_offset.v;
      if (off < cc.data_page_offset)
        return off;
      else
        return cc.data_page_offset;
    }
    else if (cc.index_page_offset.tag == FStar_Pervasives_Native_None)
      return cc.data_page_offset;
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

typedef struct option__Parquet_Pulse_Toplevel_column_chunk_s
{
  FStar_Pervasives_Native_option____ tag;
  Parquet_Pulse_Toplevel_column_chunk v;
}
option__Parquet_Pulse_Toplevel_column_chunk;

FStar_Pervasives_Native_option__int64_t
Parquet_Pulse_Toplevel0_impl_first_column_offset(Parquet_Pulse_Toplevel_row_group rg)
{
  option__Parquet_Pulse_Toplevel_column_chunk first_column;
  if ((size_t)0U == rg.columns.len)
    first_column =
      ((option__Parquet_Pulse_Toplevel_column_chunk){ .tag = FStar_Pervasives_Native_None });
  else
  {
    Parquet_Pulse_Toplevel_column_chunk rv = rg.columns.data[0U];
    first_column =
      (
        (option__Parquet_Pulse_Toplevel_column_chunk){
          .tag = FStar_Pervasives_Native_Some,
          .v = rv
        }
      );
  }
  if (first_column.tag == FStar_Pervasives_Native_None)
    return ((FStar_Pervasives_Native_option__int64_t){ .tag = FStar_Pervasives_Native_None });
  else if (first_column.tag == FStar_Pervasives_Native_Some)
  {
    Parquet_Pulse_Toplevel_column_chunk first = first_column.v;
    if (first.meta_data.tag == FStar_Pervasives_Native_Some)
    {
      Parquet_Pulse_Toplevel_column_meta_data cmd = first.meta_data.v;
      int64_t res = Parquet_Pulse_Toplevel0_impl_offset_of_column_chunk(cmd);
      return
        ((FStar_Pervasives_Native_option__int64_t){ .tag = FStar_Pervasives_Native_Some, .v = res });
    }
    else if (first.meta_data.tag == FStar_Pervasives_Native_None)
      return ((FStar_Pervasives_Native_option__int64_t){ .tag = FStar_Pervasives_Native_None });
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

FStar_Pervasives_Native_option___int64_t___int64_t_
Parquet_Pulse_Toplevel0_impl_rg_range(
  Parquet_Pulse_Toplevel_row_group rg,
  FStar_Pervasives_Native_option__int64_t csz
)
{
  FStar_Pervasives_Native_option__int64_t
  fco = Parquet_Pulse_Toplevel0_impl_first_column_offset(rg);
  if (uu___is_Some__int64_t(fco) && uu___is_Some__int64_t(rg.total_compressed_size1))
  {
    int64_t ite0;
    if (fco.tag == FStar_Pervasives_Native_Some)
      ite0 = fco.v;
    else
      ite0 = KRML_EABORT(int64_t, "unreachable (pattern matches are exhaustive in F*)");
    int64_t ite;
    if (rg.total_compressed_size1.tag == FStar_Pervasives_Native_Some)
      ite = rg.total_compressed_size1.v;
    else
      ite = KRML_EABORT(int64_t, "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (FStar_Pervasives_Native_option___int64_t___int64_t_){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = ite0, .snd = ite }
        }
      );
  }
  else if (csz.tag == FStar_Pervasives_Native_None)
    return
      ((FStar_Pervasives_Native_option___int64_t___int64_t_){ .tag = FStar_Pervasives_Native_None });
  else if (csz.tag == FStar_Pervasives_Native_Some)
  {
    int64_t total_sz = csz.v;
    option__Parquet_Pulse_Toplevel_column_chunk o;
    if ((size_t)0U == rg.columns.len)
      o = ((option__Parquet_Pulse_Toplevel_column_chunk){ .tag = FStar_Pervasives_Native_None });
    else
    {
      Parquet_Pulse_Toplevel_column_chunk rv = rg.columns.data[0U];
      o =
        (
          (option__Parquet_Pulse_Toplevel_column_chunk){
            .tag = FStar_Pervasives_Native_Some,
            .v = rv
          }
        );
    }
    if (o.tag == FStar_Pervasives_Native_None)
      return
        (
          (FStar_Pervasives_Native_option___int64_t___int64_t_){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else if (o.tag == FStar_Pervasives_Native_Some)
    {
      Parquet_Pulse_Toplevel_column_chunk first = o.v;
      if (first.meta_data.tag == FStar_Pervasives_Native_None)
        return
          (
            (FStar_Pervasives_Native_option___int64_t___int64_t_){
              .tag = FStar_Pervasives_Native_None
            }
          );
      else if (first.meta_data.tag == FStar_Pervasives_Native_Some)
      {
        Parquet_Pulse_Toplevel_column_meta_data cmd = first.meta_data.v;
        int64_t off = Parquet_Pulse_Toplevel0_impl_offset_of_column_chunk(cmd);
        return
          (
            (FStar_Pervasives_Native_option___int64_t___int64_t_){
              .tag = FStar_Pervasives_Native_Some,
              .v = { .fst = off, .snd = total_sz }
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

bool
Parquet_Pulse_Toplevel0_impl_rg_disjoint(
  FStar_Pervasives_Native_option___int64_t___int64_t_ rg,
  size_t n,
  FStar_Pervasives_Native_option___int64_t___int64_t_ *crg,
  size_t i
)
{
  KRML_MAYBE_UNUSED_VAR(rg);
  KRML_MAYBE_UNUSED_VAR(n);
  KRML_MAYBE_UNUSED_VAR(crg);
  KRML_MAYBE_UNUSED_VAR(i);
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__, "");
  KRML_HOST_EXIT(255U);
}

bool
Parquet_Pulse_Toplevel0_impl_validate_file_meta_data_aux(
  int64_t data_size,
  Parquet_Pulse_Vec_vec__Parquet_Pulse_Toplevel_row_group l
)
{
  if ((size_t)0U == l.len)
    return true;
  else
  {
    KRML_CHECK_SIZE(sizeof (FStar_Pervasives_Native_option___int64_t___int64_t_), l.len);
    FStar_Pervasives_Native_option___int64_t___int64_t_
    *rg_ranges =
      KRML_HOST_MALLOC(sizeof (FStar_Pervasives_Native_option___int64_t___int64_t_) * l.len);
    if (rg_ranges != NULL)
      for (uint32_t _i = 0U; _i < l.len; ++_i)
        rg_ranges[_i] =
          (
            (FStar_Pervasives_Native_option___int64_t___int64_t_){
              .tag = FStar_Pervasives_Native_None
            }
          );
    bool pres = true;
    size_t pi = l.len;
    bool res = pres;
    bool cond0;
    if (res)
    {
      size_t __anf0 = pi;
      cond0 = __anf0 != (size_t)0U;
    }
    else
      cond0 = false;
    while (cond0)
    {
      size_t i_ = pi;
      size_t i = i_ - (size_t)1U;
      Parquet_Pulse_Toplevel_row_group rg = l.data[i];
      pi = i;
      size_t pi1 = (size_t)0U;
      bool pres1 = true;
      bool __anf00 = pres1;
      bool cond;
      if (__anf00)
      {
        size_t i1 = pi1;
        cond = i1 < rg.columns.len;
      }
      else
        cond = false;
      while (cond)
      {
        size_t i10 = pi1;
        Parquet_Pulse_Toplevel_column_chunk elt = rg.columns.data[i10];
        bool res = Parquet_Pulse_Toplevel0_impl_column_size_nonnegative(elt);
        pres1 = res;
        if (res)
          pi1 = i10 + (size_t)1U;
        bool __anf0 = pres1;
        bool ite;
        if (__anf0)
        {
          size_t i1 = pi1;
          ite = i1 < rg.columns.len;
        }
        else
          ite = false;
        cond = ite;
      }
      bool __anf01 = pres1;
      if (!__anf01)
        pres = false;
      else
      {
        bool poverflow = false;
        int64_t bound;
        if (rg.total_compressed_size1.tag == FStar_Pervasives_Native_None)
          bound = data_size;
        else if (rg.total_compressed_size1.tag == FStar_Pervasives_Native_Some)
          bound = rg.total_compressed_size1.v;
        else
          bound = KRML_EABORT(int64_t, "unreachable (pattern matches are exhaustive in F*)");
        if (data_size < bound)
          pres = false;
        else
        {
          FStar_Pervasives_Native_option__int64_t
          csz = Parquet_Pulse_Toplevel0_compute_cols_size(&poverflow, rg.columns, bound);
          bool overflow = poverflow;
          bool ite;
          if (csz.tag == FStar_Pervasives_Native_Some)
          {
            int64_t sz = csz.v;
            ite = overflow || sz > bound;
          }
          else
            ite = false;
          if (ite)
            pres = false;
          else
          {
            FStar_Pervasives_Native_option___int64_t___int64_t_
            rrg = Parquet_Pulse_Toplevel0_impl_rg_range(rg, csz);
            rg_ranges[i] = rrg;
            bool __anf01 = Parquet_Pulse_Toplevel0_impl_rg_disjoint(rrg, l.len, rg_ranges, i_);
            pres = __anf01;
          }
        }
      }
      bool res = pres;
      bool ite;
      if (res)
      {
        size_t __anf0 = pi;
        ite = __anf0 != (size_t)0U;
      }
      else
        ite = false;
      cond0 = ite;
    }
    KRML_HOST_FREE(rg_ranges);
    return pres;
  }
}

bool
Parquet_Pulse_Toplevel0_impl_validate_file_meta_data(
  size_t footer_start,
  Parquet_Pulse_Toplevel_file_meta_data md
)
{
  uint64_t footer_start_u64 = (uint64_t)footer_start;
  if ((size_t)footer_start_u64 != footer_start)
    return false;
  else if (footer_start_u64 >= 9223372036854775808ULL)
    return false;
  else
  {
    int64_t footer_start64 = (int64_t)footer_start_u64;
    bool
    __anf0 =
      Parquet_Pulse_Toplevel0_impl_validate_file_meta_data_aux(footer_start64,
        md.row_groups);
    if (__anf0)
    {
      size_t pi = (size_t)0U;
      bool pres = true;
      bool __anf01 = pres;
      bool cond;
      if (__anf01)
      {
        size_t i = pi;
        cond = i < md.row_groups.len;
      }
      else
        cond = false;
      while (cond)
      {
        size_t i0 = pi;
        Parquet_Pulse_Toplevel_row_group elt = md.row_groups.data[i0];
        bool res = Parquet_Pulse_Toplevel0_impl_validate_row_group_aux(elt);
        pres = res;
        if (res)
          pi = i0 + (size_t)1U;
        bool __anf01 = pres;
        bool ite;
        if (__anf01)
        {
          size_t i = pi;
          ite = i < md.row_groups.len;
        }
        else
          ite = false;
        cond = ite;
      }
      return pres;
    }
    else
      return false;
  }
}

static size_t len__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.len;
}

bool
Parquet_Pulse_Toplevel0_impl_validate_page_data(
  Pulse_Lib_Slice_slice__uint8_t ph,
  Pulse_Lib_Slice_slice__uint8_t data
)
{
  Parquet_Pulse_Toplevel_page_header ph_ = Parquet_Pulse_Toplevel0_read_page_header(ph);
  if (ph_.compressed_page_size < (int32_t)0)
    return false;
  else
    return (size_t)(uint32_t)ph_.compressed_page_size == len__uint8_t(data);
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

typedef struct
__Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t__s
{
  Pulse_Lib_Slice_slice__uint8_t fst;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t snd;
}
__Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_;

bool
Parquet_Pulse_Toplevel0_validate_page(Pulse_Lib_Slice_slice__uint8_t input, size_t *poffset)
{
  size_t offset1 = *poffset;
  bool is_valid1 = Parquet_Pulse_Toplevel0_validate_page_header(input, poffset);
  if (is_valid1)
  {
    size_t off = *poffset;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    s_ = split__uint8_t(input, offset1);
    Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s10, .snd = s20 };
    Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t input230 = _letpattern.snd;
    size_t consumed0 = off - offset1;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(input230, consumed0);
    Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern1.fst;
    Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern1.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern10 = { .fst = s11, .snd = s21 };
    Pulse_Lib_Slice_slice__uint8_t left0 = _letpattern10.fst;
    Pulse_Lib_Slice_slice__uint8_t right0 = _letpattern10.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern11 = { .fst = left0, .snd = right0 };
    Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern11.fst;
    Pulse_Lib_Slice_slice__uint8_t input30 = _letpattern11.snd;
    __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
    _letpattern0 = { .fst = input10, .snd = { .fst = input20, .snd = input30 } };
    Pulse_Lib_Slice_slice__uint8_t xr = _letpattern0.snd.snd;
    Pulse_Lib_Slice_slice__uint8_t x = _letpattern0.snd.fst;
    *poffset = (size_t)0U;
    size_t offset2 = *poffset;
    *poffset = len__uint8_t(xr);
    bool is_valid = true;
    bool res;
    if (is_valid)
    {
      size_t off1 = *poffset;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      s_ = split__uint8_t(xr, offset2);
      Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern1 = { .fst = s10, .snd = s20 };
      Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern1.fst;
      Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern1.snd;
      size_t consumed = off1 - offset2;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(input23, consumed);
      Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern2.fst;
      Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern2.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern20 = { .fst = s1, .snd = s2 };
      Pulse_Lib_Slice_slice__uint8_t left = _letpattern20.fst;
      Pulse_Lib_Slice_slice__uint8_t right = _letpattern20.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern21 = { .fst = left, .snd = right };
      Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern21.fst;
      Pulse_Lib_Slice_slice__uint8_t input3 = _letpattern21.snd;
      __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
      _letpattern10 = { .fst = input1, .snd = { .fst = input2, .snd = input3 } };
      Pulse_Lib_Slice_slice__uint8_t x1 = _letpattern10.snd.fst;
      res = Parquet_Pulse_Toplevel0_impl_validate_page_data(x, x1);
    }
    else
      res = false;
    if (res)
    {
      size_t off_ = *poffset;
      *poffset = off + off_;
      return true;
    }
    else
      return false;
  }
  else
    return false;
}

bool
Parquet_Pulse_Toplevel0_impl_validate_offset_index_all(
  Parquet_Pulse_Toplevel_column_chunk cc,
  Pulse_Lib_Slice_slice__uint8_t data,
  Parquet_Pulse_Toplevel_offset_index oi
)
{
  KRML_MAYBE_UNUSED_VAR(cc);
  KRML_MAYBE_UNUSED_VAR(data);
  KRML_MAYBE_UNUSED_VAR(oi);
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__, "");
  KRML_HOST_EXIT(255U);
}

bool
Parquet_Pulse_Toplevel0_impl_validate_offset_index_all0(
  Pulse_Lib_Slice_slice__uint8_t data,
  Parquet_Pulse_Toplevel_column_chunk cc,
  Pulse_Lib_Slice_slice__uint8_t x
)
{
  Parquet_Pulse_Toplevel_offset_index oi = Parquet_Pulse_Toplevel0_read_offset_index(x);
  return Parquet_Pulse_Toplevel0_impl_validate_offset_index_all(cc, data, oi);
}

bool
Parquet_Pulse_Toplevel0_validate_jump_offset_index(
  size_t offset_sz,
  size_t length_sz,
  Pulse_Lib_Slice_slice__uint8_t data,
  Parquet_Pulse_Toplevel_column_chunk cc,
  Pulse_Lib_Slice_slice__uint8_t input
)
{
  if (offset_sz > len__uint8_t(input))
    return false;
  else if (length_sz > len__uint8_t(input) - offset_sz)
    return false;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    s_ = split__uint8_t(input, offset_sz + length_sz);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t s10 = _letpattern.fst;
    size_t poffset = offset_sz;
    size_t offset = poffset;
    bool is_valid0 = Parquet_Pulse_Toplevel0_validate_offset_index(s10, &poffset);
    bool is_valid;
    if (is_valid0)
    {
      size_t off = poffset;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      s_ = split__uint8_t(s10, offset);
      Pulse_Lib_Slice_slice__uint8_t s110 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s210 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern1 = { .fst = s110, .snd = s210 };
      Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern1.fst;
      Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern1.snd;
      size_t consumed = off - offset;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(input23, consumed);
      Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern2.fst;
      Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern2.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern20 = { .fst = s11, .snd = s21 };
      Pulse_Lib_Slice_slice__uint8_t left = _letpattern20.fst;
      Pulse_Lib_Slice_slice__uint8_t right = _letpattern20.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern21 = { .fst = left, .snd = right };
      Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern21.fst;
      Pulse_Lib_Slice_slice__uint8_t input3 = _letpattern21.snd;
      __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
      _letpattern10 = { .fst = input1, .snd = { .fst = input2, .snd = input3 } };
      Pulse_Lib_Slice_slice__uint8_t x = _letpattern10.snd.fst;
      is_valid = Parquet_Pulse_Toplevel0_impl_validate_offset_index_all0(data, cc, x);
    }
    else
      is_valid = false;
    size_t off = poffset;
    return off == offset_sz + length_sz && is_valid;
  }
}

static bool uu___is_Some__int32_t(FStar_Pervasives_Native_option__int32_t projectee)
{
  if (projectee.tag == FStar_Pervasives_Native_Some)
    return true;
  else
    return false;
}

bool
Parquet_Pulse_Toplevel0_impl_validate_all_validate_column_chunk(
  Pulse_Lib_Slice_slice__uint8_t data,
  Parquet_Pulse_Toplevel_column_chunk cc
)
{
  if
  (
    uu___is_Some__int64_t(cc.offset_index_offset) && uu___is_Some__int32_t(cc.offset_index_length)
  )
  {
    FStar_Pervasives_Native_option__int64_t _letpattern = cc.offset_index_offset;
    if (_letpattern.tag == FStar_Pervasives_Native_Some)
    {
      int64_t offset = _letpattern.v;
      FStar_Pervasives_Native_option__int32_t _letpattern1 = cc.offset_index_length;
      if (_letpattern1.tag == FStar_Pervasives_Native_Some)
      {
        int32_t length = _letpattern1.v;
        size_t offset_sz = (size_t)(uint64_t)offset;
        size_t length_sz = (size_t)(uint32_t)length;
        if ((int64_t)0 <= offset && (int32_t)0 <= length)
          return
            Parquet_Pulse_Toplevel0_validate_jump_offset_index(offset_sz,
              length_sz,
              data,
              cc,
              data);
        else
          return false;
      }
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
  else
    return true;
}

bool
Parquet_Pulse_Toplevel0_impl_validate_all_validate_row_group(
  Pulse_Lib_Slice_slice__uint8_t data,
  Parquet_Pulse_Toplevel_row_group rg
)
{
  size_t pi = (size_t)0U;
  bool pres = true;
  bool __anf0 = pres;
  bool cond;
  if (__anf0)
  {
    size_t i = pi;
    cond = i < rg.columns.len;
  }
  else
    cond = false;
  while (cond)
  {
    size_t i0 = pi;
    Parquet_Pulse_Toplevel_column_chunk elt = rg.columns.data[i0];
    bool res = Parquet_Pulse_Toplevel0_impl_validate_all_validate_column_chunk(data, elt);
    pres = res;
    if (res)
      pi = i0 + (size_t)1U;
    bool __anf0 = pres;
    bool ite;
    if (__anf0)
    {
      size_t i = pi;
      ite = i < rg.columns.len;
    }
    else
      ite = false;
    cond = ite;
  }
  return pres;
}

bool Parquet_Pulse_Toplevel0_validate_header_magic_number(Pulse_Lib_Slice_slice__uint8_t input)
{
  if ((size_t)0U > len__uint8_t(input))
    return false;
  else if ((size_t)4U > len__uint8_t(input) - (size_t)0U)
    return false;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    s_ = split__uint8_t(input, (size_t)4U);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t s10 = _letpattern.fst;
    size_t poffset = (size_t)0U;
    size_t offset = poffset;
    size_t offset1 = poffset;
    bool is_valid0;
    if (len__uint8_t(s10) - offset1 < (size_t)4U)
      is_valid0 = false;
    else
    {
      poffset = offset1 + (size_t)4U;
      is_valid0 = true;
    }
    bool is_valid;
    if (is_valid0)
    {
      size_t off = poffset;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      s_ = split__uint8_t(s10, offset);
      Pulse_Lib_Slice_slice__uint8_t s110 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s210 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern1 = { .fst = s110, .snd = s210 };
      Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern1.fst;
      Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern1.snd;
      size_t consumed = off - offset;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(input23, consumed);
      Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern2.fst;
      Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern2.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern20 = { .fst = s11, .snd = s21 };
      Pulse_Lib_Slice_slice__uint8_t left = _letpattern20.fst;
      Pulse_Lib_Slice_slice__uint8_t right = _letpattern20.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern21 = { .fst = left, .snd = right };
      Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern21.fst;
      Pulse_Lib_Slice_slice__uint8_t input3 = _letpattern21.snd;
      __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
      _letpattern10 = { .fst = input1, .snd = { .fst = input2, .snd = input3 } };
      Pulse_Lib_Slice_slice__uint8_t x = _letpattern10.snd.fst;
      is_valid = Parquet_Pulse_Toplevel0_validate_is_PAR1(x);
    }
    else
      is_valid = false;
    size_t off = poffset;
    return off == (size_t)4U && is_valid;
  }
}

bool
Parquet_Pulse_Toplevel0_impl_validate_all0(
  Parquet_Pulse_Toplevel_file_meta_data fmd,
  Pulse_Lib_Slice_slice__uint8_t data
)
{
  size_t footer_start = len__uint8_t(data);
  bool res1 = Parquet_Pulse_Toplevel0_impl_validate_file_meta_data(footer_start, fmd);
  if (res1)
  {
    bool res2 = Parquet_Pulse_Toplevel0_validate_header_magic_number(data);
    if (res2)
    {
      size_t pi = (size_t)0U;
      bool pres = true;
      bool __anf0 = pres;
      bool cond;
      if (__anf0)
      {
        size_t i = pi;
        cond = i < fmd.row_groups.len;
      }
      else
        cond = false;
      while (cond)
      {
        size_t i0 = pi;
        Parquet_Pulse_Toplevel_row_group elt = fmd.row_groups.data[i0];
        bool res = Parquet_Pulse_Toplevel0_impl_validate_all_validate_row_group(data, elt);
        pres = res;
        if (res)
          pi = i0 + (size_t)1U;
        bool __anf0 = pres;
        bool ite;
        if (__anf0)
        {
          size_t i = pi;
          ite = i < fmd.row_groups.len;
        }
        else
          ite = false;
        cond = ite;
      }
      return pres;
    }
    else
      return false;
  }
  else
    return false;
}

bool
Parquet_Pulse_Toplevel0_impl_validate_all(
  uint32_t len,
  Pulse_Lib_Slice_slice__uint8_t y,
  Pulse_Lib_Slice_slice__uint8_t x
)
{
  KRML_MAYBE_UNUSED_VAR(len);
  Parquet_Pulse_Toplevel_file_meta_data f = Parquet_Pulse_Toplevel0_read_footer(y);
  return Parquet_Pulse_Toplevel0_impl_validate_all0(f, x);
}

bool
Parquet_Pulse_Toplevel0_validate_parquet(Pulse_Lib_Slice_slice__uint8_t input, size_t *poffset)
{
  size_t input_len = len__uint8_t(input);
  size_t offset1 = *poffset;
  if (input_len - offset1 < (size_t)4U)
    return false;
  else
  {
    size_t off = input_len - (size_t)4U;
    size_t poff = off;
    size_t offset20 = poff;
    size_t offset30 = poff;
    bool is_valid0;
    if (len__uint8_t(input) - offset30 < (size_t)4U)
      is_valid0 = false;
    else
    {
      poff = offset30 + (size_t)4U;
      is_valid0 = true;
    }
    bool is_valid2;
    if (is_valid0)
    {
      size_t off1 = poff;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      s_ = split__uint8_t(input, offset20);
      Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern = { .fst = s10, .snd = s20 };
      Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern.fst;
      Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
      size_t consumed = off1 - offset20;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern1 = split__uint8_t(input23, consumed);
      Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern1.fst;
      Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern1.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern10 = { .fst = s1, .snd = s2 };
      Pulse_Lib_Slice_slice__uint8_t left = _letpattern10.fst;
      Pulse_Lib_Slice_slice__uint8_t right = _letpattern10.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern11 = { .fst = left, .snd = right };
      Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern11.fst;
      Pulse_Lib_Slice_slice__uint8_t input3 = _letpattern11.snd;
      __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
      _letpattern0 = { .fst = input1, .snd = { .fst = input2, .snd = input3 } };
      Pulse_Lib_Slice_slice__uint8_t x = _letpattern0.snd.fst;
      is_valid2 = Parquet_Pulse_Toplevel0_validate_is_PAR1(x);
    }
    else
      is_valid2 = false;
    if (is_valid2)
    {
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(input, off);
      Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern = { .fst = s10, .snd = s20 };
      Pulse_Lib_Slice_slice__uint8_t l = _letpattern.fst;
      size_t input_len1 = len__uint8_t(l);
      size_t offset2 = *poffset;
      bool is_valid10;
      if (input_len1 - offset2 < (size_t)4U)
        is_valid10 = false;
      else
      {
        size_t off1 = input_len1 - (size_t)4U;
        size_t poff1 = off1;
        size_t offset30 = poff1;
        bool is_valid21;
        if (len__uint8_t(l) - offset30 < (size_t)4U)
          is_valid21 = false;
        else
        {
          poff1 = offset30 + (size_t)4U;
          is_valid21 = true;
        }
        if (is_valid21)
        {
          size_t off_ = poff1;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          s_ = split__uint8_t(l, off1);
          Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
          Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern1 = { .fst = s10, .snd = s20 };
          Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern1.fst;
          Pulse_Lib_Slice_slice__uint8_t input230 = _letpattern1.snd;
          size_t consumed0 = off_ - off1;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern2 = split__uint8_t(input230, consumed0);
          Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern2.fst;
          Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern2.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern20 = { .fst = s11, .snd = s21 };
          Pulse_Lib_Slice_slice__uint8_t left0 = _letpattern20.fst;
          Pulse_Lib_Slice_slice__uint8_t right0 = _letpattern20.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern21 = { .fst = left0, .snd = right0 };
          Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern21.fst;
          Pulse_Lib_Slice_slice__uint8_t input30 = _letpattern21.snd;
          __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
          _letpattern10 = { .fst = input10, .snd = { .fst = input20, .snd = input30 } };
          Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern10.snd.fst;
          size_t pos_ = (size_t)1U;
          uint8_t first = op_Array_Access__uint8_t(input_, (size_t)0U);
          size_t pos_1 = pos_ + (size_t)1U;
          uint8_t first1 = op_Array_Access__uint8_t(input_, pos_);
          size_t pos_2 = pos_1 + (size_t)1U;
          uint8_t first2 = op_Array_Access__uint8_t(input_, pos_1);
          uint8_t first3 = op_Array_Access__uint8_t(input_, pos_2);
          uint32_t n = (uint32_t)first3;
          uint32_t bfirst0 = (uint32_t)first2;
          uint32_t n0 = bfirst0 + n * 256U;
          uint32_t bfirst1 = (uint32_t)first1;
          uint32_t n1 = bfirst1 + n0 * 256U;
          uint32_t bfirst = (uint32_t)first;
          uint32_t x = bfirst + n1 * 256U;
          uint32_t x0 = x;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          s_0 = split__uint8_t(l, off1);
          Pulse_Lib_Slice_slice__uint8_t s12 = s_0.fst;
          Pulse_Lib_Slice_slice__uint8_t s22 = s_0.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern11 = { .fst = s12, .snd = s22 };
          Pulse_Lib_Slice_slice__uint8_t l1 = _letpattern11.fst;
          size_t input_len2 = len__uint8_t(l1);
          size_t offset3 = *poffset;
          bool is_valid11;
          if (input_len2 - offset3 < (size_t)x0)
            is_valid11 = false;
          else
          {
            size_t off2 = input_len2 - (size_t)x0;
            size_t poff2 = off2;
            size_t off30 = poff2;
            bool is_valid22;
            if (len__uint8_t(l1) - off30 < (size_t)x0)
              is_valid22 = false;
            else
            {
              size_t off_len = off30 + (size_t)x0;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              s_ = split__uint8_t(l1, off_len);
              Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
              Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern2 = { .fst = s1, .snd = s2 };
              Pulse_Lib_Slice_slice__uint8_t inl = _letpattern2.fst;
              bool res = Parquet_Pulse_Toplevel0_validate_footer(inl, &poff2);
              size_t off_1 = poff2;
              is_valid22 = res && off_1 == off_len;
            }
            if (is_valid22)
            {
              size_t off_1 = poff2;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              s_ = split__uint8_t(l1, off2);
              Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
              Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern2 = { .fst = s10, .snd = s20 };
              Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern2.fst;
              Pulse_Lib_Slice_slice__uint8_t input230 = _letpattern2.snd;
              size_t consumed0 = off_1 - off2;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern3 = split__uint8_t(input230, consumed0);
              Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern3.fst;
              Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern3.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern30 = { .fst = s11, .snd = s21 };
              Pulse_Lib_Slice_slice__uint8_t left0 = _letpattern30.fst;
              Pulse_Lib_Slice_slice__uint8_t right0 = _letpattern30.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern31 = { .fst = left0, .snd = right0 };
              Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern31.fst;
              Pulse_Lib_Slice_slice__uint8_t input30 = _letpattern31.snd;
              __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
              _letpattern20 = { .fst = input10, .snd = { .fst = input20, .snd = input30 } };
              Pulse_Lib_Slice_slice__uint8_t y = _letpattern20.snd.fst;
              Pulse_Lib_Slice_slice__uint8_t l2 = _letpattern20.fst;
              size_t offset4 = *poffset;
              *poffset = len__uint8_t(l2);
              bool is_valid = true;
              bool is_valid1;
              if (is_valid)
              {
                size_t off3 = *poffset;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                s_ = split__uint8_t(l2, offset4);
                Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
                Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern3 = { .fst = s10, .snd = s20 };
                Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern3.fst;
                Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern3.snd;
                size_t consumed = off3 - offset4;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern4 = split__uint8_t(input23, consumed);
                Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern4.fst;
                Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern4.snd;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern40 = { .fst = s1, .snd = s2 };
                Pulse_Lib_Slice_slice__uint8_t left = _letpattern40.fst;
                Pulse_Lib_Slice_slice__uint8_t right = _letpattern40.snd;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern41 = { .fst = left, .snd = right };
                Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern41.fst;
                Pulse_Lib_Slice_slice__uint8_t input3 = _letpattern41.snd;
                __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
                _letpattern30 = { .fst = input1, .snd = { .fst = input2, .snd = input3 } };
                Pulse_Lib_Slice_slice__uint8_t x1 = _letpattern30.snd.fst;
                is_valid1 = Parquet_Pulse_Toplevel0_impl_validate_all(x0, y, x1);
              }
              else
                is_valid1 = false;
              *poffset = input_len2;
              is_valid11 = is_valid1;
            }
            else
              is_valid11 = false;
          }
          *poffset = input_len1;
          is_valid10 = is_valid11;
        }
        else
          is_valid10 = false;
      }
      *poffset = input_len;
      return is_valid10;
    }
    else
      return false;
  }
}




#include "COSE_EverCrypt.h"

#include "COSE_Format.h"
#include "CBORDetAPI.h"
#include "internal/fstar.h"
#include "internal/COSE_Format.h"

extern void EverCrypt_Ed25519_sign(uint8_t *x0, uint8_t *x1, uint32_t x2, uint8_t *x3);

extern void abort(void);

COSE_Format_evercddl_int COSE_EverCrypt_mk_int(int32_t i)
{
  return
    i < 0 ? (
            (COSE_Format_evercddl_int){
              .tag = COSE_Format_Mkevercddl_int1,
              { .case_Mkevercddl_int1 = (uint64_t)(-1 - i) }
            }
          )
          : (
            (COSE_Format_evercddl_int){
              .tag = COSE_Format_Mkevercddl_int0,
              { .case_Mkevercddl_int0 = (uint64_t)i }
            }
          );
}

static Pulse_Lib_Slice_slice__uint8_t
subslice__uint8_t(Pulse_Lib_Slice_slice__uint8_t s, size_t i, size_t j)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = s.elt + i, .len = j - i });
}

void
COSE_EverCrypt_create_sig(
  uint8_t *privkey,
  COSE_Format_empty_or_serialized_map phdr,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t payload,
  uint8_t *sigbuf
)
{
  uint8_t *arr = KRML_HOST_CALLOC((size_t)1024U, sizeof (uint8_t));
  Pulse_Lib_Slice_slice__uint8_t
  outbuf = Pulse_Lib_Slice_from_array__uint8_t(arr, (size_t)1024U);
  size_t
  written =
    COSE_Format_serialize_sig_structure((
        (COSE_Format_sig_structure){
          .context = COSE_Format_Inr,
          .body_protected = phdr,
          ._x0 = { .tag = COSE_Format_Inr, { .case_Inr = { ._1 = aad, ._2 = payload } } }
        }
      ),
      outbuf);
  if (written == (size_t)0U)
    abort();
  else
  {
    EverCrypt_Ed25519_sign(sigbuf,
      privkey,
      (uint32_t)written,
      Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(subslice__uint8_t(outbuf,
          (size_t)0U,
          written)));
    KRML_HOST_FREE(arr);
  }
}

FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
COSE_EverCrypt_dummy_map_val(void)
{
  return
    (
      (FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t){
        ._1 = {
          .tag = COSE_Format_Mkevercddl_label0,
          {
            .case_Mkevercddl_label0 = {
              .tag = COSE_Format_Mkevercddl_int0,
              { .case_Mkevercddl_int0 = 0ULL }
            }
          }
        },
        ._2 = dummy_cbor_det_t()
      }
    );
}

static Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
from_array__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(
  FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  *a,
  size_t alen
)
{
  return
    (
      (Pulse_Lib_Slice_slice__FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t){
        .elt = a,
        .len = alen
      }
    );
}

COSE_Format_empty_or_serialized_map
COSE_EverCrypt_mk_phdrs(
  int32_t alg,
  FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  *rest
)
{
  COSE_Format_evercddl_int alg_ = COSE_EverCrypt_mk_int(alg);
  return
    (
      (COSE_Format_empty_or_serialized_map){
        .tag = COSE_Format_Mkempty_or_serialized_map0,
        {
          .case_Mkempty_or_serialized_map0 = {
            .intkey1 = {
              .tag = FStar_Pervasives_Native_Some,
              .v = { .tag = COSE_Format_Inl, { .case_Inl = alg_ } }
            }, .intkey2 = { .tag = FStar_Pervasives_Native_None },
            .intkey3 = { .tag = FStar_Pervasives_Native_None },
            .intkey4 = { .tag = FStar_Pervasives_Native_None },
            ._x0 = {
              .tag = COSE_Format_Inr,
              {
                .case_Inr = {
                  .tag = COSE_Format_Inr,
                  {
                    .case_Inr = {
                      ._1 = FStar_Pervasives_Native_None,
                      ._2 = FStar_Pervasives_Native_None
                    }
                  }
                }
              }
            },
            ._x1 = {
              .tag = COSE_Format_Inl,
              {
                .case_Inl = from_array__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(rest,
                  (size_t)0U)
              }
            }
          }
        }
      }
    );
}

Pulse_Lib_Slice_slice__uint8_t
COSE_EverCrypt_sign1(
  uint8_t *privkey,
  COSE_Format_header_map uhdr,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t payload,
  Pulse_Lib_Slice_slice__uint8_t outbuf
)
{
  KRML_CHECK_SIZE(sizeof (
      FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
    ),
    (size_t)0U);
  FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  phdrauxbuf[0U];
  for (uint32_t _i = 0U; _i < (size_t)0U; ++_i)
    phdrauxbuf[_i] = COSE_EverCrypt_dummy_map_val();
  COSE_Format_evercddl_int alg_ = COSE_EverCrypt_mk_int(-8);
  COSE_Format_empty_or_serialized_map
  phdr =
    {
      .tag = COSE_Format_Mkempty_or_serialized_map0,
      {
        .case_Mkempty_or_serialized_map0 = {
          .intkey1 = {
            .tag = FStar_Pervasives_Native_Some,
            .v = { .tag = COSE_Format_Inl, { .case_Inl = alg_ } }
          }, .intkey2 = { .tag = FStar_Pervasives_Native_None },
          .intkey3 = { .tag = FStar_Pervasives_Native_None },
          .intkey4 = { .tag = FStar_Pervasives_Native_None },
          ._x0 = {
            .tag = COSE_Format_Inr,
            {
              .case_Inr = {
                .tag = COSE_Format_Inr,
                {
                  .case_Inr = {
                    ._1 = FStar_Pervasives_Native_None,
                    ._2 = FStar_Pervasives_Native_None
                  }
                }
              }
            }
          },
          ._x1 = {
            .tag = COSE_Format_Inl,
            {
              .case_Inl = from_array__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(phdrauxbuf,
                (size_t)0U)
            }
          }
        }
      }
    };
  uint8_t sigbuf[64U];
  memset(sigbuf, 0U, (size_t)64U * sizeof (uint8_t));
  COSE_EverCrypt_create_sig(privkey, phdr, aad, payload, sigbuf);
  size_t
  outbuf_sz =
    COSE_Format_serialize_cose_sign1_tagged((
        (COSE_Format_cose_sign1){
          .protected0 = phdr,
          .unprotected = uhdr,
          .payload = { .tag = COSE_Format_Inl, .v = payload },
          .signature = Pulse_Lib_Slice_from_array__uint8_t(sigbuf, (size_t)64U)
        }
      ),
      outbuf);
  if (outbuf_sz == (size_t)0U)
  {
    abort();
    return outbuf;
  }
  else
    return subslice__uint8_t(outbuf, (size_t)0U, outbuf_sz);
}

Pulse_Lib_Slice_slice__uint8_t
COSE_EverCrypt_sign1_simple(
  uint8_t *privkey,
  Pulse_Lib_Slice_slice__uint8_t payload,
  Pulse_Lib_Slice_slice__uint8_t outbuf
)
{
  KRML_CHECK_SIZE(sizeof (
      FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
    ),
    (size_t)0U);
  FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  buf0[0U];
  for (uint32_t _i = 0U; _i < (size_t)0U; ++_i)
    buf0[_i] = COSE_EverCrypt_dummy_map_val();
  COSE_Format_header_map
  uhdr =
    {
      .intkey1 = { .tag = FStar_Pervasives_Native_None },
      .intkey2 = { .tag = FStar_Pervasives_Native_None },
      .intkey3 = { .tag = FStar_Pervasives_Native_None },
      .intkey4 = { .tag = FStar_Pervasives_Native_None },
      ._x0 = {
        .tag = COSE_Format_Inr,
        {
          .case_Inr = {
            .tag = COSE_Format_Inr,
            {
              .case_Inr = { ._1 = FStar_Pervasives_Native_None, ._2 = FStar_Pervasives_Native_None }
            }
          }
        }
      },
      ._x1 = {
        .tag = COSE_Format_Inl,
        {
          .case_Inl = from_array__FStar_Pervasives_Native_tuple2_COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t(buf0,
            (size_t)0U)
        }
      }
    };
  uint8_t buf[0U];
  memset(buf, 0U, (size_t)0U * sizeof (uint8_t));
  return
    COSE_EverCrypt_sign1(privkey,
      uhdr,
      Pulse_Lib_Slice_from_array__uint8_t(buf, (size_t)0U),
      payload,
      outbuf);
}

bool
COSE_EverCrypt_verify_sig(
  uint8_t *pubkey,
  COSE_Format_empty_or_serialized_map phdr,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t payload,
  uint8_t *sigbuf
)
{
  uint8_t *arr = KRML_HOST_CALLOC((size_t)1024U, sizeof (uint8_t));
  Pulse_Lib_Slice_slice__uint8_t
  outbuf = Pulse_Lib_Slice_from_array__uint8_t(arr, (size_t)1024U);
  size_t
  written =
    COSE_Format_serialize_sig_structure((
        (COSE_Format_sig_structure){
          .context = COSE_Format_Inr,
          .body_protected = phdr,
          ._x0 = { .tag = COSE_Format_Inr, { .case_Inr = { ._1 = aad, ._2 = payload } } }
        }
      ),
      outbuf);
  if (written == (size_t)0U)
  {
    abort();
    return false;
  }
  else
  {
    bool
    success =
      EverCrypt_Ed25519_verify(pubkey,
        (uint32_t)written,
        Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(subslice__uint8_t(outbuf,
            (size_t)0U,
            written)),
        sigbuf);
    KRML_HOST_FREE(arr);
    return success;
  }
}

FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
COSE_EverCrypt_verify1(
  uint8_t *pubkey,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t msg
)
{
  FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t
  scrut = COSE_Format_validate_and_parse_cose_sign1_tagged(msg);
  if (scrut.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut.tag == FStar_Pervasives_Native_Some)
  {
    FStar_Pervasives_Native_tuple2__COSE_Format_cose_sign1_Pulse_Lib_Slice_slice__uint8_t
    res1 = scrut.v;
    COSE_Format_cose_sign1 x = res1._1;
    Pulse_Lib_Slice_slice__uint8_t rem = res1._2;
    if (Pulse_Lib_Slice_len__uint8_t(rem) == (size_t)0U && x.payload.tag == COSE_Format_Inl)
    {
      Pulse_Lib_Slice_slice__uint8_t sig = x.signature;
      bool ite0;
      if (Pulse_Lib_Slice_len__uint8_t(sig) == (size_t)64U)
      {
        uint8_t *sig_ = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(sig);
        Pulse_Lib_Slice_slice__uint8_t ite;
        if (x.payload.tag == COSE_Format_Inl)
          ite = x.payload.v;
        else
          ite =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        ite0 = COSE_EverCrypt_verify_sig(pubkey, x.protected0, aad, ite, sig_);
      }
      else
        ite0 = false;
      if (ite0)
      {
        Pulse_Lib_Slice_slice__uint8_t ite;
        if (x.payload.tag == COSE_Format_Inl)
          ite = x.payload.v;
        else
          ite =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        return
          (
            (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = ite
            }
          );
      }
      else
        return
          (
            (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
              .tag = FStar_Pervasives_Native_None
            }
          );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t){
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

FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
COSE_EverCrypt_verify1_simple(uint8_t *pubkey, Pulse_Lib_Slice_slice__uint8_t msg)
{
  uint8_t buf[0U];
  memset(buf, 0U, (size_t)0U * sizeof (uint8_t));
  return
    COSE_EverCrypt_verify1(pubkey,
      Pulse_Lib_Slice_from_array__uint8_t(buf, (size_t)0U),
      msg);
}


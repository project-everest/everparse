

#include "COSE_EverCrypt.h"

#include "COSE_Format.h"
#include "CBORDetAPI.h"
#include "internal/COSE_Format.h"

extern void abort(void);

extern void
EverCrypt_Ed25519_sign(
  uint8_t *signature,
  uint8_t *private_key,
  uint32_t msg_len,
  uint8_t *msg
);

extern bool
EverCrypt_Ed25519_verify(
  uint8_t *public_key,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *signature
);

COSE_Format_evercddl_int_pretty COSE_EverCrypt_mk_int(int32_t i)
{
  if (i < (int32_t)0)
    return
      (
        (COSE_Format_evercddl_int_pretty){
          .tag = COSE_Format_Mkevercddl_int_pretty1,
          { .case_Mkevercddl_int_pretty1 = (uint64_t)((int32_t)-1 - i) }
        }
      );
  else
    return
      (
        (COSE_Format_evercddl_int_pretty){
          .tag = COSE_Format_Mkevercddl_int_pretty0,
          { .case_Mkevercddl_int_pretty0 = (uint64_t)i }
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
  COSE_Format_evercddl_empty_or_serialized_map_pretty phdr,
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
    COSE_Format_serialize_Sig_structure((
        (COSE_Format_evercddl_Sig_structure_pretty){
          .context = COSE_Format_Inr,
          .body_protected = phdr,
          ._x0 = { .tag = COSE_Format_Inr, { .case_Inr = { .fst = aad, .snd = payload } } }
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

K___COSE_Format_evercddl_label_pretty_COSE_Format_evercddl_values_pretty
COSE_EverCrypt_dummy_map_val(void)
{
  return
    (
      (K___COSE_Format_evercddl_label_pretty_COSE_Format_evercddl_values_pretty){
        .fst = {
          .tag = COSE_Format_Mkevercddl_label_pretty0,
          {
            .case_Mkevercddl_label_pretty0 = {
              .tag = COSE_Format_Mkevercddl_int_pretty0,
              { .case_Mkevercddl_int_pretty0 = 0ULL }
            }
          }
        },
        .snd = dummy_cbor_det_t()
      }
    );
}

static Pulse_Lib_Slice_slice___COSE_Format_evercddl_label_pretty___COSE_Format_evercddl_values_pretty_
from_array___COSE_Format_evercddl_label_pretty___COSE_Format_evercddl_values_pretty_(
  K___COSE_Format_evercddl_label_pretty_COSE_Format_evercddl_values_pretty *a,
  size_t alen
)
{
  return
    (
      (Pulse_Lib_Slice_slice___COSE_Format_evercddl_label_pretty___COSE_Format_evercddl_values_pretty_){
        .elt = a,
        .len = alen
      }
    );
}

COSE_Format_evercddl_empty_or_serialized_map_pretty
COSE_EverCrypt_mk_phdrs(
  int32_t alg,
  K___COSE_Format_evercddl_label_pretty_COSE_Format_evercddl_values_pretty *rest
)
{
  COSE_Format_evercddl_int_pretty alg_ = COSE_EverCrypt_mk_int(alg);
  return
    (
      (COSE_Format_evercddl_empty_or_serialized_map_pretty){
        .tag = COSE_Format_Mkevercddl_empty_or_serialized_map_pretty0,
        {
          .case_Mkevercddl_empty_or_serialized_map_pretty0 = {
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
                      .fst = { .tag = FStar_Pervasives_Native_None },
                      .snd = { .tag = FStar_Pervasives_Native_None }
                    }
                  }
                }
              }
            },
            ._x1 = {
              .tag = COSE_Format_Inl,
              {
                .case_Inl = from_array___COSE_Format_evercddl_label_pretty___COSE_Format_evercddl_values_pretty_(rest,
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
  COSE_Format_evercddl_header_map_pretty uhdr,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t payload,
  Pulse_Lib_Slice_slice__uint8_t outbuf
)
{
  KRML_CHECK_SIZE(sizeof (
      K___COSE_Format_evercddl_label_pretty_COSE_Format_evercddl_values_pretty
    ),
    (size_t)0U);
  K___COSE_Format_evercddl_label_pretty_COSE_Format_evercddl_values_pretty phdrauxbuf[0U];
  for (uint32_t _i = 0U; _i < (size_t)0U; ++_i)
    phdrauxbuf[_i] = COSE_EverCrypt_dummy_map_val();
  COSE_Format_evercddl_int_pretty alg_ = COSE_EverCrypt_mk_int((int32_t)-8);
  COSE_Format_evercddl_empty_or_serialized_map_pretty
  phdr =
    {
      .tag = COSE_Format_Mkevercddl_empty_or_serialized_map_pretty0,
      {
        .case_Mkevercddl_empty_or_serialized_map_pretty0 = {
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
                    .fst = { .tag = FStar_Pervasives_Native_None },
                    .snd = { .tag = FStar_Pervasives_Native_None }
                  }
                }
              }
            }
          },
          ._x1 = {
            .tag = COSE_Format_Inl,
            {
              .case_Inl = from_array___COSE_Format_evercddl_label_pretty___COSE_Format_evercddl_values_pretty_(phdrauxbuf,
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
    COSE_Format_serialize_COSE_Sign1_Tagged((
        (COSE_Format_evercddl_COSE_Sign1_pretty){
          .protected = phdr,
          .unprotected = uhdr,
          .payload = { .tag = COSE_Format_Inl, { .case_Inl = payload } },
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
      K___COSE_Format_evercddl_label_pretty_COSE_Format_evercddl_values_pretty
    ),
    (size_t)0U);
  K___COSE_Format_evercddl_label_pretty_COSE_Format_evercddl_values_pretty buf0[0U];
  for (uint32_t _i = 0U; _i < (size_t)0U; ++_i)
    buf0[_i] = COSE_EverCrypt_dummy_map_val();
  COSE_Format_evercddl_header_map_pretty
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
              .case_Inr = {
                .fst = { .tag = FStar_Pervasives_Native_None },
                .snd = { .tag = FStar_Pervasives_Native_None }
              }
            }
          }
        }
      },
      ._x1 = {
        .tag = COSE_Format_Inl,
        {
          .case_Inl = from_array___COSE_Format_evercddl_label_pretty___COSE_Format_evercddl_values_pretty_(buf0,
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
  COSE_Format_evercddl_empty_or_serialized_map_pretty phdr,
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
    COSE_Format_serialize_Sig_structure((
        (COSE_Format_evercddl_Sig_structure_pretty){
          .context = COSE_Format_Inr,
          .body_protected = phdr,
          ._x0 = { .tag = COSE_Format_Inr, { .case_Inr = { .fst = aad, .snd = payload } } }
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

static bool
uu___is_Inl__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty(
  FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
  projectee
)
{
  if (projectee.tag == COSE_Format_Inl)
    return true;
  else
    return false;
}

FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t
COSE_EverCrypt_verify1(
  uint8_t *pubkey,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t msg
)
{
  FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_
  scrut0 = COSE_Format_validate_and_parse_COSE_Sign1_Tagged(msg);
  if (scrut0.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    K___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty_Pulse_Lib_Slice_slice_uint8_t
    res1 = scrut0.v;
    COSE_Format_evercddl_COSE_Sign1_pretty x = res1.fst;
    Pulse_Lib_Slice_slice__uint8_t rem = res1.snd;
    if
    (
      Pulse_Lib_Slice_len__uint8_t(rem) == (size_t)0U &&
        uu___is_Inl__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty(x.payload)
    )
    {
      Pulse_Lib_Slice_slice__uint8_t sig = x.signature;
      bool ite0;
      if (Pulse_Lib_Slice_len__uint8_t(sig) == (size_t)64U)
      {
        uint8_t *sig_ = Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(sig);
        FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
        scrut = x.payload;
        Pulse_Lib_Slice_slice__uint8_t ite;
        if (scrut.tag == COSE_Format_Inl)
          ite = scrut.case_Inl;
        else
          ite =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        ite0 = COSE_EverCrypt_verify_sig(pubkey, x.protected, aad, ite, sig_);
      }
      else
        ite0 = false;
      if (ite0)
      {
        FStar_Pervasives_either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
        scrut = x.payload;
        Pulse_Lib_Slice_slice__uint8_t ite;
        if (scrut.tag == COSE_Format_Inl)
          ite = scrut.case_Inl;
        else
          ite =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        return
          (
            (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = ite
            }
          );
      }
      else
        return
          (
            (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t){
              .tag = FStar_Pervasives_Native_None
            }
          );
    }
    else
      return
        (
          (FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t){
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

FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t
COSE_EverCrypt_verify1_simple(uint8_t *pubkey, Pulse_Lib_Slice_slice__uint8_t msg)
{
  uint8_t buf[0U];
  memset(buf, 0U, (size_t)0U * sizeof (uint8_t));
  return
    COSE_EverCrypt_verify1(pubkey,
      Pulse_Lib_Slice_from_array__uint8_t(buf, (size_t)0U),
      msg);
}


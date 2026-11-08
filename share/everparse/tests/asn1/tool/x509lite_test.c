/* Tests of the C API that everparse-asn1 generates for X509Lite.asn:
   ANY DEFINED BY tables (AlgId, Extension), extension values decoded
   through CONTAINING, DEFAULT under an EXPLICIT tag (version), KEEP-BYTES
   (TBS), and round trips through the writers. */
#include "X509Lite.h"
#include <stdio.h>
#include <string.h>
#define BUF 256

static int fails = 0;
#define CHECK(c, ...) do { if (!(c)) { printf(__VA_ARGS__); printf("\n"); fails++; } } while (0)

typedef Pulse_Lib_Slice_slice__uint8 slice;

static slice sl(const uint8_t *b, size_t n) { return (slice){ .elt = (uint8_t *)b, .len = n }; }

static int same(slice s, const uint8_t *b, size_t n) {
  return s.len == n && memcmp(s.elt, b, n) == 0;
}

static int small(ASN1_Pulse_Rel_asn1_int_impl i, int64_t v) {
  return i.tag == ASN1_PULSE_REL_SMALL && i.val.Small == v;
}

/* Cert { tbs { version v3, serial 1, signature sha256WithRSAEncryption NULL,
     subject { "ab" }, extensions {
       { basicConstraints, critical TRUE, CONTAINING { cA TRUE, pathLen 3 } },
       { keyUsage, CONTAINING '101'B },
       { 1.2.3, 'x' } } },
   sigAlg ecdsa-with-SHA256 (no parameters), sig '0102'H } */
static const uint8_t cert_der[] = { 0x30, 0x5e, 0x30, 0x4b, 0xa0, 0x03, 0x02, 0x01, 0x02, 0x02, 0x01, 0x01, 0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x05, 0x00, 0x30, 0x04, 0x0c, 0x02, 0x61, 0x62, 0xa3, 0x2c, 0x30, 0x2a, 0x30, 0x12, 0x06, 0x03, 0x55, 0x1d, 0x13, 0x01, 0x01, 0xff, 0x04, 0x08, 0x30, 0x06, 0x01, 0x01, 0xff, 0x02, 0x01, 0x03, 0x30, 0x0b, 0x06, 0x03, 0x55, 0x1d, 0x0f, 0x04, 0x04, 0x03, 0x02, 0x05, 0xa0, 0x30, 0x07, 0x06, 0x02, 0x2a, 0x03, 0x04, 0x01, 0x78, 0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02, 0x03, 0x03, 0x00, 0x01, 0x02 };
#define TBS_OFF 2
#define TBS_LEN 77

/* The same certificate, version v1 (absent) and without extensions */
static const uint8_t cert_v1_der[] = { 0x30, 0x2b, 0x30, 0x18, 0x02, 0x01, 0x01, 0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x05, 0x00, 0x30, 0x04, 0x0c, 0x02, 0x61, 0x62, 0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02, 0x03, 0x03, 0x00, 0x01, 0x02 };
/* ... with version v1 explicitly encoded: not DER */
static const uint8_t cert_v1_explicit_der[] = { 0x30, 0x30, 0x30, 0x1d, 0xa0, 0x03, 0x02, 0x01, 0x00, 0x02, 0x01, 0x01, 0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x05, 0x00, 0x30, 0x04, 0x0c, 0x02, 0x61, 0x62, 0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02, 0x03, 0x03, 0x00, 0x01, 0x02 };
/* ... with sha256WithRSAEncryption without its NULL parameters */
static const uint8_t cert_sha_noparam_der[] = { 0x30, 0x29, 0x30, 0x16, 0x02, 0x01, 0x01, 0x30, 0x0b, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x30, 0x04, 0x0c, 0x02, 0x61, 0x62, 0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02, 0x03, 0x03, 0x00, 0x01, 0x02 };
/* ... with an unknown algorithm 1.2.3 and parameters 'p' (the fallback) */
static const uint8_t cert_unk_alg_der[] = { 0x30, 0x25, 0x30, 0x12, 0x02, 0x01, 0x01, 0x30, 0x07, 0x06, 0x02, 0x2a, 0x03, 0x04, 0x01, 0x70, 0x30, 0x04, 0x0c, 0x02, 0x61, 0x62, 0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02, 0x03, 0x03, 0x00, 0x01, 0x02 };

static const uint8_t ext_bc_der[] = { 0x30, 0x12, 0x06, 0x03, 0x55, 0x1d, 0x13, 0x01, 0x01, 0xff, 0x04, 0x08, 0x30, 0x06, 0x01, 0x01, 0xff, 0x02, 0x01, 0x03 };
static const uint8_t ext_ku_der[] = { 0x30, 0x0b, 0x06, 0x03, 0x55, 0x1d, 0x0f, 0x04, 0x04, 0x03, 0x02, 0x05, 0xa0 };
static const uint8_t ext_unk_der[] = { 0x30, 0x07, 0x06, 0x02, 0x2a, 0x03, 0x04, 0x01, 0x78 };
/* basicConstraints whose value is not a BasicConstraints */
static const uint8_t ext_bc_bad_der[] = { 0x30, 0x08, 0x06, 0x03, 0x55, 0x1d, 0x13, 0x04, 0x01, 0x78 };
/* critical FALSE explicitly encoded: not DER */
static const uint8_t ext_bc_false_der[] = { 0x30, 0x0c, 0x06, 0x03, 0x55, 0x1d, 0x13, 0x01, 0x01, 0x00, 0x04, 0x02, 0x30, 0x00 };

static int validate_cert(const uint8_t *b, size_t n) {
  size_t off = 0;
  return validate_Cert(sl(b, n), &off) && off == n;
}

static int validate_ext(const uint8_t *b, size_t n) {
  size_t off = 0;
  return validate_Extension(sl(b, n), &off) && off == n;
}

static void write_cert_ok(const char *name, Cert x, const uint8_t *exp, size_t n) {
  uint8_t out[BUF];
  size_t pos = BUF;
  ASN1_Pulse_JitWriter_jit_result r = write_Cert(x, sl(out, BUF), &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - n && memcmp(out + pos, exp, n) == 0,
        "%s: write: expected the DER bytes (result %d, %zu bytes)", name, (int)r, BUF - pos);
}

static void write_ext_ok(const char *name, Extension x, const uint8_t *exp, size_t n) {
  uint8_t out[BUF];
  size_t pos = BUF;
  ASN1_Pulse_JitWriter_jit_result r = write_Extension(x, sl(out, BUF), &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - n && memcmp(out + pos, exp, n) == 0,
        "%s: write: expected the DER bytes (result %d, %zu bytes)", name, (int)r, BUF - pos);
}

static void test_cert(void) {
  CHECK(validate_cert(cert_der, sizeof cert_der), "cert: validate");
  Cert c = parse_Cert(sl(cert_der, sizeof cert_der));
  TBS *t = &c.tbs.value;
  CHECK(t->version.tag == X509LITE_IMPL_TBS_VERSION_PRESENT && small(t->version.val.TBS_version_present, 2),
        "cert: version v3");
  CHECK(small(t->serial, 1), "cert: serial");
  CHECK(t->signature.tag == X509LITE_IMPL_ALGID_ALGORITHM_SHA256WITHRSAENCRYPTION, "cert: signature");
  CHECK(t->extensions.tag == X509LITE_IMPL_TBS_EXTENSIONS_PRESENT, "cert: extensions");
  CHECK(c.tbs.raw.tag == X509LITE_IMPL_TBS_RAW_PRESENT &&
        c.tbs.raw.val.TBS_raw_present.elt == cert_der + TBS_OFF &&
        c.tbs.raw.val.TBS_raw_present.len == TBS_LEN, "cert: KEEP-BYTES of tbs");
  CHECK(c.sigAlg.tag == X509LITE_IMPL_ALGID_ALGORITHM_ECDSA_WITH_SHA256, "cert: sigAlg");
  static const uint8_t sig[] = { 0x01, 0x02 };
  CHECK(c.sig.unused == 0 && same(c.sig.bytes, sig, 2), "cert: sig");
  write_cert_ok("cert", c, cert_der, sizeof cert_der);
  c.tbs.raw.tag = X509LITE_IMPL_TBS_RAW_ABSENT;
  write_cert_ok("cert (tbs bytes absent)", c, cert_der, sizeof cert_der);

  /* DEFAULT under an EXPLICIT tag */
  CHECK(validate_cert(cert_v1_der, sizeof cert_v1_der), "cert v1: validate");
  Cert c1 = parse_Cert(sl(cert_v1_der, sizeof cert_v1_der));
  CHECK(c1.tbs.value.version.tag == X509LITE_IMPL_TBS_VERSION_ABSENT, "cert v1: version absent");
  CHECK(c1.tbs.value.extensions.tag == X509LITE_IMPL_TBS_EXTENSIONS_ABSENT, "cert v1: no extensions");
  write_cert_ok("cert v1", c1, cert_v1_der, sizeof cert_v1_der);
  CHECK(!validate_cert(cert_v1_explicit_der, sizeof cert_v1_explicit_der), "cert v1 explicit: not DER");
  /* Writing v1 explicitly omits it */
  c1.tbs.value.version.tag = X509LITE_IMPL_TBS_VERSION_PRESENT;
  c1.tbs.value.version.val.TBS_version_present = (ASN1_Pulse_Rel_asn1_int_impl){ .tag = ASN1_PULSE_REL_SMALL, .val = { .Small = 0 } };
  write_cert_ok("cert v1 (version present)", c1, cert_v1_der, sizeof cert_v1_der);

  /* AlgId table */
  CHECK(!validate_cert(cert_sha_noparam_der, sizeof cert_sha_noparam_der), "sha256 without NULL: rejected");
  CHECK(validate_cert(cert_unk_alg_der, sizeof cert_unk_alg_der), "unknown algorithm: validate");
  Cert c2 = parse_Cert(sl(cert_unk_alg_der, sizeof cert_unk_alg_der));
  static const uint8_t k123[] = { 0x2a, 0x03 }, p[] = { 0x04, 0x01, 0x70 };
  AlgId a = c2.tbs.value.signature;
  CHECK(a.tag == X509LITE_IMPL_ALGID_ALGORITHM_OTHER &&
        same(a.val.AlgId_algorithm_other.key, k123, 2) &&
        a.val.AlgId_algorithm_other.other.tag == X509LITE_IMPL_ALGID_PARAMETERS_PRESENT &&
        same(a.val.AlgId_algorithm_other.other.val.AlgId_parameters_present, p, 3),
        "unknown algorithm: fallback (key and ANY parameters)");
  write_cert_ok("unknown algorithm", c2, cert_unk_alg_der, sizeof cert_unk_alg_der);
}

static void test_extensions(void) {
  /* basicConstraints: the OCTET STRING is decoded as a BasicConstraints */
  CHECK(validate_ext(ext_bc_der, sizeof ext_bc_der), "basicConstraints: validate");
  Extension e = parse_Extension(sl(ext_bc_der, sizeof ext_bc_der));
  CHECK(e.tag == X509LITE_IMPL_EXTENSION_EXTNID_ID_CE_BASICCONSTRAINTS, "basicConstraints: case");
  Extension_id_ce_basicConstraints *bc = &e.val.Extension_extnID_id_ce_basicConstraints;
  CHECK(bc->critical.tag == X509LITE_IMPL_EXTENSION_CRITICAL_PRESENT && bc->critical.val.Extension_critical_present,
        "basicConstraints: critical");
  CHECK(bc->extnValue.cA.tag == X509LITE_IMPL_BASICCONSTRAINTS_CA_PRESENT && bc->extnValue.cA.val.BasicConstraints_cA_present,
        "basicConstraints: cA");
  CHECK(bc->extnValue.pathLenConstraint.tag == X509LITE_IMPL_BASICCONSTRAINTS_PATHLENCONSTRAINT_PRESENT &&
        small(bc->extnValue.pathLenConstraint.val.BasicConstraints_pathLenConstraint_present, 3),
        "basicConstraints: pathLenConstraint");
  write_ext_ok("basicConstraints", e, ext_bc_der, sizeof ext_bc_der);
  /* (0..MAX) is checked inside the OCTET STRING */
  bc->extnValue.pathLenConstraint.val.BasicConstraints_pathLenConstraint_present.val.Small = -1;
  uint8_t out[BUF];
  size_t pos = BUF;
  CHECK(write_Extension(e, sl(out, BUF), &pos) == ASN1_PULSE_JITWRITER_JIT_INVALID,
        "basicConstraints: pathLenConstraint -1 is INVALID");
  CHECK(!validate_ext(ext_bc_bad_der, sizeof ext_bc_bad_der), "basicConstraints: bad contents rejected");
  CHECK(!validate_ext(ext_bc_false_der, sizeof ext_bc_false_der), "basicConstraints: critical FALSE is not DER");

  /* keyUsage: CONTAINING BIT STRING, built by hand */
  static const uint8_t bits[] = { 0xa0 };
  Extension ku;
  memset(&ku, 0, sizeof ku);
  ku.tag = X509LITE_IMPL_EXTENSION_EXTNID_ID_CE_KEYUSAGE;
  ku.val.Extension_extnID_id_ce_keyUsage.critical.tag = X509LITE_IMPL_EXTENSION_CRITICAL_ABSENT;
  ku.val.Extension_extnID_id_ce_keyUsage.extnValue = (ASN1_Pulse_Rel_asn1_bitstring_impl){ .unused = 5, .bytes = sl(bits, 1) };
  write_ext_ok("keyUsage", ku, ext_ku_der, sizeof ext_ku_der);
  CHECK(validate_ext(ext_ku_der, sizeof ext_ku_der), "keyUsage: validate");
  Extension ku2 = parse_Extension(sl(ext_ku_der, sizeof ext_ku_der));
  CHECK(ku2.tag == X509LITE_IMPL_EXTENSION_EXTNID_ID_CE_KEYUSAGE &&
        ku2.val.Extension_extnID_id_ce_keyUsage.extnValue.unused == 5 &&
        same(ku2.val.Extension_extnID_id_ce_keyUsage.extnValue.bytes, bits, 1), "keyUsage: parse");

  /* An unknown extension keeps its OCTET STRING */
  CHECK(validate_ext(ext_unk_der, sizeof ext_unk_der), "unknown extension: validate");
  Extension u = parse_Extension(sl(ext_unk_der, sizeof ext_unk_der));
  static const uint8_t k123[] = { 0x2a, 0x03 }, x[] = { 0x78 };
  CHECK(u.tag == X509LITE_IMPL_EXTENSION_EXTNID_OTHER &&
        same(u.val.Extension_extnID_other.key, k123, 2) &&
        same(u.val.Extension_extnID_other.other.extnValue, x, 1), "unknown extension: parse");
  write_ext_ok("unknown extension", u, ext_unk_der, sizeof ext_unk_der);
  /* The key of the fallback must not be one of the table */
  static const uint8_t kbc[] = { 0x55, 0x1d, 0x13 };
  u.val.Extension_extnID_other.key = sl(kbc, 3);
  pos = BUF;
  CHECK(write_Extension(u, sl(out, BUF), &pos) == ASN1_PULSE_JITWRITER_JIT_INVALID,
        "fallback with a known key is INVALID");
}

int main(void) {
  test_cert();
  test_extensions();
  if (fails) { printf("%d failures\n", fails); return 1; }
  printf("x509lite_test: all tests passed\n");
  return 0;
}

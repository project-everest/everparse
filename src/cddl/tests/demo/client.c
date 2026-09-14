#include "CDDLExtractionTest.h"
#include "CBORDetAPI.h"

/* The two extraction backends publish this program's types under different
 * names and, for `option', under a different shape.
 *
 *   * karamel names a specialization after the module the argument came from
 *     (option__CDDLTest_Test_evercddl_uint) and flattens a tagged union whose
 *     only payload-carrying constructor is Some into a bare field:
 *
 *         struct { tags tag; uint64_t v; }
 *
 *   * Custard names it after the argument alone (option__evercddl_uint) --
 *     see its warning 377, which says as much and tells consumers not to
 *     depend on the name -- and gives every tagged union the general shape,
 *     one arm per constructor:
 *
 *         struct { enum tags tag; union { struct { uint64_t v; } Some; } val; }
 *
 * Neither is wrong; they are different surfaces for the same program.  The
 * macros below are the whole difference for this client.
 */
#ifdef EVERPARSE_CUSTARD
#  define TEST_OPT_UINT   FStar_Pervasives_Native_option__evercddl_uint
#  define TEST_SOME       FSTAR_PERVASIVES_NATIVE_SOME__EVERCDDL_UINT
#  define TEST_SLICE_U8   Pulse_Lib_Slice_slice__uint8
#  define TEST_SOME_V(o)  ((o).val.FStar_Pervasives_Native_Some__evercddl_uint.v)
#  define TEST_MK_SOME(x) { .tag = TEST_SOME, \
                            .val = { .FStar_Pervasives_Native_Some__evercddl_uint = { .v = (x) } } }
#else
#  define TEST_OPT_UINT   FStar_Pervasives_Native_option__CDDLTest_Test_evercddl_uint
#  define TEST_SOME       FStar_Pervasives_Native_Some
#  define TEST_SLICE_U8   Pulse_Lib_Slice_slice__uint8_t
#  define TEST_SOME_V(o)  ((o).v)
#  define TEST_MK_SOME(x) { .tag = TEST_SOME, .v = (x) }
#endif

int main(void) {
  TEST_OPT_UINT test_snd = TEST_MK_SOME(42L);
  CDDLTest_Test_test1 test = {
    .foo = 18L,
    .bar = test_snd
  };
  uint8_t out[32];
  TEST_SLICE_U8 out_s = {
    .elt = out,
    .len = 32
  };
  size_t sz = CDDLTest_Test_serialize_test1(test, out_s);
  if (sz == 0) {
    return 1;
  }
  sz = cbor_det_validate(out, sz);
  if (sz == 0) {
    return 2;
  }
  cbor_det_t obj = cbor_det_parse(out, sz);
  if (! (CDDLTest_Test_validate_test1(obj)))
    return 3;
  CDDLTest_Test_test1 ret = CDDLTest_Test_parse_test1(obj);
  if (! (ret.foo == test.foo && ret.bar.tag == test.bar.tag &&
         TEST_SOME_V(ret.bar) == TEST_SOME_V(test.bar)))
    return 4;
  return CDDLTest_Client_main();
}

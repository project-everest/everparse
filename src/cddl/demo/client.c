#include "CDDLExtractionTest.h"

int main(void) {
  FStar_Pervasives_Native_option__CDDLTest_Test_evercddl_uint_pretty test_snd = {
    .tag = FStar_Pervasives_Native_Some,
    .v = 42L
  };
  CDDLTest_Test_evercddl_test1_pretty test = {
    .x0 = 18L,
    .x1 = test_snd
  };
  uint8_t out[32];
  Pulse_Lib_Slice_slice__uint8_t out_s = {
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
  CDDLTest_Test_evercddl_test1_pretty ret = CDDLTest_Test_parse_test1(obj);
  if (! (ret.x0 == test.x0 && ret.x1.tag == test.x1.tag && ret.x1.v == test.x1.v))
    return 4;
  return CDDLTest_Client_main();
}

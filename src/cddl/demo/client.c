#include "CDDLExtractionTest.h"

int main(void) {
  FStar_Pervasives_Native_option__uint64_t test_snd = {
    .tag = FStar_Pervasives_Native_Some,
    .v = 42L
  };
  CDDLTest_Test_evercddl_test1 test = {
    .fst = 18L,
    .snd = test_snd
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
  CDDLTest_Test_evercddl_test1 ret = CDDLTest_Test_parse_test1(obj);
  if (! (ret.fst == test.fst && ret.snd.tag == test.snd.tag && ret.snd.v == test.snd.v))
    return 4;
  return CDDLTest_Client_main();
}

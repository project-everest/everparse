import json
from pathlib import Path
import unittest

from runtime_abi import inventory


HERE = Path(__file__).resolve().parent


class RuntimeContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.contract = json.loads((HERE / "runtime-contract.json").read_text())

    def test_profiles(self):
        profiles = self.contract["profiles"]
        self.assertEqual(
            {(p["api"], p["stream"]) for p in profiles},
            {(api, stream) for api in ("pulse", "lowstar")
             for stream in ("buffer", "extern", "static")},
        )
        self.assertEqual(len(profiles), 6)
        self.assertEqual(len({p["directory"] for p in profiles}), 6)
        for p in profiles:
            expected = ("" if p["api"] == "pulse" else "lowstar/") + p["stream"]
            self.assertEqual(p["directory"], expected)
            self.assertTrue(
                all(name.startswith("EverParse") for name in p["static_hooks"])
            )
            self.assertFalse(set(p["static_hooks"]) & set(p["extern_values"]))

    def test_static_exceptions(self):
        profiles = {(p["api"], p["stream"]): p for p in self.contract["profiles"]}
        self.assertEqual(len(profiles["pulse", "static"]["static_hooks"]), 7)
        self.assertEqual(len(profiles["lowstar", "static"]["static_hooks"]), 5)
        self.assertEqual(
            profiles["pulse", "static"]["extern_values"], ["EverParseNullPtr"]
        )
        self.assertNotIn(
            "EverParseStreamOf", profiles["lowstar", "static"]["static_hooks"]
        )
        for p in profiles.values():
            if p["stream"] != "static":
                self.assertEqual(p["static_hooks"], [])

    def test_boolean(self):
        self.assertEqual(self.contract["boolean"], {
            "name": "BOOLEAN", "representation": "uint8_t",
            "false": 0, "true": 1, "truth": "nonzero",
        })

    def test_validator_pipeline_is_unchanged(self):
        self.assertTrue(self.contract["retain_runtime_krml"])
        self.assertEqual(
            self.contract["validator_generator"], ["Custard KrmlC", "KaRaMeL"]
        )
        self.assertIn(
            "Pulse.Lib.Pervasives._zero_for_deref",
            self.contract["krml_only_roots"],
        )
        self.assertEqual(
            sum(name.endswith(".error_handler_macro")
                for name in self.contract["krml_only_roots"]),
            5,
        )


class InventoryTests(unittest.TestCase):
    def test_function_bodies_do_not_enter_the_inventory(self):
        result = inventory("""
          #define EVERPARSE_VALIDATOR_SUCCESS (0U)
          static inline BOOLEAN EverParseTest(uint32_t size, uint32_t access) {
            if (size >= access) { return 1; } else { return 0; }
          }
          extern uint8_t *EverParseRead(void *base, uint64_t size);
        """)
        self.assertEqual(result["functions"]["EverParseTest"], {
            "linkage": "static inline", "return": "BOOLEAN",
            "parameters": ["uint32_t", "uint32_t"],
        })
        self.assertEqual(
            result["functions"]["EverParseRead"]["parameters"],
            ["void *", "uint64_t"],
        )
        self.assertEqual(result["macros"]["EVERPARSE_VALIDATOR_SUCCESS"], "( 0U )")

    def test_types_and_values(self):
        result = inventory("""
          extern "C" {
          typedef uint8_t *EVERPARSE_APP_CTXT;
          typedef struct Frame_s { BOOLEAN filled; uint64_t pos; } FRAME;
          typedef void (*HANDLER)(uint8_t code, uint8_t *context);
          extern uint8_t *EverParseNullPtr;
          }
        """)
        self.assertEqual(result["types"]["FRAME"]["fields"],
                         "BOOLEAN filled ; uint64_t pos ;")
        self.assertEqual(result["types"]["HANDLER"]["kind"], "callback")
        self.assertEqual(result["values"], {"EverParseNullPtr": "uint8_t *"})

    def test_unknown_declarations_fail(self):
        with self.assertRaises(ValueError):
            inventory("uint64_t unexpected_global = 0;")
        with self.assertRaises(ValueError):
            inventory("extern uint8_t f(uint8_t (*callback)(void));")

    def test_reference_covers_contract(self):
        reference = json.loads((HERE / "runtime-abi.json").read_text())["profiles"]
        contract = json.loads((HERE / "runtime-contract.json").read_text())
        self.assertEqual(set(reference), {
            p["directory"] for p in contract["profiles"]
        })
        for p in contract["profiles"]:
            abi = reference[p["directory"]]
            self.assertIn("EVERPARSE_ERROR_HANDLER", abi["types"])
            self.assertIn("EVERPARSE_APP_CTXT", abi["types"])
            self.assertIn("EverParseGetBitfield64MsbFirst", abi["functions"])
            self.assertNotIn("_zero_for_deref", str(abi))
            self.assertNotIn("ERROR_HANDLER_MACRO", str(abi))
            for name in p["static_hooks"]:
                self.assertIn(abi["functions"][name]["linkage"],
                              ("static", "static inline"))
            for name in p["extern_values"]:
                self.assertIn(name, abi["values"])
            if p["api"] == "lowstar":
                self.assertEqual(abi["functions"]["EverParseIsError"]["return"],
                                 "BOOLEAN")
                self.assertIn("BOOLEAN filled", abi["types"]["EVERPARSE_ERROR_FRAME"]["fields"])
            if p["api"] == "lowstar" and p["stream"] != "buffer":
                self.assertIn("BOOLEAN has_length",
                              abi["types"]["EVERPARSE_INPUT_BUFFER"]["fields"])
                self.assertEqual(
                    abi["functions"]["EverParseStreamOf"]["linkage"], "extern"
                )


if __name__ == "__main__":
    unittest.main()

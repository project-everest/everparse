import json
from pathlib import Path
import unittest

from runtime_abi import inventory
from runtime_headers import PROFILES, annotate, profile_config


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

    def test_split_record_and_function_declarations(self):
        result = inventory("""
          typedef struct Frame_s FRAME;
          struct Frame_s { BOOLEAN filled; };
          static inline BOOLEAN f(uint32_t x);
          static inline BOOLEAN f(uint32_t y) { return y > 0; }
        """)
        self.assertEqual(result["types"]["FRAME"],
                         {"kind": "record", "fields": "BOOLEAN filled ;"})
        self.assertEqual(result["functions"]["f"]["parameters"], ["uint32_t"])
        with self.assertRaises(ValueError):
            inventory("static bool f(void); static BOOLEAN f(void) { return 1; }")

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


class ExtractionProfileTests(unittest.TestCase):
    def test_all_profiles_match_the_reference_names(self):
        reference = json.loads((HERE / "runtime-abi.json").read_text())["profiles"]
        for profile in PROFILES:
            names, _, _, _, _ = profile_config(profile)
            targets = [target for module in names.values() for target in module.values()]
            self.assertEqual(len(targets), len(set(targets)))
            expected = reference[profile]
            self.assertEqual(set(targets),
                             set(expected["functions"]) | set(expected["types"])
                             | set(expected["values"]) | set(expected["macros"]))

    def test_annotations_preserve_bodies(self):
        source = "module Example\n[@ CMacro ]\nlet answer = 42ul\n"
        result = annotate(source, {"answer": "ANSWER"})
        self.assertIn("let answer = 42ul\n", result)
        self.assertIn('[@@ CMacro; FStar.Attributes.rename_let "ANSWER";', result)
        self.assertIn("FStar.Attributes.CInline", result)

    def test_static_hooks_use_supplying_headers(self):
        result = annotate("assume val has : unit -> bool\n",
                          {"has": "EverParseHas"}, foreign={"has"},
                          static_hooks={"EverParseHas"})
        self.assertIn('custard_extern "EverParseHas"', result)
        self.assertIn('custard_c_header "EverParseStreamPrimitives.h"', result)
        self.assertNotIn("custard_declare_in_c_header", result)

    def test_invalid_annotations_fail(self):
        with self.assertRaises(ValueError):
            annotate("let answer = 42\n", {"missing": "Missing"})
        with self.assertRaises(ValueError):
            annotate("let answer = 0\nlet answer = 1\n", {"answer": "Answer"})


if __name__ == "__main__":
    unittest.main()

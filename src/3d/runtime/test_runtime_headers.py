import json
from argparse import Namespace
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from runtime_abi import compare_abi, inventory
from runtime_headers import PROFILES, RUNTIME, companion, extract, profile_config


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

    def test_validator_pipeline_is_native(self):
        self.assertFalse(self.contract["retain_runtime_krml"])
        self.assertEqual(
            self.contract["validator_generator"], ["Custard C"]
        )
        self.assertEqual(self.contract["runtime_unit"], "EverParse.cui")


class InventoryTests(unittest.TestCase):
    def test_function_bodies_do_not_enter_the_inventory(self):
        result = inventory("""
          #define EVERPARSE_STATUS_SUCCESS (0U)
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
        self.assertEqual(result["macros"]["EVERPARSE_STATUS_SUCCESS"], "( 0U )")

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

    def test_abi_comparison_rejects_boolean_and_linkage_regressions(self):
        expected = inventory("static inline BOOLEAN f(uint8_t n) { return n; }")
        self.assertEqual(compare_abi(expected, expected), [])
        self.assertTrue(compare_abi(
            expected, inventory("static inline bool f(uint8_t n) { return n; }")
        ))
        self.assertTrue(compare_abi(
            expected, inventory("extern BOOLEAN f(uint8_t n);")
        ))
        actual = inventory(
            "typedef bool BOOLEAN; static inline BOOLEAN f(uint8_t n) { return n; }"
        )
        self.assertIn("BOOLEAN is not a uint8_t alias", compare_abi(expected, actual))

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
    def test_validator_booleans_are_independent_of_stream_booleans(self):
        contract = json.loads((HERE / "runtime-contract.json").read_text())
        self.assertEqual(contract["validator_boolean"],
                         {"pulse": "bool", "lowstar": "BOOLEAN"})
        self.assertEqual(contract["boolean"]["representation"], "uint8_t")

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

    def test_canonical_sources_own_all_bindings(self):
        for profile in PROFILES:
            names, _, _, external, _ = profile_config(profile)
            for module, declarations in names.items():
                suffix = ".fsti" if module == "InputStream.LowstarExtern.Raw" else ".fst"
                source = (RUNTIME / ("EverParse3d." + module + suffix)).read_text()
                for target in declarations.values():
                    self.assertIn('"' + target + '"', source)
            for qualified, target in external.items():
                module, _ = qualified.rsplit(".", 1)
                source = (RUNTIME / ("EverParse3d." + module + ".fst")).read_text()
                self.assertIn('custard_extern "' + target + '"', source)

    def test_static_and_extern_share_verified_modules(self):
        for prefix in ("", "lowstar/"):
            self.assertEqual(profile_config(prefix + "static"),
                             profile_config(prefix + "extern"))

    def test_companions_only_declare_selected_functions(self):
        for profile in ("static", "lowstar/static"):
            declarations = inventory(companion(profile))
            self.assertEqual(set(declarations["functions"]),
                             set(PROFILES[profile]["static_hooks"]))
            self.assertEqual(declarations["values"], {})
            self.assertEqual(declarations["types"], {})
            self.assertNotIn("EverParseStreamOf", declarations["functions"])
            for signature in declarations["functions"].values():
                self.assertEqual(signature["linkage"], "static inline")
        for profile in ("extern", "lowstar/extern"):
            declarations = inventory(companion(profile))
            self.assertTrue(declarations["functions"])
            self.assertTrue(all(s["linkage"] == "extern"
                                for s in declarations["functions"].values()))
        with self.assertRaises(ValueError):
            companion("buffer")

    def test_copy_buffer_metadata_exists_for_every_stream(self):
        for profile in PROFILES:
            _, _, _, external, _ = profile_config(profile)
            self.assertIn("EVERPARSE_COPY_BUFFER_T", external.values())

    def test_extraction_cannot_shadow_the_shared_library(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build = root / "build"
            (build / "src").mkdir(parents=True)
            (build / "src/EverParse3d.ErrorCode.fst").write_text("stale profile source")
            output = root / "published/EverParse.h"

            def run(command, check):
                self.assertTrue(check)
                includes = [command[i + 1] for i, arg in enumerate(command)
                            if arg == "--include"]
                self.assertIn(str(RUNTIME), includes)
                self.assertNotIn(str(build / "src"), includes)
                self.assertNotIn(str(build / "checked"), includes)
                if "--codegen" in command:
                    (build / "EverParse.h").write_text("header")
                    (build / "EverParse.cui").write_text("unit")

            with patch("runtime_headers.subprocess.run", side_effect=run), \
                    patch("runtime_headers.native_path", side_effect=str):
                extract(Namespace(profile="extern", build_dir=build, output=output,
                                  fstar="fstar.exe", fstar_options=""))
            self.assertEqual(output.read_text(), "header")
            self.assertEqual(output.with_suffix(".cui").read_text(), "unit")
            self.assertEqual(sorted(p.name for p in output.parent.iterdir()),
                             ["EverParse.cui", "EverParse.h"])


if __name__ == "__main__":
    unittest.main()

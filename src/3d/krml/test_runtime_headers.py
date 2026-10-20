import json
from pathlib import Path
import unittest


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


if __name__ == "__main__":
    unittest.main()

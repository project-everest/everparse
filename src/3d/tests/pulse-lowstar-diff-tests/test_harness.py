"""Generated harness regression tests; these fixtures do not certify either backend."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from cases import generate as cases
from compare import check_executed, compare, coverage, read_trace
from corpus import HERE, SUITES, HarnessError, classify, excluded, inventory, source_path, write_json
from driver import ast_fields, check_signatures, generate, observations, parameters, signatures
from proxy import selected_args
from run import build_suite, c_sources, command, main


class CommandTests(unittest.TestCase):
    def test_clean_removes_both_build_trees_but_preserves_sources_and_rejects_symlinks(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root = Path(tmp)
            outputs = (root / "_build", root / "adapter-tests/_build")
            for output in outputs:
                output.mkdir(parents=True)
                (output / "generated").write_text("artifact")
            source = root / "adapter-tests/fixture.c"
            source.write_text("source")
            with patch("run.HERE", root):
                self.assertEqual(main(["--clean"]), 0)
                self.assertTrue(all(not output.exists() for output in outputs))
                self.assertEqual(source.read_text(), "source")
                outputs[0].mkdir()
                outputs[1].symlink_to(outputs[0], target_is_directory=True)
                with self.assertRaisesRegex(HarnessError, "symlinked"):
                    main(["--clean"])
                self.assertTrue(outputs[0].is_dir())
                self.assertTrue(outputs[1].is_symlink())

    def test_root_targets_have_separate_budgets_and_retained_logs(self):
        with patch("run.command") as execute:
            build_suite("root", HERE, HERE, {}, HERE / "build.log", 7, api="legacy_lowstar")
        self.assertEqual(execute.call_count, len(SUITES["root"][1]))
        for index, call in enumerate(execute.call_args_list):
            self.assertEqual(call.args[0],
                             ["make", "--no-print-directory", "-j1", "-C",
                              HERE, SUITES["root"][1][index]])
            self.assertEqual(call.args[1:], (HERE, {}, HERE / "build.log", 7))
            self.assertEqual(call.kwargs, {"append": index > 0})
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            log = Path(tmp) / "build.log"
            command([sys.executable, "-c", "print('first target')"], HERE, os.environ, log, 5)
            command([sys.executable, "-c", "print('second target')"],
                    HERE, os.environ, log, 5, append=True)
            self.assertIn("\nfirst target\n", log.read_text())
            self.assertIn("\nsecond target\n", log.read_text())

    def test_cleanup_extras_are_scoped_to_lowstar_root_cleanup(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root = Path(tmp)
            out = root / "out.cleanup"
            (out / "internal").mkdir(parents=True)
            (out / "internal/ELF.h").write_text("worker")
            (out / "EverParsePulseInternal.h").write_text("runtime")
            for api in ("legacy_lowstar", "lowstar"):
                with patch("run.command") as execute:
                    build_suite("root", root, root, {}, root / "build.log", 7, api=api)
                self.assertEqual(execute.call_count, len(SUITES["root"][1]))
                for call, target in zip(execute.call_args_list, SUITES["root"][1]):
                    expected = ["make", "--no-print-directory", "-j1", "-C", root, target]
                    if api == "lowstar" and target == "batch-cleanup-test":
                        expected += ["EXTRA_CLEAN_OUT_FILES=EverParsePulseInternal.h internal"]
                    self.assertEqual(call.args[0], expected)
            with patch("run.command") as execute:
                build_suite("modules", root, root, {}, root / "build.log", 7, api="lowstar")
            self.assertEqual(execute.call_args.args[0],
                             ["make", "--no-print-directory", "-j1", "-C", root / "modules", "all"])

    def test_cleanup_inventory_rejects_missing_extra_nested_and_symlinked_outputs(self):
        layouts = ("missing-internal", "empty-internal", "extra-header", "nested-header",
                   "empty-directory", "symlink-header", "symlink-directory",
                   "missing-runtime", "symlink-runtime")
        for layout in layouts:
            with self.subTest(layout=layout), tempfile.TemporaryDirectory(dir=HERE) as tmp:
                root = Path(tmp)
                out = root / "out.cleanup"
                internal = out / "internal"
                internal.mkdir(parents=True)
                worker = internal / "ELF.h"
                worker.write_text("worker")
                runtime = out / "EverParsePulseInternal.h"
                runtime.write_text("runtime")
                if layout in {"missing-internal", "empty-internal"}:
                    worker.unlink()
                    if layout == "missing-internal":
                        internal.rmdir()
                elif layout == "extra-header":
                    (internal / "Other.h").write_text("unexpected")
                elif layout in {"nested-header", "empty-directory"}:
                    (internal / "nested").mkdir()
                    if layout == "nested-header":
                        (internal / "nested/Other.h").write_text("unexpected")
                elif layout == "symlink-header":
                    worker.unlink()
                    worker.symlink_to(runtime)
                elif layout == "symlink-directory":
                    internal.rename(out / "elsewhere")
                    internal.symlink_to(out / "elsewhere", target_is_directory=True)
                elif layout == "missing-runtime":
                    runtime.unlink()
                elif layout == "symlink-runtime":
                    runtime.unlink()
                    runtime.symlink_to(worker)
                with patch("run.command") as execute, self.assertRaisesRegex(
                        HarnessError, "lowstar cleanup"):
                    build_suite("root", root, root, {}, root / "build.log", 7, api="lowstar")
                self.assertEqual(execute.call_count,
                                 SUITES["root"][1].index("batch-cleanup-test") + 1)

    def test_cleanup_make_extension_keeps_legacy_default_and_accepts_only_known_lowstar_files(self):
        for api in ("legacy_lowstar", "lowstar"):
            with self.subTest(api=api), tempfile.TemporaryDirectory(dir=HERE) as tmp:
                root = Path(tmp)
                out = root / "out.cleanup"
                out.mkdir()
                (out / "Unit.c").write_text("generated")
                if api == "lowstar":
                    (out / "internal").mkdir()
                    (out / "internal/ELF.h").write_text("worker")
                    (out / "EverParsePulseInternal.h").write_text("runtime")
                (root / "Makefile").write_text(
                    "clean_out_files = Unit.c\n"
                    "clean_out_files += $(EXTRA_CLEAN_OUT_FILES)\n"
                    "batch-cleanup-test:\n"
                    '\ttest "$$(ls out.cleanup | sort)" = '
                    '"$$(for f in $(clean_out_files); do echo $$f; done | sort)"\n')
                env = dict(os.environ)
                for key in ("MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES", "EXTRA_CLEAN_OUT_FILES"):
                    env.pop(key, None)
                with patch.dict(SUITES, {"root": (".", ["batch-cleanup-test"], [])}):
                    build_suite("root", root, root, env, root / "build.log", 5, api=api)
                self.assertIn("test \"$(ls out.cleanup | sort)\"", (root / "build.log").read_text())
                self.assertEqual((out / "Unit.c").read_text(), "generated")

    def test_timeout_stops_descendants_and_retains_failure_log(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root = Path(tmp)
            ready, survived = root / "ready", root / "survived"
            child = ("import pathlib,time; "
                     f"pathlib.Path({str(ready)!r}).write_text('ready'); "
                     "time.sleep(3); "
                     f"pathlib.Path({str(survived)!r}).write_text('survived')")
            parent = ("import subprocess,sys; "
                      f"subprocess.Popen([sys.executable, '-c', {child!r}]).wait()")
            log = root / "timeout.log"
            with self.assertRaisesRegex(HarnessError, r"timeout \(1s\)"):
                command([sys.executable, "-c", parent], HERE, os.environ, log, 1)
            self.assertTrue(ready.exists(), "fixture descendant must have started")
            time.sleep(3)
            self.assertFalse(survived.exists(), "timeout must not leave descendants running")
            self.assertIn("$ ", log.read_text())


class InventoryTests(unittest.TestCase):
    def test_generated_and_harness_files_are_not_corpus(self):
        for name in ("out.batch/Test.3d", "foo/obj/Test.c", "foo/interpret.out/Test.3d",
                     "pulse-diff/seeds.inc", "pulse-lowstar-diff-tests/run.py"):
            self.assertTrue(excluded(name), name)
        self.assertFalse(excluded("output_types/TPoint.3d"))
        self.assertFalse(excluded("obj.3d"))
        self.assertFalse(excluded("objects/New.3d"))
        self.assertEqual(classify("probe/src/Probe.3d"),
                         ("runtime-grammar", ["probe/src", "probe"]))
        self.assertEqual(classify("goto_return/snapshot/GotoReturnWrapper.c"),
                         ("snapshot", ["goto_return"]))
        self.assertEqual(classify("exttype/Test.3d")[0], "generation-only-grammar")

    def test_unknown_scope_and_negative_fail_closed(self):
        for name in ("new_stream/Test.3d", "FAILNew.3d", "../Test.3d", "/tmp/Test.3d"):
            with self.assertRaises(HarnessError, msg=name):
                classify(name)
        with self.assertRaises(HarnessError):
            source_path("a//b")

    def test_git_inventory_ignores_untracked_generated_files(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root = Path(tmp)
            corpus = root / "src/3d/tests"
            corpus.mkdir(parents=True)
            (corpus / "A.3d").write_text("entrypoint")
            (corpus / "unexpected.3d").write_text("generated")
            subprocess.run(["git", "init", "-q", tmp], check=True)
            subprocess.run(["git", "-C", tmp, "add", "src/3d/tests/A.3d"], check=True)
            data = inventory(root)
            self.assertEqual([r["path"] for r in data["files"]], ["A.3d"])
            manifest = root / "manifest.json"
            write_json(manifest, data)
            with self.assertRaisesRegex(HarnessError, "unlisted packaged grammars"):
                inventory(root, manifest)
            (corpus / "unexpected.3d").unlink()
            self.assertEqual(inventory(root, manifest), data)
            (corpus / "A.3d").write_text("changed")
            with self.assertRaisesRegex(HarnessError, "checksum mismatch"):
                inventory(root, manifest)


class CompareTests(unittest.TestCase):
    def test_return_partial_update_error_and_pointer_differences(self):
        fields = {"return": 0, "out.x": 17, "out.p": "input+3",
                  "error.0.kind": 6, "error.0.position": 7}
        baseline = {("input-1", "Check", field): value for field, value in fields.items()}
        self.assertEqual(compare(baseline, baseline), [])
        for field in fields:
            changed = dict(baseline)
            changed["input-1", "Check", field] = "different"
            diffs = compare(baseline, changed)
            self.assertEqual(len(diffs), 1)
            self.assertEqual(diffs[0]["field"], field)
            self.assertEqual(diffs[0]["legacy_lowstar"], fields[field])
        missing = dict(baseline)
        del missing["input-1", "Check", "out.x"]
        self.assertEqual(compare(baseline, missing)[0]["missing"], "lowstar")
        self.assertNotEqual(compare({("x", "f", "return"): True},
                                    {("x", "f", "return"): 1}), [])

    def test_trace_rejects_empty_duplicate_invalid_and_unknown_pointer(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            p = Path(tmp) / "trace"
            valid = "@@" + json.dumps(dict(case="a", function="f", field="return", value=0)) + "\n"
            p.write_text("client diagnostic\n" + valid)
            self.assertEqual(read_trace(p), {("a", "f", "return"): 0})
            for text in ("client passed\n", valid + valid, "@@bad\n",
                         "@@{}\n", valid.replace('"value": 0', '"value": "<unregistered-pointer>"')):
                p.write_text(text)
                with self.assertRaises(HarnessError, msg=text):
                    read_trace(p)

    def test_missing_fields_do_not_count_as_coverage(self):
        required = {"f": {"fields": ["return", "out.x"], "return": "BOOLEAN"}}
        result = coverage({("a", "f", "return"): 0}, required)["f"]
        self.assertEqual(result, {"cases": 1, "success": 0, "failure": 1,
                                  "missing_fields": ["a:out.x"]})
        self.assertEqual(coverage({}, required)["f"]["missing_fields"], ["no executed cases"])

    def test_identically_missing_input_execution_is_not_a_pass(self):
        required = {"f": {}}
        inputs = "first 0 0 0 0 0 0 1 -\nsecond 0 0 0 0 0 0 1 -\n"
        partial = {("first", "f", "return"): 1}
        self.assertEqual(compare(partial, partial), [])
        with self.assertRaisesRegex(HarnessError, "1 missing"):
            check_executed(partial, inputs, required)
        partial["second", "f", "return"] = 0
        check_executed(partial, inputs, required)


class DriverTests(unittest.TestCase):
    def test_internal_header_dependency_keeps_worker_implementation(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            out = Path(tmp)
            (out / "internal").mkdir()
            (out / "Entry.c").write_text('#include "internal/Worker.h"\n')
            (out / "internal/Worker.h").write_text('#include "../Public.h"\n')
            (out / "Worker.c").write_text('#include "internal/Worker.h"\n')
            (out / "Public.h").write_text('#include "internal/Worker.h"\n')
            (out / "Unrelated.c").write_text("int unrelated;\n")
            self.assertEqual({p.name for p in c_sources(out, "Entry")}, {"Entry.c", "Worker.c"})

    def test_proxy_preserves_stream_options_and_rejects_api_override(self):
        args = ["--input_stream", "static", "--config", "flags.config", "--batch", "Test.3d"]
        self.assertEqual(selected_args(args, "lowstar"), args + ["--api", "lowstar"])
        self.assertEqual(args[-1], "Test.3d")
        for args in (["--api", "pulse"], ["--api"], ["--api=legacy_lowstar"], ["--pulse"]):
            with self.assertRaises(ValueError):
                selected_args(args, "lowstar")

    def test_signature_parser_and_exact_abi_comparison(self):
        parsed = parameters("uint64_t *Out, EVERPARSE_INPUT_BUFFER Input,\nuint64_t Start")
        self.assertEqual(parsed, [("uint64_t*", "Out"), ("EVERPARSE_INPUT_BUFFER", "Input"),
                                  ("uint64_t", "Start")])
        check_signatures({"f": ("uint64_t", parsed)}, {"f": ("uint64_t", parsed)})
        with self.assertRaisesRegex(HarnessError, "incompatible"):
            check_signatures({"f": ("uint64_t", parsed)}, {"f": ("uint8_t", parsed)})
        with self.assertRaisesRegex(HarnessError, "public functions differ"):
            check_signatures({"f": ("uint64_t", parsed)}, {})
        with self.assertRaises(HarnessError):
            parameters("void (*callback)(void)")
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            header = Path(tmp) / "Wrapper.h"
            header.write_text("size_t NewCheck(uint8_t *base, uint32_t len);\n")
            with self.assertRaisesRegex(HarnessError, "unsupported public return"):
                signatures(header)

    def test_deterministic_cases_have_nonzero_starts_and_initialized_outputs(self):
        req = {"f": {"direct": True}}
        first = cases(req, {}, 5)
        self.assertEqual(first, cases(req, {}, 5))
        rows = [r.split() for r in first.splitlines()]
        self.assertTrue(any(r[5] == "3" for r in rows))
        self.assertEqual({r[4] for r in rows}, {"0", "165"})
        self.assertTrue(all(int(r[5]) <= int(r[2]) for r in rows))

    def test_specialization_array_witnesses_select_both_widths_with_capacity(self):
        for prefix, suffix in (("SpecializeTaggedUnionArray", "Main"),
                               ("SpecializeVlarray", "UnknownHeaders")):
            for direct in (False, True):
                fn = prefix + ("Validate" if direct else "Check") + suffix
                for iterations in range(4):
                    rows = [r.split() for r in cases({fn: {"direct": direct}}, {}, iterations).splitlines()]
                    for arg in (8, 9):
                        for initial in (0, 165):
                            self.assertTrue(any(int(r[2]) == 8 and int(r[3]) == arg
                                                and int(r[4]) == initial and int(r[5]) == 0
                                                and int(r[6]) > 0 for r in rows),
                                            (fn, iterations, arg, initial))
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root = Path(tmp)
            for module, count in (("SpecializeTaggedUnionArray", "Count"),
                                  ("SpecializeVLArray", "UnknownHeaderCount")):
                (root / (module + ".h")).write_text(f"""
uint64_t {module}ValidateMain(BOOLEAN Requestor32, uint16_t {count},
 uint8_t *Ctxt, EVERPARSE_ERROR_HANDLER ErrorHandlerFn, uint8_t *Input,
 uint64_t InputLength, uint64_t StartPosition);
""")
                text, _ = generate(module, root, root, [root])
                self.assertIn("abi_0((BOOLEAN)((arg & 1)), (uint16_t)(arg >> 1)", text)

    def test_grammar_len_argument_is_not_confused_with_input_length(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root = Path(tmp)
            (root / "Scope.h").write_text("""
uint64_t ScopeValidate(uint32_t Len, uint8_t *Ctxt,
 EVERPARSE_ERROR_HANDLER ErrorHandlerFn, uint8_t *Input,
 uint64_t InputLength, uint64_t StartPosition);
""")
            text, _ = generate("Scope", root, root, [root])
            self.assertIn("abi_0((uint32_t)(arg), context, df_error, buf, len, start)", text)

    def test_structural_observers_never_serialize_padding(self):
        init, code, fields = observations("S", "o", "out.s", lambda ty: ["small", "nested.large"])
        self.assertEqual(fields, ["out.s.small", "out.s.nested.large"])
        self.assertIn("o.nested.large", "\n".join(code))
        self.assertNotIn("memcmp", "\n".join(code))
        self.assertNotIn("sizeof", "\n".join(code))
        self.assertIn("S o = {0}", init)

    def test_real_header_fields_and_padding_pointer_normalization(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root = Path(tmp)
            header = root / "Types.h"
            header.write_text("""
#include <stdint.h>
typedef struct { uint32_t large; } INNER;
typedef struct { uint8_t small; INNER nested; uint16_t flag:3; } OUTPUT;
typedef struct { uint32_t x; struct { uint32_t y; uint32_t z; }; } ANONYMOUS;
""")
            resolve = ast_fields(header, [root])
            self.assertEqual(resolve("OUTPUT"), ["small", "nested.large", "flag"])
            self.assertEqual(resolve("ANONYMOUS"), ["x", "y", "z"])
            _, code, fields = observations("OUTPUT", "out", "out.value", resolve)
            source = """
#include "Types.h"
typedef unsigned char BOOLEAN;
typedef uint8_t *EVERPARSE_INPUT_BUFFER;
#include "observe.h"
int main(int argc, char **argv) {
 OUTPUT out; uint8_t input[4] = {0};
 memset(&out, argc>1 ? 255:0, sizeof out);
 out.small=7; out.nested.large=argc>2 ? 9:8; out.flag=3;
 df_begin("same-input","Fixture");
 df_region("input",input,sizeof input);
 df_pointer("out.pointer",input+2);
"""
            (root / "test.c").write_text(source + "\n".join(code) + "\ndf_end(1,0); return 0; }\n")
            exe = root / "test"
            subprocess.run(["cc", "-std=c11", "-I" + str(HERE), "-I" + str(root),
                            str(root / "test.c"), "-o", str(exe)], check=True, capture_output=True)
            import os
            values = []
            for index, args in enumerate(([], ["padding"], ["padding", "mutation"])):
                trace = root / str(index)
                subprocess.run([str(exe), *args], check=True, capture_output=True,
                               env=dict(os.environ, DIFF_TRACE=str(trace)))
                values.append(read_trace(trace))
            self.assertEqual(compare(values[0], values[1]), [])
            self.assertEqual(compare(values[1], values[2])[0]["field"], "out.value.nested.large")
            self.assertEqual(values[0]["same-input", "Fixture", "out.pointer"], "input+2")
            self.assertEqual(fields, ["out.value.small", "out.value.nested.large", "out.value.flag"])

    def test_compiled_fixture_observes_failures_offsets_and_packed_positions(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root = Path(tmp)
            (root / "EverParse.h").write_text("""
#ifndef EP_H
#define EP_H
#include <stdint.h>
typedef unsigned char BOOLEAN;
typedef uint8_t *EVERPARSE_INPUT_BUFFER;
typedef void (*EVERPARSE_ERROR_HANDLER)(const char *,const char *,const char *,
 uint64_t,uint8_t *,EVERPARSE_INPUT_BUFFER,uint64_t);
#endif
""")
            (root / "Fixture.h").write_text("""
#include "EverParse.h"
uint64_t FixtureValidateRead(uint32_t *Out, uint8_t *Ctxt,
 EVERPARSE_ERROR_HANDLER ErrorHandlerFn, uint8_t *Input,
 uint64_t InputLength, uint64_t StartPosition);
uint64_t FixtureValidateLook(uint32_t *Out, uint8_t *Ctxt,
 EVERPARSE_ERROR_HANDLER ErrorHandlerFn, uint8_t *Input,
 uint64_t InputLength, uint64_t StartPosition);
""")
            (root / "FixtureWrapper.h").write_text("""
#include "Fixture.h"
BOOLEAN FixtureCheck(uint32_t *Out, uint8_t *base, uint32_t len);
""")
            (root / "Fixture.c").write_text("""
#include "Fixture.h"
uint64_t FixtureValidateRead(uint32_t *out, uint8_t *ctx, EVERPARSE_ERROR_HANDLER eh,
 uint8_t *input, uint64_t len, uint64_t start) {
 if (len > start) { *out = input[start]; ++start; }
 if (len == start) { eh("S", "tail", "not enough data", 2, ctx, input, start);
   return (UINT64_C(2)<<60)|start; }
 return start+1;
}
uint64_t FixtureValidateLook(uint32_t *out, uint8_t *ctx, EVERPARSE_ERROR_HANDLER eh,
 uint8_t *input, uint64_t len, uint64_t start) {
 (void)out;
 if (len-start<2) { eh("S","tail","not enough data",2,ctx,input,start);
   return (UINT64_C(2)<<60)|start; }
 return start+2;
}
""")
            (root / "FixtureWrapper.c").write_text("""
#include "FixtureWrapper.h"
static void error(const char *a,const char *b,const char *c,uint64_t d,
 uint8_t *e,EVERPARSE_INPUT_BUFFER f,uint64_t g) {}
BOOLEAN FixtureCheck(uint32_t *out, uint8_t *base, uint32_t len) {
 uint8_t ctxt=0;
 return FixtureValidateRead(out,&ctxt,error,base,len,0)>>60 == 0;
}
""")
            text, required = generate("Fixture", root, root, [root])
            (root / "driver.c").write_text(text)
            exe = root / "fixture"
            subprocess.run(["cc", "-std=c11", "-Werror=incompatible-pointer-types",
                            "-I" + str(root), "-I" + str(HERE),
                            str(root / "driver.c"), str(root / "Fixture.c"),
                            str(root / "FixtureWrapper.c"),
                            "-Wl,--wrap=FixtureValidateRead", "-Wl,--wrap=FixtureValidateLook",
                            "-o", str(exe)], check=True, capture_output=True)
            trace = root / "trace"
            import os
            subprocess.run([str(exe)], input="partial 1 4 0 165 3 3 1 0000002a\n"
                           "no-read 2 4 0 165 3 3 1 0000002a\n"
                           "wrapper 0 1 0 165 0 3 1 2a\n",
                           text=True, check=True, capture_output=True,
                           env=dict(os.environ, DIFF_TRACE=str(trace)))
            observed = read_trace(trace)
            self.assertEqual(observed["partial", "FixtureValidateRead", "out.Out"], 42)
            self.assertEqual(observed["partial", "FixtureValidateRead", "return.kind"], 2)
            self.assertEqual(observed["partial", "FixtureValidateRead", "return.position"], 4)
            self.assertEqual(observed["no-read", "FixtureValidateLook", "out.Out"], 165)
            self.assertEqual(observed["no-read", "FixtureValidateLook", "return.position"], 3)
            self.assertEqual(observed["wrapper", "FixtureCheck", "validator.position"], 1)
            self.assertEqual(observed["partial", "FixtureValidateRead", "error.0.input"], "input+0")
            self.assertFalse(coverage(observed, required)["FixtureCheck"]["missing_fields"])
            invalid = subprocess.run([str(exe)], input="incomplete", text=True, capture_output=True)
            self.assertEqual(invalid.returncode, 2)
            self.assertIn("malformed differential input", invalid.stderr)


if __name__ == "__main__":
    unittest.main()

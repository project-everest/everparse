import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from corpus import APIS, HERE, HarnessError
from parallel import JobBudget, run_jobs
from run import run_suites


class BudgetTests(unittest.TestCase):
    def exercise_parallelism(self, budget):
        lock = threading.Lock()
        barrier = threading.Barrier(3, timeout=10)
        active = maximum = 0

        def action():
            nonlocal active, maximum
            with lock:
                active += 1
                maximum = max(maximum, active)
            barrier.wait()
            with lock:
                active -= 1
            return "done"

        result = dict(run_jobs([(i, action) for i in range(6)], budget))
        self.assertEqual(result, {i: "done" for i in range(6)})
        self.assertEqual(maximum, 3)
        self.assertTrue(budget.implicit_available)

    def test_standalone_limit_and_serial_default(self):
        with patch.dict(os.environ, MAKEFLAGS=""):
            with JobBudget() as budget:
                self.assertEqual(budget.jobs, 1)
                self.assertEqual(list(run_jobs([(i, lambda: 42) for i in range(4)], budget)),
                                 [(i, 42) for i in range(4)])
            with JobBudget(3) as budget:
                self.exercise_parallelism(budget)
            with self.assertRaisesRegex(HarnessError, "positive"):
                JobBudget(0)

    @unittest.skipUnless(sys.platform == "linux", "Linux pipe jobserver")
    def test_pipe_tokens_returned_without_changing_make_reader(self):
        reader, writer = os.pipe()
        try:
            os.write(writer, b"XY")
            with patch.dict(os.environ, MAKEFLAGS=f" -j3 --jobserver-auth={reader},{writer}"):
                with JobBudget(3) as budget:
                    self.assertTrue(os.get_blocking(reader))
                    self.exercise_parallelism(budget)
                    self.assertEqual(sorted(os.read(budget.reader, 2)), sorted(b"XY"))
                    self.assertTrue(os.get_blocking(reader))
        finally:
            os.close(reader)
            os.close(writer)

    def test_fifo_tokens_and_unavailable_slots(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            fifo = Path(tmp) / "fifo"
            os.mkfifo(fifo)
            fd = os.open(fifo, os.O_RDWR | os.O_NONBLOCK)
            try:
                with patch.dict(os.environ, MAKEFLAGS=f"--jobserver-auth=fifo:{fifo}"):
                    with JobBudget(3) as budget:
                        self.assertEqual(budget.acquire(), b"")
                        self.assertIsNone(budget.acquire())
                        os.write(fd, b"XY")
                        token = budget.acquire()
                        self.assertEqual(token, b"X")
                        budget.release(token)
                        budget.release(b"")
                        self.exercise_parallelism(budget)
                        self.assertEqual(sorted(os.read(fd, 2)), sorted(b"XY"))
            finally:
                os.close(fd)

    def test_tokens_returned_on_worker_and_iterator_errors(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            fifo = Path(tmp) / "fifo"
            os.mkfifo(fifo)
            fd = os.open(fifo, os.O_RDWR | os.O_NONBLOCK)
            try:
                for kind in ("worker", "iterator"):
                    os.write(fd, b"X")

                    def fail():
                        raise RuntimeError("injected failure")

                    def jobs():
                        yield 0, lambda: 0
                        if kind == "iterator":
                            raise RuntimeError("injected failure")
                        yield 1, fail

                    with patch.dict(os.environ, MAKEFLAGS=f"--jobserver-auth=fifo:{fifo}"):
                        with JobBudget(2) as budget:
                            with self.assertRaisesRegex(RuntimeError, "injected"):
                                list(run_jobs(jobs(), budget))
                            self.assertTrue(budget.implicit_available)
                    self.assertEqual(os.read(fd, 1), b"X")
            finally:
                os.close(fd)

    def test_invalid_jobserver_is_not_silently_ignored(self):
        with patch.dict(os.environ, MAKEFLAGS="--jobserver-auth=-1,-1"):
            with self.assertRaisesRegex(HarnessError, "jobserver"):
                JobBudget(4)

    def test_real_recursive_make_jobserver(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root = Path(tmp)
            script = root / "check.py"
            script.write_text(
                "from parallel import JobBudget\n"
                "from test_parallel import BudgetTests\n"
                "with JobBudget(3) as budget:\n"
                "    assert budget.reader is not None\n"
                "    BudgetTests().exercise_parallelism(budget)\n")
            (root / "Makefile").write_text(
                f"all:\n\t+{sys.executable} {script}\n")
            env = dict(os.environ, PYTHONPATH=str(HERE))
            for key in ("MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES"):
                env.pop(key, None)
            result = subprocess.run(["make", "--no-print-directory", "-j3", "-C", root],
                                    env=env, capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn("INTERNAL", result.stderr)


class AccountingTests(unittest.TestCase):
    def test_parallel_builds_comparisons_and_failures_preserve_accounting(self):
        for failure in (None, "build", "comparison", "mismatch"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory(dir=HERE) as tmp:
                work = Path(tmp)
                report = {"suites": {}}
                stages = {api: (work / api, {}) for api in APIS}
                args = SimpleNamespace(timeout=10, iterations=1, cc="cc", clang="clang")
                barrier = threading.Barrier(2, timeout=10)

                def build(suite, target, api, *args):
                    barrier.wait()
                    if failure == "build" and api == "lowstar":
                        raise HarnessError("build failed")

                def compare(*args, modules):
                    output, module = modules[0]
                    if failure == "comparison" and module == "A":
                        raise HarnessError("comparison failed")
                    return [{"output": output, "module": module, "missing_coverage": {},
                             "differences": ["mismatch"] if failure == "mismatch" else []}]

                with patch.dict(os.environ, MAKEFLAGS=""), \
                     patch("run.SUITES", {"fixture": (".", ["all"], ["out"])}), \
                     patch("run.build_target", side_effect=build), \
                     patch("run.comparison_modules", return_value=[("out", "B"), ("out", "A")]), \
                     patch("run.differential", side_effect=compare) as diff, JobBudget(2) as budget:
                    run_suites(["fixture"], work, stages, work, args, report, budget)
                result = report["suites"]["fixture"]
                self.assertEqual(result["status"],
                                 "blocked" if failure in {"build", "comparison"} else
                                 "failed" if failure == "mismatch" else "passed")
                self.assertEqual(set(result["builds"]), set(APIS))
                self.assertEqual(diff.call_count, 0 if failure == "build" else 2)
                if failure != "build":
                    self.assertEqual([item["module"] for item in result["comparisons"]],
                                     ["B"] if failure == "comparison" else ["A", "B"])
                self.assertEqual(json.loads((work / "report.json").read_text()), report)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""Full-corpus Low* ABI differential gate. Partial runs never certify compatibility."""

import argparse
from functools import partial
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile

from cases import generate as generate_cases, seeds
from clients import support_for
from compare import check_executed, compare, coverage, read_trace
from corpus import (APIS, CORPUS, HERE, NEGATIVES, SUITES, HarnessError, digest,
                    inventory, write_json)
from driver import generate, signatures
from parallel import JobBudget, run_jobs


def run_process(argv, *, timeout, **kwargs):
    """Bound the entire process group, including make/generator descendants."""
    with subprocess.Popen(argv, start_new_session=True, **kwargs) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass  # The group finished between the timeout and termination.
            process.communicate()
            raise
    return subprocess.CompletedProcess(argv, process.returncode, stdout, stderr)


def command(argv, cwd, env, log, timeout, *, append=False):
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("a" if append else "w") as output:
        output.write("$ " + shlex.join(map(str, argv)) + "\n")
        output.flush()
        try:
            process = run_process(list(map(str, argv)), cwd=cwd, env=env,
                                  stdout=output, stderr=subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired as error:
            raise HarnessError(f"timeout ({timeout}s): {log}") from error
    if process.returncode:
        raise HarnessError(f"command failed ({process.returncode}): {log}")


def build_suite(suite, home, tree, env, log, timeout, *, api, target=None):
    directory, targets, _ = SUITES[suite]
    if target is not None:
        targets = [target]
    for index, target in enumerate(targets):
        lowstar_cleanup = api == "lowstar" and suite == "root" and target == "batch-cleanup-test"
        extras = (["EXTRA_CLEAN_OUT_FILES=EverParsePulseInternal.h internal"]
                  if lowstar_cleanup else [])
        command(["make", "--no-print-directory", "-j1", "-C", tree / directory, target, *extras],
                home, env, log, timeout, append=index > 0)
        if lowstar_cleanup:
            out = tree / directory / "out.cleanup"
            internal = out / "internal"
            if internal.is_symlink() or not internal.is_dir():
                raise HarnessError(f"missing or non-directory lowstar cleanup internal inventory: {internal}")
            entries = list(internal.rglob("*"))
            found = sorted(p.relative_to(out).as_posix() for p in entries)
            if found != ["internal/ELF.h"] or any(p.is_symlink() or not p.is_file() for p in entries):
                raise HarnessError("unexpected lowstar cleanup internal inventory: "
                                   f"expected regular internal/ELF.h only, found {found}")
            header = out / "EverParsePulseInternal.h"
            if header.is_symlink() or not header.is_file():
                raise HarnessError(f"missing or non-regular lowstar cleanup runtime header: {header}")


def stage(home, work, api, listing):
    root = work / api
    root.mkdir()
    tree = root / "tests"
    for record in listing["files"]:
        source, dest = home / CORPUS / record["path"], tree / record["path"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dest)
        if digest(dest) != record["sha256"]:
            raise HarnessError(f"source changed during staging: {source}")
    proxy = root / "home"
    proxy.mkdir()
    for path in home.iterdir():
        if path.name not in {"bin", ".git"}:
            (proxy / path.name).symlink_to(path, target_is_directory=path.is_dir())
    (proxy / "bin").mkdir()
    for path in (home / "bin").iterdir():
        if path.name != "3d.exe":
            (proxy / "bin" / path.name).symlink_to(path)
    shutil.copy2(HERE / "proxy.py", proxy / "bin/3d.exe")
    (proxy / "bin/3d.exe").chmod(0o755)
    write_json(proxy / "bin/proxy.json",
               {"api": api, "home": str(home), "log": str(root / "invocations")})
    env = dict(os.environ, EVERPARSE_HOME=str(proxy), EVERPARSE_API=api)
    # Inherited make command-line overrides must not bypass the API proxy.
    for key in ("MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES", "EVERPARSE_CMD", "EVERPARSE_EXE", "3D",
                "EXTRA_CLEAN_OUT_FILES"):
        env.pop(key, None)
    return tree, env


def negative(name, home, tree, env, work, timeout):
    stage_name, pattern = NEGATIVES[name]
    odir = tree / "negative" / Path(name).stem
    odir.mkdir(parents=True)
    argv = [str(Path(env["EVERPARSE_HOME"]) / "bin/3d.exe"), "--batch",
            "--odir", str(odir), name]
    fstar = env.get("FSTAR_EXE")
    if fstar:
        argv += ["--fstar", fstar]
    process = run_process(argv, cwd=tree, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True, timeout=timeout)
    text = process.stdout + process.stderr
    (work / (name + ".log")).write_text(text)
    if process.returncode <= 0 or not re.search(pattern, text):
        raise HarnessError(f"{name}: not the expected {stage_name} failure "
                           f"(returncode {process.returncode})")
    if stage_name == "verification":
        if not re.search(re.escape(Path(name).stem) + r"\.fst\(", text):
            raise HarnessError(f"{name}: verification failed outside the negative grammar")
    elif re.search(r"Running: .*fstar.*--cache_checked_modules", text):
        raise HarnessError(f"{name}: unexpectedly reached verification")
    return {"stage": stage_name, "status": "expected-failure", "returncode": process.returncode}


def c_sources(out, module):
    """Follow generated includes, without linking unrelated output-type namespaces."""
    out = out.resolve()
    todo = [p for p in out.glob("*.c") if p.stem in {
        module, module + "Wrapper", module + "StaticAssertions", module + "AutoStaticAssertions"}
        or p.stem.startswith(module + "_")]
    seen = set()
    sources = set()
    while todo:
        path = todo.pop().resolve()
        if path in seen:
            continue
        seen.add(path)
        if path.suffix == ".c":
            if re.search(r"\bmain\s*\(", path.read_text()):
                raise HarnessError(f"unexpected main in generated module dependency: {path}")
            sources.add(path)
        for name in re.findall(r'#include\s+"([^"]+)"', path.read_text()):
            candidates = (path.parent / name, out / name)
            for header in candidates:
                if header.resolve().is_relative_to(out.resolve()) and header.is_file():
                    todo.append(header)
                    for impl in (header.with_suffix(".c"), out / (header.stem + ".c")):
                        if impl.is_file():
                            todo.append(impl)
                    break
    return sorted(sources)


def macro_trace(stderr, trace):
    """Original handler macros print all their specified diagnostic fields."""
    case = fn = None
    counts = {}
    with trace.open("a") as output:
        for line in stderr.read_text().splitlines():
            if line.startswith("@@CASE "):
                _, case, fn = line.split()
            elif line.startswith("[macro error handler]"):
                if case is None:
                    raise HarnessError("macro diagnostic outside a differential case")
                n = counts.get((case, fn), 0)
                counts[case, fn] = n + 1
                output.write("@@" + json.dumps(dict(case=case, function=fn,
                                                   field=f"macro.{n}", value=line)) + "\n")


def abi_regression(suite, home, stages, work, cc, timeout):
    if suite not in {"root", "modules"}:
        return None
    module = "TestActions1" if suite == "root" else "Point"
    relative = "out.batch-interpret" if suite == "root" else "modules/obj"
    traces = {}
    for api in APIS:
        generated = stages[api][0] / relative
        executable = work / (api + "-abi")
        command([*shlex.split(cc), "-std=c11", "-D_DEFAULT_SOURCE",
                 "-Werror=incompatible-pointer-types", "-Werror=implicit-function-declaration",
                 *(["-DDF_READ"] if suite == "root" else []),
                 f"-I{generated}", f"-I{home / 'src/3d'}",
                 f"-I{home / 'src/3d/prelude/buffer'}", f"-I{HERE}",
                 HERE / "abi_regression.c",
                 *[p for p in c_sources(generated, module) if not p.stem.endswith("Wrapper")],
                 "-o", executable],
                home, stages[api][1], work / (api + "-abi.compile.log"), timeout)
        trace = work / (api + "-abi.trace")
        command([executable], home, dict(stages[api][1], DIFF_TRACE=str(trace)),
                work / (api + "-abi.run.log"), timeout)
        traces[api] = read_trace(trace)
    differences = compare(traces[APIS[0]], traces[APIS[1]])
    write_json(work / "abi-comparison.json", differences)
    if differences:
        raise HarnessError(f"direct ABI regression mismatch: {work / 'abi-comparison.json'}")
    return {"status": "passed", "observations": len(traces[APIS[0]])}


def comparison_modules(suite, stages):
    directory, _, outputs = SUITES[suite]
    for output in outputs:
        roots = {api: stages[api][0] / directory / output for api in APIS}
        for api, root in roots.items():
            if not root.is_dir():
                raise HarnessError(f"{suite}/{output}: missing {api} output")
        modules = {}
        for api, root in roots.items():
            modules[api] = {p.name.removesuffix("Wrapper.h") for p in root.glob("*Wrapper.h")}
            # Exported no-read validators may live in wrapperless dependency modules.
            modules[api].update(p.stem for p in root.glob("*.h")
                                if not p.stem.endswith("Wrapper") and signatures(p, True))
        if modules[APIS[0]] != modules[APIS[1]] or not modules[APIS[0]]:
            raise HarnessError(f"{suite}/{output}: missing or unequal public module sets: {modules}")
        for module in sorted(modules[APIS[0]]):
            yield output, module


def differential(suite, home, stages, work, iterations, timeout, cc, clang, *, modules=None):
    directory = SUITES[suite][0]
    reports = []
    for output, module in (comparison_modules(suite, stages) if modules is None else modules):
        roots = {api: stages[api][0] / directory / output for api in APIS}
        target = work / output / module
        target.mkdir(parents=True)
        src = stages[APIS[0]][0] / directory
        stream = suite in {"extern", "static", "funptr"} or output == "extern.out"
        support, extra, setup = support_for(suite, module, src, roots[APIS[0]])
        if suite == "tcpip" and not stream:
            extra = []
        includes = [roots[APIS[0]], src, src / "src", src / "extern",
                    home / "src/3d", home / "src/3d/prelude" / ("extern" if stream else "buffer")]
        source, required = generate(module, roots[APIS[0]], roots[APIS[1]], includes,
                                    support=support, extern=stream, funptr=suite == "funptr",
                                    copy_setup=setup, clang=clang)
        driver = target / "driver.c"
        driver.write_text(source)
        write_json(target / "required.json", required)
        seed_inputs = seeds(home / "share/everparse/tests/3d/pulse-lowstar-diff/seeds.inc")
        data = generate_cases(required, seed_inputs, iterations)
        (target / "inputs.txt").write_text(data)
        traces = {}
        for api in APIS:
            original = roots[api]
            root = target / (api + "-package")
            root.mkdir()
            for path in original.rglob("*"):
                if path.is_file() and path.suffix in {".c", ".h"}:
                    absolute = [name for name in re.findall(
                        r'#include\s+"([^"]+)"', path.read_text()) if Path(name).is_absolute()]
                    if absolute:
                        raise HarnessError(f"non-relocatable generated includes in {path}: {absolute}")
                    dest = root / path.relative_to(original)
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(path, dest)
            # The driver is literally the same source for both compilations.
            # Included client files come from the reference staging tree and
            # have verified byte equality with the candidate staging tree.
            inc = [root, *includes[1:], HERE]
            executable = target / api
            sources = c_sources(root, module)
            if not sources:
                raise HarnessError(f"{suite}/{output}/{module}: no generated C")
            wraps = ["-Wl,--wrap=" + fn for fn, info in required.items()
                     if info["return"] == "uint64_t" and info["direct"]]
            command([*shlex.split(cc), "-O1", "-g", "-std=c11", "-D_DEFAULT_SOURCE",
                     "-Werror=incompatible-pointer-types", "-Werror=implicit-function-declaration",
                     "-Werror=int-conversion", *[f"-I{p}" for p in inc],
                     str(driver), *sources, *extra, *wraps, "-o", executable],
                    home, stages[api][1], target / (api + ".compile.log"), timeout)
            trace = target / (api + ".trace")
            stdout, stderr = target / (api + ".stdout"), target / (api + ".stderr")
            with (target / "inputs.txt").open() as inp, stdout.open("w") as out, stderr.open("w") as err:
                process = run_process([str(executable)], stdin=inp, stdout=out, stderr=err,
                                      env=dict(stages[api][1], DIFF_TRACE=str(trace)),
                                      timeout=timeout)
            if process.returncode:
                raise HarnessError(f"{suite}/{output}/{module}: {api} driver failed "
                                   f"({process.returncode}); see {stderr}")
            macro_trace(stderr, trace)
            traces[api] = read_trace(trace)
            check_executed(traces[api], data, required)
        differences = compare(traces[APIS[0]], traces[APIS[1]])
        accounting = coverage(traces[APIS[0]], required)
        write_json(target / "comparison.json", {"differences": differences, "coverage": accounting})
        missing = {fn: item for fn, item in accounting.items()
                   if item["missing_fields"] or not item["failure"] or
                   (item["success"] != 0 if item.get("negative_only") else not item["success"])}
        reports.append({"output": output, "module": module, "coverage": accounting,
                        "differences": differences, "missing_coverage": missing})
    return reports


def job_result(action):
    try:
        return {"status": "passed", "value": action()}
    except (HarnessError, subprocess.TimeoutExpired, OSError) as error:
        return {"status": "blocked", "error": str(error)}


def build_target(suite, target, api, home, tree, env, work, timeout):
    build_suite(suite, home, tree, env, work / f"{api}.{target}.build.log",
                timeout, api=api, target=target)
    if suite == "root" and target == "elf-test":
        command([tree / "out.elf/elf-test", sys.executable], home, env,
                work / (api + ".elf-client.log"), timeout)


def run_suites(selected, home, stages, work, args, report, budget):
    jobs = []
    for suite in selected:
        result = {"status": "running", "builds": {}, "build_jobs": {}}
        report["suites"][suite] = result
        suite_work = work / "results" / suite
        suite_work.mkdir(parents=True)
        for api, (tree, env) in stages.items():
            targets = NEGATIVES if suite == "negative" else SUITES[suite][1]
            result["build_jobs"][api] = {target: {"status": "pending"} for target in targets}
            if suite == "negative":
                (suite_work / api).mkdir()
            for target in targets:
                action = (partial(negative, target, home, tree, env, suite_work / api, args.timeout)
                          if suite == "negative" else
                          partial(build_target, suite, target, api, home, tree, env,
                                  suite_work, args.timeout))
                jobs.append(((suite, api, target), partial(job_result, action)))
    write_json(work / "report.json", report)
    for (suite, api, target), result in run_jobs(jobs, budget):
        report["suites"][suite]["build_jobs"][api][target] = result
        print(f"{suite}/{api}/{target}: {result['status']}", flush=True)
        write_json(work / "report.json", report)

    comparisons = []
    for suite in selected:
        result = report["suites"][suite]
        errors = []
        for api in APIS:
            builds = result["build_jobs"][api]
            blocked = [item["error"] for item in builds.values() if item["status"] != "passed"]
            result["builds"][api] = (
                {"status": "blocked", "error": "; ".join(blocked)} if blocked else
                {name: item["value"] for name, item in builds.items()} if suite == "negative" else
                "passed")
            errors.extend(blocked)
        if errors:
            result.update(status="blocked", error="; ".join(errors))
            continue
        if suite == "negative":
            result["status"] = "passed"
            continue
        suite_work = work / "results" / suite
        try:
            modules = list(comparison_modules(suite, stages))
        except (HarnessError, OSError) as error:
            result.update(status="blocked", error=str(error))
            continue
        result.update(abi=None, comparisons=[])
        if suite in {"root", "modules"}:
            action = partial(abi_regression, suite, home, stages, suite_work, args.cc, args.timeout)
            comparisons.append(((suite, "abi"), partial(job_result, action)))
        for output, module in modules:
            action = partial(differential, suite, home, stages, suite_work,
                             args.iterations, args.timeout, args.cc, args.clang,
                             modules=[(output, module)])
            comparisons.append(((suite, f"{output}/{module}"), partial(job_result, action)))
    for (suite, name), outcome in run_jobs(comparisons, budget):
        result = report["suites"][suite]
        if outcome["status"] != "passed":
            result["status"] = "blocked"
            result.setdefault("comparison_errors", {})[name] = outcome["error"]
            result["error"] = "; ".join(
                result["comparison_errors"][key] for key in sorted(result["comparison_errors"]))
        elif name == "abi":
            result["abi"] = outcome["value"]
        else:
            result["comparisons"].extend(outcome["value"])
            result["comparisons"].sort(key=lambda item: (item["output"], item["module"]))
        write_json(work / "report.json", report)
    for suite in selected:
        result = report["suites"][suite]
        if result["status"] == "running":
            result["status"] = "failed" if any(
                item["differences"] or item["missing_coverage"]
                for item in result["comparisons"]) else "passed"
        print(f"{suite}: {result['status']}" + (": " + result["error"] if "error" in result else ""),
              flush=True)
    write_json(work / "report.json", report)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--home", type=Path, default=HERE.parents[3])
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--inventory-only", action="store_true")
    parser.add_argument("--suite", action="append", choices=[*SUITES, "negative"])
    parser.add_argument("--iterations", type=int, default=256)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--jobs", type=int,
                        help="maximum concurrent jobs (default: make jobserver/CPU limit, else 1)")
    parser.add_argument("--cc", default=os.environ.get("CC", "cc"))
    parser.add_argument("--clang", default="clang")
    parser.add_argument("--clean", action="store_true")
    args = parser.parse_args(argv)
    build = HERE / "_build"
    if args.clean:
        outputs = (build, HERE / "adapter-tests/_build")
        for output in outputs:
            if output.is_symlink() or not output.resolve().is_relative_to(HERE):
                raise HarnessError(f"refusing to clean symlinked build directory: {output}")
        for output in outputs:
            if output.exists():
                shutil.rmtree(output)
        return 0
    if args.iterations < 0 or args.timeout <= 0 or (args.jobs is not None and args.jobs <= 0):
        parser.error("iterations must be nonnegative; timeout and jobs must be positive")
    home = args.home.resolve()
    listing = inventory(home, args.manifest)
    build.mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="run-", dir=build))
    write_json(work / "inventory.json", listing)
    print(f"Artifacts: {work}", flush=True)
    if args.inventory_only:
        print(f"{len(listing['files'])} corpus files")
        return 0
    selected = list(dict.fromkeys(args.suite)) if args.suite else [*SUITES, "negative"]
    report = {"status": "running", "partial": args.suite is not None, "suites": {},
              "inventory": str(work / "inventory.json"),
              "generator_sha256": digest(home / "bin/3d.exe")}
    stages = {api: stage(home, work, api, listing) for api in APIS}
    with JobBudget(args.jobs) as budget:
        report["jobs"] = budget.jobs
        report["jobserver"] = budget.reader is not None
        print(f"Concurrency: at most {budget.jobs} jobs"
              + (" using GNU Make jobserver" if report["jobserver"] else ""), flush=True)
        run_suites(selected, home, stages, work, args, report, budget)
    # Every original source is rechecked after the run, including support files.
    changed = [r["path"] for r in listing["files"]
               if digest(home / CORPUS / r["path"]) != r["sha256"]]
    report["source_changes"] = changed
    report["generator_changed"] = report["generator_sha256"] != digest(home / "bin/3d.exe")
    report["files"] = [
        {"path": row["path"], "category": row["category"],
         "coverage": {suite: report["suites"].get(
             "negative" if suite.startswith("negative:") else suite, {"status": "not-run"})["status"]
                      for suite in row["suites"]}}
        for row in listing["files"]]
    report["generation_invocations"] = {
        api: [json.loads(p.read_text()) for p in sorted((work / api / "invocations").glob("*.json"))]
        for api in APIS}
    report["status"] = ("passed" if not changed and not report["generator_changed"] and not report["partial"] and
                        all(r["status"] == "passed" for r in report["suites"].values())
                        else "incomplete" if report["partial"] else "failed")
    write_json(work / "report.json", report)
    print(f"Compatibility gate: {report['status']}; {work / 'report.json'}")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (HarnessError, OSError, ValueError) as error:
        print(f"pulse-lowstar-diff-tests: {error}", file=sys.stderr)
        sys.exit(2)

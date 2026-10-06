#!/usr/bin/env python3
"""Executed via each isolated proxy installation's bin/3d.exe."""

import json
import os
from pathlib import Path
import subprocess
import sys
import time


def selected_args(args, api):
    if "--pulse" in args:
        raise ValueError("removed --pulse option in original recipe")
    for i, arg in enumerate(args):
        if arg == "--api" and (i + 1 == len(args) or args[i + 1] != api):
            raise ValueError("recipe attempts to override differential API")
        if arg.startswith("--api=") and arg != "--api=" + api:
            raise ValueError("recipe attempts to override differential API")
    return args + ["--api", api]


def main():
    config = json.loads((Path(sys.argv[0]).resolve().parent / "proxy.json").read_text())
    args = selected_args(sys.argv[1:], config["api"])
    env = dict(os.environ, EVERPARSE_HOME=config["home"])
    record = {"api": config["api"], "cwd": os.getcwd(), "args": args}
    log = Path(config["log"]) / (str(time.time_ns()) + "-" + str(os.getpid()) + ".json")
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(json.dumps(dict(record, status="started")))
    result = subprocess.run([str(Path(config["home"]) / "bin/3d.exe"), *args], env=env)
    log.write_text(json.dumps(dict(record, status="finished", returncode=result.returncode)))
    return result.returncode


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Compile and run the libc++ tests adapted to the custom mutex classes."""

import argparse
import os
from pathlib import Path
import shlex
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent


def run_step(command, timeout):
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as error:
        print(f"  {shlex.join(command)}\n  {error}", flush=True)
        return False
    if result.returncode:
        print(f"  {shlex.join(command)}\n{result.stdout}{result.stderr}", flush=True)
        return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cxx", default=os.environ.get("CXX", "clang++"),
                        help="compiler executable (default: CXX or clang++)")
    parser.add_argument("--stdlib", choices=("libstdc++", "libc++", "default"),
                        default="libstdc++",
                        help="standard library; use default with GCC")
    parser.add_argument("--filter", default="", metavar="TEXT",
                        help="run only tests whose relative path contains TEXT")
    args = parser.parse_args()

    tests = sorted(path for path in ROOT.glob("*/*.cpp")
                   if args.filter in path.relative_to(ROOT).as_posix())
    if not tests:
        parser.error("no tests match the filter")

    flags = ["-std=c++17", "-pthread", "-g", "-O1", "-UNDEBUG",
             "-I" + str(ROOT / "support")]
    if args.stdlib != "default":
        flags.append("-stdlib=" + args.stdlib)

    passed = 0
    with tempfile.TemporaryDirectory(prefix="brick-mutex-tests-") as build_dir:
        for index, source in enumerate(tests):
            name = source.relative_to(ROOT).as_posix()
            command = [args.cxx, *flags, str(source)]
            compile_only = source.name.endswith(".compile.pass.cpp")
            executable = Path(build_dir) / str(index)
            command += ["-fsyntax-only"] if compile_only else ["-o", str(executable)]
            if not run_step(command, timeout=60):
                print(f"FAIL (compile) {name}", flush=True)
                continue
            if not compile_only and not run_step([str(executable)], timeout=20):
                print(f"FAIL (run) {name}", flush=True)
                continue
            passed += 1
            print(f"PASS {name}", flush=True)

    print(f"{passed}/{len(tests)} passed ({args.cxx}, {args.stdlib})", flush=True)
    return 0 if passed == len(tests) else 1


if __name__ == "__main__":
    raise SystemExit(main())

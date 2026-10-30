#!/usr/bin/env python3
# Copyright 2026 The mathdb-lean Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#     https://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Compile every statement, and refuse one that rests on anything but Lean's own axioms.

`lake env lean` exits 0 on a `sorry` -- it is a warning -- so a compile check alone
passes a statement whose `Problem.Target` is a `sorry` underneath, or a module that
proves a helper by `sorry`. Each module is therefore compiled with
`#print axioms Problem.Target` appended, and it passes only if

* it compiles,
* nothing in it uses `sorry`, and
* `Problem.Target` depends on no axiom beyond propext, Classical.choice and Quot.sound.

Run from the repository root after `lake build`:

    python check_statements.py problems/1/E1.lean ...   # these modules
    python check_statements.py --shard 0/8              # one eighth of all of them

Exit status is 0 only if every module passed.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DEPENDS = re.compile(r"'Problem\.Target' depends on axioms: \[([^\]]*)\]")
NONE = "'Problem.Target' does not depend on any axioms"
SORRY = re.compile(r"declaration uses .sorry.")


def modules(shard: str | None) -> list[Path]:
    found = sorted(ROOT.glob("problems/*/*.lean"), key=lambda p: p.relative_to(ROOT).as_posix())
    if not shard:
        return found
    index, count = (int(x) for x in shard.split("/"))
    return [path for n, path in enumerate(found, 1) if n % count == index]


def check(module: Path, lake: str) -> list[str]:
    """What is wrong with this module, or nothing."""
    text = module.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory() as temp:
        probe = Path(temp) / module.name
        probe.write_text(text.rstrip("\n") + "\n\n#print axioms Problem.Target\n",
                         encoding="utf-8", newline="\n")
        run = subprocess.run([lake, "env", "lean", "-DautoImplicit=false",
                              "-DrelaxedAutoImplicit=false", str(probe)],
                             cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
                             errors="replace")
    out = run.stdout + run.stderr
    if run.returncode != 0:
        return ["does not compile:\n" + out.strip()[-3000:]]
    faults = []
    if SORRY.search(out):
        faults.append("a declaration uses sorry")
    found = DEPENDS.search(out)
    if found:
        extra = sorted({a.strip() for a in found.group(1).split(",") if a.strip()} - ALLOWED)
        if extra:
            faults.append("Problem.Target depends on %s" % ", ".join(extra))
    elif NONE not in out:
        faults.append("no axiom report for Problem.Target:\n" + out.strip()[-1000:])
    return faults


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("modules", nargs="*", help="module files; all of them if none")
    parser.add_argument("--shard", help="i/n: the modules whose 1-based position is i mod n")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args(argv)
    chosen = [Path(m).resolve() for m in args.modules] or modules(args.shard)
    failed = 0
    for module in chosen:
        faults = check(module, args.lake)
        if faults:
            failed += 1
            where = module.relative_to(ROOT).as_posix()
            for fault in faults:
                print("::error file=%s::%s" % (where, fault.splitlines()[0]))
                print(fault)
    print("%d module(s), %d failed" % (len(chosen), failed))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

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
"""Check this repository against its own release record.

Every `problems/<problem>/problem.toml` is derived from `benchmark.json`, so the
same fact is written down twice. That is acceptable only while something can tell
you the two still agree, so this re-derives each field and compares rather than
asking you to trust that nobody edited one side. It also hashes every module
against the digest the release recorded, which is the check that matters: the
module is the artifact, and an edited problem must be visible even when every
sidecar still agrees with itself.

    python verify.py                 # every problem
    python verify.py 1 391594

Exit status is 0 only if every check passed. Needs Python 3.11+ for tomllib.
"""
from __future__ import annotations

import hashlib
import json
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROBLEMS = ROOT / "problems"


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def main(argv: list[str]) -> int:
    manifest = json.loads((ROOT / "benchmark.json").read_text(encoding="utf-8"))
    released = manifest["problems"]
    recorded = manifest["report"]["tasks"]
    under_review = set(manifest.get("under_review") or ())
    toolchain = manifest["toolchain"]

    faults: list[str] = []
    folders = sorted(p for p in PROBLEMS.iterdir() if p.is_dir())
    wanted = [PROBLEMS / name for name in argv] if argv else folders

    # Every released task must be reachable from exactly one folder, and no folder
    # may carry a module the release does not list. A regrouping that dropped or
    # duplicated a task would otherwise pass every per-file check.
    seen: dict[str, str] = {}
    for folder in folders:
        for module in sorted(folder.glob("*.lean")):
            task_id = module.stem
            if task_id in seen:
                faults.append("%s: also in problems/%s" % (task_id, seen[task_id]))
            seen[task_id] = folder.name
            if task_id not in released:
                faults.append("%s: a module the release does not list" % task_id)
    for task_id in sorted(set(released) - set(seen)):
        faults.append("%s: released but no module in any folder" % task_id)

    for folder in wanted:
        side = folder / "problem.toml"
        if not side.is_file():
            faults.append("%s: no problem.toml" % folder.name)
            continue
        try:
            held = tomllib.loads(side.read_text(encoding="utf-8"))
        except tomllib.TOMLDecodeError as error:
            faults.append("%s: problem.toml does not parse (%s)" % (folder.name, error))
            continue

        number = held.get("mathdb_number")
        if type(number) is not int or number <= 0 or folder.name != str(number):
            faults.append("%s: folder must match its positive mathdb_number, got %r"
                          % (folder.name, number))

        entries = held.get("task") or []
        modules = sorted(p.stem for p in folder.glob("*.lean"))
        if sorted(e.get("id", "") for e in entries) != modules:
            faults.append("%s: toml lists %s, folder holds %s"
                          % (folder.name, [e.get("id") for e in entries], modules))
        if held.get("tasks") != len(entries):
            faults.append("%s: tasks = %r but %d task entries"
                          % (folder.name, held.get("tasks"), len(entries)))

        for entry in entries:
            task_id = entry.get("id", "")
            task = released.get(task_id)
            if task is None:
                continue  # already reported above
            if task["question_id"] != held.get("problem_id"):
                faults.append("%s: %s belongs to %s"
                              % (folder.name, task_id, task["question_id"]))

            module = folder / entry.get("file", "%s.lean" % task_id)
            if not module.is_file():
                faults.append("%s: %s names a file that is not here" % (folder.name, task_id))
                continue
            got = digest(module.read_text(encoding="utf-8"))
            if got != task["target_hash"]:
                faults.append("%s: %s hashes to %s, release recorded %s"
                              % (folder.name, task_id, got, task["target_hash"]))

            evidence = recorded.get(task_id, {})
            for where, key, expected in (
                (held, "mathdb_number", task.get("mathdb_number")),
                (entry, "module", task.get("module")),
                (entry, "shape", task.get("shape")),
                (entry, "track", task.get("track")),
                (entry, "part", task.get("part")),
                (entry, "pair_id", task.get("pair_id")),
                (entry, "statement_id", task.get("statement_id")),
                (entry.get("environment", {}), "lean", toolchain.get("lean")),
                (entry.get("environment", {}), "mathlib_rev", toolchain.get("mathlib_rev")),
                (entry.get("evidence", {}), "target_hash", task.get("target_hash")),
                (entry.get("evidence", {}), "conversion_hash", evidence.get("conversion_hash")),
                (entry.get("evidence", {}), "semantic_anchor", evidence.get("semantic_anchor")),
            ):
                value = where.get(key)
                if not expected and value is None:
                    continue  # an empty value is omitted rather than written as ""
                if value != expected:
                    faults.append("%s: %s.%s is %r, release says %r"
                                  % (folder.name, task_id, key, value, expected))

            read = entry.get("evidence", {}).get("reviewed_by_a_person")
            if read is not (task_id not in under_review):
                faults.append("%s: %s reviewed_by_a_person is %r, release says %r"
                              % (folder.name, task_id, read, task_id not in under_review))

        # A pair is whole or it is not published. Half a pair tells a solver which
        # direction is true, so a folder holding one side of a pair_id whose other
        # side the release also assigns to it is a defect, not a smaller benchmark.
        for entry in entries:
            pair = entry.get("pair_id")
            if not pair:
                continue
            here = {e.get("id") for e in entries if e.get("pair_id") == pair}
            whole = {t for t, v in released.items() if v.get("pair_id") == pair}
            if here != whole:
                faults.append("%s: pair %s is split -- here %s, released %s"
                              % (folder.name, pair, sorted(here), sorted(whole)))

    # The MathDB block, if the manifest carries one. It states the same number in
    # two places -- beside each obligation and once per problem -- so the two have
    # to be checked against each other, and the file's own fingerprint has to still
    # be the one it claims, or a citation to `manifest_hash` identifies nothing.
    held_mathdb = manifest.get("mathdb")
    if held_mathdb:
        entries = held_mathdb.get("problems") or {}
        for task_id, task in released.items():
            entry = entries.get(task["question_id"])
            if entry is None:
                faults.append("mathdb: %s names no state for %s"
                              % (task_id, task["question_id"]))
                continue
            resolved = entry.get("state") in {"resolved", "dev_only"}
            if ("mathdb_number" in task) is not resolved:
                faults.append("mathdb: %s carries a number but its problem is %r"
                              % (task_id, entry.get("state")) if "mathdb_number" in task
                              else "mathdb: %s has no number but its problem is resolved" % task_id)
            elif resolved and task["mathdb_number"] != entry["mathdb_number"]:
                faults.append("mathdb: %s says %r, its problem says %r"
                              % (task_id, task["mathdb_number"], entry["mathdb_number"]))

        counted = {"resolved": 0, "dev_only": 0}
        for ref, entry in entries.items():
            state = entry.get("state")
            if state not in counted:
                faults.append("mathdb: %s has unknown state %r" % (ref, state))
                continue
            counted[state] += 1
            where = held_mathdb.get("by_mathdb_number", {}).get(str(entry["mathdb_number"]))
            if where != ref:
                faults.append("mathdb: the reverse map sends %s to %r, not %s"
                              % (entry["mathdb_number"], where, ref))
        for state, n in counted.items():
            if held_mathdb.get("counts", {}).get(state) != n:
                faults.append("mathdb: counts say %s=%r, the entries hold %d"
                              % (state, held_mathdb.get("counts", {}).get(state), n))

    release = manifest["report"]["release"]
    expected_hash = release.pop("manifest_hash", None)
    manifest_hash = hashlib.sha256(
        json.dumps(manifest, sort_keys=True, ensure_ascii=False).encode("utf-8")
    ).hexdigest()[:16]
    if manifest_hash != expected_hash:
        faults.append("manifest_hash: computed %s, release says %r"
                      % (manifest_hash, expected_hash))

    for fault in faults[:40]:
        print("  %s" % fault)
    if len(faults) > 40:
        print("  ... and %d more" % (len(faults) - 40))
    print()
    print("%d problem(s) checked, %d module(s), %d fault(s)"
          % (len(wanted), len(seen), len(faults)))
    return 1 if faults else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

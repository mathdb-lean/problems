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
    python verify.py 1 391594 wikipedia-collatzconjecture

Exit status is 0 only if every check passed. Needs Python 3.11+ for tomllib.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROBLEMS = ROOT / "problems"


def check_projects(environments: dict, sources: list[Path], faults: list[str]) -> int:
    """Each source directory's Lean project against the environment the manifest states.

    A source is checked in the environment its own upstream pins, and the source
    directory is that environment's Lean project: `lean-toolchain` and
    `lake-manifest.json` beside the problem folders. The manifest records the
    toolchain every task of the source was checked against; a project that pins
    something else would compile the problems somewhere they were never checked.
    """
    held = {src.name for src in sources}
    for name in sorted(set(environments) ^ held):
        faults.append("environments: %s is %s" % (name, "stated but has no source directory"
                      if name in environments else "a source directory with no environment"))
    checked = 0
    for src in sources:
        environment = environments.get(src.name) or {}
        toolchain = environment.get("toolchain") or {}
        pinned = src / "lean-toolchain"
        if not pinned.is_file():
            faults.append("problems/%s: no lean-toolchain" % src.name)
        elif pinned.read_text(encoding="utf-8").strip() != toolchain.get("lean"):
            faults.append("problems/%s: lean-toolchain is %s, the manifest says %r"
                          % (src.name, pinned.read_text(encoding="utf-8").strip(), toolchain.get("lean")))
        lake = src / "lake-manifest.json"
        if not lake.is_file() or not (src / "lakefile.toml").is_file():
            faults.append("problems/%s: no lakefile.toml and lake-manifest.json" % src.name)
            continue
        packages = json.loads(lake.read_text(encoding="utf-8")).get("packages") or []
        mathlib = next((p.get("rev") for p in packages if p.get("name") == "mathlib"), None)
        if mathlib != toolchain.get("mathlib_rev"):
            faults.append("problems/%s: lake-manifest.json pins mathlib %r, the manifest says %r"
                          % (src.name, mathlib, toolchain.get("mathlib_rev")))
        checked += 1
    return checked


def slug(problem_id: str) -> str:
    """`wikipedia:CollatzConjecture` -> `wikipedia-collatzconjecture`.

    The folder name for a problem MathDB has no number for. A colon is not a
    path character on Windows, and this repository has to clone there.
    """
    return re.sub(r"[^A-Za-z0-9]+", "-", problem_id).strip("-").lower()


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def label(folder: Path) -> str:
    """`formal-conjectures/391455`: how a problem folder is named in a fault."""
    return folder.relative_to(PROBLEMS).as_posix()


def main(argv: list[str]) -> int:
    manifest = json.loads((ROOT / "benchmark.json").read_text(encoding="utf-8"))
    released = manifest["problems"]
    recorded = manifest["report"]["tasks"]
    under_review = set(manifest.get("under_review") or ())
    environments = manifest.get("environments") or {}

    faults: list[str] = []
    # `problems/<source>/<folder>/`: one directory per source, one folder per
    # problem inside it. A problem folder directly under `problems/` is the layout
    # published before 2026-10-09 and is a fault now, not a second place to look.
    sources = sorted(p for p in PROBLEMS.iterdir() if p.is_dir() and not p.name.startswith("."))
    for src in sources:
        if (src / "problem.toml").is_file() or any(src.glob("*.lean")):
            faults.append("problems/%s: a problem folder outside any source directory" % src.name)
    # A source directory is also a Lean project, so `.lake/` and the like may sit
    # beside the problem folders after a build; they are not problems.
    folders = sorted(p for src in sources for p in src.iterdir()
                     if p.is_dir() and not p.name.startswith("."))
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
            seen[task_id] = label(folder)
            if task_id not in released:
                faults.append("%s: a module the release does not list" % task_id)
    for task_id in sorted(set(released) - set(seen)):
        faults.append("%s: released but no module in any folder" % task_id)

    for folder in wanted:
        side = folder / "problem.toml"
        if not side.is_file():
            faults.append("%s: no problem.toml" % label(folder))
            continue
        try:
            held = tomllib.loads(side.read_text(encoding="utf-8"))
        except tomllib.TOMLDecodeError as error:
            faults.append("%s: problem.toml does not parse (%s)" % (label(folder), error))
            continue

        # A folder is addressed by MathDB's number when MathDB has one, and by the
        # id its source gives the problem when it does not. Both are required to
        # be exact; what is not required is that every collection have a MathDB
        # number, because most of them are not Erdos problems and MathDB holds no
        # record keyed to them. Minting a local number to fill the gap would make
        # an address out of something nobody issued.
        number = held.get("mathdb_number")
        if number is None:
            expected = slug(held.get("problem_id") or "")
            if folder.name != expected:
                faults.append("%s: no mathdb_number, so the folder must be %r"
                              % (label(folder), expected))
        elif type(number) is not int or number <= 0 or folder.name != str(number):
            faults.append("%s: folder must match its positive mathdb_number, got %r"
                          % (label(folder), number))
        # ... and it sits under the directory of the source that posed it.
        source_name = (held.get("source") or {}).get("name") or ""
        if folder.parent.name != source_name:
            faults.append("%s: its source is %r, so it belongs under problems/%s/"
                          % (label(folder), source_name, source_name))

        entries = held.get("task") or []
        modules = sorted(p.stem for p in folder.glob("*.lean"))
        if sorted(e.get("id", "") for e in entries) != modules:
            faults.append("%s: toml lists %s, folder holds %s"
                          % (label(folder), [e.get("id") for e in entries], modules))
        if held.get("tasks") != len(entries):
            faults.append("%s: tasks = %r but %d task entries"
                          % (label(folder), held.get("tasks"), len(entries)))

        for entry in entries:
            task_id = entry.get("id", "")
            task = released.get(task_id)
            if task is None:
                continue  # already reported above
            if task["question_id"] != held.get("problem_id"):
                faults.append("%s: %s belongs to %s"
                              % (label(folder), task_id, task["question_id"]))

            module = folder / entry.get("file", "%s.lean" % task_id)
            if not module.is_file():
                faults.append("%s: %s names a file that is not here" % (label(folder), task_id))
                continue
            got = digest(module.read_text(encoding="utf-8"))
            if got != task["target_hash"]:
                faults.append("%s: %s hashes to %s, release recorded %s"
                              % (label(folder), task_id, got, task["target_hash"]))

            evidence = recorded.get(task_id, {})
            toolchain = (environments.get(task.get("source") or "") or {}).get("toolchain") or {}
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
                                  % (label(folder), task_id, key, value, expected))

            read = entry.get("evidence", {}).get("reviewed_by_a_person")
            if read is not (task_id not in under_review):
                faults.append("%s: %s reviewed_by_a_person is %r, release says %r"
                              % (label(folder), task_id, read, task_id not in under_review))

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
                              % (label(folder), pair, sorted(here), sorted(whole)))

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

        # Five states, and no two of them mean the same thing. MathDB has a record;
        # MathDB answered that it has none; the lookup never got an answer, which
        # is not evidence of absence; the record was created here rather than
        # found; and the problem is not an Erdos problem, so the lookup -- which
        # keys on the Erdos number -- had nothing to ask about. Collapsing any two
        # is how a count stops meaning anything: recording rate-limited requests
        # as absences once turned 311 problems MathDB does have into problems it
        # does not.
        counted = dict.fromkeys(
            ("resolved", "dev_only", "absent_from_mathdb", "unresolved",
             "not_an_erdos_problem"), 0)
        for ref, entry in entries.items():
            state = entry.get("state")
            if state not in counted:
                faults.append("mathdb: %s has unknown state %r" % (ref, state))
                continue
            counted[state] += 1
            if "mathdb_number" not in entry:
                continue
            where = held_mathdb.get("by_mathdb_number", {}).get(str(entry["mathdb_number"]))
            if where != ref:
                faults.append("mathdb: the reverse map sends %s to %r, not %s"
                              % (entry["mathdb_number"], where, ref))
        for state, n in counted.items():
            stated = held_mathdb.get("counts", {}).get(state, 0)
            if stated != n:
                faults.append("mathdb: counts say %s=%r, the entries hold %d"
                              % (state, stated, n))

    # The manifest's own fingerprint. A single release writes it under
    # `report.release`; a distribution assembled from several releases writes it
    # under `report.distribution`, because there is no one release to attribute
    # it to. Both are excluded from the digest, and whichever is present is the
    # value a citation identifies this content by.
    report = manifest["report"]
    home = "distribution" if "distribution" in report else "release"
    expected_hash = report[home].pop("manifest_hash", None)
    for other in ("distribution", "release"):
        if other != home and other in report:
            report[other].pop("manifest_hash", None)
    manifest_hash = hashlib.sha256(
        json.dumps(manifest, sort_keys=True, ensure_ascii=False).encode("utf-8")
    ).hexdigest()[:16]
    if manifest_hash != expected_hash:
        faults.append("manifest_hash: computed %s, %s says %r"
                      % (manifest_hash, home, expected_hash))

    projects = check_projects(environments, sources, faults)

    for fault in faults[:40]:
        print("  %s" % fault)
    if len(faults) > 40:
        print("  ... and %d more" % (len(faults) - 40))
    print()
    print("%d problem(s) checked, %d module(s), %d Lean project(s), %d fault(s)"
          % (len(wanted), len(seen), projects, len(faults)))
    return 1 if faults else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

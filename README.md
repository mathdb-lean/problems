# mathdb-lean problems

Mathematical problems formalized in Lean 4, with the pinned project they compile
against. **One folder is one problem.** Inside it are that problem's proof
obligations and a `problem.toml` describing them.

```
problems/
  erdos-1/
    E1.lean                  one proof obligation
    problem.toml
  erdos-1002/
    E1002_prove.lean         the two directions of one open question,
    E1002_refute.lean        published together
    problem.toml
  erdos-1209/
    E1209_parts_i.lean       nine obligations: three parts, one of them
    E1209_parts_ii.lean      in four sub-parts, most as prove/refute pairs
    …
    problem.toml
```

Currently **704 problems / 1106 obligations**, all from the
[Erdős problems](https://www.erdosproblems.com/) collection. Nothing in the layout
is specific to it: a folder is named `<collection>-<id>` after the id the
**source** gives the problem — `erdos-1209` is Erdős problem 1209 — so another
collection's problems sit beside these without rearranging anything.

That source id is the problem's permanent identity here, which is why it is the
folder name: a link, a bookmark or a submission path keeps working. An external
reference, including a MathDB key, is recorded as a field once it is known rather
than used as the address — a reference that may be assigned later cannot be an
address that must not change.

Each obligation is a frozen `Problem.Target` — a proposition stated in Lean, with
no proof. A grader elaborates one module at a time against the project in
`project/` and checks what it denotes.

## Read this before using it as a benchmark

**No problem here has been read by a person.** Every obligation is marked
`reviewed_by_a_person = false`: machine checks passed, no human has confirmed that
the Lean states the mathematics the source poses.

The release's `release_id` is `erdos-reviewed`. That is the name of the *admission
policy*, **not** a claim that anything was reviewed. The release record says so
itself:

```
"note": "1106 of 1106 have not been read by a person yet"
```

The name is kept as published rather than corrected after the fact, because the
record is the record. Read it as "admitted by the erdos-reviewed policy".

So a faithfulness error in any individual problem is possible, and finding one is
useful. What *is* machine-established is below.

## What was established by machine

Every published obligation:

- **elaborates** against the pinned project (Lean `v4.33.1`, mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`);
- **reaches only** `propext`, `Classical.choice`, `Quot.sound` in its axiom
  closure — no `sorryAx`, no added axiom;
- **matches the interface** an obligation of its shape claims to have;
- **survived a tactic suite** aimed at closing the goal without doing the
  mathematics.

40 further candidates were **omitted**, each listed with its reason in
`benchmark.json.report.omitted` — `compile is failed or its evidence is
stale/missing`, `dependencies is failed …`. They are named rather than dropped
silently, so the gap between 1146 and 1106 is accounted for.

## What is in it

| | |
|---|---|
| problems | 704 |
| obligations | 1106 |
| obligations per problem | 415 problems have 1, 237 have 2, 52 have 3–9 |
| track | 672 open, 434 solved |
| shape | 345 `decide`, 300 `prove`, 300 `refute`, 142 `proof`, 19 `value` |
| source | [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at `e04cc601840dd7a37f89b821a67f3a9e3c38d9c3` |

`track` says whether the problem is **solved in the literature** — a fact about
mathematics, not about this repository. `source_has_lean_proof`, in each module's
metadata, is a different claim and is false for almost every problem, because the
upstream corpus is a statement repository.

The 300 `prove` and 300 `refute` modules are **300 complete pairs**: the two
directions of one open question, either of which settles it. A pair always sits in
one folder, because half a pair tells a solver which direction is true. `verify.py`
refuses a split pair.

## `problem.toml`

One per folder, generated from `benchmark.json`. It carries the problem's identity
and prose, its upstream source, and one `[[task]]` entry per obligation:

```toml
problem_id = "erdos:1002"
collection = "erdos"
tasks = 2
reviewed_by_a_person = false
prose = "…the question, as the source states it…"

[source]
name = "formal-conjectures"
revision = "e04cc601840dd7a37f89b821a67f3a9e3c38d9c3"
file = "FormalConjectures/ErdosProblems/1002.lean"

[[task]]
id = "E1002_prove"
file = "E1002_prove.lean"
shape = "prove"
track = "open"
pair_id = "…"
  [task.environment]
  lean = "leanprover/lean4:v4.33.1"
  mathlib_rev = "0df444a360eaa60ab8c11dca51a86af692955474"
  [task.evidence]
  target_hash = "…"
  semantic_anchor = "…"
  reviewed_by_a_person = false
```

The environment pin sits **inside each task**, not once at the root. Today all
1106 share one Lean and one mathlib revision; an obligation re-verified later
against a different one records that in its own entry, and nothing about the other
problems changes.

## Layout

```
problems/<collection>-<id>/   one folder per problem: its modules and problem.toml
project/                      the pinned Lean project the modules compile against
  lakefile.toml  lean-toolchain  lake-manifest.json
  lean/MathdbUtil*            the statement-support library every module imports
  lean/MathdbMathlib*         vendored Mathlib additions it was written against
benchmark.json                the release record
verify.py                     checks this repository against that record
```

Four things, and the root says which is which: the problems, the project to
compile them against, the record of what was released, and the checker for it.

The modules are deliberately **not** a `lean_lib` in `project/lakefile.toml`. They
are the benchmark: each is elaborated on its own, against the built project, never
as part of it.

## Using it

```sh
cd project
lake exe cache get      # mathlib binaries, optional but much faster
lake build              # builds MathdbUtil and MathdbMathlib
cd ..
python verify.py        # every module still hashes to what the release recorded
```

Then point a grader's `project_dir` at `project/` and its problem directory at
`problems/`. A submission replaces the `sorry` in a copy of one module; the grader
elaborates the result and compares what `Problem.Target` denotes against that
task's `semantic_anchor`.

A grader that expects all problems flat in one directory needs to walk folders
instead — `glob("problems/*/*.lean")` rather than `glob("*.lean")`. The file stem
is still the obligation's id, which is what submission filenames and result
directories key on.

## Verifying the release against this repository

`python verify.py` does all of it, and exits non-zero on any mismatch:

- every module hashes to the `target_hash` the release recorded (1106 of 1106);
- every `problem.toml` field re-derives from `benchmark.json`;
- every released obligation appears in exactly one folder, and no folder holds a
  module the release does not list;
- no `pair_id` is split across or out of a folder.

The environment is pinned by content too:
`benchmark.json.report.release.environment_hash` is derived from the toolchain, the
mathlib revision, and a hash over `project/lean/MathdbUtil*` and
`project/lean/MathdbMathlib*` — all three are in this repository, so the pin is
reconstructible here.

## Provenance and license

Apache 2.0 — see `LICENSE`. `NOTICE` states what was taken from formal-conjectures
and how it was changed, as Apache 2.0 section 4(b) requires:
`project/lean/MathdbUtil*` and `project/lean/MathdbMathlib*` are its
`FormalConjecturesUtil/` and `FormalConjecturesForMathlib/`, renamed. Upstream's
author list and the Lean pins are carried over unchanged.

This repository holds **releases**. The library that produces them — the records,
the conversion and review evidence, the per-problem history — is maintained
separately; nothing here is a source of truth, and nothing here should be edited by
hand. To correct a problem, correct it in the library and cut a new release.

# mathdb-lean problems

Lean 4 problem modules from the [Erdős problems](https://www.erdosproblems.com/),
with the pinned project they compile against. One release so far:
`erdos-20261001/`, holding **1106** problems.

Each problem is a frozen `Problem.Target` — a proposition stated in Lean, with no
proof — plus the identity and provenance of the statement it came from. A grader
elaborates one module at a time against this project and checks what it denotes.

## Read this before using it as a benchmark

**No problem here has been read by a person.** All 1106 are marked
`under_review` in `benchmark.json`: machine checks passed, no human has confirmed
that the Lean states the mathematics the source poses.

The release's own `release_id` and profile name are `erdos-reviewed`. That is a
*policy* name — the name of the admission profile — and **not** a claim that
anything was reviewed. The release record says so itself:

```
"note": "1106 of 1106 have not been read by a person yet"
```

The name is kept as published rather than corrected after the fact, because the
record is the record. Read it as "admitted by the erdos-reviewed policy", not as
"reviewed".

So: a faithfulness error in any individual problem is possible, and finding one
is useful. What *is* machine-established is below.

## What was established by machine

Every exported problem:

- **elaborates** against the pinned project (Lean `v4.33.1`, mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`);
- **reaches only** `propext`, `Classical.choice`, `Quot.sound` in its axiom
  closure — no `sorryAx`, no added axiom;
- **matches the interface** a task of its shape claims to have;
- **survived a tactic suite** aimed at closing the goal without doing the
  mathematics.

40 further candidates were **omitted** and are listed in
`benchmark.json.report.omitted`, each with its reason — 'compile is failed or its
evidence is stale/missing', 'dependencies is failed …'. They are named rather than
dropped silently, so the gap between 1146 and 1106 is accounted for.

## What is in it

| | |
|---|---|
| problems | 1106 |
| track | 672 open, 434 solved |
| shape | 345 `decide`, 300 `prove`, 300 `refute`, 142 `proof`, 19 `value` |
| source | [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at `e04cc601840dd7a37f89b821a67f3a9e3c38d9c3` |

`track` says whether the problem is **solved in the literature** — a fact about
mathematics, not about this repository. `source_has_lean_proof` is a different
claim and is false for almost every problem, because the upstream corpus is a
statement repository.

The 300 `prove` and 300 `refute` modules are **300 complete pairs**: the two
directions of the same open problem, either of which settles it. They are
published together on purpose. Half a pair tells a solver which direction is true,
so if you subset this benchmark, keep pairs whole — `pair_id` in `benchmark.json`
identifies them, and all 300 are whole here.

## Layout

```
lakefile.toml  lean-toolchain  lake-manifest.json   the pinned Lean project
lean/
  MathdbUtil*       the statement-support library every problem imports
  MathdbMathlib*    vendored Mathlib additions the library was written against
erdos-20261001/
  benchmark.json    identity, provenance, hashes, policy, selection, omissions
  problems/
    E1.lean  E1002_prove.lean  …    1106 modules
```

The problem modules are deliberately **not** a `lean_lib` in `lakefile.toml`.
They are the benchmark: each is elaborated on its own, against the built project,
never as part of it.

## Using it

```sh
lake exe cache get      # mathlib binaries, optional but much faster
lake build              # builds MathdbUtil and MathdbMathlib
```

Then point a grader's `project_dir` at this directory and give it
`erdos-20261001/problems/`. A submission replaces the `sorry` in a copy of one
module; the grader elaborates the result and compares what `Problem.Target`
denotes against the `semantic_anchor` recorded for that task in
`benchmark.json.report.tasks`.

## Verifying the release against this repository

The release pins its environment by content, so you can check that this
repository is the one it was produced against:

- `benchmark.json.policy` holds the allowed imports and axioms;
- `benchmark.json.report.release.environment_hash` is derived from the toolchain,
  the mathlib revision, and a hash over `lean/MathdbUtil*` and
  `lean/MathdbMathlib*` — all three are in this repository;
- every entry in `benchmark.json.problems` carries a `target_hash`, the digest of
  the module text as published. 1106 of 1106 files under
  `erdos-20261001/problems/` hash to the value recorded for them.

## Provenance and license

Apache 2.0 — see `LICENSE`. `NOTICE` states what was taken from
formal-conjectures and how it was changed, as Apache 2.0 section 4(b) requires:
`lean/MathdbUtil*` and `lean/MathdbMathlib*` are its `FormalConjecturesUtil/` and
`FormalConjecturesForMathlib/`, renamed. `AUTHORS` and the Lean pins are carried
over unchanged.

This repository holds **releases**. The library that produces them — the records,
the conversion and review evidence, the per-problem history — is maintained
separately; nothing here is a source of truth, and nothing here should be edited
by hand. To correct a problem, correct it in the library and cut a new release.

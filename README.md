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
| shape | 345 `decide`, 300 `prove`, 300 `refute`, 142 `proof`, 19 `value` — see below |
| source | [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at `e04cc601840dd7a37f89b821a67f3a9e3c38d9c3` |

`track` says whether the problem is **solved in the literature** — a fact about
mathematics, not about this repository. `source_has_lean_proof`, in each module's
metadata, is a different claim and is false for almost every problem, because the
upstream corpus is a statement repository.

The 300 `prove` and 300 `refute` modules are **300 complete pairs**: the two
directions of one open question, either of which settles it. A pair always sits in
one folder, because half a pair tells a solver which direction is true. `verify.py`
refuses a split pair.

## The five kinds of obligation

An obligation's `shape` is not a difficulty label. It fixes the **arity of
`Problem.Target`**, which is to say: what the submitter has to hand over.

| shape | `Problem.Target` | submitter supplies | count | open / solved | frozen gold |
|---|---|---|---|---|---|
| `proof` | `Target : Prop` | a proof | 142 | 55 / 87 | — |
| `prove` | `Target : Prop` | a proof | 300 | 299 / 1 | — |
| `refute` | `Target : Prop` | a proof | 300 | 299 / 1 | — |
| `decide` | `Target (verdict : Prop) : Prop` | a verdict **and** a proof | 345 | 0 / 345 | all 345 |
| `value` | `Target (value : τ) : Prop` | a value **and** a proof | 19 | 19 / 0 | — |

Two questions separate all five. Everything else about a shape follows from them.

```
Does the submitter supply an answer?
│
├── no ──→ How many obligations does the question become?
│          ├── one  ────────────────→  proof
│          └── two, as a pair  ─────→  prove / refute      settle either side
│
└── yes ─→ Is the answer already known?
           ├── yes, a Prop  ───────→  decide    graded against frozen gold
           └── no, an object  ─────→  value     graded as a verified witness
```

**The first question is the parameter**, and it is the one that changes the work.
`proof`, `prove` and `refute` state a fixed proposition and ask only for a proof.
`decide` and `value` leave a hole: the submitter fills it, and the proof is then
about the answer they chose, not about a proposition anyone handed them.

**The second question only separates shapes that share a signature.** `proof`,
`prove` and `refute` are all `Target : Prop` — identical in Lean. What differs is
how a question was cut into obligations: `proof` is one obligation, while `prove`
and `refute` are two halves of one question, the second being `¬ ( … )` around the
same body. So 300 `prove` plus 300 `refute` is **300 questions, not 600** — and a
solver picks whichever direction they believe. `proof` is the case where the setter
took the direction as known, which is why 87 of its 142 are `solved` while 299 of
the 300 pairs are open.

For the two that take an answer, what differs is whether the answer exists to be
checked against. `decide`'s hole is a `Prop` with two useful values and the answer
is known for all 345, so they are graded against a frozen gold. `value`'s hole is a
mathematical object and **none of the 19 has a gold**, because nobody knows the
answer — so the strongest thing a grader can say is that the submitter proved the
statement of the object they produced.

### `proof` — prove the statement

```lean
abbrev Target : Prop := …
```

The plain case: one proposition, prove it. 87 of the 142 are `solved` in the
literature, so a proof exists somewhere; 55 are open.

### `prove` / `refute` — the two directions of one open question

Published as **300 complete pairs**, both members in the same folder. The pair
shares a `pair_id`; `prove` states the conjecture and `refute` states its
negation, built as `¬ ( … )` around the same body. Settling either settles the
problem, so a solver may attack whichever side they believe.

This is why a pair is never split: seeing only the `prove` side of a question
tells you the setter believed it was provable. 299 of the 300 pairs are open. The
one exception is `erdos-1119`, which the source marks `research solved` with
`source_has_lean_proof: false` — settled in the literature, not in Lean, and
published as a pair because nothing here knows which direction the literature
settled it in.

### `decide` — say which way it goes, then prove that

```lean
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ n : ℕ → ℕ, StrictMono n ∧ 0 < n 0 ∧ …
```

The submitter supplies `verdict` and proves `verdict ↔ <the statement>`. Answering
`True` claims the statement holds; `False` claims it fails. Either way the proof is
the work — a verdict with no proof of the equivalence earns nothing.

All 345 are `solved`, and all 345 carry a frozen `gold_arguments`, so these are
graded against a known answer. The golds are **219 `True` and 126 `False`**: the
verdict is a real question, not a formality. Answering `True` everywhere would
match 63% of the verdicts and still prove nothing. The gold is fixed before any
submission is read, never after.

### `value` — supply the object, then prove the statement about it

```lean
abbrev Target (value : ℝ) : Prop := …
```

The submitter supplies the answer itself and proves the statement holds of it.
The 19 answer types, as published:

| type | count | |
|---|---|---|
| `ℕ → ℝ` | 11 | a real-valued sequence or bound |
| `ℝ` | 5 | a constant |
| `ℕ` | 1 | |
| `ℕ → ℕ` | 1 | |
| `∀ {U₁ U₂ : Type}, SimpleGraph U₁ → SimpleGraph U₂ → Prop` | 1 | a relation between graphs |

All 19 are open and **none has a gold**, because the answer is not known. They are
graded as a verified witness rather than against a fixed answer: an accepted
submission has proved the statement of the object it chose, which is a weaker
claim than matching a known answer, and a grader that conflates the two overstates
the result.

### `track` is about the literature, not the task

`open` and `solved` say whether mathematics has settled the problem — a fact about
the world, not about this repository and not a difficulty ranking. A `solved`
problem can still be hard to formalize a proof of; `source_has_lean_proof` in each
module's metadata is the separate, almost always false, claim that the upstream
corpus holds a machine-checked proof.

## Using this in research

### The answer is often written in the problem

This is not the usual training-data worry. It is in the artifact. Each module
carries the problem as the source poses it, in a `- prose:` field the solver
reads, and that prose frequently goes on to say how the problem was resolved.

Measured over the 345 `decide` obligations — the ones where the task *is* to say
which way it goes — a conservative keyword scan finds **190 (55%) whose prose
states the resolution outright**: 61 saying false against a `False` gold, 119
saying true against a `True` gold, 10 ambiguous. Inspected samples show the scan
under-reports rather than over-reports, and nothing was found where the prose
contradicts the gold. Examples, verbatim:

```
E1022  "… This is false, and c_t < 2 for all t: a counterexample is provided by Wood [Wo13b]"
E1000  "… This was solved by Haight [Ha] who proved that such a sequence does exist"
```

Over all 1106 obligations: **374 proses carry a literature citation** such as
`[Wo13b]` (326 of them on `solved` problems), and **all 1106** carry an
`erdosproblems.com` URL in `- notes:`, which is a direct route to the problem's
public page.

So a reader of the problem gets, for a majority of `decide` tasks, the direction
for free. It does not hand them the score — the obligation is
`verdict ↔ statement`, and the proof is still the work — but it does mean a
`decide` number is not a measurement of deciding. **If deciding is what you are
measuring, strip `prose` and `notes`, or report the 155 silent ones separately.**
`verify.py` keeps working either way; it hashes the published module, so note that
stripping fields changes the text and therefore the `target_hash`. Strip at load
time, not on disk.

### Nothing here has been read by a person

All 1106 are `reviewed_by_a_person = false`. A faithfulness error — Lean that does
not state the mathematics the source poses — is possible in any individual
problem, and a score computed over these is a score over propositions no human has
confirmed. Say so when you report one.

### What a result may and may not claim

- **`value` is not "answered correctly".** None of the 19 has a gold, because the
  answer is not known. An accepted `value` submission proved the statement of the
  object it supplied — a verified witness. Reporting it as a match against a known
  answer overstates it, and ftp-eval's own verdict text says
  `verified witness; no fixed gold` for exactly this reason.
- **`decide` is graded against a frozen gold**, fixed before any submission is
  read. The golds are 219 `True` to 126 `False`: a blanket `True` matches 63% of
  the verdicts and scores nothing without the equivalence proof. Report verdict
  accuracy and proof success separately, or the two get conflated.
- **Keep pairs whole when you subset.** `prove` and `refute` share a `pair_id`.
  Shipping one side tells the solver which direction the setter believed, so a
  subset that splits a pair measures something easier than the benchmark does.
  `verify.py` refuses a split pair.
- **`open` and `solved` are not difficulty.** They say whether mathematics has
  settled the problem. 672 obligations are open and 434 solved, and a number
  averaged over both says little: the solved ones have a proof in the literature
  that a model may have read, the open ones have none that anyone has.
- **`track` is not `source_has_lean_proof`.** The latter is almost always false:
  upstream is a statement repository, so "solved" rarely means a machine-checked
  proof exists.

### Citing it

`CITATION.cff` is in the repository, and GitHub renders it as *Cite this
repository*. Pin two things or the citation does not identify what you ran:

- the **`release_id`** from `benchmark.json` — `erdos-reviewed` here — which fixes
  which problems and which environment;
- the **commit** of this repository, which fixes the bytes.

`benchmark.json.report.release` also carries `environment_hash`, `profile_hash`
and `manifest_hash`; quoting `manifest_hash` identifies the release in one value.

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

# mathdb-lean problems

Lean 4 statements of the open and solved problems on [MathDB](https://mathdb.com), one folder
per problem, named by its MathDB number: `problems/315817/` is
[mathdb.com/p/315817](https://mathdb.com/p/315817) (Erdős problem 690).

```
problems/
  315817/
    E690.lean            one proof obligation, as the module FtpEvalBench.E690
    E690/Challenge.lean  the same statement with `sorry` holes, the file a solver fills in
    problem.toml         what the problem is, where each statement came from, how it is checked
  …
MathDBLib.lean           definitions that are MathDB's own (see below)
lakefile.toml            the Lean project every statement compiles against
benchmark.json           the release record: every obligation, its hash and its evidence
verify.py                checks the folders against benchmark.json
check_statements.py      compiles every statement and audits the axioms it rests on
TRACK-REVIEW.md          where `track` and erdosproblems.com disagree, for review
```

1532 obligations in 1009 problems. All of them are on MathDB; how far each statement *is* its
MathDB problem is stated per problem (see [MathDB](#mathdb)).

## The Lean project

There is one project, and it is formal-conjectures':

| | |
|---|---|
| [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) | `e04cc601`, required unmodified |
| Lean | `leanprover/lean4:v4.33.1`, the one formal-conjectures pins |
| Mathlib | `0df444a3`, inherited from formal-conjectures |

Statements import `FormalConjecturesUtil` (the `answer(…)` elaborator and problem metadata) and
`FormalConjecturesForMathlib` exactly as formal-conjectures publishes them. Nothing upstream
provides is copied into this repository.

**`MathDBLib`** is for definitions MathDB's statements need that neither Mathlib nor
formal-conjectures has. It is empty today: a definition belongs there only when it is genuinely
new, and anything upstream would accept should go upstream instead.

```sh
lake exe cache get                                   # Mathlib binaries
lake build                                           # MathDBLib, and formal-conjectures' libraries
lake env lean problems/315817/E690.lean
python check_statements.py problems/315817/E690.lean  # compiles it and audits its axioms
python verify.py                                     # every module still hashes to the release
```

## Sources

Every obligation but ten is formal-conjectures' own (Erdős problems, OEIS, Wikipedia, arXiv,
the Millennium problems and more), converted into one module per obligation; `problem.toml`
records the upstream file and revision of each, and `benchmark.json` the declaration. The
ten of the `authored` collection were written in the mathdb-lean library, which is not
public; for them the module here is the statement of record. [openai/math](https://github.com/openai/math)
is not copied here: it pins a different Lean and Mathlib, and none of its problems is on MathDB.

## Obligations

`shape` fixes what a solver hands over, as the arity of `Problem.Target`:

| shape | `Problem.Target` | the solver supplies | count |
|---|---|---|---|
| `proof` | `Target : Prop` | a proof | 384 |
| `prove` / `refute` | `Target : Prop` | a proof of either direction of one open question | 379 pairs |
| `decide` | `Target (verdict : Prop) : Prop` | a verdict and a proof, graded against a frozen answer | 384 |
| `value` | `Target (value : τ) : Prop` | an object and a proof about it; no answer is known | 6 |

The two halves of a `prove` / `refute` pair always sit in the same folder: seeing only one side
would tell a solver which way the setter believed it goes.

A `value` obligation is published only when its predicate pins the answer (`answer_pinned`,
with the reason, in `benchmark.json`). Eighteen were withdrawn on 2026-10-30 because a free
witness closed them: `f =Θ[atTop] value` holds at `value := f`, so "solving" one settled nothing.

`Problem.Target` has exactly the type its shape gives in the table above. Twenty-four `proof`
obligations (23 from Written on the Wall, one Chvátal) were withdrawn on 2026-10-31 because it did
not: the statement used a `variable` from its file, Lean made it a parameter, and `Target` was
`{α : Type u_1} → [Fintype α] → … → Prop`, so `theorem solution : Problem.Target` could not even
be stated.

Every statement compiles against the project, uses no `sorry`, and its `Problem.Target` depends
on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and `Target` has its shape's
type (`check_statements.py`, run by the `Check statements` workflow). `reviewed_by_a_person = false` on every obligation means what
it says: none has been read by a person, and a statement can say something other than the
problem. A proof settles the Lean statement; whether that settles the problem is a separate
question.

## `track`

`track` is formal-conjectures' own category for the statement it formalized — `research open`
or `research solved` — not an independent record of the literature. The two differ where the
formalized statement is a sharpened or partial form of the problem, and where upstream marks a
problem solved on the strength of a proof elsewhere. Against erdosproblems.com's status, 22 of
697 Erdős problems disagree and 10 have obligations that disagree among themselves; they are
listed in [TRACK-REVIEW.md](TRACK-REVIEW.md), waiting on a person to say which label is right.

Where formal-conjectures links a machine-checked proof kept outside its own corpus, the task
carries it as `source_formal_proof` — 430 obligations, all `solved`. `source_has_lean_proof` in a
module's header speaks only for the formal-conjectures corpus itself, so it is `false` for
these.

## MathDB

`benchmark.json`'s `mathdb` block gives, per problem, MathDB's number and row id, and a
`relation` saying how the Lean statements relate to that MathDB problem:

| relation | meaning | problems |
|---|---|---|
| `identity` | matched on the problem's own number or id | 991 |
| `stronger` | a proof of the Lean statement settles the MathDB problem, not conversely | 2 |
| `weaker` | the Lean statement is a special case; proving it does not settle the MathDB problem | 1 |
| `unreviewed` | matched by hand; how the two relate has not been checked | 15 |

The three read so far: Kakeya (`315983`, MathDB states only `n ≥ 4`) and Navier–Stokes
(`315852`, any one of Fefferman's (A)–(D) settles it; (A) and (B) are here) are `stronger`;
normality of π (`405914`, MathDB asks for every base, the statement is base 10) is `weaker`.

## Grading

[formal-theorem-proving-eval-api](https://github.com/mathdb-lean/formal-theorem-proving-eval-api)
grades answers against this repository as it is (from its 2026-10-30 version on): pass the
repository root, or one problem folder, as `--problems`, and `-o project_dir=` this repository once `lake build` has run. It
reads the gold answers, the toolchain and the policy from `benchmark.json`, and refuses to grade
a problem whose frozen answer it cannot find.

## `problem.toml`

`problem_id` is the source's id for the problem, `mathdb_number` the folder name, `prose` the
statement in words (a task whose own declaration says something else carries its own `prose`).
`[source]` names the upstream file and revision. Each `[[task]]` is one obligation: its module,
`shape`, `track`, `source_formal_proof` and `answer_pinned` where they apply, the toolchain it
was checked against, and its evidence hashes. `benchmark.json` holds the same facts for every
problem; `verify.py` re-derives each field from it and hashes every module, so an edit to either
side shows up.

## License

Apache 2.0. Statements converted from formal-conjectures keep its copyright notice; see `NOTICE`.

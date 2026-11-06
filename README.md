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
MathDBLib/               definitions that are MathDB's own (see below)
lakefile.toml            the Lean project every statement compiles against
benchmark.json           the release record: every obligation, its hash and its evidence
verify.py                checks the folders against benchmark.json
```

1574 obligations in 1045 problems. All of them are on MathDB.

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
lake exe cache get              # Mathlib binaries
lake build                      # MathDBLib, and formal-conjectures' libraries with it
lake env lean problems/315817/E690.lean
python verify.py                # every module still hashes to what the release recorded
```

## Sources

Most statements are formal-conjectures' own (Erdős problems, OEIS, Wikipedia, arXiv and more),
converted into one module per obligation; `problem.toml` records the upstream file and revision
of each. The `authored` collection and a few Millennium and Wikipedia problems were written for
MathDB. [openai/math](https://github.com/openai/math) is not copied here: it pins a different
Lean and Mathlib, and none of its problems is on MathDB.

## Obligations

`shape` fixes what a solver hands over, as the arity of `Problem.Target`:

| shape | `Problem.Target` | the solver supplies | count |
|---|---|---|---|
| `proof` | `Target : Prop` | a proof | 408 |
| `prove` / `refute` | `Target : Prop` | a proof of either direction of one open question | 379 pairs |
| `decide` | `Target (verdict : Prop) : Prop` | a verdict and a proof, graded against a frozen answer | 384 |
| `value` | `Target (value : τ) : Prop` | an object and a proof about it; no answer is known | 24 |

The two halves of a `prove` / `refute` pair always sit in the same folder: seeing only one side
would tell a solver which way the setter believed it goes.

`reviewed_by_a_person = false` on every obligation means what it says: every statement
compiles against the project (the `Check statements` workflow), but none has been read by a
person, and a statement can say something other than the problem. A proof settles the Lean
statement; whether that settles the problem is a separate question.

## `problem.toml`

`problem_id` is the source's id for the problem, `mathdb_number` the folder name, `prose` the
statement in words. `[source]` names the upstream file and revision. Each `[[task]]` is one
obligation: its module, `shape`, `track` (`open` or `solved` in the literature), the toolchain it
was checked against, and its evidence hashes. `benchmark.json` holds the same facts for every
problem; `verify.py` re-derives each field from it and hashes every module, so an edit to either
side shows up.

## License

Apache 2.0. Statements converted from formal-conjectures keep its copyright notice; see `NOTICE`.

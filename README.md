# mathdb-lean problems

Mathematical problems formalized in Lean 4. **One directory per source, and inside
it one folder per problem.** A folder holds that problem's proof obligations and a
`problem.toml` describing them. Each source directory is also the Lean project its
problems compile against, pinned to what that source's own upstream builds with.

```
problems/
  formal-conjectures/          one directory per source, and its Lean project:
    lakefile.toml              requires formal-conjectures at the pinned commit
    lean-toolchain             upstream's Lean
    lake-manifest.json         upstream's Mathlib, inherited
    1/
      E1.lean                  one proof obligation
      problem.toml
    391455/
      E1002_prove.lean         the two directions of one open question,
      E1002_refute.lean        published together
      problem.toml
    391594/
      E1209_parts_i.lean       nine obligations: three parts, one of them
      E1209_parts_ii.lean      in four sub-parts, most as prove/refute pairs
      …
      problem.toml
    406068/
      O100434_conjecture1.lean OEIS A100434, linked to its production MathDB number
      O100434_conjecture2.lean three obligations, each named by its Lean module
      O100434_conjecture3.lean
      problem.toml
  openai-math/
    lakefile.toml …            requires Mathlib at openai/math's revision
    openai-math-003/
      DirichletSevenEighths.lean   one openai/math result family; each of its
      HeckeSevenEighths.lean       comparator challenges is one obligation
      …
      problem.toml
  mathdb-lean/
    lakefile.toml …            the formal-conjectures environment again
    authored-onewayfunctions/
      AOneWayFunctions_prove.lean  a statement written in this library, for a
      AOneWayFunctions_refute.lean problem no imported corpus had formalized;
      problem.toml                 an open question ships as a prove/refute pair
```

Currently **1275 problems / 1971 obligations** across fourteen collections from three sources.

| collection | problems | obligations | what it is |
|---|---|---|---|
| `erdos` | 704 | 1106 | [Erdős problems](https://www.erdosproblems.com/) |
| `openai-math` | 230 | 397 | the Lean challenges of OpenAI's [math](https://github.com/openai/math) results: a manuscript's formalized theorems, each published upstream with a comparator-accepted proof |
| `authored` | 9 | 12 | statements written in this library (source `mathdb-lean`) for problems no imported corpus had formalized; each file says where it departs from the textbook formulation |
| `oeis` | 146 | 218 | conjectures stated in an [OEIS](https://oeis.org/) entry |
| `wikipedia` | 60 | 76 | named conjectures with a Wikipedia article |
| `green` | 39 | 66 | Ben Green's [open problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf) |
| `wotw` | 36 | 36 | Written on the Wall II, a conjecture-generator's output |
| `paper` | 15 | 16 | problems posed in a specific paper |
| `arxiv` | 12 | 13 | problems posed in an arXiv preprint |
| `mathoverflow` | 8 | 10 | questions asked on MathOverflow |
| `books` | 6 | 7 | problems posed in a book |
| `kourovka` | 5 | 8 | the [Kourovka Notebook](https://kourovka-notebook.org/) of group theory problems |
| `millennium` | 4 | 5 | Clay Millennium Prize problems |
| `other` | 1 | 1 | what upstream files under no source |

Every problem's `- notes:` line carries the reference its **source** declares — the
Wikipedia article, the arXiv abstract, the DOI, the Clay PDF — read out of the
upstream file rather than built from its name. For `green`, `wotw` and `kourovka`
upstream declares none to carry, and the route back is `- source_locator:`, which
names the upstream file that does. For `openai-math` it names the result family
and its scope note in openai/math; the catalogue under `openai-math/`
(`MANUSCRIPTS.md`, `manuscripts.json`) lists every manuscript of that source,
formalized or not, with a link to its PDF at the pinned revision.

## How a folder is named

Under `problems/` there is one directory per source — `formal-conjectures/`,
`openai-math/`, `mathdb-lean/` — and inside it a folder is **MathDB's problem number** where MathDB
has a record of the problem, and the **id its source gives it** where MathDB has
none. Both are exact, and `verify.py` refuses a folder that is neither, or that
sits under the wrong source.

```
problems/formal-conjectures/391455/        MathDB problem 391455, which is Erdős problem 1002
problems/formal-conjectures/406068/        MathDB problem 406068, from OEIS A100434
problems/openai-math/openai-math-003/      openai-math:003, result family 003 of openai/math
problems/mathdb-lean/authored-fourierrestriction/   authored:FourierRestriction, stated in this library
```

For a MathDB problem number `n`, its folder is
`https://github.com/mathdb-lean/problems/tree/main/problems/formal-conjectures/{n}`.
1,027 of the 1,036 published formal-conjectures problems use their confirmed
production MathDB numbers: all 704 Erdős problems and 323 from the other
collections. The other nine — three `millennium` and six `wikipedia` problems,
first published on 2026-10-16 and 2026-10-17 — have not been looked up in MathDB
yet and use their source id until they are. Dev may
assign a different number to the same problem; repository URLs always use the
production number. The 230 OpenAI math result families retain their source IDs
until a production MathDB mapping is confirmed. No local numbers are invented.

Either way the source identity is unchanged: `problem_id = "erdos:1002"` and
`problem_id = "oeis:100434"` are in each `problem.toml`, and Lean filenames and
module names keep their own obligation ids.

An obligation's file stem is its **published id**, which is what a submission
filename and a results directory key on. It is the last component of the Lean
module the file declares: `E1002_prove.lean` declares `FtpEvalBench.E1002_prove`.
That is unique by construction — two obligations cannot declare the same module —
and it is what Lean expects a file to be called, so the name a grader keys on and
the name the compiler resolves are one string. The library's own identity for the
obligation is opaque and travels in the manifest as `task_id`: an id that encodes
a name has to change when the name does, and a published address must not.

Each obligation is a frozen `Problem.Target` — a proposition stated in Lean, with
no proof. **Each source directory is itself the Lean project** its obligations
compile against, so a grader points `project_dir` and its problem directory at the
same `problems/<source>/`. It elaborates one module at a time against the project
and checks what it denotes.

## What was established by machine

Every published obligation:

- **elaborates** against its source's pinned project: for `formal-conjectures`
  and `mathdb-lean`, Lean `v4.33.1` and mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474` with upstream formal-conjectures'
  own support libraries, which is what that upstream builds with; for
  `openai-math`, Lean `v4.34.1` and mathlib
  `d13f23b723b8a846827a245b89c10fc7d3f11612`, which is what openai/math builds with;
- **reaches only** `propext`, `Classical.choice`, `Quot.sound` in its axiom
  closure — no `sorryAx`, no added axiom;
- **matches the interface** an obligation of its shape claims to have.

Separately, a **tactic suite** is run at the goal to see whether it closes without
anybody doing the mathematics -- `trivial`, `rfl`, `simp`, `norm_num`, `decide`,
`omega`, `positivity`. A target that falls to one of those is worthless to score
on, and only an attack finds that. On 2026-10-05, on Lean `v4.33.1` and mathlib `0df444a3` —
the pin `formal-conjectures` obligations are checked on again — every then published
obligation that admitted a probe was run against it — 1526 of the then 1550 — and **none
fell**. The modules it ran on imported the support library under the name this repository
then gave its copy, and later obligations did not exist yet, so the campaign has not been
repeated on the modules as published now, nor run against `openai-math` or `mathdb-lean`;
until it is, the published obligations carry elaboration and axiom evidence but no attack
evidence of their own. The 24 `value` obligations are not
attacked at all: their `Problem.Target` takes the answer the submitter chooses, so
there is no fixed goal to close. The campaign is re-run rather than cited once,
because a mathlib upgrade that made a target provable by `norm_num` is the only
direction that matters.

105 further candidates were **omitted**, each listed with its reason under its own
release in `benchmark.json.report.releases[].omitted` — `compile is failed or its
evidence is stale/missing`, `dependencies is failed …`. They are named rather than
dropped silently, so the gap between the 2076 obligations the releases considered and
the 1971 published is accounted for. One of them was published before: the authored
`ATateShafarevichFiniteness`, whose statement uses
`Field.absoluteGaloisGroup.mapOfAlgebra`, which the Mathlib formal-conjectures pins
does not have yet; `report.releases[].withdrawn` records it by identity and reason.
The two obligations of Erdős problem 1057, withdrawn on 2026-10-08 when Mathlib
`d13f23b7`'s `Nat.IsCarmichael` made upstream's `IsCarmichael` ambiguous under
`open Nat`, are published again: the Mathlib they are now checked on has no
`Nat.IsCarmichael`.

## What is in it

| | |
|---|---|
| problems | 1275 |
| obligations | 1971 |
| obligations per problem | 798 problems have 1, 379 have 2, 98 have 3–10 |
| track | 1019 open, 952 solved |
| shape | 805 `proof`, 384 `decide`, 379 `prove`, 379 `refute`, 24 `value` — see below |
| sources | [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at `e04cc601840dd7a37f89b821a67f3a9e3c38d9c3`; [openai/math](https://github.com/openai/math) at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; mathdb-lean (statements written in this library) at `b80da422c1869ddababb2992c7dc83556e0f930c` |

`track` describes the **statement that was formalized**, not necessarily the
problem as posed — see below, where a cross-check against MathDB's own catalog
disagrees for 44 of the problems both catalogues carry a status for. `source_has_lean_proof`, in each module's metadata, is a
different claim again: false for almost every formal-conjectures problem, because
that corpus is a statement repository, and true for every `openai-math` obligation,
whose upstream publishes a proof its comparator accepted against the same statement.

The 379 `prove` and 379 `refute` modules are **379 complete pairs**: the two
directions of one open question, either of which settles it. A pair always sits in
one folder, because half a pair tells a solver which direction is true. `verify.py`
refuses a split pair.

## The five kinds of obligation

An obligation's `shape` is not a difficulty label. It fixes the **arity of
`Problem.Target`**, which is to say: what the submitter has to hand over.

| shape | `Problem.Target` | submitter supplies | count | open / solved | frozen gold |
|---|---|---|---|---|---|
| `proof` | `Target : Prop` | a proof | 805 | 239 / 566 | — |
| `prove` | `Target : Prop` | a proof | 379 | 378 / 1 | — |
| `refute` | `Target : Prop` | a proof | 379 | 378 / 1 | — |
| `decide` | `Target (verdict : Prop) : Prop` | a verdict **and** a proof | 384 | 0 / 384 | all 384 |
| `value` | `Target (value : τ) : Prop` | a value **and** a proof | 24 | 24 / 0 | — |

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
same body. So 379 `prove` plus 379 `refute` is **379 questions, not 758** — and a
solver picks whichever direction they believe. `proof` is the case where the setter
took the direction as known, which is why 566 of its 805 are `solved` while 378 of
the 379 pairs are open.

For the two that take an answer, what differs is whether the answer exists to be
checked against. `decide`'s hole is a `Prop` with two useful values and the answer
is known for all 384, so they are graded against a frozen gold. `value`'s hole is a
mathematical object and **none of the 24 has a gold**, because nobody knows the
answer — so the strongest thing a grader can say is that the submitter proved the
statement of the object they produced.

### `proof` — prove the statement

```lean
abbrev Target : Prop := …
```

The plain case: one proposition, prove it. 566 of the 805 are `solved` in the
literature, so a proof exists somewhere; 239 are open.

### `prove` / `refute` — the two directions of one open question

Published as **379 complete pairs**, both members in the same folder. The pair
shares a `pair_id`; `prove` states the conjecture and `refute` states its
negation, built as `¬ ( … )` around the same body. Settling either settles the
problem, so a solver may attack whichever side they believe.

This is why a pair is never split: seeing only the `prove` side of a question
tells you the setter believed it was provable. 378 of the 379 pairs are open. The
one exception is Erdős problem 1119 (`problems/formal-conjectures/391543`), which the source marks `research solved` with
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

All 384 are `solved`, and all 384 carry a frozen `gold_arguments`, so these are
graded against a known answer. The golds are **231 `True` and 153 `False`**: the
verdict is a real question, not a formality. Answering `True` everywhere would
match 60% of the verdicts and still prove nothing. The gold is fixed before any
submission is read, never after.

### `value` — supply the object, then prove the statement about it

```lean
abbrev Target (value : ℝ) : Prop := …
```

The submitter supplies the answer itself and proves the statement holds of it.
The 24 answer types, as published:

| type | count | |
|---|---|---|
| `ℕ → ℝ` | 12 | a real-valued sequence or bound |
| `ℝ` | 5 | a constant |
| `ℕ → ℕ` | 2 | |
| `ℕ` | 1 | |
| `ℝ → ℕ` | 1 | |
| `ℕ+ → ℕ∞` | 1 | |
| `∀ {U₁ U₂ : Type}, SimpleGraph U₁ → SimpleGraph U₂ → Prop` | 1 | a relation between graphs |
| `∀ (G : Type) [Group G] [TopologicalSpace G], Prop` | 1 | a property of topological groups |

All 24 are open and **none has a gold**, because the answer is not known. They are
graded as a verified witness rather than against a fixed answer: an accepted
submission has proved the statement of the object it chose, which is a weaker
claim than matching a known answer, and a grader that conflates the two overstates
the result.

### `track`: what it actually describes, and where it is known to be wrong

`open` and `solved` are not a difficulty ranking. They come from
`formal-conjectures`'s `source_category`, and the thing that category describes is
**the statement formalized from the problem** — which is not always the problem.

Cross-checked against MathDB's own catalogue on the **497 problems whose MathDB
status this release records**: the two agree on **445** and disagree on **44**.

| MathDB says | this library says | count |
|---|---|---|
| `open` | `solved` | 36 |
| `claimed_progress` | `solved` | 5 |
| `claimed_solved` | `open` | 3 |

Sampling the first direction, the cause is the same each time. `problems/formal-conjectures/1` is
MathDB's *Maximum size of sets with distinct subset sums*, recorded open; the
module here says *"This conjecture is false. A machine-checked disproof constructs
sum-distinct sets for which N / 2^n tends to zero."* Both are right about
different things: what was formalized is the sharpened claim `N ≫ 2^n`, and that
is false, while the Erdős problem — the asymptotics of `f(n)` — is open.

A further **8** have obligations that disagree among themselves, which a single
status per problem cannot express and this one can: Erdős problem 12 has parts i
and ii settled and part iii open.

Every one of those numbers is **recomputable**, and that is the point: an earlier
version of this section quoted 613 and 74, and nothing in the published artifact
let a reader check it, because `mathdb.problems` carries `status` for only some
entries. The comparison now lives in the library as `tools/track_review.py`,
which states its rule — MathDB `open` and `claimed_progress` mean nobody has
settled it; `solved`, `refuted` and `claimed_solved` mean somebody has;
`claimed_solved` is reported apart because MathDB distinguishing it from `solved`
is MathDB saying the claim is not accepted yet — and emits the 44 as a queue with
each problem's folder and MathDB link.

So: do not read `track` as "mathematics has settled this", and do not average a
figure over `open` versus `solved` without saying which 44 you are standing on.
They are waiting on human review, which is the only thing that can decide which
label belongs where. `source_has_lean_proof` is the separate, almost always false,
claim that the upstream corpus holds a machine-checked proof.

## Using this in research

### Knowing the answer is not knowing the proof

Nothing is accepted here without a proof Lean's kernel checks. That is what makes
the benchmark robust to its own openness, and it is deliberate: a `prove`/`refute`
pair publishes **both** directions so a solver may pick one, and a `proof`
obligation publishes only the direction that holds. Telling the solver which way
to go was never the difficulty being withheld.

So the following is a description of what a solver is told, not a defect. Each
module carries the problem as the source poses it in a `- prose:` field, and that
prose often says how the problem was resolved. Over the 345 `decide` obligations
of the Erdős collection — the set this was measured on, before the other twelve
were added — a conservative keyword scan finds **190 (55%) whose prose states the
resolution outright**: 61 false against a `False` gold, 119 true against a `True`
gold, 10 ambiguous, 155 silent. Inspected samples show the scan under-reports, and nothing
was found where the prose contradicts the gold. Verbatim:

```
E1022  "… This is false, and c_t < 2 for all t: a counterexample is provided by Wood [Wo13b]"
E1000  "… This was solved by Haight [Ha] who proved that such a sequence does exist"
```

Across the 1106 Erdős obligations, **374 proses carry a literature citation** such
as `[Wo13b]` (326 of them on `solved` problems) and **all 1106** carry an
`erdosproblems.com` URL in `- notes:`. The other collections carry whatever
reference their own source declares, in the same field.

None of that is removable in any meaningful sense: 952 of the 1971 obligations are
on problems mathematics has already settled, so their answers and often their
proofs are in the literature whatever this repository prints. Stripping the prose
would hide a pointer, not the fact.

The one thing it does rule out is a **verdict-only metric**. Scoring a model on
picking `True` or `False` without the equivalence proof measures nothing here —
the direction is in the problem text for a majority of them, and a blanket `True`
matches 60% regardless. This benchmark defines no such metric; report proof
success, which is the thing the kernel decides.

### Nothing here has been read by a person

All 1971 are `reviewed_by_a_person = false`. The machine checks above passed; no
human has confirmed that the Lean states the mathematics the source poses. So a
faithfulness error in any individual problem is possible — finding one is useful —
and a score computed over these is a score over propositions nobody has read. Say
so when you report one.

One name misleads and is worth knowing about: each release's `release_id` ends in
`-reviewed` — `erdos-reviewed`, `oeis-reviewed` — which is the name of the
*admission policy*, not a claim of review. Each release record says as much in its
own `note` — `1106 of 1106 have not been read by a person yet` — and the names are
kept as published rather than corrected after the fact, because the record is the
record.

### What a result may and may not claim

- **`value` is not "answered correctly".** None of the 24 has a gold, because the
  answer is not known. An accepted `value` submission proved the statement of the
  object it supplied — a verified witness. Reporting it as a match against a known
  answer overstates it, and ftp-eval's own verdict text says
  `verified witness; no fixed gold` for exactly this reason.
- **`decide` is graded against a frozen gold**, fixed before any submission is
  read, and what is scored is the proof of `verdict ↔ statement`. The verdict on
  its own is not a result: the golds are 231 `True` to 153 `False`, a blanket
  `True` matches 60% of them, and the direction is already in the problem text for
  a majority. Report proof success.
- **Keep pairs whole when you subset.** `prove` and `refute` share a `pair_id`.
  Shipping one side tells the solver which direction the setter believed, so a
  subset that splits a pair measures something easier than the benchmark does.
  `verify.py` refuses a split pair.
- **`open` and `solved` are not difficulty.** They say whether mathematics has
  settled the problem. 1019 obligations are open and 952 solved, and a number
  averaged over both says little: the solved ones have a proof in the literature
  that a model may have read, the open ones have none that anyone has.
- **`track` is not `source_has_lean_proof`.** The latter is almost always false:
  upstream is a statement repository, so "solved" rarely means a machine-checked
  proof exists.

### Citing it

Pin two things, or the citation does not identify what you ran:

- **`report.distribution.manifest_hash`** from `benchmark.json`, a digest over the
  whole manifest, which fixes which problems, which environment and which evidence
  in one value;
- the **commit** of this repository, which fixes the bytes.

`python verify.py` recomputes that digest, so a citation to it is checkable rather
than quoted on trust. It is recomputed whenever the manifest is amended, and
`report.distribution.amends` keeps every earlier hash in order, so a citation to a
superseded one still resolves to a file that names it.

Each collection was admitted by **its own release**, and `report.releases[]`
carries that release's `release_id` — `erdos-reviewed`, `oeis-reviewed`, one per
collection — along with its `profile_hash`, `environment_hash` and the candidates
it omitted. Cite one of those when you report on a single collection rather than
on the whole distribution. The distribution itself is `mathdb-lean-problems`; it is
not named after any one of its releases.

## `problem.toml`

One per folder, generated from `benchmark.json`. It carries the problem's identity
and prose, its upstream source, and one `[[task]]` entry per obligation:

Abridged from `problems/formal-conjectures/391455/problem.toml`, which is Erdős problem 1002:

```toml
problem_id = "erdos:1002"
mathdb_number = 391455
collection = "erdos"
tasks = 2
reviewed_by_a_person = false
prose = "…the question, as the source states it…"
notes = "Erdos Problem 1002 -- https://www.erdosproblems.com/1002"

[source]
name = "formal-conjectures"
revision = "e04cc601840dd7a37f89b821a67f3a9e3c38d9c3"
file = "FormalConjectures/ErdosProblems/1002.lean"

[policy]
release_id = "erdos-reviewed"
released_at = "…"
allowed_axioms = ["propext", "Classical.choice", "Quot.sound"]
allowed_imports = ["Init", "Std", "Batteries", "Aesop", "Qq", "Plausible",
                   "Mathlib", "FormalConjecturesForMathlib", "FormalConjecturesUtil"]

[[task]]
id = "E1002_prove"
file = "E1002_prove.lean"
module = "FtpEvalBench.E1002_prove"
shape = "prove"
track = "open"
pair_id = "E1002"
declaration = "erdos_1002"
statement_id = "…"
  [task.environment]
  lean = "leanprover/lean4:v4.33.1"
  mathlib_rev = "0df444a360eaa60ab8c11dca51a86af692955474"
  [task.evidence]
  target_hash = "…"
  conversion_hash = "…"
  semantic_anchor = "…"
  reviewed_by_a_person = false
```

`mathdb_number` appears only where MathDB has a record of the problem, which is
why 1027 of the 1275 files carry it; `pair_id` only on the two halves of a pair,
`gold_arguments` only on the 384 `decide` obligations, and `part` only where the
question was cut into parts.

The environment pin sits **inside each task**, not once at the root. Today every
obligation of a source shares that source's Lean and mathlib revision — the 1574 of
`formal-conjectures` and `mathdb-lean` one, the 397 of `openai-math` another; an
obligation re-verified later against a different one records that in its own entry,
and nothing about the other problems changes.

## Layout

```
problems/<source>/<folder>/   one folder per problem: its modules and problem.toml
problems/<source>/lakefile.toml, lean-toolchain, lake-manifest.json
                              the source's Lean project: the environment its upstream pins
openai-math/                  the openai/math manuscript catalogue (MANUSCRIPTS.md, manuscripts.json)
benchmark.json                the release record
verify.py                     checks this repository against that record
```

Four things: the problems, the projects to compile them against, the record of
what was released, and the checker for it.

### One Lean project per source

A source is checked in the environment its own upstream pins, because two
upstreams pin two different Mathlibs and one project cannot match both.
`benchmark.json` states each source's toolchain and policy under
`environments.<source>`, and the source directory carries the project.

`problems/formal-conjectures/lakefile.toml` **requires
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at the
commit its problems were taken from, unmodified**, and does not require Mathlib
itself: Mathlib, and everything it pulls in, is inherited from upstream's own
manifest, and `lean-toolchain` is upstream's. The support libraries every module
imports — `FormalConjecturesUtil`, and `FormalConjecturesForMathlib` through it —
are upstream's files, fetched by Lake under upstream's names. This repository
carries no copy of them. `problems/mathdb-lean/` is the same environment, because
statements written in the library import the same support library.

`problems/openai-math/lakefile.toml` requires Mathlib alone, at the revision
openai/math pins: a comparator judge needs a challenge and its solution in one
environment, and openai/math wrote its challenges in that one.

Every published obligation records where it came from, as
`- source_locator: FormalConjectures/ErdosProblems/1002.lean#erdos_1002`. For
`formal-conjectures` that is a path in upstream at the recorded revision — on
GitHub, `https://github.com/google-deepmind/formal-conjectures/blob/<revision>/<path>`,
and, once `lake` has fetched the project, the same file under
`problems/formal-conjectures/.lake/packages/formal_conjectures/`. An `openai-math`
locator is a path in openai/math at the recorded revision; the catalogue under
`openai-math/` links into it.

The formal-conjectures package also holds upstream's statement corpus,
`FormalConjectures`, which is mostly `sorry`. No policy admits it: each
`allowed_imports` names `FormalConjecturesUtil` and `FormalConjecturesForMathlib`
only, and the axiom audit refuses `sorryAx` regardless.

The problem modules are deliberately **not** a `lean_lib`. They are the benchmark:
each is elaborated on its own, against the built project, never as part of it.
The `lakefile.toml`s are generated and declare no library of their own; keep it
that way if you edit one.

## Using it

```sh
cd problems/formal-conjectures        # or problems/mathdb-lean, problems/openai-math
lake exe cache get                    # mathlib binaries, optional but much faster
lake build FormalConjecturesUtil      # `lake build Mathlib` for problems/openai-math
cd ../.. && python verify.py          # every module still hashes to what the release recorded
```

`lake` writes its output to `.lake/` inside the source directory, which is
git-ignored — several gigabytes of it once mathlib is cached.

Then point a grader's `project_dir` and its problem directory at the same source
directory; the three carry different import headers and environments and are
graded as separate problem sets. A submission is an obligation's
`<id>/Challenge.lean` with its `sorry`s filled in, and the grader elaborates it
against that project.

A grader that expects all problems flat in one directory needs to walk folders
instead — `glob("problems/<source>/*/*.lean")` rather than `glob("*.lean")`. The file stem
is still the obligation's id, which is what submission filenames and result
directories key on.

The evaluator's check API asks two questions of one problem at a time — one of
these, or a statement of your own written in the same format. Is this proof
correct (`ftp-eval check-proof`; each obligation's `<id>/Challenge.lean` is the
file to fill in)? And is this formalization faithful to its prose
(`ftp-eval check-statement`: an LLM judge against the problem's `prose`, plus
prover probes for whether the statement elaborates and is not vacuous)? Both run
on the command line or behind `ftp-eval serve` over HTTP, one server per source
directory and its project; the
[check API](https://github.com/mathdb-lean/formal-theorem-proving-eval-api/blob/main/docs/api.md)
documents them.

## MathDB handles

`benchmark.json` carries MathDB's numeric handle and row UUID for every problem
MathDB has a record of, matched by production problem identity — the Erdős number,
or the problem id the source publishes for the other collections — using read-only
production queries. Each such obligation and `problem.toml` carries the same
`mathdb_number` as its folder. The existing `mathdb.by_mathdb_number` index maps
that number back to the source identity.

| state | count | |
|---|---|---|
| `resolved` | **1027** | all 704 Erdős problems, and 323 from the other formal-conjectures collections |
| `not_an_erdos_problem` | 248 | the 230 `openai-math` families and 9 `mathdb-lean` problems, which the lookup does not cover, and the 9 formal-conjectures problems no lookup has been run for yet |

MathDB's numbers differ between production and dev. `state = "resolved"` identifies
a production record; each entry includes its actual `mathdb_url`. **The MathDB
number is not the Erdős number.**

The states are kept apart rather than recorded as an absence, because "MathDB does
not have this" and "this was never a question MathDB was asked" are different facts —
and so is "the lookup never got an answer", which is why recording rate-limited
requests as absences once turned 311 problems MathDB does have into problems it does
not. Erdős problem 1057's entry was dropped when its obligations were withdrawn on
2026-10-08 and is restated, with `restated_from` naming the manifest it was recorded
in, from the release published before that; no new lookup was made for it.

Seven formerly provisional mappings now use their assigned production numbers:

| Erdős problem | Production number |
|---|---|
| 1046 | 405989 |
| 1134 | 405990 |
| 1213 | 405991 |
| 362 | 405992 |
| 542 | 405993 |
| 673 | 405994 |
| 895 | 405995 |

`report.distribution.amends` records earlier manifest fingerprints. The current
fingerprint is recomputed after the metadata amendment; statement hashes are unchanged.

## Verifying the release against this repository

`python verify.py` does all of it, and exits non-zero on any mismatch:

- every module hashes to the `target_hash` its own release recorded (1971 of 1971);
- every source directory's Lean project pins the toolchain and mathlib revision
  its `environments` entry states;
- every `problem.toml` release field agrees with `benchmark.json`, including the folder's `mathdb_number`;
- every released obligation appears in exactly one folder, and no folder holds a
  module the release does not list;
- no `pair_id` is split across or out of a folder;
- the `mathdb` block agrees with itself: obligation handles match their problem,
  the reverse map round-trips, and the counts match the entries;
- the manifest matches its recorded fingerprint.

The environment is pinned by content too:
`report.releases[].release.environment_hash` is derived from the toolchain, the
mathlib revision, the Lake version and the source's `project_hash`, a digest over
the packages its `lake-manifest.json` pins (name, URL, commit) and its Lean
options. All of it is in `problems/<source>/`, so the pin is reconstructible here,
and a fork of an upstream is a different environment from the upstream even at the
same commit. `verify.py` checks that each source directory's `lean-toolchain` and
mathlib revision are the ones `environments.<source>` states.

## Provenance and license

Apache 2.0 — see `LICENSE`. `NOTICE` states what was taken from formal-conjectures
and from openai/math and how each was changed, as Apache 2.0 section 4(b)
requires. formal-conjectures' support libraries are not in this repository at all:
the projects require them from upstream, unmodified. Until 2026-10-28 this
repository carried a renamed copy of them, twelve files of it edited to build on
Lean `v4.34.1`, and a mirror of upstream's statement corpus; both are in its
history. The `openai-math` modules are OpenAI's challenge files with each sorried
theorem restated as a definition and a `Problem.Target` added.

This repository holds **releases**. The library that produces them — the records,
the conversion and review evidence, the per-problem history — is maintained
separately; nothing here is a source of truth, and nothing here should be edited by
hand. To correct a problem, correct it in the library and cut a new release.

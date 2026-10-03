/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E678
- collection: erdos
- question_id: erdos:678
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/678.lean#erdos_678
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Write $M(n, k)$ be the least common multiple of $\{n+1, \dotsc, n+k\}$. Let $k$ be sufficiently large. Are there infinitely many $m, n$ with $m \geq n + k$ such that $$ M(n, k) > M(m, k + 1) $$? The answer is yes, as proved in a strong form by Cambie [Ca24]. [Ca24] S. Cambie, Resolution of an Erdős' problem on least common multiples. arXiv:2410.09138 (2024). This was formalized in Lean by Alexeev using Aristotle, on top of the PNT+ project. For a fixed $k$ there are only finitely many such pairs, so "infinitely many" is read here as ranging over $k$ as well: for every sufficiently large $k$ at least one pair $(m, n)$ occurs. See `erdos_678.variants.infinitely_many_triples` for the reading in which the infinitude is stated directly, and `erdos_678.variants.not_infinitely_many_pairs` for why it cannot be asked of a single $k$.
- notes: Erdos Problem 678 -- https://www.erdosproblems.com/678
- track: solved
- answer_shape: decide
- source_stem: 678
- mathdb_ref: erdos:678
- source_namespace: Erdos678
- source_theorem: erdos_678
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: lcmInterval_lt_example1 lcmInterval_lt_example2 lcmInterval_lt_example3 lcmInterval_lt_example4
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Asymptotics Filter Finset

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
The referee of [Er79] found the example $M(96, 7) > M(104, 8)$, showing that there are cases where
$M(n, k) > M(m, k + 1)$ with $m \geq n + k$.
[Er79] Erdős, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.
-/
@[category test, AMS 11]
lemma lcmInterval_lt_example1 : lcmInterval 104 8 < lcmInterval 96 7 := by decide

/--
The referee of [Er79] found the example $M(132, 7) > M(139, 8)$, showing that there are cases where
$M(n, k) > M(m, k + 1)$ with $m \geq n + k$.
[Er79] Erdős, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.
-/
@[category test, AMS 11]
lemma lcmInterval_lt_example2 : lcmInterval 139 8 < lcmInterval 132 7 := by decide

/--
Cambie [Ca24] found the example $M(52, 7) > M(62, 8)$.
[Ca24] S. Cambie, Resolution of an Erdős' problem on least common multiples. arXiv:2410.09138 (2024).
-/
@[category test, AMS 11]
lemma lcmInterval_lt_example3 : lcmInterval 62 8 < lcmInterval 52 7 := by decide

/--
Cambie [Ca24] found the example $M(36, 8) > M(48, 9)$.
[Ca24] S. Cambie, Resolution of an Erdős' problem on least common multiples. arXiv:2410.09138 (2024).
-/
@[category test, AMS 11]
lemma lcmInterval_lt_example4 : lcmInterval 47 9 < lcmInterval 36 8 := by decide

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ᶠ k in atTop, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Nonempty

end Problem

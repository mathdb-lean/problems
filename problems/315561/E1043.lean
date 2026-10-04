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

- problem_id: E1043
- collection: erdos
- question_id: erdos:1043
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1043.lean#erdos_1043
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 1043**: Let $f\in \mathbb{C}[x]$ be a monic polynomial. Must there exist a straight line $\ell$ such that the projection of $$\{ z: \lvert f(z)\rvert\leq 1\}$$ onto $\ell$ has measure at most $2$? Pommerenke [Po61] proved that the answer is no. The projection onto the line $\ell = \mathbb{R} u$ is measured with the Lebesgue measure of that line, so `volume` of the projected set is its length. This was formalized in Lean by Alexeev using Aristotle.
- notes: Erdos Problem 1043 -- https://www.erdosproblems.com/1043
- track: solved
- answer_shape: decide
- source_stem: 1043
- mathdb_ref: erdos:1043
- source_namespace: Erdos1043
- source_theorem: erdos_1043
- source_category: research solved
- source_ams: 28 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open MeasureTheory Polynomial

/-- The set $\{ z \in \mathbb{C} : \lvert f(z)\rvert\leq 1\}$ -/
def levelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (f : ℂ[X]), f.Monic → f.degree ≥ 1 →
      ∃ (u : ℂ), ‖u‖ = 1 ∧
      volume ((ℝ ∙ u).orthogonalProjectionOnto '' levelSet f) ≤ 2

end Problem

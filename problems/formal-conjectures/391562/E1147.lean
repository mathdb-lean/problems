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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E1147
- collection: erdos
- question_id: erdos:1147
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1147.lean#erdos_1147
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\alpha>0$ be an irrational number. Is the set $$A=\left\{ n\geq 1: \| \alpha n^2\| < \frac{1}{\log n}\right\},$$ where $\|\cdot\|$ denotes the distance to the nearest integer, an additive basis of order $2$? This was disproved by Konieczny [Ko16b], and is false both for almost every $\alpha>0$, and also is false specifically for $\alpha=\sqrt{2}$. More generally, given any $\epsilon(n)\to 0$, the set $A=\{ n\geq 1: \| \alpha n^2\| < \epsilon(n)\}$ is not an additive basis of order $2$ for almost every $\alpha>0$.
- notes: Erdos Problem 1147 -- https://www.erdosproblems.com/1147
- track: solved
- answer_shape: decide
- source_stem: 1147
- mathdb_ref: erdos:1147
- source_namespace: Erdos1147
- source_theorem: erdos_1147
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter MeasureTheory

namespace Problem

/-- The set $\{ n\geq 1: \| \alpha n^2\| < \epsilon(n)\}$. -/
def recurrenceSet (α : ℝ) (ε : ℕ → ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ distToNearestInt (α * n ^ 2) < ε n}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ α : ℝ, 0 < α → Irrational α →
        (recurrenceSet α fun n ↦ 1 / Real.log n).IsAsymptoticAddBasisOfOrder 2

end Problem

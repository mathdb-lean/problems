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

- problem_id: E846
- collection: erdos
- question_id: erdos:846
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/846.lean#erdos_846
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 846** Let `A ⊂ ℝ²` be an infinite set for which there exists some `ϵ>0` such that in any subset of `A` of size `n` there are always at least `ϵn` with no three on a line. Is it true that `A` is the union of a finite number of sets where no three are on a line? In other words, prove or disprove the following statement: every infinite `ε`-non-trilinear subset of the plane is weakly non-trilinar.
- notes: Erdos Problem 846 -- https://www.erdosproblems.com/846
- track: solved
- answer_shape: decide
- source_stem: 846
- mathdb_ref: erdos:846
- source_namespace: Erdos846
- source_theorem: erdos_846
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open EuclideanGeometry

namespace Problem

section Prelims

/-- We say a subset `A` of points in the plane is `ε`-non-trilinear if any subset
`B` of `A`, contains a non-trilinear subset `C` of size at least `ε|B|`. -/
def NonTrilinearFor (A : Set ℝ²) (ε : ℝ) : Prop :=
  ∀ B : Finset ℝ², ↑B ⊆ A → ∃ C ⊆ B,
    ε * B.card ≤ C.card ∧ NonTrilinear (C : Set ℝ²)

/-- We say a subset `A` of points in the plane is weakly non-trilinear if it is
a finite union of non-trilinear sets. -/
def WeaklyNonTrilinear (A : Set ℝ²) : Prop :=
  ∃ B : Finset (Set ℝ²), A = sSup B ∧ ∀ b ∈ B, NonTrilinear b

end Prelims

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ᵉ (A : Set ℝ²) (ε > 0), A.Infinite → NonTrilinearFor A ε →
        WeaklyNonTrilinear A

end Problem

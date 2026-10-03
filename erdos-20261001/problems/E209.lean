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

- problem_id: E209
- collection: erdos
- question_id: erdos:209
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/209.lean#erdos_209
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be a finite collection of $d\geq 4$ non-parallel lines in $\mathbb{R}^2$ such that there are no points where at least four lines from $A$ meet. Must there exist a 'Gallai triangle' (or 'ordinary triangle'): three lines from $A$ which intersect in three points, and each of these intersection points only intersects two lines from $A$? Füredi and Palásti [FuPa84] showed this is false when $d\geq 4$ is not divisible by $9$. Escudero [Es16] showed this is false for all $d\geq 4$.
- notes: Erdos Problem 209 -- https://www.erdosproblems.com/209
- track: solved
- answer_shape: decide
- source_stem: 209
- mathdb_ref: erdos:209
- source_namespace: Erdos209
- source_theorem: erdos_209
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open EuclideanGeometry Affine

namespace Problem

/-- The number of lines from `A` that pass through the point `p`. -/
noncomputable def pointMultiplicity (A : Finset (AffineSubspace ℝ ℝ²)) (p : ℝ²) : ℕ :=
  {L ∈ (A : Set (AffineSubspace ℝ ℝ²)) | p ∈ L}.ncard

/--
A *Gallai triangle* (or *ordinary triangle*) in a collection `A` of lines: three lines from `A`
which intersect in three points, and each of these intersection points only intersects two
lines from `A`.
-/
def HasGallaiTriangle (A : Finset (AffineSubspace ℝ ℝ²)) : Prop :=
  ∃ L₁ ∈ A, ∃ L₂ ∈ A, ∃ L₃ ∈ A, L₁ ≠ L₂ ∧ L₂ ≠ L₃ ∧ L₁ ≠ L₃ ∧
    ∃ p₁ p₂ p₃ : ℝ², p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
      p₁ ∈ L₁ ∧ p₁ ∈ L₂ ∧ p₂ ∈ L₂ ∧ p₂ ∈ L₃ ∧ p₃ ∈ L₃ ∧ p₃ ∈ L₁ ∧
      pointMultiplicity A p₁ = 2 ∧ pointMultiplicity A p₂ = 2 ∧ pointMultiplicity A p₃ = 2

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ d : ℕ, 4 ≤ d → ∀ A : Finset (AffineSubspace ℝ ℝ²), A.card = d →
          (∀ L ∈ A, IsLine L) →
          ((A : Set (AffineSubspace ℝ ℝ²)).Pairwise fun L₁ L₂ => ¬ L₁ ∥ L₂) →
          (∀ p : ℝ², pointMultiplicity A p ≤ 3) →
          HasGallaiTriangle A

end Problem

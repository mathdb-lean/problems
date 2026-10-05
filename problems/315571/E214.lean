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

- problem_id: E214
- collection: erdos
- question_id: erdos:214
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/214.lean#erdos_214
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $S\subset \mathbb{R}^2$ be such that no two points in $S$ are distance $1$ apart. Must the complement of $S$ contain four points which form a unit square? The answer is yes, proved by Juhász [Ju79], who proved more generally that the complement of $S$ must contain a congruent copy of any set of four points.
- notes: Erdos Problem 214 -- https://www.erdosproblems.com/214
- track: solved
- answer_shape: decide
- source_stem: 214
- mathdb_ref: erdos:214
- source_namespace: Erdos214
- source_theorem: erdos_214
- source_category: research solved
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped Congruent EuclideanGeometry

namespace Problem

/-- The four vertices of a unit square. -/
def unitSquare : Fin 4 → ℝ² := ![!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]]

/-- Colouring the points of `S` blue and the points of `Sᶜ` red gives a red/blue colouring of
$\mathbb{R}^2$; it is unit-distance-avoiding if no two blue points are distance $1$ apart. -/
def UnitDistanceAvoiding (S : Set ℝ²) : Prop := ∀ x ∈ S, ∀ y ∈ S, dist x y ≠ 1

/-- Any unit-distance-avoiding colouring contains a congruent red copy of every set of `n`
points. -/
def HasRedCopies (n : ℕ) : Prop :=
  ∀ S : Set ℝ², UnitDistanceAvoiding S → ∀ K : Fin n → ℝ², Function.Injective K →
    ∃ p : Fin n → ℝ², (∀ i, p i ∈ Sᶜ) ∧ (p ≅ K)

/-- The largest integer `k` such that any unit-distance-avoiding colouring contains a congruent
red copy of every set of `k` points. -/
noncomputable def k : ℕ := sSup {n | HasRedCopies n}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ S : Set ℝ², UnitDistanceAvoiding S →
          ∃ p : Fin 4 → ℝ², (∀ i, p i ∈ Sᶜ) ∧ (p ≅ unitSquare)

end Problem

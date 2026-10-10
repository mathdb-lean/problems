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

- problem_id: E99_refute
- collection: erdos
- question_id: erdos:99
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/99.lean#erdos_99
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For sufficiently large n, is it the case that any set of n points with minimum distance $1$ that minimizes diameter must contain an equilateral triangle of side length 1?
- notes: Erdos Problem 99 -- https://www.erdosproblems.com/99
- track: open
- answer_shape: refute
- pair_id: E99
- pair_role: refute
- source_stem: 99
- mathdb_ref: erdos:99
- source_namespace: Erdos99
- source_theorem: erdos_99
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set Metric EuclideanGeometry

namespace Problem

/-- A set has minimum distance $1$ if all pairwise distances are at least $1$,
and the minimum is achieved. -/
def HasMinDist1 (A : Finset ℝ²) : Prop :=
  (∀ᵉ (p ∈ A) (q ∈ A), p ≠ q → dist p q ≥ 1) ∧
  (∃ᵉ (p ∈ A) (q ∈ A), dist p q = 1)

/-- Three points form an equilateral triangle of side length 1. -/
def FormsEquilateralTriangle (p q r : ℝ²) : Prop :=
  dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1

abbrev Target : Prop :=
    ¬ (
      ∀ᶠ n in Filter.atTop, ∀ A : Finset ℝ²,
        A.card = n → HasMinDist1 A →
        (IsMinOn (fun B: Finset ℝ² => diam (B : Set ℝ²)) {B : Finset ℝ² | B.card = n ∧ HasMinDist1 B} A) →
        ∃ᵉ (p ∈ A) (q ∈ A) (r ∈ A), FormsEquilateralTriangle p q r
    )

end Problem

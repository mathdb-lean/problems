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

- problem_id: E100_prove
- collection: erdos
- question_id: erdos:100
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/100.lean#erdos_100
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is the diameter of $A$ at least $Cn$ for some constant $C > 0$?
- notes: Erdos Problem 100 -- https://www.erdosproblems.com/100
- track: open
- answer_shape: prove
- pair_id: E100
- pair_role: prove
- source_stem: 100
- mathdb_ref: erdos:100
- source_namespace: Erdos100
- source_theorem: erdos_100
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set Metric Filter Real
open scoped EuclideanGeometry

namespace Problem

/-- If two distances in A differ, they differ by at least 1. -/
def DistancesSeparated (A : Finset ℝ²) : Prop :=
  ∀ p₁ q₁ p₂ q₂, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1

abbrev Target : Prop :=
    ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) > C * n

end Problem

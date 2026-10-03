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

- problem_id: E188
- collection: erdos
- question_id: erdos:188
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/188.lean#erdos_188
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: What is the smallest $k$ such that $\mathbb{R}^2$ can be red/blue coloured with no pair of red points unit distance apart, and no $k$-term arithmetic progression of blue points with distance 1?
- notes: Erdos Problem 188 -- https://www.erdosproblems.com/188
- track: open
- answer_shape: value
- answer_type: ℕ
- answer_pinned: true
- answer_pinned_reason: extremum_is_unique
- source_stem: 188
- mathdb_ref: erdos:188
- source_namespace: Erdos188
- source_theorem: erdos_188
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The set of numbers $k$ such that $\mathbb{R}^2$ can be red/blue coloured with no pair of red
points unit distance apart, and no $k$-term arithmetic progression of blue points with distance 1.
-/
def s := { k : ℕ | ∃ blue : Set ℂ,
  (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1) ∧
    ¬ (∃ᵉ (bs ⊆ blue) (z) (d), ‖d‖ = 1 ∧ bs.IsAPOfLengthWith k z d) }

abbrev Target (value : ℕ) : Prop :=
    IsLeast s value

end Problem

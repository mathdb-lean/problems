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

- problem_id: E1121
- collection: erdos
- question_id: erdos:1121
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1121.lean#erdos_1121
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $C_1,\ldots,C_n$ are circles in $\mathbb{R}^2$ with radii $r_1,\ldots,r_n$ such that no line disjoint from all the circles divides them into two non-empty sets then the circles can be covered by a circle of radius $r=\sum r_i$. This is true, and was proved by Goodman and Goodman [GoGo45] (whose proof also generalises to higher dimensions). A generalisation to convex bodies was proved by Hadwiger [Ha47]. An alternative proof is given by Bezdek and Litvak [BeLi16].
- notes: Erdos Problem 1121 -- https://www.erdosproblems.com/1121
- track: solved
- answer_shape: proof
- source_stem: 1121
- mathdb_ref: erdos:1121
- source_namespace: Erdos1121
- source_theorem: erdos_1121
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open scoped EuclideanGeometry

abbrev Target : Prop :=
    ∀ {n : ℕ} (c : Fin n → ℝ²) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
        (hsep : ∀ (v : ℝ²) (t : ℝ), v ≠ 0 →
          (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), inner ℝ v p ≠ t) →
          (∀ i, inner ℝ v (c i) < t) ∨ (∀ i, t < inner ℝ v (c i))),
      ∃ z : ℝ², (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i)

end Problem

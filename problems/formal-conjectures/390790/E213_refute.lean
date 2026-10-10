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

- problem_id: E213_refute
- collection: erdos
- question_id: erdos:213
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/213.lean#erdos_213
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $n \geq 4$. Are there $n$ points in $\mathbb{R}^2$, no three on a line and no four on a circle, such that all pairwise distances are integers?
- notes: Erdos Problem 213 -- https://www.erdosproblems.com/213
- track: open
- answer_shape: refute
- pair_id: E213
- pair_role: refute
- source_stem: 213
- mathdb_ref: erdos:213
- source_namespace: Erdos213
- source_theorem: erdos_213
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open EuclideanGeometry

namespace Problem

/--
The predicate (on $n$) that there exist $n$ points in $\mathbb{R}^2$,
no three on a line and no four on a circle,
such that all pairwise distances are integers.
-/
def Erdos213For (n : ℕ) : Prop := ∃ S : Set ℝ², S.Finite ∧ S.ncard = n ∧
    NonTrilinear S ∧
    (∀ Q : Set ℝ², Q ⊆ S ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q) ∧
    (S.Pairwise fun p₁ p₂ => dist p₁ p₂ ∈ Set.range Int.cast)

abbrev Target : Prop :=
    ¬ (
      ∀ n : ℕ, n ≥ 4 → Erdos213For n
    )

end Problem

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

- problem_id: G85_refute
- collection: green
- question_id: green:85
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/85.lean#green_85
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that $A$ is an open subset of $[0, 1]^2$ with measure $\alpha$. Are there four points in $A$ determining an axis-parallel rectangle with area $\gt c \alpha^2$?
- notes: Green, open problem 85
- track: open
- answer_shape: refute
- pair_id: G85
- pair_role: refute
- source_stem: 85
- source_namespace: Green85
- source_theorem: green_85
- source_category: research open
- source_ams: 28 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter MeasureTheory Set Topology

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∃ c > 0, ∀ A : Set (ℝ × ℝ),
        IsOpen A →
        A ⊆ Icc 0 1 ×ˢ Icc 0 1 →
        A.Nonempty →
        let α := (volume A).toReal
        ∃ x₁ x₂ y₁ y₂,
          {(x₁, y₁), (x₂, y₁), (x₂, y₂), (x₁, y₂)} ⊆ A ∧
          c * α ^ 2 ≤ |x₁ - x₂| * |y₁ - y₂|
    )

end Problem

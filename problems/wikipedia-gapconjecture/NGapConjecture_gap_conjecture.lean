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

- problem_id: NGapConjecture_gap_conjecture
- collection: wikipedia
- question_id: wikipedia:GapConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/GapConjecture.lean#gap_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If a finitely generated group has superpolynomial growth, then with respect to any finite generating set its growth function is at least $e^{\sqrt n}$ in Grigorchuk's preorder on growth functions, where the comparison is witnessed by linearly rescaling the radius.
- notes: Wikipedia: GapConjecture -- https://en.wikipedia.org/wiki/Gromov%27s_theorem_on_groups_of_polynomial_growth#The_gap_conjecture
- track: open
- answer_shape: proof
- source_stem: GapConjecture
- source_namespace: GapConjecture
- source_theorem: gap_conjecture
- source_category: research open
- source_ams: 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter GromovPolynomialGrowth

abbrev Target : Prop :=
    ∀ (G : Type) [Group G] (S : Set G), S.Finite → Subgroup.closure S = ⊤ →
      HasSuperPolynomialGrowth G →
      ∃ C : ℕ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop, Real.exp (Real.sqrt (n : ℝ)) ≤
          (GrowthFunction S (C * n) : ℝ)

end Problem

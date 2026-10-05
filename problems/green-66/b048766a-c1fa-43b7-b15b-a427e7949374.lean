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

- problem_id: G66_prove
- collection: green
- question_id: green:66
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/66.lean#green_66
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there always a sum of two squares between $X - \frac{1}{10}X^{1/4}$ and $X$? We formalize this as an eventual statement for sufficiently large real $X$.
- notes: Green, open problem 66
- track: open
- answer_shape: prove
- pair_id: G66
- pair_role: prove
- source_stem: 66
- source_namespace: Green66
- source_theorem: green_66
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

/-- A natural number is a sum of two squares if it can be written as `a ^ 2 + b ^ 2`. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

abbrev Target : Prop :=
    ∀ᶠ X : ℝ in atTop,
        ∃ n : ℕ, IsSumOfTwoSquares n ∧
          (n : ℝ) ∈ Set.Icc (X - (1 / 10 : ℝ) * X ^ (1 / 4 : ℝ)) X

end Problem

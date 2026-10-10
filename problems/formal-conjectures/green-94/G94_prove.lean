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

- problem_id: G94_prove
- collection: green
- question_id: green:94
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/94.lean#green_94
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let `A ⊂ R` be a set of positive measure. Does $A$ contain an affine copy of `{1, 1/2, 1/4, . . . }`?
- notes: Green, open problem 94 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.94
- track: open
- answer_shape: prove
- pair_id: G94
- pair_role: prove
- source_stem: 94
- source_namespace: Green94
- source_theorem: green_94
- source_category: research open
- source_ams: 28
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set MeasureTheory

namespace Problem

abbrev Target : Prop :=
    ∀ A : Set ℝ,
    MeasurableSet A ∧ volume A > 0 →
    ∃ a b : ℝ, a ≠ 0 ∧ ∀ n : ℕ, a * (1 / 2^n) + b ∈ A

end Problem

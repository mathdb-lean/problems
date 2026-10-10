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

- problem_id: G60_refute
- collection: green
- question_id: green:60
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/60.lean#green_60
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there an absolute constant $c > 0$ such that, whenever $A ⊆ \mathbb{N}$ is a set of squares with $|A| ≥ 2$, the sumset $A + A$ satisfies $|A + A| ≥ |A|^{1 + c}$?
- notes: Green, open problem 60 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8
- track: open
- answer_shape: refute
- pair_id: G60
- pair_role: refute
- source_stem: 60
- source_namespace: Green60
- source_theorem: green_60
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Pointwise

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∃ c > (0 : ℝ),
        ∀ (A : Finset ℕ),
          (∀ a ∈ A, IsSquare a) →
          2 ≤ A.card →
            ((A + A).card : ℝ) ≥ (A.card : ℝ) ^ (1 + c)
    )

end Problem

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

- problem_id: G82
- collection: green
- question_id: green:82
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/82.lean#green_82
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A \subset \mathbb{Z}$ be a set of size $n$. For how many $\theta \in \mathbb{R}/\mathbb{Z}$ must we have $\sum_{a \in A} \cos(2\pi a\theta) = 0$? The answer is the function `minZeros`.
- notes: Green, open problem 82 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.82
- track: open
- answer_shape: value
- answer_type: ℕ+ → ℕ∞
- answer_pinned: false
- answer_pinned_reason: unclassified
- source_stem: 82
- source_namespace: Green82
- source_theorem: green_82
- source_category: research open
- source_ams: 11 42
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real Set
open scoped Finset

namespace Problem

/-- The minimum number of zeros in $[0,1)$ of $\sum_{a \in A} \cos(2\pi a\theta)$
over all sets $A \subset \mathbb{Z}$ of size $n$. -/
noncomputable def minZeros (n : ℕ+) : ℕ∞ :=
  ⨅ A : {A : Finset ℤ // A.card = n},
    ({θ : ℝ | θ ∈ Ico 0 1 ∧ ∑ a ∈ A.val, cos (2 * π * a * θ) = 0} : Set ℝ).ncard

abbrev Target (value : ℕ+ → ℕ∞) : Prop :=
    value = minZeros

end Problem

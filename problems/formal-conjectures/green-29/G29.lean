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

- problem_id: G29
- collection: green
- question_id: green:29
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/29.lean#green_29
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that $A$ is a $K$-approximate group (not necessarily abelian). Is there $S \subset A$, $|S| \gg K^{-O(1)} |A|$, with $S^8 \subset A^4$? The answer is negative. A counterexample is given, for arbitrarily large finite groups `H`, by `A = ({-1} × H) ∪ ({1} × H) ∪ {(0, 1)}` in `Multiplicative ℤ × H`.
- notes: Green, open problem 29 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.29
- track: solved
- answer_shape: decide
- source_stem: 29
- source_namespace: Green29
- source_theorem: green_29
- source_category: research solved
- source_ams: 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open scoped Pointwise

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ {G : Type*} [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
          1 ≤ K → IsApproximateSubgroup K (A : Set G) →
            ∃ S ⊆ A, C * K ^ (-c) * (A.card : ℝ) ≤ (S.card : ℝ) ∧
            S ^ 8 ⊆ A ^ 4

end Problem

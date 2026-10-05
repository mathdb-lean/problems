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

- problem_id: G49
- collection: green
- question_id: green:49
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/49.lean#green_49
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that $A \subset \mathbb{F}_2^n$ is a set with $|A + A| \leq K|A|$. Is it true that $A$ is covered by $K^{O(1)}$ translates of a subspace of size $\leq |A|$? Solved by [GGM25], with at most $2K^{12}$ translates. The factor $2$ cannot be omitted: for $A = \mathbb{F}_2^n \setminus \{0\}$ one has $K = 2^n / (2^n - 1)$, so $K^C \to 1$ as $n \to \infty$, while every subspace of size at most $|A|$ is proper and two translates are needed.
- notes: Green, open problem 49
- track: solved
- answer_shape: decide
- source_stem: 49
- source_namespace: Green49
- source_theorem: green_49
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped Pointwise Finset

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ C > 0,
          ∀ n (A : Finset (𝔽₂ n)), A.Nonempty →
          ∀ K ≥ (1 : ℝ), (#(A + A) : ℝ) ≤ K * #A →
            ∃ (W : Submodule (ZMod 2) (𝔽₂ n)) (T : Finset (𝔽₂ n)),
              Nat.card W ≤ #A ∧
              (#T : ℝ) ≤ 2 * K ^ C ∧
              (A : Set (𝔽₂ n)) ⊆ T + W

end Problem

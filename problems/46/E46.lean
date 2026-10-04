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

- problem_id: E46
- collection: erdos
- question_id: erdos:46
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/46.lean#erdos_46
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does every finite colouring of the integers have a monochromatic solution to $1=\sum \frac{1}{n_i}$ with $2\leq n_1<\cdots <n_k$? The answer is yes, as proved by Croot [Cr03] - indeed, there are infinitely many disjoint such monochromatic solutions.
- notes: Erdos Problem 46 -- https://www.erdosproblems.com/46
- track: solved
- answer_shape: decide
- source_stem: 46
- mathdb_ref: erdos:46
- source_namespace: Erdos46
- source_theorem: erdos_46
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
    -- For any finite colouring of the integers
    ∀ (𝓒 : ℕ → ℕ), (Set.range 𝓒).Finite →
      -- there are integers `2 ≤ n₁ < ⋯ < n_k`
      ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) ∧
        -- whose reciprocals sum to `1`
        ∑ n ∈ S, (1 / n : ℚ) = 1 ∧
        -- and which all have the same colour
        (𝓒 '' (S : Set ℕ)).Subsingleton

end Problem

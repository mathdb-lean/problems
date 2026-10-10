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

- problem_id: E869
- collection: erdos
- question_id: erdos:869
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/869.lean#erdos_869
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $A_1, A_2$ are disjoint additive bases of order $2$ (i.e. $A_i + A_i$ contains all large integers) then must $A = A_1 \cup A_2$ contain a minimal additive basis of order $2$ (one such that deleting any element creates infinitely many $n \notin A + A$)? A question of Erdős and Nathanson [ErNa88, Er92c]. The answer is no: Larsen [La26] constructed disjoint bases $A_1, A_2$ of order $2$ such that $A_1 \cup A_2$ contains no minimal basis of order $2$.
- notes: Erdos Problem 869 -- https://www.erdosproblems.com/869
- track: solved
- answer_shape: decide
- source_stem: 869
- mathdb_ref: erdos:869
- source_namespace: Erdos869
- source_theorem: erdos_869
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (A₁ A₂ : Set ℕ), Disjoint A₁ A₂ →
          A₁.IsAsymptoticAddBasisOfOrder 2 → A₂.IsAsymptoticAddBasisOfOrder 2 →
          ∃ D ⊆ A₁ ∪ A₂, D.IsAsymptoticAddBasisOfOrder 2 ∧
            ∀ d ∈ D, ¬ (D \ {d}).IsAsymptoticAddBasisOfOrder 2

end Problem

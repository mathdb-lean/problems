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

- problem_id: E741_parts_ii
- collection: erdos
- question_id: erdos:741
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/741.lean#erdos_741.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a basis $A$ of order $2$ such that if $A=A_1\sqcup A_2$ then $A_1+A_1$ and $A_2+A_2$ cannot both have bounded gaps? This was proved by DeepMind prover agent.
- notes: Erdos Problem 741 -- https://www.erdosproblems.com/741
- track: solved
- answer_shape: decide
- source_stem: 741
- mathdb_ref: erdos:741
- source_namespace: Erdos741
- source_theorem: erdos_741.parts.ii
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped Pointwise
open Set

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ A : Set ℕ, IsAddBasisOfOrder (A ∪ {0}) 2 ∧ ∀ A₁ A₂,
        A = A₁ ∪ A₂ → Disjoint A₁ A₂ → ¬ (IsSyndetic (A₁ + A₁) ∧ IsSyndetic (A₂ + A₂))

end Problem

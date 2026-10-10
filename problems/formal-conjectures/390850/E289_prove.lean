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

- problem_id: E289_prove
- collection: erdos
- question_id: erdos:289
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/289.lean#erdos_289
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for all sufficiently large $k$, there exist finite intervals $I_1, \dotsc, I_k \subset \mathbb{N}$, distinct, not overlapping or adjacent, with $|I_i| \geq 2$ for $1 \leq i \leq k$ such that $$ 1 = \sum_{i=1}^k \sum_{n \in I_i} \frac{1}{n}? $$ Here two intervals are adjacent if their union is again an interval, so any two of the $I_i$ must be separated by at least one integer.
- notes: Erdos Problem 289 -- https://www.erdosproblems.com/289
- track: open
- answer_shape: prove
- pair_id: E289
- pair_role: prove
- source_stem: 289
- mathdb_ref: erdos:289
- source_namespace: Erdos289
- source_theorem: erdos_289
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Asymptotics Filter Finset

namespace Problem

abbrev Target : Prop :=
    (∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ,
        (∀ i, (I i).1 < (I i).2) ∧
        (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
        ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1)

end Problem

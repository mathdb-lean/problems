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

- problem_id: Nconjecture_1_3_to_2_3_conjecture_1_3_to_2_3_prove
- collection: wikipedia
- question_id: wikipedia:conjecture_1_3_to_2_3
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/conjecture_1_3_to_2_3.lean#conjecture_1_3_to_2_3
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does every finite partially ordered set that is not totally ordered contain two elements $x$ and $y$ such that the probability that $x$ appears before $y$ in a random linear extension is between $\frac 1 3$ and $\frac 2 3$? The set of all total order extensions is represented as order preserving bijections $P$ of $1, ..., n$.
- notes: Wikipedia: conjecture_1_3_to_2_3 -- https://en.wikipedia.org/wiki/1/3%E2%80%932/3_conjecture
- track: open
- answer_shape: prove
- pair_id: Nconjecture_1_3_to_2_3_conjecture_1_3_to_2_3
- pair_role: prove
- source_stem: conjecture_1_3_to_2_3
- source_namespace: Conjecture_1_3_to_2_3
- source_theorem: conjecture_1_3_to_2_3
- source_category: research open
- source_ams: 6
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (P : Type) [Finite P] [PartialOrder P]
        (not_total : ¬ Std.Total (α := P) (· ≤ ·)) (total_ext : Set <| OrderHom P ℕ)
        (total_ext_def : ∀ σ, σ ∈ total_ext ↔ Set.range σ = Set.Icc 1 (Nat.card P)),
        ∃ x y : P, ({σ ∈ total_ext | σ x < σ y}.ncard / total_ext.ncard : ℚ)
          ∈ Set.Icc (1/3) (2/3)

end Problem

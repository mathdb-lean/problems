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

- problem_id: E238_refute
- collection: erdos
- question_id: erdos:238
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/238.lean#erdos_238
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let `c₁, c₂ > 0`. Is it true that for any sufficiently large `x`, there exists more than `c₁ * log x` many consecutive primes `≤ x` such that the difference between any two is `> c₂`?
- notes: Erdos Problem 238 -- https://www.erdosproblems.com/238
- track: open
- answer_shape: refute
- pair_id: E238
- pair_role: refute
- source_stem: 238
- mathdb_ref: erdos:238
- source_namespace: Erdos238
- source_theorem: erdos_238
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Topology
open Set Filter Real

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ᵉ (c₁ > 0) (c₂ > 0), ∀ᶠ (x : ℝ) in atTop, ∃ (k : ℕ),
          c₁ * log x < k ∧ ∃ f : Fin k → ℕ, ∃ m, (∀ i, f i ≤ x ∧ f i = (m + i.1).nth Nat.Prime)
          ∧ ∀ i : Fin (k - 1), c₂ < primeGap (m + i.1)
    )

end Problem

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

- problem_id: E951_refute
- collection: erdos
- question_id: erdos:951
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/951.lean#erdos_951
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If `1 < a 0 < ...` has property `Erdos951Prop`, is it true that `#{a i ≤ x} ≤ π x`?
- notes: Erdos Problem 951 -- https://www.erdosproblems.com/951
- track: open
- answer_shape: refute
- pair_id: E951
- pair_role: refute
- source_stem: 951
- mathdb_ref: erdos:951
- source_namespace: Erdos951
- source_theorem: erdos_951
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Finsupp Nat.Prime Topology
open Filter

namespace Problem

/-- A sequence `a : ℕ → ℝ` is said to have property `Erdos951Prop` if for any pair of distinct
finitely supported sequences `k l : ℕ →₀ ℕ` their corresponding Beurling integers are of distance
at least one apart. -/
def Erdos951Prop (a : ℕ → ℝ) : Prop :=
  ∀ (k ℓ : ℕ →₀ ℕ), k ≠ ℓ → |beurlingInteger a k - beurlingInteger a ℓ| ≥ 1

abbrev Target : Prop :=
    ¬ (
      ∀ a : ℕ → ℝ, 1 < a 0 → StrictMono a → Erdos951Prop a →
            ∀ᶠ (x : ℝ) in Filter.atTop, {i : ℕ | a i ≤ x}.ncard ≤ π ⌊x⌋₊
    )

end Problem

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

- problem_id: E375_prove
- collection: erdos
- question_id: erdos:375
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/375.lean#erdos_375
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is `Erdos375Prop` true?
- notes: Erdos Problem 375 -- https://www.erdosproblems.com/375
- track: open
- answer_shape: prove
- pair_id: E375
- pair_role: prove
- source_stem: 375
- mathdb_ref: erdos:375
- source_namespace: Erdos375
- source_theorem: erdos_375
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set Filter Topology Asymptotics

namespace Problem

/-- This is a proposition saying that for any `n ≥ 1` and any `k`, if `n + 1, ..., n + k` are all
composite, then there are distinct primes `p₁, ... pₖ` such that `pᵢ ∣ n + i` for all `1 ≤ i ≤ k`.
-/
def Erdos375Prop : Prop := ∀ n ≥ 1, ∀ k, (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1

abbrev Target : Prop :=
    Erdos375Prop

end Problem

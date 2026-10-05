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

- problem_id: E890_parts_b_refute
- collection: erdos
- question_id: erdos:890
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/890.lean#erdos_890.parts.b
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that $$\limsup_{n\to \infty}\left(\sum_{0\leq i < k}\omega(n+i)\right) \frac{\log\log n}{\log n}=1,$$ where $\omega$ counts the number of distinct prime factors without restriction?
- notes: Erdos Problem 890 -- https://www.erdosproblems.com/890
- track: open
- answer_shape: refute
- pair_id: E890_parts_b
- pair_role: refute
- source_stem: 890
- mathdb_ref: erdos:890
- source_namespace: Erdos890
- source_theorem: erdos_890.parts.b
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Finset Real
open scoped Nat.Prime ArithmeticFunction.omega

namespace Problem

/-- `omegaGt k n` counts the number of distinct prime factors of `n` that are strictly
greater than `k`. -/
def omegaGt (k n : ℕ) : ℕ :=
  (n.primeFactors.filter (· > k)).card

local notation "ω_gt" => omegaGt

abbrev Target : Prop :=
    ¬ (
      ∀ k ≥ 1, limsup (fun n ↦ (∑ i ∈ range k, (ω (n + i) : EReal)) *
        (log (log n) / log n)) atTop = 1
    )

end Problem

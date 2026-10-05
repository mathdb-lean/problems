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

- problem_id: E280
- collection: erdos
- question_id: erdos:280
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/280.lean#erdos_280
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $n_1<n_2<\cdots $ be an infinite sequence of integers with associated $a_k\pmod{n_k}$, such that for some $\epsilon>0$ we have $n_k>(1+\epsilon)k\log k$ for all $k$. Then $$ \#\{ m<n_k : m\not\equiv a_i\pmod{n_i} \textrm{ for }1\leq i\leq k\}\neq o(k). $$ Cambie observed that this is false.
- notes: Erdos Problem 280 -- https://www.erdosproblems.com/280
- track: solved
- answer_shape: decide
- source_stem: 280
- mathdb_ref: erdos:280
- source_namespace: Erdos280
- source_theorem: erdos_280
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open Filter

/-- The integer `m` is covered by one of the first `k` chosen congruence classes. -/
def isCoveredBy (n a : ℕ → ℕ) (m k : ℕ) : Prop :=
  ∃ i ∈ Finset.Icc 1 k, m % n i = a i

/-- The number of integers below `n k` not covered by the first `k` congruence classes. -/
noncomputable def uncoveredCount (n a : ℕ → ℕ) (k : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n k)).filter (fun m => ¬ isCoveredBy n a m k)).card

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (n a : ℕ → ℕ), StrictMono n → (∀ i, 1 ≤ i → a i < n i) →
          (∃ ε : ℝ, 0 < ε ∧
            ∀ k, 1 ≤ k → (n k : ℝ) > (1 + ε) * (k : ℝ) * Real.log (k : ℝ)) →
          ¬ Tendsto
            (fun k : ℕ => (uncoveredCount n a k : ℝ) / (k : ℝ))
            atTop (nhds 0)

end Problem

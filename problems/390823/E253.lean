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

- problem_id: E253
- collection: erdos
- question_id: erdos:253
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/253.lean#erdos_253
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a_1 < a_2 < \dotsc$ be an infinite sequence of positive integers such that $\frac{a_{i+1}}{a_i} \to 1$. If every arithmetic progression contains infinitely many integers which are the sum of distinct $a_i$ then every sufficiently large integer is the sum of distinct $a_i$.
- notes: Erdos Problem 253 -- https://www.erdosproblems.com/253
- track: solved
- answer_shape: proof
- source_stem: 253
- mathdb_ref: erdos:253
- source_namespace: Erdos253
- source_theorem: erdos_253
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open scoped Topology

/-- The predicate that `a : ℕ → ℕ` is a strictly monotone sequence such that every infinite
arithmetic progression contains infinitely many integers that are the sum of distinct $a_i$s. -/
@[inline]
def RepresentsAPs (a : ℕ → ℕ) : Prop :=
    StrictMono a ∧ ∀ l, l.IsAPOfLength ⊤ → (subsetSums (Set.range a) ∩ l).Infinite

abbrev Target : Prop :=
    ¬ ∀ a : ℕ → ℕ, 0 < a 0 →
        RepresentsAPs a → (Filter.atTop.Tendsto (fun n ↦ (a <| n + 1 : ℝ) / a n) (𝓝 1)) →
          subsetSums (Set.range a) ∈ Filter.cofinite

end Problem
